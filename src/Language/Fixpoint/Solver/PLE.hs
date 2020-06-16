--------------------------------------------------------------------------------
-- | This module implements "Proof by Logical Evaluation" where we 
--   unfold function definitions if they *must* be unfolded, to strengthen
--   the environments with function-definition-equalities. 
--   The algorithm is discussed at length in:
-- 
--     1. "Refinement Reflection", POPL 2018, https://arxiv.org/pdf/1711.03842
--     2. "Reasoning about Functions", VMCAI 2018, https://ranjitjhala.github.io/static/reasoning-about-functions.pdf 
--------------------------------------------------------------------------------

{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ExistentialQuantification #-}

module Language.Fixpoint.Solver.PLE (instantiate, unify) where

import           Language.Fixpoint.Types hiding (simplify)
import           Language.Fixpoint.Types.Config  as FC
import qualified Language.Fixpoint.Types.Visitor as Vis
import qualified Language.Fixpoint.Misc          as Misc 
import qualified Language.Fixpoint.Smt.Interface as SMT
import           Language.Fixpoint.Defunctionalize
import qualified Language.Fixpoint.Utils.Trie    as T 
import           Language.Fixpoint.Utils.Progress 
import           Language.Fixpoint.SortCheck
import           Language.Fixpoint.Graph.Deps             (isTarget) 
import           Language.Fixpoint.Solver.Sanitize        (symbolEnv)
import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import           Data.Hashable
import           GHC.Generics
import           Data.Generics()
import qualified Data.HashMap.Strict  as M
import qualified Data.HashSet         as S
import qualified Data.List            as L
import qualified Data.Maybe           as Mb 
import           Debug.Trace          (trace)

mytracepp :: (PPrint a) => String -> a -> a
mytracepp = notracepp

--------------------------------------------------------------------------------
-- | Strengthen Constraint Environments via PLE 
--------------------------------------------------------------------------------
instantiate :: (Loc a) => Config -> SInfo a -> IO (SInfo a)
instantiate cfg fi' = do 
    let cs = [ (i, c) | (i, c) <- M.toList (cm fi), isPleCstr aEnv i c ] 
    let t  = mkCTrie cs                                               -- 1. BUILD the Trie
    res   <- withProgress (1 + length cs) $ 
               withCtx cfg file sEnv (pleTrie t . instEnv cfg fi cs)  -- 2. TRAVERSE Trie to compute InstRes
    return $ resSInfo cfg sEnv fi res                                 -- 3. STRENGTHEN SInfo using InstRes
  where
    file   = srcFile cfg ++ ".evals"
    sEnv   = symbolEnv cfg fi
    aEnv   = ae fi 
    fi     = normalize fi' 



------------------------------------------------------------------------------- 
-- | Step 1a: @instEnv@ sets up the incremental-PLE environment 
instEnv :: (Loc a) => Config -> SInfo a -> [(SubcId, SimpC a)] -> SMT.Context -> InstEnv a 
instEnv cfg fi cs ctx = InstEnv cfg ctx bEnv aEnv (M.fromList cs) γ s0
  where 
    bEnv              = bs fi
    aEnv              = ae fi
    γ                 = knowledge cfg ctx fi  
    s0                = EvalEnv (SMT.ctxSymEnv ctx) mempty

---------------------------------------------------------------------------------------------- 
-- | Step 1b: @mkCTrie@ builds the @Trie@ of constraints indexed by their environments 
mkCTrie :: [(SubcId, SimpC a)] -> CTrie 
mkCTrie ics  = T.fromList [ (cBinds c, i) | (i, c) <- ics ]
  where
    cBinds   = L.sort . elemsIBindEnv . senv 

---------------------------------------------------------------------------------------------- 
-- | Step 2: @pleTrie@ walks over the @CTrie@ to actually do the incremental-PLE
pleTrie :: CTrie -> InstEnv a -> IO InstRes
pleTrie t env = loopT env ctx0 diff0 Nothing res0 t 
  where 
    diff0        = []
    res0         = M.empty 
    ctx0         = initCtx $ ((mkEq <$> es0) ++ (mkEq' <$> es0'))
    es0          = L.filter (null . eqArgs) (aenvEqs   . ieAenv $ env)
    es0'         = L.filter (null . smArgs) (aenvSimpl . ieAenv $ env)
    mkEq  eq     = (EVar $ eqName eq, eqBody eq)
    mkEq' rw     = (EApp (EVar $ smName rw) (EVar $ smDC rw), smBody rw)

loopT :: InstEnv a -> ICtx -> Diff -> Maybe BindId -> InstRes -> CTrie -> IO InstRes
loopT env ctx delta i res t = case t of 
  T.Node []  -> return res
  T.Node [b] -> loopB env ctx delta i res b
  T.Node bs  -> withAssms env ctx delta Nothing $ \ctx' -> do 
                  (ctx'', res') <- ple1 env ctx' i res 
                  foldM (loopB env ctx'' [] i) res' bs

loopB :: InstEnv a -> ICtx -> Diff -> Maybe BindId -> InstRes -> CBranch -> IO InstRes
loopB env ctx delta iMb res b = case b of 
  T.Bind i t -> loopT env ctx (i:delta) (Just i) res t
  T.Val cid  -> withAssms env ctx delta (Just cid) $ \ctx' -> do 
                  progressTick
                  (snd <$> ple1 env ctx' iMb res) 


withAssms :: InstEnv a -> ICtx -> Diff -> Maybe SubcId -> (ICtx -> IO b) -> IO b 
withAssms env@(InstEnv {..}) ctx delta cidMb act = do 
  let ctx'  = updCtx env ctx delta cidMb 
  let assms = icAssms ctx'
  SMT.smtBracket ieSMT  "PLE.evaluate" $ do
    forM_ assms (SMT.smtAssert ieSMT) 
    act ctx'

-- | @ple1@ performs the PLE at a single "node" in the Trie 
ple1 :: InstEnv a -> ICtx -> Maybe BindId -> InstRes -> IO (ICtx, InstRes)
ple1 (InstEnv {..}) ctx i res = 
  updCtxRes res i <$> evalCandsLoop ieCfg ctx ieSMT ieKnowl ieEvEnv


evalToSMT :: String -> Config -> SMT.Context -> (Expr, Expr) -> Pred 
evalToSMT msg cfg ctx (e1,e2) = toSMT ("evalToSMT:" ++ msg) cfg ctx [] (EEq e1 e2)

toPairs :: S.HashSet ([Expr], Expr) -> S.HashSet (Expr, Expr)
toPairs = S.map (\(a,b) -> (last a, b))


fromPairs :: S.HashSet (Expr, Expr) -> S.HashSet ([Expr], Expr)
fromPairs = S.map (\(a,b) -> ([a], b)) 

evalCandsLoop :: Config -> ICtx -> SMT.Context -> Knowledge -> EvalEnv -> IO ICtx 
evalCandsLoop cfg ictx0 ctx γ env = go ictx0 
  where
    withRewrites exprs =
      let
        rws = [rewrite e rw | rw <- knSims γ
                            ,  e <- S.toList (snd `S.map` exprs)]
      in 
        exprs <> S.fromList (map (\(a,b) -> ([a], b)) $ concat rws)
    go ictx | S.null (icCands ictx) = return ictx 
    go ictx =  do let cands = icCands ictx
                  let env' = env {  evAccum    = icEquals   ictx <> evAccum env }
                  evalResults   <- SMT.smtBracket ctx "PLE.evaluate" $ do
                               SMT.smtAssert ctx (pAnd (S.toList $ icAssms ictx)) 
                               mapM (evalOne γ env' ictx) (S.toList cands)
                  let us = mconcat evalResults 
                  if S.null (us `S.difference` icEquals ictx)
                        then return ictx 
                        else do  let oks      = (last . fst) `S.map` us
                                 let us'      = withRewrites us 
                                 let eqsSMT   = evalToSMT "evalCandsLoop" cfg ctx `S.map` (toPairs us')
                                 let ictx'    = ictx { icSolved = icSolved ictx <> oks 
                                                     , icEquals = icEquals ictx <> us'

                                                     , icAssms  = icAssms  ictx <> S.filter (not . isTautoPred) eqsSMT }
                                 let newcands = mconcat (makeCandidates γ ictx' <$> S.toList (cands <> (snd `S.map` us)))
                                 go (ictx' { icCands = S.fromList newcands})
                                 


rewrite :: Expr -> Rewrite -> [(Expr,Expr)] 
rewrite e rw = Mb.catMaybes $ map (`rewriteTop` rw) (notGuardedApps e)

rewriteTop :: Expr -> Rewrite -> Maybe (Expr,Expr) 
rewriteTop e rw
  | (EVar f, es) <- splitEApp e
  , f == smDC rw
  , length es == length (smArgs rw)
  = Just (EApp (EVar $ smName rw) e, subst (mkSubst $ zip (smArgs rw) es) (smBody rw))
  | otherwise
  = Nothing

---------------------------------------------------------------------------------------------- 
-- | Step 3: @resSInfo@ uses incremental PLE result @InstRes@ to produce the strengthened SInfo 
---------------------------------------------------------------------------------------------- 

resSInfo :: Config -> SymEnv -> SInfo a -> InstRes -> SInfo a
resSInfo cfg env fi res = strengthenBinds fi res' 
  where
    res'     = M.fromList $ zip is ps''
    ps''     = zipWith (\i -> elaborate (atLoc dummySpan ("PLE1 " ++ show i)) env) is ps' 
    ps'      = defuncAny cfg env ps
    (is, ps) = unzip (M.toList res)

---------------------------------------------------------------------------------------------- 
-- | @InstEnv@ has the global information needed to do PLE
---------------------------------------------------------------------------------------------- 

data InstEnv a = InstEnv 
  { ieCfg   :: !Config
  , ieSMT   :: !SMT.Context
  , ieBEnv  :: !BindEnv
  , ieAenv  :: !AxiomEnv 
  , ieCstrs :: !(M.HashMap SubcId (SimpC a))
  , ieKnowl :: !Knowledge
  , ieEvEnv :: !EvalEnv
  } 

---------------------------------------------------------------------------------------------- 
-- | @ICtx@ is the local information -- at each trie node -- obtained by incremental PLE
---------------------------------------------------------------------------------------------- 

data ICtx    = ICtx 
  { icAssms    :: S.HashSet Pred            -- ^ Equalities converted to SMT format
  , icCands    :: S.HashSet Expr            -- ^ "Candidates" for unfolding
  , icEquals   :: S.HashSet ([Expr], Expr)     -- ^ Accumulated equalities
  , icSolved   :: S.HashSet Expr            -- ^ Terms that we have already expanded
  , icSimpl    :: !ConstMap                 -- ^ Map of expressions to constants
  , icSubcId   :: Maybe SubcId              -- ^ Current subconstraint ID
  } 

---------------------------------------------------------------------------------------------- 
-- | @InstRes@ is the final result of PLE; a map from @BindId@ to the equations "known" at that BindId
---------------------------------------------------------------------------------------------- 

type InstRes = M.HashMap BindId Expr

---------------------------------------------------------------------------------------------- 
-- | @Unfold is the result of running PLE at a single equality; 
--     (e, [(e1, e1')...]) is the source @e@ and the (possible empty) 
--   list of PLE-generated equalities (e1, e1') ... 
---------------------------------------------------------------------------------------------- 

type CTrie   = T.Trie   SubcId
type CBranch = T.Branch SubcId
type Diff    = [BindId]    -- ^ in "reverse" order

initCtx :: [(Expr,Expr)] -> ICtx
initCtx es = ICtx 
  { icAssms    = mempty 
  , icCands    = mempty 
  , icEquals   = S.fromList $ map (\(a,b) -> ([a], b)) es  
  , icSolved   = mempty
  , icSimpl    = mempty 
  , icSubcId   = Nothing
  }

equalitiesPred :: S.HashSet (Expr, Expr) -> [Expr]
equalitiesPred eqs = [ EEq e1 e2 | (e1, e2) <- S.toList eqs, e1 /= e2 ] 

updCtxRes :: InstRes -> Maybe BindId -> ICtx -> (ICtx, InstRes) 
updCtxRes res iMb ctx = (ctx, res')
  where 
    res' = updRes res iMb (pAnd $ equalitiesPred $ toPairs $ icEquals ctx)


updRes :: InstRes -> Maybe BindId -> Expr -> InstRes
updRes res (Just i) e = M.insert i e res 
updRes res  Nothing _ = res 

---------------------------------------------------------------------------------------------- 
-- | @updCtx env ctx delta cidMb@ adds the assumptions and candidates from @delta@ and @cidMb@ 
--   to the context. 
---------------------------------------------------------------------------------------------- 

updCtx :: InstEnv a -> ICtx -> Diff -> Maybe SubcId -> ICtx 
updCtx InstEnv {..} ctx delta cidMb 
              = ctx { icAssms  = S.fromList (filter (not . isTautoPred) ctxEqs)  
                    , icCands  = S.fromList cands           <> icCands  ctx
                    , icEquals = fromPairs initEqs          <> icEquals ctx
                    , icSimpl  = M.fromList (S.toList sims) <> icSimpl ctx <> econsts
                    , icSubcId = cidMb
                    }
  where         
    initEqs   = S.fromList $ concat [rewrite e rw | e  <- (cands ++ (snd <$> S.toList (icEquals ctx)))
                                                  , rw <- knSims ieKnowl]
    cands     = concatMap (makeCandidates ieKnowl ctx) (rhs:es)
    sims      = S.filter (isSimplification (knDCs ieKnowl)) (initEqs <> toPairs (icEquals ctx))
    econsts   = M.fromList $ findConstants ieKnowl es
    ctxEqs    = toSMT "updCtx" ieCfg ieSMT [] <$> L.nub (concat 
                  [ equalitiesPred initEqs 
                  , equalitiesPred sims 
                  , equalitiesPred (toPairs $ icEquals ctx)
                  , [ expr xr   | xr@(_, r) <- bs, null (Vis.kvars r) ] 
                  ])
    bs        = unElab <$> binds
    (rhs:es)  = unElab <$> (eRhs : (expr <$> binds))
    eRhs      = maybe PTrue crhs subMb
    binds     = [ lookupBindEnv i ieBEnv | i <- delta ] 
    subMb     = getCstr ieCstrs <$> cidMb


findConstants :: Knowledge -> [Expr] -> [(Expr, Expr)]
findConstants γ es = [(EVar x, c) | (x,c) <- go [] (concatMap splitPAnd es)]  
  where 
    go su ess = if ess == ess' 
                  then su 
                  else go (su ++ su') ess' 
       where ess' = subst (mkSubst su') <$> ess
             su'  = makeSu ess 
    makeSu exprs  = [(x,c) | (EEq (EVar x) c) <- exprs 
                           , isConstant (knDCs γ) c
                           , EVar x /= c ]

makeCandidates :: Knowledge -> ICtx -> Expr -> [Expr]
makeCandidates γ ctx expr 
  = mytracepp ("\n" ++ show (length cands) ++ " New Candidates") cands
  where 
    cands = filter (\e -> isRedex γ e && (not (e `S.member` icSolved ctx))) (notGuardedApps expr)

isRedex :: Knowledge -> Expr -> Bool 
isRedex γ e = isGoodApp γ e || isIte e 
  where 
    isIte (EIte _ _ _) = True 
    isIte _            = False 


isGoodApp :: Knowledge -> Expr -> Bool 
isGoodApp γ e 
  | (EVar f, es) <- splitEApp e
  , Just i       <- L.lookup f (knSummary γ)
  = length es >= i
  | otherwise
  = False 
    



getCstr :: M.HashMap SubcId (SimpC a) -> SubcId -> SimpC a 
getCstr env cid = Misc.safeLookup "Instantiate.getCstr" cid env

isPleCstr :: AxiomEnv -> SubcId -> SimpC a -> Bool
isPleCstr aenv sid c = isTarget c && M.lookupDefault False sid (aenvExpand aenv) 


--------------------------------------------------------------------------------
data EvalEnv = EvalEnv
  { evEnv      :: !SymEnv
  , evAccum    :: S.HashSet ([Expr], Expr)
  }

type EvalST a = StateT EvalEnv IO a
--------------------------------------------------------------------------------

evalOne :: Knowledge -> EvalEnv -> ICtx -> Expr -> IO (S.HashSet ([Expr], Expr))
evalOne γ env ctx e = do
  (e',st) <- runStateT (eval γ ctx [e]) env 
  return $ if e' == e then evAccum st else S.insert ([e], e') (evAccum st)

notGuardedApps :: Expr -> [Expr]
notGuardedApps = go 
  where 
    go e@(EApp e1 e2)  = [e] ++ go e1 ++ go e2
    go (PAnd es)       = concatMap go es
    go (POr es)        = concatMap go es
    go (PAtom _ e1 e2) = go e1  ++ go e2
    go (PIff e1 e2)    = go e1  ++ go e2
    go (PImp e1 e2)    = go e1  ++ go e2 
    go (EBin  _ e1 e2) = go e1  ++ go e2
    go (PNot e)        = go e
    go (ENeg e)        = go e
    go e@(EIte b _ _)  = go b ++ [e] -- ++ go e1 ++ go e2  
    go (ECoerc _ _ e)  = go e 
    go (ECst e _)      = go e 
    go (ESym _)        = []
    go (ECon _)        = []
    go (EVar _)        = []
    go (ELam _ _)      = []
    go (ETApp _ _)     = []
    go (ETAbs _ _)     = []
    go (PKVar _ _)     = []
    go (PAll _ _)      = []
    go (PExist _ _)    = []
    go (PGrad{})       = []

unifyAll :: [Symbol] -> [Expr] -> [Expr] -> Maybe Subst
unifyAll _ []     []               = Just (Su M.empty)
unifyAll freeVars (template:xs) (seen:ys) =
  do
    rs@(Su s1) <- unify freeVars template seen
    let xs' = map (subst rs) xs
    let ys' = map (subst rs) ys
    (Su s2) <- unifyAll (freeVars L.\\ M.keys s1) xs' ys'
    return $ Su (M.union s1 s2)
unifyAll _ _ _ = undefined

unify :: [Symbol] -> Expr -> Expr -> Maybe Subst
unify _ template seenExpr | template == seenExpr = Just (Su M.empty)
unify freeVars template seenExpr = case (template, seenExpr) of
  (EVar rwVar, _) | rwVar `elem` freeVars ->
    return $ Su (M.singleton rwVar seenExpr)
  (EApp templateF templateBody, EApp seenF seenBody) ->
    unifyAll freeVars [templateF, templateBody] [seenF, seenBody]
  (ENeg rw, ENeg seen) ->
    unify freeVars rw seen
  (EBin op rwLeft rwRight, EBin op' seenLeft seenRight) | op == op' ->
    unifyAll freeVars [rwLeft, rwRight] [seenLeft, seenRight]
  (EIte cond rwLeft rwRight, EIte seenCond seenLeft seenRight) ->
    unifyAll freeVars [cond, rwLeft, rwRight] [seenCond, seenLeft, seenRight]
  (ECst rw _, ECst seen _) ->
    unify freeVars rw seen
  (ETApp rw _, ETApp seen _) ->
    unify freeVars rw seen
  (ETAbs rw _, ETAbs seen _) ->
    unify freeVars rw seen
  (PAnd rw, PAnd seen ) ->
    unifyAll freeVars rw seen
  (POr rw, POr seen ) ->
    unifyAll freeVars rw seen
  (PNot rw, PNot seen) ->
    unify freeVars rw seen
  (PImp templateF templateBody, PImp seenF seenBody) ->
    unifyAll freeVars [templateF, templateBody] [seenF, seenBody]
  (PIff templateF templateBody, PIff seenF seenBody) ->
    unifyAll freeVars [templateF, templateBody] [seenF, seenBody]
  (PAtom rel templateF templateBody, PAtom rel' seenF seenBody) | rel == rel' ->
    unifyAll freeVars [templateF, templateBody] [seenF, seenBody]
  (PAll _ rw, PAll _ seen) ->
    unify freeVars rw seen
  (PExist _ rw, PExist _ seen) ->
    unify freeVars rw seen
  (PGrad _ _ _ rw, PGrad _ _ _ seen) ->
    unify freeVars rw seen
  (ECoerc _ _ rw, ECoerc _ _ seen) ->
    unify freeVars rw seen
  _ -> Nothing

type Op = Symbol
type OpOrdering = [Symbol]
type Term = Expr

data SCDir =
    SCUp
  | SCEq 
  | SCDown
  deriving (Eq, Ord, Show, Generic)

instance Hashable SCDir

type SCPath = ((Op, Int), (Op, Int), [SCDir])

data SCEntry = SCEntry {
    from :: (Op, Int)
  , to   :: (Op, Int)
  , dir  :: SCDir
} deriving (Eq, Ord, Show, Generic)

instance Hashable SCEntry

getDir :: OpOrdering -> Term -> Term -> SCDir
getDir _ (EVar _) (EVar _) = SCEq
getDir o from to =
  case (synGTE o from to, synGTE o to from) of
      (True, True)  -> SCEq
      (True, False) -> SCDown
      (False, _)    -> SCUp

getSC :: OpOrdering -> Term -> Term -> S.HashSet SCEntry
getSC o l r = case (splitEApp l, splitEApp r) of
  ((EVar op, ts), (EVar op', us)) ->
    S.fromList $ do
      (i, from) <- zip [0..] ts
      (j, to)   <- zip [0..] us
      return $ SCEntry (op, i) (op', j) (getDir o from to)
  _ -> S.empty

scp :: OpOrdering -> [Expr] -> S.HashSet SCPath
scp _ []       = S.empty
scp _ [_]      = S.empty
scp o [t1, t2] = S.fromList $ do
  (SCEntry a b d) <- S.toList $ getSC o t1 t2
  return (a, b, [d])
scp o (t1:t2:trms) = S.fromList $ do
  (SCEntry a b' d) <- S.toList $ getSC o t1 t2
  (a', b, ds)      <- S.toList $ scp o (t2:trms)
  guard $ b' == a'
  return (a, b, d:ds)

synEQ :: OpOrdering -> Expr -> Expr -> Bool
synEQ o l r = synGTE o l r && synGTE o r l

opGT :: OpOrdering -> Op -> Op -> Bool
opGT ordering op1 op2 = case (L.elemIndex op1 ordering, L.elemIndex op2 ordering)  of
  (Just index1, Just index2) -> index1 > index2
  _ -> False

removeSynEQs :: OpOrdering -> [Expr] -> [Expr] -> ([Expr], [Expr])
removeSynEQs _ [] ys      = ([], ys)
removeSynEQs ordering (x:xs) ys
  | Just yIndex <- L.findIndex (synEQ ordering x) ys
  = removeSynEQs ordering xs $ take yIndex ys ++ drop (yIndex + 1) ys
  | otherwise =
    let
      (xs', ys') = removeSynEQs ordering xs ys
    in
      (x:xs', ys')

synGTEM :: OpOrdering -> [Expr] -> [Expr] -> Bool
synGTEM ordering xs ys =     
  case removeSynEQs ordering xs ys of
    (_   , []) -> True
    (xs', ys') -> any (\x -> all (synGT ordering x) ys') xs'
    
synGT :: OpOrdering -> Term -> Term -> Bool
synGT o t1 t2 = synGTE o t1 t2 && not (synGTE o t2 t1)
    
synGTE :: OpOrdering -> Expr -> Expr -> Bool
synGTE _        (EVar _)   (EVar _)   = True
synGTE _        (EVar _)   (EApp _ _) = False
synGTE _        (EApp _ _) (EVar _)   = True
synGTE ordering t1 t2 = case (splitEApp t1, splitEApp t2) of
  ((EVar x, tms), (EVar y, tms')) ->
    if opGT ordering x y then
      synGTEM ordering [t1] tms'
    else if opGT ordering y x then
      synGTEM ordering tms [t2]
    else
      synGTEM ordering tms tms'
  _ -> False


powerset :: [a] -> [[a]]
powerset [] = [[]]
powerset (x:xs) = [x:ps | ps <- powerset xs] ++ powerset xs
    
orderings :: S.HashSet Op -> S.HashSet OpOrdering
orderings ops = S.fromList $ do
  ops' <- powerset (S.toList ops)
  L.permutations ops'

opSyms :: Expr -> S.HashSet Symbol
opSyms (EApp (EVar op) ts) = S.insert op (opSyms ts)
opSyms _ = S.empty

diverges :: [Expr] -> Bool
diverges terms = all diverges' orderings'
  where
   syms'       = S.unions (map opSyms terms)
   orderings'  = orderings syms'
   diverges' o = divergesFor o terms
   
divergesFor :: OpOrdering -> [Expr] -> Bool
divergesFor o trms = any diverges' (L.subsequences trms)
  where
    diverges' :: [Expr] -> Bool
    diverges' trms' =
      any ascending (scp o trms') && all (not . descending) (scp o trms')
      
descending :: SCPath -> Bool
descending (_, _, ds) = L.elem SCDown ds && L.notElem SCUp ds

ascending :: SCPath -> Bool
ascending  (a, b, ds) = a == b && L.elem SCUp ds

type SubExpr = (Expr, Expr -> Expr)

subExprs :: Expr -> [SubExpr]
subExprs ite@(EIte c lhs rhs)  = (ite,id):c'' ++ l'' ++ r''
  where
    c' = subExprs c
    l' = subExprs lhs
    r' = subExprs rhs
    c'' = map (\(e, f) -> (e, \e' -> EIte (f e') lhs rhs)) c'
    l'' = map (\(e, f) -> (e, \e' -> EIte c (f e') rhs)) l'
    r'' = map (\(e, f) -> (e, \e' -> EIte c lhs (f e'))) r'
    
subExprs bin@(EBin op lhs rhs) = (bin,id):lhs'' ++ rhs''
  where
    lhs' = subExprs lhs
    rhs' = subExprs rhs
    lhs'' :: [SubExpr]
    lhs'' = map (\(e, f) -> (e, \e' -> EBin op (f e') rhs)) lhs'
    rhs'' :: [SubExpr]
    rhs'' = map (\(e, f) -> (e, \e' -> EBin op lhs (f e'))) rhs'
    
subExprs e = [(e, id)]

getRewrites :: Knowledge -> SymEnv -> [Expr] -> SubExpr -> AutoRewrite -> MaybeT IO Expr
getRewrites γ symEnv path  (subE, toE) (AutoRewrite args lhs rhs) =
  do
    su@(Su suMap) <- MaybeT $ return $ unify freeVars lhs subE
    let subE' = subst su rhs
    let expr' = toE subE'
    guard $ expr' `L.notElem` path
    let (argSorts', exprSorts') = sortsToUnify (M.toList suMap)
    let (argSorts, exprSorts)   = (gSorts argSorts', gSorts exprSorts')
    checkSorts argSorts exprSorts
    mapM_ (check . subst su) exprs
    guard $ not $ diverges $ path ++ [expr']
    return expr'
  where
    check :: Expr -> MaybeT IO ()
    check e = do
      valid <- MaybeT $ Just <$> isValid γ e
      guard valid

    checkSorts argSorts exprSorts =
      case runCM0 dummySpan $ unifys env Nothing argSorts exprSorts of
        Right  _ -> return ()
        Left   _ -> mzero

    sortsToUnify substList = unzip $ do
      (sym, e) <- substList
      sort     <- Mb.maybeToList (sortOf sym)
      return (sort, sortExpr dummySpan (seSort symEnv) e)
      
    sortOf sym =
      lookup sym [(sym, sort) | RR sort (Reft (sym, _)) <- args ]
      
    freeVars = [s | RR _ (Reft (s, _)) <- args ]
    exprs    = [e | RR _ (Reft (_, e)) <- args ]

    env = mkSearchEnv (seSort symEnv)


eval :: Knowledge -> ICtx -> [Expr] -> EvalST Expr
eval _ ctx path
  | Just v <- M.lookup (last path) (icSimpl ctx)
  = return v
        
eval γ ctx path =
  do
    -- let e = trace ("Eval " ++ (show $ last path)) $ last path
    let e = last path
    rws <- getRWs 
    e'  <- simplify γ ctx <$> go e
    let evAccum' = S.fromList $ map (path, ) $ filter (/= e) (e':rws)
    modify (\st -> st { evAccum = S.union evAccum' (evAccum st)})
    if e /= e'
      then eval γ (addConst (e,e') ctx) (path ++ [e'])
      else return e
  where
    autorws  =
      Mb.fromMaybe [] $ do
        cid <- icSubcId ctx
        M.lookup cid $ knAutoRWs γ

    getRWs :: EvalST [Expr]
    getRWs = concat <$> mapM getRWs' (subExprs (last path))

    getRWs' :: SubExpr -> EvalST [Expr]
    getRWs' s = do
      env <- gets evEnv
      Mb.catMaybes <$> mapM (liftIO . runMaybeT . getRewrites γ env path s) autorws

    addConst (e,e') ctx = if isConstant (knDCs γ) e'
                           then ctx { icSimpl = M.insert e e' $ icSimpl ctx} else ctx 
    go (ELam (x,s) e)   = ELam (x, s) <$> eval γ' ctx [e] where γ' = γ { knLams = (x, s) : knLams γ }
    go e@(EIte b e1 e2) = evalIte γ ctx e b e1 e2
    go (ECoerc s t e)   = ECoerc s t  <$> go e
    go e@(EApp _ _)     = case splitEApp e of 
                           (f, es) -> do (f':es') <- mapM (eval γ ctx . return) (f:es) 
                                         evalApp γ (eApps f' es) (f',es')
    go e@(PAtom r e1 e2) = fromMaybeM (PAtom r <$> go e1 <*> go e2) (evalBool γ e)
    go (ENeg e)         = do e'  <- eval γ ctx [e]
                             return $ ENeg e'
    go (EBin o e1 e2)   = do e1' <- eval γ ctx [e1]
                             e2' <- eval γ ctx [e2]
                             return $ EBin o e1' e2'
    go (ETApp e t)      = flip ETApp t <$> go e
    go (ETAbs e s)      = flip ETAbs s <$> go e
    go e@(PNot e')      = fromMaybeM (PNot <$> go e')           (evalBool γ e)
    go e@(PImp e1 e2)   = fromMaybeM (PImp <$> go e1 <*> go e2) (evalBool γ e)
    go e@(PIff e1 e2)   = fromMaybeM (PIff <$> go e1 <*> go e2) (evalBool γ e)
    go e@(PAnd es)      = fromMaybeM (PAnd <$> (go  <$$> es))   (evalBool γ e)
    go e@(POr es)       = fromMaybeM (POr  <$> (go <$$> es))    (evalBool γ e)
    go e                = return e


fromMaybeM :: (Monad m) => m a -> m (Maybe a) -> m a 
fromMaybeM a ma = do 
  mx <- ma 
  case mx of 
    Just x  -> return x 
    Nothing -> a  

(<$$>) :: (Monad m) => (a -> m b) -> [a] -> m [b]
f <$$> xs = f Misc.<$$> xs



 
evalApp :: Knowledge -> Expr -> (Expr, [Expr]) -> EvalST Expr
evalApp γ _ (EVar f, es) 
  | Just eq <- L.find ((== f) . eqName) (knAms γ)
  , length (eqArgs eq) <= length es 
  = do env <- seSort <$> gets evEnv
       let (es1,es2) = splitAt (length (eqArgs eq)) es
       return $ eApps (substEq env eq es1) es2 

evalApp γ _ (EVar f, e:es) 
  | (EVar dc, as) <- splitEApp e
  , Just rw <- L.find (\rw -> smName rw == f && smDC rw == dc) (knSims γ)
  , length as == length (smArgs rw)
  = return $ eApps (subst (mkSubst $ zip (smArgs rw) as) (smBody rw)) es 

evalApp _ e _
  = return e 
  
--------------------------------------------------------------------------------
-- | 'substEq' unfolds or instantiates an equation at a particular list of
--   argument values. We must also substitute the sort-variables that appear
--   as coercions. See tests/proof/ple1.fq
--------------------------------------------------------------------------------
substEq :: SEnv Sort -> Equation -> [Expr] -> Expr
substEq env eq es = subst su (substEqCoerce env eq es)
  where su = mkSubst $ zip (eqArgNames eq) es

substEqCoerce :: SEnv Sort -> Equation -> [Expr] -> Expr
substEqCoerce env eq es = Vis.applyCoSub coSub $ eqBody eq
  where 
    ts    = snd    <$> eqArgs eq
    sp    = panicSpan "mkCoSub"
    eTs   = sortExpr sp env <$> es
    coSub = mkCoSub env eTs ts

mkCoSub :: SEnv Sort -> [Sort] -> [Sort] -> Vis.CoSub
mkCoSub env eTs xTs = M.fromList [ (x, unite ys) | (x, ys) <- Misc.groupList xys ] 
  where
    unite ts    = Mb.fromMaybe (uError ts) (unifyTo1 senv ts)
    senv        = mkSearchEnv env
    uError ts   = panic ("mkCoSub: cannot build CoSub for " ++ showpp xys ++ " cannot unify " ++ showpp ts) 
    xys         = Misc.sortNub $ concat $ zipWith matchSorts _xTs _eTs
    (_xTs,_eTs) = (xTs, eTs)

matchSorts :: Sort -> Sort -> [(Symbol, Sort)]
matchSorts s1 s2 = go s1 s2
  where
    go (FObj x)      {-FObj-} y    = [(x, y)]
    go (FAbs _ t1)   (FAbs _ t2)   = go t1 t2
    go (FFunc s1 t1) (FFunc s2 t2) = go s1 s2 ++ go t1 t2
    go (FApp s1 t1)  (FApp s2 t2)  = go s1 s2 ++ go t1 t2
    go _             _             = []

--------------------------------------------------------------------------------

eqArgNames :: Equation -> [Symbol]
eqArgNames = map fst . eqArgs

evalBool :: Knowledge -> Expr -> EvalST (Maybe Expr) 
evalBool γ e = do 
  bt <- liftIO $ isValid γ e
  if bt then return $ Just PTrue 
   else do 
    bf <- liftIO $ isValid γ (PNot e)
    if bf then return $ Just PFalse 
          else return Nothing 

evalIte :: Knowledge -> ICtx -> Expr -> Expr -> Expr -> Expr -> EvalST Expr
evalIte γ ctx _ b0 e1 e2 = do 
  b <- eval γ ctx [b0]
  b'  <- liftIO $ (mytracepp ("evalEIt POS " ++ showpp b) <$> isValid γ b)
  nb' <- liftIO $ (mytracepp ("evalEIt NEG " ++ showpp (PNot b)) <$> isValid γ (PNot b))
  if b' 
    then return $ e1 
    else if nb' then return $ e2 
    else return $ EIte b e1 e2  

--------------------------------------------------------------------------------
-- | Knowledge (SMT Interaction)
--------------------------------------------------------------------------------
data Knowledge = KN 
  { knSims    :: ![Rewrite]           -- ^ Rewrite rules came from match and data type definitions 
  , knAms     :: ![Equation]          -- ^ All function definitions
  , knContext :: SMT.Context
  , knPreds   :: SMT.Context -> [(Symbol, Sort)] -> Expr -> IO Bool
  , knLams    :: ![(Symbol, Sort)]
  , knSummary :: ![(Symbol, Int)]      -- summary of functions to be evaluates (knSims and knAsms) with their arity
  , knDCs     :: !(S.HashSet Symbol)     -- data constructors drawn from Rewrite 
  , knSels    :: !(SelectorMap) 
  , knConsts  :: !(ConstDCMap)
  , knAutoRWs :: M.HashMap SubcId [AutoRewrite]
  }

isValid :: Knowledge -> Expr -> IO Bool
isValid γ e = do 
  contra <- knPreds γ (knContext γ) (knLams γ) PFalse
  if contra 
    then return False 
    else knPreds γ (knContext γ) (knLams γ) e

knowledge :: Config -> SMT.Context -> SInfo a -> Knowledge
knowledge cfg ctx si = KN 
  { knSims    = sims 
  , knAms     = aenvEqs aenv
  , knContext = ctx 
  , knPreds   = askSMT  cfg 
  , knLams    = [] 
  , knSummary =    ((\s -> (smName s, 1)) <$> sims) 
                ++ ((\s -> (eqName s, length (eqArgs s))) <$> aenvEqs aenv)
  , knDCs     = S.fromList (smDC <$> sims) 
  , knSels    = Mb.catMaybes $ map makeSel  sims 
  , knConsts  = Mb.catMaybes $ map makeCons sims 
  , knAutoRWs = aenvAutoRW aenv
  } 
  where 
    sims = aenvSimpl aenv ++ concatMap reWriteDDecl (ddecls si) 
    aenv = ae si 

    makeCons rw 
      | null (syms $ smBody rw)
      = Just (smName rw, (smDC rw, smBody rw))
      | otherwise
      = Nothing 

    makeSel rw 
      | EVar x <- smBody rw
      = (smName rw,) . (smDC rw,) <$> L.elemIndex x (smArgs rw)
      | otherwise 
      = Nothing 

reWriteDDecl :: DataDecl -> [Rewrite]
reWriteDDecl ddecl = concatMap go (ddCtors ddecl) 
  where 
    go (DCtor f xs) = zipWith (\r i -> SMeasure r f' ys (EVar (ys!!i)) ) rs [0..]
       where 
        f'  = symbol f 
        rs  = (val . dfName) <$> xs  
        mkArg ws = zipWith (\_ i -> intSymbol (symbol ("darg"::String)) i) ws [0..]
        ys  = mkArg xs 

askSMT :: Config -> SMT.Context -> [(Symbol, Sort)] -> Expr -> IO Bool
askSMT cfg ctx bs e
  | isTautoPred  e     = return True
  | null (Vis.kvars e) = SMT.checkValidWithContext ctx [] PTrue e'
  | otherwise          = return False
  where 
    e'                 = toSMT "askSMT" cfg ctx bs e 

toSMT :: String ->  Config -> SMT.Context -> [(Symbol, Sort)] -> Expr -> Pred
toSMT msg cfg ctx bs e = defuncAny cfg senv . elaborate "makeKnowledge" (elabEnv bs) . mytracepp ("toSMT from " ++ msg ++ showpp e)
                          $ e 
  where
    elabEnv      = insertsSymEnv senv
    senv         = SMT.ctxSymEnv ctx


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

withCtx :: Config -> FilePath -> SymEnv -> (SMT.Context -> IO a) -> IO a
withCtx cfg file env k = do
  ctx <- SMT.makeContextWithSEnv cfg file env
  _   <- SMT.smtPush ctx
  res <- k ctx
  _   <- SMT.cleanupContext ctx
  return res


-- (sel_i, D, i), meaning sel_i (D x1 .. xn) = xi, 
-- i.e., sel_i selects the ith value for the data constructor D  
type SelectorMap = [(Symbol, (Symbol, Int))]
type ConstDCMap = [(Symbol, (Symbol, Expr))]

-- ValueMap maps expressions to constants (including data constructors)
type ConstMap = M.HashMap Expr Expr
type LDataCon = Symbol              -- Data Constructors 

isSimplification :: S.HashSet LDataCon -> (Expr,Expr) -> Bool 
isSimplification dcs (_,c) = isConstant dcs c 
  

isConstant :: S.HashSet LDataCon -> Expr -> Bool 
isConstant dcs e = S.null (S.difference (S.fromList $ syms e) dcs) 

class Simplifiable a where 
  simplify :: Knowledge -> ICtx -> a -> a 


instance Simplifiable Expr where 
  simplify γ ictx e = mytracepp ("simplification of " ++ showpp e) $ fix (Vis.mapExpr tx) e
    where 
      fix f e = if e == e' then e else fix f e' where e' = f e 
      tx e 
        | Just e' <- M.lookup e (icSimpl ictx)
        = e' 
      tx (EApp (EVar f) a)
        | Just (dc, c)  <- L.lookup f (knConsts γ) 
        , (EVar dc', _) <- splitEApp a
        , dc == dc' 
        = c
      tx (EIte b e1 e2)
        | isTautoPred b  = e1 
        | isContraPred b = e2
      tx (ECoerc s t e)
        | s == t = e 
      tx (EApp (EVar f) a)
        | Just (dc, i)  <- L.lookup f (knSels γ) 
        , (EVar dc', es) <- splitEApp a
        , dc == dc' 
        = es!!i
      tx e = e  



-------------------------------------------------------------------------------
-- | Normalization of Equation: make their arguments unique -------------------
-------------------------------------------------------------------------------

class Normalizable a where 
  normalize :: a -> a 

instance Normalizable (GInfo c a) where 
  normalize si = si {ae = normalize $ ae si}

instance Normalizable AxiomEnv where 
  normalize aenv = aenv { aenvEqs   = mytracepp "aenvEqs"  (normalize <$> aenvEqs   aenv)
                        , aenvSimpl = mytracepp "aenvSimpl" (normalize <$> aenvSimpl aenv) }

instance Normalizable Rewrite where 
  normalize rw = rw { smArgs = xs', smBody = normalizeBody (smName rw) $ subst su $ smBody rw }
    where 
      su  = mkSubst $ zipWith (\x y -> (x,EVar y)) xs xs'
      xs  = smArgs rw 
      xs' = zipWith mkSymbol xs [0..]
      mkSymbol x i = x `suffixSymbol` intSymbol (smName rw) i 


instance Normalizable Equation where 
  normalize eq = eq {eqArgs = zip xs' ss, eqBody = normalizeBody (eqName eq) $ subst su $ eqBody eq }
    where 
      su      = mkSubst $ zipWith (\x y -> (x,EVar y)) xs xs'
      (xs,ss) = unzip (eqArgs eq) 
      xs'     = zipWith mkSymbol xs [0..]
      mkSymbol x i = x `suffixSymbol` intSymbol (eqName eq) i 


normalizeBody :: Symbol -> Expr -> Expr
normalizeBody f = go   
  where 
    go e 
      | any (== f) (syms e) 
      = go' e 
    go e 
      = e 
    
    go' (PAnd [PImp c e1,PImp (PNot c') e2])
      | c == c' = EIte c e1 (go' e2)
    go' e = e 

_splitBranches :: Symbol -> Expr -> [(Expr, Expr)]
_splitBranches f = go   
  where 
    go (PAnd es) 
      | any (== f) (syms es) 
      = go' <$> es
    go e 
      = [(PTrue, e)]

    go' (PImp c e) = (c, e) 
    go' e          = (PTrue, e)

