--------------------------------------------------------------------------------
-- | This module implements "Proof by Logical Evaluation" where we 
--   unfold function definitions if they *must* be unfolded, to strengthen
--   the environments with function-definition-equalities. 
--   The algorithm is discussed at length in:
-- 
--     1. "Refinement Reflection", POPL 2018, https://arxiv.org/pdf/1711.03842
--     2. "Reasoning about Functions", VMCAI 2018, https://ranjitjhala.github.io/static/reasoning-about-functions.pdf 
--------------------------------------------------------------------------------

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
import qualified Data.HashMap.Strict  as M
import qualified Data.HashSet         as S
import qualified Data.List            as L
import qualified Data.Maybe           as Mb 
import           Debug.Trace          (trace)

mytracepp :: (PPrint a) => String -> a -> a
mytracepp = notracepp

traceE :: (Expr,Expr) -> (Expr,Expr)
traceE (e,e') 
  | False -- True 
  , e /= e' 
  = trace ("\n" ++ showpp e ++ " ~> " ++ showpp e') (e,e') 
  | otherwise 
  = (e,e')

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
    s0                = EvalEnv (SMT.ctxSymEnv ctx) mempty mempty

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

evalCandsLoop :: Config -> ICtx -> SMT.Context -> Knowledge -> EvalEnv -> IO ICtx 
evalCandsLoop cfg ictx0 ctx γ env = go ictx0 
  where
    withRewrites exprs =
      let
        rws = [rewrite e rw | rw <- knSims γ
                            ,  e <- S.toList (snd `S.map` exprs)]
      in 
        exprs <> S.fromList (concat rws)
    go ictx | S.null (icCands ictx) = return ictx 
    go ictx =  do let cands = icCands ictx
                  let env' = env {  evAccum    = icEquals   ictx <> evAccum env
                                 ,  evRewrites = icRewrites ictx <> evRewrites env
                                 }
                  evalResults   <- SMT.smtBracket ctx "PLE.evaluate" $ do
                               SMT.smtAssert ctx (pAnd (S.toList $ icAssms ictx)) 
                               mapM (evalOne γ env' ictx) (S.toList cands)
                  let (EvalOneResult us autorws) = mconcat evalResults 
                  if S.null (us `S.difference` icEquals ictx) && S.null (autorws `S.difference` icRewrites ictx)
                        then return ictx 
                        else do  let oks      = fst `S.map` us
                                 let autorws' = withRewrites autorws
                                 let us'      = withRewrites us 
                                 let eqsSMT   = evalToSMT "evalCandsLoop" cfg ctx `S.map` (us <> autorws)
                                 let ictx'    = ictx { icSolved = icSolved ictx <> oks 
                                                     , icEquals = icEquals ictx <> us'
                                                     , icRewrites = icRewrites ictx <> autorws'

                                                     , icAssms  = icAssms  ictx <> S.filter (not . isTautoPred) eqsSMT }
                                 let newcands = mconcat ((makeCandidates γ ictx') <$> (S.toList (cands <> (snd `S.map` (us <> autorws)))))
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
  , icEquals   :: S.HashSet (Expr,Expr)     -- ^ Accumulated equalities
  , icSolved   :: S.HashSet Expr            -- ^ Terms that we have already expanded
  , icSimpl    :: !ConstMap                 -- ^ Map of expressions to constants
  , icSubcId   :: Maybe SubcId              -- ^ Current subconstraint ID
  , icRewrites :: S.HashSet (Expr,Expr)     -- ^ User-generated rewrites
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
  , icEquals   = S.fromList es  
  , icSolved   = mempty
  , icSimpl    = mempty 
  , icSubcId   = Nothing
  , icRewrites = mempty
  }

equalitiesPred :: S.HashSet (Expr, Expr) -> [Expr]
equalitiesPred eqs = [ EEq e1 e2 | (e1, e2) <- S.toList eqs, e1 /= e2 ] 

updCtxRes :: InstRes -> Maybe BindId -> ICtx -> (ICtx, InstRes) 
updCtxRes res iMb ctx = (ctx, res')
  where 
    res' = updRes res iMb (pAnd $ equalitiesPred $ (icRewrites ctx <> icEquals ctx )) 


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
                    , icEquals = initEqs                    <> icEquals ctx
                    , icSimpl  = M.fromList (S.toList sims) <> icSimpl ctx <> econsts
                    , icSubcId = cidMb
                    }
  where         
    initEqs   = S.fromList $ concat [rewrite e rw | e  <- (cands ++ (snd <$> S.toList (icEquals ctx)))
                                                  , rw <- knSims ieKnowl]
    cands     = concatMap (makeCandidates ieKnowl ctx) (rhs:es)
    sims      = S.filter (isSimplification (knDCs ieKnowl)) (initEqs <> icEquals ctx)
    econsts   = M.fromList $ findConstants ieKnowl es
    ctxEqs    = toSMT "updCtx" ieCfg ieSMT [] <$> L.nub (concat 
                  [
                    equalitiesPred (icRewrites ctx)
                  , equalitiesPred initEqs 
                  , equalitiesPred sims 
                  , equalitiesPred (icEquals ctx)
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
  = length es == i
  | otherwise
  = False 
    



getCstr :: M.HashMap SubcId (SimpC a) -> SubcId -> SimpC a 
getCstr env cid = Misc.safeLookup "Instantiate.getCstr" cid env

isPleCstr :: AxiomEnv -> SubcId -> SimpC a -> Bool
isPleCstr aenv sid c = isTarget c && M.lookupDefault False sid (aenvExpand aenv) 


--------------------------------------------------------------------------------
data EvalEnv = EvalEnv
  { evEnv      :: !SymEnv
  , evAccum    :: S.HashSet (Expr, Expr)
  , evRewrites :: S.HashSet (Expr, Expr)
  }

type EvalST a = StateT EvalEnv IO a
--------------------------------------------------------------------------------

data EvalOneResult = EvalOneResult (S.HashSet (Expr, Expr)) (S.HashSet (Expr, Expr))

evalOne :: Knowledge -> EvalEnv -> ICtx -> Expr -> IO EvalOneResult
evalOne γ env ctx e = do
  (e',st) <- runStateT (eval γ ctx e) env 
  let pleAccum = if e' == e then evAccum st else S.insert (e, e') (evAccum st)
  return $ EvalOneResult pleAccum (evRewrites st)

instance Semigroup EvalOneResult where
  (EvalOneResult ac rw) <> (EvalOneResult ac' rw') = EvalOneResult (ac <> ac') (rw <> rw')
  
instance Monoid EvalOneResult where
  mempty = EvalOneResult mempty mempty

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

getRewrites :: Knowledge -> SymEnv -> Expr -> AutoRewrite -> IO [Expr]
getRewrites γ symEnv expr@(EApp lhs rhs) ar = do
  base   <- runMaybeT (getRewrite γ symEnv expr ar)
  lhs'   <- getRewrites γ symEnv lhs ar
  rhs'   <- getRewrites γ symEnv rhs ar
  return $ Mb.maybeToList base
    ++ [ EApp l r | l <- lhs:lhs'
                  , r <- rhs:rhs'
                  , l /= lhs || r /= rhs]

getRewrites γ symEnv expr ar =
  Mb.maybeToList <$> runMaybeT (getRewrite γ symEnv expr ar)

multiSetRpoGTE :: [Equation] -> [Expr] -> [Expr] -> Bool
multiSetRpoGTE _   _  []    =  True
multiSetRpoGTE _   [] (_:_) =  False
multiSetRpoGTE eqs xs ys =
  let
    xs' = filter (\x -> all (\y -> rpoGTE eqs x y) ys) xs
    ys' = filter (\y -> all (\x -> rpoGTE eqs y x) xs) ys
  in
    if
      length xs' > length ys' then True
    else
      if
        length ys' > length xs' then False
      else
        if length xs' == 0 && length ys' == 0
        then True
        else multiSetRpoGTE eqs (xs L.\\ xs') (ys L.\\ ys')

isSubTerm :: Expr -> Expr -> Bool
isSubTerm e (PAnd xs)       = any (\x -> x == e || isSubTerm e x) xs
isSubTerm e (EIte xx yy zz) = any (\x -> x == e || isSubTerm e x) [xx,yy,zz]
isSubTerm e (EApp f xs)     = any (\x -> x == e || isSubTerm e x) [f, xs]
isSubTerm _ _ = False
  
rpoGTE ::  [Equation] -> Expr -> Expr -> Bool
rpoGTE _ e e' | e' `isSubTerm` e      = True
rpoGTE _ e e' | e == e'               = True
rpoGTE _ e e' | e `isSubTerm`  e'     = False
rpoGTE _ _ (ESym _)                   = True
rpoGTE _ _ (ECon _)                   = True
rpoGTE _ _ (EVar _)                   = True
rpoGTE _ _ PTrue                      = True
rpoGTE eqs e (PAtom _ x y)            = multiSetRpoGTE eqs [e] [x,y]
rpoGTE eqs e (EIte x y z)             = multiSetRpoGTE eqs [e] [x,y,z]
rpoGTE eqs e            e'@(EApp _ _) = rpoGTEApp eqs e e'
rpoGTE eqs e@(EApp _ _) e'            = rpoGTEApp eqs e e'
rpoGTE _   e e' = error (show e ++ "\n\n---\n\n" ++ show e')

getSymbols :: [Equation] -> Symbol -> [Symbol]
getSymbols eqs s
  | Just eq <- L.find ((== s) . eqName) eqs =
      syms (eqBody eq)
  | otherwise = []

rpoGTEApp :: [Equation] -> Expr -> Expr -> Bool
rpoGTEApp eqs e e' =
  let
    (f, xs) = splitEApp e
    (g, ys) = splitEApp e'
  in
    if f == g
    then multiSetRpoGTE eqs xs ys
    else 
      case (f,g) of
        ((EVar f'),(EVar g')) | g' `notElem` getSymbols eqs f'
                            &&  f' `notElem` getSymbols eqs g'
                            &&  f' < g' ->
                                multiSetRpoGTE eqs [e] ys
        ((EVar f'),(EVar g')) | g' `elem`    getSymbols eqs f'
                            &&  f' `notElem` getSymbols eqs g' ->
             multiSetRpoGTE eqs [e] ys                      
        _ -> multiSetRpoGTE eqs xs  [e']
  

getRewrite :: Knowledge -> SymEnv -> Expr -> AutoRewrite -> MaybeT IO Expr
getRewrite γ symEnv expr (AutoRewrite args lhs rhs) =
  do
    su@(Su suMap) <- MaybeT $ return $ unify freeVars lhs expr
    let expr' = subst su rhs
    guard $ expr /= expr'
    guard $ rpoGTE (knAms γ) expr expr'
    let (argSorts', exprSorts') = sortsToUnify (M.toList suMap)
    let (argSorts, exprSorts)   = (gSorts argSorts', gSorts exprSorts')
    checkSorts argSorts exprSorts
    mapM_ (check . subst su) exprs
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


eval :: Knowledge -> ICtx -> Expr -> EvalST Expr
eval _ ctx e
  | Just v <- M.lookup e (icSimpl ctx)
  = return v
eval γ ctx e =
  do acc       <- S.toList . evAccum <$> get
     alreadyRW <- gets evRewrites
     case L.lookup e acc of
        Just e' -> eval γ ctx e'
        _ -> do
          e'  <- simplify γ ctx <$> go e
          rws <- getRWs e
          let alreadyRW' = S.union alreadyRW (S.fromList $ map (e,) rws)
          if e /= e'
            then do modify (\st -> st { evAccum = S.insert (traceE (e, e')) (evAccum st)
                                      , evRewrites = alreadyRW' })
                    eval γ (addConst (e,e') ctx) e'
            else do modify (\st -> st { evRewrites = alreadyRW' })
                    return e
  where
    autorws  =
      Mb.fromMaybe [] $ do
        cid <- icSubcId ctx
        M.lookup cid $ knAutoRWs γ

    getRWs :: Expr -> EvalST [Expr]
    getRWs e = do
      env <- gets evEnv
      concat <$> mapM (liftIO . getRewrites γ env e) autorws

    addConst (e,e') ctx = if isConstant (knDCs γ) e'
                           then ctx { icSimpl = M.insert e e' $ icSimpl ctx} else ctx 
    go (ELam (x,s) e)   = ELam (x, s) <$> eval γ' ctx e where γ' = γ { knLams = (x, s) : knLams γ }
    go e@(EIte b e1 e2) = evalIte γ ctx e b e1 e2
    go (ECoerc s t e)   = ECoerc s t  <$> go e
    go e@(EApp _ _)     = case splitEApp e of 
                           (f, es) -> do (f':es') <- mapM (eval γ ctx) (f:es) 
                                         evalApp γ (eApps f' es) (f',es')
    go e@(PAtom r e1 e2) = fromMaybeM (PAtom r <$> go e1 <*> go e2) (evalBool γ e)
    go (ENeg e)         = do e'  <- eval γ ctx e
                             return $ ENeg e'
    go (EBin o e1 e2)   = do e1' <- eval γ ctx e1 
                             e2' <- eval γ ctx e2 
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
  , length (eqArgs eq) == length es 
  = do env <- seSort <$> gets evEnv
       return $ substEq env eq es

evalApp γ _ (EVar f, [e]) 
  | (EVar dc, as) <- splitEApp e
  , Just rw <- L.find (\rw -> smName rw == f && smDC rw == dc) (knSims γ)
  , length as == length (smArgs rw)
  = return $ subst (mkSubst $ zip (smArgs rw) as) (smBody rw)

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
  b <- eval γ ctx b0 
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

