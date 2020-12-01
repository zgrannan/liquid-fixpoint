--------------------------------------------------------------------------------
-- | This module implements "Proof by Logical Evaluation" where we 
--   unfold function definitions if they *must* be unfolded, to strengthen
--   the environments with function-definition-equalities. 
--   The algorithm is discussed at length in:
-- 
--     1. "Refinement Reflection", POPL 2018, https://arxiv.org/pdf/1711.03842
--     2. "Reasoning about Functions", VMCAI 2018, https://ranjitjhala.github.io/static/reasoning-about-functions.pdf 
--------------------------------------------------------------------------------

{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ExistentialQuantification #-}

module Language.Fixpoint.Solver.PLE (instantiate, pleID', reify) where

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
import           Language.Fixpoint.Solver.Rewrite
import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import qualified Data.HashMap.Strict  as M
import qualified Data.HashSet         as S
import qualified Data.List            as L
import qualified Data.Maybe           as Mb
import           Data.Text (splitOn, unpack)
import           Debug.Trace          (trace)
import Text.Printf (printf)
import Data.Hashable (Hashable(hash))

mytracepp :: (PPrint a) => String -> a -> a
mytracepp = notracepp

traceE :: (Expr,Expr) -> (Expr,Expr)
traceE (e,e')
  | isEnabled
  , e /= e'
  = trace ("\n" ++ showpp e ++ " ~> " ++ showpp e') (e,e')
  | otherwise
  = (e,e')
  where
    isEnabled :: Bool
    isEnabled = False

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
instEnv cfg fi cs ctx = InstEnv cfg ctx bEnv aEnv cs γ s0
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
evalCandsLoop cfg ictx0 ctx γ env = go mempty ictx0
  where
    withRewrites exprs =
      let
        rws = [rewrite e rw | rw <- knSims γ
                            ,  e <- S.toList (snd `S.map` exprs)]
      in
        exprs <> (S.fromList $ concat rws)
    showProof ictx facts =
      case icSubcId ictx0 of
        Just cid | S.member cid (knShowProofs γ) ->
          liftIO $ putStrLn (generateEqs γ ictx facts)
        _ -> return ()
    go facts ictx | S.null (icCands ictx) = showProof ictx facts >> return ictx
    go facts ictx = do
                  let cands = icCands ictx
                  let env' = env {  evAccum    = icEquals   ictx <> evAccum env }
                  evalResults <- SMT.smtBracket ctx "PLE.evaluate" $ do
                               SMT.smtAssert ctx (pAnd (S.toList $ icAssms ictx))
                               mapM (evalOne γ env' ictx) (S.toList cands)
                  let (facts', us) = mconcat evalResults
                  if S.null (us `S.difference` icEquals ictx)
                        then showProof ictx facts >> return ictx
                        else do  let oks      = fst `S.map` us
                                 let us'      = withRewrites us
                                 let eqsSMT   = evalToSMT "evalCandsLoop" cfg ctx `S.map` us'
                                 let ictx'    = ictx { icSolved = icSolved ictx <> oks
                                                     , icEquals = icEquals ictx <> us'
                                                     , icAssms  = icAssms  ictx <> S.filter (not . isTautoPred) eqsSMT }
                                 let newcands = mconcat (makeCandidates γ ictx' <$> S.toList (cands <> (snd `S.map` us)))
                                 go (S.union facts facts') (ictx' { icCands = S.fromList newcands})



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
  , ieCstrs :: ![(SubcId, SimpC a)]
  , ieKnowl :: !Knowledge
  , ieEvEnv :: !EvalEnv
  }

---------------------------------------------------------------------------------------------- 
-- | @ICtx@ is the local information -- at each trie node -- obtained by incremental PLE
---------------------------------------------------------------------------------------------- 

data ICtx    = ICtx
  { icAssms     :: S.HashSet Pred            -- ^ Equalities converted to SMT format
  , icCands     :: S.HashSet Expr            -- ^ "Candidates" for unfolding
  , icEquals    :: EvAccum                   -- ^ Accumulated equalities
  , icSolved    :: S.HashSet Expr            -- ^ Terms that we have already expanded
  , icSimpl     :: !ConstMap                 -- ^ Map of expressions to constants
  , icSubcId    :: Maybe SubcId              -- ^ Current subconstraint ID
  , icPLEEquals :: S.HashSet Expr            -- ^ The PLE facts
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
  }

equalitiesPred :: S.HashSet (Expr, Expr) -> [Expr]
equalitiesPred eqs = [ EEq e1 e2 | (e1, e2) <- S.toList eqs, e1 /= e2 ]


pleID' = PAtom Eq (ECst (EBin Plus (ECst (ECon (I 1)) FInt) (ECst (ECon (I 2)) FInt)) FInt) (ECst (EBin Plus (ECst (ECon (I 11111111111)) FInt) (ECst (ECon (I 2)) FInt)) FInt)

pleID :: Expr
pleID = EEq
        (EBin Plus (ECon (I 1)) (ECon (I 2)))
        (EBin Plus (ECon (I 11111111111)) (ECon (I 2)))

updCtxRes :: InstRes -> Maybe BindId -> ICtx -> (ICtx, InstRes)
updCtxRes res iMb ctx = (ctx, res')
  where
    res' = updRes res iMb (pAnd $ map asPLECons $ equalitiesPred $ icEquals ctx)
    asPLECons eq = POr [pleID, eq]


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
                    , icSubcId = fst <$> L.find (\(_, b) -> (head delta) `memberIBindEnv` (_cenv b)) ieCstrs
                    }
  where
    initEqs   = S.fromList $ concat [rewrite e rw | e  <- (cands ++ (snd <$> S.toList (icEquals ctx)))
                                                  , rw <- knSims ieKnowl]
    cands     = concatMap (makeCandidates ieKnowl ctx) (rhs:es)
    sims      = S.filter (isSimplification (knDCs ieKnowl)) (initEqs <> icEquals ctx)
    econsts   = M.fromList $ findConstants ieKnowl es
    ctxEqs    = toSMT "updCtx" ieCfg ieSMT [] <$> L.nub (concat
                  [ equalitiesPred initEqs
                  , equalitiesPred sims
                  , equalitiesPred (icEquals ctx)
                  , [ expr xr   | xr@(_, r) <- bs, null (Vis.kvars r) ]
                  ])
    bs        = unElab <$> binds
    (rhs:es)  = unElab <$> (eRhs : (expr <$> binds))
    eRhs      = maybe PTrue crhs subMb
    binds     = [ lookupBindEnv i ieBEnv | i <- delta ]
    subMb     = getCstr (M.fromList ieCstrs) <$> cidMb


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

type EvAccum = S.HashSet (Expr, Expr)

type Facts  = S.HashSet (Expr, Expr)

insertFact :: Expr -> Expr -> Facts -> Facts
insertFact e@(EEq (ECon _) (ECon _)) _ f = f -- error (show e)
insertFact e e'                        f = S.insert (e, e') f

--------------------------------------------------------------------------------
data EvalEnv = EvalEnv
  { evEnv      :: !SymEnv
  , evAccum    :: EvAccum
  , evFacts    :: Facts
  }

type EvalST a = StateT EvalEnv IO a
--------------------------------------------------------------------------------


getAutoRws :: Knowledge -> ICtx -> [AutoRewrite]
getAutoRws γ ctx =
  Mb.fromMaybe [] $ do
    cid <- icSubcId ctx
    M.lookup cid $ knAutoRWs γ

testStr :: Symbol -> String
testStr test = if symbolString test == "GHC.Types.[]" then"[]" else symbolString test ++ "{}"

type Constructors = M.HashMap String Int


data ReifyContext = ReifyContext
  {  rSplitLists :: S.HashSet Expr
  ,  rParens     :: Bool
  }

parens :: ReifyContext -> String -> String
parens rc s =
  if rParens rc
  then printf "(%s)" s
  else s

reifyP' :: ReifyContext -> Expr -> String
reifyP' rc = reify' rc{rParens=True}

reifyNP' :: ReifyContext -> Expr -> String
reifyNP' rc = reify' rc{rParens=False}

withListSplit :: Expr -> ReifyContext -> ReifyContext
withListSplit e rc = rc{rSplitLists = S.insert e (rSplitLists rc)}

patternHead :: Expr -> String
patternHead s = printf "head_%s" (show $ abs $ hash s)

patternTail :: Expr -> String
patternTail s = printf "tail_%s" (show $ abs $ hash s)

reify' :: ReifyContext -> Expr -> String
reify' rc (EApp (EVar f) x )
  | Just c <- stripPrefix "lqdc##$select##" f
  , [name, index] <- splitOn "##" (symbolText c)
  , name == "GHC.Types.:"
  , S.member x (rSplitLists rc)
  = if index == "1" then patternHead x else patternTail x
reify' rc (EApp (EVar f) x )
  | Just c <- stripPrefix "lqdc##$select##" f
  = let [name, index] = splitOn "##" (symbolText c)
    in parens rc $ "case " ++ reify' rc x ++ " of {" ++ unpack name ++ " x -> x }"
reify' rc (EApp (EVar f) x)  | Just test <- unTestSymbol f =
  parens rc $ "case " ++ reify' rc x ++ " of { " ++ testStr test ++ " -> True ; _ -> False }"
reify' rc e@(EApp _ _) =
  let (f, args) = splitEApp e
  in parens rc $ unwords (reifyP' rc f : map (reifyP' rc) args)
reify' _ (EVar x)            = takeWhile (/= '#') $ symbolString x
reify' _ (ECon (I c))        = show c
reify' _ PFalse              = "False"
reify' _ PTrue               = "True"
reify' rc (EBin op t1 t2) =
  parens rc $ printf "%s %s %s" (reifyP' rc t1) (show $ toFix op) (reifyP' rc t2)

reify' rc (EIte (EApp (EVar f) x) t e) | Just "GHC.Types.[]" <- unTestSymbol f =
  parens rc $ printf
    "case %s of { [] -> %s ; ( %s : %s) -> %s }"
    (reifyP' rc x)
    (reify' rc t)
    (patternHead x)
    (patternTail x)
    (reify' (withListSplit x rc) e)

reify' rc ee@(EIte (EApp (EVar f) x) t e) | Just test <- unTestSymbol f =
  show (toFix ee)
  -- parens rc $ printf
  --   "case %s of { %s -> %s ; _ -> %s }"
  --   (reifyP' rc x) (testStr test) (reifyNP' rc t) (reifyNP' rc e)

reify' rc (EIte i t e) =
  parens rc $ printf "if %s then %s else %s" (reify' rc i) (reify' rc t) (reify' rc e)
reify' rc (PAtom op lhs rhs)  =
  parens rc $ printf "%s %s %s" (reify' rc lhs) (opString op) (reify' rc rhs)
    where
      opString :: Brel -> String
      opString Eq = "=="
      opString Ne = "/="
      opString op = show (toFix op)
reify' _ e                  = error (show e)

reify :: Expr -> String
reify = reify' (ReifyContext S.empty False)

uselessPatternMatch :: Knowledge -> Expr -> Bool
uselessPatternMatch γ (EApp (EVar f) arg) | (EVar g, _) <- splitEApp arg =
  isTestSymbol f && S.member g (knDCs γ)
uselessPatternMatch _ _ = False

normalForm :: Expr -> Facts -> Expr
normalForm e0 f = nf [e0] where
  nf :: [Expr] -> Expr
  nf [] = undefined
  nf path@(e:_) = case S.toList (S.filter (\(lhs, rhs) -> lhs == e && rhs /= e) f) of
    [(_, e')] | L.notElem e' path -> nf (e':path)
    []                            -> e
    _                             -> error "Nonterminating?"


{-
The algorithm:

1. Run `simplify` on all facts (for constant folding, selector elimination, etc)
2. For each fact, evaluate it to it's "normal form" (i.e the PLE fixpoint)
3. Re-simplify the facts, in case the normal form enables new simplifications
4. Eliminate redundant facts (useless pattern matches, x == x)
-}
generateEqs :: Knowledge -> ICtx -> Facts -> String
generateEqs γ ictx facts = L.intercalate " ?\n" (S.toList (S.map toEq usefulFacts))
  where
    simplifyEQ (lhs, rhs) =
      let
        rhs'    = Vis.mapExpr (flip normalForm facts') rhs
        factsL  = S.filter ((/=) lhs . fst) facts'
        lhs'    = Vis.mapExpr (flip normalForm factsL) lhs
      in
        (simplify γ ictx lhs', simplify γ ictx rhs')
    both f (x,y)      = (f x, f y)
    facts'            = S.map (both $ simplify γ ictx) facts
    simplified        = S.map simplifyEQ facts'
    usefulFacts       = S.filter canUse simplified
    canUse (lhs, rhs) = not (uselessPatternMatch γ lhs || uselessPatternMatch γ rhs || lhs == rhs)
    toEq (lhs, rhs)   = "(" ++ reify lhs ++ " ==. " ++ reify rhs ++ ")"

type EvalOneResult = (Facts, EvAccum)

evalOne :: Knowledge -> EvalEnv -> ICtx -> Expr -> IO EvalOneResult
-- evalOne γ env ctx e | null $ getAutoRws γ ctx = do
--     (e',st) <- runStateT (fastEval γ ctx e) env
--     return (evFacts st, evAccum st)
evalOne γ env ctx e = do
  result <- execStateT (eval γ ctx [(e, PLE)]) env
  return (evFacts result, evAccum result)

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



subsFromAssm :: Expr -> [(Symbol, Expr)]
subsFromAssm (PAnd es)                                   = concatMap subsFromAssm es
subsFromAssm (EEq lhs rhs) | (EVar v) <- unElab lhs
                           , anfPrefix `isPrefixOfSym` v = [(v, unElab rhs)]
subsFromAssm _                                           = []

fastEval :: Knowledge -> ICtx -> Expr -> EvalST Expr
fastEval _ ctx e
  | Just v <- M.lookup e (icSimpl ctx)
  = return v

fastEval γ ctx e =
  do acc       <- S.toList . evAccum <$> get
     case L.lookup e acc of
        Just e' -> fastEval γ ctx e'
        _ -> do
          e'  <- simplify γ ctx <$> go e
          if e /= e'
            then do
                    modify (\st -> st { evAccum = S.insert (traceE (e, e')) (evAccum st)
                                      , evFacts = insertFact e e' (evFacts st)
                                      })
                    fastEval γ (addConst (e,e') ctx) e'
            else return e
  where
    addConst (e,e') ctx = if isConstant (knDCs γ) e'
                           then ctx { icSimpl = M.insert e e' $ icSimpl ctx} else ctx
    go (ELam (x,s) e)   = ELam (x, s) <$> fastEval γ' ctx e where γ' = γ { knLams = (x, s) : knLams γ }
    go e@(EIte b e1 e2) = fastEvalIte γ ctx e b e1 e2
    go (ECoerc s t e)   = ECoerc s t  <$> go e
    go e@(EApp _ _)     = case splitEApp e of
                           (f, es) -> do (f':es') <- mapM (fastEval γ ctx) (f:es)
                                         evalApp γ ctx (eApps f' es) (f',es')
    go e@(PAtom r e1 e2) = fromMaybeM (PAtom r <$> go e1 <*> go e2) (evalBool γ e)
    go (ENeg e)         = do e'  <- fastEval γ ctx e
                             return $ ENeg e'
    go (EBin o e1 e2)   = do e1' <- fastEval γ ctx e1
                             e2' <- fastEval γ ctx e2
                             return $ EBin o e1' e2'
    go (ETApp e t)      = flip ETApp t <$> go e
    go (ETAbs e s)      = flip ETAbs s <$> go e
    go e@(PNot e')      = fromMaybeM (PNot <$> go e')           (evalBool γ e)
    go e@(PImp e1 e2)   = fromMaybeM (PImp <$> go e1 <*> go e2) (evalBool γ e)
    go e@(PIff e1 e2)   = fromMaybeM (PIff <$> go e1 <*> go e2) (evalBool γ e)
    go e@(PAnd es)      = fromMaybeM (PAnd <$> (go  <$$> es))   (evalBool γ e)
    go e@(POr es)       = fromMaybeM (POr  <$> (go <$$> es))    (evalBool γ e)
    go e                = return e

eval :: Knowledge -> ICtx -> [(Expr, TermOrigin)] -> EvalST ()
eval _ ctx path
  | pathExprs <- map fst path
  , e         <- last pathExprs
  , Just v    <- M.lookup e (icSimpl ctx)
  = when (v /= e) $ modify (\st -> st { evAccum = S.insert (e, v) (evAccum st)})

eval γ ctx path =
  do
    rws <- getRWs
    e'  <- simplify γ ctx <$> evalStep γ ctx e
    let evalIsNewExpr = L.notElem e' pathExprs
    let exprsToAdd    = (if evalIsNewExpr then [e'] else []) ++ map fst rws
    let evAccum'      = S.fromList $ map (e,) $ exprsToAdd
    modify (\st -> st { evAccum = S.union evAccum' (evAccum st)})
    when evalIsNewExpr $ eval γ (addConst (e, e')) (path ++ [(e', PLE)])
    mapM_ (\rw -> (eval γ ctx) (path ++ [rw])) rws
  where
    pathExprs = map fst path
    e         = last pathExprs
    autorws   = getAutoRws γ ctx

    getRWs :: EvalST [(Expr, TermOrigin)]
    getRWs =
      let
        ints      = concatMap subsFromAssm (S.toList $ icAssms ctx)
        su        = Su (M.fromList ints)
        e'        = subst' e
        subst' ee =
          let ee' = subst su ee
          in if ee == ee' then ee else subst' ee'
        rwArgs = RWArgs (isValid γ) (knRWTerminationOpts γ)
        getRWs' s =
          Mb.catMaybes <$> mapM (liftIO . runMaybeT . getRewrite rwArgs path s) autorws
      in concat <$> mapM getRWs' (subExprs e')

    addConst (e,e') = if isConstant (knDCs γ) e'
                      then ctx { icSimpl = M.insert e e' $ icSimpl ctx} else ctx

evalStep :: Knowledge -> ICtx -> Expr -> EvalST Expr
evalStep γ ctx (ELam (x,s) e)   = ELam (x, s) <$> evalStep γ' ctx e where γ' = γ { knLams = (x, s) : knLams γ }
evalStep γ ctx e@(EIte b e1 e2) = evalIte γ ctx e b e1 e2
evalStep γ ctx (ECoerc s t e)   = ECoerc s t <$> evalStep γ ctx e
evalStep γ ctx e@(EApp _ _)     = case splitEApp e of
  (f, es) ->
    do
      f' <- evalStep γ ctx f
      if f' /= f
        then return (eApps f' es)
        else
          do
            es' <- mapM (evalStep γ ctx) es
            if es /= es'
              then return (eApps f' es')
              else evalApp γ ctx (eApps f' es') (f',es')
evalStep γ ctx e@(PAtom r e1 e2) =
  fromMaybeM (PAtom r <$> evalStep γ ctx e1 <*> evalStep γ ctx e2) (evalBool γ e)
evalStep γ ctx (ENeg e) = ENeg <$> evalStep γ ctx e
evalStep γ ctx (EBin o e1 e2)   = do
  e1' <- evalStep γ ctx e1
  if e1' /= e1
    then return (EBin o e1' e2)
    else EBin o e1 <$> evalStep γ ctx e2
evalStep γ ctx (ETApp e t)      = flip ETApp t <$> evalStep γ ctx e
evalStep γ ctx (ETAbs e s)      = flip ETAbs s <$> evalStep γ ctx e
evalStep γ ctx e@(PNot e')      = fromMaybeM (PNot <$> evalStep γ ctx e') (evalBool γ e)
evalStep γ ctx e@(PImp e1 e2)   = fromMaybeM (PImp <$> evalStep γ ctx e1 <*> evalStep γ ctx e2) (evalBool γ e)
evalStep γ ctx e@(PIff e1 e2)   = fromMaybeM (PIff <$> evalStep γ ctx e1 <*> evalStep γ ctx e2) (evalBool γ e)
evalStep γ ctx e@(PAnd es)      = fromMaybeM (PAnd <$> (evalStep γ ctx <$$> es)) (evalBool γ e)
evalStep γ ctx e@(POr es)       = fromMaybeM (POr  <$> (evalStep γ ctx <$$> es)) (evalBool γ e)
evalStep _ _   e                = return e

fromMaybeM :: (Monad m) => m a -> m (Maybe a) -> m a
fromMaybeM a ma = do
  mx <- ma
  case mx of
    Just x  -> return x
    Nothing -> a

(<$$>) :: (Monad m) => (a -> m b) -> [a] -> m [b]
f <$$> xs = f Misc.<$$> xs




evalApp :: Knowledge -> ICtx -> Expr -> (Expr, [Expr]) -> EvalST Expr
evalApp γ ctx _ (EVar f, es)
  | Just eq <- L.find ((== f) . eqName) (knAms γ)
  , length (eqArgs eq) <= length es
  = do env <- seSort <$> gets evEnv
       let (es1,es2) = splitAt (length (eqArgs eq)) es
       shortcut (substEq env eq es1) es2
  where
    shortcut (EIte i e1 e2) es2 = do
      b   <- fastEval γ ctx i
      b'  <- liftIO $ (mytracepp ("evalEIt POS " ++ showpp b) <$> isValid γ b)
      nb' <- liftIO $ (mytracepp ("evalEIt NEG " ++ showpp (PNot b)) <$> isValid γ (PNot b))
      r <- if b'
        then shortcut e1 es2
        else if nb' then shortcut e2 es2
        else return $ eApps (EIte b e1 e2) es2
      return r
    shortcut e' es2 = return $ eApps e' es2

evalApp γ _ _ (EVar f, e:es)
  | (EVar dc, as) <- splitEApp e
  , Just rw <- L.find (\rw -> smName rw == f && smDC rw == dc) (knSims γ)
  , length as == length (smArgs rw)
  = return $ eApps (subst (mkSubst $ zip (smArgs rw) as) (smBody rw)) es

evalApp _ _ e _
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

fastEvalIte :: Knowledge -> ICtx -> Expr -> Expr -> Expr -> Expr -> EvalST Expr
fastEvalIte γ ctx _ b0 e1 e2 = do
  b <- fastEval γ ctx b0
  b'  <- liftIO $ (mytracepp ("evalEIt POS " ++ showpp b) <$> isValid γ b)
  nb' <- liftIO $ (mytracepp ("evalEIt NEG " ++ showpp (PNot b)) <$> isValid γ (PNot b))
  if b'
    then return $ e1
    else if nb' then return $ e2
    else return $ EIte b e1 e2

evalIte :: Knowledge -> ICtx -> Expr -> Expr -> Expr -> Expr -> EvalST Expr
evalIte γ ctx _ b0 e1 e2 = do
  b   <- evalStep γ ctx b0
  if b /= b0 then return (EIte b e1 e2) else
    do
      b'  <- liftIO $ isValid γ b
      nb' <- liftIO $ isValid γ (PNot b)
      return $
        if b'
        then e1
        else if nb' then e2
        else EIte b e1 e2

--------------------------------------------------------------------------------
-- | Knowledge (SMT Interaction)
--------------------------------------------------------------------------------
data Knowledge = KN
  { knSims              :: ![Rewrite]           -- ^ Rewrite rules came from match and data type definitions 
  , knAms               :: ![Equation]          -- ^ All function definitions
  , knContext           :: SMT.Context
  , knPreds             :: SMT.Context -> [(Symbol, Sort)] -> Expr -> IO Bool
  , knLams              :: ![(Symbol, Sort)]
  , knSummary           :: ![(Symbol, Int)]      -- summary of functions to be evaluates (knSims and knAsms) with their arity
  , knDCs               :: !(S.HashSet Symbol)     -- data constructors drawn from Rewrite 
  , knSels              :: !(SelectorMap)
  , knConsts            :: !(ConstDCMap)
  , knAutoRWs           :: M.HashMap SubcId [AutoRewrite]
  , knRWTerminationOpts :: RWTerminationOpts
  , knShowProofs        :: S.HashSet SubcId
  }

isValid :: Knowledge -> Expr -> IO Bool
isValid γ e = do
  contra <- knPreds γ (knContext γ) (knLams γ) PFalse
  if contra
    then return False
    else knPreds γ (knContext γ) (knLams γ) e

knowledge :: Config -> SMT.Context -> SInfo a -> Knowledge
knowledge cfg ctx si = KN
  { knSims                     = sims
  , knAms                      = aenvEqs aenv
  , knContext                  = ctx
  , knPreds                    = askSMT  cfg
  , knLams                     = []
  , knSummary                  =    ((\s -> (smName s, 1)) <$> sims)
                                 ++ ((\s -> (eqName s, length (eqArgs s))) <$> aenvEqs aenv)
  , knDCs                      = S.fromList (smDC <$> sims)
  , knSels                     = Mb.catMaybes $ map makeSel  sims
  , knConsts                   = Mb.catMaybes $ map makeCons sims
  , knAutoRWs                  = aenvAutoRW aenv
  , knRWTerminationOpts        =
      if (rwTerminationCheck cfg)
      then RWTerminationCheckEnabled (maxRWOrderingConstraints cfg)
      else RWTerminationCheckDisabled
  , knShowProofs = aenvShowProofs aenv
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
--   | isContraPred e     = return False 
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
      tx (EBin bop e1 e2) = applyConstantFolding bop e1 e2
      tx (EEq (ECon x) (ECon y)) = if x == y then PTrue else PFalse
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

applyConstantFolding :: Bop -> Expr -> Expr -> Expr
applyConstantFolding bop e1 e2 =
  case (e1, e2) of
    ((ECon (R left)), (ECon (R right))) ->
      Mb.fromMaybe e (cfR bop left right)
    ((ECon (R left)), (ECon (I right))) ->
      Mb.fromMaybe e (cfR bop left (fromIntegral right))
    ((ECon (I left)), (ECon (R right))) ->
      Mb.fromMaybe e (cfR bop (fromIntegral left) right)
    ((ECon (I left)), (ECon (I right))) ->
      Mb.fromMaybe e (cfI bop left right)
    _ -> e
  where

    e = EBin bop e1 e2

    getOp :: Num a => Bop -> Maybe (a -> a -> a)
    getOp Minus    = Just (-)
    getOp Plus     = Just (+)
    getOp Times    = Just (*)
    getOp RTimes   = Just (*)
    getOp _        = Nothing

    cfR :: Bop -> Double -> Double -> Maybe Expr
    cfR bop left right = fmap go (getOp' bop)
      where
        go f = ECon $ R $ f left right

        getOp' Div      = Just (/)
        getOp' RDiv     = Just (/)
        getOp' op       = getOp op

    cfI :: Bop -> Integer -> Integer -> Maybe Expr
    cfI bop left right = fmap go (getOp' bop)
      where
        go f = ECon $ I $ f left right

        getOp' Mod = Just mod
        getOp' op  = getOp op


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

