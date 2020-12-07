{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}

-- | This is a wrapper around IO that permits SMT queries

module Language.Fixpoint.Solver.Monad
       ( -- * Type
         SolveM

         -- * Execution
       , runSolverM

         -- * Get Binds
       , getBinds

         -- * SMT Query
       , filterRequired
       , filterValid
       , filterValidGradual
       , checkSat
       , smtEnablembqi

         -- * Debug
       , Stats
       , tickIter
       , stats
       , numIter
       )
       where

import           Language.Fixpoint.Solver.PLE (pleID')
import           Language.Fixpoint.Utils.Progress
import qualified Language.Fixpoint.Types.Config  as C
import           Language.Fixpoint.Types.Config  (Config)
import qualified Language.Fixpoint.Types   as F
-- import qualified Language.Fixpoint.Misc    as Misc
-- import           Language.Fixpoint.SortCheck
import qualified Language.Fixpoint.Types.Solutions as F
-- import qualified Language.Fixpoint.Types.Errors  as E
import           Language.Fixpoint.Smt.Serialize ()
import           Language.Fixpoint.Types.PrettyPrint ()
import           Language.Fixpoint.Smt.Interface
-- import qualified Language.Fixpoint.Smt.Theories as Thy
import           Language.Fixpoint.Solver.Sanitize
import           Language.Fixpoint.Solver.Stats
import           Language.Fixpoint.Graph.Types (SolverInfo (..))
-- import           Language.Fixpoint.Solver.Solution
-- import           ata.Maybe           (catMaybes)
import           Data.List            (intercalate, find, nub, partition)
-- import           Data.Char            (isUpper)
import           Control.Monad.State.Strict
import qualified Data.HashMap.Strict as M
import           Data.Maybe (maybeToList, fromJust, isJust, catMaybes)
import           Control.Exception.Base (bracket)
import Text.Printf
import Data.Hashable (Hashable(hash))
import qualified Data.Text as T
import Language.Fixpoint.SortCheck (unElab)
import Language.Fixpoint.Types (symbolText, Symbol, symbol, Expr(..), eApps, Subst(..), Subable(subst))
import Debug.Trace (trace)

--------------------------------------------------------------------------------
-- | Solver Monadic API --------------------------------------------------------
--------------------------------------------------------------------------------

type SolveM = StateT SolverState IO

data SolverState = SS
  { ssCtx     :: !Context          -- ^ SMT Solver Context
  , ssBinds   :: !F.BindEnv        -- ^ All variables and types
  , ssStats   :: !Stats            -- ^ Solver Statistics
  }

stats0    :: F.GInfo c b -> Stats
stats0 fi = Stats nCs 0 0 0 0
  where
    nCs   = M.size $ F.cm fi

--------------------------------------------------------------------------------
runSolverM :: Config -> SolverInfo b c -> SolveM a -> IO a
--------------------------------------------------------------------------------
runSolverM cfg sI act =
  bracket acquire release $ \ctx -> do
    res <- runStateT act' (s0 ctx)
    smtWrite ctx "(exit)"
    return (fst res)
  where
    s0 ctx   = SS ctx be (stats0 fi)
    act'     = assumesAxioms (F.asserts fi) >> act
    release  = cleanupContext
    acquire  = makeContextWithSEnv cfg file initEnv
    initEnv  = symbolEnv   cfg fi
    be       = F.bs fi
    file     = C.srcFile cfg
    -- only linear arithmentic when: linear flag is on or solver /= Z3
    -- lar     = linear cfg || Z3 /= solver cfg
    fi       = (siQuery sI) {F.hoInfo = F.HOI (C.allowHO cfg) (C.allowHOqs cfg)}


--------------------------------------------------------------------------------
getBinds :: SolveM F.BindEnv
--------------------------------------------------------------------------------
getBinds = ssBinds <$> get

--------------------------------------------------------------------------------
getIter :: SolveM Int
--------------------------------------------------------------------------------
getIter = numIter . ssStats <$> get

----------------------------------------------------------------------------
incIter, incBrkt :: SolveM ()
--------------------------------------------------------------------------------
incIter   = modifyStats $ \s -> s {numIter = 1 + numIter s}
incBrkt   = modifyStats $ \s -> s {numBrkt = 1 + numBrkt s}

--------------------------------------------------------------------------------
incChck, incVald :: Int -> SolveM ()
--------------------------------------------------------------------------------
incChck n = modifyStats $ \s -> s {numChck = n + numChck s}
incVald n = modifyStats $ \s -> s {numVald = n + numVald s}

withContext :: (Context -> IO a) -> SolveM a
withContext k = (lift . k) =<< getContext

getContext :: SolveM Context
getContext = ssCtx <$> get

modifyStats :: (Stats -> Stats) -> SolveM ()
modifyStats f = modify $ \s -> s { ssStats = f (ssStats s) }

--------------------------------------------------------------------------------
-- | SMT Interface -------------------------------------------------------------
--------------------------------------------------------------------------------
-- | `filterRequired [(x1, p1),...,(xn, pn)] q` returns a minimal list [xi] s.t.
--   /\ [pi] => q
--------------------------------------------------------------------------------
filterRequired :: F.Cand a -> F.Expr -> SolveM [a]
--------------------------------------------------------------------------------
filterRequired = error "TBD:filterRequired"

{-
(set-option :produce-unsat-cores true)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

; Z3 will only track assertions that are named.

(assert (< 0 x))
(assert (! (< 0 y)       :named b2))
(assert (! (< x 10)      :named b3))
(assert (! (< y 10)      :named b4))
(assert (! (< (+ x y) 0) :named bR))
(check-sat)
(get-unsat-core)

> unsat (b2 bR)
-}

--------------------------------------------------------------------------------
-- | `filterValid p [(x1, q1),...,(xn, qn)]` returns the list `[ xi | p => qi]`
--------------------------------------------------------------------------------
filterValid :: F.SrcSpan -> Maybe F.SubcId -> F.Expr -> F.Cand a -> SolveM [a]
--------------------------------------------------------------------------------
filterValid sp id p qs = do
  qs' <- withContext $ \me ->
           smtBracket me "filterValidLHS" $
             filterValid_ sp id p qs me
  -- stats
  incBrkt
  incChck (length qs)
  incVald (length qs')
  return qs'


splitPLEConstraints :: F.Expr -> ([F.Expr], [F.Expr])
splitPLEConstraints p =
    let
      (fromPLE, notFromPLE) = partition isPLEConstraint (F.splitPAnd p)
    in
      (map (fromJust . getPLEConstraint) fromPLE, notFromPLE)
  where
    getPLEConstraint (F.POr [x, r]) | x == pleID' = Just r
    getPLEConstraint _                            = Nothing
    isPLEConstraint = isJust . getPLEConstraint


filterValid_ :: F.SrcSpan -> Maybe F.SubcId -> F.Expr -> F.Cand a -> Context -> IO [a]
filterValid_ sp subcID p qs me = catMaybes <$> do
  -- printf "%d soft constraints, %d hard\n" (length soft) (length hard)
  -- mapM_ print (map unElab hard)
  mapM_ (smtAssert' me) (nub soft)
  smtAssert me (F.PAnd hard)
  -- smtAssert me p
  forM qs $ \(q, x) ->
    smtBracketAt sp me "filterValidRHS" $ do
      -- printf "Check: %s\n" (fst $ reify (unElab q))
      smtAssert me (F.PNot q)
      valid <- smtCheckUnsat me
      when valid $ do
        (Asserts assertIDs) <- command me GetUnsatCore
        printf "Unsat Core %s: %s\n" (show subcID) (show assertIDs)
        printFacts $ map (unElab . getConstraint) assertIDs
      return $ if valid then Just x else Nothing
  where
    printFacts facts = printf "S.fromList [ %s ]\n\n" $ intercalate "\n," (map toPair facts)
    toPair (F.EEq lhs rhs) = show (lhs, rhs)

    (soft, hard) = splitPLEConstraints p
    getConstraint smtAssertID =
      let
        hash'    = read (drop 2 $ T.unpack smtAssertID)
        (Just c) = find (\c -> hash c == hash') soft
      in
        c


--------------------------------------------------------------------------------
-- | `filterValidGradual ps [(x1, q1),...,(xn, qn)]` returns the list `[ xi | p => qi]`
-- | for some p in the list ps
--------------------------------------------------------------------------------
filterValidGradual :: [F.Expr] -> F.Cand a -> SolveM [a]
--------------------------------------------------------------------------------
filterValidGradual p qs = do
  qs' <- withContext $ \me ->
           smtBracket me "filterValidGradualLHS" $
             filterValidGradual_ p qs me
  -- stats
  incBrkt
  incChck (length qs)
  incVald (length qs')
  return qs'

filterValidGradual_ :: [F.Expr] -> F.Cand a -> Context -> IO [a]
filterValidGradual_ ps qs me
  = (map snd . fst) <$> foldM partitionCandidates ([], qs) ps
  where
    partitionCandidates :: (F.Cand a, F.Cand a) -> F.Expr -> IO (F.Cand a, F.Cand a)
    partitionCandidates (ok, candidates) p = do
      (valids', invalids')  <- partition snd <$> filterValidOne_ p candidates me
      let (valids, invalids) = (fst <$> valids', fst <$> invalids')
      return (ok ++ valids, invalids)

filterValidOne_ :: F.Expr -> F.Cand a -> Context -> IO [((F.Expr, a), Bool)]
filterValidOne_ p qs me = do
  smtAssert me p
  forM qs $ \(q, x) ->
    smtBracket me "filterValidRHS" $ do
      smtAssert me (F.PNot q)
      valid <- smtCheckUnsat me
      return $ ((q, x), valid)

smtEnablembqi :: SolveM ()
smtEnablembqi
  = withContext $ \me ->
      smtWrite me "(set-option :smt.mbqi true)"

--------------------------------------------------------------------------------
checkSat :: F.Expr -> SolveM  Bool
--------------------------------------------------------------------------------
checkSat p
  = withContext $ \me ->
      smtBracket me "checkSat" $
        smtCheckSat me p

--------------------------------------------------------------------------------
assumesAxioms :: [F.Triggered F.Expr] -> SolveM ()
--------------------------------------------------------------------------------
assumesAxioms es = withContext $ \me -> forM_  es $ smtAssertAxiom me


---------------------------------------------------------------------------
stats :: SolveM Stats
---------------------------------------------------------------------------
stats = ssStats <$> get

---------------------------------------------------------------------------
tickIter :: Bool -> SolveM Int
---------------------------------------------------------------------------
tickIter newScc = progIter newScc >> incIter >> getIter

progIter :: Bool -> SolveM ()
progIter newScc = lift $ when newScc progressTick
