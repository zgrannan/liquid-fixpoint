{-# LANGUAGE DeriveGeneric             #-}

module Language.Fixpoint.Solver.Rewrite where

import           Control.Monad.State
import           Debug.Trace          (trace)
import           GHC.Generics
import           Data.Hashable
import qualified Data.HashSet         as S
import qualified Data.List            as L
import qualified Data.Maybe           as Mb
import           Language.Fixpoint.Types hiding (simplify)
import qualified Data.Text as TX

type Op = Symbol
type OpOrdering = [Symbol]
data Term = Term Symbol [Term]

instance Show Term where
  show (Term op [])   = TX.unpack $ symbolText op
  show (Term op args) = TX.unpack (symbolText op) ++ "(" ++ L.intercalate ", " (map show args) ++ ")"

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
getDir o from to =
  case (synGTE o from to, synGTE o to from) of
      (True, True)  -> SCEq
      (True, False) -> SCDown
      (False, _)    -> SCUp

getSC :: OpOrdering -> Term -> Term -> S.HashSet SCEntry
getSC o (Term op ts) (Term op' us) = 
  S.fromList $ do
    (i, from) <- zip [0..] ts
    (j, to)   <- zip [0..] us
    return $ SCEntry (op, i) (op', j) (getDir o from to)

scp :: OpOrdering -> [Term] -> S.HashSet SCPath
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

synEQ :: OpOrdering -> Term -> Term -> Bool
synEQ o l r = synGTE o l r && synGTE o r l

opGT :: OpOrdering -> Op -> Op -> Bool
opGT ordering op1 op2 = case (L.elemIndex op1 ordering, L.elemIndex op2 ordering)  of
  (Just index1, Just index2) -> index1 < index2
  (Just index1, Nothing)     -> True
  _ -> False

removeSynEQs :: OpOrdering -> [Term] -> [Term] -> ([Term], [Term])
removeSynEQs _ [] ys      = ([], ys)
removeSynEQs ordering (x:xs) ys
  | Just yIndex <- L.findIndex (synEQ ordering x) ys
  = removeSynEQs ordering xs $ take yIndex ys ++ drop (yIndex + 1) ys
  | otherwise =
    let
      (xs', ys') = removeSynEQs ordering xs ys
    in
      (x:xs', ys')

synGTEM :: OpOrdering -> [Term] -> [Term] -> Bool
synGTEM ordering xs ys =     
  case removeSynEQs ordering xs ys of
    (_   , []) -> True
    (xs', ys') -> any (\x -> all (synGT ordering x) ys') xs'
    
synGT :: OpOrdering -> Term -> Term -> Bool
synGT o t1 t2 = synGTE o t1 t2 && not (synGTE o t2 t1)

synGTM :: OpOrdering -> [Term] -> [Term] -> Bool
synGTM o t1 t2 = synGTEM o t1 t2 && not (synGTEM o t2 t1)

synGTE :: OpOrdering -> Term -> Term -> Bool
synGTE ordering t1@(Term x tms) t2@(Term y tms') =
  if opGT ordering x y then
    synGTM ordering [t1] tms'
  else if opGT ordering y x then
    synGTM ordering tms [t2]
  else
    synGTEM ordering tms tms'

powerset :: [a] -> [[a]]
powerset [] = [[]]
powerset (x:xs) = [x:ps | ps <- powerset xs] ++ powerset xs

subsequencesOfSize :: Int -> [a] -> [[a]]
subsequencesOfSize n xs = let l = length xs
                          in if n>l then [] else subsequencesBySize xs !! (l-n)
 where
   subsequencesBySize [] = [[[]]]
   subsequencesBySize (x:xs) = let next = subsequencesBySize xs
                             in zipWith (++) ([]:next) (map (map (x:)) next ++ [[]])

maxOrderingConstraints = 2

data TermOrigin = PLE | RW OpOrdering

data DivergeResult = Diverges | QuasiTerminates OpOrdering

getOrdering :: TermOrigin -> Maybe OpOrdering
getOrdering (RW o) = Just o
getOrdering PLE    = Nothing

diverges :: [(Term, TermOrigin)] -> Term -> DivergeResult
diverges path term = go 0 
  where
   path' = map fst path ++ [term]
   go n | n >= length syms' || n > maxOrderingConstraints = Diverges
   go n = case L.find (not . diverges') (orderings' n) of
     Just ordering -> QuasiTerminates ordering
     Nothing       -> go (n + 1)
   ops (Term o xs) = o:concatMap ops xs
   syms'           = L.nub $ concatMap ops path'
   suggestedOrderings :: [OpOrdering]
   suggestedOrderings =
     reverse $ Mb.catMaybes $ map (getOrdering . snd) path
   orderings' n    =
     suggestedOrderings ++ concatMap L.permutations ((subsequencesOfSize n) syms')
   diverges' o     = divergesFor o path term
     -- if divergesFor o path term then True else trace (show o ++ " does not diverge") False
   -- diverges'' (n,s) | n `mod` 1000 == 0 = trace (show n) $ diverges' s
   -- diverges'' (n,s) = diverges' s

divergesFor :: OpOrdering -> [(Term, TermOrigin)] -> Term -> Bool
divergesFor o path term = any diverges' terms'
  where
    terms = map fst path ++ [term]
    terms' = case snd (last path) of
      (RW _) -> L.tails terms
      _      -> L.subsequences terms
    diverges' :: [Term] -> Bool
    diverges' trms' =
      any ascending (scp o trms') && all (not . descending) (scp o trms')
      
descending :: SCPath -> Bool
descending (a, b, ds) = a == b && L.elem SCDown ds && L.notElem SCUp ds

ascending :: SCPath -> Bool
ascending  (a, b, ds) = a == b && L.elem SCUp ds

mkTerm s ts = Term (symbol s) ts

rev term = mkTerm "reverse" [term]
x = mkTerm "x" []
isNil term = mkTerm "isNil" [term]
headx = mkTerm "headx" []
tailx = mkTerm "tailx" []
cons h t = mkTerm "cons" [h, t]
concat' xs ys = mkTerm "concat" [xs, ys]
ite x y z = mkTerm "ite" [x,y,z]
nil = mkTerm "[]" []

f x = mkTerm "f" [x]
g x = mkTerm "g" [x]
s x = mkTerm "S" [x]


example =
  [ g $ x
  , g $ s $ x
  ]
