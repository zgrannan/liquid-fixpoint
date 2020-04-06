{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--savequery" @-}

module Assoc where
import Prelude hiding ((++))
{-@ infix ++ @-}

infixl 3 ***
{-@ assume (***) :: a -> p:QED -> { if (isAdmit p) then false else true } @-}
(***) :: a -> QED -> ()
_ *** _ = ()

data QED = Admit | QED

{-@ measure isAdmit :: QED -> Bool @-}
{-@ Admit :: {v:QED | isAdmit v } @-}

infixl 3 ===
{-@ (===) :: x:a -> y:{a | y == x} -> {v:a | v == x && v == y} @-}
(===) :: a -> a -> a
_ === y  = y

{-@ assoc3 :: xs:[a] -> ys:[a] -> zs:[a] -> ws:[a] -> us:[a]
          -> { right xs ys (right us zs ws) = left (left xs ys us) zs ws } @-}
assoc3 :: [a] -> [a] -> [a] -> [a] -> [a] -> ()
assoc3 xs ys zs ws us =
      left xs ys (right us zs ws)
  === left (xs ++ ys) us (zs ++ ws)
  *** QED

{-@ assoc2 :: xs:[a] -> ys:[a] -> zs:[a] -> ws:[a]
          -> { right xs ys (zs ++ ws) = left (xs ++ ys) zs ws} @-}
assoc2 :: [a] -> [a] -> [a] -> [a] -> ()
assoc2 xs ys zs ws = ()

{-@ reflect left @-}
left as bs cs = (as ++ bs) ++ cs

{-@ reflect right @-}
right as bs cs = as ++ (bs ++ cs)

{-@ assoc' :: as:[a] -> bs:[a] -> cs:[a]
          -> { left as bs cs = right as bs cs } @-}
assoc' :: [a] -> [a] -> [a] -> ()
assoc' _ _ _ = ()


{-@ assoc :: as:[a] -> bs:[a] -> cs:[a]
          -> { left as bs cs = right as bs cs } @-}
assoc :: [a] -> [a] -> [a] -> ()
assoc [] _ _       = ()
assoc (_:as) bs cs = assoc as bs cs



{-@ reflect ++ @-}
(++)::[a] -> [a] -> [a]
[]     ++ es = es
(d:ds) ++ es = d:(ds ++ es)
