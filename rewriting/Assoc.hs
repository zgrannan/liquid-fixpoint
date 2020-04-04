{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--savequery" @-}

module Assoc where
import Prelude hiding ((++))
{-@ infix ++ @-}

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
