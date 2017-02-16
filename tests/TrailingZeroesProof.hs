module TrailingZeroes where

import Language.Haskell.Liquid.ProofCombinators 


theorem :: Int -> Proof
{-@ theorem :: n:Nat -> {trailingZeroes0 n == trailingZeroes1 n} @-}
theorem n
  =   trailingZeroes0 n 
  ==. go0 0 n 
  ==. go1 0 (n`div`5) ? pf 0 n 
  ==. trailingZeroes1 n 
  *** QED 

{-@ pf :: x:Int -> y:Int ->  { go0 x y ==  go1 x (y/5) } / [y] @-}
pf :: Int -> Int -> Proof 
pf x y | y `div` 5 <= 0
  = go0 x y ==. x ==. go1 x (y`div`5) 
  *** QED 
pf x y 
  =   go0 x y 
  ==. go0 (x + (y `div` 5)) (y`div`5)
  ==. go1 (x + (y `div` 5)) ((y`div`5)`div` 5) ? pf (x + y`div`5) (y`div`5)
  ==. go1 x (y`div`5)
  *** QED 



{-@ measure trailingZeroes0 :: Int -> Int @-}
{-@ assume  trailingZeroes0 :: n:Nat -> {v:Int | v == go0 0 n && v == trailingZeroes0 n } @-}
trailingZeroes0 :: Int -> Int 
trailingZeroes0 n 
 = go0 0 n

{-@ Lazy go0 @-}
{-@ measure go0 :: Int -> Int -> Int @-}
{-@ assume go0 :: x:Int -> y:Int -> {v:Int | v == go0 x y && (if (5 <= y) then (v == go0 (x + (y/5)) (y / 5)) else (v == x)) } @-}

go0 :: Int -> Int -> Int 
go0 x y | 5 <= y    = go0 (x + (y `div` 5)) (y `div` 5)
        | otherwise = x

{-@ measure trailingZeroes1 :: Int -> Int @-}
{-@ assume  trailingZeroes1 :: n:Nat -> {v:Int | v == go1 0 (n/5) && v == trailingZeroes1 n } @-}
trailingZeroes1 :: Int -> Int 
trailingZeroes1 n 
 = go1 0 (n `div` 5) 

{-@ Lazy go1 @-}
{-@ measure go1 :: Int -> Int -> Int @-}
{-@ assume go1 :: x:Int -> y:Int -> {v:Int | v == go1 x y && (if (0 < y) then (v == go1 (x + y) (y / 5)) else (v == x)) } @-}

go1 :: Int -> Int -> Int 
go1 s n | 0 < n     = go1 (s + n) (n `div` 5)
        | otherwise = s
