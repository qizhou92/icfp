module AddDigits where

import Language.Haskell.Liquid.ProofCombinators 
{- 
public int 
  addDigits1(int num) { 
    while (num > 9) {
     num = num / 10 + num % 10; }
     return num; }

public int 
   addDigits0(int num) {
   int result = num - 9 * ((num - 1) / 9) ; 
   return result;
}

-}

{-@ measure addDigits0 :: Int -> Int @-}
{-@ measure addDigits1 :: Int -> Int @-}

addDigits1, addDigits0 :: Int -> Int 
{-@ assume addDigits1 :: n:{Int | 0 < n } -> {v:Int | (v == addDigits1 n) && (if (n > 9) then (v == (addDigits1 ((n / 10) + (n mod 10))) ) else ( v == n) )} @-} 
addDigits1 num 
  | num > 9 
  = addDigits1 (num `div` 10 + num `mod` 10)
addDigits1 num = num  

{-@ assume addDigits0 :: n:{Int | 0 < n } -> {v:Int | (v == n - 9 * ((n -1) / 9)) && v == addDigits0 n } @-} 
addDigits0 num = num - 9 * ((num - 1) `div` 9)


equivalenceProof :: Int -> Proof 
{-@ equivalenceProof :: n:{Int | 0 < n} -> {addDigits1 n == addDigits0 n } @-} 
equivalenceProof n 
  | n <= 9 
  =   addDigits1 n
  ==. n 
  ==. addDigits0 n 
  *** QED 
equivalenceProof n 
  =   addDigits1 n 
  ==. addDigits1 (n `div` 10 + n `mod` 10)
  ==. addDigits0 (n `div` 10 + n `mod` 10)
       ? equivalenceProof (n `div` 10 + n `mod` 10)
  ==. (n `div` 10 + n `mod` 10) - 9 * (((n `div` 10 + n `mod` 10) - 1) `div` 9)
  ==. n - 9 * ((n - 1) `div` 9) 
  ==. addDigits0 n 
  *** QED 

