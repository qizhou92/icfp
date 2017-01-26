module AddDigits where

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

addDigits1, addDigits0 :: Int -> Int 
addDigits1 num 
  | num > 9 
  = addDigits0 (num `div` 10 + num `mod` 10)
addDigits1 num = num  

addDigits0 num = num - 9 * ((num - 1) `div` 9)