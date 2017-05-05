module Reverse where 

{- checkEq reverse0 reverse1 -}
{- checkEq reverse2 reverse1 -}

import Prelude 
reverse0 :: Int -> Int 
reverse0 x = go0 0 x 
  where 
    go0 res x | 0 < x     = go0 (res * 10 + x `mod` 10) (x `div` 10) 
              | otherwise = res 



reverse1 :: Int -> Int 
reverse1 x = go1 0 x 
  where
    go1 rev x | 0 < x     = go1 (rev * 10 + x `mod` 10) (x `div` 10)
              | otherwise = rev 


reverse2 :: Int -> Int 
reverse2 x = go1 0 x 
  where
    go1 rev x | 0 < x     = go1 (rev * 10 + x `mod` 10) (x `div` 10)
              | otherwise = rev 
