module TrailingZeroes where

{-
public int trailingZeroes0(int n) { 
  int sum=0;
  while(n>=5){
   sum += n / 5;
   n = n / 5; }
   return sum; }

-}

trailingZeroes0 :: Int -> Int 
trailingZeroes0 n = go 0 n
  where
    go s n | n >= 5    = go (s + n `div` 5) (n `div` 5)
           | otherwise = s 


{-

public int trailingZeroes1(int n) { 
   int x=0;
   int y=n/5;
   while(y!=0){
    x = x + y;
    y = y / 5;}
   return x; }
-}

trailingZeroes1 :: Int -> Int 
trailingZeroes1 n = go 0 (n `div` 5) 
  where
    go x y | y /= 0    = go (x + y) (y `div` 5)
           | otherwise = x
