module Reverse where 

import Language.Haskell.Liquid.ProofCombinators 

{-@ reserveProof :: n:Int -> {reverse0 n == reverse1 n} @-}
reserveProof :: Int -> Proof 
reserveProof n
  =   reverse0 n 
  ==. go0 0 x 
  ==. go1 0 x ? pf 0 x 
  ==. reverse1 n 
  *** QED 



{-@ pf :: res:Int -> x:Int -> { go0 res x == go1 res x } @-}
pf :: Int -> Int -> Proof 
pf res x 
  =   go0 res x 

  ==. go1 res x 
  *** QED 


{-
public int reverse0(int x) {
	int res = 0; 
	while (x > 0){
	int mod = x % 10;
	x = x / 10; 
	res = res * 10 + mod;
	}
	return res;
}


-}


{-@ measure reverse0 :: Int -> Int @-}
{-@ measure go0      :: Int -> Int -> Int @-}

reverse0 :: Int -> Int 
reverse0 x = go0 0 x 

go0 :: Int -> Int -> Int 
go0 res x | x > 0     = go0 (res * 10 + (x `mod` 10)) (x `div` 10) 
          | otherwise = res 


{-
public int reverse1(int x) {
	int rev = 0;
	while (x != 0){
	 rev = rev * 10 + x % 10;
	 x = x / 10;
	}
	return rev;
}
-}

{-@ measure reverse1 :: Int -> Int @-}
{-@ measure go1      :: Int -> Int -> Int @-}

reverse1 :: Int -> Int 
reverse1 x = go1 0 x 

go1 :: Int -> Int -> Int 
go1 rev x | x /= 0    = go1 (rev * 10 + x `mod` 10) (x `div` 10)
          | otherwise = rev 

