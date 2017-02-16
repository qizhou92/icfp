module Reverse where 

import Language.Haskell.Liquid.ProofCombinators 


{-@ reserveProof :: n:Int -> {reverse0 n == reverse1 n} @-}
reserveProof :: Int -> Proof 
reserveProof n
  =   reverse0 n 
  ==. go0 0 n 
  ==. go1 0 n ? pf 0 n 
  ==. reverse1 n 
  *** QED 
 

{-@ pf :: res:Int -> x:Int -> { go0 res x == go1 res x  } @-}
pf :: Int -> Int -> Proof 
pf res x | x <= 0 
  =   go0 res x 
  ==. res 
  ==. go1 res x 
  *** QED 
pf res x  
  =   go0 res x 
  ==. go0 (res * 10 + (x `mod` 10)) (x `div` 10) 
  ==. go1 (res * 10 + (x `mod` 10)) (x `div` 10) 
      ? pf (res * 10 + (x `mod` 10)) (x `div` 10)
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
{-@ Lazy go0 @-}

{-@ assume reverse0 :: x:Int -> {v:Int | v == reverse0 x && v == go0 0 x } @-} 
reverse0 :: Int -> Int 
reverse0 x = go0 0 x 

{-@ assume go0 :: res:Int -> x:Int -> {v:Int | v == go0 res x && v == (if (0 < x) then (go0 ((res * 10) + (x mod 10)) (x/10)) else (res)) } @-} 
go0 :: Int -> Int -> Int 
go0 res x | 0 < x     = go0 (res * 10 + x `mod` 10) (x `div` 10) 
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
{-@ Lazy go1 @-}

{-@ assume reverse1 :: x:Int -> {v:Int | v == reverse1 x && v == go1 0 x } @-} 
reverse1 :: Int -> Int 
reverse1 x = go1 0 x 

{-@ assume go1 :: res:Int -> x:Int -> {v:Int | v == go1 res x && v == (if (0 < x) then (go1 ((res * 10) + (x mod 10)) (x/10)) else (res)) } @-} 
go1 :: Int -> Int -> Int 
go1 rev x | 0 < x     = go1 (rev * 10 + x `mod` 10) (x `div` 10)
          | otherwise = rev 

