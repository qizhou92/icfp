module Reverse where 

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

reverse0 :: Int -> Int 
reverse0 x = go 0 x 
  where
    go res x | x > 0     = go (res * 10 + (x `mod` 10)) (x `div` 10) 
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

reverse1 :: Int -> Int 
reverse1 x = go 0 x 
  where
    go rev x | x /= 0    = go (rev * 10 + x `mod` 10) (x `div` 10)
             | otherwise = rev 

