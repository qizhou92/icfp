module ClimbStairs where 

{- 
import Language.Haskell.Liquid.ProofCombinators 



{-@ pf :: n:Int -> i:Int -> sum: Int -> prev: Int -> cur:Int -> 
       count1:Int -> count2:{Int | count2 + count1 == sum } 
       ->  {go0 n sum prev cur i == go1 n count1 count2 (i+1) } @-}
pf :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> Proof 
{- 	


pf n sum prev cur i count1 count2 
  | n < i 
  =   go0 n sum prev cur i
  ==. sum 
  ==. go1 n count1 count2 i
  *** QED 

pf n sum prev cur i count1 count2 
  | n == i 
  =   go0 n sum prev cur i
  ==. sum 
  ==. count2 + count1
  ==. go1 n count2 (count2 + count1) (i + 1)
  ==. go1 n count1 count2 i
  *** QED 

-}

pf n i sum prev cur count1 count2 
  | i < n 
  =   go0 n sum prev cur i
  ==. go0 n (sum + prev) cur sum     (i + 1)
  ==. go1 n count2 (count2 + count1) (i + 2) 
       ? pf n (i+1) (sum + prev) cur sum count2 (count2 + count1)
  ==. go1 n count1 count2 (i+1)
  *** QED 

-}

{-@ reflect climbStairs0 @-}
climbStairs0 :: Int -> Int 
climbStairs0 n =
  if n <= 1 then 1 else go0 n 2 1 0 2 

{-@ reflect go0 @-}
go0 :: Int -> Int -> Int -> Int -> Int -> Int 
{-@ Lazy go0 @-}
go0 n sum prev cur i =  
  if i < n then go0 n (sum + prev) cur sum (i + 1)
      else sum 

{-
  go0 n  2  1  0 2 
  go0 n  3  0  2 3
  go0 n  3  2  3 4 
  go0 n  5  3  3 5 
  go0 n  8  3  5 6 
  go0 n 11  5  8 7  
  go0 n 16  8 11 8  
  go0 n 24 11 8 9 



go1 n 1  1  2 
go1 n 1  2  3
go1 n 2  3  4 
go1 n 3  5  5 
go1 n 5  8  6 
go1 n 8  13 7 
go1 n 11 17 8 
go1 n 28 11 9 
go1 n 39 28 10
-}


{-@ reflect climbStairs1 @-}
climbStairs1 :: Int -> Int 
climbStairs1 n = if n <= 1 then 1 else go1 n 1 1 2 

{-@ reflect go1 @-}
go1 :: Int -> Int -> Int -> Int -> Int 
{-@ Lazy go1 @-}
go1 n count1 count2 i =
 if i <= n then go1 n count2 (count2 + count1) (i + 1)
           else count2 




