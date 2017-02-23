module ClimbStairs where 

import Language.Haskell.Liquid.ProofCombinators 
{-@ LIQUID "--no-termination" @-}

climbStairs00 n =
  if n <= 1 then 1
  else climbStairs0Rec 2 1 0 2
  where climbStairs0Rec sum prev cur i = 
          if i < n then climbStairs0Rec (sum + prev) sum sum (i + 1)
           else sum
    

climbStairs11 n =
  if n <= 1 then 1
  else
    let climbStairs1Rec count1 count2 i =
               if i <= n then climbStairs1Rec count2 (count2 + count1) (i + 1)
               else count2 in
      climbStairs1Rec 1 1 2





{-@ pf :: n:Int -> i:Int -> sum: Int -> prev: Int -> cur:Int -> 
       count1:Int -> count2:Int
       ->  {go0 n sum prev cur i == go1 n count1 count2 (i+1) } @-}
pf :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> Proof 

pf n sum prev cur i count1 count2 
  = undefined 

{-

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
  if i < n then go0 n (sum + prev) sum sum (i + 1)
      else sum 



{-@ reflect climbStairs1 @-}
climbStairs1 :: Int -> Int 
climbStairs1 n = if n <= 1 then 1 else go1 n 1 1 2 

{-@ reflect go1 @-}
go1 :: Int -> Int -> Int -> Int -> Int 
{-@ Lazy go1 @-}
go1 n count1 count2 i =
 if i <= n then go1 n count2 (count2 + count1) (i + 1)
           else count2 




