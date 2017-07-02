-- @checkEq sum sum2

sum1 n =
if n < 0 then n + sum1 (n + 1)
 else (if n == 0 then 0 else n + sum1 (n - 1))

;

sum2 n =
 let sum1 n =
   if n < 0 then n + sum1 (n + 1)
 else (if n == 0 then 0 else n + sum1 (n - 1))
 in (n + sum1 (x - 1))
 
 --query sum x =  x + sum (x - 1)