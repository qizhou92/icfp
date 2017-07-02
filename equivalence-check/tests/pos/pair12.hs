-- @checkEq sum sum2

sum1 n =
if n < 0 then n + sum1 (n + 1)
 else (if n == 0 then 0 else n + sum1 (n - 1))

;

sum2 n =
if n < 0 then n + sum2 (n + 1)
 else (if n == 0 then 0 else n + sum2 (n - 1))

 
 --query x ≤ y ⇒ sum x ≤ sum y