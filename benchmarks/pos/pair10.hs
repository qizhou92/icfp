-- @checkEq sum sum_acc

sum n =
if n < 0 then n + sum (n + 1)
 else (if n == 0 then 0 else n + sum (n - 1))

;

sum_acc n a =
if n < 0 then sum_acc (n + 1) (a + n)
else (if n == 0 then a else sum_acc (n - 1) (a + n))

 
 --query sum (x + a) = sum_acc x a 