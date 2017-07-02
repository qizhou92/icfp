-- @checkEq mult mult_acc

mult x y =
if y == 0 then 0 else x + mult x (y-1)

;

mult_acc x y a =
if y == 0 then a else mult_acc x (y-1) (a+x)

--query mult x y  = mult acc x y 0