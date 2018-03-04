-- @checkEq mult mult2

mult x y =
if y == 0 then 0 else x + mult x (y-1)

;

mult2 x y = 
let mult x y =
  if y == 0 then 0 else x + mult x (y-1)
 in y + mult x y


--query mult (1 + x) y = mult2 x y