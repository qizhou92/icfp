-- @checkEq mult mult2

mult x y =
if y == 0 then 0 else x + mult x (y-1)

;

mult2 x y z= 
let mult x y =
  if y == 0 then 0 else x + mult x (y-1)
 in mult x z + mult y z
 


--query mult (x+y) z = mult2 x y z 