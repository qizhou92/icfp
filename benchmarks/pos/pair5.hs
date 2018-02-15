-- @checkEq mult mult2

mult x y =
if y == 0 then 0 else x + mult x (y-1)

;

mult2 x y =
if y == 0 then 0 else x + mult2 x (y-1)
 


--query mult x y = mult2 y x 