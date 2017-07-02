-- @checkEq mult1 mult2

mult1 x y z=
 let mult x y =
   if y == 0 then 0 else x + mult x (y-1)
  in mult (mult x y) z

;

mult2 x y z=
 let mult x y =
   if y == 0 then 0 else x + mult x (y-1)
  in mult x (mult y z) 
 


--query mult x (y+z) = mult2 x y z 