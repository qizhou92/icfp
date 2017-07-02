-- @checkEq mult mult1

mult x y =
if y == 0 then 0 else x + mult x (y-1)

;

mult1 x y =
if y == 0 then 0 else x + mult x (y-1)

 
 --query 0 ≤ x1 ≤ x2 ∧ 0 ≤ y1 ≤ y2 ⇒ mult x1 y1 ≤ mult1 x2 y2