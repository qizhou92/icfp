-- @checkEq reverse0 reverse1
-- @checkEq reverse2 reverse1

reverse0 x =
  let go0 res x =
    if 0 < x then
      go0 ((res * 10) + (mod x 10)) (div x 10)
    else
      res
  in
    go0 0 x
;

reverse1 x =
  let go1 rev x =
    if 0 < x then
      go1 ((rev * 10) + (mod x 10)) (div x 10)
    else
      rev
  in
     go1 0 x
;

reverse2 x =
  let go1 rev x =
     if 0 < x then
       go1 ((rev * 10) + (mod x 10)) (div x 10)
     else
       rev
  in
    go1 0 x
