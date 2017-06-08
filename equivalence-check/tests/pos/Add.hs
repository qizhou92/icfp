-- @checkEq add0 add1

add0 x =
  let go0 x =
    if 0 < x then
      x + go0 (x-1)
    else
      0
  in
    go0 x
;

add1 x = (x * (x-1)) / 2
