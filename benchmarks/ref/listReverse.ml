(* listReverse : 'a list -> 'a list *)
let listReverse l = 
  let rec loop a b = match a with [] -> b | (h::t) -> loop t (h::b) in
    loop l []

