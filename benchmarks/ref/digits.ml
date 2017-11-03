(* digitsOfInt : int -> int list *)
let rec digitsOfInt n = if n<10 then [n] else (digitsOfInt (n/10))@[n mod 10]


(* digits : int -> int list *)
let digits n = digitsOfInt (abs n)


