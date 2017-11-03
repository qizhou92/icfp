(* val sumList : int list -> int *) 
let rec sumList l = match l with [] -> 0 | (h::t) -> h+sumList t

(* digitsOfInt : int -> int list *)
let rec digitsOfInt n = if n<10 then [n] else (digitsOfInt (n/10))@[n mod 10]

(* digitalRoot : int -> int *)
let rec digitalRoot n = if n < 10 then n else digitalRoot (sumList (digitsOfInt n));;

