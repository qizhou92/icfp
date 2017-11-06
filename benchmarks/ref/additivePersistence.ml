(* val sumList : int list -> int *) 
let rec sumList l = match l with [] -> 0 | (h::t) -> h+sumList t

(* digitsOfInt : int -> int list *)
let rec digitsOfInt n = if n<10 then [n] else (digitsOfInt (n/10))@[n mod 10]

(* additivePersistence : int -> int *)
let rec additivePersistence n = if n < 10 then 0 else 1+additivePersistence (sumList (digitsOfInt n));;


