(* val sumList : int list -> int *) 
let rec sumList l = match l with [] -> 0 | (h::t) -> h+sumList t


(* digitsOfInt : int -> int list *)
let rec digitsOfInt n = if n<10 then [n] else (digitsOfInt (n/10))@[n mod 10]


(* digits : int -> int list *)
let digits n = digitsOfInt (abs n)

(* additivePersistence : int -> int *)
let rec additivePersistence n = if n < 10 then 0 else 1+additivePersistence (sumList (digitsOfInt n));;

(* digitalRoot : int -> int *)
let rec digitalRoot n = if n < 10 then n else digitalRoot (sumList (digitsOfInt n));;


(* listReverse : 'a list -> 'a list *)
let listReverse l = 
  let rec loop a b = match a with [] -> b | (h::t) -> loop t (h::b) in
    loop l []

(* SKIP *)
(* explode : string -> char list *)
let explode s = 
  let rec _exp i = 
    if i >= String.length s then [] else (s.[i])::(_exp (i+1)) in
  _exp 0


let palindrome w = let e = explode w in e = listReverse e

