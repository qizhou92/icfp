(* -- Recursive Summation ------------- *)

let rec sumTo n = if n = 0
                    then 0
                    else n + sumTo (n - 1)


(* -- Tail-Recursive Summation ------------------ *)

let sumToTR n =
  let rec loop n acc = if n == 0
                         then acc
                         else loop (n - 1) (acc + n)
  in
    loop n 0

(* -- Invariant relating the two implementations ----------------------- *)

(*-@  val inv :: n:Nat -> acc:Nat -> { loop n acc == acc + sumTo n }   @-*)

let rec inv n acc = if n == 0
                      then ()
                      else inv (n - 1) (acc + n)

(* -- Equivalence of two implementations ------------------------------- *)

(*-@ val equiv :: n:Nat -> {sumTo n = sumToTR n}                       @-*)

let equiv n = inv n 0
