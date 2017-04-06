(* sum_1_inner: compute n * (n - i) *)
let rec sum_1_inner n i =
  if i >= n then 0
  else n + (sum_1_inner n (i + 1))

(* sum_1_outer n m i: compute (n * n) * (n - i) *)
let rec sum_1_outer n i =
  if i >= n then 0
  else (sum_1_inner n 0) + (sum_1_outer n (i + 1))

(* sum_1 n m: compute n * n * n *)
let sum_1 n m = sum_1_outer n 0 (* rel-invs 0 *)

(* sum_2_aux: compute n * (n - i) * (n - j) *)
let rec sum_2_aux n i j =
  if i >= n then 0
  else if j >= n then sum_2_aux n (i + 1) 0
  else n + (sum_2_aux n i (j + 1))

(* sum_2 n c: compute n * n * n *)
let sum_2 n m = sum_2_aux n 0 0

(* relational invariants proving equivalence: *)
 
(* constraints for which each solution are relational invariants *)

(* deprecated:
 g(sum_1, sum_2) =>  ((n_1 = n_2 /\ c_1 = c_2) = > output_1 = output_2 )

 g(sumAdd_1, sum_2) /\ constrains1 => g(sum_1,sum_2)

 g(sumAdd_1, sumAdd_2 ) /\ constrains6 => g(sumAdd_1, sum_2)

 g(sumAdd_1, sumAux, sumAdd_2 ) /\ constrains2 => g(sumAdd_1, sumAdd_2 )

 g(sumAdd_2) /\ constrains3 => g(sumAdd_1, sumAdd_2)

 g(sumAdd_2) /\ cosntrains7  => g(sumAdd_2 )

 g(sumAdd_2) /\ cosntrains8  => g(sumAdd_2 )
 
 cosntrains9  => g(sumAdd_2 )

 g(sumAux,sumAdd_2) /\ constrains3  => g(sumAdd_1, sumAux, sumAdd_2 )

 g(sumAdd_1, sumAux,sumAdd_2) /\ constrains2  => g(sumAdd_1, sumAux, sumAdd_2 )

 g(sumAux,sumAdd_2 ) /\ constrains4 => g(sumAux,sumAdd_2)

 g(sumAdd_2 ) /\ constrains5 => g(sumAux,sumAdd_2)            

*)
