(* sum_1_inner: compute n * (n - i) *)
let rec sum_1_inner n i =
  if i >= n then 0
  else n + (sum_1_inner n (i + 1))

(* sum_1_outer n m i: compute (n * n) * (n - i) *)
let rec sum_1_outer n i =
  if i >= n then 0
  else (sum_1_inner n 0) + (sum_1_outer n (i + 1))

(* sum_1 n m: compute n * n * n *)
let sum_1 n = sum_1_outer n 0

(* sum_2_aux: compute n * (n - i) * (n - j) *)
let rec sum_2_aux n i j =
  if i >= n then 0
  else if j >= n then sum_2_aux n (i + 1) 0
  else n + (sum_2_aux n i (j + 1))

(* sum_2 n c: compute n * n * n *)
let sum_2 n = sum_2_aux n 0 0

(* relational invariants proving equivalence: 

0: goal: functions are equivalent
{ sum_1, sum_2 } |-> \alpha_0^0 = \alpha_1^0 => \nu_0 = \nu_1

0.0: function bodies: under equivalent contexts, give equivalent values
{ sum_1-body, sum_2-body } |-> n_0 = n_1 => \nu_0 = \nu_1

0.0.0: deconstruct bodies of main functions on abstraction:
{ sum_1-outer-body, sum_2-aux-body } |-> 
  arg_0^0 = arg_1^0, arg_0^1 = arg_1^1, arg_1^2 = 0 =>
  \nu_0 = \nu_1

0.0.0.x: sum_1_outer evaluates under its else case, sum_2_aux evaluates under its third case.

{ sum_1-outer-else, sum_2_aux-case-2 } |->
  n_0 = n_1, i_0 = i_1, j_1 = 0 => \nu_0 = \nu_1

If we restrict relational invariants to only pair a sub-expression in one program with a sub-expression in the other term, that it seems like the proof gets stuck (assuming all invariants are expressed in linear arithmetic).

But if we relax invariants to be over sets of subexpressions, then we can support the invariant given directly above by supporting the following invariant, which groups two sub-expressions of program 0 with one sub-expression of program 1:

{ sum_1-term0, sum_1-term1, sum_2-aux-case-2 } |->
  n_00 = n_01 = n_1, i_00 = i_01 = i_1, j_1 = 0 => \nu_00 + \nu_01 + \nu_1

The remaining bindings in the proof deconstruct the recursive functions called in the else case of sum_1_outer (sum_1_inner and sum_1_outer itself) and called in the second else case of sum_2_aux (sum_2_aux itself).

0.0.1: deconstruct bodies of main functions on arguments:
{ sum_1-body-args, sum_2-body-args } |-> 
  arg_0^0 = arg_1^0, arg_0^1 = arg_1^1, arg_1^2 = 0

*)

(* constraints for which each solution are relational invariants:
   TODO: 
 *)
