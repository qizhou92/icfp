(*********************************************)
let rec assoc (d,k,l) = match l with
    | [] -> d
    | (ki,vi)::t -> if ki = k then vi else assoc (d,k,t)

(*********************************************)
let removeDuplicates l = 
  let rec helper (seen,rest) = 
      match rest with 
        [] -> seen
      | h::t -> 
        let seen' = if List.mem h seen then seen else h :: seen in
        let rest' = t in 
	  helper (seen',rest') 
  in
      List.rev (helper ([],l))

(*********************************************)

let rec wwhile (f,b) = let (b', c) = f b in
    if (not c) then b' else wwhile (f,b')

(*********************************************)
let fixpoint (f,b) = wwhile ((fun b' -> if ((f b') = b') then (f b', false) else (f b', true)), b)


(*********************************************)
(* ffor: int * int * (int -> unit) -> unit *)
let rec ffor (low, high, f) = 
  if low > high 
  then () 
  else let _ = f low in ffor (low+1,high,f)
      
