(* For this assignment, you may use the following library functions:

   List.map
   List.fold_left
   List.fold_right
   List.split
   List.combine
   List.length

   See http://caml.inria.fr/pub/docs/manual-ocaml/libref/List.html for documentation.
*)

(******************* 1. Warm Up   ********************************)

let sqsum xs = 
  let f b x = b+x*x in
  let base = 0 in
  List.fold_left f base xs

let pipe fs = 
  let f b x = fun z -> x (b z) in
  let base = fun x -> x in
  List.fold_left f base fs

let rec sepConcat sep sl = 
   match sl with 
       [] -> ""
     | (h::t) -> 
	 let f b x = b^sep^x in
	 let base = h in
	 let l = t in
	   List.fold_left f base l

let stringOfList f l = "["^(sepConcat "; " (List.map f l))^"]"

(******************* 2. big numbers ******************************)

let rec clone x n = if n <= 0 then [] else x::clone x (n-1)

let rec padZero l1 l2 =
  let ll1 = List.length l1 in
  let ll2 = List.length l2 in
	((clone 0 (ll2 - ll1))@l1, (clone 0 (ll1 - ll2))@l2)

let rec removeZero l = match l with
    0::t -> removeZero t
  | _ -> l

let bigAdd l1 l2 = 
  let add (l1,l2) = 
    let f b x = let ((c,r),(x,y))=(b,x) in 
                let t = x+y+c in
                  (t/10,(t mod 10)::r) in
    let base = (0,[]) in
    let args = List.rev (List.combine (0::l1) (0::l2)) in
    let (_,res) = (List.fold_left f base args) in
      res
  in 
    removeZero (add (padZero l1 l2))

(******************* 2. big numbers ******************************)

let rec mulByDigit i l = if i=0 then [] else bigAdd l (mulByDigit (i-1) l)

(******************* 2. big numbers ******************************)

let bigMul l1 l2 = 
  let f b x = let (p,r)=b in (0::p,bigAdd r ((mulByDigit x l1)@p)) in
  let base = ([],[]) in
  let args = List.rev l2 in
  let (_,res) = (List.fold_left f base args) in
    res


