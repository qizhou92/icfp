
let rec assoc (d,k,l) = match l with
  | [] -> d
  | (ki,vi)::t -> if ki = k then vi else assoc (d,k,t)


