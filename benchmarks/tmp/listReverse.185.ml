
let rec listReverse l =
  match l with | [] -> [] | hd::tl -> hd :: (listReverse tl);;
