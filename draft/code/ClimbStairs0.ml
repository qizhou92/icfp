(fun n ->
   (if (n <= 1 (* 2 *) ) then
       (1 (* 3 *) )
    else
       ( (fix (fun cS0Rec
         sum prev cur i ->
           (if i < n then
               cS0Rec
                 (sum + prev)
                 cur
                 sum
                 (i + 1)
            else sum ) ) (* 5 *) )
           2 1 0 2 (* 4 *) )
   (* 1 *) )
(* 0 *) )
