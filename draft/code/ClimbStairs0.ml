(fun n ->
   (if (n <= 1 (* 2 *) ) then (1 (* 3 *))
    else
       ((fix (fun cS0Rec
         (sum, prev, cur, i) ->
           (if i < n (* 8 *) then
               (cS0Rec
                 (sum + prev,
                  cur, sum, i + 1 (* 11 *))
               (* 9 *))
            else (sum (* 10 *))
           (* 7 *)))
        (* 5 *))
           (2, 1, 0, 2 (* 6 *) )
       (* 4 *) )
   (* 1 *) )
(* 0 *) )
