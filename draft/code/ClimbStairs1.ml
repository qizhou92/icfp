(fun n ->
  (if (n <= 1 (* 2 *) ) then (1 (* 3 *))
   else
      ((fix (fun cS1rec (count1, count2, i) ->
        (if i <= n (* 8 *) then
            (cS1rec (count2, count2 + count1, i + 1 (* 11 *))
            (* 9 *))
         else (count2 (* 10 *))
        (* 7 *)))
       (* 5 *))
          (1, 1, 2 (* 6 *) )
      (* 4 *) )
  (* 1 *) )
(* 0 *) )
