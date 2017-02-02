(fun n ->
  (if (n <= 1 (* 2 *) ) then
      (1 (* 3 *) )
   else
      ( (fix (fun cS1rec count1 count2 i ->
        if i <= n then
          cS1rec count2 (count2 + count1) (i + 1)
        else count2) (* 5 *) ) 
          1 1 2 (* 4 *) )
  ) (* 1 *)
(* 0 *) )
