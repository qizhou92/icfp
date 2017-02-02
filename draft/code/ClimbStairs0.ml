let climbStairs0 n =
  (if n <= 1 then 1 (* 4 *)
  else
    let rec climbStairs0Rec
        sum prev cur i = 
      if i < n then
        climbStairsRec
          (sum + prev) cur sum (i + 1)
      else sum) (* 2 *) in
    climbStairsRec 2 1 0 2 (* 1 *)
