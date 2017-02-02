let climbStairs1 n =
  if n <= 1 then 1
  else
    let rec climbStairs1Rec count1 count2 i =
      if i <= n then
        climbStairs1Rec
          count2 (count2 + count1) (i + 1)
      else count2 in
    climbStairs1Rec 1 1 2
