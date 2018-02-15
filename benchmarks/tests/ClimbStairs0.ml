let climbStairs0 n =
  if n <= 1 then 1
  else
    let rec climbStairs0Rec sum prev cur i = 
      if i < n then climbStairs0Rec (sum + prev) sum sum (i + 1)
      else sum in
    climbStairs0Rec 2 1 0 2

