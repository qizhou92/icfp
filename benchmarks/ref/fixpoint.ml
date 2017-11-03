
let fixpoint (f,b) = wwhile ((fun b' -> if ((f b') = b') then (f b', false) else (f b', true)), b)



