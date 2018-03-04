-- @checkEq map map2

map f xs = if xs == [] 
                   then [] 
                   else let h = head xs in 
                        let t = tail xs in 
                          f h : map f t 
;

map2 f xs = if xs == [] 
                   then [] 
                   else let h = head xs in 
                        let t = tail xs in 
                          f h : map2 f t 
