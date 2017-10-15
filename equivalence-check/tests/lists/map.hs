-- @checkEq map1 map2

map1 f xs = if xs == [] 
                   then [] 
                   else let h = head xs in 
                        let t = tail xs in 
                          f h : map f t 
;

map2 f xs = if xs == [] 
                   then [] 
                   else let h = head xs in 
                        let t = tail xs in 
                          f h : map f t 
