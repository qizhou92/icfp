-- @checkEq foldr1 foldr2

foldr1 f b xs = if xs == [] 
                       then b 
                       else let h = head xs in 
                            let t = tail xs in 
                              f h (foldr1 f b t) 
;

foldr2 f b xs = if xs == [] 
                       then b 
                       else let h = head xs in 
                            let t = tail xs in 
                              f h (foldr2 f b t)  
