-- @checkEq top1 top2

top1 x = 
 let l = [1, 2, 3, 4] in 
 let m = [5, 6, 7, 8] in 
 head l : tail m 
;

top2 x = 
 let l = [1, 2, 3, 4] in 
 let m = [5, 6, 7, 8] in 
 head l : tail m 