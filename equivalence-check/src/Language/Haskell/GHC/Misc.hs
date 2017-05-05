module Language.Haskell.GHC.Misc where

import CoreSyn 
import Var 

findBind :: CoreProgram -> Var -> CoreBind
findBind [] _ 
  = error "findBind: Not found"
findBind (bd:bds) x 
  | x `elem` binds bd
  = bd  
  | otherwise 
  = findBind bds x 

binds (NonRec x _) = [x]
binds (Rec xes)    = fst <$> xes