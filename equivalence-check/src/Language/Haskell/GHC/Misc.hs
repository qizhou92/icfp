module Language.Haskell.GHC.Misc where

import CoreSyn 
import Var 

findBind :: CoreProgram -> Var -> CoreExpr
findBind [] _ 
  = error "findBind: Not found"
findBind (bd:bds) x 
  | x `elem` binds bd
  = bindExpr x bd  
  | otherwise 
  = findBind bds x 


bindExpr :: Var -> CoreBind -> CoreExpr 
bindExpr _ (NonRec _ e)  = e
bindExpr _ (Rec [(_,e)]) = e 
bindExpr _ _             = error "Cannot turn binder to program"

binds (NonRec x _) = [x]
binds (Rec xes)    = fst <$> xes