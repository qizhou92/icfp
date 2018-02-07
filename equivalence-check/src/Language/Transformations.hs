{-# LANGUAGE OverloadedStrings #-}
module Language.Transformations  where

import Language.Types
import qualified Data.Map as M


resugarMatch :: CoreExpr -> CoreExpr
resugarMatch = go 
  where
    go e | Just (e0, e1, x, y, e2) <- toMatch e  
         = EMatch e0 e1 x y e2 
    go (EBin b e1 e2) = EBin b (go e1) (go e2)
    go (EIf e e1 e2)  = EIf (go e) (go e1) (go e2)
    go (EMatch e e1 x y e2) = EMatch (go e) (go e1) x y (go e2)
    go (ECon e1 e2) = ECon (go e1) (go e2)
    go (ELet x e1 e2) = ELet x (go e1) (go e2)
    go (EApp e1 e2) = EApp (go e1) (go e2)
    go (ELam x e) = ELam x (go e)
    go (EFix x e) = EFix x (go e)
    go (EVar x) = EVar x 
    go (EBool b) = EBool b 
    go (EInt i)  = EInt i 
    go (ENil)    = ENil

    toMatch (EIf isNil e1 e2)
      | Just e <- isCheckNil isNil 
      , Just (x, y, ec) <- isConsMatch e e2  
      = Just (e, e1, x, y, ec)
    toMatch _ 
      = Nothing

    isCheckNil (EBin Eq ENil x) 
      = Just x 
    isCheckNil (EBin Eq x ENil) 
      = Just x 
    isCheckNil _ 
      = Nothing

    isConsMatch xs (ELet x takeHead (ELet y takeTail e)) 
      | takeHead == EApp "head" xs
      , takeTail == EApp "tail" xs
      = Just (x, y, e)
    isConsMatch xs (ELet y takeTail (ELet x takeHead e)) 
      | takeHead == EApp "head" xs
      , takeTail == EApp "tail" xs
      = Just (x, y, e)
    isConsMatch _ _ 
      = Nothing 

listToFix :: Tranformable a => a -> a 
listToFix =  mapSort go 
  where 
  	go (TList t)        = TFix "VList" (TPlus TNil (TProduct t (TVar "VList")))
  	go (TVar x)         = TVar x 
  	go TInt             = TInt
  	go TBool            = TBool
  	go (TArr t1 t2)     = TArr (go t1) (go t2)
  	go (TPlus t1 t2)    = TPlus (go t1) (go t2)
  	go (TProduct t1 t2) = TProduct (go t1) (go t2)
  	go (TFix x t2)      = TFix x (go t2)
  	go TNil             = TNil



class Tranformable a where
  mapSort :: (Type -> Type) -> a -> a
  mapSort _ x = x 

  mapExpr :: (CoreExpr -> CoreExpr) -> a -> a
  mapExpr _ x = x 


instance Tranformable Scheme where
  mapSort f (Forall ts t) = Forall (map f ts) (f t) 

instance Tranformable CoreExpr where
  mapExpr f e = f e 

instance Tranformable Type where
  mapSort f x = f x    

instance (Ord x, Tranformable x, Tranformable y) => Tranformable (M.Map x y) where
  mapSort f m = M.fromList $ [(mapSort f x, mapSort f y) | (x,y) <- M.toList m]
  mapExpr f m = M.fromList $ [(mapExpr f x, mapExpr f y) | (x,y) <- M.toList m]

instance Tranformable a => Tranformable [a] where
  mapSort f xs = map (mapSort f) xs
  mapExpr f xs = map (mapExpr f) xs

instance (Tranformable x, Tranformable y) => Tranformable (x, y) where
  mapSort f (x, y) = (mapSort f x, mapSort f y)
  mapExpr f (x, y) = (mapExpr f x, mapExpr f y)

instance Tranformable Var where
