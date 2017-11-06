module Language.Equivalence.Transformations  where

import Language.Equivalence.Types
import qualified Data.Map as M


desugarMatch :: CoreExpr -> CoreExpr
desugarMatch e = e 

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
