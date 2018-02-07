{-# LANGUAGE OverloadedStrings #-}
module Language.Transformations  where

import           Control.Lens

import qualified Data.Map as M

import           Language.Types

resugarMatch :: CoreExpr -> CoreExpr
resugarMatch = rewrite (\case
  EIf cond e1 e2 -> do
    e <- isCheckNil cond
    (x, y, ec) <- isConsMatch e e2
    pure (EMatch e e1 x y ec)
  _ -> Nothing)
  where
    isCheckNil = \case
      EBin Eq ENil x -> Just x
      EBin Eq x ENil -> Just x
      _ -> Nothing

    isConsMatch xs (ELet x takeHead (ELet y takeTail e))
      | takeHead == EApp "head" xs , takeTail == EApp "tail" xs = Just (x, y, e)
    isConsMatch xs (ELet y takeTail (ELet x takeHead e)) 
      | takeHead == EApp "head" xs , takeTail == EApp "tail" xs = Just (x, y, e)
    isConsMatch _ _ = Nothing

listToFix :: Tranformable a => a -> a
listToFix = mapSort (rewrite (\case
  TList t -> Just $ TFix "VList" (TPlus TNil (TProduct t (TVar "VList")))
  _ -> Nothing))

class Tranformable a where
  mapSort :: (Type -> Type) -> a -> a
  mapSort _ x = x 

  mapExpr :: (CoreExpr -> CoreExpr) -> a -> a
  mapExpr _ x = x 


instance Tranformable Scheme where
  mapSort f (Forall ts t) = Forall (map f ts) (f t) 

instance Tranformable CoreExpr where
  mapExpr f = f

instance Tranformable Type where
  mapSort f = f

instance (Ord x, Tranformable x, Tranformable y) => Tranformable (M.Map x y) where
  mapSort f m = M.fromList [(mapSort f x, mapSort f y) | (x,y) <- M.toList m]
  mapExpr f m = M.fromList [(mapExpr f x, mapExpr f y) | (x,y) <- M.toList m]

instance Tranformable a => Tranformable [a] where
  mapSort f = map (mapSort f)
  mapExpr f = map (mapExpr f)

instance (Tranformable x, Tranformable y) => Tranformable (x, y) where
  mapSort f (x, y) = (mapSort f x, mapSort f y)
  mapExpr f (x, y) = (mapExpr f x, mapExpr f y)

instance Tranformable Var where
