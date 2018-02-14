module Language.HOTypeInference where

import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Writer

import           Data.Data (Data)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Generics.Fixplate.Base
import           Data.Generics.Fixplate.Attributes

import           Language.Types
import           Language.HORT

import           Grammar
import qualified Formula as F

data InferenceError
  = UnificationError Type Type
  | UnboundError Var

type Ctxt = Map Var HORT

type Infer a = StateT Int (ExceptT InferenceError (Writer [Rule])) a

(<:) :: MonadWriter [Rule] m => HORT -> HORT -> m ()
(<:) s t = tell (subtype s t)

infer :: Attr CoreExpr' ([F.Var], Type) -> Infer (Attr CoreExpr' HORT)
infer = fmap (annMap snd . annZip) .
  synthetiseM (\(Ann (free, ty) e) ->
    fresh free ty >>= \t -> case e of

    -- prim s, t' <: t, A ~ e : s -> t', A ~ e' : s
    -- --------------------------------------------
    -- A ~ e e' : t
    --
    -- HO s, t' <: t, s <: s', A ~ e : s' -> t', A ~ e' : s
    -- --------------------------------------------
    -- A ~ e e' : t
    EApp st s -> case split st of
      Nothing -> undefined
      Just (s', t') -> do
        t' <: t
        if isPrim s then undefined else s <: s'
        undefined
        -- constrain t [st, s'] (F.LBool True) -- ??
        pure t

    EBin op r s ->
      let f = case op of
            Plus -> F.mkAdd F.Int (valueOf r) (valueOf s)
            _ -> undefined
      in undefined

      )
