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

data InferenceError
  = UnificationError Type Type
  | UnboundError Var

type Ctxt = Map Var HORT

type Infer a = ExceptT InferenceError (Writer [Rule]) a

(<:) :: MonadWriter [Rule] m => HORT -> HORT -> m ()
(<:) s t = tell (subtype s t)

prim :: HORT -> Bool
prim = undefined

fresh :: Type -> Infer HORT
fresh = undefined

split :: HORT -> Infer (HORT, HORT)
split = undefined

infer :: Attr CoreExpr' Type -> Infer (Attr CoreExpr' HORT)
infer = fmap (annMap snd . annZip) .
  synthetiseM (\(Ann ty e) -> case e of

  -- prim s, t' <: t, A ~ e : s -> t', A ~ e' : s
  -- --------------------------------------------
  -- A ~ e e' : t
  --
  -- HO s, t' <: t, s <: s', A ~ e : s' -> t', A ~ e' : s
  -- --------------------------------------------
  -- A ~ e e' : t
  EApp st s -> do
    t <- fresh ty
    (s', t') <- split st
    t' <: t
    if prim s then undefined else s <: s'
    pure t
    )

