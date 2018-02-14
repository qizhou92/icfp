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
  | InvalidSplit HORT

type Ctxt = Map Var HORT

type Infer a = StateT Int (ExceptT InferenceError (Writer [Rule])) a

-- | Split the function type into the argument and result types or
-- generate an error if the type cannot be split.
safeSplit :: MonadError InferenceError m => HORT -> m (HORT, HORT)
safeSplit t = case split t of
  Nothing -> throwError (InvalidSplit t)
  Just x -> pure x

-- | Find the type of the variable in the context or generate an error
-- if it is not in the context.
isearch :: Var -> Ctxt -> Infer HORT
isearch x ctxt =
  case M.lookup x ctxt of
    Nothing -> throwError (UnboundError x)
    Just t' -> pure t'

-- | Generate grammar rules which force the first type to be a subtype of
-- the second.
(<:) :: MonadWriter [Rule] m => HORT -> HORT -> m ()
(<:) s t = tell (subtype s t)

-- | Generate a new higher order relational type for every
giveType :: Attr CoreExpr' ([F.Var], Type) -> Infer (Attr CoreExpr' HORT)
giveType = fmap unAttrib . traverse (uncurry fresh) . Attrib

-- | Annotate each subexpression with the context which maps variables
-- to their corresponding context.
contextualize :: Attr CoreExpr' HORT -> Attr CoreExpr' (HORT, Ctxt)
contextualize = annZip . inherit (\(Fix (Ann t e)) ctxt -> case e of
  ELam x _ -> M.insert x t ctxt
  _ -> ctxt) M.empty

-- | Given an expression where every subexpression has a higher order relational
-- type and has access to the correct context, generate constraints which
-- encode the typing relationships in the expression and propogate the
-- type to the parent expression.
infer :: Attr CoreExpr' (HORT, Ctxt) -> Infer (Attr CoreExpr' HORT)
infer = fmap (annMap snd . annZip) .
  synthetiseM (\(Ann (t, ctxt) e) -> case e of
      EVar x -> isearch x ctxt

      -- prim s, t' <: t, A ~ e : s -> t', A ~ e' : s
      -- --------------------------------------------
      -- A ~ e e' : t
      --
      -- HO s, t' <: t, s <: s', A ~ e : s' -> t', A ~ e' : s
      -- --------------------------------------------
      -- A ~ e e' : t
      EApp st s -> do
        (s', t') <- safeSplit st
        if isPrim s
        then undefined
        else do
          t' <: t
          s <: s'
          pure t

      ELam x t' -> do
        s <- isearch x ctxt
        undefined -- ??

      EBin op r s ->
        let f = case op of
              Plus -> F.mkAdd F.Int (valueOf r) (valueOf s)
              _ -> undefined
        in do
        tell (constrain t [r, s] f)
        pure t

      EInt i -> do
        tell (constrain t [] (F.mkEql F.Int (valueOf t) (F.LInt $ toInteger i)))
        pure t

      EBool b -> do
        tell (constrain t [] (F.mkEql F.Bool (valueOf t) (F.LBool b)))
        pure t
    )

typeConstraints :: Attr CoreExpr' ([F.Var], Type) -> Either InferenceError Grammar
typeConstraints e =
  let ac = runExceptT (evalStateT (infer =<< contextualize <$> giveType e) 0)
  in case runWriter ac of
    (Left err, _) -> Left err
    (Right _, rs) -> Right (Grammar undefined rs)
