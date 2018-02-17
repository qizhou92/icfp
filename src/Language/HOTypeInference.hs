{-# LANGUAGE QuasiQuotes #-}
module Language.HOTypeInference where

import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Writer

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
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
  deriving (Show, Read, Eq)

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
(<:) s t = tell (subtype (F.LBool True) [] s t)

-- | Generate a new higher order relational type for every
giveType :: Attr CoreExpr' (Map Var Type, [Var], Type) -> Infer (Attr CoreExpr' HORT)
giveType = fmap unAttrib . traverse (\(m, vs, t) -> fresh m vs t) . Attrib

-- | Annotate each subexpression with the context which maps variables
-- to their corresponding context.
contextualize :: Attr CoreExpr' HORT -> Attr CoreExpr' (HORT, Ctxt)
contextualize = annZip . inherit (\(Fix (Ann t e)) ctxt -> case e of
  EFix x _ -> M.insert x t ctxt
  ELam x _ ->
    case split t of
      Just (s, t') -> if isPrim s then ctxt else M.insert x s ctxt
      Nothing -> error "lambda has non-arrow type"
  _ -> ctxt) M.empty

addFreeVars :: Attr CoreExpr' (Map Var Type, Type)
            -> Attr CoreExpr' (Map Var Type, [Var], Type)
addFreeVars = annZipWith (\(m, t) vs -> (m, S.toList vs, t)) . freeVars

-- | Given an expression where every subexpression has a higher order relational
-- type and has access to the correct context, generate constraints which
-- encode the typing relationships in the expression and propogate the
-- type to the parent expression.
infer :: Attr CoreExpr' (HORT, Ctxt) -> Infer (Attr CoreExpr' HORT)
infer = fmap (annMap snd . annZip) .
  synthetiseM (\(Ann (t, ctxt) e) -> do
    case e of
      EVar x ->
        if isPrim t
        then
          let tv = valueOf t
              vx = F.Var (getVar x) (F.exprType tv)
          in tell (constrain [F.expr|$tv = @vx|] [] t)
        else do
          t' <- isearch x ctxt
          t' <: t

      EApp st s ->
        if isPrim s
        then
          let tv = valueOf t
              sv = valueOf s
              stv = valueOf st
              sta = argumentOf st
          in tell (subtype [F.expr|$sta = $sv|] [s] st t)
        else do
          (s', t') <- safeSplit st
          t' <: t
          s <: s'

      ELam x t' ->
        if x `M.member` ctxt -- x is HO
        then do
          (_ , t'') <- safeSplit t
          t' <: t''
        else do
          let ta = argumentOf t
          let vx = F.Var (getVar x) (F.exprType ta)
          tell $ subtype [F.expr|$ta = @vx|] [] t' t

      EBin op r s ->
        let rv = valueOf r
            sv = valueOf s
            tv = valueOf t
            f = case op of
              Plus  -> [F.expr|$tv = $rv + $sv|]
              Minus -> [F.expr|$tv = $rv - $sv|]
              Mul   -> [F.expr|$tv = $rv * $sv|]
              Div   -> [F.expr|$tv = $rv / $sv|]
              Eq    -> [F.expr|$tv = ($rv = $sv)|]
              Ne    -> [F.expr|$tv = (not ($rv = $sv))|]
              Lt    -> [F.expr|$tv = ($rv < $sv)|]
              Le    -> [F.expr|$tv = ($rv <= $sv)|]
              And   -> [F.expr|$tv = ($rv && $sv)|]
              Or    -> [F.expr|$tv = ($rv || $sv)|]
              Cons  -> undefined
        in tell (constrain f [r, s] t)

      EInt i ->
        let tv = valueOf t
            i' = F.LInt $ toInteger i
        in tell (constrain [F.expr|$tv = $i'|] [] t)

      EBool b ->
        let tv = valueOf t
            b' = F.LBool b
        in tell (constrain [F.expr|$tv = $b'|] [] t)

      EIf s t' t'' -> do
        let sv = valueOf s
        tell $ subtype [F.expr|$sv|] [s] t' t
        tell $ subtype [F.expr|not $sv|] [s] t'' t

      EFix _ t' -> t' <: t

      ENil -> undefined
      EMatch{} -> undefined
      ECon{} -> undefined
      ELet{} -> undefined
    pure t)

typeConstraints :: Attr CoreExpr' (Map Var Type, Type) -> Either InferenceError Grammar
typeConstraints e =
  let e' = infer =<< contextualize <$> giveType (addFreeVars e)
      ac = runExceptT (evalStateT e' 0)
  in case runWriter ac of
    (Left err, _) -> Left err
    (Right _, rs) -> Right (Grammar 0 rs)
