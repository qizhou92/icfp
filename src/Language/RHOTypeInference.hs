{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.RHOTypeInference where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Writer
import           Control.Monad.Reader

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Generics.Fixplate.Base

import           Language.Types

import           Grammar
import qualified Formula as F

data RHORT = RHORT
  deriving (Show, Read, Eq)

-- TODO signature is not correct
fresh :: MonadState Int m => m RHORT
fresh = undefined

subtype :: MonadWriter [Rule] m
        => F.Expr -> [RHORT] -> RHORT -> RHORT -> m ()
subtype = undefined

constrain :: MonadWriter [Rule] m => F.Expr -> [RHORT] -> RHORT -> m ()
constrain = undefined

valueOf :: Int -> RHORT -> F.Var
valueOf = undefined

argumentOf :: Int -> RHORT -> F.Var
argumentOf = undefined

isPrim :: Int -> RHORT -> Bool
isPrim = undefined

split :: Int -> RHORT -> (RHORT, RHORT)
split = undefined

type IExpr = Attr CoreExpr' (ExprID, [(Var, Type)])

data InferenceState = InferenceState
  { _typeCounter :: Int
  , _typeMap :: Map (Seq ExprID) RHORT
  } deriving (Show, Read, Eq)
makeLenses ''InferenceState

data InferenceError
  = UnificationError Type Type
  | UnboundError Var
  deriving (Show, Read, Eq)

-- TODO should the context have free variables or just the type?
-- type Ctxt = ([Var], RHORT)
type Ctxt = RHORT

type Infer a =
  ReaderT Ctxt
    (StateT InferenceState
    (ExceptT InferenceError
    (Writer [Rule]))) a

infer :: Seq IExpr -> Infer RHORT
infer Empty = ask
infer es =
  let idxs = fmap (fst.attribute) es in
  M.lookup idxs <$> use typeMap >>= \case
    -- We've already performed type judgements on this expression index,
    -- so just propogate the type rather than doing it again.
    Just t -> pure t
    -- We need to perform type judgements over every index in the array.
    Nothing -> do
      -- Construct a fresh type.
      t <- zoom typeCounter fresh
      -- Now perform inference on every index in the expression sequence.
      mapM_ (infer' t es) [0..Seq.length es-1]
      -- Then just propogate the type.
      pure t

infer' :: RHORT -> Seq IExpr -> Int -> Infer ()
infer' t esSeq idx =
  -- Indexed type judgements are a dispatch over the form of the expression
  -- at the index.
  let (Fix (Ann _ e)) = Seq.index esSeq idx
      es = Seq.deleteAt idx esSeq
  in case e of
    EVar x ->
      let tv = valueOf idx t
          vx = F.Var (getVar x) (view F.varType tv)
      in constrain [F.expr|@tv = @vx|] [] t
      -- TODO Do we constrain the variable if it is HO?

    EApp app arg -> do
      st <- infer (Seq.insertAt idx app es)
      s <- infer (Seq.insertAt idx arg es)
      if isPrim idx s
      then do
        let sv = valueOf idx s
        let sta = argumentOf idx st
        subtype [F.expr|@sta = @sv|] [s] st t
      else do
        -- When the argument is not primitive, all we can do is indicate that
        -- the output type of the applicand should be a subtype of the full
        -- application and that the input of the applicand is a supertype of
        -- the argument.
        let (s', t') = split idx st
        t' <: t
        s <: s'

    ELam x e' -> do
      -- TODO how do we add x to the context?
      let (s, t'') = split idx t
      let ta = argumentOf idx t
      let vx = F.Var (getVar x) (view F.varType ta)
      if isPrim idx s
      then do
        -- TODO
        t' <- infer (Seq.insertAt idx e' es)
        subtype [F.expr|@ta = @vx|] [] t' t
      else do
        -- TODO
        t' <- local undefined (infer (Seq.insertAt idx e' es))
        t' <: t''

    -- Fix expressions have no impact on the system of constraints.
    EFix{} ->
      pure ()

    EIf cond consequent alternative -> do
      t'  <- infer ((Seq.insertAt idx cond . Seq.insertAt idx consequent) es)
      t'' <- infer ((Seq.insertAt idx cond . Seq.insertAt idx alternative) es)

      let b'  = valueOf idx t'
      let b'' = valueOf idx t''

      subtype [F.expr|@b'|] [] t' t
      subtype [F.expr|@b''|] [] t'' t

    -- First, we infer the type obtained by replacing the expression at the
    -- index by both arguments. Then, the constraint formed is a first
    -- order logical constraint that can be directly expressed by the
    -- variables in the two known types.
    EBin bin arg1 arg2 -> do
      s <- infer ((Seq.insertAt idx arg1 . Seq.insertAt idx arg2) es)
      let rv = valueOf idx s
          sv = valueOf (idx+1) s
          tv = valueOf idx t
          f = case bin of
            Plus  -> [F.expr|@tv = @rv + @sv|]
            Minus -> [F.expr|@tv = @rv - @sv|]
            Mul   -> [F.expr|@tv = @rv * @sv|]
            Div   -> [F.expr|@tv = @rv / @sv|]
            Eq    -> [F.expr|@tv = (@rv = @sv)|]
            Ne    -> [F.expr|@tv = (not (@rv = @sv))|]
            Lt    -> [F.expr|@tv = (@rv < @sv)|]
            Le    -> [F.expr|@tv = (@rv <= @sv)|]
            And   -> [F.expr|@tv = (@rv && @sv)|]
            Or    -> [F.expr|@tv = (@rv || @sv)|]
            Cons  -> undefined
      constrain f [s] t

    -- For integer constants, we just bind the value to the constant.
    EInt i ->
      -- TODO are we supposed to infer here?
      let tv = valueOf idx t
          i' = F.LInt $ toInteger i
      in constrain [F.expr|@tv = $i'|] [] t

    -- For boolean constants, we just bind the value to the constant.
    EBool b ->
      let tv = valueOf idx t
          b' = F.LBool b
      in constrain [F.expr|@tv = $b'|] [] t

    ENil -> undefined
    EMatch{} -> undefined
    ECon{} -> undefined
    ELet{} -> undefined

-- | The first type is a subtype of the second with no additional constraints.
(<:) :: MonadWriter [Rule] m => RHORT -> RHORT -> m ()
(<:) = subtype (F.LBool True) []
