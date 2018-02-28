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
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Generics.Fixplate.Base

import           Language.Types

import           Grammar
import qualified Formula as F

data RHORT = RHORT
  deriving (Show, Read, Eq, Ord)

-- TODO signature is not correct
freshType :: MonadState Int m
          => Set (Var, Type)
          -> Seq Type
          -> Seq Int
          -> m RHORT
freshType = undefined

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

data Annotation = Annotation
  { fixID :: FixID
  , uniqueID :: ExprID
  , availVars :: Set (Var, Type)
  , expressionType :: Type
  } deriving (Show, Read, Eq, Ord)

type IExpr = Attr CoreExpr' Annotation

data InferenceState = InferenceState
  { _typeCounter :: Int
  , _typeMap :: Map (Seq ExprID) RHORT
  , _cloneMap :: Map (Seq FixID) (Set RHORT)
  } deriving (Show, Read, Eq, Ord)
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

runInfer :: Infer a -> Either InferenceError (a, InferenceState, [Rule])
runInfer ac =
  let (res, rs) =
        runWriter (runExceptT (runStateT (runReaderT ac undefined)
          (InferenceState 0 M.empty M.empty)))
  in fmap (\(a, st) -> (a, st, rs)) res

infer :: Seq IExpr -> Infer RHORT
infer Empty = ask
infer es =
  let idxs = fmap (uniqueID . attribute) es in
  M.lookup idxs <$> use typeMap >>= \case
    -- We've already performed type judgements on this expression index,
    -- so just propogate the type rather than doing it again.
    Just t -> pure t
    -- We need to perform type judgements over every index in the array.
    Nothing -> do
      -- Construct a fresh type.
      let available = foldMap (availVars . attribute) es
      let ts = fmap (expressionType . attribute) es
      t <- zoom typeCounter (freshType available ts idxs)

      -- Now perform inference on every index in the expression sequence.
      mapM_ (infer' t es) [0..Seq.length es-1]

      -- Next, we will add the type to the clones map so we can check
      -- inductiveness later.
      let fixIds = fmap (fixID . attribute) es
      cloneMap %= M.insertWith S.union fixIds (S.singleton t)

      -- Then propogate the type.
      pure t

infer' :: RHORT -> Seq IExpr -> Int -> Infer ()
infer' t esSeq idx =
  -- Indexed type judgements are a dispatch over the form of the expression
  -- at the index.
  let (Fix (Ann _ e)) = Seq.index esSeq idx
      es = Seq.deleteAt idx esSeq
  in case e of
    EVar x -> do
      t' <- infer es
      let tv = valueOf idx t
      let vx = F.Var (getVar x) (view F.varType tv)
      subtype [F.expr|@tv = @vx|] [] t' t

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
    EInt i -> do
      t' <- infer es
      let tv = valueOf idx t
      let i' = F.LInt $ toInteger i
      subtype [F.expr|@tv = $i'|] [] t' t

    -- For boolean constants, we just bind the value to the constant.
    EBool b -> do
      t' <- infer es
      let tv = valueOf idx t
      let b' = F.LBool b
      subtype [F.expr|@tv = $b'|] [] t' t

    ENil -> undefined
    EMatch{} -> undefined
    ECon{} -> undefined
    ELet{} -> undefined

-- | The first type is a subtype of the second with no additional constraints.
(<:) :: MonadWriter [Rule] m => RHORT -> RHORT -> m ()
(<:) = subtype (F.LBool True) []
