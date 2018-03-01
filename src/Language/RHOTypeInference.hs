{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.RHOTypeInference where

import           Control.Lens hiding (argument)
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
import           Language.RHORT

import           Grammar
import qualified Formula as F

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

type Ctxt = RHORT

type Infer a =
  ReaderT Ctxt
    (StateT InferenceState
    (ExceptT InferenceError
    (Writer [Rule]))) a

runInfer :: Infer a -> Either InferenceError (a, InferenceState, [Rule])
runInfer ac =
  let (res, rs) =
        runWriter (runExceptT (runStateT (do
          ctx0 <- zoom typeCounter (freshType mempty mempty mempty)
          runReaderT ac ctx0)
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
      t <- mkRHORT es

      -- Now perform inference on every index in the expression sequence.
      mapM_ (infer' t es) [0..Seq.length es-1]

      -- Next, we will add the type to the clones map so we can check
      -- inductiveness later.
      let fixIds = fmap (fixID . attribute) es
      cloneMap %= M.insertWith S.union fixIds (S.singleton t)

      -- Then propogate the type.
      pure t

mkRHORT :: Seq IExpr -> Infer RHORT
mkRHORT es =
  let idxs = fmap (uniqueID . attribute) es
      available = foldMap (availVars . attribute) es
      ts = fmap (expressionType . attribute) es
  in zoom typeCounter (freshType available ts idxs)

mkCtxt :: Seq IExpr -> Infer RHORT
mkCtxt es =
  let available = foldMap (availVars . attribute) es
  in zoom typeCounter (freshType available Empty Empty)

infer' :: RHORT -> Seq IExpr -> Int -> Infer ()
infer' t esSeq idx =
  -- Indexed type judgements are a dispatch over the form of the expression
  -- at the index.
  let (Fix (Ann a e)) = Seq.index esSeq idx
      es = Seq.deleteAt idx esSeq
      arg = argumentOf (uniqueID a) idx
      val = valueOf (uniqueID a)
  in case e of
    EVar _ -> do
      t' <- infer es
      t' <: t

    EApp applicand argument -> do
      st <- infer (Seq.insertAt idx applicand es)
      s <- infer (Seq.insertAt idx argument es)
      if isPrim idx s
      then do
        let sv = val idx s
        let sta = arg st
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
      let (s, t'') = split idx t
      if isPrim idx s
      then do
        let ta = arg t
        let vx = F.Var (getVar x) (view F.varType ta)
        t' <- infer (Seq.insertAt idx e' es)
        subtype [F.expr|@ta = @vx|] [] t' t
      else do
        ctx <- ask
        ctx' <- mkCtxt (Seq.insertAt idx e' es)
        subtype (F.LBool True) [s] ctx ctx'
        t' <- local (const ctx') (infer (Seq.insertAt idx e' es))
        t' <: t''

    -- Fix expressions have no impact on the system of constraints.
    EFix{} -> pure ()

    EIf cond consequent alternative -> do
      r <- infer (Seq.insertAt idx cond es)
      let b  = val idx r

      ctx <- ask
      ctx'  <- mkCtxt (Seq.insertAt idx consequent es)
      ctx'' <- mkCtxt (Seq.insertAt idx alternative es)

      subtype [F.expr|@b|] [r] ctx ctx'
      subtype [F.expr|not @b|] [r] ctx ctx''

      t'  <- local (const ctx')  (infer (Seq.insertAt idx consequent es))
      t'' <- local (const ctx'') (infer (Seq.insertAt idx alternative es))

      t' <: t
      t'' <: t

    -- First, we infer the type obtained by replacing the expression at the
    -- index by both arguments. Then, the constraint formed is a first
    -- order logical constraint that can be directly expressed by the
    -- variables in the two known types.
    EBin bin arg1 arg2 -> do
      s <- infer ((Seq.insertAt idx arg1 . Seq.insertAt idx arg2) es)
      let rv = val idx s
          sv = val (idx+1) s
          tv = val idx t
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
      let tv = valueOf (uniqueID a) idx t
      let i' = F.LInt $ toInteger i
      subtype [F.expr|@tv = $i'|] [] t' t

    -- For boolean constants, we just bind the value to the constant.
    EBool b -> do
      t' <- infer es
      let tv = valueOf (uniqueID a) idx t
      let b' = F.LBool b
      subtype [F.expr|@tv = $b'|] [] t' t

    ENil -> undefined
    EMatch{} -> undefined
    ECon{} -> undefined
    ELet{} -> undefined

-- | The first type is a subtype of the second with no additional constraints.
(<:) :: MonadWriter [Rule] m => RHORT -> RHORT -> m ()
(<:) = subtype (F.LBool True) []
