module Language.Types where

import           Control.Lens hiding (para)
import           Control.Monad.State
import           Control.Monad.Writer
import           Control.Monad.Reader

import           Data.Data.Lens
import           Data.Data (Data)
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc hiding ((<>))
import           Data.Generics.Fixplate.Base
import           Data.Generics.Fixplate.Morphisms
import           Data.Generics.Fixplate.Attributes
import qualified Data.Generics.Fixplate.Traversals as T
import           Data.Generics.Fixplate.Draw

import           GHC.Exts(IsString(..))

import           Formula (MonadVocab, fresh)

type Program = [Bind]
type Bind    = (Var, CoreExpr)

newtype Var = Var { getVar :: String }
  deriving (Show, Read, Eq, Ord, Data)
instance Pretty Var where pretty (Var v) = pretty v

data Type
  = TVar Var
  | TInt
  | TBool
  | TArr Type Type
  | TPlus Type Type
  | TProduct Type Type
  | TFix Var Type
  | TNil
  | TList Type
  deriving (Show, Read, Eq, Ord, Data)
instance Plated Type where plate = uniplate

isPrimitiveType :: Type -> Bool
isPrimitiveType = \case
  TInt -> True
  TBool -> True
  (TArr _ _) -> False
  _ -> error "currently not support (isPrimitiveType in Types.hs)"

data CoreExpr' a
  = ENil
  | EInt Int
  | EBool Bool
  | EVar Var
  | EBin Binop a a
  | EIf a a a
  -- match e e1 x y e2 = case e of {Nil -> e1; Cons x y -> e2}
  | EMatch a a Var Var a
  | ECon a a
  | ELet Var a a
  | EApp a a
  | ELam Var a
  | EFix Var a
  deriving (Show, Read, Eq, Ord, Data, Functor, Foldable, Traversable)

data Binop = Plus | Minus | Mul | Div | Eq | Ne | Lt | Le | And | Or | Cons
  deriving (Show, Read, Eq, Ord, Data)

type CoreExpr = Mu CoreExpr'

enil :: CoreExpr
enil = Fix ENil

eint :: Int -> CoreExpr
eint = Fix . EInt

ebool :: Bool -> CoreExpr
ebool = Fix . EBool

evar :: Var -> CoreExpr
evar = Fix . EVar

ebin :: Binop -> CoreExpr -> CoreExpr -> CoreExpr
ebin o e e' = Fix (EBin o e e')

eif :: CoreExpr -> CoreExpr -> CoreExpr -> CoreExpr
eif c e e' = Fix (EIf c e e')

ematch :: CoreExpr -> CoreExpr -> Var -> Var -> CoreExpr -> CoreExpr
ematch e n x y c = Fix (EMatch e n x y c)

econ :: CoreExpr -> CoreExpr -> CoreExpr
econ x y = Fix (ECon x y)

elet :: Var -> CoreExpr -> CoreExpr -> CoreExpr
elet v e e' = Fix (ELet v e e')

eapp :: CoreExpr -> CoreExpr -> CoreExpr
eapp x y = Fix (EApp x y)

elam :: Var -> CoreExpr -> CoreExpr
elam v e = Fix (ELam v e)

efix :: Var -> CoreExpr -> CoreExpr
efix v e = Fix (EFix v e)

instance Pretty CoreExpr where
  pretty = cata (\case
    EInt i           -> p i
    EBool b          -> p b
    EVar (Var x)     -> p x
    EBin o e1 e2     -> parens (p o <+> e1 <+> e2)
    EIf c t e        -> p "if" <+> c <+> p "then" <+> t <+> p "else" <+> e
    ELet x e e'      -> vsep [ p "let" <+> p x <+> p "=" <+> e <+> p "in" , e']
    EApp e1 e2       -> parens (e1 <+> e2)
    ELam x e         -> parens (p "\\" <> p x <+> p "->" <+> e)
    EFix x e         -> p "fix" <+> p x <+> e
    ENil             -> p "[]"
    ECon x y         -> parens (p "con" <+> x <+> y)
    EMatch e n x y c ->
      p "match" <+> e <+> p "with" <+>
        braces (p "Nil ->" <+> n <> p "; Cons" <+> p x <+> p y <+> p "->" <+> c))
    where p = pretty

instance IsString CoreExpr where fromString x = evar (Var x)

instance Pretty Binop where
  pretty = pretty . \case
    Plus  -> "+" :: String
    Minus -> "-"
    Mul   -> "*"
    Div   -> "/"
    Eq    -> "="
    Ne    -> "!="
    Lt    -> "<"
    Le    -> "<="
    And   -> "&&"
    Or    -> "||"
    Cons  -> ":"

prettyCtxt :: Show b => Ann CoreExpr' b a -> String
prettyCtxt (Ann ctx _) = show ctx

showTreeCtxt :: Show a => Attr CoreExpr' a -> String
showTreeCtxt = showTreeWith prettyCtxt

freeVars :: Attr CoreExpr' a -> Attr (Ann CoreExpr' a) (Set Var)
freeVars = synthetise (\(Ann _ e) -> case e of
  -- In the case of a variable, add that variable as a free variable.
  EVar v                 -> S.singleton v
  -- In the case of 'let', 'lambda', and 'fix' expressions, variables
  -- which are bound are no longer free.
  ELet v _ vs            -> S.delete v vs
  ELam v vs              -> S.delete v vs
  EFix v vs              -> S.delete v vs
  -- The match expression is the most complex. Remove the bound variables
  -- from the 'cons' case, but keep all free variables from the matched
  -- expression and the 'nil' case.
  EMatch tar nc v1 v2 cc -> tar <> nc <> S.delete v1 (S.delete v2 cc)
  -- All other expressions propogate the transitive closure.
  EBin _ e1 e2           -> e1 <> e2
  EIf c t e'             -> c <> t <> e'
  EApp e1 e2             -> e1 <> e2
  ECon a b               -> a <> b
  EInt _                 -> S.empty
  EBool _                -> S.empty
  ENil                   -> S.empty)

availableVars :: Attr CoreExpr' a -> Attr CoreExpr' (Set Var, a)
availableVars ex = runReader (go ex) S.empty
  where
    go (Fix (Ann a e)) = do
      vs <- ask
      (Fix . Ann (vs, a)) <$> case e of
        ELam x e' -> ELam x <$> local (S.insert x) (go e')
        EFix x e' -> EFix x <$> local (S.insert x) (go e')
        e' -> traverse go e'

type FixID = Int
type ExprID = Int

numberExpressions :: MonadState ExprID m
                  => Attr CoreExpr' a -> m (Attr CoreExpr' (ExprID, a))
numberExpressions = fmap (annZipWith (\a eid -> (eid, a)))
                  . synthetiseM (const $ do x <- get ; put (x+1) ; pure x)

-- | Use alpha renaming to ensure every binding binds a different variable.
uniqueNames :: MonadVocab m => Attr CoreExpr' a -> m (Attr CoreExpr' a)
uniqueNames ex = runReaderT (go ex) M.empty
  where
    go (Fix (Ann a e)) = Fix . Ann a <$> case e of
      EFix x e'    -> newName EFix x e'
      ELam x e'    -> newName ELam x e'
      EVar (Var x) -> EVar . Var . M.findWithDefault x x <$> ask
      _            -> traverse go e

    newName f (Var x) e = do
      x' <- lift (fresh x)
      f (Var x') <$> local (M.insert x x') (go e)

unwindFix :: Attr CoreExpr' a -> Attr CoreExpr' a
unwindFix ex = runReader (unw ex) M.empty
  where
    unw (Fix node@(Ann _ e')) = case e' of
      -- In the case of a fix expression, unwind with the fix expression in the
      -- context, removing the Fix.
      EFix x e -> local (M.insert x node) (unw e)
      -- In the case of a lambda expression, remove the matched fix variable
      -- from the context before recursing over the subexpressions.
      ELam x _ -> T.descendM (local (M.delete x) . unw) (Fix node)
      -- In the case of a variable try to replace it by value in the context.
      EVar x -> Fix . M.findWithDefault node x <$> ask
      -- In all other cases, recurse over the subexpressions.
      _ -> T.descendM unw (Fix node)

-- Which variables are bound as part of the expression?
boundVars :: Attr CoreExpr' a -> Set Var
boundVars = attribute . synthetise (\(Ann _ e) -> case e of
  EVar _                 -> S.empty
  ELam v vs              -> S.insert v vs
  ELet v _ vs            -> S.insert v vs
  EFix _ vs              -> vs
  EMatch tar nc v1 v2 cc -> S.fromList [v1, v2] <> tar <> nc <> cc
  EBin _ e1 e2           -> e1 <> e2
  EIf c t e'             -> c <> t <> e'
  EApp e1 e2             -> e1 <> e2
  ECon a b               -> a <> b
  EInt _                 -> S.empty
  EBool _                -> S.empty
  ENil                   -> S.empty)

emptyAttr :: CoreExpr -> Attr CoreExpr' ()
emptyAttr = synthetise (const ())
