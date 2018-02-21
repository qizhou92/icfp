module Language.Types where

import           Control.Lens hiding (para)
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Writer
import           Data.Data.Lens 
import           Data.Data (Data)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Monoid
import           Data.Text.Prettyprint.Doc hiding ((<>))
import           Data.Generics.Fixplate.Base
import           Data.Generics.Fixplate.Morphisms
import           Data.Generics.Fixplate.Attributes
import           Data.Generics.Fixplate.Attributes
import qualified Data.Generics.Fixplate.Traversals as T
import           GHC.Exts(IsString(..))

type Program = [Bind]
type Bind    = (Var, CoreExpr)

newtype Var = Var { getVar :: String }
  deriving (Show, Read, Eq, Ord, Data)
instance Pretty Var where pretty (Var v) = pretty v

type TV = String

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
isPrimitiveType TInt = True
isPrimitiveType TBool = True
isPrimitiveType (TArr _ _) = False
isPrimitiveType _ = error "currently not support (isPrimitiveType in Types.hs)"

types :: Data a => Traversal' a Type
types = biplate

data Scheme = Forall [Type] Type
  deriving (Show, Read, Eq, Ord, Data)

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
        braces (p "Nil ->" <+> n <> p "; Cons" <+> p x <+> p y <+> p "->" <+> c)
    )
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

freeVars :: Attr CoreExpr' a -> Attr (Ann CoreExpr' a) (Set Var)
freeVars = synthetise (\(Ann _ e) -> case e of
  -- In the case of a variable, add that variable as a free variable.
  EVar v              -> S.singleton v
  -- In the case of 'let', 'lambda', and 'fix' expressions, variables
  -- which are bound are no longer free.
  ELet v _ vs         -> S.delete v vs
  ELam v vs           -> S.delete v vs
  EFix v vs           -> S.delete v vs
  -- The match expression is the most complex. Remove the bound variables
  -- from the 'cons' case, but keep all free variables from the matched
  -- expression and the 'nil' case.
  EMatch tar nc v1 v2 cc ->
    tar <> nc <> S.delete v1 (S.delete v2 cc)
  -- All other expressions propogate the transitive closure.
  EBin _ e1 e2     -> e1 <> e2
  EIf c t e        -> c <> t <> e
  EApp e1 e2       -> e1 <> e2
  ECon a b         -> a <> b
  EInt _           -> S.empty
  EBool _          -> S.empty
  ENil             -> S.empty)

attach :: MonadState Int m => Attr CoreExpr' a -> m (Attr (Ann CoreExpr' a) Int)
attach = synthetiseM (\e -> do
  x <- get
  put (x+1)
  pure x)

unwind :: Attr CoreExpr' a  -> Attr CoreExpr' a
unwind = T.transform (\(Ann v e) -> unwindFixExpr e)

unwindFixExpr :: CoreExpr -> CoreExpr 
unwindFixExpr = undefined 

-- Which variables are bound as part of the expression?
boundVars :: Attr CoreExpr' a -> Set Var
boundVars = attribute . synthetise (\(Ann _ e) -> case e of
  EVar v              -> S.empty
  ELam v vs           -> S.insert v vs
  EFix v vs           -> vs
  EMatch tar nc v1 v2 cc -> S.fromList [v1, v2] <> tar <> nc <> cc
  ELet _ _ vs         -> vs
  EBin _ e1 e2     -> e1 <> e2
  EIf c t e        -> c <> t <> e
  EApp e1 e2       -> e1 <> e2
  ECon a b         -> a <> b
  EInt _           -> S.empty
  EBool _          -> S.empty
  ENil             -> S.empty)

emptyAttr :: CoreExpr -> Attr CoreExpr' ()
emptyAttr = synthetise (const ())


