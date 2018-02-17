module Language.Types where

import           Control.Lens hiding (para)
import           Control.Monad.Reader

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

-- -- | Substitute variables by corresponding expressions.
-- subst :: Map Var CoreExpr -> CoreExpr -> CoreExpr
-- subst m x = runReader (sub x) m
--   where
--     protect v e = local (M.delete v) (sub e)
--     sub :: CoreExpr -> Reader (Map Var CoreExpr) CoreExpr
--     sub = \case
--       -- If the variable is to be substituted, do so.
--       EVar v () -> M.findWithDefault (EVar v ()) v <$> ask
--       -- 'let', 'lambda', 'fix', and 'match' expressions guard against the
--       -- substitution of their bound variable(s).
--       (ELet v e1 e2 ()) -> ELet v <$> protect v e1 <*> protect v e2 <*> pure ()
--       (ELam v e ()) -> ELam v <$> protect v e <*> pure ()
--       (EFix v e ()) -> EFix v <$> protect v e <*> pure ()
--       EMatch tar nc v1 v2 cc () ->
--         EMatch <$> sub tar
--                <*> sub nc
--                <*> pure v1
--                <*> pure v2
--                <*> local (M.delete v1 . M.delete v2) (sub cc)
--                <*> pure ()
--       -- In all other cases, recursively substitute over subexpressions.
--       e -> e & plate %%~ sub
--
-- data Result = Result {resGoal :: (Var, Var), resResult :: Bool}
--   deriving Show

-- data EqEnv = EqEnv
--   { eqProgram :: Program
--   , eqGoals   :: [(Var, Var)]
--   }

-- goalsToPrograms :: Program -> (Var, Var) -> (Bind, Bind)
-- goalsToPrograms bs (x1, x2) = ((x1, findBind bs x1), (x2, findBind bs x2))

-- findBind :: Program -> Var -> CoreExpr
-- findBind ((x,e):bs) y
--   | x == y    = e
--   | otherwise = findBind bs y
-- findBind [] _ = error "findBind: Not found"

-- mkPairs :: [String] -> [(Var, Var)]
-- mkPairs (x1:x2:rest) = (Var x1, Var x2) : mkPairs rest
-- mkPairs _            = []

-- exprList :: [CoreExpr] -> CoreExpr
-- exprList = foldr (EBin Cons) ENil

-- isFix :: CoreExpr -> Bool
-- isFix (ELet x ex _) =  x `S.member` freeVars ex
-- isFix _             = False

