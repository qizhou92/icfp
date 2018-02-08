module Language.Types where

import           Control.Lens
import           Control.Monad.Reader

import           Data.Data.Lens
import           Data.Data (Data)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Monoid
import           Data.Text.Prettyprint.Doc hiding ((<>))

import           GHC.Exts(IsString(..))

type Program = [Bind]
type Bind    = (Var, CoreExpr)

newtype Var = Var String
  deriving (Show, Eq, Ord, Data)
instance Pretty Var where pretty (Var v) = pretty v

type TV = String
data Type
  = TVar TV
  | TInt
  | TBool
  | TArr Type Type
  | TPlus Type Type
  | TProduct Type Type
  | TFix TV Type
  | TNil
  | TList Type
  deriving (Eq, Ord, Show, Data)
instance Plated Type where plate = uniplate

data Scheme = Forall [Type] Type
  deriving (Show)

data CoreExpr
  = ENil
  | EInt  Int
  | EBool Bool
  | EVar Var
  | EBin Binop CoreExpr CoreExpr
  | EIf CoreExpr CoreExpr CoreExpr
  -- match e e1 x y e2 = case e of {Nil -> e1; Cons x y -> e2}
  | EMatch CoreExpr CoreExpr Var Var CoreExpr
  | ECon CoreExpr CoreExpr
  | ELet Var CoreExpr CoreExpr
  | EApp CoreExpr CoreExpr
  | ELam Var CoreExpr
  | EFix Var CoreExpr
  deriving (Eq, Show, Ord, Data)

instance Pretty CoreExpr where
  pretty = \case
    EInt i           -> p i
    EBool b          -> p b
    EVar (Var x)     -> p x
    EBin o e1 e2     -> parens (p o <+> p e1 <+> p e2)
    EIf c t e        -> p "if" <+> p c <+> p "then" <+> p t <+> p "else" <+> p e
    ELet x e e'      -> vsep [ p "let" <+> p x <+> p "=" <+> p e <+> p "in" , p e']
    EApp e1 e2       -> parens (p e1 <+> p e2)
    ELam x e         -> p "\\" <> p x <+> p "->" <+> p e
    EFix x e         -> p "fix " <+> p x <+> p e
    ENil             -> p "[]"
    ECon x y         -> parens (p "con" <+> p x <+> p y)
    EMatch e n x y c ->
      p "match" <+> p e <+> p "with" <+>
        braces (p "Nil ->" <+> p n <> p "; Cons" <+> p x <+> p y <+> p "->" <+> p c)
    where p = pretty

data Binop = Plus | Minus | Mul | Div | Eq | Ne | Lt | Le | And | Or | Cons
  deriving (Eq, Ord, Show, Data)

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

data Result = Result {resGoal :: (Var, Var), resResult :: Bool}
  deriving Show

data EqEnv = EqEnv
  { eqProgram :: Program
  , eqGoals   :: [(Var, Var)]
  } deriving Show

goalsToPrograms :: Program -> (Var, Var) -> (Bind, Bind)
goalsToPrograms bs (x1, x2) = ((x1, findBind bs x1), (x2, findBind bs x2))

findBind :: Program -> Var -> CoreExpr
findBind ((x,e):bs) y
  | x == y    = e
  | otherwise = findBind bs y
findBind [] _ = error "findBind: Not found"

mkPairs :: [String] -> [(Var, Var)]
mkPairs (x1:x2:rest) = (Var x1, Var x2) : mkPairs rest
mkPairs _            = []

instance IsString CoreExpr where
  fromString = EVar . Var

instance Plated CoreExpr where
  plate = uniplate

exprList :: [CoreExpr] -> CoreExpr
exprList = foldr (EBin Cons) ENil

isFix :: CoreExpr -> Bool
isFix (ELet x ex _) =  x `S.member` freeVars ex
isFix _             = False

-- | The free variables in an expression.
freeVars :: CoreExpr -> Set Var
freeVars = snd . freeVarsAndMap

-- | A mapping of all subexpressions to their free variables.
freeVarsMap :: CoreExpr -> Map CoreExpr (Set Var)
freeVarsMap = fst . freeVarsAndMap

freeVarsAndMap :: CoreExpr -> (Map CoreExpr (Set Var), Set Var)
freeVarsAndMap = para (\e acc ->
  let (ms, vss) = unzip acc
      -- In general, expression free variables include all free variables from
      -- subexpressions.
      vs = mconcat vss
      m = mconcat ms
      vs' = case e of
        -- In the case of a variable, add that variable as a free variable.
        EVar v               -> S.insert v vs
        -- In the case of 'let', 'lambda', and 'fix' expressions, variables
        -- which are bound are no longer free.
        ELet v _ _           -> S.delete v vs
        ELam v _             -> S.delete v vs
        EFix v _             -> S.delete v vs
        -- The match expression is the most complex. Remove the bound variables
        -- from the 'cons' case, but keep all free variables from the matched
        -- expression and the 'nil' case.
        EMatch tar nc v1 v2 cc ->
          freeVars tar <> freeVars nc <> S.delete v1 (S.delete v2 (freeVars cc))
        -- All other expressions propogate the transitive closure.
        _                    -> vs
  in (M.insert e vs' m, vs'))

-- | Substitute variables by corresponding expressions.
subst :: Map Var CoreExpr -> CoreExpr -> CoreExpr
subst m x = runReader (sub x) m
  where
    protect v e = local (M.delete v) (sub e)
    sub = \case
      -- If the variable is to be substituted, do so.
      EVar v -> M.findWithDefault (EVar v) v <$> ask
      -- 'let', 'lambda', 'fix', and 'match' expressions guard against the
      -- substitution of their bound variable(s).
      (ELet v e1 e2) -> ELet v <$> protect v e1 <*> protect v e2
      (ELam v e) -> ELam v <$> protect v e
      (EFix v e) -> EFix v <$> protect v e
      EMatch tar nc v1 v2 cc ->
        EMatch <$> sub tar
               <*> sub nc
               <*> pure v1
               <*> pure v2
               <*> local (M.delete v1 . M.delete v2) (sub cc)
      -- In all other cases, recursively substitute over subexpressions.
      e -> e & plate %%~ sub
