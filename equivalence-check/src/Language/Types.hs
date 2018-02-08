{-# LANGUAGE OverloadedStrings #-}
module Language.Types where

import           Control.Lens
import           Control.Monad.Reader

import           Data.Data.Lens
import           Data.Data (Data)

import           GHC.Exts( IsString(..) )
import           Text.Printf (printf)
import           Control.Exception
import           Data.Typeable
import qualified Data.List as L
import           System.Exit

import           Data.Monoid
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Map (Map)
import qualified Data.Map as M

type Program = [Bind]
type Bind    = (Var, CoreExpr)

newtype Var = Var String
  deriving (Eq, Ord, Data)
instance Show Var where show (Var x) = x

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

newtype Error = Error {errMsg :: String}
  deriving (Show, Typeable)

instance Exception Error

data CoreExpr
  = ENil
  | EInt  Int
  | EBool Bool
  | EVar Var
  | EBin Binop CoreExpr CoreExpr
  | EIf  CoreExpr  CoreExpr  CoreExpr
  -- match e e1 x y e2 = case e of {Nil -> e1; Cons x y -> e2}
  | EMatch CoreExpr CoreExpr Var Var CoreExpr
  | ECon CoreExpr CoreExpr
  | ELet Var   CoreExpr  CoreExpr
  | EApp CoreExpr  CoreExpr
  | ELam Var   CoreExpr
  | EFix Var   CoreExpr
  deriving (Eq, Show, Ord, Data)

data Binop
  = Plus
  | Minus
  | Mul
  | Div
  | Eq
  | Ne
  | Lt
  | Le
  | And
  | Or
  | Cons
  deriving (Eq, Ord, Show, Data)

data Result = Result {resGoal :: (Var, Var), resResult :: Bool}
  deriving Show

data EqEnv = EqEnv
  { eqProgram :: Program
  , eqGoals   :: [(Var, Var)]
  } deriving Show

data Config = Config
  { cfgFile    :: String
  , cfgQueries :: [(Var, Var)]
  } deriving (Show)

goalsToPrograms :: Program -> (Var, Var) -> (Bind, Bind)
goalsToPrograms bs (x1, x2) = ((x1, findBind bs x1), (x2, findBind bs x2))

findBind :: Program -> Var -> CoreExpr
findBind ((x,e):bs) y
  | x == y    = e
  | otherwise = findBind bs y
findBind [] _ = error "findBind: Not found"

makeConfig :: [String] -> IO Config
makeConfig (file : xs) =
  return $ Config file (mkPairs xs)
makeConfig _     = do
   putStrLn "No input file specified"
   exitWith $ ExitFailure 0

mkPairs :: [String] -> [(Var, Var)]
mkPairs (x1:x2:rest) = (Var x1, Var x2) : mkPairs rest
mkPairs _            = []


instance IsString CoreExpr where
  fromString = EVar . Var

instance Plated CoreExpr where
  plate = uniplate

data Value
  = VInt  Int
  | VBool Bool
  | VClos Env Var CoreExpr
  | VNil
  | VPair Value Value
  | VErr  String
  | VPrim (Value -> Value)

type Env = [(Var, Value)]

instance Eq Value where
  (VInt x1)     == (VInt x2)     = x1 == x2
  (VBool x1)    == (VBool x2)    = x1 == x2
  VNil          == VNil          = True
  (VPair x1 y1) == (VPair x2 y2) = x1 == x2 && y1 == y2
  _             == _             = False

instance Show Value where
  show = valueString

binopString :: Binop -> String
binopString = \case
  Plus  -> "+"
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

valueString :: Value -> String
valueString = \case
  VInt i        -> printf "%d" i
  VBool b       -> printf "%s" (show b)
  VClos env x v -> printf "<<%s, \\%s -> %s>>" (envString env) (show x) (show v)
  VPair v w     -> printf "(%s : %s)" (show v) (show w)
  VErr s        -> printf "ERROR: %s" s
  VNil          -> "[]"
  VPrim _       -> "<<primitive-function>>"

envString :: Env -> String
envString env = printf "{ %s }" (L.intercalate ", " bs)
  where
    bs        = [ x ++ " := " ++ show v | (Var x, v) <- env]

exprString :: CoreExpr -> String
exprString = \case
  EInt i       -> printf "%d" i
  EBool b      -> printf "%s" (show b)
  EVar (Var x) -> x
  EBin o e1 e2 -> printf "(%s %s %s)" (go e1) (binopString o) (go e2)
  EIf c t e    -> printf "if %s then %s else %s" (go c) (go t) (go e)
  ELet x e e'  -> printf "let %s = %s in \n %s" (show x) (go e) (go e')
  EApp e1 e2   -> printf "(%s %s)" (go e1) (go e2)
  ELam x e     -> printf "\\%s -> %s" (show x) (go e)
  EFix x e     -> printf "fix %s %s" (show x) (go e)
  ENil           -> "[]"
  EMatch e n x y c -> printf "match %s with {Nil -> %s; Cons %s %s -> %s}"  
                       (go e) (go n) (show x) (show y) (go c)
  where
    go = exprString

bindString :: Bind -> String
bindString (x, e) = printf "let %s =\n  %s" (show x) (exprString e)

progString :: Program -> String
progString xes = L.intercalate "\n" (bindString <$> xes)

--------------------------------------------------------------------------------

class IsCoreExpr a where
  expr  :: a -> CoreExpr
  value :: a -> Value

instance IsCoreExpr Int where
  expr  = EInt
  value = VInt

instance IsCoreExpr Bool where
  expr  = EBool
  value = VBool

exprList :: [CoreExpr] -> CoreExpr
exprList = foldr (EBin Cons) ENil

valueList :: [Value] -> Value
valueList = foldr VPair VNil

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

test :: CoreExpr
test = ELam (Var "x") (EBin Plus (EVar (Var "x")) (EInt 3))

test2 = subst (M.singleton (Var "x") (EInt 5)) test
