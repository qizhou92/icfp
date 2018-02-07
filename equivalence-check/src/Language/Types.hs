{-# LANGUAGE OverloadedStrings #-}
module Language.Types where

import           GHC.Exts( IsString(..) )
import           Text.Printf (printf)
import           Text.PrettyPrint.HughesPJ hiding ((<>))
import           Control.Exception
import           Data.Typeable
import qualified Data.List as L
import           System.Exit
-- import           Language.Equivalence.Misc
-- import           Language.Equivalence.Expr hiding (Var)

import Data.Monoid
import qualified Data.Set as S 
import qualified Data.Map as Map

type Program = [Bind]
type Bind    = (Var, CoreExpr)

goalsToPrograms :: Program -> (Var, Var) -> (Bind, Bind)
goalsToPrograms bs (x1, x2) = ((x1, findBind bs x1), (x2, findBind bs x2))

findBind :: Program -> Var -> CoreExpr
findBind ((x,e):bs) y
  | x == y    = e
  | otherwise = findBind bs y
findBind [] _ = error "findBind: Not found"

data Result = Result {resGoal :: (Var, Var), resResult :: Bool}
  deriving Show

-- instance Show Result where
--   show (Result (x1, x2) b) = printf "Programs %s and %s %s equivalent" (showPpr x1) (showPpr x2) res
--     where
--       res :: String
--       res | b              = " are "
--           | otherwise      = " are not "

data EqEnv
  = EqEnv { eqProgram :: Program
          , eqGoals   :: [(Var, Var)]
          }
  deriving Show

-- instance Show EqEnv where
   -- show (EqEnv p x) = printf " EqEnv: goals = %s \nprogram:\n%s" gs ps
   --    where
   --      gs          = unlines (showPpr <$> x)
   --      ps          = progString p


data Config = Config
  { cfgFile    :: String
  , cfgQueries :: [(Var, Var)]
  } deriving (Show)

makeConfig :: [String] -> IO Config
makeConfig (file : xs) =
  return $ Config file (mkPairs xs)
makeConfig _     = do
   putStrLn "No input file specified"
   exitWith $ ExitFailure 0

mkPairs :: [String] -> [(Var, Var)]
mkPairs (x1:x2:rest) = (Var x1, Var x2) : mkPairs rest
mkPairs _            = []


data Error = Error {errMsg :: String}
             deriving (Show, Typeable)

instance Exception Error

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
  deriving (Eq, Ord, Show)

data Var = Var String
           deriving (Eq, Ord)

instance Show Var where
  show (Var x) = x

-- instance PPrint Var where
--   ppr = text . show

instance IsString CoreExpr where
  fromString = EVar . Var

data CoreExpr = ENil 
  |EInt  Int
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
  deriving (Eq, Show, Ord)

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
binopString Plus  = "+"
binopString Minus = "-"
binopString Mul   = "*"
binopString Div   = "/"
binopString Eq    = "="
binopString Ne    = "!="
binopString Lt    = "<"
binopString Le    = "<="
binopString And   = "&&"
binopString Or    = "||"
binopString Cons  = ":"

valueString :: Value -> String
valueString (VInt i)        = printf "%d" i
valueString (VBool b)       = printf "%s" (show b)
valueString (VClos env x v) = printf "<<%s, \\%s -> %s>>" (envString env) (show x) (show v)
valueString (VPair v w)     = printf "(%s : %s)" (show v) (show w)
valueString (VErr s)        = printf "ERROR: %s" s
valueString VNil            = "[]"
valueString (VPrim _)       = "<<primitive-function>>"

envString :: Env -> String
envString env = printf "{ %s }" (L.intercalate ", " bs)
  where
    bs        = [ x ++ " := " ++ show v | (Var x, v) <- env]

exprString :: CoreExpr -> String
exprString (EInt i)       = printf "%d" i
exprString (EBool b)      = printf "%s" (show b)
exprString (EVar (Var x)) = x
exprString (EBin o e1 e2) = printf "(%s %s %s)" (exprString e1) (binopString o) (exprString e2)
exprString (EIf c t e)    = printf "if %s then %s else %s" (exprString c) (exprString t) (exprString e)
exprString (ELet x e e')  = printf "let %s = %s in \n %s" (show x) (exprString e) (exprString e')
exprString (EApp e1 e2)   = printf "(%s %s)" (exprString e1) (exprString e2)
exprString (ELam x e)     = printf "\\%s -> %s" (show x) (exprString e)
exprString (EFix x e)     = printf "fix %s %s" (show x) (exprString e)
exprString ENil           = "[]"
exprString (EMatch e n x y c) = printf "match %s with {Nil -> %s; Cons %s %s -> %s}"  
                                       (exprString e) (exprString n) (show x) (show y) (exprString c)

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
isFix (ELet x ex _) =  x `S.member` (freeVars ex)
isFix _             = False 

freeVars :: CoreExpr -> S.Set Var
freeVars (EVar v)       = S.singleton v
freeVars (EInt _)       = mempty
freeVars (EBool _)      = mempty
freeVars ENil           = mempty
freeVars (EBin _ e1 e2) = freeVars e1 <> freeVars e2 
freeVars (EIf e e1 e2)  = freeVars e <> freeVars e1 <> freeVars e2 
freeVars (ELet x ex e)  = S.filter (/= x) (freeVars ex <> freeVars e)
freeVars (EApp e1 e2)   = freeVars e1 <> freeVars e2 
freeVars (ELam x e)     = S.filter (/= x) (freeVars e)
freeVars (EFix x e)     = S.filter (/= x) (freeVars e)
freeVars (EMatch e en x y ec) 
  = freeVars e <> freeVars en <> S.filter (\v -> (v /= x && v /= y)) (freeVars ec)


getFreeVarsMap :: CoreExpr -> Map.Map CoreExpr [Var]
getFreeVarsMap e@(EVar v) = Map.singleton e [v]
getFreeVarsMap e@(EBin _ e1 e2) = do
  let leftMap = getFreeVarsMap e1
  let rightMap = getFreeVarsMap e2
  let allVars = (leftMap Map.! e1) ++ (rightMap Map.! e2)
  Map.insert e allVars (Map.union leftMap rightMap)
getFreeVarsMap e@(EIf e1 e2 e3) = do
  let map1 = getFreeVarsMap e1
  let map2 = getFreeVarsMap e2
  let map3 = getFreeVarsMap e3
  let allVars = (map1 Map.! e1) ++ (map2 Map.! e2) ++ (map3 Map.! e3)
  Map.insert e allVars (Map.union (Map.union map1 map2) map3)
getFreeVarsMap e@(ELet x e1 e2) = do
  let map1 = getFreeVarsMap e1
  let map2 = getFreeVarsMap e2
  let allVars = filter (/=x) ((map1 Map.! e1) ++ (map2 Map.! e2))
  Map.insert e allVars (Map.union map1 map2)
getFreeVarsMap e@(EApp e1 e2) = do
  let map1 = getFreeVarsMap e1
  let map2 = getFreeVarsMap e2
  let allVars = (map1 Map.! e1) ++ (map2 Map.! e2)
  Map.insert e allVars (Map.union map1 map2)
getFreeVarsMap e@(ELam x e1) = do
  let map1 = getFreeVarsMap e1
  let allVars =filter (/= x) (map1 Map.! e1)
  Map.insert e allVars map1 
getFreeVarsMap e@(EFix x e1) = do 
  let map1 = getFreeVarsMap e1
  let allVars =filter (/= x) (map1 Map.! e1)
  Map.insert e allVars map1 
getFreeVarsMap e@(EMatch e1 e2 x y e3) = do
  let map1 = getFreeVarsMap e1
  let map2 = getFreeVarsMap e2
  let map3 = getFreeVarsMap e3
  let allVars = (map1 Map.! e1) ++ (map2 Map.! e2) ++(filter (\v -> (v /= x && v /= y)) (map3 Map.! e3))
  Map.insert e allVars (Map.union (Map.union map1 map2) map3)
getFreeVarsMap e = Map.singleton e []

subst :: (Var, CoreExpr) -> CoreExpr -> CoreExpr
subst (x,e) (EVar v)
  | x == v        
  = e 
  | otherwise
  = EVar v 
subst _ e@(EInt _)      = e
subst _ e@(EBool _)      = e
subst _ e@ENil           = e
subst su (EBin b e1 e2) = EBin b (subst su e1) (subst su e2)
subst su (EIf e e1 e2)  = EIf (subst su e) (subst su e1) (subst su e2)
subst su@(y,_) (ELet x ex e)
  | x == y 
  = ELet x ex e 
  | otherwise
  = ELet x (subst su ex) (subst su e)
subst su (EApp e1 e2)   
  = EApp (subst su e1) (subst su e2) 
subst su@(y,_) (ELam x e)     
  | x == y 
  = ELam x e 
  | otherwise
  = ELam x (subst su e)
subst su@(y,_) (EFix x e)     
  | x == y 
  = EFix x e 
  | otherwise
  = EFix x (subst su e)
subst su@(z,_) (EMatch e e1 x y e2) 
  = EMatch (subst su e) (subst su e1) x y 
           (if (x == z || y == z) then e2 else subst su e2)




-------------------------------------------------------------------------------
-- | Types --------------------------------------------------------------------
-------------------------------------------------------------------------------

type TV = String
data Type = TVar TV
           | TInt
           | TBool
           | TArr Type Type
           | TPlus Type Type
           | TProduct Type Type
           | TFix TV Type
           | TNil
           | TList Type 
  deriving (Eq, Ord,Show)


data Scheme = Forall [Type] Type
  deriving (Show)
