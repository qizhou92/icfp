module Language.Haskell.Expr where
import Data.String
import Data.Bool
import Data.List

data Sort = BoolSort
            | IntegerSort
            | RealSort
	deriving (Eq)

data Var = Var String Sort
     deriving (Eq)

var_pretty_print :: Var -> String

var_pretty_print (Var name sort) = show name

data Constant = ConstantInt Integer
               | ConstantBool Bool
               | ConstantReal Rational

constant_pretty_print :: Constant -> String 

constant_pretty_print x = case x of 
                 ConstantInt value -> show value
                 ConstantBool value -> show value
                 ConstantReal value -> show value

data Function = Function String [Sort]
	deriving (Eq)

function_parameter_number :: Function -> Int

function_parameter_number (Function name list)
 | null list = 0
 | otherwise = length list

function_name :: Function -> String

function_name (Function name list) = name


data Parameter = ParameterVar Var 
			   | ParameterConstant Constant

data Expr  = ExprVar Var
            |ExprConstant Constant
            |ApplyFunction Function [Parameter]
            |MkAdd [Expr]
            |MkMul [Expr]
            |MkSub [Expr]
            |MkDiv Expr Expr
            |MkMod Expr Expr
            |MkRem Expr Expr
            |MkLt  Expr Expr
            |MkLe Expr Expr
            |MkGt Expr Expr
            |MkGe Expr Expr
            |MkEq Expr Expr
            |MkNot Expr
            |MkIff Expr Expr
            |MkImplies Expr Expr
            |MkAnd [Expr]
            |MkOr  [Expr]

list_parameter_pretty_print :: [Parameter] -> String



list_parameter_pretty_print list = case list of
	x:xs -> (parameter_pretty_print x) ++ "  " ++ (list_parameter_pretty_print xs)
	otherwise -> ""
parameter_pretty_print :: Parameter -> String

parameter_pretty_print x = case x of 
                     ParameterVar y -> (var_pretty_print y) ++ "  "
                     ParameterConstant y ->(constant_pretty_print y) ++ "  "

list_expr_pretty_print :: [Expr] -> String
list_expr_pretty_print list = case list of
	x:xs -> (expr_pretty_print x) ++ "  " ++ (list_expr_pretty_print xs)
	otherwise -> ""  

expr_pretty_print :: Expr -> String

expr_pretty_print x = case x of
            ExprVar y -> var_pretty_print y
            ExprConstant y -> constant_pretty_print y
            ApplyFunction f args -> case args of 
                                 x:xs -> (function_name f)
                                 otherwise -> "( "++(function_name f)++(list_parameter_pretty_print args)++" )"
            MkAdd exprs -> "(+ "++(list_expr_pretty_print exprs)++" )"
            MkMul exprs -> "(* "++(list_expr_pretty_print exprs)++" )"
            MkSub exprs -> "(- "++(list_expr_pretty_print exprs)++" )"
            MkDiv expr1 expr2 -> "(div "++(expr_pretty_print expr1) ++ "  " ++(expr_pretty_print expr2)++ " )"
            MkMod expr1 expr2 -> "(mod "++(expr_pretty_print expr1) ++ "  "++(expr_pretty_print expr2) ++ " )"
            MkRem expr1 expr2 -> "(rem "++(expr_pretty_print expr1) ++ "  " ++ (expr_pretty_print expr2) ++ " )"
            MkLt  expr1 expr2 ->"(< " ++ (expr_pretty_print expr1) ++ "  " ++ (expr_pretty_print expr2) ++ " )"
            MkLe expr1 expr2 -> "(<= " ++ (expr_pretty_print expr1) ++ "  " ++ (expr_pretty_print expr2) ++ " )"
            MkGt expr1 expr2 ->"(> " ++ (expr_pretty_print expr1) ++ "  " ++ (expr_pretty_print expr2) ++ " )"
            MkGe expr1 expr2 ->"(>= " ++ (expr_pretty_print expr1) ++ "  " ++ (expr_pretty_print expr2) ++ " )"
            MkEq expr1 expr2 -> "(= " ++ (expr_pretty_print expr1) ++ "  " ++ (expr_pretty_print expr2) ++ " )"
            MkNot expr1      -> "(not " ++ (expr_pretty_print expr1) ++ " )"
            MkIff expr1 expr2  -> "(iff " ++ (expr_pretty_print expr1) ++ "  " ++ (expr_pretty_print expr2) ++ " )"
            MkImplies expr1 expr2 -> "(=> " ++ (expr_pretty_print expr1) ++ "  " ++ (expr_pretty_print expr2) ++ " )" 
            MkAnd exprs -> "(and " ++ (list_expr_pretty_print exprs) ++ " )"
            MkOr  exprs -> "(or " ++ (list_expr_pretty_print exprs) ++ " )"


