module Language.Haskell.Expr where
import Data.String
import Data.Bool
import Data.List

data Sort = BoolSort
            | IntegerSort
            | RealSort
            | Sort String
	deriving (Eq)

data Var = Var String Sort
     deriving (Eq)

var_pretty_print :: Var -> IO ()

var_pretty_print (Var name sort) = print name

data Constant = ConstantInt Integer
               | ConstantBool Bool
               | ConstantReal Rational

constant_pretty_print :: Constant -> IO() 

constant_pretty_print x = case x of 
                 ConstantInt value -> print value
                 ConstantBool value -> print value
                 ConstantReal value -> print value

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

list_parameter_pretty_print :: [Parameter] -> IO ()



list_parameter_pretty_print = mapM_ parameter_pretty_print
parameter_pretty_print :: Parameter -> IO ()

parameter_pretty_print x = case x of 
                     ParameterVar y -> var_pretty_print y
                     ParameterConstant y -> constant_pretty_print y

list_expr_pretty_print :: [Expr] -> IO ()
list_expr_pretty_print = mapM_ expr_pretty_print

expr_pretty_print :: Expr -> IO ()

expr_pretty_print x = case x of
            ExprVar y -> var_pretty_print y
            ExprConstant y -> constant_pretty_print y
            ApplyFunction f args -> do
            	                            print "("
            	                            print (function_name f)
            	                            list_parameter_pretty_print args
            	                            print ")"
            MkAdd exprs -> do
            	              print "(+ "
            	              list_expr_pretty_print exprs
            	              print " )"
            MkMul exprs -> do 
            	              print "(* "
            	              list_expr_pretty_print exprs
            	              print " )"
            MkSub exprs -> do
            	              print "(- "
            	              list_expr_pretty_print exprs
            	              print " )"
            MkDiv expr1 expr2 -> do 
            	              print "(div "
            	              expr_pretty_print expr1
            	              expr_pretty_print expr2
            	              print " )"
            MkMod expr1 expr2 -> do
            	              print "(mod "
            	              expr_pretty_print expr1
            	              expr_pretty_print expr2
            	              print " )"
            MkRem expr1 expr2 -> do
            	              print "(rem "
            	              expr_pretty_print expr1
            	              expr_pretty_print expr2
            	              print " )"
            MkLt  expr1 expr2 -> do
            	              print "(< "
            	              expr_pretty_print expr1
            	              expr_pretty_print expr2
            	              print " )"
            MkLe expr1 expr2 -> do
            		          print "(<= "
            		          expr_pretty_print expr1
            		          expr_pretty_print expr2
            		          print " )"
            MkGt expr1 expr2 -> do
            	              print "(> "
            	              expr_pretty_print expr1
            	              expr_pretty_print expr2
            	              print " )"
            MkGe expr1 expr2 -> do
            	              print "(>= "
            	              expr_pretty_print expr1
            	              expr_pretty_print expr2
            	              print " )"
            MkEq expr1 expr2 -> do
            	              print "(= "
            	              expr_pretty_print expr1
            	              expr_pretty_print expr2
            	              print " )"
            MkNot expr1      -> do
            	              print "(not "
            	              expr_pretty_print expr1
            	              print " )"
            MkIff expr1 expr2  -> do
            	              print "(iff "
            	              expr_pretty_print expr1
            	              expr_pretty_print expr2
            	              print " )"
            MkImplies expr1 expr2 -> do
                              print "(=> "
                              expr_pretty_print expr1
                              expr_pretty_print expr2
                              print " )" 
            MkAnd exprs -> do
            	           print "(and "
            	           list_expr_pretty_print exprs
            	           print " )"
            
            MkOr  exprs -> do
            	           print "(or "
            	           list_expr_pretty_print exprs
            	           print " )"


