module Language.Haskell.Expr where
import Data.String
import Data.Bool
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Text.Parsec
import Text.Parsec.String
import qualified Text.Parsec.Token as T
import Text.Parsec.Language (emptyDef)
import Text.ParserCombinators.Parsec.Number


data Sort = BoolSort
            | IntegerSort
            | RealSort
  deriving (Eq,Show)

parseSort :: Parser Sort

parseSort = (reserved "Bool" >> return BoolSort)
         <|> (reserved "Int" >> return IntegerSort)
         <|> (reserved "Real" >> return RealSort)

parseArgument :: Parser String
parseArgument = do
  string "x!"
  number <- many digit
  return ("x!"++(number))

parseName :: Parser String
parseName = many (letter <|> digit <|> char '!') <* spaces


parseVariable :: Parser Sort
parseVariable = do 
  name <- parseArgument
  sort <- parseSort
  return sort
parseListSort :: Parser [Sort]

parseListSort = (reserved "Bool" >> return [] )
              <|> (do 
                     (parens (many (parens parseVariable))))

sort_list_pretty_print :: [Sort] -> String
sort_pretty_print :: Sort -> String

sort_pretty_print sort = case sort of
    BoolSort -> "Bool"
    IntegerSort -> "Int"
    RealSort -> "Real"

sort_list_pretty_print list = case list of
    x:xs -> (sort_pretty_print x) ++ "  " ++ (sort_list_pretty_print xs)
    otherwise -> ""

data Var = Var String Sort
     deriving (Eq, Show)

var_pretty_print :: Var -> String

var_pretty_print (Var name sort) = show name

data Constant = ConstantInt Integer
               | ConstantBool Bool
               | ConstantReal Float
  deriving (Eq, Show)

constant_pretty_print :: Constant -> String 

constant_pretty_print x = case x of 
                 ConstantInt value -> show value
                 ConstantBool value -> show value
                 ConstantReal value -> show value

data Function = Function String [Sort]
  deriving (Eq,Show)


parseFunction :: Parser Function
parseFunction = do 
  string "define-fun"
  spaces
  name <- parseName
  list <- parseListSort
  return (Function name list)

function_parameter_number :: Function -> Int

function_parameter_number (Function name list)
 | null list = 0
 | otherwise = length list

function_name :: Function -> String

function_name (Function name list) = name



data Parameter = ParameterVar Var 
  | ParameterConstant Constant
  deriving ( Show )

data Expr  = ExprVar Var
            |ExprConstant Constant
            |ApplyFunction Function [Parameter]
            |MkAdd [Expr]
            |MkMul [Expr]
            |MkSub [Expr]
            |MkDiv_1 Expr Expr
            |MkDiv_2 Expr Expr
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
            |MkEmpty
  deriving ( Show )

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
            MkDiv_1 expr1 expr2 -> "(div "++(expr_pretty_print expr1) ++ "  " ++(expr_pretty_print expr2)++ " )"
            MkDiv_2 expr1 expr2 -> "(/ "++(expr_pretty_print expr1) ++ "  " ++(expr_pretty_print expr2)++ " )"
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


data ParseState = ParseState (Map.Map String Expr) (Map.Map String Sort)

parseSymbol :: Parser String
parseSymbol = do
  string "a!"
  number <- many digit
  return ("a!"++(number))

parseSymbolExpr :: ParseState -> Parser Expr
parseSymbolExpr  (ParseState symbolMap sortMap) =  do
 symbolName <- parseSymbol
 return (symbolMap Map.! symbolName)

parseVar :: ParseState  -> Parser Expr
parseVar (ParseState symbolMap sortMap) = do
  name <- parseArgument
  return (ExprVar (Var name (sortMap Map.! name)))

-- parse float number might only apply for non-negative number, but it is fine here.
parseConstant :: ParseState -> Parser Expr
parseConstant (ParseState symbolMap sortMap)= 
             (reserved "true" >> return (ExprConstant (ConstantBool True)))
         <|> (reserved "false" >> return (ExprConstant (ConstantBool False)))
         <|> (do 
              value <- int
              return (ExprConstant (ConstantInt value)))
         <|> (do
              value <- floating
              return (ExprConstant (ConstantReal value))
              )

-- it seems not necessary to define parse function
parseApplyFunction :: ParseState -> Parser Expr
parseApplyFunction = undefined 

parseAdd :: ParseState -> Parser Expr
parseAdd parseState = do
  reserved "+"
  spaces
  exprs <- many (parsePureExpr parseState) 
  return (MkAdd exprs)

parseMul :: ParseState -> Parser Expr
parseMul parseState = do
  reserved "*"
  spaces
  exprs <- many (parsePureExpr parseState) 
  return (MkMul exprs)

parseSub :: ParseState -> Parser Expr
parseSub parseState = do
  reserved "-"
  spaces
  exprs <- many (parsePureExpr parseState) 
  return (MkSub exprs)

-- be careful it might be /
parseDiv1 :: ParseState -> Parser Expr
parseDiv1 parseState = do
  reserved "div"
  spaces
  expr1 <- parsePureExpr parseState
  expr2 <- parsePureExpr parseState
  return (MkDiv_1 expr1 expr2)

parseDiv2 :: ParseState -> Parser Expr
parseDiv2 parseState = do
  reserved "/"
  spaces
  expr1 <- parsePureExpr parseState
  expr2 <- parsePureExpr parseState
  return (MkDiv_2 expr1 expr2)

parseMod :: ParseState -> Parser Expr
parseMod parseState = do
  reserved "mod"
  spaces
  expr1 <- parsePureExpr parseState
  expr2 <- parsePureExpr parseState
  return (MkMod expr1 expr2)

parseRem :: ParseState -> Parser Expr
parseRem parseState = do
  reserved "rem"
  spaces
  expr1 <- parsePureExpr parseState
  expr2 <- parsePureExpr parseState
  return (MkRem expr1 expr2)

parseLt :: ParseState -> Parser Expr
parseLt parseState = do
  reserved "<"
  spaces
  expr1 <- parsePureExpr parseState
  expr2 <- parsePureExpr parseState
  return (MkLt expr1 expr2)

parseLe :: ParseState -> Parser Expr
parseLe parseState = do
  reserved "<="
  spaces
  expr1 <- parsePureExpr parseState
  expr2 <- parsePureExpr parseState
  return (MkLe expr1 expr2)

parseGt :: ParseState -> Parser Expr
parseGt parseState = do
  reserved ">"
  spaces
  expr1 <- parsePureExpr parseState
  expr2 <- parsePureExpr parseState
  return (MkGt expr1 expr2)

parseGe :: ParseState -> Parser Expr
parseGe parseState = do
  reserved ">="
  spaces
  expr1 <- parsePureExpr parseState
  expr2 <- parsePureExpr parseState
  return (MkGe expr1 expr2)

parseEq :: ParseState -> Parser Expr
parseEq parseState = do
  reserved "="
  spaces
  expr1 <- parsePureExpr parseState
  expr2 <- parsePureExpr parseState
  return (MkEq expr1 expr2)

parseNot :: ParseState -> Parser Expr
parseNot parseState = do
  reserved "not"
  spaces
  expr <- parsePureExpr parseState
  return (MkNot expr)

parseIff :: ParseState -> Parser Expr
parseIff parseState = do
  reserved "Iff"
  spaces
  expr1 <- parsePureExpr parseState
  expr2 <- parsePureExpr parseState
  return (MkIff expr1 expr2)

parseImplies :: ParseState -> Parser Expr
parseImplies parseState = do
  reserved "=>"
  spaces
  expr1 <- parsePureExpr parseState
  expr2 <- parsePureExpr parseState
  return (MkImplies expr1 expr2)

parseAnd :: ParseState -> Parser Expr
parseAnd parseState = do
  reserved "and"
  spaces
  exprs <- many (parsePureExpr parseState)
  return (MkAnd exprs)

parseOr :: ParseState -> Parser Expr
parseOr parseState = do
  reserved "or"
  spaces
  exprs <- many (parsePureExpr parseState)
  return (MkOr exprs)

parseExpr :: ParseState -> Parser Expr

parseExpr parseState = 
  parsePureExpr parseState
  <|> parseLetExpr parseState

parseLetSecondExpr :: (Bool,(Expr,ParseState))  -> Parser Expr

parseLetSecondExpr (x,(y,z)) = case x of
  True -> return y
  False -> parsePureExpr z

parseLetExpr ::ParseState -> Parser Expr

parseLetExpr parseState = do
 reserved "let"
 argumentParseResult <-parseLetListArgs parseState
 parseLetSecondExpr argumentParseResult
 

parseLetExprArgus ::ParseState -> Parser (ParseState,(Bool, Expr))
parseLetExprArgus parseState = undefined


parseSingleLetPair :: ParseState ->Parser ParseState

parseSingleLetPair (ParseState symbolMap sortMap) = do
 name <-parseSymbol
 expr <-parsePureExpr (ParseState symbolMap sortMap)
 let newMap = Map.insert name expr symbolMap
 return (ParseState newMap sortMap)

parseLetListArgs :: ParseState -> Parser (Bool,(Expr,ParseState))
parseLetListArgs parseState = 
  (do
  newParseState <- parens (parseSingleLetPair parseState)
  newResult<- (parseLetListArgs newParseState)
  return newResult)
  <|> (do 
       expr <- parens (parseLetExpr parseState)
       return (True,(expr,parseState)))
  <|> 
      return (False,(MkEmpty,parseState)) 


parseListLetPair :: ParseState -> Parser ParseState
parseListLetPair parseState = do
  newParseState <- parens (parseSingleLetPair parseState)
  newParseState'<- (parseListLetPair newParseState)
  return newParseState'

parsePureExpr :: ParseState -> Parser Expr

parsePureExpr parseState = 
      parseSymbolExpr parseState
  <|> parseVar parseState
  <|> parseConstant parseState
  <|> parens (parseAdd parseState)
  <|> parens (parseMul parseState)
  <|> parens (parseSub parseState)
  <|> parens (parseDiv1 parseState)
  <|> parens (parseDiv2 parseState)
  <|> parens (parseMod parseState)
  <|> parens (parseRem parseState)
  <|> parens (parseLt parseState)
  <|> parens (parseLe parseState)
  <|> parens (parseGt parseState)
  <|> parens (parseGe parseState)
  <|> parens (parseEq parseState)
  <|> parens (parseNot parseState)
  <|> parens (parseIff parseState)
  <|> parens (parseImplies parseState)
  <|> parens (parseAnd parseState)
  <|> parens (parseOr parseState)


lexer = T.makeTokenParser emptyDef
parens    = T.parens lexer
symbol     = T.symbol lexer
identifier = T.identifier lexer
reserved    = T.reserved lexer
