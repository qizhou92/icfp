module Language.Equivalence.Expr where
import qualified Data.Map as Map
import Text.Parsec
import Text.Parsec.String
import qualified Text.Parsec.Token as T
import Text.Parsec.Language (emptyDef)
import Text.ParserCombinators.Parsec.Number


data Sort = BoolSort
            | IntegerSort
            | RealSort
  deriving (Eq,Show,Ord)

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
  parseArgument
  spaces
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
    [] -> ""

data Var = Var String Sort
     deriving (Eq, Show)

var_pretty_print :: Var -> String

var_pretty_print (Var name _) = show name

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
  deriving (Eq,Show,Ord)


parseFunction :: Parser Function
parseFunction = do 
  string "define-fun"
  spaces
  name <- parseName
  list <- parseListSort
  spaces
  reserved "Bool"
  return (Function name list)

function_parameter_number :: Function -> Int

function_parameter_number (Function _ list)
 | null list = 0
 | otherwise = length list

function_name :: Function -> String

function_name (Function name _) = name



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
   [] -> ""

parameter_pretty_print :: Parameter -> String

parameter_pretty_print x = case x of 
                     ParameterVar y -> (var_pretty_print y) ++ "  "
                     ParameterConstant y ->(constant_pretty_print y) ++ "  "

list_expr_pretty_print :: [Expr] -> String

list_expr_pretty_print list = case list of
  x:xs -> (expr_pretty_print x) ++ "  " ++ (list_expr_pretty_print xs)
  [] -> ""  

expr_pretty_print :: Expr -> String

expr_pretty_print x = case x of
            ExprVar y -> var_pretty_print y
            ExprConstant y -> constant_pretty_print y
            ApplyFunction f args -> case args of 
                                 _:_ -> (function_name f)
                                 [] -> "( "++(function_name f)++(list_parameter_pretty_print args)++" )"
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
            MkEmpty -> ""


data ParseState = ParseState (Map.Map String Expr) (Map.Map String Sort)

parseSymbol :: Parser String
parseSymbol = do
  string "a!"
  number <- many digit
  spaces
  return ("a!"++(number))

parseSymbolExpr :: ParseState -> Parser Expr
parseSymbolExpr  (ParseState symbolMap _) =  do
 symbolName <- parseSymbol
 return (symbolMap Map.! symbolName)

parseVar :: ParseState  -> Parser Expr
parseVar (ParseState _ sortMap) = do
  name <- parseArgument
  spaces
  return (ExprVar (Var name (sortMap Map.! name)))

-- parse float number might only apply for non-negative number, but it is fine here.
parseConstant :: ParseState -> Parser Expr
parseConstant  _ = 
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
  exprs <- many (parseExpr parseState) 
  return (MkAdd exprs)

parseMul :: ParseState -> Parser Expr
parseMul parseState = do
  reserved "*"
  spaces
  exprs <- many (parseExpr parseState) 
  return (MkMul exprs)

parseSub :: ParseState -> Parser Expr
parseSub parseState = do
  reserved "-"
  spaces
  exprs <- many (parseExpr parseState) 
  return (mkSubExpr exprs)

mkSubExpr:: [Expr] -> Expr
mkSubExpr list 
   |(length list) == 1 = (subExprToNegativeExpr (head list))  
   |otherwise = (MkSub list)

subExprToNegativeExpr :: Expr -> Expr
subExprToNegativeExpr theExpr = case theExpr of
  ExprConstant (ConstantInt value) -> ExprConstant (ConstantInt (0-value))
  _ -> (MkSub ((ExprConstant (ConstantInt 0)):[theExpr]))



-- be careful it might be /
parseDiv1 :: ParseState -> Parser Expr
parseDiv1 parseState = do
  reserved "div"
  spaces
  expr1 <- parseExpr parseState
  spaces
  expr2 <- parseExpr parseState
  return (MkDiv_1 expr1 expr2)

parseDiv2 :: ParseState -> Parser Expr
parseDiv2 parseState = do
  reserved "/"
  spaces
  expr1 <- parseExpr parseState
  spaces
  expr2 <- parseExpr parseState
  return (MkDiv_2 expr1 expr2)

parseMod :: ParseState -> Parser Expr
parseMod parseState = do
  reserved "mod"
  spaces
  expr1 <- parseExpr parseState
  spaces
  expr2 <- parseExpr parseState
  return (MkMod expr1 expr2)

parseRem :: ParseState -> Parser Expr
parseRem parseState = do
  reserved "rem"
  spaces
  expr1 <- parseExpr parseState
  spaces
  expr2 <- parseExpr parseState
  return (MkRem expr1 expr2)

parseLt :: ParseState -> Parser Expr
parseLt parseState = do
  reserved "<"
  spaces
  expr1 <- parseExpr parseState
  spaces
  expr2 <- parseExpr parseState
  return (MkLt expr1 expr2)

parseLe :: ParseState -> Parser Expr
parseLe parseState = do
  reserved "<="
  spaces
  expr1 <- parseExpr parseState
  spaces
  expr2 <- parseExpr parseState
  return (MkLe expr1 expr2)

parseGt :: ParseState -> Parser Expr
parseGt parseState = do
  reserved ">"
  spaces
  expr1 <- parseExpr parseState
  spaces
  expr2 <- parseExpr parseState
  return (MkGt expr1 expr2)

parseGe :: ParseState -> Parser Expr
parseGe parseState = do
  reserved ">="
  spaces
  expr1 <- parseExpr parseState
  spaces
  expr2 <- parseExpr parseState
  return (MkGe expr1 expr2)

parseEq :: ParseState -> Parser Expr
parseEq parseState = do
  reserved "="
  spaces
  expr1 <- parseExpr parseState
  spaces
  expr2 <- parseExpr parseState
  return (MkEq expr1 expr2)

parseNot :: ParseState -> Parser Expr
parseNot parseState = do
  reserved "not"
  spaces
  expr <- parseExpr parseState
  return (MkNot expr)

parseIff :: ParseState -> Parser Expr
parseIff parseState = do
  reserved "Iff"
  spaces
  expr1 <- parseExpr parseState
  spaces
  expr2 <- parseExpr parseState
  return (MkIff expr1 expr2)

parseImplies :: ParseState -> Parser Expr
parseImplies parseState = do
  reserved "=>"
  spaces
  expr1 <- parseExpr parseState
  spaces
  expr2 <- parseExpr parseState
  return (MkImplies expr1 expr2)

parseAnd :: ParseState -> Parser Expr
parseAnd parseState = do
  reserved "and"
  spaces
  exprs <- many (parseExpr parseState)
  return (MkAnd exprs)

parseOr :: ParseState -> Parser Expr
parseOr parseState = do
  reserved "or"
  spaces
  exprs <- many (parseExpr parseState)
  return (MkOr exprs)

parseLetSecondExpr :: (Bool,(Expr,ParseState))  -> Parser Expr

parseLetSecondExpr (x,(y,z)) = case x of
  True -> return y
  False -> parseExpr z

parseLetExpr ::ParseState -> Parser Expr

parseLetExpr parseState = do
 reserved "let"
 argumentParseResult <- parens (parseLetListArgs parseState)
 parseLetSecondExpr argumentParseResult


parseSingleLetPair :: ParseState ->Parser ParseState

parseSingleLetPair (ParseState symbolMap sortMap) = do
 name <-parseSymbol
 spaces
 expr <-parseExpr (ParseState symbolMap sortMap)
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

parseExpr :: ParseState -> Parser Expr

parseExpr parseState = 
      parseSymbolExpr parseState
  <|> parseVar parseState
  <|> parseConstant parseState
  <|> parens (parseNeedParensExpr parseState)

parseNeedParensExpr parseState = 
      parseAdd parseState
  <|> parseMul parseState
  <|> parseSub parseState
  <|> parseDiv1 parseState
  <|> parseDiv2 parseState
  <|> parseMod parseState
  <|> parseRem parseState
  <|> parseLe parseState
  <|> parseLt parseState
  <|> parseGe parseState
  <|> parseGt parseState
  <|> parseEq parseState
  <|> parseNot parseState
  <|> parseIff parseState
  <|> parseImplies parseState
  <|> parseAnd parseState
  <|> parseOr parseState
  <|> parseLetExpr parseState
parseSatResult :: Parser Bool
parseSatResult = 
  (do
  reserved "unsat"
  spaces
  return True)
  <|> (do
  reserved "sat"
  spaces
  return False
  )
parseCHCResult :: Parser (Bool, (Map.Map Function Expr))
parseCHCResult = do
  result <- parseSatResult
  predicateSoltuions <- parsePredicatesSoltuions result
  return (result,predicateSoltuions)

parsePredicatesSoltuions :: Bool -> Parser (Map.Map Function Expr)
parsePredicatesSoltuions result = case result of
 True  ->(do  
          result <- parseAllPredicatesSoltuions
          return result)
 False ->  return Map.empty

parseAllPredicatesSoltuions :: Parser (Map.Map Function Expr)
parseAllPredicatesSoltuions = 
  do
    (x,y) <- parens (parseFunctionInvariant)
    oldMap <- parseAllPredicatesSoltuions
    let theMap = Map.insert x y oldMap
    return theMap
  <|>
    return Map.empty 


parseFunctionInvariant :: Parser (Function,Expr)
parseFunctionInvariant = do
  function <- parseFunction
  expr <- parseExpr (ParseState Map.empty (getVariableSortMap function))
  return (function,expr)

getVariableSortMap :: Function -> (Map.Map String Sort)
getVariableSortMap (Function _ list) = getSortMap 1 list

getSortMap :: Int -> [Sort] -> (Map.Map String Sort)
getSortMap number list = case list of
 x:xs -> Map.insert ("x!"++show(number)) x (getSortMap (number+1) xs)
 [] -> Map.empty

lexer = T.makeTokenParser emptyDef
parens    = T.parens lexer
symbol     = T.symbol lexer
identifier = T.identifier lexer
reserved    = T.reserved lexer
