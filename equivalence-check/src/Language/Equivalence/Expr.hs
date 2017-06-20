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
parseName = many (letter <|> digit <|> char '!' <|> char '@') <* spaces


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
    x:xs ->" "++(sort_pretty_print x)++ (sort_list_pretty_print xs)
    [] -> ""

data Var = Var String Sort
     deriving (Eq, Show,Ord)

var_pretty_print :: Var -> String

var_pretty_print (Var name _) = name

data Constant = ConstantInt Int
               | ConstantBool Bool
               | ConstantReal Float
  deriving (Eq, Show,Ord)

constant_pretty_print :: Constant -> String 

constant_pretty_print x = case x of 
                 ConstantInt value -> show value
                 ConstantBool value -> if value then "true"
                                          else  "false"
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
  deriving ( Show,Eq,Ord )

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
  deriving (Eq,Ord )
instance Show Expr where
  show = expr_pretty_print 

collectVar :: Expr -> [Var]
collectVar x = case x of
  ExprVar var -> [var]
  MkAdd list -> concat (map collectVar list)
  MkMul list -> concat (map collectVar list)
  MkSub list -> concat (map collectVar list)
  MkDiv_1 expr1 expr2 -> (collectVar expr1) ++ (collectVar expr2)
  MkDiv_2 expr1 expr2 -> (collectVar expr1) ++ (collectVar expr2)
  MkMod expr1 expr2 -> (collectVar expr1) ++ (collectVar expr2)
  MkRem expr1 expr2 -> (collectVar expr1) ++ (collectVar expr2)
  MkLt expr1 expr2 -> (collectVar expr1) ++ (collectVar expr2)
  MkLe expr1 expr2 -> (collectVar expr1) ++ (collectVar expr2)
  MkGt expr1 expr2 -> (collectVar expr1) ++ (collectVar expr2)
  MkGe expr1 expr2 -> (collectVar expr1) ++ (collectVar expr2)
  MkEq expr1 expr2 -> (collectVar expr1) ++ (collectVar expr2)
  MkNot expr1 -> (collectVar expr1)
  MkIff expr1 expr2 -> (collectVar expr1) ++ (collectVar expr2)
  MkImplies expr1 expr2 -> (collectVar expr1) ++ (collectVar expr2)
  MkAnd list -> concat (map collectVar list)
  MkOr list -> concat (map collectVar list)
  _ -> []
list_parameter_pretty_print :: [Parameter] -> String



list_parameter_pretty_print list = case list of
   x:xs -> (parameter_pretty_print x) ++ " " ++ (list_parameter_pretty_print xs)
   [] -> ""

parameter_pretty_print :: Parameter -> String

parameter_pretty_print x = case x of 
                     ParameterVar y -> (var_pretty_print y) ++ " "
                     ParameterConstant y ->(constant_pretty_print y) ++ " "

list_expr_pretty_print :: [Expr] -> String

list_expr_pretty_print list = case list of
  x:xs -> (expr_pretty_print x) ++ " " ++ (list_expr_pretty_print xs)
  [] -> ""  

expr_pretty_print :: Expr -> String

expr_pretty_print x = case x of
            ExprVar y -> var_pretty_print y
            ExprConstant y -> constant_pretty_print y
            ApplyFunction f args -> case args of 
                                 _:_ -> "("++(function_name f)++" "++(list_parameter_pretty_print args)++")"
                                 [] -> (function_name f)
            MkAdd exprs -> "(+ "++(list_expr_pretty_print exprs)++")"
            MkMul exprs -> "(* "++(list_expr_pretty_print exprs)++")"
            MkSub exprs -> "(- "++(list_expr_pretty_print exprs)++")"
            MkDiv_1 expr1 expr2 -> "(div "++(expr_pretty_print expr1) ++ " " ++(expr_pretty_print expr2)++ ")"
            MkDiv_2 expr1 expr2 -> "(/ "++(expr_pretty_print expr1) ++ " " ++(expr_pretty_print expr2)++ ")"
            MkMod expr1 expr2 -> "(mod "++(expr_pretty_print expr1) ++ " "++(expr_pretty_print expr2) ++ ")"
            MkRem expr1 expr2 -> "(rem "++(expr_pretty_print expr1) ++ " " ++ (expr_pretty_print expr2) ++ ")"
            MkLt  expr1 expr2 ->"(< " ++ (expr_pretty_print expr1) ++ " " ++ (expr_pretty_print expr2) ++ ")"
            MkLe expr1 expr2 -> "(<= " ++ (expr_pretty_print expr1) ++ " " ++ (expr_pretty_print expr2) ++ ")"
            MkGt expr1 expr2 ->"(> " ++ (expr_pretty_print expr1) ++ " " ++ (expr_pretty_print expr2) ++ ")"
            MkGe expr1 expr2 ->"(>= " ++ (expr_pretty_print expr1) ++ " " ++ (expr_pretty_print expr2) ++ ")"
            MkEq expr1 expr2 -> "(= " ++ (expr_pretty_print expr1) ++ " " ++ (expr_pretty_print expr2) ++ ")"
            MkNot expr1      -> "(not " ++ (expr_pretty_print expr1) ++ ")"
            MkIff expr1 expr2  -> "(iff " ++ (expr_pretty_print expr1) ++ " " ++ (expr_pretty_print expr2) ++ ")"
            MkImplies expr1 expr2 -> "(=> " ++ (expr_pretty_print expr1) ++ " " ++ (expr_pretty_print expr2) ++ ")" 
            MkAnd exprs -> "(and " ++ (list_expr_pretty_print exprs) ++ ")"
            MkOr  exprs -> "(or " ++ (list_expr_pretty_print exprs) ++ ")"
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
  if result then (do predicateSoltuions <- parens (parsePredicatesSoltuions)
                     (return (result,predicateSoltuions)))
  else (return (result,Map.empty))

parsePredicatesSoltuions :: Parser (Map.Map Function Expr)
parsePredicatesSoltuions = do
  reserved "fixedpoint"  
  result <- parseAllPredicatesSoltuions
  return result

parseAllPredicatesSoltuions :: Parser (Map.Map Function Expr)
parseAllPredicatesSoltuions = 
  do
    (x,y) <- parens (parseFunctionInvariant)
    oldMap <- parseAllPredicatesSoltuions
    let theMap = Map.insert x y oldMap
    return theMap
  <|>
    return Map.empty 

subExpr :: (Map.Map Var Var) -> Expr -> Expr
subExpr substitutionList originalExpr = case originalExpr of
   ExprVar theOldVar -> if (Map.member theOldVar substitutionList) then(ExprVar (substitutionList Map.! theOldVar))
                            else (ExprVar theOldVar)
   MkAdd list -> MkAdd (map (subExpr substitutionList) list)
   MkMul list -> MkMul (map (subExpr substitutionList) list)
   MkSub list -> MkSub (map (subExpr substitutionList) list)
   MkDiv_1 expr1 expr2 -> MkDiv_1 (subExpr substitutionList expr1) (subExpr substitutionList expr2)
   MkDiv_2 expr1 expr2 -> MkDiv_2 (subExpr substitutionList expr1) (subExpr substitutionList expr2)
   MkMod expr1 expr2 -> MkMod (subExpr substitutionList expr1) (subExpr substitutionList expr2)
   MkRem expr1 expr2 -> MkRem (subExpr substitutionList expr1) (subExpr substitutionList expr2)
   MkLt  expr1 expr2 -> MkLt (subExpr substitutionList expr1) (subExpr substitutionList expr2)
   MkLe expr1 expr2 -> MkLe (subExpr substitutionList expr1) (subExpr substitutionList expr2)
   MkGt expr1 expr2 -> MkGt (subExpr substitutionList expr1) (subExpr substitutionList expr2)
   MkGe expr1 expr2 -> MkGe (subExpr substitutionList expr1) (subExpr substitutionList expr2)
   MkEq expr1 expr2 -> MkEq (subExpr substitutionList expr1) (subExpr substitutionList expr2)
   MkNot expr1 -> MkNot (subExpr substitutionList expr1) 
   MkIff expr1 expr2 -> MkIff (subExpr substitutionList expr1) (subExpr substitutionList expr2)
   MkImplies expr1 expr2 -> MkImplies (subExpr substitutionList expr1) (subExpr substitutionList expr2)
   MkAnd list -> MkAnd (map (subExpr substitutionList) list)
   MkOr  list -> MkOr (map (subExpr substitutionList) list)
   _ -> originalExpr


parseFunctionInvariant :: Parser (Function,Expr)
parseFunctionInvariant = do
  function <- parseFunction
  expr <- parseExpr (ParseState Map.empty (getVariableSortMap function))
  return (function,expr)

getVariableSortMap :: Function -> (Map.Map String Sort)
getVariableSortMap (Function _ list) = getSortMap 0 list

getSortMap :: Int -> [Sort] -> (Map.Map String Sort)
getSortMap number list = case list of
 x:xs -> Map.insert ("x!"++show(number)) x (getSortMap (number+1) xs)
 [] -> Map.empty



lexer = T.makeTokenParser emptyDef
parens    = T.parens lexer
symbol     = T.symbol lexer
identifier = T.identifier lexer
reserved    = T.reserved lexer
