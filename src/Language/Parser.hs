module Language.Parser where

import           Data.Functor.Identity

import           Text.Parsec
import           Text.ParserCombinators.Parsec.Char
import qualified Text.Parsec.Token as T
import           Text.Parsec.Language (emptyDef)

import           Language.Types

lexeme :: Stream s m Char => ParsecT s u m b -> ParsecT s u m b
lexeme p = do { x <- p; spaces; return x  }

parseExpr :: CharParser st CoreExpr
parseExpr = lambda <|> ex1

ex1 :: CharParser st CoreExpr
ex1 = ex2

ex2 :: CharParser st CoreExpr
ex2 = ex3 `chainl1` (op "||" >> return (ebin Or))

ex3 :: CharParser st CoreExpr
ex3 = ex4 `chainl1` (op "&&" >> return (ebin And))

ex4 :: CharParser st CoreExpr
ex4 = ex6 `chainl1` compareop

ex6 :: CharParser st CoreExpr
ex6 = ex7 `chainl1` addop

ex7 :: CharParser st CoreExpr
ex7 = exInf `chainl1` mulop

exInf :: CharParser st CoreExpr
exInf = atom

atom :: CharParser st CoreExpr
atom = try app <|> nonapp
  where
    nonapp = parens parseExpr <|> (evar <$> try var) <|> bool <|> (eint <$> integer)
    app = (res "if" >> eif <$> nonapp <*> nonapp <*> nonapp)
      <|> (do v <- nonapp
              args <- many1 nonapp
              pure (foldl eapp v args))

lambda :: CharParser st CoreExpr
lambda = do
  op "\\"
  v <- var
  char '.'
  T.whiteSpace lexer
  e <- parseExpr
  pure (elam v e)

bool :: CharParser st CoreExpr
bool = const (ebool True)  <$> res "true"
   <|> const (ebool False) <$> res "false"

var :: CharParser st Var
var = Var <$> ident

compareop, mulop, addop :: CharParser st (CoreExpr -> CoreExpr -> CoreExpr)

compareop = (op "<="  >> pure (ebin Le))
        <|> (op "<"   >> pure (ebin Lt))
        <|> (op "!="  >> pure (ebin Ne))
        <|> (op "="   >> pure (ebin Eq))

mulop = (op "*" >> pure (ebin Mul))
    <|> (op "/" >> pure (ebin Div))

addop = (op "+" >> pure (ebin Plus))
    <|> (op "-" >> pure (ebin Minus))

integer :: (Read i, Integral i) => CharParser st i
integer = lexeme $ do { ds <- many1 digit ; return (read ds) }

lexer :: T.GenTokenParser String u Identity
lexer = T.makeTokenParser (emptyDef { T.identStart = letter <|> char '_'
                                    , T.identLetter = alphaNum
                                    <|> char '_' <|> char '/' <|> char '$' <|> char '#' <|> char '/' <|> char '{' <|> char '}'
                                    , T.reservedOpNames = [ "->" , "<-" , "<->" , "=>"
                                                          , "||"
                                                          , "&&"
                                                          , "=" , "<" , "<=" , ">" , ">="
                                                          , "+" , "-"
                                                          , "*" , "/", "%"
                                                          , "(", ")"
                                                          , ":"
                                                          , ";"
                                                          , "~"
                                                          , "\\", "."
                                                          ]
                                    , T.reservedNames = [ "not", "distinct"
                                                        , "and", "or"
                                                        , "add", "mul"
                                                        , "def"
                                                        , "true", "false"
                                                        , "call"
                                                        , "anything"
                                                        , "cond"
                                                        , "return"
                                                        , "assert"
                                                        , "Int", "Bool", "Real", "Arr"
                                                        , "jump"
                                                        , "done"
                                                        , "skip"
                                                        ]
                                    })

res :: String -> CharParser st ()
res = T.reserved lexer

ident :: CharParser st String
ident = T.identifier lexer

op :: String -> CharParser st ()
op = T.reservedOp lexer

symbol :: String -> CharParser st String
symbol = T.symbol lexer

commaSep :: CharParser st a -> CharParser st [a]
commaSep = T.commaSep lexer

parens :: CharParser st a -> CharParser st a
parens = T.parens lexer

braces :: CharParser st a -> CharParser st a
braces = T.braces lexer
