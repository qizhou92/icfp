module Language.Grammar where

import qualified Language.TypeInference as TI
import           Language.HOTypeInference
import           Language.Types
import           Language.UniqueNames
import           Language.Parser

import           Text.Parsec
import           Text.ParserCombinators.Parsec.Char
import qualified Text.Parsec.Token as T
import           Text.Parsec.Language (emptyDef)

import Data.Text.Prettyprint.Doc

import           Grammar

-- | Given an expression, generate a grammar of type constraints which expresses
-- relationships between the types of subexpressions and the top level expression,
-- obeying the judgement rules of higher order refinement types.
exprGrammar :: CoreExpr -> Either InferenceError Grammar
exprGrammar e =
  case TI.typeCheck (uniqueNames e) of
    Left (TI.UnificationError t1 t2) -> Left (UnificationError t1 t2)
    Left (TI.UnboundError x) -> Left (UnboundError x)
    Right e' -> typeConstraints e'

test :: String
test = "(\\x.x+1)5"

pipeline :: String -> IO ()
pipeline e =
  case parse parseExpr "" e of
    Left e -> print e
    Right ex -> case exprGrammar ex of
      Left e -> print "fuck"
      Right g -> print (pretty g)
