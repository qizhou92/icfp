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
import           Data.Generics.Fixplate.Draw

import Data.Text.Prettyprint.Doc

import           Grammar
import           Formula (runVocab)

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
test = "(\\f.\\x.f x)(\\y.y+1)3"

project :: String -> IO ()
project e =
  case parse parseExpr "" e of
    Left e -> print e
    Right ex -> print (pretty ex)


pipeline :: String -> IO ()
pipeline e =
  case parse parseExpr "" e of
    Left e -> print e
    Right ex -> case exprGrammar ex of
      Left e -> print "error"
      Right g -> print (pretty g)

pipelineSimp :: String -> IO ()
pipelineSimp e =
  case parse parseExpr "" e of
    Left e -> print e
    Right ex -> case exprGrammar ex of
      Left e -> print "error"
      Right g -> print (pretty (runVocab (simplify g)))


drawTypes :: String -> IO ()
drawTypes e =
  case parse parseExpr "" e of
    Left e -> print e
    Right ex -> case addFreeVars <$> TI.typeCheck (uniqueNames ex) of
      Left e -> print "error"
      Right g -> drawTreeWith prettyCtxt g
