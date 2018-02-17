module Language.Grammar where

import Control.Monad.State

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
import           Data.Generics.Fixplate.Base
import qualified Data.Map as M

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

testIf = "(\\x.if (x < 3) true false)2"

testFix = "(fix f. \\x. if (x < 0) 0 (1 + (f (x-1))))"

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
      Left e -> print e
      Right g -> plot "tmp" g

pipelineSimp :: String -> IO ()
pipelineSimp e =
  case parse parseExpr "" e of
    Left e -> print e
    Right ex -> case exprGrammar ex of
      Left e -> print "error"
      Right g -> plot "simp" (runVocab (simplify g))


drawTypes :: String -> IO ()
drawTypes e =
  case parse parseExpr "" e of
    Left e -> print e
    Right ex -> case TI.typeCheck (uniqueNames ex) of
      Left e -> print "error"
      Right g -> drawTreeWith (\(Ann (_, t) _) -> show t) g

drawBasicCtxt :: String -> IO ()
drawBasicCtxt e =
  case parse parseExpr "" e of
    Left e -> print e
    Right ex -> case evalStateT (TI.contextualize $ uniqueNames ex) (TI.InferenceState 0 M.empty) of
      Left e -> print "error"
      Right g -> drawTreeWith (\(Ann t _) -> show t) g
