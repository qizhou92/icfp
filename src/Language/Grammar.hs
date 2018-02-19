{-# LANGUAGE QuasiQuotes #-}
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
import           Data.Map (Map)
import qualified Data.Map as M

import Data.Text.Prettyprint.Doc

import           Grammar
import           Formula (runVocab)
import qualified Formula as F

-- | Given an expression, generate a grammar of type constraints which expresses
-- relationships between the types of subexpressions and the top level expression,
-- obeying the judgement rules of higher order refinement types.
exprGrammar :: CoreExpr -> Either InferenceError Grammar
exprGrammar e =
  case TI.typeCheck (runVocab $ uniqueNames e) of
    Left (TI.UnificationError t1 t2) -> Left (UnificationError t1 t2)
    Left (TI.UnboundError x) -> Left (UnboundError x)
    Right e' -> typeConstraints e'

test :: String
test = "(\\f.\\x.f x)(\\y.y+1)3"

testIf = "(\\x.if (x < 3) true false)2"

testFix = "(fix f. \\x. if (x < 0) 0 (1 + (f (x-1))))"

parseE :: String -> CoreExpr
parseE e = case parse parseExpr "" e of
  Left e -> error (show e)
  Right ex -> ex

parseG :: String -> Grammar
parseG e = case exprGrammar (parseE e) of
  Left e -> error (show e)
  Right g -> g

pipeline :: String -> IO ()
pipeline e = plot "tmp" (parseG e)

pipelineSimp :: String -> IO ()
pipelineSimp e =
  case parse parseExpr "" e of
    Left e -> print e
    Right ex -> case exprGrammar ex of
      Left e -> print e
      Right g -> plot "simp" (runVocab (simplify g))


drawTypes :: String -> IO ()
drawTypes e =
  case parse parseExpr "" e of
    Left e -> print e
    Right ex -> case TI.typeCheck (runVocab $ uniqueNames ex) of
      Left e -> print e
      Right g -> drawTreeWith (\(Ann (_, t) _) -> show t) g

drawBasicCtxt :: String -> IO ()
drawBasicCtxt e =
  case parse parseExpr "" e of
    Left e -> print e
    Right ex -> case evalStateT (TI.contextualize $ runVocab $ uniqueNames ex) (TI.InferenceState 0 M.empty) of
      Left e -> print "error"
      Right g -> drawTreeWith (\(Ann t _) -> show t) g

solvePair :: F.Expr -> String -> String -> IO ()
solvePair q s1 s2 =
  let g1 = runVocab (simplify (parseG s1))
      g2 = runVocab (simplify (parseG s2))
  -- let g1 = parseG s1
  --     g2 = parseG s2
  in do
    let g = Grammar.product g1 g2
    print (_grammarStart g1)
    plot "g1" g1
    print (_grammarStart g)
    plot "tmp" g
    plot "nonrec" (nonrecursive g)
    solve mempty g q >>= \case
      Left e -> print e
      Right m ->
        mapM_ (print . pretty) (M.toList m)

-- testSum = "fix sum. \\n. if (n < 0)" ++
--                            "(n + sum (n + 1))" ++
--                            "(if (n = 0)" ++
--                                "0" ++
--                                "(n + sum (n - 1)))"
testSum = "fix sum. \\n. if (n = 0)" ++
                           "0" ++
                           "(n + sum (n - 1))"

testSumF =
  [F.expr|n > 0 && l/arg1_0 = n && r/arg1_0 = n - 1 -> l/out_0 = r/out_0 + n|]

-- let rec sum n =
--     if n < 0 then n + sum (n + 1)
--       else if n = 0 then 0
--         else n + sum (n - 1)

-- let main n =
--     if n > 0 then
--         let s1 = sum n in
--                 let s2 = sum (n - 1) in
--                         assert(s1 = n + s2)
--                           else ()

