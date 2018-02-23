{-# LANGUAGE QuasiQuotes #-}
module Language.Grammar where

import Control.Monad.State

import           Language.Types
import           Language.Parser
import qualified Language.Solve as S

import           Text.Parsec
import           Data.Generics.Fixplate.Base
import           Data.Text.Prettyprint.Doc

import           Grammar
import           Formula (runVocab)
import qualified Formula as F

parseE :: String -> CoreExpr
parseE s = case parse parseExpr "" s of
  Left e -> error (show e)
  Right ex -> ex

basicPlotE :: CoreExpr -> IO ()
basicPlotE ex = do
  let ex' = runVocab $ uniqueNames (evalState (numberExpressions ex) 0)
  print (pretty (forget ex'))
  (cs, g) <- S.exprGrammar ex'
  print cs
  let gs = simplify g
  plot "basic" g
  plot "simplified" gs

testSum :: String
testSum = "fix sum. \\n. if (n = 0)" ++
                           "0" ++
                           "(n + sum (n - 1))"

testSumF :: F.Expr
testSumF =
  [F.expr|n > 0 && l/arg1/0 = n && r/arg1/0 = n - 1 -> l/out/0 = r/out/0 + n|]

addFunction :: String
addFunction = "fix f . \\f1 . \\f2 . \\x . " ++
                "if (x <= 0) (f2 x) (f f1 (f1 x) (x-1))"

qiTest :: String
qiTest = "(" ++ addFunction ++ ") (\\x1. \\y1. x1+y1) (\\x2. x2+1)"

qiTest2 :: String
qiTest2 =
  let addF = "fix f . \\f1.\\f2.\\x.(f f1 (f1 x) (x-1))"
  in "(" ++ addF ++ ") (\\x1. \\y1. x1+y1) (\\x2. x2+1)"

simple :: String
simple = "(\\x.x+x)2"

notSoSimple :: String
notSoSimple = "(\\f.f 1)(\\x.x+2)"

doubleCall :: String
doubleCall = "(\\f.(f 1) + (f 2))(\\x.x+3)"

doubleCall2 :: String
doubleCall2 = "(\\f.f (f 1))(\\x.x+2)"
