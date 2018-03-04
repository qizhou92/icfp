{-# LANGUAGE QuasiQuotes #-}
module Language.Grammar where

import Control.Monad.State

import           Language.Types
import           Language.Parser
import qualified Language.Solve as S

import           Text.Parsec
import           Data.Generics.Fixplate.Base
import           Data.Text.Prettyprint.Doc
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import           Grammar
import           Formula (runVocab)
import qualified Formula as F

parseE :: String -> CoreExpr
parseE s = case parse parseExpr "" s of
  Left e -> error (show e)
  Right ex -> ex

basicPlotE :: CoreExpr -> IO ()
basicPlotE ex =
  void $ S.solveCE (F.LBool True) (Seq.singleton ex)

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
qiTest = "(" ++ addFunction ++ ") (\\x1. \\y1. x1+y1) (\\x2. x2+1)3"

qiTest2 :: String
qiTest2 =
  let addF = "fix f . \\f1.\\f2.\\x.(f f1 (f1 x) (x-1))"
  in "(" ++ addF ++ ") (\\x1. \\y1. x1+y1) (\\x2. x2+1)"

davidTest :: String
davidTest =
  "(\\f.f 1)((\\x.\\y.x + y))"

something :: String
something =
  "(\\f.f 123 + f 519)(\\x.x + 46)"

davidTest2 :: String
davidTest2 =
  "(\\a.((\\f.f 1 + f 2)((\\x.\\y.x + y)a)))"

simpleFix :: String
simpleFix =
  "(\\x. fix f. \\y. f x y)3"

simpleRename :: String
simpleRename =
  "(\\y.(\\x. x+1)y + (\\x. x+2)y)0"

simple :: String
simple = "(\\x. x + 3)5"

simpleIf :: String
simpleIf = "(\\x. if (x < 5) 0 x)"
