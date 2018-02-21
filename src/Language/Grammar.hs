{-# LANGUAGE QuasiQuotes #-}
module Language.Grammar where

import Control.Monad.State

import qualified Language.TypeInference as TI
import           Language.HOTypeInference
import           Language.Types
import           Language.Parser

import           Text.Parsec
import           Data.Generics.Fixplate.Draw
import           Data.Generics.Fixplate.Base
import qualified Data.Map as M
import           Data.Text.Prettyprint.Doc
import           Data.Generics.Fixplate.Attributes

import           Grammar
import           Formula (runVocab)
import qualified Formula as F

-- | Given an expression, generate a grammar of type constraints which expresses
-- relationships between the types of subexpressions and the top level expression,
-- obeying the judgement rules of higher order refinement types.
exprGrammar :: F.MonadVocab m => CoreExpr -> m (Either InferenceError Grammar)
exprGrammar e = do
  g <- uniqueNames e
  pure $ case TI.typeCheck g of
    Left (TI.UnificationError t1 t2) -> Left (UnificationError t1 t2)
    Left (TI.UnboundError x) -> Left (UnboundError x)
    Right e' -> typeConstraints e'

test :: String
test = "(\\f.\\x.f x)(\\y.y+1)3"

testIf :: String
testIf = "(\\x.if (x < 3) true false)2"

testFix :: String
testFix = "(fix f. \\x. if (x < 0) 0 (1 + (f (x-1))))"

parseE :: String -> CoreExpr
parseE s = case parse parseExpr "" s of
  Left e -> error (show e)
  Right ex -> ex

parseG :: F.MonadVocab m => String -> m Grammar
parseG s = exprGrammar (parseE s) >>= \case
  Left e -> error (show e)
  Right g -> pure g

pipeline :: String -> IO ()
pipeline e = plot "tmp" (runVocab $ parseG e)

pipelineSimp :: String -> IO ()
pipelineSimp e = plot "simp" (simplify (runVocab $ parseG e))

drawTypes :: String -> IO ()
drawTypes s =
  let ex = parseE s
  in case TI.typeCheck (runVocab $ uniqueNames ex) of
    Left e -> print e
    Right g -> drawTreeWith (\(Ann (_, t) _) -> show t) g

drawBasicCtxt :: String -> IO ()
drawBasicCtxt s =
  let ex = parseE s
  in case evalStateT (TI.contextualize $ runVocab $ uniqueNames ex)
    (TI.InferenceState 0 M.empty) of
      Left e -> print e
      Right g -> drawTreeWith (\(Ann t _) -> show t) g

solvePair :: F.Expr -> String -> String -> IO ()
solvePair q s1 s2 =
  F.runVocabT $ do
    g1 <- simplify <$> parseG s1
    g2 <- simplify <$> parseG s2
    let g = simplify (Grammar.product g1 g2)
    -- let g = Grammar.product g1 g2
    liftIO $ print (_grammarStart g1)
    plot "g1" g1
    liftIO $ print (_grammarStart g)
    plot "tmp" g
    plot "unwound" =<< (snd <$> (unwindAll =<< unwindAll =<< unwindAll (mempty, g1)))
    solve mempty g q >>= \case
      Left e -> liftIO $ print e
      Right m ->
        liftIO $ mapM_ (print . pretty) (M.toList m)

basicPlot :: String -> IO ()
basicPlot s = do
  let g = runVocab $ parseG s
  let gs = simplify g
  plot "basic" g
  plot "simplified" gs

-- testSum = "fix sum. \\n. if (n < 0)" ++
--                            "(n + sum (n + 1))" ++
--                            "(if (n = 0)" ++
--                                "0" ++
--                                "(n + sum (n - 1)))"
testSum = "fix sum. \\n. if (n = 0)" ++
                           "0" ++
                           "(n + sum (n - 1))"

testSumF =
  [F.expr|n > 0 && l/arg1/0 = n && r/arg1/0 = n - 1 -> l/out/0 = r/out/0 + n|]

-- Fix addFunction = \f1 \f2 \x \y if x<=0 (f2 x) else (addFunction f1 (f1 x) (x-1)(y+1) ) (edited)
addFunction = "fix f . \\f1 . \\f2 . \\x . \\y . " ++
                "if (x <= 0) (f2 x) (f f1 (f1 x) (x-1) (y+1))"

qiTest = "(" ++ addFunction ++ ") (\\x1. \\y1. x1+y1) (\\x2. x2+1)"

qiTest2 =
  let addF = "fix f . \\f1.\\f2.\\x.(f f1 (f1 x) (x-1))"
  in "(" ++ addF ++ ") (\\x1. \\y1. x1+y1) (\\x2. x2+1)"

unwindTest =
  forget $ unwindFix $ synthetise (const ()) $ parseE qiTest2


mytest f1 f2 x y =
  if (x :: Int) <= 0
  then f2 x
  else mytest f1 (f1 x) (x - 1) (y + 1 :: Int)

-- addFunction (\x1 \y1 x1+y1) (\x2 x2+1)

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

