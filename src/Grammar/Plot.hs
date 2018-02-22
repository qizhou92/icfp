{-# LANGUAGE OverloadedStrings #-}
module Grammar.Plot where

import           Control.Lens
import           Control.Monad.State

import           Data.Data.Lens
import           Data.Monoid ((<>))
import           Data.List (intercalate, nub)
import           Data.Text.Prettyprint.Doc hiding ((<>), dot)

import qualified Turtle
import           System.Info

import           Formula hiding (Rule, symbol, annot)
import           Grammar.Grammar

plot :: MonadIO m => FilePath -> Grammar -> m ()
plot fn g = do
  let txt = dot g
      cmdopen = case System.Info.os of
        "mingw32" -> "start"
        "linux"   -> "xdg-open"
        _         -> "open"
  liftIO $ writeFile (fn ++ ".dot") txt
  let fn' = Turtle.fromString (fn ++ ".dot")
  _ <- Turtle.shell ("dot -Tpdf " <> fn' <> "> " <> fn' <> ".pdf") Turtle.empty
  _ <- Turtle.shell (cmdopen <> " " <> fn' <> ".pdf") Turtle.empty
  return ()

dot :: Grammar -> String
dot g =
  let vs = map symbol $ nub $ toListOf template g
      es = concatMap rule (g ^. grammarRules)
      globalAtts = [ "node[fontsize=6];"
                   , "edge[fontsize=6, arrowsize=0.6];"]
  in "digraph {\n" ++ unlines (map ("  " ++) (globalAtts ++ vs ++ es)) ++ "}"
  where
    symbol nt =
      let vs = view nonterminalVars nt
          vs' = unwords (map (view varName) vs)
          lbl = case view nonterminalID nt of
            ConcreteID i -> "\"" ++ show i ++ "\n" ++ vs' ++ "\""
            PhantomID i j toRename -> "\"" ++ show i ++ ":" ++ show j ++ "\n" ++
                                   unwords toRename ++ "\n" ++ vs' ++ "\", " ++
                                     "style=dashed"
      in show (nonterminalPrimary nt) ++ " [label=" ++ lbl ++ "];"
    rule (Rule ct lhs f rhs) =
      let annot = " [label=\"" ++ show ct ++ ": " ++ show (pretty f) ++ "\"];"
          inc = map (view nonterminalID) rhs
          tar = lhs ^. nonterminalID
      in case inc of
        [i] -> [sym i ++ " -> " ++ sym tar ++ annot]
        _ ->
          let mid = "m" ++ intercalate "_" (map sym (inc ++ [tar])) in
          [ mid ++ " [shape=point, width=0.00001, height=0.00001];" ]
          ++ map (\i -> sym i ++ " -> " ++ mid ++ " [dir=none];") inc
          ++ [ mid ++ " -> " ++ sym tar ++ annot ]
    sym = show . primaryID
