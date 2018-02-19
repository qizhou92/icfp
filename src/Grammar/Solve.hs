module Grammar.Solve where

import           Control.Lens
import           Control.Monad.Extra (allM, anyM)
import           Control.Monad.State

import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S

import           Formula hiding (Rule)
import qualified Formula as F
import qualified Formula.Z3 as Z3

import           Grammar.Grammar
import           Grammar.Dominator
import           Grammar.Unwind
import           Grammar.Synthesize
import           Grammar.Chc

solve :: Clones -> Grammar -> Expr -> IO (Either Model (Map Symbol (Expr, Expr)))
solve cs g f = loop (cs, g)
  where
    loop (clones, g') = interpolate g' f >>= \case
      Left e -> pure (Left e)
      Right m -> do
        ind <- inductive clones g' m
        if M.findWithDefault False (g ^. grammarStart) ind
        then onInductive g' clones m ind
        else loop $ unwind (M.keysSet $ M.filter not ind) (clones, g')

    onInductive g' clones m ind = do
      let indS = M.keysSet $ M.filter id ind
      let invs = synthesizeInvariants indS clones g' m
      m <- traverse simpBoth invs
      pure (Right m)

    simpBoth (x, y) = (,) <$> Z3.superSimplify x <*> Z3.superSimplify y

interpolate :: Grammar -> Expr -> IO (Either Model (Map Symbol Expr))
interpolate g' q =
  runSystem (F.Query [app terminal] (LBool True) q : map clause (g ^. grammarRules))
  where
    g = nonrecursive g'
    terminal = view ruleLHS (head $ rulesFor (g ^. grammarStart)
                                             (g ^. grammarRules))

inductive :: Clones -> Grammar -> Map Symbol Expr -> IO (Map Symbol Bool)
inductive clones g m = execStateT (ind (g ^. grammarStart)) M.empty
  where
    descs sym =
      let cs = cloneFor sym clones
          ds = descendants (nonrecursive g) sym
          cds = S.toList $ S.intersection cs ds
      in map (\cd -> M.findWithDefault (LBool True) cd m) cds

    ind :: Symbol -> StateT (Map Symbol Bool) IO Bool
    ind sym = do
      memo <- get
      case M.lookup sym memo of
        Just b -> pure b
        Nothing ->
          (at sym <?=) =<<
          let f = M.findWithDefault (LBool False) sym m
          in or <$> sequence
              [ pure $ f == LBool True
              , manyAnd (descs sym) `Z3.entails` f
              , indByPred sym
              ]

    indByPred sym =
      let ps = predecessors (g ^. grammarRules) sym
          backTars = map lhsSymbol (backRules g)
      in if | null ps -> pure True
            | sym `elem` backTars -> pure False
            | otherwise ->
              let cats = M.elems (categorize (g ^. grammarRules))
                  cps = map (`predecessors` sym) cats
              in anyM (allM ind . S.toList) cps
