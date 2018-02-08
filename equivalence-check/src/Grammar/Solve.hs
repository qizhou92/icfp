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

solve :: Clones Int -> Grammar Int -> Expr -> IO (Int, Either Model (Map Int (Expr, Expr)))
solve cs g f = loop 1 (cs, g)
  where
    loop iters (clones, g') = interpolate g' f >>= \case
      Left e -> pure (iters, Left e)
      Right m -> do
        ind <- inductive clones g' m
        if M.findWithDefault False (g ^. grammarStart) ind
        then onInductive iters g' clones m ind
        else loop (iters+1) $ unwind (M.keysSet $ M.filter not ind) (clones, g')

    onInductive iters g' clones m ind = do
      let indS = M.keysSet $ M.filter id ind
      let invs = synthesizeInvariants indS clones g' m
      m' <- traverse simpBoth invs
      pure (iters, Right m')

    simpBoth (x, y) = (,) <$> Z3.superSimplify x <*> Z3.superSimplify y

interpolate :: Grammar Int -> Expr -> IO (Either Model (Map Int Expr))
interpolate g' q =
  runSystem (F.Query [app terminal] (LBool True) q : map clause (g ^. grammarProductions))
  where
    g = nonrecursive g'
    terminal = view productionLHS (head $ productionsFor (g ^. grammarStart)
                                                         (g ^. grammarProductions)) & vars %~ unaliasedVar

inductive :: Clones Int -> Grammar Int -> Map Int Expr -> IO (Map Int Bool)
inductive clones g m = execStateT (ind (g ^. grammarStart)) M.empty
  where
    descs sym =
      let cs = cloneFor sym clones
          ds = descendants (nonrecursive g) sym
          cds = S.toList $ S.intersection cs ds
      in map (\cd -> M.findWithDefault (LBool True) cd m) cds

    ind :: Int -> StateT (Map Int Bool) IO Bool
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
      let ps = predecessors (g ^. grammarProductions) sym
          backTars = map lhsSymbol (backProductions g)
      in if | null ps -> pure True
            | sym `elem` backTars -> pure False
            | otherwise ->
              let cats = M.elems (categorize (g ^. grammarProductions))
                  cps = map (`predecessors` sym) cats
              in anyM (allM ind . S.toList) cps
