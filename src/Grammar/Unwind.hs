module Grammar.Unwind where

import           Control.Lens
import           Control.Monad.State

import           Data.Data.Lens
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.List (partition)
import           Data.List.Split
import           Data.Foldable (foldrM, traverse_)

import           Grammar.Grammar
import           Formula

unwindAll :: MonadVocab m => (Clones, Grammar) -> m (Clones, Grammar)
unwindAll (cs, g) = unwind (allSymbols g) (cs, g)

toUnwind :: Set Symbol -> Grammar -> [(Symbol, Symbol, Set String)]
toUnwind valid =
  M.elems . foldMap (\(s, tar, vs) ->
    if tar `elem` valid
    then M.singleton tar (s, tar, vs)
    else M.empty) . phantoms

unwind :: MonadVocab m => Set Symbol -> (Clones, Grammar) -> m (Clones, Grammar)
unwind valid (cs, g) = foldrM unwindOnPhantom (cs, g) (toUnwind valid g)

unwindOnPhantom :: MonadVocab m
                => (Symbol, Symbol, Set String) -> (Clones, Grammar) -> m (Clones, Grammar)
unwindOnPhantom (s, tar, vs) (cs, g) = do
    traverse_ fresh vs
    toPaste'' <- toPaste' & vars %~ renameSpecial
                          & vars %%~ renameBound
    let g' = g & grammarRules <>~ toPaste''
               & grammarRules . biplate %~ (\ntid ->
          if primaryID ntid == s then ConcreteID s else ntid)

    let cs' = foldr (uncurry clone) cs (M.toList symMap)
    pure (cs', g')
  where
    toPaste = reaches tar (g ^. grammarRules)
    maxSym = maximum (g ^.. biplate) :: Symbol
    pasteSyms = toPaste ^.. biplate :: [Symbol]
    symMap = M.insert tar s $ M.fromList (zip pasteSyms [maxSym+1..])
    toPaste' = toPaste & biplate %~ (\s -> M.findWithDefault s s symMap)
    renameBound v = if baseName (view varName v) `elem` vs
                    then v & varName %%~ (fetch . baseName)
                    else pure v

    renameSpecial v = case splitOn "/" (view varName v) of
      [vn] -> v
      [vn, s] -> let s' = M.findWithDefault (read s) (read s) symMap
                 in v & varName .~ (vn ++ "/" ++ show s')
      _ -> error "bad variable name in renameSpecial"

reaches :: Symbol -> [Rule] -> [Rule]
reaches start rs = evalState (reach start) S.empty
  where
    reach = visit [] (\sym ->
      let rs' = rulesFor sym rs
          ps = S.toList $ predecessors rs' sym
      in fmap (rs' ++) (concat <$> mapM reach ps))
