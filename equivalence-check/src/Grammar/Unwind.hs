module Grammar.Unwind where

import           Control.Lens
import           Control.Monad.State

import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.List (partition)

import           Grammar.Grammar
import           Grammar.Dominator

unwindAll :: (Clones Int, Grammar Int) -> (Clones Int, Grammar Int)
unwindAll (cs, g) = unwind (symbols g) (cs, g)

-- | Find the first recursive invocation in the grammar along each branch and unwind it.
-- That is, follow the productions until a nonterminal symbol appears which has already been
-- seen. Create new copies of all the productions succeeding this one with new symbols.
-- unwind :: (Clones sym, Grammar sym) -> (Clones sym, Grammar sym)
-- unwind (clones, g) = let (clones', old, new) = unwind' clones g in (clones', g & grammarProductions .~ (old ++ new))
unwind :: Set Int -> (Clones Int, Grammar Int) -> (Clones Int, Grammar Int)
unwind valid (clones, Grammar start rs) =
  let initial = (clones, maximum (symbols rs)+1)
      (rs', (clones', _)) = runState (evalStateT (unw [] start) S.empty) initial
  in (clones', Grammar start rs')
  where
    unw seen = visit [] (\sym ->
      let seen' = sym : seen
          (back, for) = partition (any (`elem` seen') . rhsSymbols) (productionsFor sym rs)
          otherBack = if null back then [] else tail back
          ps = S.toList $ predecessors (for ++ otherBack) sym
      in
      if null back || sym `notElem` valid
      -- If no productions to the symbol are backwards or the symbol is not allowed to
      -- be unwound, recurse.
      then fmap ((back ++ for) ++) (concat <$> mapM (unw seen') ps)
      -- Otherwise, unwind the first backwards production and preserve all other productions
      -- to the symbol.
      else do newRs <- lift (cloneFrom (head back))
              let ps' = filter (`notElem` rhsSymbols (head back)) ps
              rs' <- concat <$> mapM (unw seen') ps'
              pure (tail back ++ for ++ newRs ++ rs'))

    -- Clone all productions which reach the production symbol by creating fresh symbols and
    -- substituting them in. Mark these fresh symbols as clones. In addition, add
    -- a production which connects the cloned portion to the production symbol.
    cloneFrom r = do
      let reaching = reaches (lhsSymbol r) rs
      let syms = S.toList $ symbols reaching :: [Int]
      s <- use _2
      _2 += length syms
      let m = M.fromList (zip syms [s..])
      let sub sym = M.findWithDefault sym sym m
      let reaching' = reaching & allSymbols %~ sub
      let r' = r & productionRHS . allSymbols %~ sub
      mapM_ (\(i, j) -> _1 %= clone i j) (M.toList m)
      pure (r' : reaching')

unwind2 :: Set Int -> (Clones Int, Grammar Int) -> (Clones Int, Grammar Int)
unwind2 valid (clones, g@(Grammar start rs)) =
  let initial = (clones, rs, maximum (symbols rs))
      (clones', rs', _) = execState (evalStateT (unw start) S.empty) initial
  in (clones', Grammar start rs')
  where
    backs = backProductions g
    unw = visit () (\sym -> do
      when (sym `elem` valid) $ do
        rs' <- lift (use _2)
        let backsTo = filter (`elem` backs) (productionsFor sym rs')
        lift (mapM_ (doUnw sym) backsTo)
      mapM_ unw (predecessors rs sym))

    doUnw sym r = do
      rs' <- use _2
      newSym <- _3 <+= 1
      let rel = filter (elem sym . symbols) rs'
      let replace s = if s == sym then newSym else s
      let rs'' = (r & productionRHS . allSymbols %~ replace) : (rel & allSymbols %~ replace)
            ++ filter (/= r) rs'
      _2 .= rs''
      _1 %= clone sym newSym

reaches :: Int -> [Production Int] -> [Production Int]
reaches start rs = evalState (reach start) S.empty
  where
    reach = visit [] (\sym ->
      let rs' = productionsFor sym rs
          ps = S.toList $ predecessors rs' sym
      in fmap (rs' ++) (concat <$> mapM reach ps))
