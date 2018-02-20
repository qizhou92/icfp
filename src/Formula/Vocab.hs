{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances #-}
module Formula.Vocab where

import           Control.Lens
import           Control.Monad.State

import           Data.Foldable
import           Data.Data (Data)
import qualified Data.Map as M
import           Data.Map (Map)
import           Data.List.Split

import           Formula.Var

class Monad m => MonadVocab m where
  fresh :: String -> m String
  fetch :: String -> m String

newtype VocabT m a = Vocab { getVocab :: StateT (Map String Int) m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadTrans)

instance MonadState s m => MonadState s (VocabT m) where
  state = lift . state

instance Monad m => MonadVocab (VocabT m) where
  fresh n = do
    Vocab (M.lookup n <$> get >>= \case
      Nothing -> modify (M.insert n 0)
      Just i  -> modify (M.insert n (i+1)))
    fetch n

  fetch n = Vocab (M.lookup n <$> get >>= \case
    Nothing -> pure n
    Just i -> pure (n ++ "#" ++ show i))

instance MonadVocab m => MonadVocab (StateT s m) where
  fresh = lift . fresh
  fetch = lift . fetch

type Vocab a = VocabT Identity a

runVocab :: Vocab a -> a
runVocab (Vocab a) = evalState a M.empty

runVocabT :: Monad m => VocabT m a -> m a
runVocabT (Vocab a) = evalStateT a M.empty

baseName :: String -> String
baseName = head . splitOn "#"
