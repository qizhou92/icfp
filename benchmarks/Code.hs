
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric     #-}

module Code where

import GHC.Generics
import Data.Maybe
import qualified Data.Text                  as T
import qualified Data.Text.IO               as T
import qualified Data.ByteString.Lazy       as LB
import qualified Data.ByteString.Lazy.Char8 as LBC
import Control.Monad
import Data.Aeson
import Data.Aeson.Parser
import System.FilePath

{- | To generate a bunch of benchmarks in the `tmp/` sub-directory, do:
      
      $ stack ghci 
      $ :l Code.hs 
      $ main 
 
     You can tweak the parameters in `main` to generate more benchmarks
     or for different problems by changing the `5` or the name of the 
     problem...

     * The `ref/` directory has the reference solutions, 
     * The files `tmp/problem.i.ml` contain candidate solutions taken from the `pairs.json`
 -} 

main = do
  mapM_ (writeSols "pairs.json" "tmp")
    [ Q 5 (\p -> problem p == "sumList"    )
    , Q 5 (\p -> problem p == "digitsOfInt")
    , Q 5 (\p -> problem p == "digits"     )
    , Q 5 (\p -> problem p == "listReverse")
    ]

-- 5 solutions for problem `sumList`
q_5_sumList = Q 5 (\p -> problem p == "sumList")
q_5_assoc   = Q 5 (\p -> problem p == "assoc")

writeSols :: FilePath    -- ^ .json file
          -> FilePath    -- ^ dest  directory
          -> Query       -- ^ which problems?
          -> IO ()
writeSols jsonFile dstDir q = readPairs jsonFile q >>= writePairs dstDir

--- >>> readPairs "pairs.json" q_5_sumList
readPairs  :: FilePath -> Query -> IO [Pair]
readPairs jsonFile (Q num cond) = do
  pairs <- getPairs jsonFile
  return $ take num (filter cond pairs)

writePairs :: FilePath -> [Pair] -> IO ()
writePairs dstDir pairs = forM_ pairs $ \p ->
  T.writeFile (dstDir </> pairFile p) (fix p)

pairFile :: Pair -> FilePath
pairFile p = T.unpack (problem p) ++ "." ++ show (index p) ++ ".ml"

data Query = Q
  { qNum  :: Int
  , qCond :: Pair -> Bool
  }

getPairsForProblem name pairs = filter (\p -> problem p == name) pairs

getPairs :: FilePath -> IO [Pair]
getPairs f = map decodePair . LBC.lines <$> LB.readFile f

decodePair :: LB.ByteString -> Pair
decodePair = fromJust . decode

-- decodeWith :: Parser Value -> (Value -> Result a) -> ByteString -> Maybe a

data Pair = Pair
  { hw      :: !T.Text
  , index   :: !Int
  , problem :: !T.Text
  , bad     :: !T.Text
  , fix     :: !T.Text
  } deriving (Show)


instance FromJSON Pair where
  parseJSON (Object v) = Pair <$> v .: "hw"
                              <*> v .: "index"
                              <*> v .: "problem"
                              <*> v .: "bad"
                              <*> v .: "fix"
