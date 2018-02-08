module Main where

import Language

import System.Environment
import System.Exit
import Data.Maybe (mapMaybe)
import Data.List  (isPrefixOf)

parseProg :: String -> Program
parseProg = undefined

-- main :: IO ExitCode
-- main = equivalenceCheck =<< makeConfig =<< getArgs

main :: IO ()
main = putStrLn "Not Equivalent -- temporary"

-- equivalenceCheck :: Config -> IO ExitCode
-- equivalenceCheck cfg = do
--   prog <- makeProgram cfg
--   putStrLn ("************** Program ************** \n" ++ show prog)
--   putStrLn ("************** Types ************** \n"   ++ show (types prog))
--   -- res   <- mapM (uncurry verify) (goalsToPrograms (eqProgram eqEnv) <$> eqGoals eqEnv)
--   -- putStrLn (unlines (show <$> res))
--   exitWith ExitSuccess

-- makeProgram :: Config -> IO Program
-- makeProgram cfg = parseProg <$> readFile (cfgFile cfg)

-- _makeEqEnv :: Config -> IO EqEnv
-- _makeEqEnv cfg = do
--   str  <- readFile (cfgFile cfg)
--   return $ EqEnv (parseProg str) (queries str ++ cfgQueries cfg)

queries :: String -> [(Var, Var)]
queries = mapMaybe stringQuery . lines

stringQuery :: String -> Maybe (Var, Var)
stringQuery l
  | isPrefixOf "--" l   = case words (drop 2 l) of
                            ["@checkEq", v1, v2] -> Just (Var v1, Var v2)
                            _                    -> Nothing
  | otherwise           = Nothing
