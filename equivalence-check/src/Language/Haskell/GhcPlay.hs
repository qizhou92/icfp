module Language.Haskell.GHC.GhcPlay (

    makeEqEnv

  ) where 

import DynamicLoading
import GHC
import GHC.Paths (libdir)
import HscTypes
import TidyPgm
import HscMain
import Var hiding (varName)
import DynFlags
import CoreSyn

import Data.Foldable (find)
import Control.Monad (liftM)
import Control.Monad.IO.Class (liftIO)
import System.IO.Temp

import Data.Maybe (catMaybes)

import qualified Data.Map.Strict as M 


import Language.Haskell.Types
import Language.Haskell.Misc


makeEqEnv :: Config -> IO EqEnv
makeEqEnv cfg = runGhc' (ghcEqCheck cfg)

runGhc' :: Ghc a -> IO a
runGhc' act =
  withSystemTempDirectory "tmp_check" $ \tmp ->
    runGhc (Just libdir) $ do
      flg <- getSessionDynFlags
      let flg' = configureDynFlags tmp flg 
      _ <- setSessionDynFlags flg'
      prettyPrintGhcErrors flg' act 

configureDynFlags :: FilePath -> DynFlags -> DynFlags
configureDynFlags tmp flg = flg { objectDir    = Just tmp
                                , hiDir        = Just tmp
                                , stubDir      = Just tmp} `gopt_set` Opt_KeepRawTokenStream


ghcEqCheck :: Config -> Ghc EqEnv
ghcEqCheck cfg = do 
   let fn = target cfg
   -- First, set the target to the desired filename
   target <- guessTarget fn Nothing
   _      <- setTargets [target]
   _      <- load LoadAllTargets
   modGraph <- depanal [] True
   case find ((== fn) . msHsFilePath) modGraph of
     Just modSummary -> do
       parsedMod <- parseModule modSummary
       mod_guts <- coreModule `fmap`
                      (desugarModule =<< typecheckModule parsedMod)
       mod <- liftM (gutsToCoreModule (mg_safe_haskell mod_guts)) $ do 
                 hsc_env <- getSession
                 simpl_guts <- liftIO $ hscSimplify hsc_env mod_guts
                 tidy_guts <- liftIO $ tidyProgram hsc_env simpl_guts
                 return $ Left tidy_guts 
       pairs <- makePairs (moduleName $ ms_mod modSummary) $ snd $ pm_annotations parsedMod
       let cbs = cm_binds mod
       liftIO $ putStrLn ("INITIAL CBS = " ++ showPpr cbs)
       return $ EqEnv cbs pairs  

     Nothing -> error "compileToCoreModule: target FilePath not found in module dependency graph"
  where -- two versions, based on whether we simplify (thus run tidyProgram,
        -- which returns a (CgGuts, ModDetails) pair, or not (in which case
        -- we just have a ModGuts.
        gutsToCoreModule :: SafeHaskellMode
                         -> Either (CgGuts, ModDetails) ModGuts
                         -> CoreModule
        gutsToCoreModule safe_mode (Left (cg, md)) = CoreModule {
          cm_module = cg_module cg,
          cm_types  = md_types md,
          cm_binds  = cg_binds cg,
          cm_safe   = safe_mode
        }
        gutsToCoreModule safe_mode (Right mg) = CoreModule {
          cm_module  = mg_module mg,
          cm_types   = typeEnvFromEntities (bindersOfBinds (mg_binds mg))
                                           (mg_tcs mg)
                                           (mg_fam_insts mg),
          cm_binds   = mg_binds mg,
          cm_safe    = safe_mode
         }

makePairs :: ModuleName -> M.Map SrcSpan [Located AnnotationComment] -> Ghc [(Var, Var)]
makePairs md ans0 = mapM (ghcLookupPair md) ans
  where 
   ans = catMaybes [getEquivalencePair x | AnnBlockComment x <- unLoc <$> concat (M.elems ans0)]
   ghcLookupPair md (x1, x2) = (,) <$> ghcLookup md x1 <*> ghcLookup md x2 

getEquivalencePair :: String -> Maybe (String, String)
getEquivalencePair = go . words 
  where
    go [_start, "checkEq", x1, x2, _end] = Just $ (x1, x2)
    go _ = Nothing  

ghcLookup :: ModuleName -> String -> Ghc Id 
ghcLookup md x = do 
   hsEnv  <- getSession
   name   <- liftIO $ hscParseIdentifier hsEnv x
   mname  <- liftIO $ lookupRdrNameInModuleForPlugins hsEnv md (unLoc name)
   things <- liftIO $ mapM (hscTcRcLookupName hsEnv) (case mname of Just x -> [x]; _ -> [])
   let ids = [x | Just (AnId x) <- things]
   case ids of 
     []    -> error ("Not found: " ++ x)
     (x:_) -> return x

