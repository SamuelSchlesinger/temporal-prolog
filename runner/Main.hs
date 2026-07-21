module Main where

import Control.Exception (IOException, try)
import qualified Data.Map.Strict as Map
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Text.Megaparsec (errorBundlePretty)
import Text.Read (readMaybe)

import TemporalProlog.Batch
import TemporalProlog.Normalizer
import TemporalProlog.Parser
import TemporalProlog.Syntax

data Command = Help | Run FilePath BatchOptions

main :: IO ()
main = do
  parsed <- parseCommandLine <$> getArgs
  case parsed of
    Left err -> die err
    Right Help -> printHelp
    Right (Run path options) -> runFile path options

runFile :: FilePath -> BatchOptions -> IO ()
runFile path options = do
  sourceResult <- try (readFile path) :: IO (Either IOException String)
  case sourceResult of
    Left err -> die $ "cannot read " ++ path ++ ": " ++ show err
    Right source -> case parseProgram path source of
      Left err -> die (errorBundlePretty err)
      Right parsed -> case normalizeDetailed parsed of
        Left err -> die err
        Right normalized -> do
          mapM_ (hPutStrLn stderr) (normalizationWarnings normalized)
          case runBatchWithAuxiliaries options
              (normalizedProgram normalized)
              (normalizedPatternFunctions normalized)
              (normalizedAuxiliaryPredicates normalized) of
            Left err -> die err
            Right result -> putStr (renderBatch result)

parseCommandLine :: [String] -> Either String Command
parseCommandLine [] = Right Help
parseCommandLine ["--help"] = Right Help
parseCommandLine ["-h"] = Right Help
parseCommandLine (path:arguments) =
  Run path <$> go defaultOptions arguments
  where
    defaultOptions = BatchOptions
      { batchSteps = 1
      , batchAssertions = Map.empty
      , batchIncludeInternal = False
      }

    go options [] = Right options
    go options ("--steps":value:rest) = do
      steps <- maybe (Left "invalid --steps value") Right
        (readMaybe value :: Maybe Int)
      go options { batchSteps = steps } rest
    go _ ("--steps":[]) = Left "--steps requires an integer"
    go options ("--assert":value:rest) = do
      (step, atom) <- parseAssertion value
      go options
        { batchAssertions = Map.insertWith (flip (++)) step [atom]
            (batchAssertions options)
        } rest
    go _ ("--assert":[]) = Left "--assert requires STEP:ATOM"
    go options ("--include-internal":rest) =
      go options { batchIncludeInternal = True } rest
    go _ (unknown:_) = Left $ "unknown option " ++ show unknown

parseAssertion :: String -> Either String (Int, Atom)
parseAssertion value = case break (== ':') value of
  (stepText, ':' : atomText) | not (null stepText) && not (null atomText) -> do
    step <- maybe (Left "invalid assertion step") Right
      (readMaybe stepText :: Maybe Int)
    atom <- case parseAtom "<command line>" atomText of
      Left err -> Left (errorBundlePretty err)
      Right parsed -> Right parsed
    Right (step, atom)
  _ -> Left "assertion must be STEP:ATOM"

printHelp :: IO ()
printHelp = do
  putStrLn "Temporal Prolog batch runner"
  putStrLn "usage: temporal-prolog-run PROGRAM [--steps N] [--assert STEP:ATOM]..."
  putStrLn "                           [--include-internal]"
  putStrLn "all minimal branches and their complete world histories are printed"

die :: String -> IO a
die err = do
  hPutStrLn stderr ("error: " ++ err)
  exitFailure
