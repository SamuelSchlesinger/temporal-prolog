module Main where

import Control.Exception (IOException, try)
import System.Directory (makeAbsolute)
import System.Environment (getArgs)
import System.Exit (ExitCode(..), exitFailure, exitSuccess, exitWith)
import System.FilePath (isAbsolute, takeDirectory, (</>))
import System.IO (hPutStrLn, stderr)
import Text.Megaparsec (errorBundlePretty)
import Text.Read (readMaybe)

import TemporalProlog.ModelChecker
import TemporalProlog.Normalizer (normalize)
import TemporalProlog.Parser (parseProgram)
import TemporalProlog.Scenario

data Options = Options
  { optionScenario        :: Maybe FilePath
  , optionDot             :: Maybe FilePath
  , optionCounterexamples :: Int
  , optionIncludeInternal :: Bool
  , optionHelp            :: Bool
  }

defaultOptions :: Options
defaultOptions = Options Nothing Nothing 3 False False

main :: IO ()
main = do
  arguments <- getArgs
  case parseOptions defaultOptions arguments of
    Left err -> hPutStrLn stderr ("error: " ++ err) >> printHelp >> exitFailure
    Right options
      | optionHelp options -> printHelp >> exitSuccess
      | otherwise -> case optionScenario options of
          Nothing -> printHelp >> exitFailure
          Just scenarioFile -> run options scenarioFile

run :: Options -> FilePath -> IO ()
run options scenarioFile = do
  scenarioSource <- readText scenarioFile
  scenario <- case parseScenario scenarioFile scenarioSource of
    Left err -> die err
    Right value -> pure value
  absoluteScenario <- makeAbsolute scenarioFile
  let configuredProgram = scenarioProgram scenario
      programFile = if isAbsolute configuredProgram
        then configuredProgram
        else takeDirectory absoluteScenario </> configuredProgram
  programSource <- readText programFile
  program <- case parseProgram programFile programSource of
    Left err -> die (errorBundlePretty err)
    Right value -> pure value
  (normalProgram, pfNames) <- case normalize program of
    Left err -> die err
    Right ((value, names), warnings) -> do
      mapM_ (hPutStrLn stderr) warnings
      pure (value, names)
  result <- case runModelCheck scenario normalProgram pfNames of
    Left err -> die err
    Right value -> pure value
  putStr (renderCheckSummary (optionCounterexamples options)
    (optionIncludeInternal options) result)
  case optionDot options of
    Nothing -> pure ()
    Just path -> do
      writeResult <- try (writeFile path (renderCheckDot (optionIncludeInternal options) result))
        :: IO (Either IOException ())
      case writeResult of
        Left err -> die ("cannot write " ++ path ++ ": " ++ show err)
        Right () -> putStrLn ("dot=" ++ path)
  if checkPassed result then exitSuccess else exitWith (ExitFailure 2)

readText :: FilePath -> IO String
readText path = do
  result <- try (readFile path) :: IO (Either IOException String)
  either (die . (("cannot read " ++ path ++ ": ") ++) . show) pure result

die :: String -> IO a
die message = hPutStrLn stderr ("error: " ++ message) >> exitFailure

parseOptions :: Options -> [String] -> Either String Options
parseOptions options [] = Right options
parseOptions options ("--help" : rest) = parseOptions options { optionHelp = True } rest
parseOptions options ("-h" : rest) = parseOptions options { optionHelp = True } rest
parseOptions options ("--include-internal" : rest) =
  parseOptions options { optionIncludeInternal = True } rest
parseOptions options ("--dot" : path : rest) =
  parseOptions options { optionDot = Just path } rest
parseOptions _ ["--dot"] = Left "--dot requires a path"
parseOptions options ("--counterexamples" : value : rest) = case readMaybe value of
  Just count | count >= 0 -> parseOptions options { optionCounterexamples = count } rest
  _ -> Left "--counterexamples requires a non-negative integer"
parseOptions _ ["--counterexamples"] = Left "--counterexamples requires an integer"
parseOptions options (argument : rest)
  | take 1 argument == "-" = Left $ "unknown option " ++ show argument
  | otherwise = case optionScenario options of
      Nothing -> parseOptions options { optionScenario = Just argument } rest
      Just _ -> Left "only one scenario file may be supplied"

printHelp :: IO ()
printHelp = do
  putStrLn "Temporal Prolog bounded protocol model checker"
  putStrLn "usage: temporal-prolog-check SCENARIO [OPTIONS]"
  putStrLn ""
  putStrLn "  --dot PATH             write the explored tree as Graphviz DOT"
  putStrLn "  --counterexamples N    print at most N traces (default: 3)"
  putStrLn "  --include-internal     include normalizer-generated facts"
  putStrLn "  -h, --help             show this help"
