module Main where

import Control.Exception (try, IOException)
import Control.Monad.IO.Class (liftIO)
import Control.Monad (when)
import Data.Char (isDigit)
import Data.Maybe (isJust)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.IO (hPutStrLn, stderr)
import System.Console.Haskeline
import Text.Megaparsec (errorBundlePretty)
import Text.Read (readMaybe)

import TemporalProlog.Syntax
import TemporalProlog.Parser
import TemporalProlog.PrettyPrint
import TemporalProlog.Normalizer
import TemporalProlog.Interpreter as Interp

data REPLState = REPLState
  { rsInterp   :: InterpreterState
  , rsProgram  :: Program
  , rsNormProg :: NormalProgram
  , rsPFNames  :: Set.Set String
  }

main :: IO ()
main = do
  putStrLn "Temporal Prolog — based on Sakuragawa 1986"
  putStrLn "Type :help for available commands."
  let emptyProg = Program [] []
      initState = REPLState
        { rsInterp   = newInterpreterState [] Set.empty
        , rsProgram  = emptyProg
        , rsNormProg = []
        , rsPFNames  = Set.empty
        }
  runInputT defaultSettings (loop initState)

loop :: REPLState -> InputT IO ()
loop st = do
  let prompt = case getWorldNumber (rsInterp st) of
        Nothing -> "> "
        Just n  -> show n ++ "> "
  minput <- getInputLine prompt
  case minput of
    Nothing -> outputStrLn "Goodbye."
    Just input ->
      let trimmed = dropWhile (== ' ') input
      in if null trimmed then loop st
         else do
           result <- processInput trimmed st
           case result of
             Nothing  -> outputStrLn "Goodbye."
             Just st' -> loop st'

-- | Parse a colon command into (command, arguments).
parseCommand :: String -> Maybe (String, String)
parseCommand (':' : rest) =
  let (cmd, args) = break (== ' ') rest
  in  Just (':' : cmd, dropWhile (== ' ') args)
parseCommand _ = Nothing

processInput :: String -> REPLState -> InputT IO (Maybe REPLState)
processInput input st = case parseCommand input of
  Just (cmd, args) -> dispatchCommand cmd args st
  Nothing          -> handleProgramInput input st

dispatchCommand :: String -> String -> REPLState -> InputT IO (Maybe REPLState)
dispatchCommand cmd args st = case cmd of
  ":quit"     -> return Nothing
  ":q"        -> return Nothing
  ":help"     -> showHelp >> return (Just st)
  ":load"     -> requireArg "filename" args st (cmdLoad st)
  ":save"     -> requireArg "filename" args st (cmdSave st)
  ":assert"   -> requireArg "atom"     args st (cmdAssert st)
  ":query"    -> requireArg "atom"     args st (cmdQuery st)
  ":step"     -> cmdStep args st
  ":world"    -> noArgs cmd args st cmdWorld
  ":history"  -> noArgs cmd args st cmdHistory
  ":program"  -> noArgs cmd args st cmdProgram
  ":trace"    -> noArgs cmd args st cmdTrace
  ":examples" -> noArgs cmd args st cmdExamples
  ":reset"    -> noArgs cmd args st cmdReset
  _           -> unknownCommand cmd st

-- | Require a non-empty argument. If missing, print an error and return the state unchanged.
requireArg :: String -> String -> REPLState -> (String -> InputT IO (Maybe REPLState)) -> InputT IO (Maybe REPLState)
requireArg label args st action
  | null args = do
      outputStrLn $ "Missing argument: <" ++ label ++ ">"
      return (Just st)
  | otherwise = action args

-- | Warn if unexpected arguments are given, but run the command anyway.
noArgs :: String -> String -> REPLState -> (REPLState -> InputT IO (Maybe REPLState)) -> InputT IO (Maybe REPLState)
noArgs cmd args st action = do
  when (not (null args)) $
    outputStrLn $ cmd ++ ": ignoring unexpected arguments: " ++ args
  action st

unknownCommand :: String -> REPLState -> InputT IO (Maybe REPLState)
unknownCommand cmd st = do
  outputStrLn $ "Unknown command: " ++ cmd
  outputStrLn "Type :help for available commands."
  return (Just st)

cmdLoad :: REPLState -> String -> InputT IO (Maybe REPLState)
cmdLoad st fp = do
  fileResult <- liftIO (try (readFile fp) :: IO (Either IOException String))
  case fileResult of
    Left err -> do
      outputStrLn $ "Error loading file: " ++ show err
      return (Just st)
    Right contents -> case parseProgram fp contents of
      Left err -> do
        outputStrLn $ "Parse error: " ++ errorBundlePretty err
        return (Just st)
      Right prog -> case normalize prog of
        Left err -> do
          outputStrLn $ "Normalization error: " ++ err
          return (Just st)
        Right ((normProg, pfNames), warnings) -> do
          liftIO $ mapM_ (hPutStrLn stderr) warnings
          let interp = newInterpreterState normProg pfNames
          outputStrLn $ "Loaded " ++ show (length (progRules prog)) ++ " rules and "
                      ++ show (length (progPatternFuncs prog)) ++ " pattern functions from " ++ fp
          return $ Just st { rsProgram  = prog
                           , rsNormProg = normProg
                           , rsInterp   = interp
                           , rsPFNames  = pfNames
                           }

cmdSave :: REPLState -> String -> InputT IO (Maybe REPLState)
cmdSave st fp = do
  liftIO $ writeFile fp (ppProgram (rsProgram st))
  outputStrLn $ "Saved program to " ++ fp
  return (Just st)

cmdAssert :: REPLState -> String -> InputT IO (Maybe REPLState)
cmdAssert st factStr = case parseAtom "<repl>" factStr of
  Left err -> do
    outputStrLn $ "Parse error: " ++ errorBundlePretty err
    return (Just st)
  Right atom ->
    if isGroundAtom atom
      then return $ Just st { rsInterp = assertFact atom (rsInterp st) }
      else do
        outputStrLn "Asserted facts must be ground (no variables)."
        return (Just st)

cmdQuery :: REPLState -> String -> InputT IO (Maybe REPLState)
cmdQuery st queryStr = case parseAtom "<repl>" queryStr of
  Left err -> do
    outputStrLn $ "Parse error: " ++ errorBundlePretty err
    return (Just st)
  Right atom -> do
    let results = queryAtom atom (rsInterp st)
    if null results
      then outputStrLn "No."
      else do
        outputStrLn "Yes."
        mapM_ (\s -> outputStrLn $ "  " ++ showSubst s) results
    return (Just st)

cmdStep :: String -> REPLState -> InputT IO (Maybe REPLState)
cmdStep args st = do
  let doStep n = case stepWorldN n (rsInterp st) of
        Left err -> do outputStrLn $ "Error: " ++ err; return (Just st)
        Right st' -> return $ Just st { rsInterp = st' }
  case args of
    [] -> doStep 1
    _  -> case readMaybe args :: Maybe Int of
      Just n | n > 0 -> doStep n
      Just _ -> do outputStrLn "Step count must be a positive integer."; return (Just st)
      Nothing -> do outputStrLn $ "Invalid step count: " ++ args; return (Just st)

cmdWorld :: REPLState -> InputT IO (Maybe REPLState)
cmdWorld st = do
  case currentWorld (rsInterp st) of
    Nothing -> outputStrLn "No world computed yet. Use :step to advance."
    Just w -> do
      let userFacts = filter (not . isInternalAtom) (Set.toList (worldToSet w))
      case getWorldNumber (rsInterp st) of
        Nothing -> outputStrLn "World:"
        Just n  -> outputStrLn $ "World " ++ show n ++ ":"
      mapM_ (outputStrLn . ("  " ++) . ppAtom) userFacts
  return (Just st)

cmdHistory :: REPLState -> InputT IO (Maybe REPLState)
cmdHistory st = do
  let hist = Interp.getHistory (rsInterp st)
  if null hist
    then outputStrLn "No history yet. Use :step to advance."
    else mapM_ (\(i, w) -> do
      let userFacts = filter (not . isInternalAtom) (Set.toList (worldToSet w))
      outputStrLn $ "World " ++ show i ++ ":"
      mapM_ (outputStrLn . ("  " ++) . ppAtom) userFacts
      ) (zip [(0::Int)..] hist)
  return (Just st)

cmdProgram :: REPLState -> InputT IO (Maybe REPLState)
cmdProgram st = do
  outputStrLn "=== Source Program ==="
  outputStrLn $ ppProgram (rsProgram st)
  outputStrLn "=== Normalized Program ==="
  outputStrLn $ ppNormalProgram (rsNormProg st)
  return (Just st)

cmdTrace :: REPLState -> InputT IO (Maybe REPLState)
cmdTrace st = do
  let traces = traceDerivations (rsInterp st)
  if null traces
    then outputStrLn "No derivations to trace. Use :step to advance."
    else do
      let wnStr = case getWorldNumber (rsInterp st) of
            Nothing -> "?"
            Just n  -> show n
      outputStrLn $ "Derivations for world " ++ wnStr ++ ":"
      let userTraces = filter (\(a, _) -> not (isInternalAtom a)) traces
      mapM_ (\(fact, rule) ->
        outputStrLn $ "  " ++ ppAtom fact ++ "  <--  " ++ ppNormalRule rule
        ) userTraces
  return (Just st)

cmdExamples :: REPLState -> InputT IO (Maybe REPLState)
cmdExamples st = do
  outputStrLn "Example programs you can try:\n"
  outputStrLn "  % Simple fact derivation"
  outputStrLn "  hot(heater) => off(heater)."
  outputStrLn "  ~hot(heater) => on(heater)."
  outputStrLn ""
  outputStrLn "  % Temporal: previous world"
  outputStrLn "  @on(X) /\\ hot(X) => warning(X)."
  outputStrLn ""
  outputStrLn "  % Future: next step"
  outputStrLn "  request(X) => next process(X)."
  outputStrLn ""
  outputStrLn "  % Load example files with :load examples/<name>.tpl"
  return (Just st)

cmdReset :: REPLState -> InputT IO (Maybe REPLState)
cmdReset _ = do
  outputStrLn "State reset."
  return $ Just REPLState
    { rsInterp   = newInterpreterState [] Set.empty
    , rsProgram  = Program [] []
    , rsNormProg = []
    , rsPFNames  = Set.empty
    }

handleProgramInput :: String -> REPLState -> InputT IO (Maybe REPLState)
handleProgramInput input st = case parseProgramItem "<repl>" input of
  Left err -> do
    outputStrLn $ "Parse error: " ++ errorBundlePretty err
    return (Just st)
  Right item -> do
    let prog = rsProgram st
        (prog', addedMsg) = case item of
          Left pf -> (prog { progPatternFuncs = progPatternFuncs prog ++ [pf] },
                      "Added: " ++ ppPatternFunc pf)
          Right rule -> (prog { progRules = progRules prog ++ [rule] },
                         "Added: " ++ ppRule rule)
    case normalize prog' of
      Left err -> do
        outputStrLn $ "Normalization error: " ++ err
        return (Just st)
      Right ((normProg, pfNames), warnings) -> do
        liftIO $ mapM_ (hPutStrLn stderr) warnings
        let oldInterp = rsInterp st
            interp' = oldInterp { isProgram = normProg, isPFNames = pfNames }
        outputStrLn addedMsg
        when (isJust (isWorldNum oldInterp)) $
          outputStrLn "Warning: past worlds were computed under the old program."
        return $ Just st { rsProgram  = prog'
                         , rsNormProg = normProg
                         , rsInterp   = interp'
                         , rsPFNames  = pfNames
                         }

showHelp :: InputT IO ()
showHelp = do
  outputStrLn "Commands:"
  outputStrLn "  :load <file>    Load a Temporal Prolog program"
  outputStrLn "  :step [n]       Advance n worlds (default 1)"
  outputStrLn "  :assert <atom>  Assert a ground fact for the next step"
  outputStrLn "  :query <atom>   Query the current world"
  outputStrLn "  :world          Show the current world"
  outputStrLn "  :history        Show all past worlds"
  outputStrLn "  :program        Show the loaded program"
  outputStrLn "  :trace          Show which rules derived each fact"
  outputStrLn "  :save <file>    Save the current program to a file"
  outputStrLn "  :examples       Show example programs"
  outputStrLn "  :reset          Reset the interpreter"
  outputStrLn "  :help           Show this help"
  outputStrLn "  :quit           Exit"
  outputStrLn ""
  outputStrLn "  Or type a rule directly to add it to the program."
  outputStrLn "  Example: temperature(X) > 100 => alarm(X)."

-- | Check if an atom is internal (should be hidden from user-facing output).
-- Matches 'true', 'at', and normalizer-generated auxiliary names (e.g. always_aux0).
isInternalAtom :: Atom -> Bool
isInternalAtom (Atom "true" []) = True
isInternalAtom (Atom "at" _)    = True
isInternalAtom (Atom name _)    = isGeneratedAuxName name

-- | Check if a name matches the normalizer's freshName pattern: *_aux<digits>
isGeneratedAuxName :: String -> Bool
isGeneratedAuxName name =
  let rev = reverse name
      (digits, rest) = span isDigit rev
  in  not (null digits) && take 4 rest == "xua_"

showSubst :: Subst -> String
showSubst s
  | null pairs = "{}"
  | otherwise  = unwords [v ++ " = " ++ ppTerm t | (v, t) <- pairs]
  where pairs = Map.toList s
