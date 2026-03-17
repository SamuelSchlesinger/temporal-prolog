module Main where

import Control.Exception (try, evaluate, IOException, SomeException)
import Control.Monad.IO.Class (liftIO)
import Control.Monad (when)
import Data.List (isPrefixOf)
import Data.Maybe (isJust)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
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
  }

main :: IO ()
main = do
  putStrLn "Temporal Prolog — based on Sakuragawa 1986"
  putStrLn "Type :help for available commands."
  let emptyProg = Program [] []
      initState = REPLState
        { rsInterp   = newInterpreterState []
        , rsProgram  = emptyProg
        , rsNormProg = []
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
    Just input -> do
      let trimmed = dropWhile (== ' ') input
      if null trimmed
        then loop st
        else if trimmed == ":quit" || trimmed == ":q"
          then outputStrLn "Goodbye."
          else do
            st' <- processInput trimmed st
            loop st'

processInput :: String -> REPLState -> InputT IO REPLState
processInput input st
  | ":quit" `isPrefixOf` input = do
      outputStrLn "Goodbye."
      return st  -- will exit via the loop
  | ":q" == input = do
      outputStrLn "Goodbye."
      return st
  | ":help" `isPrefixOf` input = do
      showHelp
      return st
  | ":load " `isPrefixOf` input = do
      let fp = dropWhile (== ' ') (drop 6 input)
      liftIO (loadFile fp st)
  | ":step" `isPrefixOf` input = do
      let rest = dropWhile (== ' ') (drop 5 input)
          doStep n = do
            let stepped = stepWorldN n (rsInterp st)
            result <- liftIO $ try (evaluate (forceWorlds stepped)) :: InputT IO (Either SomeException InterpreterState)
            case result of
              Left err -> do outputStrLn $ "Error: " ++ show err; return st
              Right st' -> return $ st { rsInterp = st' }
      case rest of
        [] -> doStep 1
        _  -> case readMaybe rest :: Maybe Int of
          Just n | n > 0 -> doStep n
          Just _ -> do outputStrLn "Step count must be a positive integer."; return st
          Nothing -> do outputStrLn $ "Invalid step count: " ++ rest; return st
  | ":assert " `isPrefixOf` input = do
      let factStr = dropWhile (== ' ') (drop 8 input)
      case parseAtom "<repl>" factStr of
        Left err -> do
          outputStrLn $ "Parse error: " ++ errorBundlePretty err
          return st
        Right atom ->
          if isGroundAtom atom
            then return $ st { rsInterp = assertFact atom (rsInterp st) }
            else do
              outputStrLn "Asserted facts must be ground (no variables)."
              return st
  | ":query " `isPrefixOf` input = do
      let queryStr = dropWhile (== ' ') (drop 7 input)
      case parseAtom "<repl>" queryStr of
        Left err -> do
          outputStrLn $ "Parse error: " ++ errorBundlePretty err
          return st
        Right atom -> do
          let results = queryAtom atom (rsInterp st)
          if null results
            then outputStrLn "No."
            else do
              outputStrLn "Yes."
              mapM_ (\s -> outputStrLn $ "  " ++ showSubst s) results
          return st
  | ":world" `isPrefixOf` input = do
      case currentWorld (rsInterp st) of
        Nothing -> outputStrLn "No world computed yet. Use :step to advance."
        Just w -> do
          let userFacts = filter (not . isInternalAtom) (Set.toList w)
          case getWorldNumber (rsInterp st) of
            Nothing -> outputStrLn "World:"
            Just n  -> outputStrLn $ "World " ++ show n ++ ":"
          mapM_ (outputStrLn . ("  " ++) . ppAtom) userFacts
      return st
  | ":history" `isPrefixOf` input = do
      let hist = Interp.getHistory (rsInterp st)
      if null hist
        then outputStrLn "No history yet. Use :step to advance."
        else mapM_ (\(i, w) -> do
          let userFacts = filter (not . isInternalAtom) (Set.toList w)
          outputStrLn $ "World " ++ show i ++ ":"
          mapM_ (outputStrLn . ("  " ++) . ppAtom) userFacts
          ) (zip [(0::Int)..] hist)
      return st
  | ":program" `isPrefixOf` input = do
      outputStrLn "=== Source Program ==="
      outputStrLn $ ppProgram (rsProgram st)
      outputStrLn "=== Normalized Program ==="
      outputStrLn $ ppNormalProgram (rsNormProg st)
      return st
  | ":reset" `isPrefixOf` input = do
      outputStrLn "State reset."
      return $ REPLState
        { rsInterp   = newInterpreterState []
        , rsProgram  = Program [] []
        , rsNormProg = []
        }
  | ":trace" `isPrefixOf` input = do
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
      return st
  | ":examples" `isPrefixOf` input = do
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
      return st
  | ":save " `isPrefixOf` input = do
      let fp = dropWhile (== ' ') (drop 6 input)
      liftIO $ writeFile fp (ppProgram (rsProgram st))
      outputStrLn $ "Saved program to " ++ fp
      return st
  | ":" `isPrefixOf` input = do
      outputStrLn $ "Unknown command: " ++ input
      outputStrLn "Type :help for available commands."
      return st
  | otherwise = do
      -- Try to parse as a rule and add to program
      case parseRule "<repl>" input of
        Left err -> do
          outputStrLn $ "Parse error: " ++ errorBundlePretty err
          return st
        Right rule -> do
          let prog = rsProgram st
              prog' = prog { progRules = progRules prog ++ [rule] }
          normResult <- liftIO $ try (normalize prog') :: InputT IO (Either IOException NormalProgram)
          case normResult of
            Left err -> do
              outputStrLn $ "Normalization error: " ++ show err
              return st
            Right normProg -> do
              let oldInterp = rsInterp st
                  interp' = oldInterp { isProgram = normProg }
              outputStrLn $ "Added: " ++ ppRule rule
              when (isJust (isWorldNum oldInterp)) $
                outputStrLn "Warning: past worlds were computed under the old program."
              return $ st { rsProgram  = prog'
                          , rsNormProg = normProg
                          , rsInterp   = interp'
                          }

loadFile :: FilePath -> REPLState -> IO REPLState
loadFile fp st = do
  fileResult <- try (readFile fp) :: IO (Either IOException String)
  case fileResult of
    Left err -> do
      putStrLn $ "Error loading file: " ++ show err
      return st
    Right contents -> case parseProgram fp contents of
      Left err -> do
        putStrLn $ "Parse error: " ++ errorBundlePretty err
        return st
      Right prog -> do
        normResult <- try (normalize prog) :: IO (Either IOException NormalProgram)
        case normResult of
          Left err -> do
            putStrLn $ "Normalization error: " ++ show err
            return st
          Right normProg -> do
            let interp = newInterpreterState normProg
            putStrLn $ "Loaded " ++ show (length (progRules prog)) ++ " rules and "
                      ++ show (length (progPatternFuncs prog)) ++ " pattern functions from " ++ fp
            return $ st { rsProgram  = prog
                        , rsNormProg = normProg
                        , rsInterp   = interp
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

-- | Check if an atom is internal (auxiliary predicates, built-in bookkeeping)
isInternalAtom :: Atom -> Bool
isInternalAtom (Atom "true" []) = True
isInternalAtom (Atom "at" _)    = True
isInternalAtom (Atom n _)       = "_aux" `isInfixOf` n
  where isInfixOf needle haystack = any (isPrefixOf needle) (tails haystack)
        tails [] = [[]]
        tails xs@(_:xs') = xs : tails xs'

showSubst :: Subst -> String
showSubst s
  | null pairs = "{}"
  | otherwise  = unwords [v ++ " = " ++ ppTerm t | (v, t) <- pairs]
  where pairs = Map.toList s

-- | Force evaluation of the worlds in an InterpreterState so that
-- errors (e.g. from stratification) are caught by 'evaluate'.
forceWorlds :: InterpreterState -> InterpreterState
forceWorlds st = case isWorlds st of
  []    -> st
  (w:_) -> w `seq` Set.size w `seq` st
