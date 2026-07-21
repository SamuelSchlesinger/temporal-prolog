-- |
-- Module      : TemporalProlog.Scenario
-- Description : Portable bounded model-checking scenario format
--
-- A scenario names a Temporal Prolog program, fixes a finite exploration
-- horizon, supplies ground assertions at selected worlds, and declares
-- safety invariants as forbidden atom patterns.  The deliberately small,
-- line-oriented format is also implemented by the Rust engine.
module TemporalProlog.Scenario
  ( Invariant(..)
  , Scenario(..)
  , parseScenario
  ) where

import Control.Monad (foldM, unless, when)
import Data.Char (isAlphaNum, isSpace)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Text.Megaparsec (errorBundlePretty)
import Text.Read (readMaybe)

import TemporalProlog.Parser (parseAtom)
import TemporalProlog.Syntax (Atom, isGroundAtom)

data Invariant = Invariant
  { invariantName      :: String
  , invariantForbidden :: Atom
  } deriving (Eq, Ord, Show)

data Scenario = Scenario
  { scenarioName       :: String
  , scenarioProgram    :: FilePath
  , scenarioSteps      :: Int
  , scenarioAssertions :: Map Int [Atom]
  , scenarioInvariants :: [Invariant]
  } deriving (Eq, Show)

data PartialScenario = PartialScenario
  { partialName           :: Maybe String
  , partialProgram        :: Maybe FilePath
  , partialSteps          :: Maybe Int
  , partialAssertions     :: Map Int [Atom]
  , partialInvariants     :: [Invariant]
  , partialInvariantNames :: Set String
  }

emptyPartial :: PartialScenario
emptyPartial = PartialScenario Nothing Nothing Nothing Map.empty [] Set.empty

-- | Parse a portable @.tpmc@ scenario.  Directives occupy one line each:
--
-- @
-- name example
-- program example.tpl
-- steps 4
-- assert 0 request(1)
-- invariant mutual_exclusion forbids violation(mutual_exclusion)
-- @
parseScenario :: FilePath -> String -> Either String Scenario
parseScenario sourceName source = do
  partial <- foldM parseNumberedLine emptyPartial (zip [1 :: Int ..] (lines source))
  name <- requireField "name" (partialName partial)
  program <- requireField "program" (partialProgram partial)
  steps <- requireField "steps" (partialSteps partial)
  when (steps <= 0) $ Left "steps must be a positive integer"
  mapM_ (validateAssertionStep steps) (Map.keys (partialAssertions partial))
  Right Scenario
    { scenarioName = name
    , scenarioProgram = program
    , scenarioSteps = steps
    , scenarioAssertions = partialAssertions partial
    , scenarioInvariants = partialInvariants partial
    }
  where
    parseNumberedLine partial (lineNumber, original) =
      let line = trim (takeWhile (/= '%') original)
      in if null line
           then Right partial
           else firstLineError lineNumber (parseDirective lineNumber line partial)

    firstLineError lineNumber = either
      (Left . ((sourceName ++ ":" ++ show lineNumber ++ ": ") ++))
      Right

    validateAssertionStep steps step
      | step < 0 = Left "assertion steps must be non-negative"
      | step >= steps = Left $ "assertion step " ++ show step
          ++ " is outside the " ++ show steps ++ "-world horizon"
      | otherwise = Right ()

requireField :: String -> Maybe a -> Either String a
requireField field = maybe (Left $ "missing required '" ++ field ++ "' directive") Right

parseDirective :: Int -> String -> PartialScenario -> Either String PartialScenario
parseDirective lineNumber line partial =
  let (directive, rest) = splitWord line
  in case directive of
    "name" -> do
      value <- exactlyOne "name" rest
      unless (validName value) $ Left "scenario names may contain only letters, digits, '_' and '-'"
      ensureUnset "name" (partialName partial)
      Right partial { partialName = Just value }
    "program" -> do
      let value = trim rest
      when (null value) $ Left "program requires a relative or absolute path"
      ensureUnset "program" (partialProgram partial)
      Right partial { partialProgram = Just value }
    "steps" -> do
      value <- exactlyOne "steps" rest
      count <- maybe (Left "steps requires a positive integer") Right (readMaybe value)
      ensureUnset "steps" (partialSteps partial)
      Right partial { partialSteps = Just count }
    "assert" -> do
      let (stepText, atomText) = splitWord rest
      when (null stepText || null atomText) $ Left "assert requires STEP and ATOM"
      step <- maybe (Left "assert step must be an integer") Right (readMaybe stepText)
      atom <- parseScenarioAtom lineNumber atomText
      unless (isGroundAtom atom) $ Left "scheduled assertions must be ground"
      Right partial
        { partialAssertions = Map.insertWith (flip (++)) step [atom]
            (partialAssertions partial)
        }
    "invariant" -> do
      let (name, afterName) = splitWord rest
          (keyword, atomText) = splitWord afterName
      when (null name || keyword /= "forbids" || null atomText) $
        Left "invariant requires NAME forbids ATOM"
      unless (validName name) $ Left "invariant names may contain only letters, digits, '_' and '-'"
      when (name `Set.member` partialInvariantNames partial) $
        Left $ "duplicate invariant name '" ++ name ++ "'"
      atom <- parseScenarioAtom lineNumber atomText
      let invariant = Invariant name atom
      Right partial
        { partialInvariants = partialInvariants partial ++ [invariant]
        , partialInvariantNames = Set.insert name (partialInvariantNames partial)
        }
    _ -> Left $ "unknown directive '" ++ directive ++ "'"
  where
    parseScenarioAtom n text = case parseAtom ("<scenario line " ++ show n ++ ">") text of
      Left err -> Left $ "invalid atom:\n" ++ errorBundlePretty err
      Right atom -> Right atom

ensureUnset :: String -> Maybe a -> Either String ()
ensureUnset _ Nothing = Right ()
ensureUnset field (Just _) = Left $ "duplicate '" ++ field ++ "' directive"

exactlyOne :: String -> String -> Either String String
exactlyOne directive rest = case words rest of
  [value] -> Right value
  _ -> Left $ directive ++ " requires exactly one value"

validName :: String -> Bool
validName name = not (null name) && all (\c -> isAlphaNum c || c == '_' || c == '-') name

splitWord :: String -> (String, String)
splitWord input =
  let stripped = dropWhile isSpace input
      (word, rest) = break isSpace stripped
  in (word, trim rest)

trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace
