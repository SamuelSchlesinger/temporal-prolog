module Main where

import Control.Monad (forM_)
import Data.Bits (xor)
import Data.Char (ord)
import qualified Data.Set as Set
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)
import System.Environment (getArgs)
import Text.Read (readMaybe)

import TemporalProlog.Interpreter
import TemporalProlog.Normalizer
import TemporalProlog.Parser
import TemporalProlog.Syntax

main :: IO ()
main = do
  args <- getArgs
  let chainLength = argument 0 50 args
      itemCount = argument 1 20 args
      iterations = argument 2 100 args
  (program, pfNames) <- compileProgram (chainSource chainLength)
  -- Validate once outside the timed loop and force the digest.
  expected <- either fail pure (execute program pfNames itemCount 0)
  let summary = semanticSummary chainLength itemCount expected
      digest = fnv1a summary
  digest `seq` pure ()
  start <- getMonotonicTimeNSec
  forM_ [1..iterations] $ \iteration -> do
    state <- either fail pure (execute program pfNames itemCount iteration)
    worldSize state `seq` pure ()
  end <- getMonotonicTimeNSec
  let elapsedMs = fromIntegral (end - start) / 1000000 :: Double
  putStrLn $ "implementation=haskell workload=chain parameters=length:"
          ++ show chainLength ++ ",items:" ++ show itemCount
          ++ " iterations=" ++ show iterations
          ++ " elapsed_ms=" ++ show elapsedMs
          ++ " digest=" ++ digest

argument :: Int -> Int -> [String] -> Int
argument index fallback args = case drop index args of
  value:_ -> maybe fallback id (readMaybe value)
  [] -> fallback

compileProgram :: String -> IO (NormalProgram, Set.Set Name)
compileProgram source = case parseProgram "<benchmark>" source of
  Left err -> fail (show err)
  Right parsed -> case normalize parsed of
    Left err -> fail err
    Right ((program, pfNames), _) -> pure (program, pfNames)

chainSource :: Int -> String
chainSource length_ = unlines $
  "seed(X) => p0(X)." :
  ["p" ++ show (index - 1) ++ "(X) => p" ++ show index ++ "(X)."
  | index <- [1..length_]]

execute :: NormalProgram -> Set.Set Name -> Int -> Int -> Either String InterpreterState
execute program pfNames itemCount salt =
  let initial = newInterpreterState program pfNames
      asserted = foldl (flip assertFact) initial
        [Atom "seed" [TFun ("item" ++ show salt ++ "_" ++ show index) []]
        | index <- [0..itemCount - 1]]
  in stepWorld asserted

worldSize :: InterpreterState -> Int
worldSize state = maybe 0 (Set.size . worldToSet) (currentWorld state)

semanticSummary :: Int -> Int -> InterpreterState -> String
semanticSummary length_ itemCount state =
  let userCount = maybe 0 (length . filter userAtom . Set.toList . worldToSet) (currentWorld state)
      terminal = Atom ("p" ++ show length_) [TFun ("item0_" ++ show (itemCount - 1)) []]
      hasTerminal = maybe False (worldMember terminal) (currentWorld state)
  in "chain:" ++ show length_ ++ ":" ++ show itemCount ++ ":"
      ++ show userCount ++ ":" ++ if hasTerminal then "true" else "false"
  where
    userAtom (Atom "at" _) = False
    userAtom (Atom "true" []) = False
    userAtom _ = True

fnv1a :: String -> String
fnv1a = pad16 . (`showHex` "") . foldl step 14695981039346656037
  where
    step :: Word64 -> Char -> Word64
    step hash char = (hash `xor` fromIntegral (ord char)) * 1099511628211
    pad16 value = replicate (16 - length value) '0' ++ value

showHex :: Word64 -> ShowS
showHex value
  | value < 16 = showChar (digits !! fromIntegral value)
  | otherwise = showHex (value `div` 16) . showChar (digits !! fromIntegral (value `mod` 16))
  where digits = "0123456789abcdef"
