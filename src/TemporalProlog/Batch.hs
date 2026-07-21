-- |
-- Module      : TemporalProlog.Batch
-- Description : Deterministic branch-preserving batch execution
--
-- Provides the non-interactive execution contract shared with the Rust
-- implementation.  Every minimal-model branch is retained, sorted
-- canonically, and rendered with its complete observable history.
module TemporalProlog.Batch
  ( BatchOptions(..)
  , BatchResult(..)
  , runBatch
  , runBatchWithAuxiliaries
  , renderBatch
  , semanticDigest
  ) where

import Control.Monad (foldM, forM, forM_, unless, when)
import Data.Bits (xor)
import qualified Data.ByteString as ByteString
import Data.List (intercalate, sortOn)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEncoding
import Data.Word (Word8, Word64)
import Numeric (showHex)

import TemporalProlog.Interpreter
import TemporalProlog.Syntax

-- | Finite execution horizon, zero-indexed external inputs, and rendering
-- visibility for one batch run.
data BatchOptions = BatchOptions
  { batchSteps           :: Int             -- ^ Positive number of worlds.
  , batchAssertions      :: Map Int [Atom]  -- ^ Ground facts by world number.
  , batchIncludeInternal :: Bool            -- ^ Display generated auxiliaries.
  } deriving (Eq, Show)

-- | Completed branch-preserving execution and the options that produced it.
data BatchResult = BatchResult
  { batchResultOptions  :: BatchOptions
  , batchResultBranches :: [InterpreterState]
  , batchResultAuxiliaryPredicates :: Set Name
  } deriving (Show)

-- | Execute a finite schedule while preserving every minimal-model branch.
-- Invalid or unreachable scheduled inputs are rejected instead of silently
-- being ignored.
runBatch
  :: BatchOptions
  -> NormalProgram
  -> Set Name
  -> Either String BatchResult
runBatch options program pfNames =
  runBatchWithAuxiliaries options program pfNames Set.empty

-- | Batch execution with exact normalizer-generated predicate metadata for
-- user-facing rendering.
runBatchWithAuxiliaries
  :: BatchOptions
  -> NormalProgram
  -> Set Name
  -> Set Name
  -> Either String BatchResult
runBatchWithAuxiliaries options program pfNames auxiliaryPredicates = do
  validateOptions options
  branches <- go 0
    [newInterpreterStateWithAuxiliaries program pfNames auxiliaryPredicates]
  Right BatchResult
    { batchResultOptions = options
    , batchResultBranches = sortOn branchKey branches
    , batchResultAuxiliaryPredicates = auxiliaryPredicates
    }
  where
    go step branches
      | step >= batchSteps options = Right branches
      | otherwise = do
          next <- fmap concat $ forM branches $ \branch -> do
            asserted <- foldM (flip assertFactEither) branch
              (Map.findWithDefault [] step (batchAssertions options))
            stepWorldAll asserted
          go (step + 1) (sortOn branchKey next)

    branchKey = map worldToSet . getHistory

validateOptions :: BatchOptions -> Either String ()
validateOptions options = do
  when (batchSteps options <= 0) $
    Left "steps must be a positive integer"
  forM_ (Map.toList (batchAssertions options)) $ \(step, atoms) -> do
    when (step < 0) $ Left "assertion steps must be non-negative"
    when (step >= batchSteps options) $ Left $
      "assertion step " ++ show step ++ " is outside the "
      ++ show (batchSteps options) ++ "-world run"
    unless (all isGroundAtom atoms) $
      Left "assertions must be ground"

-- | Render a stable, line-oriented result.  The digest covers complete raw
-- worlds, including generated auxiliaries, while the fact lists hide them by
-- default for a user-facing view.
renderBatch :: BatchResult -> String
renderBatch result = unlines $
  [ "steps=" ++ show (batchSteps options)
  , "branches=" ++ show (length branches)
  ] ++ concat
    [ renderBranch index branch
    | (index, branch) <- zip [0 :: Int ..] branches
    ]
  where
    options = batchResultOptions result
    branches = batchResultBranches result
    auxiliaryPredicates = batchResultAuxiliaryPredicates result

    renderBranch index branch =
      ("branch=" ++ show index) :
      [ "  w" ++ show worldNumber ++ "=" ++ renderWorld world
      | (worldNumber, world) <- zip [0 :: Int ..] (getHistory branch)
      ] ++ ["  digest=" ++ semanticDigest (getHistory branch)]

    renderWorld world = "[" ++ intercalate "," visible ++ "]"
      where
        visible =
          [ canonicalAtom atom
          | atom <- Set.toAscList (worldToSet world)
          , batchIncludeInternal options
              || not (internalAtom auxiliaryPredicates atom)
          ]

-- | FNV-1a checksum of a complete history using the same canonical byte
-- stream as the Rust engine.
semanticDigest :: [World] -> String
semanticDigest worlds = pad16 $ showHex digest ""
  where
    bytes = TextEncoding.encodeUtf8 . Text.pack $ concat
      [ show index ++ ":" ++ concatMap ((++ ";") . canonicalAtom)
          (Set.toAscList (worldToSet world))
      | (index, world) <- zip [0 :: Int ..] worlds
      ]
    digest = ByteString.foldl' step 14695981039346656037 bytes
    step :: Word64 -> Word8 -> Word64
    step hash byte = (hash `xor` fromIntegral byte) * 1099511628211
    pad16 value = replicate (16 - length value) '0' ++ value

canonicalAtom :: Atom -> String
canonicalAtom (Atom name []) = name
canonicalAtom (Atom name terms) =
  name ++ "(" ++ intercalate "," (map canonicalTerm terms) ++ ")"

canonicalTerm :: Term -> String
canonicalTerm (TVar variable) = variable
canonicalTerm (TFun name []) = name
canonicalTerm (TFun name terms) =
  name ++ "(" ++ intercalate "," (map canonicalTerm terms) ++ ")"
canonicalTerm (TPrev term) = "@" ++ canonicalTerm term

internalAtom :: Set Name -> Atom -> Bool
internalAtom _ (Atom "true" []) = True
internalAtom _ (Atom "at" _) = True
internalAtom auxiliaryPredicates (Atom name _) =
  name `Set.member` auxiliaryPredicates
