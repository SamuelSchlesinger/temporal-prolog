-- |
-- Module      : TemporalProlog.ModelChecker
-- Description : Bounded branching protocol model checker
--
-- Explores every minimal-model branch admitted by a scenario.  Each safety
-- invariant names a forbidden stored-fact pattern; a branch terminates at the
-- first matching world and can be rendered as a counterexample trace.
-- Exploration is deliberately bounded because the underlying language may have an
-- infinite state space.
module TemporalProlog.ModelChecker
  ( CheckNode(..)
  , CheckResult(..)
  , runModelCheck
  , runModelCheckWithAuxiliaries
  , checkPassed
  , counterexampleTraces
  , renderCheckSummary
  , renderCheckDot
  ) where

import Control.Monad (foldM, forM)
import Data.List (intercalate, sortOn)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Set (Set)

import TemporalProlog.Interpreter
import TemporalProlog.Scenario
import TemporalProlog.Syntax

data CheckNode = CheckNode
  { checkNodeId         :: Int
  , checkNodeParent     :: Maybe Int
  , checkNodeStep       :: Maybe Int
  , checkNodeAssertions :: [Atom]
  , checkNodeFacts      :: [Atom]
  , checkNodeViolations :: [String]
  } deriving (Eq, Show)

data CheckResult = CheckResult
  { checkResultScenario       :: Scenario
  , checkResultNodes          :: [CheckNode]
  , checkResultTerminalNodes  :: [Int]
  , checkResultMaxWidth       :: Int
  , checkResultAuxiliaryPredicates :: Set Name
  } deriving (Eq, Show)

data ActiveNode = ActiveNode Int InterpreterState

data Child = Child
  { childParent     :: Int
  , childState      :: InterpreterState
  , childAssertions :: [Atom]
  , childFacts      :: [Atom]
  , childViolations :: [String]
  }

-- | Explore a scenario breadth-first.  Violating nodes are retained as
-- terminal counterexamples but are not expanded further.
runModelCheck
  :: Scenario
  -> NormalProgram
  -> Set Name
  -> Either String CheckResult
runModelCheck scenario program pfNames =
  runModelCheckWithAuxiliaries scenario program pfNames Set.empty

-- | Model checking with exact normalizer-generated predicate metadata for
-- user-facing summaries and graphs.
runModelCheckWithAuxiliaries
  :: Scenario
  -> NormalProgram
  -> Set Name
  -> Set Name
  -> Either String CheckResult
runModelCheckWithAuxiliaries scenario program pfNames auxiliaryPredicates =
  go 0 1 [root]
    [ActiveNode 0
      (newInterpreterStateWithAuxiliaries program pfNames auxiliaryPredicates)]
    [] 0
  where
    root = CheckNode 0 Nothing Nothing [] [] []

    go step nextId nodes active violatedTerminals maxWidth
      | step >= scenarioSteps scenario || null active =
          Right CheckResult
            { checkResultScenario = scenario
            , checkResultNodes = nodes
            , checkResultTerminalNodes = violatedTerminals ++ map activeId active
            , checkResultMaxWidth = maxWidth
            , checkResultAuxiliaryPredicates = auxiliaryPredicates
            }
      | otherwise = do
          children <- fmap concat $ mapM (expand step) active
          let identifiers = [nextId .. nextId + length children - 1]
              assigned = zipWith assign identifiers children
              newNodes = map fst assigned
              newActive = [a | (_, Just a) <- assigned]
              newViolations = [checkNodeId n | (n, Nothing) <- assigned]
          go (step + 1) (nextId + length children)
            (nodes ++ newNodes) newActive
            (violatedTerminals ++ newViolations)
            (max maxWidth (length children))

    activeId (ActiveNode identifier _) = identifier

    expand step (ActiveNode parent state) = fmap concat $ mapM expandInput inputVariants
      where
        fixedAssertions = Map.findWithDefault [] step (scenarioAssertions scenario)
        groups = Map.findWithDefault [] step (scenarioChoices scenario)
        inputVariants = map (fixedAssertions ++) (choiceVariants groups)

        expandInput assertions = do
          asserted <- foldM (flip assertFactEither) state assertions
          branches <- stepWorldAll asserted
          let ordered = sortOn branchKey branches
          forM ordered $ \branch ->
            let violations = violatedInvariants branch
                facts = maybe [] (Set.toAscList . worldToSet) (currentWorld branch)
            in Right Child
              { childParent = parent
              , childState = branch
              , childAssertions = assertions
              , childFacts = facts
              , childViolations = violations
              }

    branchKey = maybe Set.empty worldToSet . currentWorld

    violatedInvariants state = case currentWorld state of
      Nothing -> []
      Just world ->
        [ invariantName invariant
        | invariant <- scenarioInvariants scenario
        , worldMatches (invariantForbidden invariant) world
        ]

    assign identifier child =
      let node = CheckNode
            { checkNodeId = identifier
            , checkNodeParent = Just (childParent child)
            , checkNodeStep = getWorldNumber (childState child)
            , checkNodeAssertions = childAssertions child
            , checkNodeFacts = childFacts child
            , checkNodeViolations = childViolations child
            }
          active = if null (childViolations child)
            then Just (ActiveNode identifier (childState child))
            else Nothing
      in (node, active)

checkPassed :: CheckResult -> Bool
checkPassed = all (null . checkNodeViolations) . checkResultNodes

-- | Reconstruct root-to-violation paths.  The synthetic root is omitted.
counterexampleTraces :: CheckResult -> [[CheckNode]]
counterexampleTraces result =
  map traceTo violatingNodes
  where
    nodes = checkResultNodes result
    violatingNodes = filter (not . null . checkNodeViolations) nodes
    nodeAt identifier = nodes !! identifier
    traceTo node = reverse (walk node)
    walk node = case checkNodeParent node of
      Nothing -> []
      Just 0  -> [node]
      Just parent -> node : walk (nodeAt parent)

renderCheckSummary :: Int -> Bool -> CheckResult -> String
renderCheckSummary maxCounterexamples includeInternal result =
  unlines (header ++ concatMap renderCounterexample selected)
  where
    scenario = checkResultScenario result
    nodes = checkResultNodes result
    violationNodes = filter (not . null . checkNodeViolations) nodes
    safeLeaves = length
      [ identifier
      | identifier <- checkResultTerminalNodes result
      , null (checkNodeViolations (nodes !! identifier))
      ]
    header =
      [ "scenario=" ++ scenarioName scenario
      , "steps=" ++ show (scenarioSteps scenario)
      , "nodes=" ++ show (length nodes)
      , "leaves=" ++ show (length (checkResultTerminalNodes result))
      , "safe_leaves=" ++ show safeLeaves
      , "max_width=" ++ show (checkResultMaxWidth result)
      , "input_mode=" ++ inputMode scenario
      , "invariants=" ++ show (length (scenarioInvariants scenario))
      , "violations=" ++ show (length violationNodes)
      , "result=" ++ resultLabel result
      ]
    selected = take (max 0 maxCounterexamples) (counterexampleTraces result)

    renderCounterexample [] = []
    renderCounterexample trace =
      let finalNode = last trace
      in ("counterexample invariant="
          ++ intercalate "," (checkNodeViolations finalNode)
          ++ " node=" ++ show (checkNodeId finalNode))
         : map renderTraceStep trace

    renderTraceStep node =
      "  w" ++ show (fromMaybe 0 (checkNodeStep node))
      ++ " assertions=" ++ renderAtoms (checkNodeAssertions node)
      ++ " facts=" ++ renderAtoms
          (visibleFacts includeInternal auxiliaryPredicates (checkNodeFacts node))

    auxiliaryPredicates = checkResultAuxiliaryPredicates result

renderCheckDot :: Bool -> CheckResult -> String
renderCheckDot includeInternal result = unlines $
  [ "digraph temporal_prolog {"
  , "  rankdir=LR;"
  , "  graph [labelloc=t, label=\"" ++ dotEscape title ++ "\"];"
  , "  node [shape=box, fontname=\"monospace\"] ;"
  ]
  ++ map renderNode nodes
  ++ concatMap renderEdge (drop 1 nodes)
  ++ ["}"]
  where
    nodes = checkResultNodes result
    terminals = Set.fromList (checkResultTerminalNodes result)
    auxiliaryPredicates = checkResultAuxiliaryPredicates result
    title = scenarioName (checkResultScenario result)
      ++ ": " ++ if checkPassed result then "BOUNDED SAFE" else "UNSAFE"

    renderNode node
      | checkNodeId node == 0 = "  n0 [shape=ellipse, label=\"start\"];"
      | otherwise =
          let facts = visibleFacts includeInternal auxiliaryPredicates
                (checkNodeFacts node)
              violationLines = map ("! " ++) (checkNodeViolations node)
              label = unlinesNoTrailing
                (("w" ++ show (fromMaybe 0 (checkNodeStep node)))
                 : map canonicalAtom facts ++ violationLines)
              attrs
                | not (null (checkNodeViolations node)) =
                    ", color=\"#b91c1c\", penwidth=2, style=filled, fillcolor=\"#fee2e2\""
                | checkNodeId node `Set.member` terminals = ", peripheries=2"
                | otherwise = ""
          in "  n" ++ show (checkNodeId node) ++ " [label=\""
             ++ dotEscape label ++ "\"" ++ attrs ++ "];"

    renderEdge node = case checkNodeParent node of
      Nothing -> []
      Just parent ->
        let assertionLabel = intercalate "," (map canonicalAtom (checkNodeAssertions node))
            attr = if null assertionLabel
              then ""
              else " [label=\"" ++ dotEscape assertionLabel ++ "\"]"
        in ["  n" ++ show parent ++ " -> n" ++ show (checkNodeId node) ++ attr ++ ";"]

visibleFacts :: Bool -> Set Name -> [Atom] -> [Atom]
visibleFacts True _ = id
visibleFacts False auxiliaryPredicates =
  filter (not . internalAtom auxiliaryPredicates)

internalAtom :: Set Name -> Atom -> Bool
internalAtom _ (Atom "true" []) = True
internalAtom _ (Atom "at" _) = True
internalAtom auxiliaryPredicates (Atom name _) =
  name `Set.member` auxiliaryPredicates

renderAtoms :: [Atom] -> String
renderAtoms atoms = "[" ++ intercalate "," (map canonicalAtom atoms) ++ "]"

canonicalAtom :: Atom -> String
canonicalAtom (Atom name []) = name
canonicalAtom (Atom name terms) = name ++ "(" ++ intercalate "," (map canonicalTerm terms) ++ ")"

canonicalTerm :: Term -> String
canonicalTerm (TVar variable) = variable
canonicalTerm (TFun "[]" []) = "[]"
canonicalTerm (TFun "." [headTerm, tailTerm]) =
  "[" ++ canonicalTerm headTerm ++ canonicalListTail tailTerm ++ "]"
canonicalTerm (TFun name []) = name
canonicalTerm (TFun name terms) = name ++ "(" ++ intercalate "," (map canonicalTerm terms) ++ ")"
canonicalTerm (TPrev term) = "@" ++ canonicalTerm term

canonicalListTail :: Term -> String
canonicalListTail (TFun "[]" []) = ""
canonicalListTail (TFun "." [headTerm, tailTerm]) =
  "," ++ canonicalTerm headTerm ++ canonicalListTail tailTerm
canonicalListTail term = "|" ++ canonicalTerm term

dotEscape :: String -> String
dotEscape = concatMap escape
  where
    escape '\\' = "\\\\"
    escape '"' = "\\\""
    escape '\n' = "\\n"
    escape character = [character]

unlinesNoTrailing :: [String] -> String
unlinesNoTrailing = intercalate "\n"

choiceVariants :: [ChoiceGroup] -> [[Atom]]
choiceVariants [] = [[]]
choiceVariants (group:rest) =
  [ alternativeAtoms alternative ++ suffix
  | alternative <- choiceGroupAlternatives group
  , suffix <- choiceVariants rest
  ]
  where
    alternativeAtoms (ChoiceAtom atom) = [atom]
    alternativeAtoms ChoiceNone = []

inputMode :: Scenario -> String
inputMode scenario
  | Map.null (scenarioChoices scenario) = "fixed-schedule"
  | otherwise = "configured-choices"

resultLabel :: CheckResult -> String
resultLabel result
  | checkPassed result = "BOUNDED_SAFE"
  | otherwise = "UNSAFE"
