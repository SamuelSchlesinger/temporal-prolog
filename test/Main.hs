module Main where

import Control.Monad (forM_)
import Test.Hspec
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.Either (isLeft, isRight)

import TemporalProlog.Syntax
import TemporalProlog.Batch
import TemporalProlog.Parser
import TemporalProlog.PrettyPrint
import TemporalProlog.Normalizer
import TemporalProlog.Interpreter
import TemporalProlog.ModelChecker
import TemporalProlog.Scenario
import TemporalProlog.Unification

main :: IO ()
main = hspec $ do
  parserSpec
  normalizerSpec
  interpreterSpec
  unificationSpec
  eventuallyNextSpec
  patternFunctionSpec
  unificationEqualitySpec
  stratificationSpec
  safetyValidationSpec
  edgeCaseSpec
  runtimeBoundarySpec
  mixedTPrevSpec
  backwardChainingSpec
  correctnessAndFeatureSpec
  sharedConformanceSpec
  batchExecutionSpec
  modelCheckerSpec
  propositionalOracleSpec

-- Helper: parse and normalize a program string
parseAndNormalize :: String -> NormalProgram
parseAndNormalize src = case parseProgram "<test>" src of
  Left err -> error $ "Parse error: " ++ show err
  Right prog -> case normalize prog of
    Left err -> error $ "Normalization error: " ++ err
    Right ((np, _pfNames), _warnings) -> np

-- Helper: parse and normalize, returning both program and PF names
parseAndNormalizeWithPF :: String -> (NormalProgram, Set.Set String)
parseAndNormalizeWithPF src = case parseProgram "<test>" src of
  Left err -> error $ "Parse error: " ++ show err
  Right prog -> case normalize prog of
    Left err -> error $ "Normalization error: " ++ err
    Right ((np, pfNames), _warnings) -> (np, pfNames)

compileSource :: String -> Either String (NormalProgram, Set.Set String)
compileSource src = case parseProgram "<test>" src of
  Left err -> Left (show err)
  Right prog -> case normalize prog of
    Left err -> Left err
    Right ((np, pfNames), _warnings) -> Right (np, pfNames)

compileDetailedSource :: String -> Either String NormalizationResult
compileDetailedSource src = case parseProgram "<test>" src of
  Left err -> Left (show err)
  Right program -> normalizeDetailed program

-- Helper: run program for n steps, asserting facts at each step
-- assertions: list of (worldNum, [atomString]) pairs
runWithAssertions :: String -> [(Int, [String])] -> Int -> InterpreterState
runWithAssertions src assertions totalSteps =
  let (np, pfNames) = parseAndNormalizeWithPF src
      st0 = newInterpreterState np pfNames
      assertionMap = Map.fromListWith (++) assertions
  in foldl (\st i ->
       let withAsserts = case Map.lookup i assertionMap of
             Nothing -> st
             Just atoms -> foldl (\s a -> case parseAtom "<test>" a of
               Right atom -> assertFact atom s
               Left _ -> s) st atoms
       in case stepWorld withAsserts of
            Left err -> error $ "stepWorld failed: " ++ err
            Right st' -> st'
     ) st0 [0..totalSteps-1]

-- Helper: unwrap Either from stepWorld/stepWorldN, erroring on Left
unsafeStep :: InterpreterState -> InterpreterState
unsafeStep st = case stepWorld st of
  Left err -> error $ "stepWorld failed: " ++ err
  Right st' -> st'

unsafeStepN :: Int -> InterpreterState -> InterpreterState
unsafeStepN n st = case stepWorldN n st of
  Left err -> error $ "stepWorldN failed: " ++ err
  Right st' -> st'

worldContains :: InterpreterState -> String -> Bool
worldContains st atomStr = case (currentWorld st, parseAtom "<test>" atomStr) of
  (Just w, Right atom) -> worldMember atom w
  _ -> False

parserSpec :: Spec
parserSpec = describe "Parser" $ do
  it "parses simple atoms" $ do
    parseAtom "<test>" "foo" `shouldSatisfy` isRight
    parseAtom "<test>" "p(X, Y)" `shouldSatisfy` isRight

  it "parses variables" $ do
    parseTerm "<test>" "X" `shouldBe` Right (TVar "X")
    parseTerm "<test>" "MyVar" `shouldBe` Right (TVar "MyVar")

  it "parses numbers" $ do
    parseTerm "<test>" "42" `shouldBe` Right (TFun "42" [])

  it "canonicalizes arbitrary-precision integer spellings" $ do
    parseTerm "<test>" "0009223372036854775808"
      `shouldBe` Right (TFun "9223372036854775808" [])
    parseTerm "<test>" "-0" `shouldBe` Right (TFun "0" [])

  it "parses infix div and mod at multiplicative precedence" $ do
    parseTerm "<test>" "7 div 3 mod 2" `shouldBe` Right
      (TFun "mod"
        [ TFun "div" [TFun "7" [], TFun "3" []]
        , TFun "2" []
        ])

  it "parses functors" $ do
    parseTerm "<test>" "f(X, Y)" `shouldBe` Right (TFun "f" [TVar "X", TVar "Y"])

  it "accepts keywords as term constructors" $ do
    forM_
      [ "always", "since", "after", "for", "until", "atnext"
      , "eventually", "next", "true", "false", "is"
      ] $ \name ->
        parseTerm "<test>" name `shouldBe` Right (TFun name [])
    parseAtom "<test>" "keyword_terms(always, true, is)"
      `shouldSatisfy` isRight

  it "reserves temporal keywords only in callable position" $ do
    parseAtom "<test>" "since" `shouldSatisfy` isLeft
    parseAtom "<test>" "always" `shouldSatisfy` isLeft
    parseAtom "<test>" "is(X, 1)" `shouldSatisfy` isRight
    parseAtom "<test>" "div(a, b)" `shouldSatisfy` isRight

  it "rejects non-ASCII identifiers" $ do
    parseTerm "<test>" "Ä" `shouldSatisfy` isLeft
    parseAtom "<test>" "π" `shouldSatisfy` isLeft

  it "parses lists" $ do
    parseTerm "<test>" "[]" `shouldBe` Right (TFun "[]" [])
    parseTerm "<test>" "[X|Y]" `shouldBe` Right (TFun "." [TVar "X", TVar "Y"])
    parseTerm "<test>" "[a, b]" `shouldBe`
      Right (TFun "." [TFun "a" [], TFun "." [TFun "b" [], TFun "[]" []]])

  it "parses @-terms" $ do
    parseTerm "<test>" "@X" `shouldBe` Right (TPrev (TVar "X"))

  it "parses negation conditions" $ do
    parseCond "<test>" "~p(X)" `shouldSatisfy` isRight

  it "parses previous conditions" $ do
    parseCond "<test>" "@p(X)" `shouldSatisfy` isRight

  it "parses has-been conditions" $ do
    parseCond "<test>" "#p(X)" `shouldSatisfy` isRight

  it "parses once conditions" $ do
    parseCond "<test>" "?p(X)" `shouldSatisfy` isRight

  it "preserves documented Unicode operator families" $ do
    let p = CAtom (Atom "p" [])
    parseCond "<test>" "●p" `shouldBe` Right (CPrev p)
    parseCond "<test>" "•p" `shouldBe` Right (CPrev p)
    parseCond "<test>" "■p" `shouldBe` Right (CHasBeen p)
    parseCond "<test>" "◆p" `shouldBe` Right (COnce p)
    parseCond "<test>" "◇p" `shouldBe` Right (CEventually p)
    parseRule "<test>" "a ⇒ ○b." `shouldBe` Right
      (Rule [CAtom (Atom "a" [])] (RNext (RAtom (Atom "b" []))))
    parseRule "<test>" "□p." `shouldBe` Right
      (Fact (RAlways (RAtom (Atom "p" []))))
    parseProgram "<test>" "identity(X) → X." `shouldSatisfy` isRight

  it "parses since/after/for" $ do
    parseCond "<test>" "a since b" `shouldSatisfy` isRight
    parseCond "<test>" "a after b" `shouldSatisfy` isRight
    parseCond "<test>" "a for 3" `shouldSatisfy` isRight

  it "preserves arbitrary-precision for counts before normalization" $ do
    parseCond "<test>" "a for 18446744073709551617" `shouldBe` Right
      (CFor (CAtom (Atom "a" [])) 18446744073709551617)

  it "requires parentheses for chained past-time operators" $ do
    parseCond "<test>" "a since b since c" `shouldSatisfy` isLeft
    parseCond "<test>" "a after b after c" `shouldSatisfy` isLeft
    parseCond "<test>" "a for 2 after b" `shouldSatisfy` isLeft
    parseCond "<test>" "(a since b) after c" `shouldSatisfy` isRight

  it "parses implication rules" $ do
    parseRule "<test>" "a => b." `shouldSatisfy` isRight
    parseRule "<test>" "a /\\ b => c." `shouldSatisfy` isRight

  it "parses fact rules" $ do
    parseRule "<test>" "p(X)." `shouldSatisfy` isRight

  it "parses always results" $ do
    parseRule "<test>" "always p." `shouldSatisfy` isRight

  it "parses until results" $ do
    parseRule "<test>" "a => p until q." `shouldSatisfy` isRight

  it "gives result conjunction precedence over until and atnext" $ do
    parseRule "<test>" "start => left /\\ right until stop."
      `shouldBe` Right
        (Rule [CAtom (Atom "start" [])]
          (RUntil
            (RAnd [RAtom (Atom "left" []), RAtom (Atom "right" [])])
            (CAtom (Atom "stop" []))))
    parseRule "<test>" "arm => bell /\\ light atnext fire."
      `shouldBe` Right
        (Rule [CAtom (Atom "arm" [])]
          (RAtNext
            (RAnd [RAtom (Atom "bell" []), RAtom (Atom "light" [])])
            (CAtom (Atom "fire" []))))

  it "requires parentheses for nested until and atnext results" $ do
    parseRule "<test>" "p until a until b." `shouldSatisfy` isLeft
    parseRule "<test>" "p atnext a atnext b." `shouldSatisfy` isLeft

  it "parses infix atoms" $ do
    parseCond "<test>" "X > 5" `shouldSatisfy` isRight
    parseCond "<test>" "X = Y" `shouldSatisfy` isRight

  it "parses programs" $ do
    let prog = "device(heater).\ndevice(X) /\\ hot(X) => off(X).\ndevice(X) /\\ ~hot(X) => on(X).\n"
    parseProgram "<test>" prog `shouldSatisfy` isRight

  it "parses pattern functions" $ do
    let prog = "append([], X) -> X.\n"
    case parseProgram "<test>" prog of
      Right p -> length (progPatternFuncs p) `shouldBe` 1
      Left _ -> expectationFailure "Failed to parse pattern function"

  it "parses conditional pattern-function reductions from the paper" $ do
    parseRule "<test>" "enabled(X) => choose(X) -> selected."
      `shouldBe` Right
        (Rule [CAtom (Atom "enabled" [TVar "X"])]
          (RPatternFunc "choose" [TVar "X"] (TFun "selected" [])))

  it "rejects keywords as predicate names" $ do
    parseAtom "<test>" "since" `shouldSatisfy` isLeft

  it "parses empty program" $ do
    parseProgram "<test>" "" `shouldBe` Right (Program [] [])
    parseProgram "<test>" "  \n  " `shouldBe` Right (Program [] [])

normalizerSpec :: Spec
normalizerSpec = describe "Normalizer" $ do
  it "normalizes simple facts" $ do
    let np = parseAndNormalize "p."
    length np `shouldBe` 1

  it "normalizes simple rules" $ do
    let np = parseAndNormalize "a => b."
    length np `shouldBe` 1

  it "rejects inconsistent source symbol signatures and builtin results" $ do
    let invalidPrograms =
          [ "p. p(a)."
          , "value(box). value(box(a))."
          , "choose(X) -> X. choose(X, Y) -> X."
          , "lookup(X) -> X. lookup(a)."
          , "at(99)."
          , "at(0, 1) => impossible."
          , "X is div(1) => impossible(X)."
          ]
    mapM_ (\source -> compileSource source `shouldSatisfy` isLeft)
      invalidPrograms

  it "keeps predicate and constructor namespaces distinct" $ do
    compileSource "tag(tag)." `shouldSatisfy` isRight

  it "reduces an unconditional always result to the bare result (paper step 1(2))" $ do
    let np = parseAndNormalize "always p."
    np `shouldBe` [NormalRule [] (Atom "p" [])]

  it "uses only result variables in a conditional always auxiliary" $ do
    let np = parseAndNormalize "start(X) => always running."
        auxHeads = [args | NormalRule _ (Atom name args) <- np, name == "always_aux0"]
    auxHeads `shouldSatisfy` (not . null)
    auxHeads `shouldSatisfy` all null

  it "does not collide generated predicates with source identifiers" $ do
    let np = parseAndNormalize $ unlines
          [ "always_aux0."
          , "start => always running."
          ]
        generatedNames =
          [ name
          | NormalRule _ (Atom name _) <- np
          , name /= "always_aux0"
          , name /= "running"
          ]
    generatedNames `shouldSatisfy` (not . null)
    generatedNames `shouldSatisfy` all (/= "always_aux0")

  it "records exact generated predicates without classifying source _aux names" $ do
    case parseProgram "<test>"
        "user_aux0. always_aux0. trigger => next generated." of
      Left err -> expectationFailure (show err)
      Right source -> case normalizeDetailed source of
        Left err -> expectationFailure err
        Right normalized -> do
          normalizedAuxiliaryPredicates normalized
            `shouldBe` Set.singleton "next_aux1"
          normalizedAuxiliaryPredicates normalized
            `shouldSatisfy` Set.notMember "user_aux0"

  it "increments arbitrary-precision source auxiliary suffixes exactly" $ do
    case parseProgram "<test>" $ unlines
        [ "user_aux18446744073709551615."
        , "trigger => next generated."
        ] of
      Left err -> expectationFailure (show err)
      Right source -> case normalizeDetailed source of
        Left err -> expectationFailure err
        Right normalized -> do
          normalizedAuxiliaryPredicates normalized
            `shouldBe` Set.singleton "next_aux18446744073709551616"
          normalizedAuxiliaryPredicates normalized
            `shouldSatisfy` Set.notMember "user_aux18446744073709551615"

  it "reduces an unconditional atnext result to its trigger rule (paper step 1(4))" $ do
    let np = parseAndNormalize "ready atnext trigger."
    np `shouldBe`
      [NormalRule [NormalCond 0 False (Atom "trigger" [])] (Atom "ready" [])]

  it "uses the previous trigger value in the until recurrence" $ do
    let np = parseAndNormalize "start => running until stop."
        recurrenceConds =
          [ cs
          | NormalRule cs (Atom name []) <- np
          , name == "until_aux0"
          , any ((== 1) . ncPrevDepth) cs
          ]
    recurrenceConds `shouldSatisfy` any
      (elem (NormalCond 1 True (Atom "stop" [])))

  it "expands for into repeated @" $ do
    let np = parseAndNormalize "a for 3 => b."
    -- a for 3 expands to a /\ @a /\ @@a
    let hasDepth2 = any (\r -> any (\c -> ncPrevDepth c == 2) (nrConditions r)) np
    hasDepth2 `shouldBe` True

  it "rejects zero repetitions for 'for'" $ do
    parseCond "<test>" "a for 0" `shouldSatisfy` isLeft

  it "enforces the portable for expansion limit without wrapping" $ do
    compileSource "a for 1000 => b." `shouldSatisfy` isRight
    compileSource "a for 1001 => b." `shouldSatisfy` isLeft
    compileSource "a for 18446744073709551617 => b." `shouldSatisfy` isLeft

  it "treats the Step-1 rewrite-round limit as inclusive" $ do
    let fired = RAtom (Atom "fired" [])
        resultProgram result = Program [Fact result] []
        nestedNext count = iterate RNext fired !! count
    normalizeDetailed (resultProgram (nestedNext maxNormalizationRounds))
      `shouldSatisfy` isRight
    normalizeDetailed (resultProgram (nestedNext (maxNormalizationRounds + 1)))
      `shouldSatisfy` isLeft

  it "treats the Step-2 rewrite-round limit as inclusive" $ do
    let fired = RAtom (Atom "fired" [])
        trigger = CAtom (Atom "trigger" [])
        conditionProgram condition =
          Program [Rule [condition] fired] []
        nestedEventually count = iterate CEventually trigger !! count
    normalizeDetailed (conditionProgram (nestedEventually maxNormalizationRounds))
      `shouldSatisfy` isRight
    normalizeDetailed (conditionProgram (nestedEventually (maxNormalizationRounds + 1)))
      `shouldSatisfy` isLeft

  it "treats the Step-4 rewrite-round limit as inclusive" $ do
    let fired = RAtom (Atom "fired" [])
        trigger = CAtom (Atom "trigger" [])
        conditionProgram condition =
          Program [Rule [condition] fired] []
        nestedNegation count = iterate CNeg trigger !! count
    -- One negation may remain directly on an atom, so N wrappers require
    -- N - 1 Step-4 rewrites.
    normalizeDetailed (conditionProgram (nestedNegation (maxNormalizationRounds + 1)))
      `shouldSatisfy` isRight
    normalizeDetailed (conditionProgram (nestedNegation (maxNormalizationRounds + 2)))
      `shouldSatisfy` isLeft

  it "normalizes programs with negation" $ do
    let np = parseAndNormalize "~a => b."
    length np `shouldSatisfy` (>= 1)
    -- The negated condition should be ncNegated = True
    let hasNeg = any (\r -> any ncNegated (nrConditions r)) np
    hasNeg `shouldBe` True

  it "rejects term-level @ without a pattern-function occurrence" $ do
    case parseProgram "<test>" "p(@X).\n" of
      Left err -> expectationFailure (show err)
      Right prog -> normalize prog `shouldSatisfy` isLeft

  it "handles pattern function first substep" $ do
    let np = parseAndNormalize "append([], X) -> X.\n"
    -- Should produce append([], X, X) as a fact
    let appendRules = filter (\r -> let Atom n _ = nrHead r in n == "append") np
    length appendRules `shouldSatisfy` (>= 1)

  it "produces only normal-form rules" $ do
    let np = parseAndNormalize "device(heater).\ndevice(X) /\\ hot(X) => off(X).\ndevice(X) /\\ ~hot(X) => on(X).\n@on(X) /\\ hot(X) => warning(X).\n"
    -- All rules should have NormalCond with proper structure
    let allNormal = all (\r -> all (\c -> ncPrevDepth c >= 0) (nrConditions r)) np
    allNormal `shouldBe` True

  it "normalizes temporal operators exposed inside nested conjunctions" $ do
    let np = parseAndNormalize "#(a /\\ (b since c)) => result."
    np `shouldSatisfy` (not . null)

  it "pushes negation inside conjunctions exposed by temporal expansion" $ do
    let np = parseAndNormalize "#(~(a /\\ b) /\\ c) => result."
    np `shouldSatisfy` (not . null)

interpreterSpec :: Spec
interpreterSpec = describe "Interpreter" $ do
  it "empty program produces empty worlds" $ do
    let st = unsafeStep (newInterpreterState [] Set.empty)
    case currentWorld st of
      Just w -> Set.filter (not . isInternal) (worldToSet w) `shouldBe` Set.empty
      Nothing -> expectationFailure "No world"

  it "derives facts from simple rules" $ do
    let st = runWithAssertions "hot(X) => off(X)." [(0, ["hot(heater)"])] 1
    worldContains st "off(heater)" `shouldBe` True

  it "handles negation-as-failure" $ do
    let st = runWithAssertions "device(heater).\ndevice(X) /\\ ~hot(X) => on(X)." [(0, ["hot(heater)"])] 1
    -- hot(heater) is asserted, so ~hot(heater) fails, on(heater) not derived
    worldContains st "on(heater)" `shouldBe` False

  it "foot warmer example" $ do
    let prog = "device(heater).\ndevice(X) /\\ hot(X) => off(X).\ndevice(X) /\\ ~hot(X) => on(X).\n"
    -- World 0 with hot(heater)
    let st1 = runWithAssertions prog [(0, ["hot(heater)"])] 1
    worldContains st1 "off(heater)" `shouldBe` True
    worldContains st1 "on(heater)" `shouldBe` False
    worldContains st1 "device(heater)" `shouldBe` True
    -- World 1 without assertion: device(X) binds X=heater, ~hot(heater)
    -- succeeds (ground negation), so on(heater) is derived.
    let st2 = unsafeStep st1
    worldContains st2 "on(heater)" `shouldBe` True
    worldContains st2 "off(heater)" `shouldBe` False
    worldContains st2 "device(heater)" `shouldBe` True

  it "foot warmer example with ground negation" $ do
    -- Use ground negation to avoid the free variable issue
    let prog = "hot(heater) => off(heater).\n~hot(heater) => on(heater).\n"
    let st1 = runWithAssertions prog [(0, ["hot(heater)"])] 1
    worldContains st1 "off(heater)" `shouldBe` True
    worldContains st1 "on(heater)" `shouldBe` False
    -- World 1 without assertion: ~hot(heater) succeeds (ground), on(heater) derived
    let st2 = unsafeStep st1
    worldContains st2 "on(heater)" `shouldBe` True
    worldContains st2 "off(heater)" `shouldBe` False

  it "handles @-conditions (previous world)" $ do
    let prog = "@on(X) /\\ hot(X) => warning(X).\non(X) => on(X).\n"
    let st1 = runWithAssertions prog [(0, ["on(heater)"])] 1
    -- World 0: on(heater) is asserted, but @on(heater) fails (no previous world)
    worldContains st1 "warning(heater)" `shouldBe` False
    -- World 1: assert hot(heater), @on(heater) should succeed
    let st2 = assertFact (Atom "hot" [TFun "heater" []]) st1
        st3 = unsafeStep st2
    worldContains st3 "warning(heater)" `shouldBe` True

  it "world 0 @-conditions fail" $ do
    let prog = "@p => q.\n"
    let st = runWithAssertions prog [(0, ["p"])] 1
    -- @p at world 0 should fail
    worldContains st "q" `shouldBe` False

  it "distinguishes @~p from ~@p at world 0" $ do
    let innerNeg = runWithAssertions "@~p => inner_neg.\n" [] 1
        outerNeg = runWithAssertions "~@p => outer_neg.\n" [] 1
    -- Section 5.2 defines @F as false at world 0 for every F.
    worldContains innerNeg "inner_neg" `shouldBe` False
    -- Step 4 preserves the outer negation with an auxiliary predicate.
    worldContains outerNeg "outer_neg" `shouldBe` True

  it "evaluates @~p normally once the previous world exists" $ do
    let st = runWithAssertions "@~p => absent_before.\n" [] 2
    worldContains st "absent_before" `shouldBe` True

  it "does not capture surrounding variables in has-been auxiliaries" $ do
    let prog = "#ready /\\ item(X) => result(X).\n"
        st = runWithAssertions prog [(0, ["ready", "item(a)"])] 1
    worldContains st "result(a)" `shouldBe` True

  it "mutual exclusion" $ do
    let prog = unlines
          [ "assign(X) /\\ @assigned_to(X) => assigned_to(X)."
          , "assign(1) /\\ ~@assigned_to_something => assigned_to(1)."
          , "assign(2) /\\ ~assign(1) /\\ ~@assigned_to_something => assigned_to(2)."
          , "assigned_to(X) => assigned_to_something."
          ]
    let st = runWithAssertions prog [(0, ["assign(1)", "assign(2)"])] 1
    -- Only 1 should be assigned (1 has priority)
    worldContains st "assigned_to(1)" `shouldBe` True
    worldContains st "assigned_to(2)" `shouldBe` False

  it "handles multiple steps" $ do
    let prog = "@p => q.\nq => r.\n"
    let st1 = runWithAssertions prog [(0, ["p"])] 1
    -- World 0: p is asserted. @p fails. No q or r.
    worldContains st1 "q" `shouldBe` False
    -- World 1: @p succeeds. q derived. r derived.
    let st2 = unsafeStep st1
    worldContains st2 "q" `shouldBe` True
    worldContains st2 "r" `shouldBe` True

  it "handles numeric comparisons" $ do
    let prog = "temp(X) /\\ X > 100 => alarm.\n"
    let st = runWithAssertions prog [(0, ["temp(150)"])] 1
    worldContains st "alarm" `shouldBe` True

  it "handles numeric comparison - no alarm" $ do
    let prog = "temp(X) /\\ X > 100 => alarm.\n"
    let st = runWithAssertions prog [(0, ["temp(50)"])] 1
    worldContains st "alarm" `shouldBe` False

unificationSpec :: Spec
unificationSpec = describe "Unification" $ do
  it "unifies identical terms" $ do
    unifyTerm (TFun "a" []) (TFun "a" []) `shouldBe` Just emptySubst

  it "unifies variable with term" $ do
    unifyTerm (TVar "X") (TFun "a" []) `shouldBe` Just (Map.singleton "X" (TFun "a" []))

  it "fails on different functors" $ do
    unifyTerm (TFun "a" []) (TFun "b" []) `shouldBe` Nothing

  it "unifies nested terms" $ do
    let t1 = TFun "f" [TVar "X", TFun "b" []]
        t2 = TFun "f" [TFun "a" [], TFun "b" []]
    unifyTerm t1 t2 `shouldBe` Just (Map.singleton "X" (TFun "a" []))

  it "occurs check prevents infinite terms" $ do
    unifyTerm (TVar "X") (TFun "f" [TVar "X"]) `shouldBe` Nothing

  it "matches atoms" $ do
    let pat = Atom "p" [TVar "X"]
        ground = Atom "p" [TFun "a" []]
    matchAtom pat ground `shouldBe` Just (Map.singleton "X" (TFun "a" []))

  it "fails to match different predicates" $ do
    matchAtom (Atom "p" []) (Atom "q" []) `shouldBe` Nothing

-- ============================================================
-- F. Eventually and Next operators
-- ============================================================

eventuallyNextSpec :: Spec
eventuallyNextSpec = describe "Eventually and Next operators" $ do
  it "eventually p => q: assert p at world 0, q appears and persists" $ do
    let prog = "eventually p => q.\nq => q.\n"
    let st = runWithAssertions prog [(0, ["p"])] 1
    worldContains st "q" `shouldBe` True
    -- q persists to the next world via q => q
    let st2 = unsafeStep st
    worldContains st2 "q" `shouldBe` True

  it "a => next b: b absent at world 0, present at world 1" $ do
    let prog = "a => next b.\n"
    let st = runWithAssertions prog [(0, ["a"])] 1
    -- At world 0, b should not be derived (it is deferred to next)
    worldContains st "b" `shouldBe` False
    -- At world 1, b should appear
    let st2 = unsafeStep st
    worldContains st2 "b" `shouldBe` True

  it "a => next (next b): b appears at world 2" $ do
    let prog = "a => next next b.\n"
    let st0 = runWithAssertions prog [(0, ["a"])] 1
    worldContains st0 "b" `shouldBe` False
    let st1 = unsafeStep st0
    worldContains st1 "b" `shouldBe` False
    let st2 = unsafeStep st1
    worldContains st2 "b" `shouldBe` True

  it "eventually p /\\ q => r: combined condition" $ do
    let prog = "eventually p /\\ q => r.\n"
    let st = runWithAssertions prog [(0, ["p", "q"])] 1
    worldContains st "r" `shouldBe` True

-- ============================================================
-- G. Pattern function expansion
-- ============================================================

patternFunctionSpec :: Spec
patternFunctionSpec = describe "Pattern function expansion" $ do
  it "ground wrap: wrap(hello) -> box(hello). result(wrap(hello))." $ do
    -- The ground call supplies the clause input and produces a ground result.
    let prog = "wrap(hello) -> box(hello).\nresult(wrap(hello)).\n"
    let st = runWithAssertions prog [] 1
    worldContains st "result(box(hello))" `shouldBe` True

  it "pattern function normalizes to predicate with extra arg" $ do
    -- wrap(X) -> box(X) becomes the fact wrap(X, box(X))
    let np = parseAndNormalize "wrap(X) -> box(X).\n"
    let wrapRules = filter (\r -> let Atom n _ = nrHead r in n == "wrap") np
    length wrapRules `shouldSatisfy` (>= 1)
    let NormalRule _ (Atom _ args) = head wrapRules
    length args `shouldBe` 2

  it "normalizes and executes a conditional pattern-function reduction" $ do
    let prog = unlines
          [ "enabled(X) => choose(X) -> selected."
          , "request(X) /\\ choose(X) = Y => result(Y)."
          ]
        (np, pfNames) = parseAndNormalizeWithPF prog
        chooseRules =
          [ r | r@(NormalRule _ (Atom "choose" _)) <- np ]
        st = runWithAssertions prog
          [(0, ["enabled(a)", "request(a)"])] 1
    Set.member "choose" pfNames `shouldBe` True
    chooseRules `shouldSatisfy` (not . null)
    worldContains st "result(selected)" `shouldBe` True

  it "makes @~ false at world 0 inside conditional pattern functions" $ do
    let prog = unlines
          [ "@~blocked(X) => choose(X) -> selected."
          , "request(X) /\\ choose(X) = Y => result(Y)."
          ]
        st0 = runWithAssertions prog [(0, ["request(a)"])] 1
        st1 = unsafeStep (assertFact (Atom "request" [TFun "a" []]) st0)
    worldContains st0 "result(selected)" `shouldBe` False
    worldContains st1 "result(selected)" `shouldBe` True

-- ============================================================
-- H. Unification = and at(X)
-- ============================================================

unificationEqualitySpec :: Spec
unificationEqualitySpec = describe "Unification = and at(X)" $ do
  it "p(X) /\\ X = hello => q(X): with p(hello), derives q(hello)" $ do
    let prog = "p(X) /\\ X = hello => q(X).\n"
    let st = runWithAssertions prog [(0, ["p(hello)"])] 1
    worldContains st "q(hello)" `shouldBe` True

  it "a = b => never: unification failure on distinct ground terms" $ do
    let prog = "a = b => never.\n"
    let st = runWithAssertions prog [] 1
    worldContains st "never" `shouldBe` False

  it "at(N) /\\ N > 3 => late: late appears at world 4+" $ do
    let prog = "at(N) /\\ N > 3 => late.\n"
    let st = runWithAssertions prog [] 5
    -- After 5 steps we are at world 4 (0..4)
    worldContains st "late" `shouldBe` True
    -- Check that world 3 does NOT have late
    let history = getHistory st
        world3 = history !! 3
        lateAtom = case parseAtom "<test>" "late" of
                     Right a -> a
                     Left _ -> error "bad parse"
    worldMember lateAtom world3 `shouldBe` False

  it "at(N) respects @-depth" $ do
    -- @at(N) at world 2 should give N=1 (previous world number)
    let prog = "@at(N) /\\ N = 1 => prev_was_one."
    let np = parseAndNormalize prog
    let st = unsafeStepN 3 (newInterpreterState np Set.empty)
    worldContains st "prev_was_one" `shouldBe` True

  it "at(N) at depth 0 still works" $ do
    let prog = "at(N) /\\ N = 2 => is_world_two."
    let np = parseAndNormalize prog
    let st = unsafeStepN 3 (newInterpreterState np Set.empty)
    worldContains st "is_world_two" `shouldBe` True

  it "@@at(N) gives world number minus 2" $ do
    let prog = "@@at(N) /\\ N = 1 => two_back_was_one."
    let np = parseAndNormalize prog
    let st = unsafeStepN 4 (newInterpreterState np Set.empty)
    worldContains st "two_back_was_one" `shouldBe` True

-- ============================================================
-- I. Stratification
-- ============================================================

stratificationSpec :: Spec
stratificationSpec = describe "Condition 1 and general minimal models" $ do
  it "executes a finite negative self-cycle by its minimal model" $ do
    let np = parseAndNormalize "~a => a.\n"
        st = unsafeStep (newInterpreterState np Set.empty)
    worldContains st "a" `shouldBe` True

  it "exposes every incomparable minimal model" $ do
    let np = parseAndNormalize "~a => b.\n~b => a.\n"
    case stepWorldAll (newInterpreterState np Set.empty) of
      Left err -> expectationFailure err
      Right states -> do
        length states `shouldBe` 2
        map (\st -> (worldContains st "a", worldContains st "b")) states
          `shouldMatchList` [(True, False), (False, True)]

  it "exposes the third minimal model overlooked in paper section 4.7" $ do
    let prog = unlines
          [ "assign(X) /\\ ~assigned_to_another(X) => assigned_to(X)."
          , "assigned_to(X) /\\ assign(Y) /\\ X != Y => assigned_to_another(Y)."
          ]
        (np, pfNames) = parseAndNormalizeWithPF prog
        st0 = assertFact (Atom "assign" [TFun "1" []])
            $ assertFact (Atom "assign" [TFun "2" []])
            $ newInterpreterState np pfNames
    case stepWorldAll st0 of
      Left err -> expectationFailure err
      Right states -> do
        length states `shouldBe` 3
        map (\st -> (worldContains st "assigned_to(1)",
                     worldContains st "assigned_to(2)")) states
          `shouldMatchList` [(True, False), (False, True), (False, False)]

  it "a corrected two-process choice has exactly two minimal worlds" $ do
    let prog =
          "assign(X) /\\ assign(Y) /\\ X != Y /\\ ~assigned_to(Y) => assigned_to(X).\n"
        (np, pfNames) = parseAndNormalizeWithPF prog
        st0 = assertFact (Atom "assign" [TFun "1" []])
            $ assertFact (Atom "assign" [TFun "2" []])
            $ newInterpreterState np pfNames
    case stepWorldAll st0 of
      Left err -> expectationFailure err
      Right states -> do
        length states `shouldBe` 2
        map (\st -> (worldContains st "assigned_to(1)",
                     worldContains st "assigned_to(2)")) states
          `shouldMatchList` [(True, False), (False, True)]

  it "general and fast evaluators agree on condition-1 programs" $ do
    let np = parseAndNormalize "seed(X) => p(X).\np(X) /\\ ~blocked(X) => q(X).\n"
        st0 = assertFact (Atom "seed" [TFun "a" []])
            $ newInterpreterState np Set.empty
    case (stepWorldStratified st0, stepWorldGeneralAll st0) of
      (Right fast, Right [general]) -> currentWorld fast `shouldBe` currentWorld general
      (Left err, _) -> expectationFailure err
      (_, Left err) -> expectationFailure err
      (_, Right states) -> expectationFailure $ "expected one general model, got " ++ show (length states)

  it "@~a => b: @ excludes from dependency graph but is false at world 0" $ do
    let prog = "@~a => b.\n"
    let st = runWithAssertions prog [] 1
    worldContains st "b" `shouldBe` False

-- ============================================================
-- J. Safety validation
-- ============================================================

safetyValidationSpec :: Spec
safetyValidationSpec = describe "Safety validation" $ do
  it "~p(X) => q(X) normalizes (warns about X)" $ do
    let (np, warnings) = normalizeWithWarnings "~p(X) => q(X).\n"
    length np `shouldSatisfy` (>= 1)
    length warnings `shouldSatisfy` (>= 1)

  it "r(X) /\\ ~p(X) => q(X) normalizes without warnings" $ do
    let (np, warnings) = normalizeWithWarnings "r(X) /\\ ~p(X) => q(X).\n"
    length np `shouldSatisfy` (>= 1)
    warnings `shouldBe` []

  it "warns about unbound variables in previous-world negation" $ do
    let (_, warnings) = normalizeWithWarnings "@~p(X) => q(X).\n"
    warnings `shouldSatisfy` (not . null)

  it "rejects an unsafe forward rule when execution begins" $ do
    let np = parseAndNormalize "~p(X) => q(X).\n"
    stepWorld (newInterpreterState np Set.empty) `shouldSatisfy` isLeft

  it "rejects a pattern-function call whose inputs are not grounded" $ do
    let (np, pfNames) = parseAndNormalizeWithPF $ unlines
          [ "identity(X) -> X."
          , "identity(X) = a => leaked."
          ]
    stepWorld (newInterpreterState np pfNames) `shouldSatisfy` isLeft

  it "rejects a pattern-function clause with an ungrounded output" $ do
    let (np, pfNames) = parseAndNormalizeWithPF $ unlines
          [ "wild(X) -> Y."
          , "result(wild(a))."
          ]
    stepWorld (newInterpreterState np pfNames) `shouldSatisfy` isLeft

  it "accepts a pattern-function output grounded by a positive condition" $ do
    let st = runWithAssertions (unlines
          [ "value(a)."
          , "value(Y) => choose(X) -> Y."
          , "result(choose(key))."
          ]) [] 1
    worldContains st "result(a)" `shouldBe` True

-- ============================================================
-- K-M. Edge cases
-- ============================================================

edgeCaseSpec :: Spec
edgeCaseSpec = describe "Edge cases" $ do
  it "deep @-nesting: @@@@p => q has ncPrevDepth == 4" $ do
    let np = parseAndNormalize "@@@@p => q.\n"
    let depths = [ncPrevDepth c | r <- np, c <- nrConditions r, let Atom n _ = ncAtom c, n == "p"]
    depths `shouldContain` [4]

  it "Unicode negation: parseCond \\x00ACp succeeds" $ do
    parseCond "<test>" "\x00ACp" `shouldSatisfy` isRight

  it "bare fact: p. derives p" $ do
    let st = runWithAssertions "p.\n" [] 1
    worldContains st "p" `shouldBe` True

  it "rejects non-ground assertions and negative step counts" $ do
    let st = newInterpreterState [] Set.empty
        nonGround = Atom "p" [TVar "X"]
        builtin = Atom "at" [TFun "99" []]
    assertFactEither nonGround st `shouldSatisfy` isLeft
    stepWorld (assertFact nonGround st) `shouldSatisfy` isLeft
    assertFactEither builtin st `shouldSatisfy` isLeft
    stepWorld (assertFact builtin st) `shouldSatisfy` isLeft
    stepWorldN (-1) st `shouldSatisfy` isLeft

  it "world history length after 3 steps" $ do
    let st0 = newInterpreterState [] Set.empty
        st3 = unsafeStepN 3 st0
    length (getHistory st3) `shouldBe` 3
    getWorldNumber st3 `shouldBe` Just 2

  it "self-unification: p(X) /\\ X = X => q(X) with p(a) derives q(a)" $ do
    let prog = "p(X) /\\ X = X => q(X).\n"
    let st = runWithAssertions prog [(0, ["p(a)"])] 1
    worldContains st "q(a)" `shouldBe` True

-- ============================================================
-- Runtime query and input boundaries
-- ============================================================

runtimeBoundarySpec :: Spec
runtimeBoundarySpec = describe "Runtime query and input validation" $ do
  it "evaluates external predicates through the public query API" $ do
    let state = unsafeStep (newInterpreterState [] Set.empty)
        integer value = TFun value []
    queryAtomEither (Atom "=" [integer "1", integer "1"]) state
      `shouldBe` Right [Map.empty]
    queryAtomEither (Atom "<" [integer "1", integer "2"]) state
      `shouldBe` Right [Map.empty]
    queryAtomEither
      (Atom "is" [TVar "X", TFun "+" [integer "2", integer "3"]]) state
      `shouldBe` Right [Map.singleton "X" (integer "5")]
    queryAtomEither (Atom "at" [TVar "N"]) state
      `shouldBe` Right [Map.singleton "N" (integer "0")]
    queryAtomEither (Atom "true" []) state `shouldBe` Right [Map.empty]
    queryAtomEither (Atom "false" []) state `shouldBe` Right []

  it "requires public pattern-function query inputs to be ground" $ do
    let (program, pfNames) = parseAndNormalizeWithPF "identity(X) -> X."
        state = newInterpreterState program pfNames
    queryAtomEither (Atom "identity" [TVar "X", TVar "Y"]) state
      `shouldSatisfy` isLeft
    queryAtomEither (Atom "identity" [TFun "a" [], TVar "Y"]) state
      `shouldSatisfy` isRight

  it "rejects malformed runtime queries instead of treating them as false" $ do
    let (program, pfNames) = parseAndNormalizeWithPF
          "lookup(X) -> X. present(key)."
        state = newInterpreterState program pfNames
    queryAtomEither (Atom "at" [TFun "0" [], TFun "1" []]) state
      `shouldSatisfy` isLeft
    queryAtomEither (Atom "present" []) state `shouldSatisfy` isLeft
    queryAtomEither
      (Atom "present" [TFun "key" [TFun "a" []]]) state
      `shouldSatisfy` isLeft
    queryAtomEither
      (Atom "present" [TPrev (TFun "key" [])]) state
      `shouldSatisfy` isLeft

  it "rejects predicate and constructor signature changes in assertions" $ do
    let predicateProgram = parseAndNormalize "p."
        predicateState = newInterpreterState predicateProgram Set.empty
        wrongPredicate = Atom "p" [TFun "a" []]
        constructorProgram = parseAndNormalize "value(box)."
        constructorState = newInterpreterState constructorProgram Set.empty
        wrongConstructor = Atom "value" [TFun "box" [TFun "a" []]]
    assertFactEither wrongPredicate predicateState `shouldSatisfy` isLeft
    stepWorld (assertFact wrongPredicate predicateState) `shouldSatisfy` isLeft
    assertFactEither wrongConstructor constructorState `shouldSatisfy` isLeft
    stepWorld (assertFact wrongConstructor constructorState) `shouldSatisfy` isLeft

  it "keeps dynamically introduced signatures fixed across pending and past inputs" $ do
    let emptyState = newInterpreterState [] Set.empty
        event0 = Atom "event" []
        event1 = Atom "event" [TFun "a" []]
        pendingAssertions = assertFact event0 emptyState
        firstWorld = unsafeStep pendingAssertions
    assertFactEither event1 pendingAssertions `shouldSatisfy` isLeft
    assertFactEither event1 firstWorld `shouldSatisfy` isLeft
    stepWorld (assertFact event1 firstWorld) `shouldSatisfy` isLeft

  it "rejects pattern-function and generated predicates as asserted facts" $ do
    let (pfProgram, pfNames) = parseAndNormalizeWithPF "lookup(X) -> X."
        pfState = newInterpreterState pfProgram pfNames
        pfAtom = Atom "lookup" [TFun "a" [], TFun "a" []]
    assertFactEither pfAtom pfState `shouldSatisfy` isLeft
    stepWorld (assertFact pfAtom pfState) `shouldSatisfy` isLeft
    case compileDetailedSource "trigger => next fired." of
      Left err -> expectationFailure err
      Right normalized -> do
        let state = newInterpreterStateWithAuxiliaries
              (normalizedProgram normalized)
              (normalizedPatternFunctions normalized)
              (normalizedAuxiliaryPredicates normalized)
            generated = Set.findMin (normalizedAuxiliaryPredicates normalized)
            atom = Atom generated []
        assertFactEither atom state `shouldSatisfy` isLeft
        stepWorld (assertFact atom state) `shouldSatisfy` isLeft
        queryAtomEither atom state `shouldSatisfy` isLeft

  it "rejects term-level previous and malformed arithmetic in assertions" $ do
    let state = newInterpreterState [] Set.empty
    assertFactEither (Atom "p" [TPrev (TFun "a" [])]) state
      `shouldSatisfy` isLeft
    assertFactEither (Atom "p" [TFun "div" [TFun "1" []]]) state
      `shouldSatisfy` isLeft

-- ============================================================
-- N. Term-level previous values in pattern-function expansion
-- ============================================================

mixedTPrevSpec :: Spec
mixedTPrevSpec = describe "Term-level previous pattern-function values" $ do
  it "moves @ from a pattern-function value to the generated PF condition" $ do
    let np = parseAndNormalize $ unlines
          [ "lookup(key) -> value."
          , "present(@lookup(key)) => found."
          ]
        foundRuleConds =
          [ cs | NormalRule cs (Atom "found" []) <- np ]
    foundRuleConds `shouldSatisfy` any
      (elem (NormalCond 0 False (Atom "present" [TVar "V_aux0"])))
    foundRuleConds `shouldSatisfy` any
      (elem (NormalCond 1 False
        (Atom "lookup" [TFun "key" [], TVar "V_aux0"])))

  it "uses the enclosing predicate in the current world" $ do
    let prog = unlines
          [ "lookup(key) -> value."
          , "present(@lookup(key)) => found."
          ]
        st = runWithAssertions prog [(1, ["present(value)"])] 2
    -- The generated lookup condition is previous-time; present(value) is not.
    worldContains st "found" `shouldBe` True

-- ============================================================
-- O. Backward chaining for pattern functions
-- ============================================================

backwardChainingSpec :: Spec
backwardChainingSpec = describe "Backward chaining for pattern functions" $ do
  it "append base case: append([], [1,2], X) yields X=[1,2]" $ do
    let prog = unlines
          [ "append([], X) -> X."
          , "items([1, 2])."
          , "items(X) /\\ append([], X) = Y => result(Y)."
          ]
    let st = runWithAssertions prog [] 1
    worldContains st "result([1, 2])" `shouldBe` True

  it "recursive append: append([1], [2, 3], X) yields X=[1,2,3]" $ do
    let prog = unlines
          [ "append([], X) -> X."
          , "append([H|T], Y) -> [H|append(T, Y)]."
          , "a([1])."
          , "b([2, 3])."
          , "a(X) /\\ b(Y) /\\ append(X, Y) = Z => result(Z)."
          ]
    let st = runWithAssertions prog [] 1
    worldContains st "result([1, 2, 3])" `shouldBe` True

  it "full append: [1,2,3] ++ [4,5] = [1,2,3,4,5]" $ do
    let prog = unlines
          [ "append([], X) -> X."
          , "append([H|T], Y) -> [H|append(T, Y)]."
          , "a([1, 2, 3])."
          , "b([4, 5])."
          , "a(X) /\\ b(Y) /\\ append(X, Y) = Z => combined(Z)."
          ]
    let st = runWithAssertions prog [] 1
    worldContains st "combined([1, 2, 3, 4, 5])" `shouldBe` True

  it "append used directly in rule head" $ do
    let prog = unlines
          [ "append([], X) -> X."
          , "append([H|T], Y) -> [H|append(T, Y)]."
          , "a([1, 2])."
          , "b([3])."
          , "a(X) /\\ b(Y) => combined(append(X, Y))."
          ]
    let st = runWithAssertions prog [] 1
    worldContains st "combined([1, 2, 3])" `shouldBe` True

  it "negation with PF: ~append([], [1], [99]) succeeds (false PF result)" $ do
    let prog = unlines
          [ "append([], X) -> X."
          , "marker."
          , "marker /\\ ~append([], [1], [99]) => not_match."
          ]
    let st = runWithAssertions prog [] 1
    worldContains st "not_match" `shouldBe` True

  it "negation with PF: ~append([], [1], [1]) fails (true PF result)" $ do
    let prog = unlines
          [ "append([], X) -> X."
          , "marker."
          , "marker /\\ ~append([], [1], [1]) => should_not_derive."
          ]
    let st = runWithAssertions prog [] 1
    worldContains st "should_not_derive" `shouldBe` False

  it "queryAtom works for PF predicates" $ do
    let prog = unlines
          [ "append([], X) -> X."
          , "append([H|T], Y) -> [H|append(T, Y)]."
          ]
    let (np, pfNames) = parseAndNormalizeWithPF prog
        st = unsafeStep (newInterpreterState np pfNames)
        results = queryAtom (Atom "append" [TFun "." [TFun "1" [], TFun "[]" []], TFun "." [TFun "2" [], TFun "[]" []], TVar "Z"]) st
    length results `shouldSatisfy` (> 0)
    -- Z should be bound to [1, 2]
    let expected = TFun "." [TFun "1" [], TFun "." [TFun "2" [], TFun "[]" []]]
    map (\s -> Map.lookup "Z" s) results `shouldContain` [Just expected]

  it "reports the depth limit as a resource error" $ do
    -- loop(X) -> loop(X) would recurse forever without depth limit
    let prog = unlines
          [ "loop(X) -> loop(X)."
          , "start(a)."
          , "start(X) /\\ loop(X) = Y => result(Y)."
          ]
    let (np, pfNames) = parseAndNormalizeWithPF prog
    stepWorld (newInterpreterState np pfNames) `shouldSatisfy` isLeft
    queryAtomEither (Atom "loop" [TFun "a" [], TVar "Y"])
      (newInterpreterState np pfNames) `shouldSatisfy` isLeft

-- ============================================================
-- P. Bug fix regression tests
-- ============================================================

correctnessAndFeatureSpec :: Spec
correctnessAndFeatureSpec = describe "Temporal operator semantics, parser extensions, and unification" $ do
  -- Fix 1: always with conditions captures condition variables
  it "conditional always: c(X) => always r(X) persists correctly" $ do
    let prog = unlines
          [ "c(X) => always r(X)."
          ]
    let st1 = runWithAssertions prog [(0, ["c(a)"])] 1
    worldContains st1 "r(a)" `shouldBe` True
    -- r(a) should persist even without c(a) in future worlds
    let st2 = unsafeStep st1
    worldContains st2 "r(a)" `shouldBe` True
    let st3 = unsafeStep st2
    worldContains st3 "r(a)" `shouldBe` True

  -- Fix 2: Fact (RUntil q a) — unconditional until holds whenever condition is false
  it "fact until: q until a holds when a is absent, stops when a is present" $ do
    let prog = unlines
          [ "q until trigger."
          ]
    -- World 0: no trigger, q should hold
    let st0 = runWithAssertions prog [] 1
    worldContains st0 "q" `shouldBe` True
    -- World 1: assert trigger, q should stop
    let st1 = assertFact (Atom "trigger" []) st0
        st2 = unsafeStep st1
    worldContains st2 "q" `shouldBe` False
    -- World 2: trigger gone, q resumes (unconditional until = ~trigger => q)
    let st3 = unsafeStep st2
    worldContains st3 "q" `shouldBe` True

  -- Conditional until has proper state tracking
  it "conditional until: c => q until a uses persistence auxiliary" $ do
    let prog = unlines
          [ "c => q until trigger."
          ]
    -- World 0: c holds, q should derive (no trigger)
    let st0 = runWithAssertions prog [(0, ["c"])] 1
    worldContains st0 "q" `shouldBe` True
    -- World 1: no c, no trigger — q persists via auxiliary
    let st1 = unsafeStep st0
    worldContains st1 "q" `shouldBe` True
    -- World 2: assert trigger — q stops
    let st2 = assertFact (Atom "trigger" []) st1
        st3 = unsafeStep st2
    worldContains st3 "q" `shouldBe` False

  -- Fix 3: Fact (RAtNext q a) now works instead of silently failing
  it "fact atnext: q atnext trigger fires when trigger appears" $ do
    let prog = unlines
          [ "q atnext trigger."
          ]
    -- World 0: no trigger, q should not fire
    let st0 = runWithAssertions prog [] 1
    worldContains st0 "q" `shouldBe` False
    -- World 1: assert trigger, q should fire
    let st1 = assertFact (Atom "trigger" []) st0
        st2 = unsafeStep st1
    worldContains st2 "q" `shouldBe` True

  -- Fix 5: @ depth in backward chaining
  it "pattern function with @-depth condition in BC" $ do
    let prog = unlines
          [ "lookup(key) -> val."
          , "marker."
          , "marker /\\ @lookup(key) = X => found(X)."
          ]
    let st0 = runWithAssertions prog [] 1
    -- World 0: lookup(key) = val works, @lookup requires previous world
    -- World 1: @lookup should resolve against world 0
    let st1 = unsafeStep st0
    worldContains st1 "found(val)" `shouldBe` True

  -- Fix 9: negative number literals
  it "parses negative number literals" $ do
    parseTerm "<test>" "-3" `shouldBe` Right (TFun "-3" [])
    parseTerm "<test>" "-42" `shouldBe` Right (TFun "-42" [])

  it "negative numbers in comparisons" $ do
    let prog = "temp(X) /\\ X < 0 => freezing.\n"
    let st = runWithAssertions prog [(0, ["temp(-5)"])] 1
    worldContains st "freezing" `shouldBe` True

  -- Fix 10: != operator
  it "parses != as not-equal" $ do
    parseCond "<test>" "X != Y" `shouldSatisfy` isRight

  it "!= works in rules" $ do
    let prog = unlines
          [ "p(a)."
          , "p(b)."
          , "p(X) /\\ X != a => not_a(X)."
          ]
    let st = runWithAssertions prog [] 1
    worldContains st "not_a(b)" `shouldBe` True
    worldContains st "not_a(a)" `shouldBe` False

  -- matchAtom consistency for repeated variables
  it "matchAtom rejects inconsistent bindings for p(X, X)" $ do
    let pat = Atom "p" [TVar "X", TVar "X"]
        ground1 = Atom "p" [TFun "a" [], TFun "a" []]
        ground2 = Atom "p" [TFun "a" [], TFun "b" []]
    matchAtom pat ground1 `shouldBe` Just (Map.singleton "X" (TFun "a" []))
    matchAtom pat ground2 `shouldBe` Nothing

  -- Arithmetic evaluation
  it "X is 2 + 3 evaluates to 5" $ do
    let prog = "p(X) /\\ X is 2 + 3 => q(X).\n"
    let st = runWithAssertions prog [(0, ["p(5)"])] 1
    worldContains st "q(5)" `shouldBe` True

  it "X is 2 + 3 fails for wrong value" $ do
    let prog = "p(X) /\\ X is 2 + 3 => q(X).\n"
    let st = runWithAssertions prog [(0, ["p(4)"])] 1
    worldContains st "q(4)" `shouldBe` False

  it "arithmetic with variables: X is Y + 1" $ do
    let prog = "val(X) /\\ Y is X + 1 => next_val(Y).\n"
    let st = runWithAssertions prog [(0, ["val(5)"])] 1
    worldContains st "next_val(6)" `shouldBe` True

  it "arithmetic: multiplication" $ do
    let prog = "val(X) /\\ Y is X * 3 => triple(Y).\n"
    let st = runWithAssertions prog [(0, ["val(4)"])] 1
    worldContains st "triple(12)" `shouldBe` True

  it "arithmetic: nested expressions X is (2 + 3) * 4" $ do
    let prog = "Y is (2 + 3) * 4 => result(Y).\n"
    let st = runWithAssertions prog [] 1
    worldContains st "result(20)" `shouldBe` True

  it "arithmetic: subtraction" $ do
    let prog = "Y is 10 - 3 => result(Y).\n"
    let st = runWithAssertions prog [] 1
    worldContains st "result(7)" `shouldBe` True

  it "arithmetic: div and mod" $ do
    let prog = "Y is div(10, 3) => result(Y).\n"
    let st = runWithAssertions prog [] 1
    worldContains st "result(3)" `shouldBe` True

  it "uses arbitrary-precision floor division and modulo" $ do
    let prog = unlines
          [ "Q1 is -7 div 3 => q1(Q1)."
          , "R1 is -7 mod 3 => r1(R1)."
          , "Q2 is 7 div -3 => q2(Q2)."
          , "R2 is 7 mod -3 => r2(R2)."
          , "Huge is 9223372036854775808 * 9223372036854775808 => huge(Huge)."
          ]
        st = runWithAssertions prog [] 1
    worldContains st "q1(-3)" `shouldBe` True
    worldContains st "r1(2)" `shouldBe` True
    worldContains st "q2(-3)" `shouldBe` True
    worldContains st "r2(-2)" `shouldBe` True
    worldContains st "huge(85070591730234615865843651857942052864)"
      `shouldBe` True

  it "treats invalid arithmetic as built-in failure" $ do
    let prog = unlines
          [ "Bad is 1 div 0 => division_by_zero_succeeded(Bad)."
          , "Bad is not_an_integer + 1 => non_integer_succeeded(Bad)."
          ]
        st = runWithAssertions prog [] 1
    let hasPredicate name = maybe False
          (worldMatches (Atom name [TVar "X"]))
          (currentWorld st)
    hasPredicate "division_by_zero_succeeded" `shouldBe` False
    hasPredicate "non_integer_succeeded" `shouldBe` False

  it "comparisons evaluate arithmetic: X + 1 > 5" $ do
    let prog = "val(X) /\\ X + 1 > 5 => big(X).\n"
    let st = runWithAssertions prog [(0, ["val(5)", "val(3)"])] 1
    worldContains st "big(5)" `shouldBe` True
    worldContains st "big(3)" `shouldBe` False

  -- Precedence: since/after lower than /\
  it "a /\\ b since c parses as (a /\\ b) since c" $ do
    case parseCond "<test>" "a /\\ b since c" of
      Right (CSince (CAnd [CAtom (Atom "a" []), CAtom (Atom "b" [])])
                    (CAtom (Atom "c" []))) -> return ()
      Right cond -> expectationFailure $
        "Wrong parse: expected (a /\\ b) since c, got: " ++ show cond
      Left err -> expectationFailure $ "Parse error: " ++ show err

  it "a since b /\\ c parses as a since (b /\\ c)" $ do
    case parseCond "<test>" "a since b /\\ c" of
      Right (CSince (CAtom (Atom "a" []))
                    (CAnd [CAtom (Atom "b" []), CAtom (Atom "c" [])])) -> return ()
      Right cond -> expectationFailure $
        "Wrong parse: expected a since (b /\\ c), got: " ++ show cond
      Left err -> expectationFailure $ "Parse error: " ++ show err

  -- Tracing uses recorded provenance
  it "traceDerivations returns provenance for derived facts" $ do
    let prog = "a => b.\nb => c.\n"
    let st = runWithAssertions prog [(0, ["a"])] 1
    let traces = traceDerivations st
        traceNames = map (\(Atom n _, _) -> n) traces
    traceNames `shouldContain` ["b"]
    traceNames `shouldContain` ["c"]

  -- Predicate-indexed world
  it "worldLookupPred returns only matching predicates" $ do
    let w = worldFromList [Atom "p" [TFun "a" []], Atom "q" [TFun "b" []], Atom "p" [TFun "c" []]]
        ps = worldLookupPred "p" w
    Set.size ps `shouldBe` 2
    Set.member (Atom "p" [TFun "a" []]) ps `shouldBe` True
    Set.member (Atom "q" [TFun "b" []]) ps `shouldBe` False

  -- Paper section 3: b must be witnessed strictly before a.  Printed step
  -- 2(4) is an erratum; the witness remains true once established.
  it "after operator requires an earlier right event" $ do
    let prog = unlines
          [ "monitoring after restart => check_system."
          ]
    let st = runWithAssertions prog [(0, ["monitoring"])] 1
    worldContains st "check_system" `shouldBe` False

  it "after operator is strict and remains witnessed" $ do
    let prog = unlines
          [ "monitoring after restart => check_system."
          ]
        st0 = runWithAssertions prog [(0, ["restart"])] 1
        st1 = unsafeStep st0
        st2 = unsafeStep (assertFact (Atom "monitoring" []) st1)
        st3 = unsafeStep st2
        st4 = unsafeStep (assertFact (Atom "restart" []) st3)
    worldContains st1 "check_system" `shouldBe` False
    worldContains st2 "check_system" `shouldBe` True
    worldContains st3 "check_system" `shouldBe` True
    worldContains st4 "check_system" `shouldBe` True

  it "after operator rejects a same-world pair" $ do
    let prog = unlines
          [ "a after b => result."
          ]
    let st = runWithAssertions prog [(0, ["a", "b"])] 1
    worldContains st "result" `shouldBe` False

  -- Pretty-printer handles arithmetic operators
  it "ppTerm prints X + 1 as infix" $ do
    ppTerm (TFun "+" [TVar "X", TFun "1" []]) `shouldBe` "X + 1"

  it "ppTerm prints nested arithmetic with parens" $ do
    ppTerm (TFun "*" [TFun "+" [TVar "X", TFun "1" []], TFun "3" []])
      `shouldBe` "(X + 1) * 3"

  it "ppTerm prints div and mod as infix arithmetic" $ do
    ppTerm (TFun "mod"
      [ TFun "div" [TFun "7" [], TFun "3" []]
      , TFun "2" []
      ]) `shouldBe` "(7 div 3) mod 2"

  it "ppAtom prints is as infix" $ do
    ppAtom (Atom "is" [TVar "Y", TFun "+" [TVar "X", TFun "1" []]])
      `shouldBe` "Y is X + 1"

  it "round-trips every term form through the pretty-printer" $ do
    let sources =
          [ "X"
          , "42"
          , "-3"
          , "f(X, g(a))"
          , "[]"
          , "[a, b]"
          , "[H|T]"
          , "@X"
          , "@(X + 1)"
          , "X + (Y + Z)"
          , "(X + Y) + Z"
          , "X * (Y + Z)"
          , "7 div 3 mod 2"
          , "holder(always, true, is)"
          ]
    forM_ sources $ \source -> case parseTerm "<test>" source of
      Left err -> expectationFailure (show err)
      Right parsed -> parseTerm "<pretty>" (ppTerm parsed) `shouldBe` Right parsed

  it "round-trips every condition form through the pretty-printer" $ do
    let sources =
          [ "p(X)"
          , "X = Y"
          , "~p"
          , "@p"
          , "#p"
          , "?p"
          , "eventually p"
          , "~@p"
          , "@~p"
          , "#(a /\\ b)"
          , "?(a since b)"
          , "eventually (a after b)"
          , "a /\\ b /\\ c"
          , "(a /\\ b) since c"
          , "a since (b /\\ c)"
          , "(a since b) after (c for 2)"
          , "a for 18446744073709551617"
          , "~(a /\\ b)"
          , "is(X, 2 + 3)"
          , "true()"
          ]
    forM_ sources $ \source -> case parseCond "<test>" source of
      Left err -> expectationFailure (show err)
      Right parsed -> parseCond "<pretty>" (ppCond parsed) `shouldBe` Right parsed

  it "round-trips rules without changing temporal-condition scope" $ do
    let sources =
          [ "p."
          , "a /\\ b => c."
          , "(a since b) /\\ c => next result."
          , "enabled(X) => choose(X) -> selected."
          , "q until stop."
          ]
    forM_ sources $ \source -> case parseRule "<test>" source of
      Left err -> expectationFailure (show err)
      Right parsed -> parseRule "<pretty>" (ppRule parsed) `shouldBe` Right parsed
    case parseRule "<test>" "(a since b) /\\ c => next result." of
      Left err -> expectationFailure (show err)
      Right parsed -> ppRule parsed
        `shouldBe` "(a since b) /\\ c => next result."

  it "round-trips complete programs through the pretty-printer" $ do
    let sources =
          [ ""
          , "p.\na => next b.\n"
          , "lookup(X) -> X.\npresent(lookup(key)).\n"
          ]
    forM_ sources $ \source -> case parseProgram "<test>" source of
      Left err -> expectationFailure (show err)
      Right parsed -> parseProgram "<pretty>" (ppProgram parsed) `shouldBe` Right parsed

sharedConformanceSpec :: Spec
sharedConformanceSpec = describe "Shared Haskell/Rust conformance corpus" $ do
  it "initial-world negation" $ do
    src <- readFile "conformance/cases/initial_world.tpl"
    let st = runWithAssertions src [] 1
    worldContains st "inner_negation" `shouldBe` False
    worldContains st "outer_negation" `shouldBe` True

  it "strict after remains latched" $ do
    src <- readFile "conformance/cases/after_strict.tpl"
    let same = runWithAssertions src [(0, ["restart", "monitoring"])] 1
    worldContains same "check_system" `shouldBe` False
    let witnessed = runWithAssertions src [(0, ["restart"]), (1, ["monitoring"])] 3
    worldContains witnessed "check_system" `shouldBe` True

  it "negative cycle exposes both branches" $ do
    src <- readFile "conformance/cases/negative_cycle.tpl"
    let (np, pfNames) = parseAndNormalizeWithPF src
    case stepWorldAll (newInterpreterState np pfNames) of
      Left err -> expectationFailure err
      Right states -> map (\st -> (worldContains st "a", worldContains st "b")) states
        `shouldMatchList` [(True, False), (False, True)]

  it "paper section 4.7 exposes its overlooked third branch" $ do
    src <- readFile "conformance/cases/paper_4_7.tpl"
    let (np, pfNames) = parseAndNormalizeWithPF src
        st = assertFact (Atom "assign" [TFun "1" []])
           $ assertFact (Atom "assign" [TFun "2" []])
           $ newInterpreterState np pfNames
    case stepWorldAll st of
      Left err -> expectationFailure err
      Right states -> length states `shouldBe` 3

  it "retains unsupported blockers admitted by classical minimal semantics" $ do
    src <- readFile "conformance/cases/unsupported_blocker.tpl"
    let (np, pfNames) = parseAndNormalizeWithPF src
    case stepWorldAll (newInterpreterState np pfNames) of
      Left err -> expectationFailure err
      Right states -> do
        length states `shouldBe` 2
        map (\st -> (worldContains st "p(a)", worldContains st "q(a)")) states
          `shouldMatchList` [(True, False), (False, True)]

  it "recursive pattern-function expansion" $ do
    src <- readFile "conformance/cases/append.tpl"
    let st = runWithAssertions src [] 1
    worldContains st "joined([1,2,3,4])" `shouldBe` True

  it "portable arbitrary-precision arithmetic" $ do
    src <- readFile "conformance/cases/arithmetic_edges.tpl"
    let st = runWithAssertions src [] 1
    worldContains st "canonical_integer_spellings(7,0)" `shouldBe` True
    worldContains st "quotient_negative(-3)" `shouldBe` True
    worldContains st "remainder_negative(2)" `shouldBe` True
    worldContains st "quotient_negative_divisor(-3)" `shouldBe` True
    worldContains st "remainder_negative_divisor(-2)" `shouldBe` True
    worldContains st "precedence(4)" `shouldBe` True
    worldContains st
      "arbitrary_precision(85070591730234615865843651857942052864)"
      `shouldBe` True
    maybe False
      (worldMatches (Atom "division_by_zero_succeeded" [TVar "X"]))
      (currentWorld st)
      `shouldBe` False

  it "applies until and atnext to complete result conjunctions" $ do
    src <- readFile "conformance/cases/result_precedence.tpl"
    let st = runWithAssertions src
          [(0, ["start", "arm"]), (1, ["fire"])] 2
    worldContains st "left" `shouldBe` True
    worldContains st "right" `shouldBe` True
    worldContains st "bell" `shouldBe` True
    worldContains st "light" `shouldBe` True

  it "executes every documented Unicode alias" $ do
    src <- readFile "conformance/cases/unicode_aliases.tpl"
    let st = runWithAssertions src [] 2
    worldContains st "value(token)" `shouldBe` True
    worldContains st "next_fact" `shouldBe` True
    worldContains st "unicode_ok" `shouldBe` True

  it "preserves arbitrary-precision auxiliary suffix provenance" $ do
    src <- readFile "conformance/cases/auxiliary_counter_overflow.tpl"
    let st = runWithAssertions src [] 2
    worldContains st "user_aux18446744073709551615" `shouldBe` True
    worldContains st "next_aux18446744073709551616" `shouldBe` True
    worldContains st "fired" `shouldBe` True

  it "keeps keyword constructors and arithmetic predicate names contextual" $ do
    keywordSource <- readFile "conformance/cases/keyword_constructors.tpl"
    let keywordState = runWithAssertions keywordSource [] 1
    worldContains keywordState
      "keyword_terms(always,since,after,for,until,atnext,eventually,next,true,false,is)"
      `shouldBe` True
    worldContains keywordState "prefix_builtin(5)" `shouldBe` True
    worldContains keywordState "impossible" `shouldBe` False

    predicateSource <- readFile "conformance/cases/arithmetic_predicates.tpl"
    let predicateState = runWithAssertions predicateSource
          [(0, ["div(a,b)", "mod(c,d)"])] 1
    worldContains predicateState "namespace_ok" `shouldBe` True

  it "rejects the shared negative corpus at the specified boundaries" $ do
    forZero <- readFile "conformance/rejections/for_zero.tpl"
    plainPrevious <- readFile "conformance/rejections/plain_previous_term.tpl"
    missingPeriod <- readFile "conformance/rejections/missing_period.tpl"
    compileSource forZero `shouldSatisfy` isLeft
    compileSource plainPrevious `shouldSatisfy` isLeft
    parseProgram "<test>" missingPeriod `shouldSatisfy` isLeft
    forM_
      [ "mixed_predicate_arity.tpl"
      , "mixed_constructor_arity.tpl"
      , "mixed_pattern_arity.tpl"
      , "malformed_pattern_relation.tpl"
      , "builtin_result.tpl"
      , "malformed_builtin.tpl"
      , "malformed_arithmetic.tpl"
      , "chained_temporal_condition.tpl"
      , "non_ascii_identifier.tpl"
      , "for_count_overflow.tpl"
      ] $ \filename -> do
        source <- readFile ("conformance/rejections/" ++ filename)
        compileSource source `shouldSatisfy` isLeft
    forM_
      [ "unsafe_range.tpl"
      , "unsafe_pattern_input.tpl"
      , "unsafe_pattern_output.tpl"
      ] $ \filename -> do
        source <- readFile ("conformance/rejections/" ++ filename)
        case compileSource source of
          Left err -> expectationFailure err
          Right (np, pfNames) ->
            stepWorld (newInterpreterState np pfNames) `shouldSatisfy` isLeft

batchExecutionSpec :: Spec
batchExecutionSpec = describe "Deterministic branch-preserving batch execution" $ do
  it "renders complete minimal-model histories canonically" $ do
    let (program, pfNames) = parseAndNormalizeWithPF "~a => b. ~b => a."
        options = BatchOptions 1 Map.empty False
    case runBatch options program pfNames of
      Left err -> expectationFailure err
      Right result -> renderBatch result `shouldBe` unlines
        [ "steps=1"
        , "branches=2"
        , "branch=0"
        , "  w0=[a]"
        , "  digest=3ac3fa0d287999b7"
        , "branch=1"
        , "  w0=[b]"
        , "  digest=faa2015c6af3d282"
        ]

  it "rejects unreachable and nonground scheduled assertions" $ do
    let (program, pfNames) = parseAndNormalizeWithPF "ok."
        unreachable = BatchOptions 1
          (Map.singleton 1 [Atom "event" []]) False
        nonground = BatchOptions 1
          (Map.singleton 0 [Atom "event" [TVar "X"]]) False
        builtin = BatchOptions 1
          (Map.singleton 0 [Atom "at" [TFun "99" []]]) False
    runBatch unreachable program pfNames `shouldSatisfy` isLeft
    runBatch nonground program pfNames `shouldSatisfy` isLeft
    runBatch builtin program pfNames `shouldSatisfy` isLeft

  it "keeps source predicates ending in _auxN visible" $ do
    case parseProgram "<test>"
        "user_aux0. always_aux0. trigger => next generated." of
      Left err -> expectationFailure (show err)
      Right source -> case normalizeDetailed source of
        Left err -> expectationFailure err
        Right normalized -> do
          let options = BatchOptions 2
                (Map.singleton 0 [Atom "trigger" []]) False
          case runBatchWithAuxiliaries options
              (normalizedProgram normalized)
              (normalizedPatternFunctions normalized)
              (normalizedAuxiliaryPredicates normalized) of
            Left err -> expectationFailure err
            Right result -> do
              renderBatch result `shouldContain` "w0=[always_aux0,trigger,user_aux0]"
              renderBatch result `shouldNotContain` "next_aux1"

modelCheckerSpec :: Spec
modelCheckerSpec = describe "Portable bounded protocol model checker" $ do
  it "parses schedules and rejects assertions outside the horizon" $ do
    parseScenario "<test>" (unlines
      [ "name demo"
      , "program demo.tpl"
      , "steps 1"
      , "assert 1 request"
      ]) `shouldSatisfy` isLeft
    parseScenario "<test>" (unlines
      [ "name demo"
      , "program demo.tpl"
      , "steps 1"
      , "assert 0 at(99)"
      ]) `shouldSatisfy` isLeft

  it "parses independent input-choice groups" $ do
    let source = unlines
          [ "name choices"
          , "program choices.tpl"
          , "steps 2"
          , "choose 1 p1 yes(p1)"
          , "choose 1 p1 no(p1)"
          , "choose 1 p2 yes(p2)"
          , "choose 1 p2 none"
          ]
    case parseScenario "<test>" source of
      Left err -> expectationFailure err
      Right scenario -> case Map.lookup 1 (scenarioChoices scenario) of
        Nothing -> expectationFailure "missing parsed choice groups"
        Just groups -> map (length . choiceGroupAlternatives) groups `shouldBe` [2, 2]

  it "explores both safe arbiter choices" $ do
    scenarioSource <- readFile "examples/model-checking/arbiter.tpmc"
    programSource <- readFile "examples/model-checking/arbiter.tpl"
    expectedSummary <- readFile "examples/model-checking/arbiter.expected"
    expectedDot <- readFile "examples/model-checking/arbiter.expected.dot"
    case (parseScenario "arbiter.tpmc" scenarioSource, compileDetailedSource programSource) of
      (Right scenario, Right normalized) ->
        case runModelCheckWithAuxiliaries scenario
            (normalizedProgram normalized)
            (normalizedPatternFunctions normalized)
            (normalizedAuxiliaryPredicates normalized) of
          Left err -> expectationFailure err
          Right result -> do
            checkPassed result `shouldBe` True
            length (checkResultNodes result) `shouldBe` 9
            length (checkResultTerminalNodes result) `shouldBe` 2
            checkResultMaxWidth result `shouldBe` 2
            renderCheckSummary 1 False result `shouldBe` expectedSummary
            renderCheckDot False result `shouldBe` expectedDot
      (Left err, _) -> expectationFailure err
      (_, Left err) -> expectationFailure err

  it "accepts the correct atomic-commit coordinator" $ do
    scenarioSource <- readFile "examples/model-checking/commit-safe.tpmc"
    programSource <- readFile "examples/model-checking/commit.tpl"
    expectedSummary <- readFile "examples/model-checking/commit-safe.expected"
    case (parseScenario "commit-safe.tpmc" scenarioSource, compileDetailedSource programSource) of
      (Right scenario, Right normalized) ->
        case runModelCheckWithAuxiliaries scenario
            (normalizedProgram normalized)
            (normalizedPatternFunctions normalized)
            (normalizedAuxiliaryPredicates normalized) of
          Left err -> expectationFailure err
          Right result -> do
            checkPassed result `shouldBe` True
            length (checkResultNodes result) `shouldBe` 14
            length (checkResultTerminalNodes result) `shouldBe` 4
            renderCheckSummary 1 False result `shouldBe` expectedSummary
      (Left err, _) -> expectationFailure err
      (_, Left err) -> expectationFailure err

  it "prints the shortest counterexample for the broken coordinator" $ do
    scenarioSource <- readFile "examples/model-checking/commit-buggy.tpmc"
    programSource <- readFile "examples/model-checking/commit-buggy.tpl"
    expectedSummary <- readFile "examples/model-checking/commit-buggy.expected"
    case (parseScenario "commit-buggy.tpmc" scenarioSource, compileDetailedSource programSource) of
      (Right scenario, Right normalized) ->
        case runModelCheckWithAuxiliaries scenario
            (normalizedProgram normalized)
            (normalizedPatternFunctions normalized)
            (normalizedAuxiliaryPredicates normalized) of
          Left err -> expectationFailure err
          Right result -> do
            checkPassed result `shouldBe` False
            map (map checkNodeStep) (counterexampleTraces result)
              `shouldBe` replicate 2 [Just 0, Just 1, Just 2]
            renderCheckSummary 1 False result `shouldBe` expectedSummary
            renderCheckDot False result `shouldContain` "fillcolor=\"#fee2e2\""
      (Left err, _) -> expectationFailure err
      (_, Left err) -> expectationFailure err

  it "matches invariants against stored facts, not pattern-function queries" $ do
    let scenarioSource = unlines
          [ "name fact-only-invariant"
          , "program ignored.tpl"
          , "steps 1"
          , "invariant no_lookup_fact forbids lookup(key, value)"
          ]
        programSource = "lookup(key) -> value.\n"
    case (parseScenario "<test>" scenarioSource, compileDetailedSource programSource) of
      (Right scenario, Right normalized) ->
        case runModelCheckWithAuxiliaries scenario
            (normalizedProgram normalized)
            (normalizedPatternFunctions normalized)
            (normalizedAuxiliaryPredicates normalized) of
          Left err -> expectationFailure err
          Right result -> checkPassed result `shouldBe` True
      (Left err, _) -> expectationFailure err
      (_, Left err) -> expectationFailure err

  it "explores an explicit no-input alternative" $ do
    let scenarioSource = unlines
          [ "name optional-input"
          , "program ignored.tpl"
          , "steps 1"
          , "choose 0 event present"
          , "choose 0 event none"
          , "invariant no_bad forbids bad"
          ]
        programSource = "present => bad.\n"
    case (parseScenario "<test>" scenarioSource, compileDetailedSource programSource) of
      (Right scenario, Right normalized) ->
        case runModelCheckWithAuxiliaries scenario
            (normalizedProgram normalized)
            (normalizedPatternFunctions normalized)
            (normalizedAuxiliaryPredicates normalized) of
          Left err -> expectationFailure err
          Right result -> do
            checkPassed result `shouldBe` False
            length (checkResultNodes result) `shouldBe` 3
            length (counterexampleTraces result) `shouldBe` 1
      (Left err, _) -> expectationFailure err
      (_, Left err) -> expectationFailure err

  it "renders source _aux predicates but hides actual generated predicates" $ do
    let scenarioSource = unlines
          [ "name auxiliary-visibility"
          , "program ignored.tpl"
          , "steps 2"
          , "assert 0 trigger"
          , "invariant no_bad forbids bad"
          ]
        programSource =
          "user_aux0. always_aux0. trigger => next generated."
    case (parseScenario "<test>" scenarioSource, parseProgram "<test>" programSource) of
      (Right scenario, Right source) -> case normalizeDetailed source of
        Left err -> expectationFailure err
        Right normalized -> case runModelCheckWithAuxiliaries scenario
            (normalizedProgram normalized)
            (normalizedPatternFunctions normalized)
            (normalizedAuxiliaryPredicates normalized) of
          Left err -> expectationFailure err
          Right result -> do
            renderCheckDot False result `shouldContain` "user_aux0"
            renderCheckDot False result `shouldContain` "always_aux0"
            renderCheckDot False result `shouldNotContain` "next_aux1"
      (Left err, _) -> expectationFailure err
      (_, Left err) -> expectationFailure (show err)

propositionalOracleSpec :: Spec
propositionalOracleSpec = describe "Independent exhaustive propositional oracle" $
  it "agrees with the general evaluator on 1024 two-atom programs" $ do
    let atomA = Atom "a" []
        atomB = Atom "b" []
        falseAtom = Atom "false" []
        positive atom = NormalCond 0 False atom
        negative atom = NormalCond 0 True atom
        structural =
          [ NormalRule [positive atomA, positive falseAtom] atomB
          , NormalRule [positive atomB, positive falseAtom] atomA
          ]
        optional =
          [ NormalRule [] atomA
          , NormalRule [] atomB
          , NormalRule [negative atomA] atomA
          , NormalRule [negative atomB] atomB
          , NormalRule [negative atomB] atomA
          , NormalRule [negative atomA] atomB
          , NormalRule [positive atomA] atomB
          , NormalRule [positive atomB] atomA
          , NormalRule [positive atomA, negative atomB] atomB
          , NormalRule [positive atomB, negative atomA] atomA
          ]
        programs = map (structural ++) (allSubsets optional)
        universe = Set.fromList [atomA, atomB]
        oracle program =
          let proposed = map Set.fromList (allSubsets [atomA, atomB])
              models = filter (oracleModel program) proposed
          in [ model
             | model <- models
             , not (any (\other -> other `Set.isProperSubsetOf` model) models)
             ]
        engine program = case stepWorldGeneralAll
          (newInterpreterState program Set.empty) of
            Left err -> Left err
            Right states -> Right
              [ Set.intersection universe (maybe Set.empty worldToSet (currentWorld state))
              | state <- states
              ]
    mapM_ (\(index, program) -> case engine program of
      Left err -> expectationFailure $ "program " ++ show index ++ ": " ++ err
      Right actual -> actual `shouldMatchList` oracle program)
      (zip [0 :: Int ..] programs)
  where
    oracleModel program world = all (oracleRule world) program
    oracleRule world (NormalRule conditions headAtom) =
      not (all (oracleCondition world) conditions) || headAtom `Set.member` world
    oracleCondition world (NormalCond _ negated atom)
      | atom == Atom "false" [] = negated
      | atom == Atom "true" [] = not negated
      | negated = atom `Set.notMember` world
      | otherwise = atom `Set.member` world

allSubsets :: [a] -> [[a]]
allSubsets [] = [[]]
allSubsets (item:rest) =
  let suffixes = allSubsets rest
  in suffixes ++ map (item :) suffixes

-- Helper to filter internal atoms
isInternal :: Atom -> Bool
isInternal (Atom "true" []) = True
isInternal (Atom "at" _) = True
isInternal (Atom n _) = "_aux" `isInfixOfName` n
  where isInfixOfName needle haystack = any (isPrefixOfName needle) (tails haystack)
        isPrefixOfName [] _ = True
        isPrefixOfName _ [] = False
        isPrefixOfName (x:xs) (y:ys) = x == y && isPrefixOfName xs ys
        tails [] = [[]]
        tails xs@(_:xs') = xs : tails xs'

normalizeWithWarnings :: String -> (NormalProgram, [String])
normalizeWithWarnings src = case parseProgram "<test>" src of
  Left err -> error $ "Parse error: " ++ show err
  Right prog -> case normalize prog of
    Left err -> error $ "Normalization error: " ++ err
    Right ((np, _), warnings) -> (np, warnings)
