module Main where

import Test.Hspec
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.Either (isLeft, isRight)

import TemporalProlog.Syntax
import TemporalProlog.Parser
import TemporalProlog.PrettyPrint
import TemporalProlog.Normalizer
import TemporalProlog.Interpreter
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
  mixedTPrevSpec
  backwardChainingSpec
  correctnessAndFeatureSpec

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

  it "parses functors" $ do
    parseTerm "<test>" "f(X, Y)" `shouldBe` Right (TFun "f" [TVar "X", TVar "Y"])

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

  it "parses since/after/for" $ do
    parseCond "<test>" "a since b" `shouldSatisfy` isRight
    parseCond "<test>" "a after b" `shouldSatisfy` isRight
    parseCond "<test>" "a for 3" `shouldSatisfy` isRight

  it "parses implication rules" $ do
    parseRule "<test>" "a => b." `shouldSatisfy` isRight
    parseRule "<test>" "a /\\ b => c." `shouldSatisfy` isRight

  it "parses fact rules" $ do
    parseRule "<test>" "p(X)." `shouldSatisfy` isRight

  it "parses always results" $ do
    parseRule "<test>" "always p." `shouldSatisfy` isRight

  it "parses until results" $ do
    parseRule "<test>" "a => p until q." `shouldSatisfy` isRight

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

  it "normalizes programs with negation" $ do
    let np = parseAndNormalize "~a => b."
    length np `shouldSatisfy` (>= 1)
    -- The negated condition should be ncNegated = True
    let hasNeg = any (\r -> any ncNegated (nrConditions r)) np
    hasNeg `shouldBe` True

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
    -- Pattern functions with variables produce non-ground facts that the
    -- interpreter filters out. Ground instances work correctly.
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
stratificationSpec = describe "Stratification" $ do
  it "~a => a: negative self-cycle should error" $ do
    let np = parseAndNormalize "~a => a.\n"
    stepWorld (newInterpreterState np Set.empty) `shouldSatisfy` isLeft

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

  it "depth limit prevents infinite recursion" $ do
    -- loop(X) -> loop(X) would recurse forever without depth limit
    let prog = unlines
          [ "loop(X) -> loop(X)."
          , "start(a)."
          , "start(X) /\\ loop(X) = Y => result(Y)."
          ]
    let st = runWithAssertions prog [] 1
    -- Should not derive result (depth limit hit), but should not crash
    worldContains st "result(a)" `shouldBe` False

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

  -- Paper step 2(4): a after b is established by a and persists until b.
  it "after operator is established by its left event" $ do
    let prog = unlines
          [ "monitoring after restart => check_system."
          ]
    let st = runWithAssertions prog [(0, ["monitoring"])] 1
    worldContains st "check_system" `shouldBe` True

  it "after operator persists until the right event" $ do
    let prog = unlines
          [ "monitoring after restart => check_system."
          ]
        st0 = runWithAssertions prog [(0, ["monitoring"])] 1
        st1 = unsafeStep st0
        st2 = unsafeStep (assertFact (Atom "restart" []) st1)
        st3 = unsafeStep st2
    worldContains st1 "check_system" `shouldBe` True
    worldContains st2 "check_system" `shouldBe` False
    worldContains st3 "check_system" `shouldBe` False

  it "after operator: its left event wins when both events hold" $ do
    let prog = unlines
          [ "a after b => result."
          ]
    let st = runWithAssertions prog [(0, ["a", "b"])] 1
    worldContains st "result" `shouldBe` True

  -- Pretty-printer handles arithmetic operators
  it "ppTerm prints X + 1 as infix" $ do
    ppTerm (TFun "+" [TVar "X", TFun "1" []]) `shouldBe` "X + 1"

  it "ppTerm prints nested arithmetic with parens" $ do
    ppTerm (TFun "*" [TFun "+" [TVar "X", TFun "1" []], TFun "3" []])
      `shouldBe` "(X + 1) * 3"

  it "ppAtom prints is as infix" $ do
    ppAtom (Atom "is" [TVar "Y", TFun "+" [TVar "X", TFun "1" []]])
      `shouldBe` "Y is X + 1"

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
