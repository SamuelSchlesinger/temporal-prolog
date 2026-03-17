module Main where

import Test.Hspec
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.Either (isLeft, isRight)
import Control.Exception (evaluate, try, SomeException)

import TemporalProlog.Syntax
import TemporalProlog.Parser
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

-- Helper: parse and normalize a program string
parseAndNormalize :: String -> IO NormalProgram
parseAndNormalize src = case parseProgram "<test>" src of
  Left err -> fail $ "Parse error: " ++ show err
  Right prog -> normalize prog

-- Helper: run program for n steps, asserting facts at each step
-- assertions: list of (worldNum, [atomString]) pairs
runWithAssertions :: String -> [(Int, [String])] -> Int -> IO InterpreterState
runWithAssertions src assertions totalSteps = do
  np <- parseAndNormalize src
  let st0 = newInterpreterState np
      assertionMap = Map.fromListWith (++) assertions
  return $ foldl (\st i ->
    let withAsserts = case Map.lookup i assertionMap of
          Nothing -> st
          Just atoms -> foldl (\s a -> case parseAtom "<test>" a of
            Right atom -> assertFact atom s
            Left _ -> s) st atoms
    in stepWorld withAsserts
    ) st0 [0..totalSteps-1]

worldContains :: InterpreterState -> String -> Bool
worldContains st atomStr = case (currentWorld st, parseAtom "<test>" atomStr) of
  (Just w, Right atom) -> atom `Set.member` w
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
    let prog = "hot(X) => off(X).\n~hot(X) => on(X).\n"
    parseProgram "<test>" prog `shouldSatisfy` isRight

  it "parses pattern functions" $ do
    let prog = "append([], X) -> X.\n"
    case parseProgram "<test>" prog of
      Right p -> length (progPatternFuncs p) `shouldBe` 1
      Left _ -> expectationFailure "Failed to parse pattern function"

  it "rejects keywords as predicate names" $ do
    parseAtom "<test>" "since" `shouldSatisfy` isLeft

  it "parses empty program" $ do
    parseProgram "<test>" "" `shouldBe` Right (Program [] [])
    parseProgram "<test>" "  \n  " `shouldBe` Right (Program [] [])

normalizerSpec :: Spec
normalizerSpec = describe "Normalizer" $ do
  it "normalizes simple facts" $ do
    np <- parseAndNormalize "p."
    length np `shouldBe` 1

  it "normalizes simple rules" $ do
    np <- parseAndNormalize "a => b."
    length np `shouldBe` 1

  it "expands always into auxiliary rules" $ do
    np <- parseAndNormalize "always p."
    -- always p -> p, @aux => aux, aux => p (3 rules)
    length np `shouldSatisfy` (>= 3)

  it "expands for into repeated @" $ do
    np <- parseAndNormalize "a for 3 => b."
    -- a for 3 expands to a /\ @a /\ @@a
    let hasDepth2 = any (\r -> any (\c -> ncPrevDepth c == 2) (nrConditions r)) np
    hasDepth2 `shouldBe` True

  it "normalizes programs with negation" $ do
    np <- parseAndNormalize "~a => b."
    length np `shouldSatisfy` (>= 1)
    -- The negated condition should be ncNegated = True
    let hasNeg = any (\r -> any ncNegated (nrConditions r)) np
    hasNeg `shouldBe` True

  it "handles pattern function first substep" $ do
    np <- parseAndNormalize "append([], X) -> X.\n"
    -- Should produce append([], X, X) as a fact
    let appendRules = filter (\r -> let Atom n _ = nrHead r in n == "append") np
    length appendRules `shouldSatisfy` (>= 1)

  it "produces only normal-form rules" $ do
    np <- parseAndNormalize "hot(X) => off(X).\n~hot(X) => on(X).\n@on(X) /\\ hot(X) => warning(X).\n"
    -- All rules should have NormalCond with proper structure
    let allNormal = all (\r -> all (\c -> ncPrevDepth c >= 0) (nrConditions r)) np
    allNormal `shouldBe` True

interpreterSpec :: Spec
interpreterSpec = describe "Interpreter" $ do
  it "empty program produces empty worlds" $ do
    let st = stepWorld (newInterpreterState [])
    case currentWorld st of
      Just w -> Set.filter (not . isInternal) w `shouldBe` Set.empty
      Nothing -> expectationFailure "No world"

  it "derives facts from simple rules" $ do
    st <- runWithAssertions "hot(X) => off(X)." [(0, ["hot(heater)"])] 1
    worldContains st "off(heater)" `shouldBe` True

  it "handles negation-as-failure" $ do
    st <- runWithAssertions "~hot(X) => on(X)." [(0, ["hot(heater)"])] 1
    -- hot(heater) is asserted, so ~hot(heater) fails, on(heater) not derived
    worldContains st "on(heater)" `shouldBe` False

  it "foot warmer example" $ do
    let prog = "hot(X) => off(X).\n~hot(X) => on(X).\n"
    -- World 0 with hot(heater)
    st1 <- runWithAssertions prog [(0, ["hot(heater)"])] 1
    worldContains st1 "off(heater)" `shouldBe` True
    worldContains st1 "on(heater)" `shouldBe` False
    -- World 1 without assertion: ~hot(X) has unbound X (negation-as-failure
    -- with free variables doesn't bind them), so on(X) is not ground.
    -- Neither on(heater) nor off(heater) will be derived.
    let st2 = stepWorld st1
    worldContains st2 "off(heater)" `shouldBe` False

  it "foot warmer example with ground negation" $ do
    -- Use ground negation to avoid the free variable issue
    let prog = "hot(heater) => off(heater).\n~hot(heater) => on(heater).\n"
    st1 <- runWithAssertions prog [(0, ["hot(heater)"])] 1
    worldContains st1 "off(heater)" `shouldBe` True
    worldContains st1 "on(heater)" `shouldBe` False
    -- World 1 without assertion: ~hot(heater) succeeds (ground), on(heater) derived
    let st2 = stepWorld st1
    worldContains st2 "on(heater)" `shouldBe` True
    worldContains st2 "off(heater)" `shouldBe` False

  it "handles @-conditions (previous world)" $ do
    let prog = "@on(X) /\\ hot(X) => warning(X).\non(X) => on(X).\n"
    st1 <- runWithAssertions prog [(0, ["on(heater)"])] 1
    -- World 0: on(heater) is asserted, but @on(heater) fails (no previous world)
    worldContains st1 "warning(heater)" `shouldBe` False
    -- World 1: assert hot(heater), @on(heater) should succeed
    let st2 = assertFact (Atom "hot" [TFun "heater" []]) st1
        st3 = stepWorld st2
    worldContains st3 "warning(heater)" `shouldBe` True

  it "world 0 @-conditions fail" $ do
    let prog = "@p => q.\n"
    st <- runWithAssertions prog [(0, ["p"])] 1
    -- @p at world 0 should fail
    worldContains st "q" `shouldBe` False

  it "mutual exclusion" $ do
    let prog = unlines
          [ "assign(X) /\\ @assigned_to(X) => assigned_to(X)."
          , "assign(1) /\\ ~@assigned_to_something => assigned_to(1)."
          , "assign(2) /\\ ~assign(1) /\\ ~@assigned_to_something => assigned_to(2)."
          , "assigned_to(X) => assigned_to_something."
          ]
    st <- runWithAssertions prog [(0, ["assign(1)", "assign(2)"])] 1
    -- Only 1 should be assigned (1 has priority)
    worldContains st "assigned_to(1)" `shouldBe` True
    worldContains st "assigned_to(2)" `shouldBe` False

  it "handles multiple steps" $ do
    let prog = "@p => q.\nq => r.\n"
    st1 <- runWithAssertions prog [(0, ["p"])] 1
    -- World 0: p is asserted. @p fails. No q or r.
    worldContains st1 "q" `shouldBe` False
    -- World 1: @p succeeds. q derived. r derived.
    let st2 = stepWorld st1
    worldContains st2 "q" `shouldBe` True
    worldContains st2 "r" `shouldBe` True

  it "handles numeric comparisons" $ do
    let prog = "temp(X) /\\ X > 100 => alarm.\n"
    st <- runWithAssertions prog [(0, ["temp(150)"])] 1
    worldContains st "alarm" `shouldBe` True

  it "handles numeric comparison - no alarm" $ do
    let prog = "temp(X) /\\ X > 100 => alarm.\n"
    st <- runWithAssertions prog [(0, ["temp(50)"])] 1
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
    st <- runWithAssertions prog [(0, ["p"])] 1
    worldContains st "q" `shouldBe` True
    -- q persists to the next world via q => q
    let st2 = stepWorld st
    worldContains st2 "q" `shouldBe` True

  it "a => next b: b absent at world 0, present at world 1" $ do
    let prog = "a => next b.\n"
    st <- runWithAssertions prog [(0, ["a"])] 1
    -- At world 0, b should not be derived (it is deferred to next)
    worldContains st "b" `shouldBe` False
    -- At world 1, b should appear
    let st2 = stepWorld st
    worldContains st2 "b" `shouldBe` True

  it "a => next (next b): b appears at world 2" $ do
    let prog = "a => next next b.\n"
    st0 <- runWithAssertions prog [(0, ["a"])] 1
    worldContains st0 "b" `shouldBe` False
    let st1 = stepWorld st0
    worldContains st1 "b" `shouldBe` False
    let st2 = stepWorld st1
    worldContains st2 "b" `shouldBe` True

  it "eventually p /\\ q => r: combined condition" $ do
    let prog = "eventually p /\\ q => r.\n"
    st <- runWithAssertions prog [(0, ["p", "q"])] 1
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
    st <- runWithAssertions prog [] 1
    worldContains st "result(box(hello))" `shouldBe` True

  it "pattern function normalizes to predicate with extra arg" $ do
    -- wrap(X) -> box(X) becomes the fact wrap(X, box(X))
    np <- parseAndNormalize "wrap(X) -> box(X).\n"
    let wrapRules = filter (\r -> let Atom n _ = nrHead r in n == "wrap") np
    length wrapRules `shouldSatisfy` (>= 1)
    let NormalRule _ (Atom _ args) = head wrapRules
    length args `shouldBe` 2

-- ============================================================
-- H. Unification = and at(X)
-- ============================================================

unificationEqualitySpec :: Spec
unificationEqualitySpec = describe "Unification = and at(X)" $ do
  it "p(X) /\\ X = hello => q(X): with p(hello), derives q(hello)" $ do
    let prog = "p(X) /\\ X = hello => q(X).\n"
    st <- runWithAssertions prog [(0, ["p(hello)"])] 1
    worldContains st "q(hello)" `shouldBe` True

  it "a = b => never: unification failure on distinct ground terms" $ do
    let prog = "a = b => never.\n"
    st <- runWithAssertions prog [] 1
    worldContains st "never" `shouldBe` False

  it "at(N) /\\ N > 3 => late: late appears at world 4+" $ do
    let prog = "at(N) /\\ N > 3 => late.\n"
    st <- runWithAssertions prog [] 5
    -- After 5 steps we are at world 4 (0..4)
    worldContains st "late" `shouldBe` True
    -- Check that world 3 does NOT have late
    let history = getHistory st
        world3 = history !! 3
        lateAtom = case parseAtom "<test>" "late" of
                     Right a -> a
                     Left _ -> error "bad parse"
    Set.member lateAtom world3 `shouldBe` False

  it "at(N) respects @-depth" $ do
    -- @at(N) at world 2 should give N=1 (previous world number)
    let prog = "@at(N) /\\ N = 1 => prev_was_one."
    np <- parseAndNormalize prog
    let st = stepWorldN 3 (newInterpreterState np)
    worldContains st "prev_was_one" `shouldBe` True

  it "at(N) at depth 0 still works" $ do
    let prog = "at(N) /\\ N = 2 => is_world_two."
    np <- parseAndNormalize prog
    let st = stepWorldN 3 (newInterpreterState np)
    worldContains st "is_world_two" `shouldBe` True

  it "@@at(N) gives world number minus 2" $ do
    let prog = "@@at(N) /\\ N = 1 => two_back_was_one."
    np <- parseAndNormalize prog
    let st = stepWorldN 4 (newInterpreterState np)
    worldContains st "two_back_was_one" `shouldBe` True

-- ============================================================
-- I. Stratification
-- ============================================================

stratificationSpec :: Spec
stratificationSpec = describe "Stratification" $ do
  it "~a => a: negative self-cycle should error" $ do
    np <- parseAndNormalize "~a => a.\n"
    let st = stepWorld (newInterpreterState np)
        -- Force the world set deeply: convert to list to force all elements
        forceWorld = case currentWorld st of
          Just w  -> length (Set.toList w) `seq` ()
          Nothing -> ()
    result <- try (evaluate forceWorld) :: IO (Either SomeException ())
    result `shouldSatisfy` isLeft

  it "@~a => b: @ excludes from dependency graph, should succeed" $ do
    let prog = "@~a => b.\n"
    st <- runWithAssertions prog [] 1
    -- At world 0, @~a is true (no previous world, negation of absent = true)
    worldContains st "b" `shouldBe` True

-- ============================================================
-- J. Safety validation
-- ============================================================

safetyValidationSpec :: Spec
safetyValidationSpec = describe "Safety validation" $ do
  it "~p(X) => q(X) normalizes (warns about X)" $ do
    np <- parseAndNormalize "~p(X) => q(X).\n"
    length np `shouldSatisfy` (>= 1)

  it "r(X) /\\ ~p(X) => q(X) normalizes" $ do
    np <- parseAndNormalize "r(X) /\\ ~p(X) => q(X).\n"
    length np `shouldSatisfy` (>= 1)

-- ============================================================
-- K-M. Edge cases
-- ============================================================

edgeCaseSpec :: Spec
edgeCaseSpec = describe "Edge cases" $ do
  it "deep @-nesting: @@@@p => q has ncPrevDepth == 4" $ do
    np <- parseAndNormalize "@@@@p => q.\n"
    let depths = [ncPrevDepth c | r <- np, c <- nrConditions r, let Atom n _ = ncAtom c, n == "p"]
    depths `shouldContain` [4]

  it "Unicode negation: parseCond \\x00ACp succeeds" $ do
    parseCond "<test>" "\x00ACp" `shouldSatisfy` isRight

  it "bare fact: p. derives p" $ do
    st <- runWithAssertions "p.\n" [] 1
    worldContains st "p" `shouldBe` True

  it "world history length after 3 steps" $ do
    let st0 = newInterpreterState []
        st3 = stepWorldN 3 st0
    length (getHistory st3) `shouldBe` 3
    getWorldNumber st3 `shouldBe` 2

  it "self-unification: p(X) /\\ X = X => q(X) with p(a) derives q(a)" $ do
    let prog = "p(X) /\\ X = X => q(X).\n"
    st <- runWithAssertions prog [(0, ["p(a)"])] 1
    worldContains st "q(a)" `shouldBe` True

-- ============================================================
-- N. Mixed TPrev depths
-- ============================================================

mixedTPrevSpec :: Spec
mixedTPrevSpec = describe "Mixed TPrev depths" $ do
  it "p(@X, Y) normalizes without error" $ do
    -- Previously this would error with "Mixed TPrev depths..."
    np <- parseAndNormalize "p(@X, Y) => q(X, Y)."
    length np `shouldSatisfy` (> 0)

  it "p(@X, @@Y) normalizes without error" $ do
    np <- parseAndNormalize "p(@X, @@Y) => q(X, Y)."
    length np `shouldSatisfy` (> 0)

  it "p(@X, Y, @@Z) normalizes without error" $ do
    np <- parseAndNormalize "p(@X, Y, @@Z) => q(X, Y, Z)."
    length np `shouldSatisfy` (> 0)

  it "mixed depths end-to-end: p(@X, X) matches across worlds" $ do
    -- p(@X, X) means: match p(a, b) in the current world where
    -- a appeared in p's first argument at the previous world, and b = X.
    -- World 0: assert p(hello, hello) -> projection aux derives
    -- World 1: assert p(hello, hello) -> @aux(hello) succeeds, p(hello, hello) matches
    let prog = unlines
          [ "p(@X, X) => matched(X)."
          ]
    st <- runWithAssertions prog [(0, ["p(hello, hello)"]), (1, ["p(hello, hello)"])] 2
    worldContains st "matched(hello)" `shouldBe` True

  it "mixed depths: depth-0 only args still work" $ do
    -- If all depths happen to be 0, it should still work fine
    let prog = "p(X, Y) => q(X, Y)."
    st <- runWithAssertions prog [(0, ["p(a, b)"])] 1
    worldContains st "q(a, b)" `shouldBe` True

  it "mixed depths: uniform non-zero depths still work" $ do
    -- If all depths are the same non-zero value, the existing logic handles it
    let prog = "@p(X, Y) => q(X, Y)."
    st <- runWithAssertions prog [(0, ["p(a, b)"])] 2
    worldContains st "q(a, b)" `shouldBe` True

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
