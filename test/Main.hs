module Main where

import Test.Hspec
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.Either (isLeft, isRight)

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
