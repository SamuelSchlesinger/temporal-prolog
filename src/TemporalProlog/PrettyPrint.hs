-- |
-- Module      : TemporalProlog.PrettyPrint
-- Description : Human-readable display for all AST types
--
-- Pretty-prints terms, atoms, conditions, results, rules, and their
-- normalized counterparts. Uses ASCII operator syntax. Handles special
-- display for lists (@[H|T]@, @[a, b, c]@), infix operators (@X > 5@),
-- and the @\@@ prefix.
module TemporalProlog.PrettyPrint where

import Data.List (intercalate)
import TemporalProlog.Syntax

ppTerm :: Term -> String
ppTerm (TVar v)      = v
ppTerm (TFun "[]" []) = "[]"
ppTerm (TFun f [])   = f
ppTerm (TFun "." [h, t]) = "[" ++ ppTerm h ++ ppListTail t ++ "]"
ppTerm (TFun f ts)   = f ++ "(" ++ intercalate ", " (map ppTerm ts) ++ ")"
ppTerm (TPrev t)     = "@" ++ ppTermAtom t

ppTermAtom :: Term -> String
ppTermAtom t@(TFun _ (_:_)) = ppTerm t
ppTermAtom t@(TVar _)       = ppTerm t
ppTermAtom t@(TFun _ [])    = ppTerm t
ppTermAtom t                = "(" ++ ppTerm t ++ ")"

ppListTail :: Term -> String
ppListTail (TFun "[]" [])    = ""
ppListTail (TFun "." [h, t]) = ", " ++ ppTerm h ++ ppListTail t
ppListTail t                  = " | " ++ ppTerm t

ppAtom :: Atom -> String
ppAtom (Atom "=" [l, r])  = ppTerm l ++ " = " ++ ppTerm r
ppAtom (Atom ">" [l, r])  = ppTerm l ++ " > " ++ ppTerm r
ppAtom (Atom "<" [l, r])  = ppTerm l ++ " < " ++ ppTerm r
ppAtom (Atom ">=" [l, r]) = ppTerm l ++ " >= " ++ ppTerm r
ppAtom (Atom "<=" [l, r]) = ppTerm l ++ " <= " ++ ppTerm r
ppAtom (Atom p [])         = p
ppAtom (Atom p ts)         = p ++ "(" ++ intercalate ", " (map ppTerm ts) ++ ")"

ppCond :: Cond -> String
ppCond (CAtom a)    = ppAtom a
ppCond (CNeg c)     = "~" ++ ppCondAtom c
ppCond (CPrev c)    = "@" ++ ppCondAtom c
ppCond (CHasBeen c) = "#" ++ ppCondAtom c
ppCond (COnce c)    = "?" ++ ppCondAtom c
ppCond (CSince c d) = ppCondAtom c ++ " since " ++ ppCondAtom d
ppCond (CAfter c d) = ppCondAtom c ++ " after " ++ ppCondAtom d
ppCond (CFor c n)   = ppCondAtom c ++ " for " ++ show n
ppCond (CAnd cs)    = intercalate " /\\ " (map ppCondAtom cs)

ppCondAtom :: Cond -> String
ppCondAtom c@(CAtom _) = ppCond c
ppCondAtom c@(CNeg _)  = ppCond c
ppCondAtom c@(CPrev _) = ppCond c
ppCondAtom c            = "(" ++ ppCond c ++ ")"

ppResult :: Result -> String
ppResult (RAtom a)     = ppAtom a
ppResult (RAlways r)   = "always " ++ ppResultAtom r
ppResult (RUntil r c)  = ppResultAtom r ++ " until " ++ ppCondAtom c
ppResult (RAtNext r c) = ppResultAtom r ++ " atnext " ++ ppCondAtom c
ppResult (RAnd rs)     = intercalate " /\\ " (map ppResultAtom rs)

ppResultAtom :: Result -> String
ppResultAtom r@(RAtom _) = ppResult r
ppResultAtom r            = "(" ++ ppResult r ++ ")"

ppRule :: Rule -> String
ppRule (Rule cs r) = intercalate " /\\ " (map ppCond cs) ++ " => " ++ ppResult r ++ "."
ppRule (Fact r)    = ppResult r ++ "."

ppNormalCond :: NormalCond -> String
ppNormalCond (NormalCond d neg a) =
  let prevs = replicate d '@'
      negStr = if neg then "~" else ""
  in prevs ++ negStr ++ ppAtom a

ppNormalRule :: NormalRule -> String
ppNormalRule (NormalRule [] h) = ppAtom h ++ "."
ppNormalRule (NormalRule cs h) =
  intercalate " /\\ " (map ppNormalCond cs) ++ " => " ++ ppAtom h ++ "."

ppProgram :: Program -> String
ppProgram prog = unlines $
  map ppPatternFunc (progPatternFuncs prog) ++
  map ppRule (progRules prog)

ppPatternFunc :: PatternFunc -> String
ppPatternFunc (PatternFunc f args body) =
  f ++ "(" ++ intercalate ", " (map ppTerm args) ++ ") -> " ++ ppTerm body ++ "."

ppNormalProgram :: NormalProgram -> String
ppNormalProgram = unlines . map ppNormalRule
