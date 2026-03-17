{-# LANGUAGE OverloadedStrings #-}
module TemporalProlog.Parser
  ( parseProgram
  , parseRule
  , parseCond
  , parseAtom
  , parseTerm
  , parseFile
  ) where

import Control.Monad (void)
import Data.Char (isUpper, isAlphaNum, isLower)
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import TemporalProlog.Syntax

type Parser = Parsec Void String
-- Lexer

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "%") empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

integer :: Parser Int
integer = lexeme L.decimal

-- Keywords
reserved :: [String]
reserved = ["since", "after", "for", "until", "atnext", "always", "eventually", "next", "true", "false"]

-- An atom name: starts with lowercase or is a quoted atom
atomName :: Parser Name
atomName = lexeme $ try $ do
  c <- satisfy (\ch -> isLower ch || ch == '_')
  cs <- many (satisfy (\ch -> isAlphaNum ch || ch == '_'))
  let w = c : cs
  if w `elem` reserved
    then fail $ "keyword " ++ show w ++ " cannot be used as a predicate name"
    else return w

-- A variable: starts with uppercase
variable :: Parser Var
variable = lexeme $ try $ do
  c <- satisfy isUpper
  cs <- many (satisfy (\ch -> isAlphaNum ch || ch == '_'))
  return (c : cs)

-- Operators: accept both ASCII and Unicode

opImplies :: Parser ()
opImplies = void (symbol "=>" <|> symbol "\x21D2")  -- ⇒

opAnd :: Parser ()
opAnd = void (symbol "/\\" <|> symbol "\x2227")  -- ∧

opArrow :: Parser ()
opArrow = void (symbol "->" <|> symbol "\x2192")  -- →

opPrev :: Parser Char
opPrev = lexeme (char '@' <|> char '\x25CF')  -- ●

opNeg :: Parser Char
opNeg = lexeme (char '~' <|> char '\x00AC')  -- ¬

opHasBeen :: Parser Char
opHasBeen = lexeme (char '#' <|> char '\x25A0')  -- ■

opOnce :: Parser Char
opOnce = lexeme (char '?' <|> char '\x25C6')  -- ◆

kwAlways :: Parser ()
kwAlways = void (symbol "always" <|> symbol "\x25A1")  -- □

kwEventually :: Parser ()
kwEventually = void (symbol "eventually" <|> symbol "\x25C7")  -- ◇

kwNext :: Parser ()
kwNext = void (symbol "next" <|> symbol "\x25CB")  -- ○

kwSince :: Parser ()
kwSince = void (symbol "since")

kwAfter :: Parser ()
kwAfter = void (symbol "after")

kwFor :: Parser ()
kwFor = void (symbol "for")

kwUntil :: Parser ()
kwUntil = void (symbol "until")

kwAtNext :: Parser ()
kwAtNext = void (symbol "atnext")

-- Term parsing

pTerm :: Parser Term
pTerm = pTermPrev

pTermPrev :: Parser Term
pTermPrev = do
  prevs <- many (try opPrev)
  t <- pTermAtom
  return (foldr (\_ acc -> TPrev acc) t prevs)

pTermAtom :: Parser Term
pTermAtom = choice
  [ pList
  , pNumber
  , try pFunctor
  , TVar <$> variable
  , pAtomTerm
  , between (symbol "(") (symbol ")") pTerm
  ]

pNumber :: Parser Term
pNumber = do
  n <- integer
  return (TFun (show n) [])

pAtomTerm :: Parser Term
pAtomTerm = do
  n <- atomName
  return (TFun n [])

pFunctor :: Parser Term
pFunctor = do
  f <- atomName
  args <- between (symbol "(") (symbol ")") (pTerm `sepBy` symbol ",")
  return (TFun f args)

pList :: Parser Term
pList = between (symbol "[") (symbol "]") pListInner

pListInner :: Parser Term
pListInner = pListElements <|> return (TFun "[]" [])

pListElements :: Parser Term
pListElements = do
  h <- pTerm
  rest <- optional (    (symbol "|" *> pTerm)
                    <|> (symbol "," *> pListElements) )
  case rest of
    Nothing -> return (TFun "." [h, TFun "[]" []])
    Just t  -> return (TFun "." [h, t])

-- Atom parsing

pAtom :: Parser Atom
pAtom = choice
  [ try pInfixAtom
  , try pPrefixAtom
  , pBareAtom
  ]

pPrefixAtom :: Parser Atom
pPrefixAtom = do
  p <- atomName
  args <- between (symbol "(") (symbol ")") (pTerm `sepBy` symbol ",")
  return (Atom p args)

pBareAtom :: Parser Atom
pBareAtom = choice
  [ Atom "true" []  <$ symbol "true"
  , Atom "false" [] <$ symbol "false"
  , do n <- atomName
       return (Atom n [])
  ]

pInfixAtom :: Parser Atom
pInfixAtom = do
  l <- pTerm
  op <- choice
    [ ">=" <$ symbol ">="
    , "<=" <$ symbol "<="
    , ">"  <$ symbol ">"
    , "<"  <$ symbol "<"
    , "="  <$ symbol "="
    ]
  r <- pTerm
  return (Atom op [l, r])

-- Condition parsing

pCond :: Parser Cond
pCond = pCondAnd

pCondAnd :: Parser Cond
pCondAnd = do
  cs <- pCondSinceAfterFor `sepBy1` opAnd
  case cs of
    [c] -> return c
    _   -> return (CAnd cs)

pCondSinceAfterFor :: Parser Cond
pCondSinceAfterFor = do
  c <- pCondUnary
  rest <- optional $ choice
    [ do kwSince; d <- pCondUnary; return (CSince c d)
    , do kwAfter; d <- pCondUnary; return (CAfter c d)
    , do kwFor; n <- integer; return (CFor c n)
    ]
  case rest of
    Nothing -> return c
    Just r  -> return r

pCondUnary :: Parser Cond
pCondUnary = choice
  [ do _ <- opNeg; c <- pCondUnary; return (CNeg c)
  , do _ <- opPrev; c <- pCondUnary; return (CPrev c)
  , do _ <- opHasBeen; c <- pCondUnary; return (CHasBeen c)
  , do _ <- opOnce; c <- pCondUnary; return (COnce c)
  , do kwEventually; c <- pCondUnary; return (CEventually c)
  , pCondAtom
  ]

pCondAtom :: Parser Cond
pCondAtom = choice
  [ CAtom <$> try pAtom
  , between (symbol "(") (symbol ")") pCond
  ]

-- Result parsing

pResult :: Parser Result
pResult = pResultAnd

pResultAnd :: Parser Result
pResultAnd = do
  rs <- pResultUntilAtNext `sepBy1` opAnd
  case rs of
    [r] -> return r
    _   -> return (RAnd rs)

pResultUntilAtNext :: Parser Result
pResultUntilAtNext = do
  r <- pResultUnary
  rest <- optional $ choice
    [ do kwUntil; c <- pCond; return (RUntil r c)
    , do kwAtNext; c <- pCond; return (RAtNext r c)
    ]
  case rest of
    Nothing -> return r
    Just r' -> return r'

pResultUnary :: Parser Result
pResultUnary = choice
  [ do kwAlways; r <- pResultUnary; return (RAlways r)
  , do kwNext; r <- pResultUnary; return (RNext r)
  , pResultAtom
  ]

pResultAtom :: Parser Result
pResultAtom = choice
  [ RAtom <$> try pAtom
  , between (symbol "(") (symbol ")") pResult
  ]

-- Rule parsing

pRule :: Parser Rule
pRule = try pImplicationRule <|> pFactRule

pImplicationRule :: Parser Rule
pImplicationRule = do
  body <- pCond
  opImplies
  hd <- pResult
  void (symbol ".")
  return $ case body of
    CAnd cs -> Rule cs hd
    c       -> Rule [c] hd

pFactRule :: Parser Rule
pFactRule = do
  r <- pResult
  void (symbol ".")
  return (Fact r)

-- Pattern function parsing

pPatternFunc :: Parser PatternFunc
pPatternFunc = try $ do
  f <- atomName
  args <- between (symbol "(") (symbol ")") (pTerm `sepBy` symbol ",")
  opArrow
  body <- pTerm
  void (symbol ".")
  return (PatternFunc f args body)

-- Top-level program

pProgramItem :: Parser (Either PatternFunc Rule)
pProgramItem = (Left <$> try pPatternFunc) <|> (Right <$> pRule)

pProgram :: Parser Program
pProgram = do
  sc
  items <- many pProgramItem
  eof
  let pfs = [pf | Left pf <- items]
      rs  = [r  | Right r  <- items]
  return (Program rs pfs)

-- Public API

parseProgram :: String -> String -> Either (ParseErrorBundle String Void) Program
parseProgram = parse pProgram

parseRule :: String -> String -> Either (ParseErrorBundle String Void) Rule
parseRule = parse (sc *> pRule <* eof)

parseCond :: String -> String -> Either (ParseErrorBundle String Void) Cond
parseCond = parse (sc *> pCond <* eof)

parseAtom :: String -> String -> Either (ParseErrorBundle String Void) Atom
parseAtom = parse (sc *> pAtom <* eof)

parseTerm :: String -> String -> Either (ParseErrorBundle String Void) Term
parseTerm = parse (sc *> pTerm <* eof)

parseFile :: FilePath -> IO (Either (ParseErrorBundle String Void) Program)
parseFile fp = do
  contents <- readFile fp
  return (parseProgram fp contents)
