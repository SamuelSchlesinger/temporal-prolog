use crate::ast::*;
use num_bigint::BigInt;

#[derive(Clone, Debug, Eq, PartialEq)]
enum Token {
    Ident(String),
    Number(String),
    LParen,
    RParen,
    LBracket,
    RBracket,
    Comma,
    Dot,
    Bar,
    At,
    Tilde,
    Hash,
    Question,
    And,
    Implies,
    Arrow,
    Op(String),
}

pub fn parse_program(source: &str) -> Result<Program, String> {
    let tokens = lex(source)?;
    let mut parser = Parser {
        tokens,
        position: 0,
    };
    let mut rules = Vec::new();
    while !parser.done() {
        rules.push(parser.parse_item()?);
        parser.expect(Token::Dot)?;
    }
    Ok(Program { rules })
}

pub fn parse_atom(source: &str) -> Result<Atom, String> {
    let mut parser = Parser {
        tokens: lex(source)?,
        position: 0,
    };
    let cond = parser.parse_condition()?;
    if !parser.done() {
        return Err(parser.error("unexpected input after atom"));
    }
    match cond {
        Cond::Atom(atom) => Ok(atom),
        _ => Err("expected an atom".into()),
    }
}

fn lex(source: &str) -> Result<Vec<Token>, String> {
    let chars: Vec<char> = source.chars().collect();
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if c == '%' {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }
        let pair = |a: char, b: char| i + 1 < chars.len() && chars[i] == a && chars[i + 1] == b;
        if pair('=', '>') {
            tokens.push(Token::Implies);
            i += 2;
            continue;
        }
        if pair('-', '>') {
            tokens.push(Token::Arrow);
            i += 2;
            continue;
        }
        if pair('/', '\\') {
            tokens.push(Token::And);
            i += 2;
            continue;
        }
        if pair('>', '=') || pair('<', '=') || pair('!', '=') || pair('\\', '=') {
            tokens.push(Token::Op(chars[i..i + 2].iter().collect()));
            i += 2;
            continue;
        }
        match c {
            '(' => tokens.push(Token::LParen),
            ')' => tokens.push(Token::RParen),
            '[' => tokens.push(Token::LBracket),
            ']' => tokens.push(Token::RBracket),
            ',' => tokens.push(Token::Comma),
            '.' => tokens.push(Token::Dot),
            '|' => tokens.push(Token::Bar),
            '@' | '●' | '•' => tokens.push(Token::At),
            '~' | '¬' => tokens.push(Token::Tilde),
            '#' | '■' => tokens.push(Token::Hash),
            '?' | '◆' | '◇' => tokens.push(Token::Question),
            '□' => tokens.push(Token::Ident("always".into())),
            '○' => tokens.push(Token::Ident("next".into())),
            '∧' => tokens.push(Token::And),
            '⇒' => tokens.push(Token::Implies),
            '→' => tokens.push(Token::Arrow),
            '+' | '-' | '*' | '=' | '>' | '<' => tokens.push(Token::Op(c.to_string())),
            _ if c.is_ascii_digit() => {
                let start = i;
                i += 1;
                while i < chars.len() && chars[i].is_ascii_digit() {
                    i += 1;
                }
                tokens.push(Token::Number(chars[start..i].iter().collect()));
                continue;
            }
            _ if c.is_ascii_alphabetic() || c == '_' => {
                let start = i;
                i += 1;
                while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                    i += 1;
                }
                tokens.push(Token::Ident(chars[start..i].iter().collect()));
                continue;
            }
            _ => {
                return Err(format!(
                    "unexpected character {c:?} at byte-like offset {i}"
                ))
            }
        }
        i += 1;
    }
    Ok(tokens)
}

struct Parser {
    tokens: Vec<Token>,
    position: usize,
}

impl Parser {
    fn done(&self) -> bool {
        self.position >= self.tokens.len()
    }
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.position)
    }
    fn bump(&mut self) -> Option<Token> {
        let token = self.tokens.get(self.position).cloned();
        if token.is_some() {
            self.position += 1;
        }
        token
    }
    fn error(&self, message: &str) -> String {
        format!("{message} at token {} ({:?})", self.position, self.peek())
    }
    fn expect(&mut self, expected: Token) -> Result<(), String> {
        let found = self.bump();
        if found == Some(expected.clone()) {
            Ok(())
        } else {
            Err(format!(
                "expected {expected:?}, found {found:?} at token {}",
                self.position.saturating_sub(1)
            ))
        }
    }
    fn take(&mut self, token: &Token) -> bool {
        if self.peek() == Some(token) {
            self.position += 1;
            true
        } else {
            false
        }
    }
    fn keyword(&self, keyword: &str) -> bool {
        matches!(self.peek(), Some(Token::Ident(name)) if name == keyword)
    }
    fn take_keyword(&mut self, keyword: &str) -> bool {
        if self.keyword(keyword) {
            self.position += 1;
            true
        } else {
            false
        }
    }

    fn item_has_implication(&self) -> bool {
        let mut depth = 0isize;
        for token in &self.tokens[self.position..] {
            match token {
                Token::LParen | Token::LBracket => depth += 1,
                Token::RParen | Token::RBracket => depth -= 1,
                Token::Implies if depth == 0 => return true,
                Token::Dot if depth == 0 => return false,
                _ => {}
            }
        }
        false
    }

    fn parse_item(&mut self) -> Result<SourceRule, String> {
        if self.item_has_implication() {
            let cond = self.parse_condition()?;
            self.expect(Token::Implies)?;
            let result = self.parse_result()?;
            Ok(SourceRule::Rule(flatten_and(cond), result))
        } else {
            Ok(SourceRule::Fact(self.parse_result()?))
        }
    }

    fn parse_condition(&mut self) -> Result<Cond, String> {
        let mut left = self.parse_condition_and()?;
        loop {
            if self.take_keyword("since") {
                left = Cond::Since(Box::new(left), Box::new(self.parse_condition_and()?));
            } else if self.take_keyword("after") {
                left = Cond::After(Box::new(left), Box::new(self.parse_condition_and()?));
            } else if self.take_keyword("for") {
                let count = match self.bump() {
                    Some(Token::Number(number)) => {
                        number.parse::<usize>().map_err(|e| e.to_string())?
                    }
                    found => {
                        return Err(format!(
                            "expected positive integer after for, found {found:?}"
                        ))
                    }
                };
                if count == 0 {
                    return Err("the right operand of for must be positive".into());
                }
                left = Cond::For(Box::new(left), count);
            } else {
                break;
            }
        }
        Ok(left)
    }

    fn parse_condition_and(&mut self) -> Result<Cond, String> {
        let first = self.parse_condition_unary()?;
        let mut conditions = vec![first];
        while self.take(&Token::And) {
            conditions.push(self.parse_condition_unary()?);
        }
        Ok(if conditions.len() == 1 {
            conditions.remove(0)
        } else {
            Cond::And(conditions)
        })
    }

    fn parse_condition_unary(&mut self) -> Result<Cond, String> {
        if self.take(&Token::Tilde) {
            return Ok(Cond::Neg(Box::new(self.parse_condition_unary()?)));
        }
        if self.take(&Token::At) {
            return Ok(Cond::Prev(Box::new(self.parse_condition_unary()?)));
        }
        if self.take(&Token::Hash) {
            return Ok(Cond::HasBeen(Box::new(self.parse_condition_unary()?)));
        }
        if self.take(&Token::Question) {
            return Ok(Cond::Once(Box::new(self.parse_condition_unary()?)));
        }
        if self.take_keyword("eventually") {
            return Ok(Cond::Eventually(Box::new(self.parse_condition_unary()?)));
        }
        if self.take(&Token::LParen) {
            let condition = self.parse_condition()?;
            self.expect(Token::RParen)?;
            return Ok(condition);
        }
        self.parse_atomic_condition()
    }

    fn parse_atomic_condition(&mut self) -> Result<Cond, String> {
        let left = self.parse_term(0)?;
        let relational = match self.peek() {
            Some(Token::Op(op))
                if ["=", "!=", "\\=", ">", "<", ">=", "<="].contains(&op.as_str()) =>
            {
                Some(op.clone())
            }
            Some(Token::Ident(op)) if op == "is" => Some(op.clone()),
            _ => None,
        };
        if let Some(op) = relational {
            self.bump();
            let right = self.parse_term(0)?;
            if op == "!=" || op == "\\=" {
                Ok(Cond::Neg(Box::new(Cond::Atom(Atom::new(
                    "=",
                    vec![left, right],
                )))))
            } else {
                Ok(Cond::Atom(Atom::new(op, vec![left, right])))
            }
        } else {
            Ok(Cond::Atom(term_to_atom(left)?))
        }
    }

    fn parse_result(&mut self) -> Result<ResultFormula, String> {
        let mut left = self.parse_result_and()?;
        if self.take_keyword("until") {
            left = ResultFormula::Until(Box::new(left), self.parse_condition()?);
        } else if self.take_keyword("atnext") {
            left = ResultFormula::AtNext(Box::new(left), self.parse_condition()?);
        }
        Ok(left)
    }

    fn parse_result_and(&mut self) -> Result<ResultFormula, String> {
        let first = self.parse_result_unary()?;
        let mut results = vec![first];
        while self.take(&Token::And) {
            results.push(self.parse_result_unary()?);
        }
        Ok(if results.len() == 1 {
            results.remove(0)
        } else {
            ResultFormula::And(results)
        })
    }

    fn parse_result_unary(&mut self) -> Result<ResultFormula, String> {
        if self.take_keyword("always") {
            return Ok(ResultFormula::Always(Box::new(self.parse_result_unary()?)));
        }
        if self.take_keyword("next") {
            return Ok(ResultFormula::Next(Box::new(self.parse_result_unary()?)));
        }
        if self.take(&Token::LParen) {
            let result = self.parse_result()?;
            self.expect(Token::RParen)?;
            return Ok(result);
        }
        let term = self.parse_term(0)?;
        let atom = term_to_atom(term)?;
        if self.take(&Token::Arrow) {
            let body = self.parse_term(0)?;
            Ok(ResultFormula::Reduction(atom.name, atom.terms, body))
        } else {
            Ok(ResultFormula::Atom(atom))
        }
    }

    fn parse_term(&mut self, min_precedence: u8) -> Result<Term, String> {
        let mut left = self.parse_term_prefix()?;
        loop {
            let (op, precedence) = match self.peek() {
                Some(Token::Op(op)) if op == "+" || op == "-" => (op.clone(), 10),
                Some(Token::Op(op)) if op == "*" => (op.clone(), 20),
                Some(Token::Ident(op)) if op == "div" || op == "mod" => (op.clone(), 20),
                _ => break,
            };
            if precedence < min_precedence {
                break;
            }
            self.bump();
            let right = self.parse_term(precedence + 1)?;
            left = Term::Fun(op, vec![left, right]);
        }
        Ok(left)
    }

    fn parse_term_prefix(&mut self) -> Result<Term, String> {
        if self.take(&Token::At) {
            return Ok(Term::Prev(Box::new(self.parse_term_prefix()?)));
        }
        if self.take(&Token::Op("-".into())) {
            return match self.bump() {
                Some(Token::Number(number)) => {
                    Ok(Term::Fun(canonical_integer(&number, true)?, vec![]))
                }
                found => Err(format!("expected a number after unary -, found {found:?}")),
            };
        }
        if self.take(&Token::LParen) {
            let term = self.parse_term(0)?;
            self.expect(Token::RParen)?;
            return Ok(term);
        }
        if self.take(&Token::LBracket) {
            return self.parse_list();
        }
        match self.bump() {
            Some(Token::Number(number)) => {
                Ok(Term::Fun(canonical_integer(&number, false)?, vec![]))
            }
            Some(Token::Ident(name)) => {
                if name.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
                    return Ok(Term::Var(name));
                }
                if self.take(&Token::LParen) {
                    let mut terms = Vec::new();
                    if !self.take(&Token::RParen) {
                        loop {
                            terms.push(self.parse_term(0)?);
                            if self.take(&Token::RParen) {
                                break;
                            }
                            self.expect(Token::Comma)?;
                        }
                    }
                    Ok(Term::Fun(name, terms))
                } else {
                    Ok(Term::Fun(name, vec![]))
                }
            }
            found => Err(format!(
                "expected a term, found {found:?} at token {}",
                self.position.saturating_sub(1)
            )),
        }
    }

    fn parse_list(&mut self) -> Result<Term, String> {
        if self.take(&Token::RBracket) {
            return Ok(Term::Fun("[]".into(), vec![]));
        }
        let mut items = vec![self.parse_term(0)?];
        while self.take(&Token::Comma) {
            items.push(self.parse_term(0)?);
        }
        let mut tail = if self.take(&Token::Bar) {
            self.parse_term(0)?
        } else {
            Term::Fun("[]".into(), vec![])
        };
        self.expect(Token::RBracket)?;
        for item in items.into_iter().rev() {
            tail = Term::Fun(".".into(), vec![item, tail]);
        }
        Ok(tail)
    }
}

fn canonical_integer(source: &str, negative: bool) -> Result<String, String> {
    let magnitude = source
        .parse::<BigInt>()
        .map_err(|error| format!("invalid integer literal {source:?}: {error}"))?;
    Ok(if negative { -magnitude } else { magnitude }.to_string())
}

fn term_to_atom(term: Term) -> Result<Atom, String> {
    match term {
        Term::Fun(name, terms) => Ok(Atom::new(name, terms)),
        _ => Err("predicate position must contain a name or call".into()),
    }
}

fn flatten_and(cond: Cond) -> Vec<Cond> {
    match cond {
        Cond::And(conditions) => conditions.into_iter().flat_map(flatten_and).collect(),
        other => vec![other],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_portable_surface() {
        let program =
            parse_program("append([], X) -> X.\nassign(X) /\\ ~blocked(X) => next chosen(X).")
                .unwrap();
        assert_eq!(program.rules.len(), 2);
    }

    #[test]
    fn parses_lists_and_arithmetic() {
        let atom = parse_atom("value([a,b|T], 2 + 3 * 4)").unwrap();
        assert_eq!(atom.name, "value");
        assert_eq!(atom.terms.len(), 2);
    }

    #[test]
    fn canonicalizes_arbitrary_precision_integer_spellings() {
        let atom = parse_atom("value(0009223372036854775808,-0)").unwrap();
        assert_eq!(
            atom.terms,
            vec![
                Term::Fun("9223372036854775808".into(), vec![]),
                Term::Fun("0".into(), vec![]),
            ]
        );
    }

    #[test]
    fn parses_infix_division_at_multiplicative_precedence() {
        let atom = parse_atom("value(2 + 3 * 4 div 5)").unwrap();
        assert_eq!(
            atom.terms[0],
            Term::Fun(
                "+".into(),
                vec![
                    Term::Fun("2".into(), vec![]),
                    Term::Fun(
                        "div".into(),
                        vec![
                            Term::Fun(
                                "*".into(),
                                vec![Term::Fun("3".into(), vec![]), Term::Fun("4".into(), vec![]),],
                            ),
                            Term::Fun("5".into(), vec![]),
                        ],
                    ),
                ],
            )
        );
    }
}
