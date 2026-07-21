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

/// Parse a complete source program, including the empty program.
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

/// Parse exactly one source rule, including its terminating period.
pub fn parse_rule(source: &str) -> Result<SourceRule, String> {
    let mut parser = Parser {
        tokens: lex(source)?,
        position: 0,
    };
    let rule = parser.parse_item()?;
    parser.expect(Token::Dot)?;
    parser.finish("rule")?;
    Ok(rule)
}

/// Parse exactly one condition formula.
pub fn parse_condition(source: &str) -> Result<Cond, String> {
    let mut parser = Parser {
        tokens: lex(source)?,
        position: 0,
    };
    let condition = parser.parse_condition()?;
    parser.finish("condition")?;
    Ok(condition)
}

/// Parse exactly one result formula.
pub fn parse_result(source: &str) -> Result<ResultFormula, String> {
    let mut parser = Parser {
        tokens: lex(source)?,
        position: 0,
    };
    let result = parser.parse_result()?;
    parser.finish("result")?;
    Ok(result)
}

/// Parse exactly one term.
pub fn parse_term(source: &str) -> Result<Term, String> {
    let mut parser = Parser {
        tokens: lex(source)?,
        position: 0,
    };
    let term = parser.parse_term(0)?;
    parser.finish("term")?;
    Ok(term)
}

/// Parse exactly one atom, including infix built-ins such as `X = Y`.
pub fn parse_atom(source: &str) -> Result<Atom, String> {
    match parse_condition(source)? {
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
    fn finish(&self, construct: &str) -> Result<(), String> {
        if self.done() {
            Ok(())
        } else {
            Err(self.error(&format!("unexpected input after {construct}")))
        }
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
        Term::Fun(name, _) if is_reserved_keyword(&name) => Err(format!(
            "reserved keyword {name:?} cannot be a predicate name"
        )),
        Term::Fun(name, terms) => Ok(Atom::new(name, terms)),
        _ => Err("predicate position must contain a name or call".into()),
    }
}

fn is_reserved_keyword(name: &str) -> bool {
    matches!(
        name,
        "since"
            | "after"
            | "for"
            | "eventually"
            | "always"
            | "until"
            | "atnext"
            | "next"
            | "is"
            | "div"
            | "mod"
    )
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

    fn term(source: &str) -> Result<Term, String> {
        let mut parser = Parser {
            tokens: lex(source)?,
            position: 0,
        };
        let parsed = parser.parse_term(0)?;
        if parser.done() {
            Ok(parsed)
        } else {
            Err(parser.error("unexpected input after term"))
        }
    }

    fn condition(source: &str) -> Result<Cond, String> {
        let mut parser = Parser {
            tokens: lex(source)?,
            position: 0,
        };
        let parsed = parser.parse_condition()?;
        if parser.done() {
            Ok(parsed)
        } else {
            Err(parser.error("unexpected input after condition"))
        }
    }

    fn constant(name: &str) -> Term {
        Term::Fun(name.into(), vec![])
    }

    #[test]
    fn parses_simple_atoms() {
        assert_eq!(parse_atom("foo").unwrap(), Atom::new("foo", vec![]));
        assert_eq!(parse_atom("p(X,Y)").unwrap().terms.len(), 2);
    }

    #[test]
    fn parses_variables() {
        assert_eq!(term("X").unwrap(), Term::Var("X".into()));
        assert_eq!(term("MyVar").unwrap(), Term::Var("MyVar".into()));
    }

    #[test]
    fn parses_numbers() {
        assert_eq!(term("42").unwrap(), constant("42"));
    }

    #[test]
    fn parses_functors() {
        assert_eq!(
            term("f(X,Y)").unwrap(),
            Term::Fun(
                "f".into(),
                vec![Term::Var("X".into()), Term::Var("Y".into())]
            )
        );
    }

    #[test]
    fn parses_empty_and_proper_lists() {
        assert_eq!(term("[]").unwrap(), constant("[]"));
        assert_eq!(
            term("[a,b]").unwrap(),
            Term::Fun(
                ".".into(),
                vec![
                    constant("a"),
                    Term::Fun(".".into(), vec![constant("b"), constant("[]")])
                ]
            )
        );
    }

    #[test]
    fn parses_improper_lists() {
        assert_eq!(
            term("[X|Y]").unwrap(),
            Term::Fun(
                ".".into(),
                vec![Term::Var("X".into()), Term::Var("Y".into())]
            )
        );
    }

    #[test]
    fn parses_previous_terms() {
        assert_eq!(
            term("@X").unwrap(),
            Term::Prev(Box::new(Term::Var("X".into())))
        );
    }

    #[test]
    fn parses_negated_conditions() {
        assert!(matches!(condition("~p(X)"), Ok(Cond::Neg(_))));
    }

    #[test]
    fn parses_previous_conditions() {
        assert!(matches!(condition("@p(X)"), Ok(Cond::Prev(_))));
    }

    #[test]
    fn parses_has_been_conditions() {
        assert!(matches!(condition("#p(X)"), Ok(Cond::HasBeen(_))));
    }

    #[test]
    fn parses_once_and_eventually_conditions() {
        assert!(matches!(condition("?p(X)"), Ok(Cond::Once(_))));
        assert!(matches!(
            condition("eventually p(X)"),
            Ok(Cond::Eventually(_))
        ));
    }

    #[test]
    fn parses_since_after_and_for_conditions() {
        assert!(matches!(condition("a since b"), Ok(Cond::Since(_, _))));
        assert!(matches!(condition("a after b"), Ok(Cond::After(_, _))));
        assert!(matches!(condition("a for 3"), Ok(Cond::For(_, 3))));
    }

    #[test]
    fn conjunction_binds_tighter_than_since_on_the_left() {
        assert_eq!(
            condition("a /\\ b since c").unwrap(),
            Cond::Since(
                Box::new(Cond::And(vec![
                    Cond::Atom(Atom::new("a", vec![])),
                    Cond::Atom(Atom::new("b", vec![])),
                ])),
                Box::new(Cond::Atom(Atom::new("c", vec![])))
            )
        );
    }

    #[test]
    fn conjunction_binds_tighter_than_since_on_the_right() {
        assert_eq!(
            condition("a since b /\\ c").unwrap(),
            Cond::Since(
                Box::new(Cond::Atom(Atom::new("a", vec![]))),
                Box::new(Cond::And(vec![
                    Cond::Atom(Atom::new("b", vec![])),
                    Cond::Atom(Atom::new("c", vec![])),
                ]))
            )
        );
    }

    #[test]
    fn rejects_zero_repetitions() {
        assert!(condition("a for 0").is_err());
    }

    #[test]
    fn parses_implication_and_fact_rules() {
        let program = parse_program("a /\\ b => c. p(X).").unwrap();
        assert!(matches!(program.rules[0], SourceRule::Rule(_, _)));
        assert!(matches!(program.rules[1], SourceRule::Fact(_)));
    }

    #[test]
    fn parses_future_result_operators() {
        let program =
            parse_program("always p. a => q until stop. ready atnext trigger. a => next b.")
                .unwrap();
        assert!(matches!(
            program.rules[0],
            SourceRule::Fact(ResultFormula::Always(_))
        ));
        assert!(matches!(
            program.rules[1],
            SourceRule::Rule(_, ResultFormula::Until(_, _))
        ));
        assert!(matches!(
            program.rules[2],
            SourceRule::Fact(ResultFormula::AtNext(_, _))
        ));
        assert!(matches!(
            program.rules[3],
            SourceRule::Rule(_, ResultFormula::Next(_))
        ));
    }

    #[test]
    fn parses_infix_atoms() {
        assert_eq!(
            condition("X > 5").unwrap(),
            Cond::Atom(Atom::new(">", vec![Term::Var("X".into()), constant("5")]))
        );
        assert!(matches!(condition("X = Y"), Ok(Cond::Atom(_))));
    }

    #[test]
    fn parses_not_equal_as_negated_unification() {
        assert!(matches!(condition("X != Y"), Ok(Cond::Neg(_))));
        assert!(matches!(condition("X \\= Y"), Ok(Cond::Neg(_))));
    }

    #[test]
    fn parses_pattern_function_reductions() {
        let program = parse_program("append([],X) -> X.").unwrap();
        assert!(matches!(
            program.rules[0],
            SourceRule::Fact(ResultFormula::Reduction(_, _, _))
        ));
    }

    #[test]
    fn parses_conditional_pattern_function_reductions() {
        let program = parse_program("enabled(X) => choose(X) -> selected.").unwrap();
        assert!(matches!(
            &program.rules[0],
            SourceRule::Rule(conditions, ResultFormula::Reduction(name, _, body))
                if conditions.len() == 1 && name == "choose" && body == &constant("selected")
        ));
    }

    #[test]
    fn rejects_reserved_keywords_as_predicates() {
        assert!(parse_atom("since").is_err());
        assert!(parse_atom("always").is_err());
        assert!(parse_atom("is").is_err());
        assert!(parse_atom("div").is_err());
    }

    #[test]
    fn parses_empty_programs() {
        assert_eq!(parse_program("").unwrap(), Program { rules: vec![] });
        assert_eq!(parse_program("  \n  ").unwrap(), Program { rules: vec![] });
    }

    #[test]
    fn parses_unicode_operator_aliases() {
        assert!(matches!(condition("¬p"), Ok(Cond::Neg(_))));
        assert!(matches!(condition("●p"), Ok(Cond::Prev(_))));
        assert!(matches!(condition("■p"), Ok(Cond::HasBeen(_))));
        assert!(matches!(condition("◆p"), Ok(Cond::Once(_))));
        assert!(parse_program("a ⇒ ○b.").is_ok());
        assert!(parse_program("□p.").is_ok());
    }

    #[test]
    fn parses_negative_integer_literals() {
        assert_eq!(term("-3").unwrap(), constant("-3"));
        assert_eq!(term("-42").unwrap(), constant("-42"));
    }

    #[test]
    fn rejects_missing_rule_period() {
        assert!(parse_program("p").is_err());
    }

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
