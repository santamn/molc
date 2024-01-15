use std::iter::Peekable;

use self::special_string::*;

macro_rules! regex {
    ($re:literal $(,)?) => {{
        static RE: std::sync::OnceLock<regex::Regex> = std::sync::OnceLock::new();
        RE.get_or_init(|| regex::Regex::new($re).unwrap())
    }};
}

mod special_string {
    pub struct MaybeUncloedString(String);

    impl MaybeUncloedString {
        #[inline]
        pub fn new(s: String) -> Self {
            Self(s)
        }
    }

    #[derive(Debug)]
    pub struct EscapedString(String);

    impl TryFrom<MaybeUncloedString> for EscapedString {
        type Error = ();

        fn try_from(value: MaybeUncloedString) -> Result<Self, Self::Error> {
            let v = value.0;
            // クオートであるべき場所をスキップ
            let (s, is_end_escaped) = v[1..v.len() - 1].chars().fold(
                (String::with_capacity(v.len() - 2), false),
                |(mut s, escaped), c| {
                    if escaped {
                        s.push(match c {
                            'n' => '\n',
                            't' => '\t',
                            'r' => '\r',
                            _ => c,
                        });
                        (s, false)
                    } else if c == '\\' {
                        (s, true)
                    } else {
                        s.push(c);
                        (s, false)
                    }
                },
            );

            if !is_end_escaped && v.ends_with('"') {
                Ok(Self(s))
            } else {
                Err(())
            }
        }
    }
}

#[allow(non_camel_case_types)]
enum Token {
    NIL,
    BOOL(bool),
    NUM(i64),
    STR(MaybeUncloedString),
    SYM(String),
    KEYWORD(String),
    SPECIAL(Specials),
    BRACKET(Kind, State),
    MACRO(MacroChar),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Paren,  // ()
    Square, // []
    Curly,  // {}
}

enum State {
    Open,
    Close,
}

#[derive(Debug, Clone, Copy)]
enum Specials {
    DEF,
    DO,
    IF,
    LET,
    FN,
}

enum MacroChar {
    Quote,           // '
    Quasiquote,      // `
    Unquote,         // ~
    UnquoteSplicing, // ~@
    Deref,           // @
    Dispatch,        // #
    Meta,            // ^
}

fn tokenize<I>(input: &str) -> impl Iterator<Item = Token> + '_ {
    regex!(r#"[\s,]*(;.*|~@|[\[\]{}()'`~^@]|"(?:\\.|[^\\"])*"?|[^\s\[\]{}()'"`,;]*)"#)
        .captures_iter(input)
        // cap[0]:マッチした文字列全体, cap[1]:グループ化した文字列=空白以外の部分
        .map(|cap| unsafe { cap.get(1).unwrap_unchecked() }.as_str())
        .filter(|token| !token.starts_with(';')) // コメント行を除外
        .map(|t| token(t))
}

fn token(s: &str) -> Token {
    match s {
        "nil" => Token::NIL,
        "true" => Token::BOOL(true),
        "false" => Token::BOOL(false),
        "def" => Token::SPECIAL(Specials::DEF),
        "do" => Token::SPECIAL(Specials::DO),
        "if" => Token::SPECIAL(Specials::IF),
        "let" => Token::SPECIAL(Specials::LET),
        "fn" => Token::SPECIAL(Specials::FN),
        "(" => Token::BRACKET(Kind::Paren, State::Open),
        ")" => Token::BRACKET(Kind::Paren, State::Close),
        "[" => Token::BRACKET(Kind::Square, State::Open),
        "]" => Token::BRACKET(Kind::Square, State::Close),
        "{" => Token::BRACKET(Kind::Curly, State::Open),
        "}" => Token::BRACKET(Kind::Curly, State::Close),
        "'" => Token::MACRO(MacroChar::Quote),
        "`" => Token::MACRO(MacroChar::Quasiquote),
        "~" => Token::MACRO(MacroChar::Unquote),
        "~@" => Token::MACRO(MacroChar::UnquoteSplicing),
        "@" => Token::MACRO(MacroChar::Deref),
        "#" => Token::MACRO(MacroChar::Dispatch),
        "^" => Token::MACRO(MacroChar::Meta),
        _ => {
            if let Ok(n) = s.parse::<i64>() {
                Token::NUM(n)
            } else if s.starts_with('"') {
                Token::STR(MaybeUncloedString::new(s.to_string()))
            } else if s.starts_with(':') {
                Token::KEYWORD(s[1..].to_string())
            } else {
                Token::SYM(s.to_string())
            }
        }
    }
}

#[derive(Debug)]
pub struct Symbol(String);

#[derive(Debug)]
enum Ast {
    Nil,
    Bool(bool),
    Num(i64),
    Str(EscapedString),
    Sym(Symbol),
    Keyword(String),
    List(Vec<Ast>),
    Vector(Vec<Ast>),
    Map(Vec<(Ast, Ast)>),
    SpecialForm(Box<SpecialForms>),
}

#[derive(Debug)]
enum SpecialForms {
    Def(Symbol, Ast),
    Do(Vec<Ast>),
    If(Ast, Ast, Ast),
    Let(Vec<(Symbol, Ast)>, Ast),
    Fn(Vec<Symbol>, Option<Symbol>, Ast),
}

#[derive(Debug, Clone)]
enum ParseError {
    UnexpectedEOF,
    Unclosed(Enclosure),
    Def(String),
}

#[derive(Debug, Clone, Copy)]
enum Enclosure {
    Paren,         // ()
    SquareBracket, // []
    CurlyBracket,  // {}
    Quote,         // ""
}

impl From<Kind> for Enclosure {
    fn from(kind: Kind) -> Self {
        match kind {
            Kind::Paren => Enclosure::Paren,
            Kind::Square => Enclosure::SquareBracket,
            Kind::Curly => Enclosure::CurlyBracket,
        }
    }
}

fn read_form<I>(tokens: &mut Peekable<I>) -> Result<Ast, ParseError>
where
    I: Iterator<Item = Token>,
{
    match tokens.next().ok_or(ParseError::UnexpectedEOF)? {
        Token::NIL => Ok(Ast::Nil),
        Token::BOOL(b) => Ok(Ast::Bool(b)),
        Token::NUM(n) => Ok(Ast::Num(n)),
        Token::STR(s) => Ok(Ast::Str(
            s.try_into()
                .map_err(|_| ParseError::Unclosed(Enclosure::Quote))?,
        )),
        Token::SYM(s) => Ok(Ast::Sym(Symbol(s))),
        Token::KEYWORD(s) => Ok(Ast::Keyword(s)),
        Token::BRACKET(Kind::Paren, State::Open) => {
            if let Some(&Token::SPECIAL(s)) = tokens.peek() {
                Ok(Ast::SpecialForm(Box::new(read_special_form(s, tokens)?)))
            } else {
                read_seq(tokens, Kind::Paren).map(Ast::List)
            }
        }
        Token::BRACKET(Kind::Square, State::Open) => {
            read_seq(tokens, Kind::Square).map(Ast::Vector)
        }
        // Token::CURLY(Bracket::Open) => read_map(rest).map(Ast::Map),
        // Token::MACRO(c) => read_macro(c, rest),
        _ => todo!(),
    }
}

fn read_seq<I>(tokens: &mut Peekable<I>, kind: Kind) -> Result<Vec<Ast>, ParseError>
where
    I: Iterator<Item = Token>,
{
    let mut seq = Vec::new();
    loop {
        match tokens.peek() {
            Some(&Token::BRACKET(k, State::Close)) if k == kind => {
                tokens.next();
                return Ok(seq);
            }
            Some(_) => seq.push(read_form(tokens)?),
            None => return Err(ParseError::Unclosed(kind.into())),
        }
    }
}

fn read_special_form<I>(
    atom: Specials,
    tokens: &mut Peekable<I>,
) -> Result<SpecialForms, ParseError>
where
    I: Iterator<Item = Token>,
{
    tokens.next(); // skip atom
    let f = match atom {
        Specials::DEF => read_def(tokens),
        // read_seqで")"を処理するためreturn
        Specials::DO => return read_seq(tokens, Kind::Paren).map(SpecialForms::Do),
        Specials::IF => read_if(tokens),
        Specials::LET => read_let(tokens),
        Specials::FN => read_fn(tokens),
    }?;

    if let Some(Token::BRACKET(Kind::Paren, State::Close)) = tokens.next() {
        Ok(f)
    } else {
        Err(ParseError::Unclosed(Enclosure::Paren))
    }
}

fn read_def<I>(tokens: &mut Peekable<I>) -> Result<SpecialForms, ParseError>
where
    I: Iterator<Item = Token>,
{
    let sym = match tokens.next() {
        Some(Token::SYM(s)) => s,
        Some(_) => {
            return Err(ParseError::Def(
                "First argument to def must be a Symbol".to_string(),
            ))
        }
        None => return Err(ParseError::Def("too few arguments to def".to_string())),
    };

    // TODO: 二引数目のエラー処理
    Ok(SpecialForms::Def(Symbol(sym), read_form(tokens)?))
}

// TODO
fn read_if<I>(tokens: &mut Peekable<I>) -> Result<SpecialForms, ParseError>
where
    I: Iterator<Item = Token>,
{
    let cond = read_form(tokens)?;
    let then = read_form(tokens)?;
    let els = read_form(tokens)?;
    Ok(SpecialForms::If(cond, then, els))
}

// TODO
fn read_let<I>(tokens: &mut Peekable<I>) -> Result<SpecialForms, ParseError>
where
    I: Iterator<Item = Token>,
{
    let mut bindings = Vec::new();
    loop {
        match tokens.peek() {
            Some(Token::BRACKET(Kind::Paren, State::Close)) => {
                tokens.next();
                break;
            }
            Some(_) => {
                let sym = match tokens.next() {
                    Some(Token::SYM(s)) => s,
                    Some(_) => {
                        return Err(ParseError::Def(
                            "First argument to def must be a Symbol".to_string(),
                        ))
                    }
                    None => return Err(ParseError::Def("too few arguments to def".to_string())),
                };
                let ast = read_form(tokens)?;
                bindings.push((Symbol(sym), ast));
            }
            None => return Err(ParseError::Unclosed(Enclosure::Paren)),
        }
    }
    let body = read_form(tokens)?;
    Ok(SpecialForms::Let(bindings, body))
}

// TODO
fn read_fn<I>(tokens: &mut Peekable<I>) -> Result<SpecialForms, ParseError>
where
    I: Iterator<Item = Token>,
{
    let mut params = Vec::new();
    loop {
        match tokens.peek() {
            Some(Token::BRACKET(_, State::Close)) => {
                tokens.next();
                break;
            }
            Some(_) => {
                let sym = match tokens.next() {
                    Some(Token::SYM(s)) => s,
                    Some(_) => {
                        return Err(ParseError::Def(
                            "First argument to def must be a Symbol".to_string(),
                        ))
                    }
                    None => return Err(ParseError::Def("too few arguments to def".to_string())),
                };
                params.push(Symbol(sym));
            }
            None => return Err(ParseError::Unclosed(Enclosure::Paren)),
        }
    }
    let rest = match tokens.next() {
        Some(Token::SYM(s)) => Some(Symbol(s)),
        Some(_) => {
            return Err(ParseError::Def(
                "First argument to def must be a Symbol".to_string(),
            ))
        }
        None => None,
    };
    let body = read_form(tokens)?;
    Ok(SpecialForms::Fn(params, rest, body))
}
