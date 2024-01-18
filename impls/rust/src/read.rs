use std::iter::Peekable;

use self::special_string::*;

macro_rules! regex {
    ($re:literal $(,)?) => {{
        static RE: std::sync::OnceLock<regex::Regex> = std::sync::OnceLock::new();
        RE.get_or_init(|| regex::Regex::new($re).unwrap())
    }};
}

pub fn read_str(input: &str) -> Result<Ast, ParseError> {
    read_form(&mut lexer(input).peekable())
}

// 8 8888         8 8888888888   `8.`8888.      ,8' 8 8888888888   8 888888888o.
// 8 8888         8 8888          `8.`8888.    ,8'  8 8888         8 8888    `88.
// 8 8888         8 8888           `8.`8888.  ,8'   8 8888         8 8888     `88
// 8 8888         8 8888            `8.`8888.,8'    8 8888         8 8888     ,88
// 8 8888         8 888888888888     `8.`88888'     8 888888888888 8 8888.   ,88'
// 8 8888         8 8888             .88.`8888.     8 8888         8 888888888P'
// 8 8888         8 8888            .8'`8.`8888.    8 8888         8 8888`8b
// 8 8888         8 8888           .8'  `8.`8888.   8 8888         8 8888 `8b.
// 8 8888         8 8888          .8'    `8.`8888.  8 8888         8 8888   `8b.
// 8 888888888888 8 888888888888 .8'      `8.`8888. 8 888888888888 8 8888     `88.

#[allow(clippy::upper_case_acronyms)]
enum Token {
    NIL,
    BOOL(bool),
    NUM(i64),
    STR(MaybeUncloedString),
    SYM(String),
    KEYWORD(String),
    SPECIAL(Specials),
    BRACKET(Kind, State),
    MACRO(MacroChars),
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
#[allow(clippy::upper_case_acronyms)]
enum Specials {
    DEF,
    DO,
    IF,
    LET,
    FN,
}

enum MacroChars {
    Quote,           // '
    Quasiquote,      // `
    Unquote,         // ~
    UnquoteSplicing, // ~@
    Deref,           // @
    Dispatch,        // #
    Meta,            // ^
}

fn lexer(input: &str) -> impl Iterator<Item = Token> + '_ {
    regex!(r#"[\s,]*(;.*|~@|[\[\]{}()'`~^@]|"(?:\\.|[^\\"])*"?|[^\s\[\]{}()'"`,;]*)"#)
        .captures_iter(input)
        // cap[0]:マッチした文字列全体, cap[1]:グループ化した文字列=空白以外の部分
        .map(|cap| unsafe { cap.get(1).unwrap_unchecked() }.as_str())
        .filter(|token| !token.starts_with(';')) // コメント行を除外
        .map(tokenizer)
}

fn tokenizer(s: &str) -> Token {
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
        "'" => Token::MACRO(MacroChars::Quote),
        "`" => Token::MACRO(MacroChars::Quasiquote),
        "~" => Token::MACRO(MacroChars::Unquote),
        "~@" => Token::MACRO(MacroChars::UnquoteSplicing),
        "@" => Token::MACRO(MacroChars::Deref),
        "#" => Token::MACRO(MacroChars::Dispatch),
        "^" => Token::MACRO(MacroChars::Meta),
        _ => {
            if let Ok(n) = s.parse::<i64>() {
                Token::NUM(n)
            } else if let Some(str) = s.strip_prefix('"') {
                Token::STR(MaybeUncloedString::new(str.to_string()))
            } else if let Some(keyword) = s.strip_prefix(':') {
                Token::KEYWORD(keyword.to_string())
            } else {
                Token::SYM(s.to_string())
            }
        }
    }
}

// 8 888888888o      .8.          8 888888888o.     d888888o.   8 8888888888   8 888888888o.
// 8 8888    `88.   .888.         8 8888    `88.  .`8888:' `88. 8 8888         8 8888    `88.
// 8 8888     `88  :88888.        8 8888     `88  8.`8888.   Y8 8 8888         8 8888     `88
// 8 8888     ,88 . `88888.       8 8888     ,88  `8.`8888.     8 8888         8 8888     ,88
// 8 8888.   ,88'.8. `88888.      8 8888.   ,88'   `8.`8888.    8 888888888888 8 8888.   ,88'
// 8 888888888P'.8`8. `88888.     8 888888888P'     `8.`8888.   8 8888         8 888888888P'
// 8 8888      .8' `8. `88888.    8 8888`8b          `8.`8888.  8 8888         8 8888`8b
// 8 8888     .8'   `8. `88888.   8 8888 `8b.    8b   `8.`8888. 8 8888         8 8888 `8b.
// 8 8888    .888888888. `88888.  8 8888   `8b.  `8b.  ;8.`8888 8 8888         8 8888   `8b.
// 8 8888   .8'       `8. `88888. 8 8888     `88. `Y8888P ,88P' 8 888888888888 8 8888     `88.

#[derive(Debug, Clone)]
pub enum Ast {
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Symbol(String);

#[derive(Debug, Clone)]
pub enum SpecialForms {
    Def(Symbol, Ast),
    Do(Vec<Ast>),
    If(Ast, Ast, Ast),
    Let(Vec<(Symbol, Ast)>, Ast),
    Fn(Vec<Symbol>, Option<Symbol>, Ast),
}

pub enum ParseError {
    UnexpectedEOF,
    Unclosed(Enclosure),
    OddNumberOfMap,
    Def(DefError),
    IfTooFewArgs,
}

#[derive(Debug, Clone, Copy)]
pub enum Enclosure {
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

#[derive(Debug, Clone, Copy)]
pub enum DefError {
    TooFewArgs,
    FirstArgMustBeSymbol,
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
        Token::BRACKET(Kind::Curly, State::Open) => {
            let mut m = Vec::new();
            loop {
                match tokens.peek() {
                    Some(&Token::BRACKET(Kind::Curly, State::Close)) => {
                        tokens.next();
                        return Ok(Ast::Map(m));
                    }
                    Some(_) => {
                        m.push((
                            read_form(tokens)?,
                            match read_form(tokens) {
                                Ok(ast) => ast,
                                Err(ParseError::UnexpectedEOF) => {
                                    return Err(ParseError::OddNumberOfMap)
                                }
                                Err(e) => return Err(e),
                            },
                        ));
                    }
                    None => return Err(ParseError::Unclosed(Enclosure::CurlyBracket)),
                }
            }
        }
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
            Some(_) => seq.push(read_form(tokens)?), // Q. ここでUnexpectedEOFになったらどうする？ A. ならない
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
        Some(_) => return Err(ParseError::Def(DefError::FirstArgMustBeSymbol)),
        None => return Err(ParseError::Def(DefError::TooFewArgs)),
    };

    Ok(SpecialForms::Def(
        Symbol(sym),
        match read_form(tokens) {
            Ok(ast) => ast,
            Err(ParseError::UnexpectedEOF) => return Err(ParseError::Def(DefError::TooFewArgs)),
            Err(e) => return Err(e),
        },
    ))
}

fn read_if<I>(tokens: &mut Peekable<I>) -> Result<SpecialForms, ParseError>
where
    I: Iterator<Item = Token>,
{
    let cond = match read_form(tokens) {
        Ok(ast) => ast,
        Err(ParseError::UnexpectedEOF) => return Err(ParseError::IfTooFewArgs),
        Err(e) => return Err(e),
    };
    let then = match read_form(tokens) {
        Ok(ast) => ast,
        Err(ParseError::UnexpectedEOF) => return Err(ParseError::IfTooFewArgs),
        Err(e) => return Err(e),
    };
    let els = match read_form(tokens) {
        Ok(ast) => ast,
        Err(ParseError::UnexpectedEOF) => Ast::Nil,
        Err(e) => return Err(e),
    };

    Ok(SpecialForms::If(cond, then, els))
}

fn read_let<I>(_tokens: &mut Peekable<I>) -> Result<SpecialForms, ParseError>
where
    I: Iterator<Item = Token>,
{
    todo!()
}

fn read_fn<I>(_tokens: &mut Peekable<I>) -> Result<SpecialForms, ParseError>
where
    I: Iterator<Item = Token>,
{
    todo!()
}

mod special_string {
    pub struct MaybeUncloedString(String);

    impl MaybeUncloedString {
        #[inline]
        pub fn new(s: String) -> Self {
            Self(s)
        }
    }

    #[derive(Debug, Clone)]
    pub struct EscapedString(String);

    impl TryFrom<MaybeUncloedString> for EscapedString {
        type Error = ();

        fn try_from(value: MaybeUncloedString) -> Result<Self, Self::Error> {
            let v = value.0.strip_suffix('"').ok_or(())?;
            let (s, is_end_escaped) = v.chars().fold(
                (String::with_capacity(v.len()), false),
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

            if !is_end_escaped {
                Ok(Self(s))
            } else {
                Err(())
            }
        }
    }
}
