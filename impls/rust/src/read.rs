use std::cmp::Ordering;
use std::iter::Peekable;

use self::special_string::*;

// Note
//  - token列を読む関数はread, astを加工する関数はparseから始まる
//  - 基本的にdelimiterの開始側を消費するのは呼び出し元の責任、終了側は呼び出し先の責任

macro_rules! regex {
    ($re:literal $(,)?) => {{
        static RE: std::sync::OnceLock<regex::Regex> = std::sync::OnceLock::new();
        RE.get_or_init(|| regex::Regex::new($re).unwrap())
    }};
}

pub fn read_str(input: &str) -> Result<Ast, SyntaxError> {
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
pub enum Kind {
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
pub enum Specials {
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

impl Symbol {
    #[inline]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[derive(Debug, Clone)]
pub enum SpecialForms {
    Def(Symbol, Ast),
    Do(Vec<Ast>),
    If(Ast, Ast, Ast),
    Let(Vec<(Symbol, Ast)>, Ast),
    Fn(Vec<Symbol>, Option<Symbol>, Ast),
}

pub enum SyntaxError {
    UnexpectedEOF,
    UnexpectedDelimiter(Kind),
    UnexpectedSpecial(Specials),
    Unclosed(Enclosure),
    OddNumberOfMap,
    OddNumberBindings,
    TooFewArgs(Specials),
    TooManyArgs(Specials),
    NotSymbol(MustBeSymbol),
    NotVector(MustBeVector),
    MisplacedAmpersand,
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

pub enum MustBeSymbol {
    DefFirstArg,
    LetBoundVar,
    FnParams,
}

pub enum MustBeVector {
    LetBindings,
    FnParams,
}

fn read_form<I>(tokens: &mut Peekable<I>) -> Result<Ast, SyntaxError>
where
    I: Iterator<Item = Token>,
{
    match tokens.next().ok_or(SyntaxError::UnexpectedEOF)? {
        Token::NIL => Ok(Ast::Nil),
        Token::BOOL(b) => Ok(Ast::Bool(b)),
        Token::NUM(n) => Ok(Ast::Num(n)),
        Token::STR(s) => Ok(Ast::Str(
            s.try_into()
                .map_err(|_| SyntaxError::Unclosed(Enclosure::Quote))?,
        )),
        Token::SYM(s) => Ok(Ast::Sym(Symbol(s))),
        Token::KEYWORD(s) => Ok(Ast::Keyword(s)),
        Token::BRACKET(Kind::Paren, State::Open) => {
            if let Some(&Token::SPECIAL(s)) = tokens.peek() {
                Ok(Ast::SpecialForm(Box::new(read_special_form(tokens, s)?)))
            } else {
                // TODO: 先頭がsymbolでない場合はエラーにする？
                read_seq(tokens, Kind::Paren).map(Ast::List)
            }
        }
        Token::BRACKET(Kind::Square, State::Open) => {
            read_seq(tokens, Kind::Square).map(Ast::Vector)
        }
        Token::BRACKET(Kind::Curly, State::Open) => read_map(tokens).map(Ast::Map),
        Token::MACRO(_c) => todo!("impl read_macro"),
        Token::SPECIAL(s) => Err(SyntaxError::UnexpectedSpecial(s)),
        Token::BRACKET(k, State::Close) => Err(SyntaxError::UnexpectedDelimiter(k)),
    }
}

fn read_seq<I>(tokens: &mut Peekable<I>, kind: Kind) -> Result<Vec<Ast>, SyntaxError>
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
            None => return Err(SyntaxError::Unclosed(kind.into())),
        }
    }
}

#[inline]
fn read_map<I>(tokens: &mut Peekable<I>) -> Result<Vec<(Ast, Ast)>, SyntaxError>
where
    I: Iterator<Item = Token>,
{
    let mut pairs = Vec::new();
    loop {
        match tokens.peek() {
            Some(Token::BRACKET(Kind::Curly, State::Close)) => {
                tokens.next();
                return Ok(pairs);
            }
            Some(_) => {
                pairs.push((
                    read_form(tokens)?,
                    match tokens.peek() {
                        Some(Token::BRACKET(Kind::Curly, State::Close)) => {
                            return Err(SyntaxError::OddNumberOfMap);
                        }
                        Some(_) => read_form(tokens)?,
                        None => return Err(SyntaxError::Unclosed(Enclosure::CurlyBracket)),
                    },
                ));
            }
            None => return Err(SyntaxError::Unclosed(Enclosure::CurlyBracket)),
        }
    }
}

fn read_special_form<I>(tokens: &mut Peekable<I>, s: Specials) -> Result<SpecialForms, SyntaxError>
where
    I: Iterator<Item = Token>,
{
    tokens.next(); // consume special token
    let seq = read_seq(tokens, Kind::Paren)?;
    Ok(match s {
        Specials::DEF => parse_binary_special_form(
            Specials::DEF,
            |sym, exp| {
                if let Ast::Sym(s) = sym {
                    Ok(SpecialForms::Def(s, exp))
                } else {
                    Err(SyntaxError::NotSymbol(MustBeSymbol::DefFirstArg))
                }
            },
            seq,
        )?,
        Specials::DO => SpecialForms::Do(seq),
        Specials::IF => match seq.len() {
            ..=1 => return Err(SyntaxError::TooFewArgs(Specials::IF)),
            2 => {
                let [cond, then] = unsafe { seq.try_into().unwrap_unchecked() };
                SpecialForms::If(cond, then, Ast::Nil)
            }
            3 => {
                let [cond, then, else_] = unsafe { seq.try_into().unwrap_unchecked() };
                SpecialForms::If(cond, then, else_)
            }
            4.. => return Err(SyntaxError::TooManyArgs(Specials::IF)),
        },
        Specials::LET => parse_binary_special_form(
            Specials::LET,
            |bindings, body| {
                let Ast::Vector(bindings) = bindings else {
                    return Err(SyntaxError::NotVector(MustBeVector::LetBindings));
                };
                Ok(SpecialForms::Let(parse_bindings(bindings)?, body))
            },
            seq,
        )?,
        Specials::FN => parse_binary_special_form(
            Specials::FN,
            |params, body| {
                let Ast::Vector(params) = params else {
                    return Err(SyntaxError::NotVector(MustBeVector::FnParams));
                };
                let (params, variadic) = parse_params(params)?;
                Ok(SpecialForms::Fn(params, variadic, body))
            },
            seq,
        )?,
    })
}

fn parse_binary_special_form<F>(
    s: Specials,
    parse_pair: F,
    args: Vec<Ast>,
) -> Result<SpecialForms, SyntaxError>
where
    F: FnOnce(Ast, Ast) -> Result<SpecialForms, SyntaxError>,
{
    match args.len().cmp(&2) {
        Ordering::Less => Err(SyntaxError::TooFewArgs(s)),
        Ordering::Equal => Ok({
            let [a, b] = unsafe { args.try_into().unwrap_unchecked() };
            parse_pair(a, b)?
        }),
        Ordering::Greater => Err(SyntaxError::TooManyArgs(s)),
    }
}

#[inline]
fn parse_bindings(mut v: Vec<Ast>) -> Result<Vec<(Symbol, Ast)>, SyntaxError> {
    let mut result = Vec::with_capacity(v.len() / 2);
    while let Some(sym) = v.pop() {
        if let Ast::Sym(s) = sym {
            result.push((s, v.pop().ok_or(SyntaxError::OddNumberBindings)?));
        } else {
            return Err(SyntaxError::NotSymbol(MustBeSymbol::LetBoundVar));
        }
    }
    Ok(result)
}

#[inline]
fn parse_params(v: Vec<Ast>) -> Result<(Vec<Symbol>, Option<Symbol>), SyntaxError> {
    let (mut rev_params, variadic) = v.rchunks(2).enumerate().try_fold(
        (Vec::with_capacity(v.len()), None),
        // NOTE: vを逆順でチェック => [a b c & d] ~> [& d], [b c], [a]
        |(mut acc, v), (i, chunk)| match chunk {
            [Ast::Sym(s), Ast::Sym(t)] => match (i, (s.as_str(), t.as_str())) {
                (_, (_, "&")) | (1.., ("&", _)) => Err(SyntaxError::MisplacedAmpersand),
                (0, ("&", _)) => Ok((acc, Some(t.clone()))),
                _ => {
                    acc.push(t.clone());
                    acc.push(s.clone());
                    Ok((acc, v))
                }
            },
            [Ast::Sym(s)] => match s.as_str() {
                "&" => Err(SyntaxError::MisplacedAmpersand),
                _ => {
                    acc.push(s.clone());
                    Ok((acc, v))
                }
            },
            _ => Err(SyntaxError::NotSymbol(MustBeSymbol::FnParams)),
        },
    )?;
    rev_params.reverse();
    Ok((rev_params, variadic))
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
