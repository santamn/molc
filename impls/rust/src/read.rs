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
    DEF,
    DO,
    IF,
    LET,
    FN,
    ROUND(Bracket),  // ()
    SQUARE(Bracket), // []
    CURLY(Bracket),  // {}
    MACRO(MacroChar),
}

enum Bracket {
    Open,
    Close,
}

// enum Kind {
//     Paren,  // ()
//     Square, // []
//     Curly,  // {}
// }

// enum State {
//     Open,
//     Close,
// }

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
        // cap[0]はマッチした文字列全体, cap[1]はグループ化した文字列=空白以外の部分
        .map(|cap| unsafe { cap.get(1).unwrap_unchecked() }.as_str())
        .filter(|token| !token.starts_with(';')) // コメント行を除外
        .map(|token| read_token(token))
}

fn read_token(token: &str) -> Token {
    match token {
        "nil" => Token::NIL,
        "true" => Token::BOOL(true),
        "false" => Token::BOOL(false),
        "def" => Token::DEF,
        "do" => Token::DO,
        "if" => Token::IF,
        "let" => Token::LET,
        "fn" => Token::FN,
        "(" => Token::ROUND(Bracket::Open),
        ")" => Token::ROUND(Bracket::Close),
        "[" => Token::SQUARE(Bracket::Open),
        "]" => Token::SQUARE(Bracket::Close),
        "{" => Token::CURLY(Bracket::Open),
        "}" => Token::CURLY(Bracket::Close),
        "'" => Token::MACRO(MacroChar::Quote),
        "`" => Token::MACRO(MacroChar::Quasiquote),
        "~" => Token::MACRO(MacroChar::Unquote),
        "~@" => Token::MACRO(MacroChar::UnquoteSplicing),
        "@" => Token::MACRO(MacroChar::Deref),
        "#" => Token::MACRO(MacroChar::Dispatch),
        "^" => Token::MACRO(MacroChar::Meta),
        _ => {
            if let Ok(n) = token.parse::<i64>() {
                Token::NUM(n)
            } else if token.starts_with('"') {
                Token::STR(MaybeUncloedString::new(token.to_string()))
            } else if token.starts_with(':') {
                Token::KEYWORD(token[1..].to_string())
            } else {
                Token::SYM(token.to_string())
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

#[derive(Debug, Clone, Copy)]
enum ParseError {
    UnexpectedEOF,
    Unclosed(Enclosure),
}

#[derive(Debug, Clone, Copy)]
enum Enclosure {
    Paren,         // ()
    SquareBracket, // []
    CurlyBracket,  // {}
    Quote,         // ""
}

fn read_ast<I>(next: Token, rest: &mut I) -> Result<Ast, ParseError>
where
    I: Iterator<Item = Token>,
{
    match next {
        Token::NIL => Ok(Ast::Nil),
        Token::BOOL(b) => Ok(Ast::Bool(b)),
        Token::NUM(n) => Ok(Ast::Num(n)),
        Token::STR(s) => Ok(Ast::Str(
            s.try_into()
                .map_err(|_| ParseError::Unclosed(Enclosure::Quote))?,
        )),
        Token::SYM(s) => Ok(Ast::Sym(Symbol(s))),
        Token::KEYWORD(s) => Ok(Ast::Keyword(s)),
        // Token::DEF => read_def(rest),
        // Token::DO => read_do(rest),
        // Token::IF => read_if(rest),
        // Token::LET => read_let(rest),
        // Token::FN => read_fn(rest),
        Token::ROUND(Bracket::Open) => match rest.next() {
            Some(Token::DEF) => Ok(Ast::SpecialForm(Box::new(read_def(rest)?))),
            _ => read_list(rest),
        },
        // Token::SQUARE(Bracket::Open) => read_list(rest).map(Ast::Vector),
        // Token::CURLY(Bracket::Open) => read_map(rest).map(Ast::Map),
        // Token::MACRO(c) => read_macro(c, rest),
        _ => unreachable!(),
    }
}

fn read_def<I>(tokens: &mut I) -> Result<SpecialForms, ParseError>
where
    I: Iterator<Item = Token>,
{
    let sym = match tokens.next() {
        Some(Token::SYM(s)) => s,
        _ => return Err(ParseError::UnexpectedEOF),
    };
    Ok(SpecialForms::Def(
        read_ast(tokens.next().ok_or(ParseError::UnexpectedEOF)?, tokens)?,
        read_ast(tokens.next().ok_or(ParseError::UnexpectedEOF)?, tokens)?,
    ))
}

fn read_list<I>(tokens: &mut I) -> Result<Ast, ParseError>
where
    I: Iterator<Item = Token>,
{
    let mut list = Vec::new();
    loop {
        match tokens.next() {
            Some(Token::ROUND(Bracket::Close)) => return Ok(Ast::List(list)),
            Some(token) => list.push(read_ast(token, tokens)?),
            None => return Err(ParseError::Unclosed(Enclosure::Paren)),
        }
    }
}
