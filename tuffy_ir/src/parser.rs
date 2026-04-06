//! Text format parser for tuffy IR — inverse of `display.rs`.
//!
//! Parses the Cranelift-style text format back into a `Module`.
//! Constructs IR directly (without the `Builder` API) to avoid
//! type-wrapper assertions that would make parsing fragile.
//!
//! Public API: `parse_module(input: &str) -> Result<Module, ParseError>`

use std::collections::HashMap;

use num_bigint::BigInt;

use crate::function::{BasicBlock, BlockArg, CfgNode, Function, Region, RegionKind};
use crate::instruction::{
    AtomicRmwOp, FCmpOp, FloatConst, ICmpOp, Instruction, Op, Operand, Origin,
};
use crate::module::{Module, SymbolId, SymbolTable};
use crate::typed::MemOperand;
use crate::types::{
    Annotation, FloatType, FpRewriteFlags, IntAnnotation, IntSignedness, MemoryOrdering, Type,
    VectorType,
};
use crate::value::{BlockRef, RegionRef, ValueRef};

// ── Error type ──────────────────────────────────────────────────────────────

/// A parse error with location information.
#[derive(Debug, Clone)]
pub struct ParseError {
    pub line: usize,
    pub col: usize,
    pub message: String,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "line {}:{}: {}", self.line, self.col, self.message)
    }
}

impl std::error::Error for ParseError {}

// ── Lexer ───────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq)]
enum Token {
    // Keywords
    Func,
    Region,
    Arrow,     // ->
    Eq,        // =
    Comma,     // ,
    Colon,     // :
    Dot,       // .
    LParen,    // (
    RParen,    // )
    LBrace,    // {
    RBrace,    // }
    LBracket,  // [
    RBracket,  // ]
    Semicolon, // ;
    Percent,   // %
    At,        // @
    Newline,
    // Identifiers and literals
    Ident(String),
    Integer(String), // stored as string to handle negatives and large values
    HexInteger(String),
    /// vN value reference
    Value(u32),
    /// bbN block reference
    Block(u32),
    Eof,
}

struct Lexer<'a> {
    input: &'a [u8],
    pos: usize,
    line: usize,
    col: usize,
}

impl<'a> Lexer<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            input: input.as_bytes(),
            pos: 0,
            line: 1,
            col: 1,
        }
    }

    fn peek_byte(&self) -> Option<u8> {
        self.input.get(self.pos).copied()
    }

    fn advance(&mut self) -> Option<u8> {
        let b = self.input.get(self.pos).copied()?;
        self.pos += 1;
        if b == b'\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
        Some(b)
    }

    fn skip_whitespace_no_newline(&mut self) {
        while let Some(b) = self.peek_byte() {
            if b == b' ' || b == b'\t' || b == b'\r' {
                self.advance();
            } else if b == b'/' && self.input.get(self.pos + 1) == Some(&b'/') {
                // Line comment — skip to end of line but don't consume newline
                while let Some(b) = self.peek_byte() {
                    if b == b'\n' {
                        break;
                    }
                    self.advance();
                }
            } else {
                break;
            }
        }
    }

    fn next_token(&mut self) -> Token {
        self.skip_whitespace_no_newline();
        let Some(b) = self.peek_byte() else {
            return Token::Eof;
        };
        match b {
            b'\n' => {
                self.advance();
                // Collapse consecutive newlines/carriage returns
                while matches!(self.peek_byte(), Some(b'\n') | Some(b'\r')) {
                    self.advance();
                }
                Token::Newline
            }
            b'(' => {
                self.advance();
                Token::LParen
            }
            b')' => {
                self.advance();
                Token::RParen
            }
            b'{' => {
                self.advance();
                Token::LBrace
            }
            b'}' => {
                self.advance();
                Token::RBrace
            }
            b'[' => {
                self.advance();
                Token::LBracket
            }
            b']' => {
                self.advance();
                Token::RBracket
            }
            b',' => {
                self.advance();
                Token::Comma
            }
            b':' => {
                self.advance();
                Token::Colon
            }
            b'.' => {
                self.advance();
                Token::Dot
            }
            b';' => {
                self.advance();
                Token::Semicolon
            }
            b'%' => {
                self.advance();
                Token::Percent
            }
            b'@' => {
                self.advance();
                Token::At
            }
            b'=' => {
                self.advance();
                Token::Eq
            }
            b'-' => {
                if self.input.get(self.pos + 1) == Some(&b'>') {
                    self.advance();
                    self.advance();
                    Token::Arrow
                } else {
                    // Negative number
                    self.advance();
                    let num = self.read_number_str();
                    Token::Integer(format!("-{}", num))
                }
            }
            b'0' if self.input.get(self.pos + 1) == Some(&b'x') => {
                self.advance();
                self.advance();
                let hex = self.read_hex_str();
                Token::HexInteger(hex)
            }
            b'0'..=b'9' => {
                let s = self.read_number_str();
                Token::Integer(s)
            }
            b'v' if self
                .input
                .get(self.pos + 1)
                .is_some_and(|b| b.is_ascii_digit()) =>
            {
                self.advance(); // skip 'v'
                let num_s = self.read_number_str();
                let n: u32 = num_s.parse().unwrap();
                Token::Value(n)
            }
            b'b' if self.input.get(self.pos + 1) == Some(&b'b')
                && self
                    .input
                    .get(self.pos + 2)
                    .is_some_and(|b| b.is_ascii_digit()) =>
            {
                self.advance(); // b
                self.advance(); // b
                let num_s = self.read_number_str();
                let n: u32 = num_s.parse().unwrap();
                Token::Block(n)
            }
            _ if b.is_ascii_alphabetic() || b == b'_' => {
                let ident = self.read_ident();
                match ident.as_str() {
                    "func" => Token::Func,
                    "region" => Token::Region,
                    _ => Token::Ident(ident),
                }
            }
            other => {
                self.advance();
                Token::Ident(String::from(other as char))
            }
        }
    }

    fn read_number_str(&mut self) -> String {
        let mut s = String::new();
        while let Some(b) = self.peek_byte() {
            if b.is_ascii_digit() {
                s.push(b as char);
                self.advance();
            } else {
                break;
            }
        }
        s
    }

    fn read_hex_str(&mut self) -> String {
        let mut s = String::new();
        while let Some(b) = self.peek_byte() {
            if b.is_ascii_hexdigit() {
                s.push(b as char);
                self.advance();
            } else {
                break;
            }
        }
        s
    }

    fn read_ident(&mut self) -> String {
        let mut s = String::new();
        while let Some(b) = self.peek_byte() {
            if b.is_ascii_alphanumeric() || b == b'_' {
                s.push(b as char);
                self.advance();
            } else {
                break;
            }
        }
        s
    }
}

// ── Parser ──────────────────────────────────────────────────────────────────

struct Parser<'a> {
    lexer: Lexer<'a>,
    current: Token,
    /// Map from display value number (vN) → ValueRef
    value_map: HashMap<u32, ValueRef>,
    /// Module-level symbol table (shared across functions)
    symbols: SymbolTable,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        let mut lexer = Lexer::new(input);
        let current = lexer.next_token();
        Self {
            lexer,
            current,
            value_map: HashMap::new(),
            symbols: SymbolTable::new(),
        }
    }

    fn error(&self, msg: impl Into<String>) -> ParseError {
        ParseError {
            line: self.lexer.line,
            col: self.lexer.col,
            message: msg.into(),
        }
    }

    fn advance(&mut self) -> Token {
        std::mem::replace(&mut self.current, self.lexer.next_token())
    }

    fn skip_newlines(&mut self) {
        while self.current == Token::Newline {
            self.advance();
        }
    }

    fn expect(&mut self, expected: &Token) -> Result<Token, ParseError> {
        if std::mem::discriminant(&self.current) == std::mem::discriminant(expected) {
            Ok(self.advance())
        } else {
            Err(self.error(format!("expected {:?}, got {:?}", expected, self.current)))
        }
    }

    fn expect_ident(&mut self) -> Result<String, ParseError> {
        match self.advance() {
            Token::Ident(s) => Ok(s),
            other => Err(self.error(format!("expected identifier, got {:?}", other))),
        }
    }

    fn expect_integer(&mut self) -> Result<String, ParseError> {
        match self.advance() {
            Token::Integer(s) => Ok(s),
            other => Err(self.error(format!("expected integer, got {:?}", other))),
        }
    }

    fn expect_u32(&mut self) -> Result<u32, ParseError> {
        let s = self.expect_integer()?;
        s.parse::<u32>()
            .map_err(|_| self.error(format!("invalid u32: {}", s)))
    }

    fn expect_block_ref(&mut self) -> Result<u32, ParseError> {
        match self.advance() {
            Token::Block(n) => Ok(n),
            other => Err(self.error(format!("expected bbN, got {:?}", other))),
        }
    }

    fn expect_value_num(&mut self) -> Result<u32, ParseError> {
        match self.advance() {
            Token::Value(n) => Ok(n),
            other => Err(self.error(format!("expected vN, got {:?}", other))),
        }
    }

    /// Resolve a display value number to a ValueRef.
    fn resolve_value(&self, num: u32) -> Result<ValueRef, ParseError> {
        self.value_map
            .get(&num)
            .copied()
            .ok_or_else(|| self.error(format!("undefined value v{}", num)))
    }

    /// Intern a symbol name, returning its SymbolId.
    fn intern(&mut self, name: &str) -> SymbolId {
        self.symbols.intern(name)
    }

    /// Read a symbol name after '@': sequence of alphanumeric/underscore/dot/dash chars.
    fn read_symbol_name(&mut self) -> Result<String, ParseError> {
        self.expect(&Token::At)?;
        // The ident may contain dots, so gather a continuous identifier
        let name = self.read_extended_ident()?;
        Ok(name)
    }

    /// Read an extended identifier (allows dots and dashes).
    fn read_extended_ident(&mut self) -> Result<String, ParseError> {
        let mut name = match &self.current {
            Token::Ident(s) => {
                let s = s.clone();
                self.advance();
                s
            }
            // Some keywords may appear as part of names
            Token::Integer(s) => {
                let s = s.clone();
                self.advance();
                s
            }
            // Names can start with a dot (e.g. `.Lvtable.0`)
            Token::Dot => {
                self.advance();
                let suffix = match &self.current {
                    Token::Ident(s) => {
                        let s = s.clone();
                        self.advance();
                        s
                    }
                    Token::Integer(s) => {
                        let s = s.clone();
                        self.advance();
                        s
                    }
                    _ => String::new(),
                };
                format!(".{suffix}")
            }
            other => return Err(self.error(format!("expected name, got {:?}", other))),
        };
        // Continue consuming dots/idents to build a compound name
        while let Token::Dot = &self.current {
            self.advance();
            name.push('.');
            match &self.current {
                Token::Ident(s) => {
                    name.push_str(s);
                    self.advance();
                }
                Token::Integer(s) => {
                    name.push_str(s);
                    self.advance();
                }
                _ => break,
            }
        }
        Ok(name)
    }

    // ── Type parsing ────────────────────────────────────────────────────

    fn parse_type(&mut self) -> Result<Type, ParseError> {
        match &self.current {
            Token::Ident(s) => {
                let s = s.clone();
                match s.as_str() {
                    "int" => {
                        self.advance();
                        Ok(Type::Int)
                    }
                    "bool" => {
                        self.advance();
                        Ok(Type::Bool)
                    }
                    "unit" => {
                        self.advance();
                        Ok(Type::Unit)
                    }
                    "byte" => {
                        self.advance();
                        Ok(Type::Byte(0))
                    }
                    "ptr" => {
                        self.advance();
                        Ok(Type::Ptr(0))
                    }
                    "mem" => {
                        self.advance();
                        Ok(Type::Mem)
                    }
                    "f16" => {
                        self.advance();
                        Ok(Type::Float(FloatType::F16))
                    }
                    "f32" => {
                        self.advance();
                        Ok(Type::Float(FloatType::F32))
                    }
                    "f64" => {
                        self.advance();
                        Ok(Type::Float(FloatType::F64))
                    }
                    "f128" => {
                        self.advance();
                        Ok(Type::Float(FloatType::F128))
                    }
                    "bf16" => {
                        self.advance();
                        Ok(Type::Float(FloatType::BF16))
                    }
                    "vec" => {
                        self.advance();
                        self.expect(&Token::Ident("<".into()))?;
                        // Check for "vscale x N" or just "N"
                        if matches!(&self.current, Token::Ident(s) if s == "vscale") {
                            self.advance(); // vscale
                            self.expect_ident()?; // x
                            let n = self.expect_u32()?;
                            self.expect(&Token::Ident(">".into()))?;
                            Ok(Type::Vec(VectorType::Scalable(n)))
                        } else {
                            let n = self.expect_u32()?;
                            self.expect(&Token::Ident(">".into()))?;
                            Ok(Type::Vec(VectorType::Fixed(n)))
                        }
                    }
                    "struct" => {
                        self.advance();
                        self.expect(&Token::LBrace)?;
                        let mut fields = Vec::new();
                        if self.current != Token::RBrace {
                            fields.push(self.parse_type()?);
                            while self.current == Token::Comma {
                                self.advance();
                                fields.push(self.parse_type()?);
                            }
                        }
                        self.expect(&Token::RBrace)?;
                        Ok(Type::Struct(fields))
                    }
                    _ => Err(self.error(format!("unknown type: {}", s))),
                }
            }
            Token::LBracket => {
                // [type; N]
                self.advance();
                let elem = self.parse_type()?;
                self.expect(&Token::Semicolon)?;
                let count = self.expect_u32()?;
                self.expect(&Token::RBracket)?;
                Ok(Type::Array(Box::new(elem), count))
            }
            other => Err(self.error(format!("expected type, got {:?}", other))),
        }
    }

    // ── Annotation parsing ──────────────────────────────────────────────

    /// Try to parse an annotation after a colon (`:s32`, `:u64`, `:i8`, `:alignN`).
    /// Returns None if no colon follows.
    fn try_parse_annotation(&mut self) -> Result<Option<Annotation>, ParseError> {
        if self.current != Token::Colon {
            return Ok(None);
        }
        self.advance(); // consume ':'
        self.parse_annotation_after_colon().map(Some)
    }

    /// Parse annotation text after the colon has already been consumed.
    fn parse_annotation_after_colon(&mut self) -> Result<Annotation, ParseError> {
        match &self.current {
            Token::Ident(s) => {
                let s = s.clone();
                if let Some(rest) = s.strip_prefix("align") {
                    let n: u32 = rest
                        .parse()
                        .map_err(|_| self.error(format!("invalid align annotation: {}", s)))?;
                    self.advance();
                    Ok(Annotation::Align(n))
                } else if let Some(rest) = s.strip_prefix('s') {
                    let n: u32 = rest
                        .parse()
                        .map_err(|_| self.error(format!("invalid annotation: {}", s)))?;
                    self.advance();
                    Ok(Annotation::Int(IntAnnotation {
                        bit_width: n,
                        signedness: IntSignedness::Signed,
                    }))
                } else if let Some(rest) = s.strip_prefix('u') {
                    let n: u32 = rest
                        .parse()
                        .map_err(|_| self.error(format!("invalid annotation: {}", s)))?;
                    self.advance();
                    Ok(Annotation::Int(IntAnnotation {
                        bit_width: n,
                        signedness: IntSignedness::Unsigned,
                    }))
                } else if let Some(rest) = s.strip_prefix('i') {
                    let n: u32 = rest
                        .parse()
                        .map_err(|_| self.error(format!("invalid annotation: {}", s)))?;
                    self.advance();
                    Ok(Annotation::Int(IntAnnotation {
                        bit_width: n,
                        signedness: IntSignedness::DontCare,
                    }))
                } else {
                    Err(self.error(format!("unknown annotation: {}", s)))
                }
            }
            other => Err(self.error(format!("expected annotation after ':', got {:?}", other))),
        }
    }

    /// Parse `type` optionally followed by `:annotation`.
    fn parse_type_with_annotation(&mut self) -> Result<(Type, Option<Annotation>), ParseError> {
        let ty = self.parse_type()?;
        let ann = self.try_parse_annotation()?;
        Ok((ty, ann))
    }

    // ── Operand parsing ─────────────────────────────────────────────────

    /// Parse a value reference: `vN` optionally followed by `:annotation`.
    fn parse_operand(&mut self) -> Result<Operand, ParseError> {
        let vnum = self.expect_value_num()?;
        let vref = self.resolve_value(vnum)?;
        let ann = self.try_parse_annotation()?;
        Ok(Operand {
            value: vref,
            annotation: ann,
        })
    }

    /// Parse comma-separated operands.
    fn parse_operand_list(&mut self) -> Result<Vec<Operand>, ParseError> {
        let mut ops = vec![self.parse_operand()?];
        while self.current == Token::Comma {
            self.advance();
            ops.push(self.parse_operand()?);
        }
        Ok(ops)
    }

    /// Parse optional parenthesized operand list: `(v0, v1)` or empty.
    fn parse_paren_operands(&mut self) -> Result<Vec<Operand>, ParseError> {
        if self.current != Token::LParen {
            return Ok(Vec::new());
        }
        self.advance(); // (
        if self.current == Token::RParen {
            self.advance();
            return Ok(Vec::new());
        }
        let ops = self.parse_operand_list()?;
        self.expect(&Token::RParen)?;
        Ok(ops)
    }

    /// Parse a branch target: `bbN` or `bbN(v0, v1)`.
    fn parse_branch_target(&mut self) -> Result<(u32, Vec<Operand>), ParseError> {
        let bb_num = self.expect_block_ref()?;
        let args = self.parse_paren_operands()?;
        Ok((bb_num, args))
    }

    // ── ICmpOp / FCmpOp parsing ─────────────────────────────────────────

    fn parse_icmp_op(s: &str) -> Option<ICmpOp> {
        match s {
            "eq" => Some(ICmpOp::Eq),
            "ne" => Some(ICmpOp::Ne),
            "lt" => Some(ICmpOp::Lt),
            "le" => Some(ICmpOp::Le),
            "gt" => Some(ICmpOp::Gt),
            "ge" => Some(ICmpOp::Ge),
            _ => None,
        }
    }

    fn parse_fcmp_op(s: &str) -> Option<FCmpOp> {
        match s {
            "false" => Some(FCmpOp::False),
            "oeq" => Some(FCmpOp::OEq),
            "ogt" => Some(FCmpOp::OGt),
            "oge" => Some(FCmpOp::OGe),
            "olt" => Some(FCmpOp::OLt),
            "ole" => Some(FCmpOp::OLe),
            "one" => Some(FCmpOp::ONe),
            "ord" => Some(FCmpOp::Ord),
            "uno" => Some(FCmpOp::Uno),
            "ueq" => Some(FCmpOp::UEq),
            "ugt" => Some(FCmpOp::UGt),
            "uge" => Some(FCmpOp::UGe),
            "ult" => Some(FCmpOp::ULt),
            "ule" => Some(FCmpOp::ULe),
            "une" => Some(FCmpOp::UNe),
            "true" => Some(FCmpOp::True),
            _ => None,
        }
    }

    fn parse_memory_ordering(s: &str) -> Option<MemoryOrdering> {
        match s {
            "relaxed" => Some(MemoryOrdering::Relaxed),
            "acquire" => Some(MemoryOrdering::Acquire),
            "release" => Some(MemoryOrdering::Release),
            "acqrel" => Some(MemoryOrdering::AcqRel),
            "seqcst" => Some(MemoryOrdering::SeqCst),
            _ => None,
        }
    }

    fn parse_atomic_rmw_op(s: &str) -> Option<AtomicRmwOp> {
        match s {
            "xchg" => Some(AtomicRmwOp::Xchg),
            "add" => Some(AtomicRmwOp::Add),
            "sub" => Some(AtomicRmwOp::Sub),
            "and" => Some(AtomicRmwOp::And),
            "or" => Some(AtomicRmwOp::Or),
            "xor" => Some(AtomicRmwOp::Xor),
            _ => None,
        }
    }

    fn parse_float_type(s: &str) -> Option<FloatType> {
        match s {
            "f16" | "F16" => Some(FloatType::F16),
            "f32" | "F32" => Some(FloatType::F32),
            "f64" | "F64" => Some(FloatType::F64),
            "f128" | "F128" => Some(FloatType::F128),
            "bf16" | "BF16" => Some(FloatType::BF16),
            _ => None,
        }
    }

    // ── Dot suffix parsing ──────────────────────────────────────────────

    /// After an opcode ident, try to consume `.suffix` and return the suffix string.
    fn try_parse_dot_suffix(&mut self) -> Option<String> {
        if self.current == Token::Dot {
            self.advance();
            match &self.current {
                Token::Ident(s) => {
                    let s = s.clone();
                    self.advance();
                    Some(s)
                }
                Token::Integer(s) => {
                    let s = s.clone();
                    self.advance();
                    Some(s)
                }
                _ => None,
            }
        } else {
            None
        }
    }

    /// Parse a dot-suffix as u32 (for width parameters).
    fn parse_dot_u32(&mut self) -> Result<u32, ParseError> {
        self.expect(&Token::Dot)?;
        let s = match &self.current {
            Token::Integer(s) => {
                let s = s.clone();
                self.advance();
                s
            }
            Token::Ident(s) => {
                let s = s.clone();
                self.advance();
                s
            }
            other => return Err(self.error(format!("expected number after '.', got {:?}", other))),
        };
        s.parse::<u32>()
            .map_err(|_| self.error(format!("invalid u32 dot-suffix: {}", s)))
    }

    // ── FP rewrite flags ────────────────────────────────────────────────

    /// Parse optional FP rewrite flags: `reassoc`, `contract`.
    fn parse_fp_rewrite_flags(&mut self) -> FpRewriteFlags {
        let mut flags = FpRewriteFlags::default();
        loop {
            match &self.current {
                Token::Ident(s) if s == "reassoc" => {
                    flags.reassoc = true;
                    self.advance();
                }
                Token::Ident(s) if s == "contract" => {
                    flags.contract = true;
                    self.advance();
                }
                _ => break,
            }
        }
        flags
    }

    // ── Top-level parsing ───────────────────────────────────────────────

    fn parse_module(&mut self) -> Result<Module, ParseError> {
        let mut module = Module::new("parsed");
        let mut functions = Vec::new();

        self.skip_newlines();
        while self.current != Token::Eof {
            match &self.current {
                Token::Ident(s) if s == "data" => {
                    self.parse_static_data(&mut module)?;
                }
                Token::Func => {
                    let func = self.parse_function()?;
                    functions.push(func);
                }
                _ => {
                    return Err(
                        self.error(format!("expected 'func' or 'data', got {:?}", self.current))
                    );
                }
            }
            self.skip_newlines();
        }

        // Transfer symbol table to module
        module.symbols = std::mem::take(&mut self.symbols);

        for func in functions {
            module.add_function(func);
        }

        Ok(module)
    }

    fn parse_static_data(&mut self, module: &mut Module) -> Result<(), ParseError> {
        self.expect(&Token::Ident("data".into()))?;
        let name = self.read_symbol_name()?;
        let sym_id = self.intern(&name);
        self.expect(&Token::Eq)?;
        // Parse string literal — the lexer doesn't handle strings, so we do it manually
        let data = self.parse_string_literal()?;

        // Parse optional relocations: relocs [offset: @sym, ...]
        let mut relocations = Vec::new();
        if matches!(&self.current, Token::Ident(s) if s == "relocs") {
            self.advance(); // consume "relocs"
            self.expect(&Token::LBracket)?;
            while self.current != Token::RBracket {
                let offset_str = self.expect_integer()?;
                let offset: usize = offset_str
                    .parse()
                    .map_err(|_| self.error(format!("invalid relocation offset: {offset_str}")))?;
                self.expect(&Token::Colon)?;
                let sym_name = self.read_symbol_name()?;
                let sym = self.intern(&sym_name);
                relocations.push(crate::module::StaticRelocation {
                    offset,
                    symbol: sym,
                });
                // Optional comma separator
                if self.current == Token::Comma {
                    self.advance();
                }
            }
            self.expect(&Token::RBracket)?;
        }

        module.add_static_data_with_relocs(sym_id, data, relocations);
        Ok(())
    }

    fn parse_string_literal(&mut self) -> Result<Vec<u8>, ParseError> {
        // The opening `"` may have already been consumed by the lexer as a token
        // (since `"` is not a recognized token, the lexer produces Ident("\"")).
        // Check if that happened; otherwise, consume it from raw input.
        let quote_already_consumed = matches!(&self.current, Token::Ident(s) if s == "\"");
        if quote_already_consumed {
            // Lexer already consumed the `"`. Raw position is right after it.
        } else {
            self.lexer.skip_whitespace_no_newline();
            if self.lexer.peek_byte() != Some(b'"') {
                return Err(self.error("expected '\"' for string literal"));
            }
            self.lexer.advance(); // consume opening quote
        }

        let mut data = Vec::new();
        loop {
            match self.lexer.advance() {
                Some(b'"') => break,
                Some(b'\\') => match self.lexer.advance() {
                    Some(b'\\') => data.push(b'\\'),
                    Some(b'"') => data.push(b'"'),
                    Some(b'n') => data.push(b'\n'),
                    Some(b'r') => data.push(b'\r'),
                    Some(b't') => data.push(b'\t'),
                    Some(b'0') => data.push(0),
                    Some(b'x') => {
                        let h1 = self
                            .lexer
                            .advance()
                            .ok_or_else(|| self.error("unexpected EOF in hex escape"))?;
                        let h2 = self
                            .lexer
                            .advance()
                            .ok_or_else(|| self.error("unexpected EOF in hex escape"))?;
                        let val = hex_digit(h1)? * 16 + hex_digit(h2)?;
                        data.push(val);
                    }
                    Some(c) => {
                        return Err(self.error(format!("unknown escape: \\{}", c as char)));
                    }
                    None => return Err(self.error("unexpected EOF in string")),
                },
                Some(b) => data.push(b),
                None => return Err(self.error("unexpected EOF in string")),
            }
        }

        // Advance the parser's current token since we consumed raw bytes
        self.current = self.lexer.next_token();
        Ok(data)
    }

    // ── Function parsing ────────────────────────────────────────────────

    fn parse_function(&mut self) -> Result<Function, ParseError> {
        self.value_map.clear();

        self.expect(&Token::Func)?;
        let name = self.read_symbol_name()?;
        let name_sym = self.intern(&name);

        self.expect(&Token::LParen)?;

        // Parse parameters
        let mut params = Vec::new();
        let mut param_annotations = Vec::new();
        let mut param_names: Vec<Option<SymbolId>> = Vec::new();

        if self.current != Token::RParen {
            loop {
                // Check for %name: type pattern
                let pname = if self.current == Token::Percent {
                    self.advance();
                    let n = self.read_extended_ident()?;
                    self.expect(&Token::Colon)?;
                    Some(n)
                } else {
                    None
                };

                let (ty, ann) = self.parse_type_with_annotation()?;
                params.push(ty);
                param_annotations.push(ann);
                param_names.push(pname.map(|n| self.intern(&n)));

                if self.current == Token::Comma {
                    self.advance();
                } else {
                    break;
                }
            }
        }
        self.expect(&Token::RParen)?;

        // Parse optional return type
        let (ret_ty, ret_annotation) = if self.current == Token::Arrow {
            self.advance();
            let (ty, ann) = self.parse_type_with_annotation()?;
            (Some(ty), ann)
        } else {
            (None, None)
        };

        let mut func = Function::new(
            name_sym,
            params,
            param_annotations,
            param_names,
            ret_ty,
            ret_annotation,
        );

        // Parse body: { ... }
        self.expect(&Token::LBrace)?;
        self.skip_newlines();

        // Create root function region
        let root_region = RegionRef(func.regions.len() as u32);
        func.regions.push(Region {
            kind: RegionKind::Function,
            parent: None,
            entry_block: BlockRef(0),
            children: Vec::new(),
        });
        func.root_region = root_region;

        // First pass: scan to discover all block and value definitions to build the maps
        // We need a two-pass approach, but for simplicity, we do single-pass:
        // forward references to blocks are resolved by index (bbN → BlockRef(N)).
        // Values are assigned as we encounter them.

        self.parse_region_body(&mut func, root_region)?;

        self.expect(&Token::RBrace)?;
        self.skip_newlines();

        Ok(func)
    }

    /// Parse the body of a region (blocks and nested regions).
    fn parse_region_body(
        &mut self,
        func: &mut Function,
        region: RegionRef,
    ) -> Result<(), ParseError> {
        let mut first_block = true;
        loop {
            self.skip_newlines();
            match &self.current {
                Token::Block(_) => {
                    let bref = self.parse_block(func, region)?;
                    if first_block {
                        func.regions[region.index() as usize].entry_block = bref;
                        first_block = false;
                    }
                }
                Token::Region => {
                    self.parse_nested_region(func, region)?;
                }
                Token::RBrace | Token::Eof => break,
                other => {
                    return Err(self.error(format!(
                        "expected block (bbN) or 'region' or '}}', got {:?}",
                        other
                    )));
                }
            }
        }
        Ok(())
    }

    fn parse_nested_region(
        &mut self,
        func: &mut Function,
        parent: RegionRef,
    ) -> Result<(), ParseError> {
        self.expect(&Token::Region)?;
        let kind_str = self.expect_ident()?;
        let kind = match kind_str.as_str() {
            "loop" => RegionKind::Loop,
            "plain" => RegionKind::Plain,
            "function" => RegionKind::Function,
            _ => return Err(self.error(format!("unknown region kind: {}", kind_str))),
        };

        self.expect(&Token::LBrace)?;

        let rref = RegionRef(func.regions.len() as u32);
        func.regions.push(Region {
            kind,
            parent: Some(parent),
            entry_block: BlockRef(0),
            children: Vec::new(),
        });

        // Register as child of parent region
        func.regions[parent.index() as usize]
            .children
            .push(CfgNode::Region(rref));

        self.parse_region_body(func, rref)?;
        self.expect(&Token::RBrace)?;

        Ok(())
    }

    fn parse_block(
        &mut self,
        func: &mut Function,
        region: RegionRef,
    ) -> Result<BlockRef, ParseError> {
        let bb_num = self.expect_block_ref()?;

        // Parse optional block arguments: (v0: type, v1: type)
        let arg_start = func.block_args.len() as u32;
        let mut arg_count = 0u32;

        if self.current == Token::LParen {
            self.advance();
            if self.current != Token::RParen {
                loop {
                    let vnum = self.expect_value_num()?;
                    self.expect(&Token::Colon)?;
                    let (ty, ann) = self.parse_type_with_annotation()?;
                    let vref = ValueRef::block_arg(func.block_args.len() as u32);
                    func.block_args.push(BlockArg {
                        ty,
                        annotation: ann,
                        use_list_head: None,
                    });
                    self.value_map.insert(vnum, vref);
                    arg_count += 1;

                    if self.current == Token::Comma {
                        self.advance();
                    } else {
                        break;
                    }
                }
            }
            self.expect(&Token::RParen)?;
        }

        self.expect(&Token::Colon)?;

        // Create the block
        let bref = BlockRef(func.blocks.len() as u32);

        func.blocks.push(BasicBlock {
            parent_region: region,
            arg_start,
            arg_count,
            first_inst: None,
            last_inst: None,
            inst_count: 0,
        });

        // Register as child of region
        func.regions[region.index() as usize]
            .children
            .push(CfgNode::Block(bref));

        // Verify block number matches
        // (we allow any numbering — the bb_num is display-only)
        let _ = bb_num;

        // Parse instructions until next block/region/close-brace
        self.skip_newlines();
        loop {
            match &self.current {
                Token::Block(_) | Token::Region | Token::RBrace | Token::Eof => break,
                _ => {
                    self.parse_instruction(func, bref)?;
                    self.skip_newlines();
                }
            }
        }

        Ok(bref)
    }

    // ── Instruction parsing ─────────────────────────────────────────────

    fn parse_instruction(
        &mut self,
        func: &mut Function,
        block: BlockRef,
    ) -> Result<(), ParseError> {
        // Terminators have no result binding:
        //   ret, br, brif, continue, region_yield, unreachable, trap
        match &self.current {
            Token::Ident(s)
                if matches!(
                    s.as_str(),
                    "ret" | "br" | "brif" | "continue" | "region_yield" | "unreachable" | "trap"
                ) =>
            {
                return self.parse_terminator(func, block);
            }
            _ => {}
        }

        // Check for multi-result: `v0: type, v1: type = opcode ...`
        // or single-result: `v0: type = opcode ...`
        // or multi-result with secondary annotation: `v0: mem, v1: int:s32 = ...`

        // Parse first value binding
        let v0_num = self.expect_value_num()?;
        self.expect(&Token::Colon)?;
        let (ty0, ann0) = self.parse_type_with_annotation()?;

        // Check for second value binding (multi-result)
        let multi_result = if self.current == Token::Comma {
            // Peek ahead: is the next token a value (vN)?
            // In multi-result, we have `v0: type, v1: type = ...`
            // But in operand lists we also have commas. The key distinction:
            // after the comma, if we see vN followed by : and a type, it's multi-result.
            // We can check by looking at the token pattern.
            let saved_pos = self.lexer.pos;
            let saved_line = self.lexer.line;
            let saved_col = self.lexer.col;
            let saved_current = self.current.clone();

            self.advance(); // consume comma

            if let Token::Value(v1_num) = self.current.clone() {
                // Peek further: is there a colon after?
                let _saved2_pos = self.lexer.pos;
                let _saved2_line = self.lexer.line;
                let _saved2_col = self.lexer.col;
                let _saved2_current = self.current.clone();

                self.advance(); // consume vN

                if self.current == Token::Colon {
                    // Multi-result pattern! Continue parsing.
                    self.advance(); // consume ':'
                    let (ty1, ann1) = self.parse_type_with_annotation()?;
                    Some((v1_num, ty1, ann1))
                } else {
                    // Not multi-result. Restore.
                    self.lexer.pos = saved_pos;
                    self.lexer.line = saved_line;
                    self.lexer.col = saved_col;
                    self.current = saved_current;
                    None
                }
            } else {
                // Not multi-result. Restore.
                self.lexer.pos = saved_pos;
                self.lexer.line = saved_line;
                self.lexer.col = saved_col;
                self.current = saved_current;
                None
            }
        } else {
            None
        };

        self.expect(&Token::Eq)?;

        // Parse opcode
        let opcode = self.expect_ident()?;

        let (op, result_ty, result_ann, secondary_ty, secondary_ann) =
            self.parse_op_body(func, &opcode, &ty0, &ann0, &multi_result)?;

        let inst_idx = func.append_inst(
            block,
            Instruction {
                op,
                ty: result_ty,
                secondary_ty,
                origin: Origin::synthetic(),
                result_annotation: result_ann,
                secondary_result_annotation: secondary_ann,
            },
        );

        // Register value(s)
        let vref = ValueRef::inst_result(inst_idx);
        self.value_map.insert(v0_num, vref);

        if let Some((v1_num, _, _)) = multi_result {
            let sec_ref = ValueRef::inst_secondary_result(inst_idx);
            self.value_map.insert(v1_num, sec_ref);
        }

        Ok(())
    }

    fn parse_terminator(&mut self, func: &mut Function, block: BlockRef) -> Result<(), ParseError> {
        let opcode = self.expect_ident()?;

        let (op, ty) = match opcode.as_str() {
            "ret" => {
                // ret v0, v1 or ret v0, v1, v2
                if matches!(self.current, Token::Value(_)) {
                    let ops = self.parse_operand_list()?;
                    if ops.len() == 3 {
                        // ret val, val2, mem
                        let val_op = ops[0].clone();
                        let ret2_op = ops[1].clone();
                        let mem_op: MemOperand = ops[2].clone().into();
                        (Op::Ret(Some(val_op), Some(ret2_op), mem_op), Type::Unit)
                    } else if ops.len() == 2 {
                        // ret val, mem
                        let val_op = ops[0].clone();
                        let mem_op: MemOperand = ops[1].clone().into();
                        (Op::Ret(Some(val_op), None, mem_op), Type::Unit)
                    } else if ops.len() == 1 {
                        // ret mem (void return)
                        let mem_op: MemOperand = ops[0].clone().into();
                        (Op::Ret(None, None, mem_op), Type::Unit)
                    } else {
                        return Err(self.error("ret expects 1, 2, or 3 operands"));
                    }
                } else {
                    return Err(self.error("ret expects at least one operand"));
                }
            }
            "br" => {
                let (bb_num, args) = self.parse_branch_target()?;
                (Op::Br(BlockRef(bb_num), args), Type::Unit)
            }
            "brif" => {
                let cond = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let (then_bb, then_args) = self.parse_branch_target()?;
                self.expect(&Token::Comma)?;
                let (else_bb, else_args) = self.parse_branch_target()?;
                (
                    Op::BrIf(
                        cond.into(),
                        BlockRef(then_bb),
                        then_args,
                        BlockRef(else_bb),
                        else_args,
                    ),
                    Type::Unit,
                )
            }
            "continue" => {
                let vals = if matches!(self.current, Token::Value(_)) {
                    self.parse_operand_list()?
                } else {
                    Vec::new()
                };
                (Op::Continue(vals), Type::Unit)
            }
            "region_yield" => {
                let vals = if matches!(self.current, Token::Value(_)) {
                    self.parse_operand_list()?
                } else {
                    Vec::new()
                };
                (Op::RegionYield(vals), Type::Unit)
            }
            "unreachable" => (Op::Unreachable, Type::Unit),
            "trap" => (Op::Trap, Type::Unit),
            _ => return Err(self.error(format!("unknown terminator: {}", opcode))),
        };

        func.append_inst(
            block,
            Instruction {
                op,
                ty,
                secondary_ty: None,
                origin: Origin::synthetic(),
                result_annotation: None,
                secondary_result_annotation: None,
            },
        );

        Ok(())
    }

    #[allow(clippy::type_complexity)]
    fn parse_op_body(
        &mut self,
        func: &mut Function,
        opcode: &str,
        primary_ty: &Type,
        primary_ann: &Option<Annotation>,
        multi: &Option<(u32, Type, Option<Annotation>)>,
    ) -> Result<
        (
            Op,
            Type,
            Option<Annotation>,
            Option<Type>,
            Option<Annotation>,
        ),
        ParseError,
    > {
        // Helper closures for result construction
        let single = |op: Op, ty: Type, ann: Option<Annotation>| (op, ty, ann, None, None);

        let multi_result = |op: Op,
                            multi: &Option<(u32, Type, Option<Annotation>)>,
                            primary_ty: Type,
                            primary_ann: Option<Annotation>|
         -> (
            Op,
            Type,
            Option<Annotation>,
            Option<Type>,
            Option<Annotation>,
        ) {
            if let Some((_, sec_ty, sec_ann)) = multi {
                (op, primary_ty, primary_ann, Some(sec_ty.clone()), *sec_ann)
            } else {
                (op, primary_ty, primary_ann, None, None)
            }
        };

        match opcode {
            // Simple binary ops: opcode v0, v1
            "add" | "sub" | "mul" | "div" | "rem" | "and" | "or" | "xor" | "band" | "bor"
            | "bxor" | "shl" | "shr" | "min" | "max" | "clmul" | "ptradd" | "ptrdiff"
            | "fminnum" | "fmaxnum" | "copysign" => {
                let a = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let b = self.parse_operand()?;
                let op = match opcode {
                    "add" => Op::Add(a.into(), b.into()),
                    "sub" => Op::Sub(a.into(), b.into()),
                    "mul" => Op::Mul(a.into(), b.into()),
                    "div" => Op::Div(a.into(), b.into()),
                    "rem" => Op::Rem(a.into(), b.into()),
                    "and" => Op::And(a.into(), b.into()),
                    "or" => Op::Or(a.into(), b.into()),
                    "xor" => Op::Xor(a.into(), b.into()),
                    "band" => Op::BAnd(a.into(), b.into()),
                    "bor" => Op::BOr(a.into(), b.into()),
                    "bxor" => Op::BXor(a.into(), b.into()),
                    "shl" => Op::Shl(a.into(), b.into()),
                    "shr" => Op::Shr(a.into(), b.into()),
                    "min" => Op::Min(a.into(), b.into()),
                    "max" => Op::Max(a.into(), b.into()),
                    "clmul" => Op::Clmul(a.into(), b.into()),
                    "ptradd" => Op::PtrAdd(a.into(), b.into()),
                    "ptrdiff" => Op::PtrDiff(a.into(), b.into()),
                    "fminnum" => Op::FMinNum(a.into(), b.into()),
                    "fmaxnum" => Op::FMaxNum(a.into(), b.into()),
                    "copysign" => Op::CopySign(a.into(), b.into()),
                    _ => unreachable!(),
                };
                Ok(single(op, primary_ty.clone(), *primary_ann))
            }

            // Binary with dot-suffix width: opcode.N v0, v1
            "merge" | "rotate_left" | "rotate_right" | "saturating_add" | "saturating_sub"
            | "ssaturating_add" | "ssaturating_sub" => {
                let width = self.parse_dot_u32()?;
                let a = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let b = self.parse_operand()?;
                let op = match opcode {
                    "merge" => Op::Merge(a.into(), b.into(), width),
                    "rotate_left" => Op::RotateLeft(a.into(), b.into(), width),
                    "rotate_right" => Op::RotateRight(a.into(), b.into(), width),
                    "saturating_add" => Op::SaturatingAdd(a.into(), b.into(), width),
                    "saturating_sub" => Op::SaturatingSub(a.into(), b.into(), width),
                    "ssaturating_add" => Op::SignedSaturatingAdd(a.into(), b.into(), width),
                    "ssaturating_sub" => Op::SignedSaturatingSub(a.into(), b.into(), width),
                    _ => unreachable!(),
                };
                Ok(single(op, primary_ty.clone(), *primary_ann))
            }

            // Binary with overflow (multi-result): opcode.N v0, v1
            "sadd_overflow" | "uadd_overflow" | "ssub_overflow" | "usub_overflow"
            | "smul_overflow" | "umul_overflow" => {
                let width = self.parse_dot_u32()?;
                let a = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let b = self.parse_operand()?;
                let op = match opcode {
                    "sadd_overflow" => Op::SAddWithOverflow(a.into(), b.into(), width),
                    "uadd_overflow" => Op::UAddWithOverflow(a.into(), b.into(), width),
                    "ssub_overflow" => Op::SSubWithOverflow(a.into(), b.into(), width),
                    "usub_overflow" => Op::USubWithOverflow(a.into(), b.into(), width),
                    "smul_overflow" => Op::SMulWithOverflow(a.into(), b.into(), width),
                    "umul_overflow" => Op::UMulWithOverflow(a.into(), b.into(), width),
                    _ => unreachable!(),
                };
                Ok(multi_result(op, multi, primary_ty.clone(), *primary_ann))
            }

            "scarrying_mul_add" | "ucarrying_mul_add" => {
                let width = self.parse_dot_u32()?;
                let a = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let b = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let carry = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let add = self.parse_operand()?;
                let op = match opcode {
                    "scarrying_mul_add" => {
                        Op::SCarryingMulAdd(a.into(), b.into(), carry.into(), add.into(), width)
                    }
                    "ucarrying_mul_add" => {
                        Op::UCarryingMulAdd(a.into(), b.into(), carry.into(), add.into(), width)
                    }
                    _ => unreachable!(),
                };
                Ok(multi_result(op, multi, primary_ty.clone(), *primary_ann))
            }

            // FP binary with optional flags: fadd [reassoc] [contract] v0, v1
            "fadd" | "fsub" | "fmul" | "fdiv" | "frem" => {
                let flags = self.parse_fp_rewrite_flags();
                let a = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let b = self.parse_operand()?;
                let op = match opcode {
                    "fadd" => Op::FAdd(a.into(), b.into(), flags),
                    "fsub" => Op::FSub(a.into(), b.into(), flags),
                    "fmul" => Op::FMul(a.into(), b.into(), flags),
                    "fdiv" => Op::FDiv(a.into(), b.into(), flags),
                    "frem" => Op::FRem(a.into(), b.into(), flags),
                    _ => unreachable!(),
                };
                Ok(single(op, primary_ty.clone(), *primary_ann))
            }

            // Unary ops: opcode v0
            "fneg"
            | "fabs"
            | "count_ones"
            | "count_trailing_zeros"
            | "bitcast"
            | "fp_to_si"
            | "fp_to_ui"
            | "fp_convert"
            | "ptrtoint"
            | "ptrtoaddr"
            | "inttoptr" => {
                let a = self.parse_operand()?;
                let op = match opcode {
                    "fneg" => Op::FNeg(a.into()),
                    "fabs" => Op::FAbs(a.into()),
                    "count_ones" => Op::CountOnes(a.into()),
                    "count_trailing_zeros" => Op::CountTrailingZeros(a.into()),
                    "bitcast" => Op::Bitcast(a),
                    "fp_to_si" => Op::FpToSi(a.into()),
                    "fp_to_ui" => Op::FpToUi(a.into()),
                    "fp_convert" => Op::FpConvert(a.into()),
                    "ptrtoint" => Op::PtrToInt(a.into()),
                    "ptrtoaddr" => Op::PtrToAddr(a.into()),
                    "inttoptr" => Op::IntToPtr(a.into()),
                    _ => unreachable!(),
                };
                Ok(single(op, primary_ty.clone(), *primary_ann))
            }

            // Unary with dot-suffix: opcode.N v0
            "count_leading_zeros" | "bswap" | "bit_reverse" => {
                let width = self.parse_dot_u32()?;
                let a = self.parse_operand()?;
                let op = match opcode {
                    "count_leading_zeros" => Op::CountLeadingZeros(a.into(), width),
                    "bswap" => Op::Bswap(a.into(), width),
                    "bit_reverse" => Op::BitReverse(a.into(), width),
                    _ => unreachable!(),
                };
                Ok(single(op, primary_ty.clone(), *primary_ann))
            }

            // Split: multi-result unary with dot-suffix
            "split" => {
                let width = self.parse_dot_u32()?;
                let a = self.parse_operand()?;
                let op = Op::Split(a.into(), width);
                Ok(multi_result(op, multi, primary_ty.clone(), *primary_ann))
            }

            // Comparison: icmp.op v0, v1
            "icmp" => {
                let suffix = self.try_parse_dot_suffix().ok_or_else(|| {
                    self.error("icmp requires a comparison predicate (e.g., icmp.eq)")
                })?;
                let cmp_op = Self::parse_icmp_op(&suffix)
                    .ok_or_else(|| self.error(format!("unknown icmp predicate: {}", suffix)))?;
                let a = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let b = self.parse_operand()?;
                Ok(single(
                    Op::ICmp(cmp_op, a.into(), b.into()),
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            "fcmp" => {
                let suffix = self.try_parse_dot_suffix().ok_or_else(|| {
                    self.error("fcmp requires a comparison predicate (e.g., fcmp.oeq)")
                })?;
                let cmp_op = Self::parse_fcmp_op(&suffix)
                    .ok_or_else(|| self.error(format!("unknown fcmp predicate: {}", suffix)))?;
                let a = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let b = self.parse_operand()?;
                Ok(single(
                    Op::FCmp(cmp_op, a.into(), b.into()),
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            // Select: select cond, true_val, false_val
            "select" => {
                let cond = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let tv = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let fv = self.parse_operand()?;
                Ok(single(
                    Op::Select(cond.into(), tv, fv),
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            // Memory: load.N, load.atomic.ordering
            "load" => {
                self.expect(&Token::Dot)?;
                // Check for "atomic" or a number
                match &self.current {
                    Token::Ident(s) if s == "atomic" => {
                        self.advance();
                        self.expect(&Token::Dot)?;
                        let ord_s = self.expect_ident()?;
                        let ordering = Self::parse_memory_ordering(&ord_s).ok_or_else(|| {
                            self.error(format!("unknown memory ordering: {}", ord_s))
                        })?;
                        let ptr = self.parse_operand()?;
                        self.expect(&Token::Comma)?;
                        let mem = self.parse_operand()?;
                        Ok(multi_result(
                            Op::LoadAtomic(ptr.into(), ordering, mem.into()),
                            multi,
                            primary_ty.clone(),
                            *primary_ann,
                        ))
                    }
                    _ => {
                        let bytes_s = match &self.current {
                            Token::Integer(s) => {
                                let s = s.clone();
                                self.advance();
                                s
                            }
                            other => {
                                return Err(self.error(format!(
                                    "expected byte count after 'load.', got {:?}",
                                    other
                                )));
                            }
                        };
                        let bytes: u32 = bytes_s
                            .parse()
                            .map_err(|_| self.error(format!("invalid byte count: {}", bytes_s)))?;
                        let ptr = self.parse_operand()?;
                        self.expect(&Token::Comma)?;
                        let mem = self.parse_operand()?;
                        Ok(single(
                            Op::Load(ptr.into(), bytes, mem.into()),
                            primary_ty.clone(),
                            *primary_ann,
                        ))
                    }
                }
            }

            // Memory: store.N or store.atomic.ordering
            "store" => {
                self.expect(&Token::Dot)?;
                match &self.current {
                    Token::Ident(s) if s == "atomic" => {
                        self.advance();
                        self.expect(&Token::Dot)?;
                        let ord_s = self.expect_ident()?;
                        let ordering = Self::parse_memory_ordering(&ord_s).ok_or_else(|| {
                            self.error(format!("unknown memory ordering: {}", ord_s))
                        })?;
                        let val = self.parse_operand()?;
                        self.expect(&Token::Comma)?;
                        let ptr = self.parse_operand()?;
                        self.expect(&Token::Comma)?;
                        let mem = self.parse_operand()?;
                        Ok(single(
                            Op::StoreAtomic(val, ptr.into(), ordering, mem.into()),
                            primary_ty.clone(),
                            *primary_ann,
                        ))
                    }
                    _ => {
                        let bytes_s = match &self.current {
                            Token::Integer(s) => {
                                let s = s.clone();
                                self.advance();
                                s
                            }
                            other => {
                                return Err(self.error(format!(
                                    "expected byte count after 'store.', got {:?}",
                                    other
                                )));
                            }
                        };
                        let bytes: u32 = bytes_s
                            .parse()
                            .map_err(|_| self.error(format!("invalid byte count: {}", bytes_s)))?;
                        let val = self.parse_operand()?;
                        self.expect(&Token::Comma)?;
                        let ptr = self.parse_operand()?;
                        self.expect(&Token::Comma)?;
                        let mem = self.parse_operand()?;
                        Ok(single(
                            Op::Store(val, ptr.into(), bytes, mem.into()),
                            primary_ty.clone(),
                            *primary_ann,
                        ))
                    }
                }
            }

            "stack_slot" => {
                let bytes = self.expect_u32()?;
                let align = if self.current == Token::Ident("align".into()) {
                    self.advance();
                    self.expect_u32()?
                } else {
                    0
                };
                Ok(single(
                    Op::StackSlot(bytes, align),
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            "memcopy" => {
                let dst = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let src = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let count = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let mem = self.parse_operand()?;
                Ok(single(
                    Op::MemCopy(dst.into(), src.into(), count.into(), mem.into()),
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            "memmove" => {
                let dst = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let src = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let count = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let mem = self.parse_operand()?;
                Ok(single(
                    Op::MemMove(dst.into(), src.into(), count.into(), mem.into()),
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            "memset" => {
                let dst = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let val = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let count = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let mem = self.parse_operand()?;
                Ok(single(
                    Op::MemSet(dst.into(), val, count.into(), mem.into()),
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            // rmw.op.ordering v0, v1, v2
            "rmw" => {
                self.expect(&Token::Dot)?;
                let rmw_op_s = self.expect_ident()?;
                let rmw_op = Self::parse_atomic_rmw_op(&rmw_op_s)
                    .ok_or_else(|| self.error(format!("unknown rmw op: {}", rmw_op_s)))?;
                self.expect(&Token::Dot)?;
                let ord_s = self.expect_ident()?;
                let ordering = Self::parse_memory_ordering(&ord_s)
                    .ok_or_else(|| self.error(format!("unknown ordering: {}", ord_s)))?;
                let ptr = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let val = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let mem = self.parse_operand()?;
                Ok(multi_result(
                    Op::AtomicRmw(rmw_op, ptr.into(), val, ordering, mem.into()),
                    multi,
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            // cmpxchg.succ_ord.fail_ord v0, v1, v2, v3
            "cmpxchg" => {
                self.expect(&Token::Dot)?;
                let succ_s = self.expect_ident()?;
                let succ_ord = Self::parse_memory_ordering(&succ_s)
                    .ok_or_else(|| self.error(format!("unknown ordering: {}", succ_s)))?;
                self.expect(&Token::Dot)?;
                let fail_s = self.expect_ident()?;
                let fail_ord = Self::parse_memory_ordering(&fail_s)
                    .ok_or_else(|| self.error(format!("unknown ordering: {}", fail_s)))?;
                let ptr = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let expected = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let desired = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let mem = self.parse_operand()?;
                Ok(multi_result(
                    Op::AtomicCmpXchg(
                        ptr.into(),
                        expected,
                        desired,
                        succ_ord,
                        fail_ord,
                        mem.into(),
                    ),
                    multi,
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            // fence.ordering v0
            "fence" => {
                self.expect(&Token::Dot)?;
                let ord_s = self.expect_ident()?;
                let ordering = Self::parse_memory_ordering(&ord_s)
                    .ok_or_else(|| self.error(format!("unknown ordering: {}", ord_s)))?;
                let mem = self.parse_operand()?;
                Ok(single(
                    Op::Fence(ordering, mem.into()),
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            // symbol_addr @name
            "symbol_addr" => {
                let name = self.read_symbol_name()?;
                let sym_id = self.intern(&name);
                Ok(single(
                    Op::SymbolAddr(sym_id),
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            // call v0(v1, v2, ...), mem_token [-> ret_type]
            "call" => {
                let callee = self.parse_operand()?;
                self.expect(&Token::LParen)?;
                let args = if self.current == Token::RParen {
                    Vec::new()
                } else {
                    self.parse_operand_list()?
                };
                self.expect(&Token::RParen)?;
                self.expect(&Token::Comma)?;
                let mem = self.parse_operand()?;

                // Check for -> ret_type suffix (non-void call)
                if self.current == Token::Arrow {
                    self.advance();
                    let (ret_ty, ret_ann) = self.parse_type_with_annotation()?;
                    // Non-void call: primary is mem, secondary is ret_ty.
                    // The display format puts the return annotation in the
                    // `-> type:ann` suffix. Fall back to the multi-result
                    // binding annotation for compatibility with older dumps.
                    let effective_ann = ret_ann.or_else(|| multi.as_ref().and_then(|(_, _, a)| *a));
                    Ok((
                        Op::Call(callee.into(), args, mem.into(), None),
                        primary_ty.clone(),
                        *primary_ann,
                        Some(ret_ty),
                        effective_ann,
                    ))
                } else {
                    // Void call: only mem result
                    Ok(single(
                        Op::Call(callee.into(), args, mem.into(), None),
                        primary_ty.clone(),
                        *primary_ann,
                    ))
                }
            }

            "call_ret2" => {
                let mem = self.parse_operand()?;
                Ok(single(
                    Op::CallRet2(mem.into()),
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            // sext v0, N
            "sext" => {
                let src = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let bits = self.expect_u32()?;
                Ok(single(
                    Op::Sext(src.into(), bits),
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            // zext v0, N
            "zext" => {
                let src = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let bits = self.expect_u32()?;
                Ok(single(
                    Op::Zext(src.into(), bits),
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            // si_to_fp v0, FloatType — display uses {ft:?} so prints F32, F64, etc.
            "si_to_fp" => {
                let src = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let ft_s = self.expect_ident()?;
                let ft = Self::parse_float_type(&ft_s)
                    .ok_or_else(|| self.error(format!("unknown float type: {}", ft_s)))?;
                Ok(single(
                    Op::SiToFp(src.into(), ft),
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            // ui_to_fp v0, FloatType
            "ui_to_fp" => {
                let src = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let ft_s = self.expect_ident()?;
                let ft = Self::parse_float_type(&ft_s)
                    .ok_or_else(|| self.error(format!("unknown float type: {}", ft_s)))?;
                Ok(single(
                    Op::UiToFp(src.into(), ft),
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            // Constants
            "iconst" => {
                // iconst <integer> (can be negative, can be hex)
                let val = match &self.current {
                    Token::Integer(s) => {
                        let s = s.clone();
                        self.advance();
                        s.parse::<BigInt>()
                            .map_err(|_| self.error(format!("invalid integer: {}", s)))?
                    }
                    Token::HexInteger(s) => {
                        let s = s.clone();
                        self.advance();
                        BigInt::parse_bytes(s.as_bytes(), 16)
                            .ok_or_else(|| self.error(format!("invalid hex integer: {}", s)))?
                    }
                    other => return Err(self.error(format!("expected integer, got {:?}", other))),
                };
                Ok(single(Op::Const(val), primary_ty.clone(), *primary_ann))
            }

            "bconst" => {
                let val_s = self.expect_ident()?;
                let val = match val_s.as_str() {
                    "true" => true,
                    "false" => false,
                    _ => {
                        return Err(self.error(format!("expected true/false, got {}", val_s)));
                    }
                };
                Ok(single(Op::BConst(val), primary_ty.clone(), *primary_ann))
            }

            // fconst.type hex
            "fconst" => {
                let suffix = self.try_parse_dot_suffix().ok_or_else(|| {
                    self.error("fconst requires a float type suffix (e.g., fconst.f32)")
                })?;
                let ft = Self::parse_float_type(&suffix)
                    .ok_or_else(|| self.error(format!("unknown float type: {}", suffix)))?;
                let bits_s = match &self.current {
                    Token::HexInteger(s) => {
                        let s = s.clone();
                        self.advance();
                        s
                    }
                    Token::Integer(s) => {
                        let s = s.clone();
                        self.advance();
                        s
                    }
                    other => {
                        return Err(
                            self.error(format!("expected hex literal for fconst, got {:?}", other))
                        );
                    }
                };
                let bits = u128::from_str_radix(&bits_s, 16)
                    .or_else(|_| bits_s.parse::<u128>())
                    .map_err(|_| self.error(format!("invalid float bits: {}", bits_s)))?;
                Ok(single(
                    Op::FConst(FloatConst::from_bits(ft, bits)),
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            // param: param %name or param <index>
            "param" => {
                match &self.current {
                    Token::Percent => {
                        self.advance();
                        let name = self.read_extended_ident()?;
                        // Look up the parameter index by name
                        let sym_id = self.intern(&name);
                        let idx = func
                            .param_names
                            .iter()
                            .position(|pn| *pn == Some(sym_id))
                            .ok_or_else(|| {
                                self.error(format!("unknown parameter name: %{}", name))
                            })? as u32;
                        Ok(single(Op::Param(idx), primary_ty.clone(), *primary_ann))
                    }
                    Token::Integer(_) => {
                        let idx = self.expect_u32()?;
                        Ok(single(Op::Param(idx), primary_ty.clone(), *primary_ann))
                    }
                    other => Err(self.error(format!(
                        "expected parameter index or %name, got {:?}",
                        other
                    ))),
                }
            }

            // Aggregate ops
            "extractvalue" => {
                let agg = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let indices = self.parse_index_list()?;
                Ok(single(
                    Op::ExtractValue(agg, indices),
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            "insertvalue" => {
                let agg = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let val = self.parse_operand()?;
                self.expect(&Token::Comma)?;
                let indices = self.parse_index_list()?;
                Ok(single(
                    Op::InsertValue(agg, val, indices),
                    primary_ty.clone(),
                    *primary_ann,
                ))
            }

            other => Err(self.error(format!("unknown opcode: {}", other))),
        }
    }

    /// Parse `[N, M, ...]` index list.
    fn parse_index_list(&mut self) -> Result<Vec<u32>, ParseError> {
        self.expect(&Token::LBracket)?;
        let mut indices = Vec::new();
        if self.current != Token::RBracket {
            indices.push(self.expect_u32()?);
            while self.current == Token::Comma {
                self.advance();
                indices.push(self.expect_u32()?);
            }
        }
        self.expect(&Token::RBracket)?;
        Ok(indices)
    }
}

fn hex_digit(b: u8) -> Result<u8, ParseError> {
    match b {
        b'0'..=b'9' => Ok(b - b'0'),
        b'a'..=b'f' => Ok(b - b'a' + 10),
        b'A'..=b'F' => Ok(b - b'A' + 10),
        _ => Err(ParseError {
            line: 0,
            col: 0,
            message: format!("invalid hex digit: {}", b as char),
        }),
    }
}

// ── Public API ──────────────────────────────────────────────────────────────

/// Parse a tuffy IR text format string into a `Module`.
pub fn parse_module(input: &str) -> Result<Module, ParseError> {
    let mut parser = Parser::new(input);
    parser.parse_module()
}

// ── Tests ───────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: parse a module and return it.
    fn parse(input: &str) -> Module {
        parse_module(input).unwrap_or_else(|e| panic!("parse error: {}", e))
    }

    #[test]
    fn test_simple_add_function() {
        let input = r#"
func @add(%a: int:s32, %b: int:s32) -> int:s32 {
  bb0:
    v0: int:s32 = param %a
    v1: int:s32 = param %b
    v2: int:s32 = add v0:s32, v1:s32
    ret v2:s32, v0
}
"#;
        let module = parse(input);
        assert_eq!(module.functions.len(), 1);
        let func = &module.functions[0];
        assert_eq!(module.resolve(func.name), "add");
        assert_eq!(func.params.len(), 2);
        assert_eq!(func.ret_ty, Some(Type::Int));
        // 3 normal instructions + 1 terminator
        assert_eq!(func.inst_pool.next_index() as usize, 4);
    }

    #[test]
    fn test_round_trip_simple() {
        let input = r#"func @add(%a: int:s32, %b: int:s32) -> int:s32 {
  bb0:
    v0: int:s32 = param %a
    v1: int:s32 = param %b
    v2: int:s32 = add v0, v1
    ret v2:s32, v0
}"#;
        let module = parse(input);
        let output = format!("{}", module);
        // Verify the output can be re-parsed
        let module2 = parse(&output);
        assert_eq!(module2.functions.len(), 1);
        assert_eq!(module2.functions[0].inst_pool.next_index() as usize, 4);
    }

    #[test]
    fn test_block_args() {
        let input = r#"
func @loop_test() {
  bb0(v0: mem):
    v1: int:s32 = iconst 0
    br bb1(v1)

  bb1(v2: int:s32):
    v3: bool = icmp.lt v2:s32, v1
    brif v3, bb2, bb1(v2)

  bb2:
    ret v0
}
"#;
        let module = parse(input);
        assert_eq!(module.functions.len(), 1);
        let func = &module.functions[0];
        // bb0 has 1 block arg, bb1 has 1, bb2 has 0
        assert_eq!(func.block_args.len(), 2);
    }

    #[test]
    fn test_constants() {
        let input = r#"
func @consts() {
  bb0:
    v0: int:s32 = iconst 42
    v1: int:s32 = iconst -1
    v2: bool = bconst true
    v3: bool = bconst false
    unreachable
}
"#;
        let module = parse(input);
        let func = &module.functions[0];
        assert_eq!(func.inst_pool.next_index() as usize, 5); // 4 + unreachable
    }

    #[test]
    fn test_memory_ops() {
        let input = r#"
func @mem_test() {
  bb0(v0: mem):
    v1: ptr = stack_slot 8
    v2: int:s32 = load.4 v1, v0
    v3: mem = store.4 v2, v1, v0
    ret v3
}
"#;
        let module = parse(input);
        let func = &module.functions[0];
        assert_eq!(func.inst_pool.next_index() as usize, 4); // stack_slot, load, store, ret
    }

    #[test]
    fn test_region() {
        let input = r#"
func @region_test() {
  bb0(v0: mem):
    v1: int:s32 = iconst 0
    br bb1(v1)

  region loop {
    bb1(v2: int:s32):
      v3: int:s32 = iconst 1
      v4: int:s32 = add v2, v3
      v5: bool = icmp.lt v4:s32, v1
      brif v5, bb2, bb3
    bb2:
      continue v4
    bb3:
      region_yield v4
  }

  bb4:
    ret v0
}
"#;
        let module = parse(input);
        let func = &module.functions[0];
        // root function region + loop region
        assert_eq!(func.regions.len(), 2);
        assert_eq!(func.regions[1].kind, RegionKind::Loop);
    }

    #[test]
    fn test_call() {
        let input = r#"
func @caller() {
  bb0(v0: mem):
    v1: ptr = symbol_addr @callee
    v2: mem, v3: int:s32 = call v1(), v0 -> int:s32
    ret v3:s32, v2
}
"#;
        let module = parse(input);
        let func = &module.functions[0];
        assert_eq!(func.inst_pool.next_index() as usize, 3); // symbol_addr, call, ret
        // call is multi-result
        assert!(func.inst_pool.inst(1).secondary_ty.is_some());
    }

    #[test]
    fn test_sext_zext() {
        let input = r#"
func @ext_test() {
  bb0:
    v0: int:s8 = iconst 42
    v1: int:s32 = sext v0, 32
    v2: int:u32 = zext v0, 32
    unreachable
}
"#;
        let module = parse(input);
        let func = &module.functions[0];
        assert_eq!(func.inst_pool.next_index() as usize, 4);
    }

    #[test]
    fn test_no_param_names() {
        let input = r#"
func @add(int:s32, int:s32) -> int:s32 {
  bb0:
    v0: int:s32 = param 0
    v1: int:s32 = param 1
    v2: int:s32 = add v0, v1
    ret v2, v0
}
"#;
        let module = parse(input);
        let func = &module.functions[0];
        assert_eq!(func.params.len(), 2);
        assert!(func.param_names.iter().all(|n| n.is_none()));
    }

    #[test]
    fn test_brif_with_args() {
        let input = r#"
func @brif_test() {
  bb0(v0: mem):
    v1: bool = bconst true
    brif v1, bb1(v0), bb2(v0)
  bb1(v2: mem):
    ret v2
  bb2(v3: mem):
    ret v3
}
"#;
        let module = parse(input);
        let func = &module.functions[0];
        assert_eq!(func.blocks.len(), 3);
    }

    #[test]
    fn test_select() {
        let input = r#"
func @select_test() {
  bb0:
    v0: bool = bconst true
    v1: int:s32 = iconst 1
    v2: int:s32 = iconst 2
    v3: int:s32 = select v0, v1, v2
    unreachable
}
"#;
        let module = parse(input);
        let func = &module.functions[0];
        assert_eq!(func.inst_pool.next_index() as usize, 5);
    }

    #[test]
    fn test_fp_ops() {
        let input = r#"
func @fp_test() {
  bb0:
    v0: f64 = fconst.f64 0x3ff0000000000000
    v1: f64 = fconst.f64 0x4000000000000000
    v2: f64 = fadd v0, v1
    v3: f64 = fsub reassoc v0, v1
    v4: f64 = fmul reassoc contract v0, v1
    v5: f64 = fneg v0
    v6: f64 = fabs v0
    unreachable
}
"#;
        let module = parse(input);
        let func = &module.functions[0];
        assert_eq!(func.inst_pool.next_index() as usize, 8);
    }

    #[test]
    fn test_multiple_functions() {
        let input = r#"
func @foo() {
  bb0:
    unreachable
}

func @bar() {
  bb0:
    trap
}
"#;
        let module = parse(input);
        assert_eq!(module.functions.len(), 2);
    }

    #[test]
    fn test_aggregate_ops() {
        let input = r#"
func @agg_test() {
  bb0:
    v0: int:s32 = iconst 0
    v1: int:s32 = extractvalue v0, [0, 1]
    v2: int:s32 = insertvalue v0, v1, [0]
    unreachable
}
"#;
        let module = parse(input);
        let func = &module.functions[0];
        assert_eq!(func.inst_pool.next_index() as usize, 4);
    }
}
