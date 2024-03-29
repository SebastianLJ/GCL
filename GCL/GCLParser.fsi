// Signature file for parser generated by fsyacc
module GCLParser
type token = 
  | EOF
  | WHITESPACE
  | SKIP
  | AND
  | OR
  | ANDH
  | ORH
  | NOT
  | EQUAL
  | NEQUAL
  | GT
  | GTE
  | LT
  | LTE
  | TRUE
  | FALSE
  | PLUS
  | MINUS
  | TIMES
  | DIV
  | POW
  | LPAR
  | RPAR
  | LBRACK
  | RBRACK
  | FUNC
  | CONC
  | ASSIGN
  | SEPARATOR
  | IF
  | FI
  | DO
  | OD
  | GC
  | C
  | ARRAY of (char)
  | X of (string)
  | VAR of (string)
  | NUM of (int)
type tokenId = 
    | TOKEN_EOF
    | TOKEN_WHITESPACE
    | TOKEN_SKIP
    | TOKEN_AND
    | TOKEN_OR
    | TOKEN_ANDH
    | TOKEN_ORH
    | TOKEN_NOT
    | TOKEN_EQUAL
    | TOKEN_NEQUAL
    | TOKEN_GT
    | TOKEN_GTE
    | TOKEN_LT
    | TOKEN_LTE
    | TOKEN_TRUE
    | TOKEN_FALSE
    | TOKEN_PLUS
    | TOKEN_MINUS
    | TOKEN_TIMES
    | TOKEN_DIV
    | TOKEN_POW
    | TOKEN_LPAR
    | TOKEN_RPAR
    | TOKEN_LBRACK
    | TOKEN_RBRACK
    | TOKEN_FUNC
    | TOKEN_CONC
    | TOKEN_ASSIGN
    | TOKEN_SEPARATOR
    | TOKEN_IF
    | TOKEN_FI
    | TOKEN_DO
    | TOKEN_OD
    | TOKEN_GC
    | TOKEN_C
    | TOKEN_ARRAY
    | TOKEN_X
    | TOKEN_VAR
    | TOKEN_NUM
    | TOKEN_end_of_input
    | TOKEN_error
type nonTerminalId = 
    | NONTERM__startstart
    | NONTERM_start
    | NONTERM_cExpr
    | NONTERM_gcExpr
    | NONTERM_aExpr
    | NONTERM_bExpr
/// This function maps tokens to integer indexes
val tagOfToken: token -> int

/// This function maps integer indexes to symbolic token ids
val tokenTagToTokenId: int -> tokenId

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
val prodIdxToNonTerminal: int -> nonTerminalId

/// This function gets the name of a token as a string
val token_to_string: token -> string
val start : (FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> FSharp.Text.Lexing.LexBuffer<'cty> -> (C) 
