// Signature file for parser generated by fsyacc
module MemoryParser
type token = 
  | EOF
  | WHITESPACE
  | LCBRACK
  | RCBRACK
  | ZERO
  | PLUS
  | MINUS
  | SIGN of (string)
  | ASSIGN
  | LBRACK
  | RBRACK
  | SEPARATOR
  | ARRAY of (char)
  | VAR of (string)
  | NUM of (int)
type tokenId = 
    | TOKEN_EOF
    | TOKEN_WHITESPACE
    | TOKEN_LCBRACK
    | TOKEN_RCBRACK
    | TOKEN_ZERO
    | TOKEN_PLUS
    | TOKEN_MINUS
    | TOKEN_SIGN
    | TOKEN_ASSIGN
    | TOKEN_LBRACK
    | TOKEN_RBRACK
    | TOKEN_SEPARATOR
    | TOKEN_ARRAY
    | TOKEN_VAR
    | TOKEN_NUM
    | TOKEN_end_of_input
    | TOKEN_error
type nonTerminalId = 
    | NONTERM__startstart
    | NONTERM_start
    | NONTERM_expr
    | NONTERM_conExpr
    | NONTERM_conArrElement
    | NONTERM_absExpr
    | NONTERM_absArrElement
/// This function maps tokens to integer indexes
val tagOfToken: token -> int

/// This function maps integer indexes to symbolic token ids
val tokenTagToTokenId: int -> tokenId

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
val prodIdxToNonTerminal: int -> nonTerminalId

/// This function gets the name of a token as a string
val token_to_string: token -> string
val start : (FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> FSharp.Text.Lexing.LexBuffer<'cty> -> (Memory) 
