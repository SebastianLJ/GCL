// Implementation file for parser generated by fsyacc
module InputParser
#nowarn "64";; // turn off warnings that type variables used in production annotations are instantiated to concrete type
open FSharp.Text.Lexing
open FSharp.Text.Parsing.ParseHelpers
# 2 "InputParser.fsp"

open InputTypesAST

# 10 "InputParser.fs"
// This type is the type of tokens accepted by the parser
type token = 
  | EOF
  | WHITESPACE
  | ASSIGN
  | LBRACK
  | RBRACK
  | SEPARATOR
  | ARRAY of (char)
  | VAR of (string)
  | NUM of (int)
// This type is used to give symbolic names to token indexes, useful for error messages
type tokenId = 
    | TOKEN_EOF
    | TOKEN_WHITESPACE
    | TOKEN_ASSIGN
    | TOKEN_LBRACK
    | TOKEN_RBRACK
    | TOKEN_SEPARATOR
    | TOKEN_ARRAY
    | TOKEN_VAR
    | TOKEN_NUM
    | TOKEN_end_of_input
    | TOKEN_error
// This type is used to give symbolic names to token indexes, useful for error messages
type nonTerminalId = 
    | NONTERM__startstart
    | NONTERM_start
    | NONTERM_iExpr
    | NONTERM_arrElem

// This function maps tokens to integer indexes
let tagOfToken (t:token) = 
  match t with
  | EOF  -> 0 
  | WHITESPACE  -> 1 
  | ASSIGN  -> 2 
  | LBRACK  -> 3 
  | RBRACK  -> 4 
  | SEPARATOR  -> 5 
  | ARRAY _ -> 6 
  | VAR _ -> 7 
  | NUM _ -> 8 

// This function maps integer indexes to symbolic token ids
let tokenTagToTokenId (tokenIdx:int) = 
  match tokenIdx with
  | 0 -> TOKEN_EOF 
  | 1 -> TOKEN_WHITESPACE 
  | 2 -> TOKEN_ASSIGN 
  | 3 -> TOKEN_LBRACK 
  | 4 -> TOKEN_RBRACK 
  | 5 -> TOKEN_SEPARATOR 
  | 6 -> TOKEN_ARRAY 
  | 7 -> TOKEN_VAR 
  | 8 -> TOKEN_NUM 
  | 11 -> TOKEN_end_of_input
  | 9 -> TOKEN_error
  | _ -> failwith "tokenTagToTokenId: bad token"

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
let prodIdxToNonTerminal (prodIdx:int) = 
  match prodIdx with
    | 0 -> NONTERM__startstart 
    | 1 -> NONTERM_start 
    | 2 -> NONTERM_iExpr 
    | 3 -> NONTERM_iExpr 
    | 4 -> NONTERM_iExpr 
    | 5 -> NONTERM_arrElem 
    | 6 -> NONTERM_arrElem 
    | _ -> failwith "prodIdxToNonTerminal: bad production index"

let _fsyacc_endOfInputTag = 11 
let _fsyacc_tagOfErrorTerminal = 9

// This function gets the name of a token as a string
let token_to_string (t:token) = 
  match t with 
  | EOF  -> "EOF" 
  | WHITESPACE  -> "WHITESPACE" 
  | ASSIGN  -> "ASSIGN" 
  | LBRACK  -> "LBRACK" 
  | RBRACK  -> "RBRACK" 
  | SEPARATOR  -> "SEPARATOR" 
  | ARRAY _ -> "ARRAY" 
  | VAR _ -> "VAR" 
  | NUM _ -> "NUM" 

// This function gets the data carried by a token as an object
let _fsyacc_dataOfToken (t:token) = 
  match t with 
  | EOF  -> (null : System.Object) 
  | WHITESPACE  -> (null : System.Object) 
  | ASSIGN  -> (null : System.Object) 
  | LBRACK  -> (null : System.Object) 
  | RBRACK  -> (null : System.Object) 
  | SEPARATOR  -> (null : System.Object) 
  | ARRAY _fsyacc_x -> Microsoft.FSharp.Core.Operators.box _fsyacc_x 
  | VAR _fsyacc_x -> Microsoft.FSharp.Core.Operators.box _fsyacc_x 
  | NUM _fsyacc_x -> Microsoft.FSharp.Core.Operators.box _fsyacc_x 
let _fsyacc_gotos = [| 0us; 65535us; 1us; 65535us; 0us; 1us; 2us; 65535us; 0us; 2us; 13us; 12us; 2us; 65535us; 9us; 10us; 15us; 16us; |]
let _fsyacc_sparseGotoTableRowOffsets = [|0us; 1us; 3us; 6us; |]
let _fsyacc_stateToProdIdxsTableElements = [| 1us; 0us; 1us; 0us; 2us; 1us; 4us; 1us; 1us; 1us; 2us; 1us; 2us; 1us; 2us; 1us; 3us; 1us; 3us; 1us; 3us; 1us; 3us; 1us; 3us; 2us; 4us; 4us; 1us; 4us; 2us; 5us; 6us; 1us; 6us; 1us; 6us; |]
let _fsyacc_stateToProdIdxsTableRowOffsets = [|0us; 2us; 4us; 7us; 9us; 11us; 13us; 15us; 17us; 19us; 21us; 23us; 25us; 28us; 30us; 33us; 35us; |]
let _fsyacc_action_rows = 17
let _fsyacc_actionTableElements = [|2us; 32768us; 6us; 7us; 7us; 4us; 0us; 49152us; 2us; 32768us; 0us; 3us; 5us; 13us; 0us; 16385us; 1us; 32768us; 2us; 5us; 1us; 32768us; 8us; 6us; 0us; 16386us; 1us; 32768us; 2us; 8us; 1us; 32768us; 3us; 9us; 1us; 32768us; 8us; 14us; 1us; 32768us; 4us; 11us; 0us; 16387us; 1us; 16388us; 5us; 13us; 2us; 32768us; 6us; 7us; 7us; 4us; 1us; 16389us; 5us; 15us; 1us; 32768us; 8us; 14us; 0us; 16390us; |]
let _fsyacc_actionTableRowOffsets = [|0us; 3us; 4us; 7us; 8us; 10us; 12us; 13us; 15us; 17us; 19us; 21us; 22us; 24us; 27us; 29us; 31us; |]
let _fsyacc_reductionSymbolCounts = [|1us; 2us; 3us; 5us; 3us; 1us; 3us; |]
let _fsyacc_productionToNonTerminalTable = [|0us; 1us; 2us; 2us; 2us; 3us; 3us; |]
let _fsyacc_immediateActions = [|65535us; 49152us; 65535us; 16385us; 65535us; 65535us; 16386us; 65535us; 65535us; 65535us; 65535us; 16387us; 65535us; 65535us; 65535us; 65535us; 16390us; |]
let _fsyacc_reductions ()  =    [| 
# 122 "InputParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : init)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
                      raise (FSharp.Text.Parsing.Accept(Microsoft.FSharp.Core.Operators.box _1))
                   )
                 : '_startstart));
# 131 "InputParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : init)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 36 "InputParser.fsp"
                                                    _1 
                   )
# 36 "InputParser.fsp"
                 : init));
# 142 "InputParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : string)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : int)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 47 "InputParser.fsp"
                                                                    VarInit(_1, _3) 
                   )
# 47 "InputParser.fsp"
                 : init));
# 154 "InputParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : char)) in
            let _4 = (let data = parseState.GetInput(4) in (Microsoft.FSharp.Core.Operators.unbox data : arr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 48 "InputParser.fsp"
                                                                    ArrInit(_1, _4) 
                   )
# 48 "InputParser.fsp"
                 : init));
# 166 "InputParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : init)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : init)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 49 "InputParser.fsp"
                                                                    SeqInit(_1, _3) 
                   )
# 49 "InputParser.fsp"
                 : init));
# 178 "InputParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : int)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 51 "InputParser.fsp"
                                                                    NumElem(_1)     
                   )
# 51 "InputParser.fsp"
                 : arr));
# 189 "InputParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : int)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : arr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 52 "InputParser.fsp"
                                                                    Elems(_1, _3)   
                   )
# 52 "InputParser.fsp"
                 : arr));
|]
# 202 "InputParser.fs"
let tables () : FSharp.Text.Parsing.Tables<_> = 
  { reductions= _fsyacc_reductions ();
    endOfInputTag = _fsyacc_endOfInputTag;
    tagOfToken = tagOfToken;
    dataOfToken = _fsyacc_dataOfToken; 
    actionTableElements = _fsyacc_actionTableElements;
    actionTableRowOffsets = _fsyacc_actionTableRowOffsets;
    stateToProdIdxsTableElements = _fsyacc_stateToProdIdxsTableElements;
    stateToProdIdxsTableRowOffsets = _fsyacc_stateToProdIdxsTableRowOffsets;
    reductionSymbolCounts = _fsyacc_reductionSymbolCounts;
    immediateActions = _fsyacc_immediateActions;
    gotos = _fsyacc_gotos;
    sparseGotoTableRowOffsets = _fsyacc_sparseGotoTableRowOffsets;
    tagOfErrorTerminal = _fsyacc_tagOfErrorTerminal;
    parseError = (fun (ctxt:FSharp.Text.Parsing.ParseErrorContext<_>) -> 
                              match parse_error_rich with 
                              | Some f -> f ctxt
                              | None -> parse_error ctxt.Message);
    numTerminals = 12;
    productionToNonTerminalTable = _fsyacc_productionToNonTerminalTable  }
let engine lexer lexbuf startState = (tables ()).Interpret(lexer, lexbuf, startState)
let start lexer lexbuf : init =
    Microsoft.FSharp.Core.Operators.unbox ((tables ()).Interpret(lexer, lexbuf, 0))
