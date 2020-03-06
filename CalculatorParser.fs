// Implementation file for parser generated by fsyacc
module CalculatorParser
#nowarn "64";; // turn off warnings that type variables used in production annotations are instantiated to concrete type
open FSharp.Text.Lexing
open FSharp.Text.Parsing.ParseHelpers
# 2 "CalculatorParser.fsp"

open CalculatorTypesAST

# 10 "CalculatorParser.fs"
// This type is the type of tokens accepted by the parser
type token = 
  | TIMES
  | DIV
  | PLUS
  | MINUS
  | POW
  | SQRT
  | LOG
  | LPAR
  | RPAR
  | EOF
  | NUM of (float)
// This type is used to give symbolic names to token indexes, useful for error messages
type tokenId = 
    | TOKEN_TIMES
    | TOKEN_DIV
    | TOKEN_PLUS
    | TOKEN_MINUS
    | TOKEN_POW
    | TOKEN_SQRT
    | TOKEN_LOG
    | TOKEN_LPAR
    | TOKEN_RPAR
    | TOKEN_EOF
    | TOKEN_NUM
    | TOKEN_end_of_input
    | TOKEN_error
// This type is used to give symbolic names to token indexes, useful for error messages
type nonTerminalId = 
    | NONTERM__startstart
    | NONTERM_start
    | NONTERM_expression

// This function maps tokens to integer indexes
let tagOfToken (t:token) = 
  match t with
  | TIMES  -> 0 
  | DIV  -> 1 
  | PLUS  -> 2 
  | MINUS  -> 3 
  | POW  -> 4 
  | SQRT  -> 5 
  | LOG  -> 6 
  | LPAR  -> 7 
  | RPAR  -> 8 
  | EOF  -> 9 
  | NUM _ -> 10 

// This function maps integer indexes to symbolic token ids
let tokenTagToTokenId (tokenIdx:int) = 
  match tokenIdx with
  | 0 -> TOKEN_TIMES 
  | 1 -> TOKEN_DIV 
  | 2 -> TOKEN_PLUS 
  | 3 -> TOKEN_MINUS 
  | 4 -> TOKEN_POW 
  | 5 -> TOKEN_SQRT 
  | 6 -> TOKEN_LOG 
  | 7 -> TOKEN_LPAR 
  | 8 -> TOKEN_RPAR 
  | 9 -> TOKEN_EOF 
  | 10 -> TOKEN_NUM 
  | 13 -> TOKEN_end_of_input
  | 11 -> TOKEN_error
  | _ -> failwith "tokenTagToTokenId: bad token"

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
let prodIdxToNonTerminal (prodIdx:int) = 
  match prodIdx with
    | 0 -> NONTERM__startstart 
    | 1 -> NONTERM_start 
    | 2 -> NONTERM_expression 
    | 3 -> NONTERM_expression 
    | 4 -> NONTERM_expression 
    | 5 -> NONTERM_expression 
    | 6 -> NONTERM_expression 
    | 7 -> NONTERM_expression 
    | 8 -> NONTERM_expression 
    | 9 -> NONTERM_expression 
    | 10 -> NONTERM_expression 
    | 11 -> NONTERM_expression 
    | 12 -> NONTERM_expression 
    | _ -> failwith "prodIdxToNonTerminal: bad production index"

let _fsyacc_endOfInputTag = 13 
let _fsyacc_tagOfErrorTerminal = 11

// This function gets the name of a token as a string
let token_to_string (t:token) = 
  match t with 
  | TIMES  -> "TIMES" 
  | DIV  -> "DIV" 
  | PLUS  -> "PLUS" 
  | MINUS  -> "MINUS" 
  | POW  -> "POW" 
  | SQRT  -> "SQRT" 
  | LOG  -> "LOG" 
  | LPAR  -> "LPAR" 
  | RPAR  -> "RPAR" 
  | EOF  -> "EOF" 
  | NUM _ -> "NUM" 

// This function gets the data carried by a token as an object
let _fsyacc_dataOfToken (t:token) = 
  match t with 
  | TIMES  -> (null : System.Object) 
  | DIV  -> (null : System.Object) 
  | PLUS  -> (null : System.Object) 
  | MINUS  -> (null : System.Object) 
  | POW  -> (null : System.Object) 
  | SQRT  -> (null : System.Object) 
  | LOG  -> (null : System.Object) 
  | LPAR  -> (null : System.Object) 
  | RPAR  -> (null : System.Object) 
  | EOF  -> (null : System.Object) 
  | NUM _fsyacc_x -> Microsoft.FSharp.Core.Operators.box _fsyacc_x 
let _fsyacc_gotos = [| 0us; 65535us; 1us; 65535us; 0us; 1us; 11us; 65535us; 0us; 2us; 14us; 4us; 15us; 5us; 16us; 6us; 17us; 7us; 18us; 8us; 19us; 9us; 20us; 10us; 21us; 11us; 22us; 12us; 24us; 13us; |]
let _fsyacc_sparseGotoTableRowOffsets = [|0us; 1us; 3us; |]
let _fsyacc_stateToProdIdxsTableElements = [| 1us; 0us; 1us; 0us; 6us; 1us; 2us; 3us; 4us; 5us; 6us; 1us; 1us; 6us; 2us; 2us; 3us; 4us; 5us; 6us; 6us; 2us; 3us; 3us; 4us; 5us; 6us; 6us; 2us; 3us; 4us; 4us; 5us; 6us; 6us; 2us; 3us; 4us; 5us; 5us; 6us; 6us; 2us; 3us; 4us; 5us; 6us; 6us; 6us; 2us; 3us; 4us; 5us; 6us; 7us; 6us; 2us; 3us; 4us; 5us; 6us; 8us; 6us; 2us; 3us; 4us; 5us; 6us; 9us; 6us; 2us; 3us; 4us; 5us; 6us; 10us; 6us; 2us; 3us; 4us; 5us; 6us; 12us; 1us; 2us; 1us; 3us; 1us; 4us; 1us; 5us; 1us; 6us; 1us; 7us; 1us; 8us; 1us; 9us; 1us; 10us; 1us; 11us; 1us; 12us; 1us; 12us; |]
let _fsyacc_stateToProdIdxsTableRowOffsets = [|0us; 2us; 4us; 11us; 13us; 20us; 27us; 34us; 41us; 48us; 55us; 62us; 69us; 76us; 83us; 85us; 87us; 89us; 91us; 93us; 95us; 97us; 99us; 101us; 103us; 105us; |]
let _fsyacc_action_rows = 26
let _fsyacc_actionTableElements = [|6us; 32768us; 2us; 21us; 3us; 22us; 5us; 19us; 6us; 20us; 7us; 24us; 10us; 23us; 0us; 49152us; 6us; 32768us; 0us; 14us; 1us; 15us; 2us; 16us; 3us; 17us; 4us; 18us; 9us; 3us; 0us; 16385us; 0us; 16386us; 0us; 16387us; 2us; 16388us; 0us; 14us; 1us; 15us; 2us; 16389us; 0us; 14us; 1us; 15us; 5us; 16390us; 0us; 14us; 1us; 15us; 2us; 16us; 3us; 17us; 4us; 18us; 0us; 16391us; 5us; 16392us; 0us; 14us; 1us; 15us; 2us; 16us; 3us; 17us; 4us; 18us; 2us; 16393us; 0us; 14us; 1us; 15us; 2us; 16394us; 0us; 14us; 1us; 15us; 6us; 32768us; 0us; 14us; 1us; 15us; 2us; 16us; 3us; 17us; 4us; 18us; 8us; 25us; 6us; 32768us; 2us; 21us; 3us; 22us; 5us; 19us; 6us; 20us; 7us; 24us; 10us; 23us; 6us; 32768us; 2us; 21us; 3us; 22us; 5us; 19us; 6us; 20us; 7us; 24us; 10us; 23us; 6us; 32768us; 2us; 21us; 3us; 22us; 5us; 19us; 6us; 20us; 7us; 24us; 10us; 23us; 6us; 32768us; 2us; 21us; 3us; 22us; 5us; 19us; 6us; 20us; 7us; 24us; 10us; 23us; 6us; 32768us; 2us; 21us; 3us; 22us; 5us; 19us; 6us; 20us; 7us; 24us; 10us; 23us; 6us; 32768us; 2us; 21us; 3us; 22us; 5us; 19us; 6us; 20us; 7us; 24us; 10us; 23us; 6us; 32768us; 2us; 21us; 3us; 22us; 5us; 19us; 6us; 20us; 7us; 24us; 10us; 23us; 6us; 32768us; 2us; 21us; 3us; 22us; 5us; 19us; 6us; 20us; 7us; 24us; 10us; 23us; 6us; 32768us; 2us; 21us; 3us; 22us; 5us; 19us; 6us; 20us; 7us; 24us; 10us; 23us; 0us; 16395us; 6us; 32768us; 2us; 21us; 3us; 22us; 5us; 19us; 6us; 20us; 7us; 24us; 10us; 23us; 0us; 16396us; |]
let _fsyacc_actionTableRowOffsets = [|0us; 7us; 8us; 15us; 16us; 17us; 18us; 21us; 24us; 30us; 31us; 37us; 40us; 43us; 50us; 57us; 64us; 71us; 78us; 85us; 92us; 99us; 106us; 113us; 114us; 121us; |]
let _fsyacc_reductionSymbolCounts = [|1us; 2us; 3us; 3us; 3us; 3us; 3us; 2us; 2us; 2us; 2us; 1us; 3us; |]
let _fsyacc_productionToNonTerminalTable = [|0us; 1us; 2us; 2us; 2us; 2us; 2us; 2us; 2us; 2us; 2us; 2us; 2us; |]
let _fsyacc_immediateActions = [|65535us; 49152us; 65535us; 16385us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 65535us; 16395us; 65535us; 16396us; |]
let _fsyacc_reductions ()  =    [| 
# 139 "CalculatorParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : expr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
                      raise (FSharp.Text.Parsing.Accept(Microsoft.FSharp.Core.Operators.box _1))
                   )
                 : '_startstart));
# 148 "CalculatorParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : expr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 33 "CalculatorParser.fsp"
                                                         _1 
                   )
# 33 "CalculatorParser.fsp"
                 : expr));
# 159 "CalculatorParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : expr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : expr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 43 "CalculatorParser.fsp"
                                                         TimesExpr(_1,_3) 
                   )
# 43 "CalculatorParser.fsp"
                 : expr));
# 171 "CalculatorParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : expr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : expr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 44 "CalculatorParser.fsp"
                                                         DivExpr(_1,_3) 
                   )
# 44 "CalculatorParser.fsp"
                 : expr));
# 183 "CalculatorParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : expr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : expr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 45 "CalculatorParser.fsp"
                                                         PlusExpr(_1,_3) 
                   )
# 45 "CalculatorParser.fsp"
                 : expr));
# 195 "CalculatorParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : expr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : expr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 46 "CalculatorParser.fsp"
                                                         MinusExpr(_1,_3) 
                   )
# 46 "CalculatorParser.fsp"
                 : expr));
# 207 "CalculatorParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : expr)) in
            let _3 = (let data = parseState.GetInput(3) in (Microsoft.FSharp.Core.Operators.unbox data : expr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 47 "CalculatorParser.fsp"
                                                         PowExpr(_1,_3) 
                   )
# 47 "CalculatorParser.fsp"
                 : expr));
# 219 "CalculatorParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : expr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 48 "CalculatorParser.fsp"
                                                         SqrtExpr(_2) 
                   )
# 48 "CalculatorParser.fsp"
                 : expr));
# 230 "CalculatorParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : expr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 49 "CalculatorParser.fsp"
                                                         LogExpr(_2) 
                   )
# 49 "CalculatorParser.fsp"
                 : expr));
# 241 "CalculatorParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : expr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 50 "CalculatorParser.fsp"
                                                         UPlusExpr(_2) 
                   )
# 50 "CalculatorParser.fsp"
                 : expr));
# 252 "CalculatorParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : expr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 51 "CalculatorParser.fsp"
                                                         UMinusExpr(_2) 
                   )
# 51 "CalculatorParser.fsp"
                 : expr));
# 263 "CalculatorParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _1 = (let data = parseState.GetInput(1) in (Microsoft.FSharp.Core.Operators.unbox data : float)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 52 "CalculatorParser.fsp"
                                                         Num(_1) 
                   )
# 52 "CalculatorParser.fsp"
                 : expr));
# 274 "CalculatorParser.fs"
        (fun (parseState : FSharp.Text.Parsing.IParseState) ->
            let _2 = (let data = parseState.GetInput(2) in (Microsoft.FSharp.Core.Operators.unbox data : expr)) in
            Microsoft.FSharp.Core.Operators.box
                (
                   (
# 53 "CalculatorParser.fsp"
                                                         _2 
                   )
# 53 "CalculatorParser.fsp"
                 : expr));
|]
# 286 "CalculatorParser.fs"
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
    numTerminals = 14;
    productionToNonTerminalTable = _fsyacc_productionToNonTerminalTable  }
let engine lexer lexbuf startState = (tables ()).Interpret(lexer, lexbuf, startState)
let start lexer lexbuf : expr =
    Microsoft.FSharp.Core.Operators.unbox ((tables ()).Interpret(lexer, lexbuf, 0))
