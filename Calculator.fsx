// This script implements our interactive calculator

// We need to import a couple of modules, including the generated lexer and parser
#r "C:/Users/Noah/.nuget/packages/fslexyacc/10.0.0/build/fsyacc/net46/FsLexYacc.Runtime.dll"
open FSharp.Text.Lexing
open System
#load "CalculatorTypesAST.fs"
open CalculatorTypesAST
#load "CalculatorParser.fs"
open CalculatorParser
#load "CalculatorLexer.fs"
open CalculatorLexer

// We define the evaluation function recursively, by induction on the structure
// of arithmetic expressions (AST of type  expr)    
    
(*
let rec evala a =
    match a with
    | Num(x) -> x
    | Var(x) -> 0.0 //return value of x?
    | PlusExpr(x,y) -> evala(x) + evala(y)
    | MinusExpr(x,y) -> evala(x) - evala(y)
    | TimesExpr(x,y) -> evala(x) * evala(y)
    | DivExpr(x,y) -> evala(x) / evala(y)
    | PowExpr(x,y) -> evala(x) ** evala(y)
    | UMinusExpr(x) -> - evala(x)

*)
let rec evalASyntax a =
    match a with
    | Num(_) -> true
    | Var(_) -> true
    | PlusExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | MinusExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | TimesExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | DivExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | PowExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | UMinusExpr(x) -> evalASyntax(x)
    | _ -> false

(*let rec evalb b =
    match b with
    | True -> true
    | False -> false
    | AndHardExpr(x,y) -> evalb(x) && evalb(y)
    | OrHardExpr(x,y) -> evalb(x) || evalb(y)
    | NotExpr(x) -> not (evalb(x))
    | EqualExpr(x,y) -> evala(x) = evala(y)
    | NEqualExpr(x,y) -> evala(x) <> evala(y)
    | GtExpr(x,y) -> evala(x) > evala(y)
    | GteExpr(x,y) -> evala(x) >= evala(y)
    | LtExpr(x,y) -> evala(x) < evala(y)
    | LteExpr(x,y) -> evala(x) <= evala(y)*)
    
let rec evalBSyntax b =
    match b with
    | True -> true
    | False -> true
    | AndHardExpr(x,y) -> evalBSyntax(x) && evalBSyntax(y)
    | OrHardExpr(x,y) -> evalBSyntax(x) && evalBSyntax(y)
    | NotExpr(x) -> evalBSyntax(x)
    | EqualExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | NEqualExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | GtExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | GteExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | LtExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | LteExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | _ -> false
    
(*let rec evalc c =
    match c with
    | AssignExpr(x) -> evala(x)
    | AssignArrExpr(x,y) -> evala(x)
                            evala(y)
    | SeparatorExpr(x,y) -> evalc x
                            evalc y
    | IfExpr(x) -> evalgc(x)
    | DoExpr(x) -> evalgc(x)
and evalgc gc =
    match gc with
    | FuncExpr(b, c) -> evalb(b)
                        evalc(c)
    | ConcExpr(gc1, gc2) -> evalgc(gc1)
                            evalgc(gc2)*)
    
let rec evalCSyntax c =
   match c with
   | AssignExpr(x) -> evalASyntax x
   | AssignArrExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
   | SeparatorExpr(x,y) -> evalCSyntax x && evalCSyntax y
   | IfExpr(x) -> evalGCSyntax(x)
   | DoExpr(x) -> evalGCSyntax(x)
   | Skip -> true   
and evalGCSyntax gc =
    match gc with
    | FuncExpr(b, c) -> evalBSyntax(b) && evalCSyntax(c)
    | ConcExpr(gc1, gc2) -> evalGCSyntax(gc1) && evalGCSyntax(gc2)

let parse input =
    // translate string into a buffer of characters
    let lexbuf = LexBuffer<char>.FromString input
    // translate the buffer into a stream of tokens and parse them
    let res = CalculatorParser.start CalculatorLexer.tokenize lexbuf
    // return the result of parsing (i.e. value of type "expr")
    res

// We implement here the function that interacts with the user
let rec compute n =
    if n = 0 then
        printfn "Bye bye"
    else
        printf "Enter a program in the Guarded Commands Language: "
        let e = parse (Console.ReadLine())
        // We parse the input string
        // and print the result of evaluating it
        Console.WriteLine("Parsed tokens: {0} ", e )
(*
        Console.WriteLine("Result: {0}", evalCSyntax(e))
*)
        compute n
  

// Start interacting with the user
compute 3
