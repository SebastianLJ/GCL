// This script implements our interactive calculator

// We need to import a couple of modules, including the generated lexer and parser
#r "FsLexYacc.Runtime.10.0.0/lib/net46/FsLexYacc.Runtime.dll"
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

let rec eval e = //Maybe split eval up into two function, we need tob e able to return numbers (in arithmetic expressions), boolean epressions (2>3), but also a memory in case of memory-assignemnts such as x:=2 or A[2]=1.
  //only way that it is possible to return these different types is to create seperate functions.

    
    
    
let rec evala a = match a with
    | N(x) -> x
    | X(x) -> 0 //return value of x?
    | PlusExpr(x,y) -> evala(x) + evala(y)
    | MinusExpr(x,y) -> evala(x) - evala(y)
    | TimesExpr(x,y) -> evala(x) * evala(y)
    | DivExpr(x,y) -> evala(x) / evala(y)
    | PowExpr(x,y) -> int (float (evala(x)) ** float (evala(y)))
    | UMinusExpr(x) -> - evala(x)


let rec evalb b = match b with
    | Tf(x) -> x //return true/false
    | AndHardExpr(x,y) -> evalb(x) && evalb(x)
    | OrHardExpr(x,y) -> evalb(x) || evalb(x)
    | NotExpr(x) -> not (evalb(x))
    | EqualExpr(x,y) -> evala(x) = evala(y)
    | NEqualExpr(x,y) -> evala(x) <> evala(y)
    | GtExpr(x,y) -> evala(x) > evala(y)
    | GteExpr(x,y) -> evala(x) >= evala(y)
    | LtExpr(x,y) -> evala(x) < evala(y)
    | LteExpr(x,y) -> evala(x) <= evala(y)
    
let rec evalc c = match c with
    | AssignExpr(x,y) -> 0
    | AssignArrExpr(x,y,z) -> 0
    | SeperatorExpr(x,y) -> 0
    | IfExpr(x) -> 0
    | DoExpr(x) -> 0 

let rec evalgc gc = match gc with
    | FuncExpr(b, c) -> evalb(b)
                        evalc(c)
    | ConcExpr(gc1, gc2) -> evalgc(gc1)
                            evalgc(gc2)

let parse input =
    // translate string into a buffer of characters
    let lexbuf = LexBuffer<char>.FromString input
    // translate the buffer into a stream of tokens and parse them
    let res = CalculatorParser.start CalculatorLexer.tokenize lexbuf
    // return the result of parsing (i.e. value of type "expr")
    res

// We implement here the function that interacts with the user
let rec compute n =
    if n = "exit" then
        printfn "Bye bye"
    else
        printf "Enter a program in the Guarded Commands Language: "
        try
        // We parse the input string
        let e = parse (Console.ReadLine())
        // and print the result of evaluating it
        printfn "Result: %f" (eval(e))
        compute n
        with err -> printfn "invalid syntax"

// Start interacting with the user
compute 3
