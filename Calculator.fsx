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
let variables = Map.empty.Add('x', a x);;
let arrays = Map.empty.Add('a', [|0|]);;
let rec eval e = //Maybe split eval up into two function, we need tob e able to return numbers (in arithmetic expressions), boolean epressions (2>3), but also a memory in case of memory-assignemnts such as x:=2 or A[2]=1.
  //only way that it is possible to reutrn these different types is to create seperate functions.
  match e with
    | AssignExpr(x,y) -> variables.Add(x,y) //todo
    | AssignArrExpr(x,y,z) -> //todo
    | SeperatorExpr(x,y) -> //todo
    | IfExpr(x) -> 
    | DoExpr(x) -> 
    | FuncExpr(b, C)-> //todo
    | ConcExpr(GC1, GC2) ->   //todo
    | N(x) -> x
    | X(x) -> x //return value of x?
    | PlusExpr(x,y) -> eval(x) + eval (y)
    | MinusExpr(x,y) -> eval(x) - eval (y)
    | TimesExpr(x,y) -> eval(x) * eval (y)
    | DivExpr(x,y) -> eval(x) / eval (y)
    | PowExpr(x,y) -> eval(x) ** eval (y)
    | UMinusExpr(x) -> - eval(x)

    | Tf(x) -> x //return true/false
    | AndhExpr(x,y) -> eval(x) && eval(x)
    | OrhExpr(x,y) -> eval(x) || eval(x)
    | NotExpr(x) -> not eval(x)
    | EqualExpr(x,y) -> eval(x) = eval(y)
    | NequalExpr(x,y) -> eval(x) <> eval(y)
    | GtExpr(x,y) -> eval(x) > eval(y)
    | GteExpr(x,y) -> eval(x) >= eval(y)
    | LtExpr(x,y) -> eval(x) < eval(y)
    | LteExpr(x,y) -> eval(x) <= eval(y)

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
