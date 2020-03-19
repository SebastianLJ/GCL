open System

// This script implements our interactive calculator

// We need to import a couple of modules, including the generated lexer and parser
#r "C:/Users/emils//.nuget/packages/fslexyacc/10.0.0/build/fsyacc/net46/FsLexYacc.Runtime.dll"
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
    | A(_) -> true
    | PlusExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | MinusExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | TimesExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | DivExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | PowExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | UMinusExpr(x) -> evalASyntax(x)

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
    | AndExpr(x,y) -> evalBSyntax x && evalBSyntax y
    | OrExpr(x,y) -> evalBSyntax x && evalBSyntax y
    | NotExpr(x) -> evalBSyntax(x)
    | EqualExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | NEqualExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | GtExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | GteExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | LtExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    | LteExpr(x,y) -> evalASyntax(x) && evalASyntax(y)
    
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
   | AssignExpr(_, y) -> evalASyntax y
   | AssignArrExpr(_,y,z) -> evalASyntax(y) && evalASyntax(z)
   | SeparatorExpr(x,y) -> evalCSyntax x && evalCSyntax y
   | IfExpr(x) -> evalGCSyntax(x)
   | DoExpr(x) -> evalGCSyntax(x)
   | Skip -> true   
and evalGCSyntax gc =
    match gc with
    | FuncExpr(b, c) -> evalBSyntax(b) && evalCSyntax(c)
    | ConcExpr(gc1, gc2) -> evalGCSyntax(gc1) && evalGCSyntax(gc2)
    
let rec doneGC gc =
    match gc with
    | FuncExpr(b,_) ->  NotExpr(b)
    | ConcExpr(gc1, gc2)-> AndExpr(doneGC gc1, doneGC gc2)



let rec stringifyA = function
    | Num(x) -> string x
    | Var(x) -> x
    | A(x) -> string x
    | PlusExpr(x,y)  -> stringifyA x + "+" + stringifyA y
    | MinusExpr(x,y) -> stringifyA x + "-" + stringifyA y
    | TimesExpr(x,y) -> stringifyA x + "*" + stringifyA y
    | DivExpr(x,y)   -> stringifyA x + "/" + stringifyA y
    | PowExpr(x,y)   -> stringifyA x + "^" + stringifyA y
    | UMinusExpr(x)  -> "-" + stringifyA x

let stringifyC = function
    | AssignExpr(var, value)            -> var + ":=" + stringifyA value
    | AssignArrExpr(var, index, value)  -> string var + "[" + stringifyA index + "]" + ":=" + stringifyA value 
    | Skip                              -> "skip"
    | _                                 -> failwith "Something went wrong!"

let rec stringifyB = function
    | True -> "true"
    | False -> "false"
    | AndExpr(x,y) -> stringifyB x + "&" + stringifyB y
    | OrExpr(x,y) -> stringifyB x + "|" + stringifyB y
    | AndHardExpr(x,y) -> stringifyB x + "&&" + stringifyB y 
    | OrHardExpr(x,y) -> stringifyB x + "||" + stringifyB y
    | NotExpr(x) -> "!" + "(" + stringifyB x + ")"
    | EqualExpr(x,y) -> stringifyA x + "==" + stringifyA y
    | NEqualExpr(x,y) -> stringifyA x + "!=" + stringifyA y
    | GtExpr(x,y) -> stringifyA x + ">" + stringifyA y
    | GteExpr(x,y) -> stringifyA x + ">=" + stringifyA y
    | LtExpr(x,y) -> stringifyA x + "<" + stringifyA y
    | LteExpr(x,y) -> stringifyA x + "<=" + stringifyA y
              
let rec edgesC qS qE c n =
    match c with
    | AssignExpr x         -> [qS, stringifyC (AssignExpr x), qE]
    | AssignArrExpr x      -> [qS, stringifyC (AssignArrExpr x), qE]
    | Skip                 -> [qS, stringifyC Skip, qE]
    | SeparatorExpr(c1,c2) -> edgesC qS ("q" + string n) c1 (n+1) @ edgesC ("q" + string n) qE c2 (n+1)
    | IfExpr gc            -> edgesGC qS qE gc n
    | DoExpr gc            -> edgesGC qS qS gc n @ [qS, stringifyB(doneGC gc), qE] 
and edgesGC qs qe gc n =
    match gc with
    | FuncExpr(b, c)        -> [qs, stringifyB b, "q" + string n] @ edgesC ("q" + string n) qe c (n+1)
    | ConcExpr(gc1, gc2)    -> edgesGC qs qe gc1 n @ edgesGC qs qe gc2 n
    
let rec calculateUsedNodesGc gc =
    match gc with
    | FuncExpr (_,c) -> calculateUsedNodesC c + 1
    | ConcExpr (gc1, gc2) -> calculateUsedNodesGc gc1 + calculateUsedNodesGc gc2
and calculateUsedNodesC c =
    match c with
    | SeparatorExpr(c1,c2) -> calculateUsedNodesC c1 + calculateUsedNodesC c2 + 1
    | _ -> 0
    
let rec edgesD2 qs qe gc n d =
    match gc with
    | FuncExpr (b,c) -> ((qs, stringifyB (AndExpr (b, NotExpr d)), "q" + string n)::edgesD ("q" + string n) qe c (n+1), OrExpr(b, d))
    | ConcExpr (gc1,gc2) -> let (e1, d1) = edgesD2 qs qe gc1 n d
                            let (e2, d2) = edgesD2 qs qe gc2 (n + calculateUsedNodesGc gc1) d1
                            (e1@e2, d2)
and edgesD qS qE c n =
    match c with
    | AssignExpr x         -> [qS, stringifyC (AssignExpr x), qE]
    | AssignArrExpr x      -> [qS, stringifyC (AssignArrExpr x), qE]
    | Skip                 -> [qS, stringifyC Skip, qE]
    | SeparatorExpr(c1,c2) -> edgesD qS ("q" + string n) c1 (n+1) @ edgesD ("q" + string n) qE c2 (n+1)
    | IfExpr gc -> let (E, _) = edgesD2 qS qE gc n False
                   E
    | DoExpr gc -> let (E, d) = edgesD2 qS qS gc n False
                   E@[(qS, stringifyB (NotExpr d), qE)]

let rec graphVizify = function
    | [] -> ""
    | (qs, label, qe)::xs -> qs + " -> " + qe + " [label = \"" + label + "\"];\n" + graphVizify xs

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
        try
         // We parse the input string
        let e = parse (Console.ReadLine())
        // and print the result of evaluating it
        Console.WriteLine("Parsed tokens (AST): {0} ", e )
        printfn "Program Graph: %A" (edgesC "qStart" "qEnd" e 1)
        printfn "GraphViz formatted text: \n%s" (graphVizify (edgesC "qStart" "qEnd" e 1))
        printfn "Deterministic Program Graph %A" (edgesD "qStart" "qEnd" e 1)
        compute n
        with err -> //printfn "%s" (string err)
                    printfn "Invalid Syntax!"
                    compute(n-1)
  

// Start interacting with the user
compute 3
