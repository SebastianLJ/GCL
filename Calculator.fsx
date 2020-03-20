open System

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
let updateVar var value l =
    l
    |> List.map (fun (k, v) ->
        if k = var then k, value
        else k, v)

let rec evalASyntax a =
    match a with
    | Num(_) -> true
    | Var(_) -> true
    | Array(_) -> true
    | PlusExpr(x, y) -> evalASyntax (x) && evalASyntax (y)
    | MinusExpr(x, y) -> evalASyntax (x) && evalASyntax (y)
    | TimesExpr(x, y) -> evalASyntax (x) && evalASyntax (y)
    | DivExpr(x, y) -> evalASyntax (x) && evalASyntax (y)
    | PowExpr(x, y) -> evalASyntax (x) && evalASyntax (y)
    | UMinusExpr(x) -> evalASyntax (x)



let rec AEval aExp mem =
    match (aExp, mem) with
    | (Num(x), _) -> Some x
    | (Var(x), (xs, _)) -> Some(snd (List.find (fun (id, _) -> id = x) (xs)))
    | (Array(c, a), (_, ys)) ->
        match (AEval a mem) with
        | Some i -> Some(List.item i (snd (List.find (fun (id, _) -> id = c) ys)))
        | _ -> None
    | (PlusExpr(x, y), mem) ->
        match (AEval x mem, AEval y mem) with
        | (Some x, Some y) -> Some(x + y)
        | _ -> None
    | (MinusExpr(x, y), mem) ->
        match (AEval x mem, AEval y mem) with
        | (Some x, Some y) -> Some(x - y)
        | _ -> None
    | (TimesExpr(x, y), mem) ->
        match (AEval x mem, AEval y mem) with
        | (Some x, Some y) -> Some(x * y)
        | _ -> None
    | (DivExpr(x, y), mem) ->
        match (AEval x mem, AEval y mem) with
        | (Some x, Some y) -> Some(x / y)
        | _ -> None
    | (PowExpr(x, y), mem) ->
        match (AEval x mem, AEval y mem) with
        | (Some x, Some y) -> Some((int) ((float x) ** (float y)))
        | _ -> None
    | (UMinusExpr(x), mem) ->
        match (AEval x mem) with
        | (Some x) -> Some(-1 * x)
        | _ -> None

let rec BEval bExp mem =
    match (bExp, mem) with
    | (True, _) -> Some true
    | (False, _) -> Some false
    | (AndExpr(x, y), mem) ->
        match (BEval x mem, BEval y mem) with
        | (Some x, Some y) ->
            match x with
            | true -> Some(y)
            | false -> Some false
        | _ -> None
    | (AndHardExpr(x, y), mem) ->
        match (BEval x mem) with
        | (Some x) ->
            match x with
            | true -> BEval y mem
            | false -> Some false
        | _ -> None
    | (OrExpr(x, y), mem) ->
        match (BEval x mem, BEval y mem) with
        | (Some x, Some y) ->
            match x with
            | true -> Some true
            | false -> Some(y)
        | _ -> None
    | (OrHardExpr(x, y), mem) ->
        match (BEval x mem) with
        | (Some x) ->
            match x with
            | true -> Some true
            | false -> BEval y mem
        | _ -> None
    | (NotExpr(x), mem) ->
        match (BEval x mem) with
        | (Some x) -> Some(not x)
        | _ -> None
    | (EqualExpr(x, y), mem) ->
        match (AEval x mem, AEval y mem) with
        | (Some x, Some y) -> Some(x = y)
        | _ -> None
    | (NEqualExpr(x, y), mem) ->
        match (AEval x mem, AEval y mem) with
        | (Some x, Some y) -> Some(not (x = y))
        | _ -> None
    | (GtExpr(x, y), mem) ->
        match (AEval x mem, AEval y mem) with
        | (Some x, Some y) -> Some(x > y)
        | _ -> None
    | (GteExpr(x, y), mem) ->
        match (AEval x mem, AEval y mem) with
        | (Some x, Some y) -> Some(x >= y)
        | _ -> None
    | (LtExpr(x, y), mem) ->
        match (AEval x mem, AEval y mem) with
        | (Some x, Some y) -> Some(x < y)
        | _ -> None
    | (LteExpr(x, y), mem) ->
        match (AEval x mem, AEval y mem) with
        | (Some x, Some y) -> Some(x <= y)
        | _ -> None



let rec evalBSyntax b =
    match b with
    | True -> true
    | False -> true
    | AndHardExpr(x, y) -> evalBSyntax (x) && evalBSyntax (y)
    | OrHardExpr(x, y) -> evalBSyntax (x) && evalBSyntax (y)
    | AndExpr(x, y) -> evalBSyntax x && evalBSyntax y
    | OrExpr(x, y) -> evalBSyntax x && evalBSyntax y
    | NotExpr(x) -> evalBSyntax (x)
    | EqualExpr(x, y) -> evalASyntax (x) && evalASyntax (y)
    | NEqualExpr(x, y) -> evalASyntax (x) && evalASyntax (y)
    | GtExpr(x, y) -> evalASyntax (x) && evalASyntax (y)
    | GteExpr(x, y) -> evalASyntax (x) && evalASyntax (y)
    | LtExpr(x, y) -> evalASyntax (x) && evalASyntax (y)
    | LteExpr(x, y) -> evalASyntax (x) && evalASyntax (y)


let rec evalCSyntax c =
    match c with
    | AssignExpr(_, y) -> evalASyntax y
    | AssignArrExpr(_, y, z) -> evalASyntax (y) && evalASyntax (z)
    | SeparatorExpr(x, y) -> evalCSyntax x && evalCSyntax y
    | IfExpr(x) -> evalGCSyntax (x)
    | DoExpr(x) -> evalGCSyntax (x)
    | Skip -> true

and evalGCSyntax gc =
    match gc with
    | FuncExpr(b, c) -> evalBSyntax (b) && evalCSyntax (c)
    | ConcExpr(gc1, gc2) -> evalGCSyntax (gc1) && evalGCSyntax (gc2)

let rec doneGC gc =
    match gc with
    | FuncExpr(b, _) -> NotExpr(b)
    | ConcExpr(gc1, gc2) -> AndExpr(doneGC gc1, doneGC gc2)

let rec stringifyA =
    function
    | Num(x) -> string x
    | Var(x) -> x
    | Array(x, i) -> string x + "[" + stringifyA i + "]"
    | PlusExpr(x, y) -> stringifyA x + "+" + stringifyA y
    | MinusExpr(x, y) -> stringifyA x + "-" + stringifyA y
    | TimesExpr(x, y) -> stringifyA x + "*" + stringifyA y
    | DivExpr(x, y) -> stringifyA x + "/" + stringifyA y
    | PowExpr(x, y) -> stringifyA x + "^" + stringifyA y
    | UMinusExpr(x) -> "-" + stringifyA x

let rec stringifyB =
    function
    | True -> "true"
    | False -> "false"
    | AndExpr(x, y) -> stringifyB x + "&" + stringifyB y
    | OrExpr(x, y) -> stringifyB x + "|" + stringifyB y
    | AndHardExpr(x, y) -> stringifyB x + "&&" + stringifyB y
    | OrHardExpr(x, y) -> stringifyB x + "||" + stringifyB y
    | NotExpr(x) -> "!" + "(" + stringifyB x + ")"
    | EqualExpr(x, y) -> stringifyA x + "==" + stringifyA y
    | NEqualExpr(x, y) -> stringifyA x + "!=" + stringifyA y
    | GtExpr(x, y) -> stringifyA x + ">" + stringifyA y
    | GteExpr(x, y) -> stringifyA x + ">=" + stringifyA y
    | LtExpr(x, y) -> stringifyA x + "<" + stringifyA y
    | LteExpr(x, y) -> stringifyA x + "<=" + stringifyA y

let rec calculateUsedNodesGc gc =
    match gc with
    | FuncExpr(_, c) -> calculateUsedNodesC c + 1
    | ConcExpr(gc1, gc2) -> calculateUsedNodesGc gc1 + calculateUsedNodesGc gc2

and calculateUsedNodesC c =
    match c with
    | SeparatorExpr(c1, c2) -> calculateUsedNodesC c1 + calculateUsedNodesC c2 + 1
    | _ -> 0

let rec edgesC qS qE c n =
    match c with
    | AssignExpr x -> [ qS, VAsgn x, qE ]
    | AssignArrExpr x -> [ qS, AAsgn x, qE ]
    | Skip -> [ qS, Action.Skip, qE ]
    | SeparatorExpr(c1, c2) -> edgesC qS ("q" + string n) c1 (n + 1) @ edgesC ("q" + string n) qE c2 (n + 1)
    | IfExpr gc -> edgesGC qS qE gc n
    | DoExpr gc -> edgesGC qS qS gc n @ [ qS, Test(doneGC gc), qE ]

and edgesGC qs qe gc n =
    match gc with
    | FuncExpr(b, c) -> [ qs, Test b, "q" + string n ] @ edgesC ("q" + string n) qe c (n + 1)
    | ConcExpr(gc1, gc2) -> edgesGC qs qe gc1 n @ edgesGC qs qe gc2 (n + calculateUsedNodesGc gc1)

let rec edgesD2 qs qe gc n d =
    match gc with
    | FuncExpr(b, c) ->
        ((qs, Test(AndExpr(b, NotExpr d)), "q" + string n) :: edgesD ("q" + string n) qe c (n + 1), OrExpr(b, d))
    | ConcExpr(gc1, gc2) ->
        let (e1, d1) = edgesD2 qs qe gc1 n d
        let (e2, d2) = edgesD2 qs qe gc2 (n + calculateUsedNodesGc gc1) d1
        (e1 @ e2, d2)

and edgesD qS qE c n =
    match c with
    | AssignExpr x -> [ qS, VAsgn x, qE ]
    | AssignArrExpr x -> [ qS, AAsgn x, qE ]
    | Skip -> [ qS, Action.Skip, qE ]
    | SeparatorExpr(c1, c2) -> edgesD qS ("q" + string n) c1 (n + 1) @ edgesD ("q" + string n) qE c2 (n + 1)
    | IfExpr gc ->
        let (E, _) = edgesD2 qS qE gc n False
        E
    | DoExpr gc ->
        let (E, d) = edgesD2 qS qS gc n False
        E @ [ (qS, Test(NotExpr d), qE) ]

let rec stringify action =
    match action with
    | VAsgn(x, a) -> x + ":=" + stringifyA a
    | AAsgn(x, i, a) -> string x + "[" + stringifyA i + "]" + stringifyA a
    | Action.Skip -> "skip"
    | Test b -> stringifyB b

let rec graphVizify =
    function
    | [] -> ""
    | (qs, label, qe) :: xs -> qs + " -> " + qe + " [label = \"" + stringify label + "\"];\n" + graphVizify xs

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
            printf "Arithmetic expression: 5+5 = %A" (AEval (PlusExpr(Num 5, Num 5)) ([], []))
            let e = parse (Console.ReadLine())
            // and print the result of evaluating it
            Console.WriteLine("Parsed tokens (AST): {0} ", e)
            printf "Deterministic or non-deterministic program graph (d/nd)?"
            let pg = Console.ReadLine()
            if (pg = "nd") then
                printfn "NPG: \n%A\n\nGraphViz formatted text: \n%s" (edgesC "qStart" "qEnd" e 1)
                    (graphVizify (edgesC "qStart" "qEnd" e 1))
            elif (pg = "d") then
                printfn "DPG: \n%A\n\nGraphViz formatted text: \n%s" (edgesD "qStart" "qEnd" e 1)
                    (graphVizify (edgesD "qStart" "qEnd" e 1))
            compute n
        with err ->
            printfn "Invalid Syntax!"
            compute (n - 1)


// Start interacting with the user
compute 3
