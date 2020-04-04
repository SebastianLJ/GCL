open System
open System.Collections.Generic

// This script implements GCL

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

#load "InputTypesAST.fs"

open InputTypesAST

#load "InputParser.fs"

open InputParser

#load "InputLexer.fs"

open InputLexer



// We define the evaluation function recursively, by induction on the structure
// of arithmetic expressions (AST of type  expr)
let updateVar var value l =
    l
    |> List.map (fun (k, v) ->
        if k = var then k, value
        else k, v)
    
let updateArr c index value memory =
    let rec updateIndexValue index arr =
        match (index, arr) with
        | (0, _::arr) -> value::arr
        | (n, a::arr) -> a::updateIndexValue (n-1) arr
        | _           -> failwith "It should not be possible to get here!" //Isn't it possible to get here if you input a negative index? 
    List.map (fun (k, arr) -> if k=c then k, updateIndexValue index arr else k, arr) (memory)

let rec evalASyntax a =
    match a with
    | PlusExpr(x, y)    -> evalASyntax x && evalASyntax y
    | MinusExpr(x, y)   -> evalASyntax x && evalASyntax y
    | TimesExpr(x, y)   -> evalASyntax x && evalASyntax y
    | DivExpr(x, y)     -> evalASyntax x && evalASyntax y
    | PowExpr(x, y)     -> evalASyntax x && evalASyntax y
    | UMinusExpr x      -> evalASyntax x
    | _                 -> true

let rec AEval aExp mem =
    match (aExp, mem) with
    | (Num x, _) -> Some x
    | (Var x, (xs, _)) -> try Some(snd (List.find (fun (id, _) -> id = x) xs)) with err -> failwith ("The variable " + x + " might not have been initialized")
    | (Array(c, a), (_, ys)) ->
        match (AEval a mem) with
        | Some i -> try Some(List.item i (snd (List.find (fun (id, _) -> id = c) ys))) with | :? ArgumentException -> failwith ("Index out of bounds for array \'" + string c + "\' at index: " + string i)
                                                                                            | :? KeyNotFoundException -> failwith ("The array \'" + string c + "\' might not have been initialized")
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
    | (UMinusExpr x, mem) ->
        match (AEval x mem) with
        | (Some x) -> Some(-1 * x)
        | _ -> None

let rec BEval bExp mem =
    match bExp with
    | True -> Some true
    | False -> Some false
    | AndExpr(x, y) ->
        match (BEval x mem, BEval y mem) with
        | (Some x, Some y) ->
            match x with
            | true -> Some y
            | false -> Some false
        | _ -> None
    | AndHardExpr(x, y) ->
        match BEval x mem with
        | (Some x) ->
            match x with
            | true -> BEval y mem
            | false -> Some false
        | _ -> None
    | OrExpr(x, y) ->
        match (BEval x mem, BEval y mem) with
        | (Some x, Some y) ->
            match x with
            | true -> Some true
            | false -> Some y
        | _ -> None
    | OrHardExpr(x, y) ->
        match BEval x mem with
        | (Some x) ->
            match x with
            | true -> Some true
            | false -> BEval y mem
        | _ -> None
    | NotExpr x ->
        match BEval x mem with
        | Some x -> Some(not x)
        | _ -> None
    | EqualExpr(x, y) ->
        match (AEval x mem, AEval y mem) with
        | (Some x, Some y) -> Some(x = y)
        | _ -> None
    | NEqualExpr(x, y) ->
        match (AEval x mem, AEval y mem) with
        | (Some x, Some y) -> Some(x <> y)
        | _ -> None
    | GtExpr(x, y) ->
        match (AEval x mem, AEval y mem) with
        | (Some x, Some y) -> Some(x > y)
        | _ -> None
    | GteExpr(x, y) ->
        match (AEval x mem, AEval y mem) with
        | (Some x, Some y) -> Some(x >= y)
        | _ -> None
    | LtExpr(x, y) ->
        match (AEval x mem, AEval y mem) with
        | (Some x, Some y) -> Some(x < y)
        | _ -> None
    | LteExpr(x, y) ->
        match (AEval x mem, AEval y mem) with
        | (Some x, Some y) -> Some(x <= y)
        | _ -> None
        

type mem = (string*int) list * (char*int list) list
let isVarInDomain var memory = match List.exists (fun (v,_) -> v = var) (fst memory) with
                               | true -> true
                               | false -> failwith ("The variable " + var + " might not have been initialized")
    
let isArrInDomain c index memory =
    let rec findIndex arr i =
        match arr with
        | [] -> failwith ("Index out of bounds for array \'" + string c + "\' at index: " + string index)
        | _ when i = 0 -> true
        | _::arr -> findIndex arr (i-1)
    match (List.tryFind (fun (id,_) -> id = c) (snd memory)) with
    | Some array -> findIndex (snd array) index
    | _          -> failwith ("The array \'" + string c + "\' might not have been initialized")
    
let sem action memory =
    match action with
    | Action.Skip        -> Some memory
    | VAsgn (var, value) -> match (AEval value memory, isVarInDomain var memory) with
                            | (Some value, true) -> Some (updateVar var value (fst memory), snd memory)
                            | _                  -> None
    | AAsgn (c,i,a)      -> match (AEval i memory, AEval a memory) with
                            | (Some z1, Some z2) when isArrInDomain c z1 memory -> Some (fst memory, updateArr c z1 z2 (snd memory))
                            | _                                                 -> None
                           
    | Test b             -> match BEval b memory with
                            | Some true -> Some memory
                            | _         -> None
                            

let transition pg sem (q,mem) =
    let E = List.filter (fun (qStart,_,_) -> qStart = q) pg
    let rec trans edges =
        match edges with
        | []                      -> []
        | (_, action, qTo)::edges -> match sem action mem with
                                     | Some mem' -> (qTo, mem') :: trans edges
                                     | None      -> trans edges
    trans E
    
let rec iterate pg sem (q,mem) c =
    match transition pg sem (q,mem) with
    | []               -> printfn "%A" (q,mem)
                          (q,mem)
    | t::_ when c > 0  -> printfn "%A" t
                          iterate pg sem t (c-1)
    | _                -> printfn "%A" (q,mem)
                          (q,mem)
    
let interpret pg memStart =
    iterate pg sem ("qStart", memStart) 40
    
let stringifyMem mem =
    let rec iteri arr array i acc =
        match array with
        | [] -> acc
        | x::xs -> iteri arr xs (i+1) (acc + string arr + "[" + string i + "]: " + string x + "\n")
    List.fold (fun acc (var, value) -> acc + var + ": " + string value + "\n") "" (fst mem)
    + List.fold (fun acc (arr, array) -> acc + iteri arr array 0 "") "" (snd mem)
    
let generateTerminalInformation (q,mem) =
    "status: " + if q = "qEnd" then "terminated\n" else "stuck\n"
    + "Node: " + q + "\n"
    + stringifyMem mem

let rec evalBSyntax b =
    match b with
    | True                 -> true
    | False                -> true
    | AndHardExpr(x, y)    -> evalBSyntax x && evalBSyntax y
    | OrHardExpr(x, y)     -> evalBSyntax x && evalBSyntax y
    | AndExpr(x, y)        -> evalBSyntax x && evalBSyntax y
    | OrExpr(x, y)         -> evalBSyntax x && evalBSyntax y
    | NotExpr x            -> evalBSyntax x
    | EqualExpr(x, y)      -> evalASyntax x && evalASyntax y
    | NEqualExpr(x, y)     -> evalASyntax x && evalASyntax y
    | GtExpr(x, y)         -> evalASyntax x && evalASyntax y
    | GteExpr(x, y)        -> evalASyntax x && evalASyntax y
    | LtExpr(x, y)         -> evalASyntax x && evalASyntax y
    | LteExpr(x, y)        -> evalASyntax x && evalASyntax y


let rec evalCSyntax c =
    match c with
    | AssignExpr(_, y) -> evalASyntax y
    | AssignArrExpr(_, y, z) -> evalASyntax y && evalASyntax z
    | SeparatorExpr(x, y) -> evalCSyntax x && evalCSyntax y
    | IfExpr x -> evalGCSyntax x
    | DoExpr x -> evalGCSyntax x
    | Skip -> true

and evalGCSyntax gc =
    match gc with
    | FuncExpr(b, c) -> evalBSyntax b && evalCSyntax c
    | ConcExpr(gc1, gc2) -> evalGCSyntax gc1 && evalGCSyntax gc2

let rec doneGC gc =
    match gc with
    | FuncExpr(b, _) -> NotExpr b
    | ConcExpr(gc1, gc2) -> AndExpr(doneGC gc1, doneGC gc2)

let rec stringifyA = function
    | Num x -> string x
    | Var(x) -> x
    | Array(x, i) -> string x + "[" + stringifyA i + "]"
    | PlusExpr(x, y) -> stringifyA x + "+" + stringifyA y
    | MinusExpr(x, y) -> stringifyA x + "-" + stringifyA y
    | TimesExpr(x, y) -> stringifyA x + "*" + stringifyA y
    | DivExpr(x, y) -> stringifyA x + "/" + stringifyA y
    | PowExpr(x, y) -> stringifyA x + "^" + stringifyA y
    | UMinusExpr(x) -> "-" + stringifyA x

let rec stringifyB = function
    | True -> "true"
    | False -> "false"
    | AndExpr(x, y) -> stringifyB x + "&" + stringifyB y
    | OrExpr(x, y) -> stringifyB x + "|" + stringifyB y
    | AndHardExpr(x, y) -> stringifyB x + "&&" + stringifyB y
    | OrHardExpr(x, y) -> stringifyB x + "||" + stringifyB y
    | NotExpr(x) -> "!" + "(" + stringifyB x + ")"
    | EqualExpr(x, y) -> stringifyA x + "=" + stringifyA y
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
    | AssignExpr x         -> [qS, VAsgn x , qE]
    | AssignArrExpr x      -> [qS, AAsgn x, qE]
    | Skip                 -> [qS, Action.Skip, qE]
    | SeparatorExpr(c1,c2) -> edgesC qS ("q" + string n) c1 (n+1) @ edgesC ("q" + string n) qE c2 (n+1)
    | IfExpr gc            -> edgesGC qS qE gc n
    | DoExpr gc            -> edgesGC qS qS gc n @ [qS, Test (doneGC gc), qE] 
and edgesGC qs qe gc n =
    match gc with
    | FuncExpr(b, c)        -> [qs, Test b, "q" + string n] @ edgesC ("q" + string n) qe c (n+1)
    | ConcExpr(gc1, gc2)    ->  edgesGC qs qe gc1 n @ edgesGC qs qe gc2 (n + calculateUsedNodesGc gc1)
    
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
    | AssignExpr x         -> [qS, VAsgn x, qE]
    | AssignArrExpr x      -> [qS, AAsgn x, qE]
    | Skip                 -> [qS, Action.Skip, qE]
    | SeparatorExpr(c1,c2) -> edgesD qS ("q" + string n) c1 (n+1) @ edgesD ("q" + string n) qE c2 (n+1)
    | IfExpr gc            -> let (E, _) = edgesD2 qS qE gc n False
                              E
    | DoExpr gc            -> let (E, d) = edgesD2 qS qS gc n False
                              E@[(qS, Test (NotExpr d), qE)]
                   
let rec stringify action =
    match action with
    | VAsgn (x,a)    -> x + ":=" + stringifyA a
    | AAsgn (x,i,a)  -> string x + "[" + stringifyA i + "]" + ":=" + stringifyA a
    | Action.Skip    -> "skip"
    | Test b         -> stringifyB b

let rec graphVizifyHelper = function
    | [] -> ""
    | (qs, label, qe)::xs -> qs + " -> " + qe + " [label = \"" + stringify label + "\"];\n" + graphVizifyHelper xs

let graphVizify pg = "digraph program_graph {rankdir=LR;\nnode [shape = circle]; q▷;\nnode [shape = doublecircle]; q◀;\nnode [shape = circle]\n" +
                      graphVizifyHelper pg + "}"


let stripString (stripChars:string) (text:string) =
    text.Split(stripChars.ToCharArray(), StringSplitOptions.RemoveEmptyEntries) |> String.Concat
//let rec makeMemoryFromUserInput memInput = let strippedString = stripString " " memInput
(*let rec getInitialMemory e = printfn "Enter initial memory (FORMAT: x = 1, y = 42, A = [1, 2, 4, 6], ...) "
                             let memInput = Console.ReadLine()
                             try
                                 let memory = makeMemoryFromUserInput memInput
                                 printfn "Initial memory: %A" memory
                                 printfn "%s" (generateTerminalInformation (interpret (edgesD "qStart" "qEnd" e 1) memory))
                             with err -> printfn "%s" (err.Message)
                                         getInitialMemory e
*)

let initializeVar varName varValue mem = updateVar varName varValue (mem)

let rec initializeArr xs arrName index arrMem =
    match (index,xs) with
    | (_, []) -> arrMem
    |(index,value::xs) -> initializeArr xs arrName (index+1) (updateArr arrName index value arrMem)

let rec setupArrAsList = function
     | NumElem x -> [x]
     | Elems (x,y) -> x::setupArrAsList y

let rec initializeMemory mem = function
    | VarInit (varName, varValue) -> ((varName, varValue)::(fst mem), snd mem)
    | ArrInit (arrName, arr) -> ((fst mem), initializeArr (setupArrAsList arr) arrName 0 (snd mem))
    | SeqInit (e1, e2) -> initializeMemory (initializeMemory mem e1) e2


let rec getUserInputDOrNd e =
    printfn "Deterministic or non-deterministic program graph (d/nd)?"
    let pg = Console.ReadLine()
    if (pg = "nd") then
        let programGraph = (edgesC "qStart" "qEnd" e 1)
        printfn "NPG: \n%A\n\nGraphViz formatted text: \n%s" programGraph (graphVizify programGraph)
    elif (pg = "d") then
        let programGraph = (edgesD "qStart" "qEnd" e 1)
        printfn "DPG: \n%A\n\nGraphViz formatted text: \n%s" programGraph (graphVizify programGraph)
    else getUserInputDOrNd e

let parseInitMem input =
    // translate string into a buffer of characters
    let lexbuf = LexBuffer<char>.FromString input
    // translate the buffer into a stream of tokens and parse them
    let res = InputParser.start InputLexer.tokenize lexbuf
    // return the result of parsing (i.e. value of type "expr")
    res
let parse input =
    // translate string into a buffer of characters
    let lexbuf = LexBuffer<char>.FromString input
    // translate the buffer into a stream of tokens and parse them
    let res = CalculatorParser.start CalculatorLexer.tokenize lexbuf
    // return the result of parsing (i.e. value of type "expr")
    res
// We implement here the function that interacts with the user
let rec guardedCommandLanguageRunner n =
    printf "Enter a program in the Guarded Commands Language: "
    let input = Console.ReadLine()
    if (input = "exit") then printfn "Exiting Guarded Command Language"
    else
        try
            let e = parse input
            Console.WriteLine("Parsed tokens (AST): {0} ", e)
            getUserInputDOrNd e
            try
                Console.WriteLine("Write the initial memory: ")
                let initialmem = Console.ReadLine()
                let k = parseInitMem initialmem
                let memory2 =  initializeMemory ([], []) k
(*
                let memory = ([("i",0); ("j", 0); ("n",0); ("t",0)], [('A', [3;9;5;7;8]);('B',[-3;0])])
*)
                printfn "Initial memory: %A" memory2
                printfn "%s" (generateTerminalInformation (interpret (edgesD "qStart" "qEnd" e 1) memory2))
            with err -> printfn "%s" (err.Message)
                        //getInitialMemory e
        with err -> printfn "Invalid Syntax!"
        
        guardedCommandLanguageRunner n

// Start interacting with the user
guardedCommandLanguageRunner 3
