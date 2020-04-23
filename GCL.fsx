open System
open System.Collections.Generic
open Microsoft.FSharp.Collections

// This script implements GCL

// We need to import a couple of modules, including the generated lexer and parser
#r "C:/Users/emils/.nuget/packages/fslexyacc/10.0.0/build/fsyacc/net46/FsLexYacc.Runtime.dll"
open FSharp.Text.Lexing

#load "GCLTypesAST.fs"

open GCLTypesAST

#load "GCLParser.fs"

open GCLParser

#load "GCLLexer.fs"

open GCLLexer

#load "MemoryTypesAST.fs"

open MemoryTypesAST

#load "MemoryParser.fs"

open MemoryParser

#load "MemoryLexer.fs"

open MemoryLexer



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
        | (0, _ :: arr) -> value :: arr
        | (n, a :: arr) -> a :: updateIndexValue (n - 1) arr
        | _ -> failwith "It should not be possible to get here!" //Isn't it possible to get here if you input a negative index?
    List.map (fun (k, arr) -> if k = c then k, updateIndexValue index arr else k, arr) (memory)

let rec evalASyntax a =
    match a with
    | PlusExpr(x, y) -> evalASyntax x && evalASyntax y
    | MinusExpr(x, y) -> evalASyntax x && evalASyntax y
    | TimesExpr(x, y) -> evalASyntax x && evalASyntax y
    | DivExpr(x, y) -> evalASyntax x && evalASyntax y
    | PowExpr(x, y) -> evalASyntax x && evalASyntax y
    | UMinusExpr x -> evalASyntax x
    | _ -> true

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


type mem = (string * int) list * (char * int list) list
let isVarInDomain var memory = match List.exists (fun (v, _) -> v = var) (fst memory) with
                               | true -> true
                               | false -> failwith ("The variable " + var + " might not have been initialized")

let isArrInDomain c index memory =
    let rec findIndex arr i =
        match arr with
        | [] -> failwith ("Index out of bounds for array \'" + string c + "\' at index: " + string index)
        | _ when i = 0 -> true
        | _ :: arr -> findIndex arr (i - 1)
    match (List.tryFind (fun (id, _) -> id = c) (snd memory)) with
    | Some array -> findIndex (snd array) index
    | _ -> failwith ("The array \'" + string c + "\' might not have been initialized")

let sem action memory =
    match action with
    | Action.Skip -> Some memory
    | VAsgn(var, value) -> match (AEval value memory, isVarInDomain var memory) with
                            | (Some value, true) -> Some(updateVar var value (fst memory), snd memory)
                            | _ -> None
    | AAsgn(c, i, a) -> match (AEval i memory, AEval a memory) with
                            | (Some z1, Some z2) when isArrInDomain c z1 memory -> Some(fst memory, updateArr c z1 z2 (snd memory))
                            | _ -> None

    | Test b -> match BEval b memory with
                            | Some true -> Some memory
                            | _ -> None


let transition pg sem (q, mem) =
    let E = List.filter (fun (qStart, _, _) -> qStart = q) pg
    let rec trans edges =
        match edges with
        | [] -> []
        | (_, action, qTo) :: edges -> match sem action mem with
                                       | Some mem' -> (qTo, mem') :: trans edges
                                       | None -> trans edges
    trans E

let rec iterate pg sem (q, mem) c =
    match transition pg sem (q, mem) with
    | [] -> printfn "%A" (q, mem)
            (q, mem)
    | t :: _ when c > 0 -> printfn "%A" t
                           iterate pg sem t (c - 1)
    | _ -> printfn "%A" (q, mem)
           (q, mem)

let interpret pg memStart =
    iterate pg sem ("qStart", memStart) 40

let stringifyMem mem =
    let rec iteri arr array i acc =
        match array with
        | [] -> acc
        | x :: xs -> iteri arr xs (i + 1) (acc + string arr + "[" + string i + "]: " + string x + "\n")
    List.fold (fun acc (var, value) -> acc + var + ": " + string value + "\n") "" (fst mem)
    + List.fold (fun acc (arr, array) -> acc + iteri arr array 0 "") "" (snd mem)

let generateTerminalInformation (q, mem) =
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

let rec setupArrAsList = function
     | ConNum x -> [ x ]
     | ConNums(x, y) -> x :: setupArrAsList y

let rec initializeCMemory mem = function
    | ConVar(varName, varValue) -> ((varName, varValue) :: (fst mem), snd mem)
    | ConArr(arrName, arr) -> ((fst mem), (arrName, setupArrAsList arr) :: (snd mem))
    | ConSeq(e1, e2) -> initializeCMemory (initializeCMemory mem e1) e2

let initializeConcreteMemory inputMem =
    match inputMem with
    | ConcreteMemory mem -> initializeCMemory ([],[]) mem
    | _                  -> failwith "This is not a concrete memory!"
let signAdd x y =
    match (x, y) with
    | (Pos, Pos) -> Set.empty.Add(Pos)
    | (Pos, Neg) -> Set.empty.Add(Pos).Add(Neg).Add(Zero)
    | (Neg, Pos) -> Set.empty.Add(Pos).Add(Neg).Add(Zero)
    | (Neg, Neg) -> Set.empty.Add(Neg)
    | (Zero, Pos) -> Set.empty.Add(Pos)
    | (Pos, Zero) -> Set.empty.Add(Pos)
    | (Zero, Neg) -> Set.empty.Add(Neg)
    | (Neg, Zero) -> Set.empty.Add(Neg)
    | (Zero, Zero) -> Set.empty.Add(Zero)

let signSub x y =
        match (x, y) with
        | (Pos, Pos) -> Set.empty.Add(Pos).Add(Neg).Add(Zero)
        | (Pos, Neg) -> Set.empty.Add(Pos)
        | (Neg, Pos) -> Set.empty.Add(Neg)
        | (Neg, Neg) -> Set.empty.Add(Neg).Add(Pos).Add(Zero)
        | (Zero, Pos) -> Set.empty.Add(Neg)
        | (Pos, Zero) -> Set.empty.Add(Pos)
        | (Zero, Neg) -> Set.empty.Add(Pos)
        | (Neg, Zero) -> Set.empty.Add(Neg)
        | (Zero, Zero) -> Set.empty.Add(Zero)
let signMul x y =
        match (x, y) with
        | (Pos, Neg) -> Set.empty.Add(Neg)
        | (Neg, Pos) -> Set.empty.Add(Neg)
        | (Zero, _) -> Set.empty.Add(Zero)
        | (_, Zero) -> Set.empty.Add(Zero)
        | (Pos, Pos) -> Set.empty.Add(Pos)
        | (Neg, Neg) -> Set.empty.Add(Pos)

let signDiv x y =
        match (x, y) with
        | (Pos, Neg) -> Set.empty.Add(Neg)
        | (Neg, Pos) -> Set.empty.Add(Neg)
        | (Zero, _) -> Set.empty.Add(Zero)
        | (_, Zero) -> Set.empty
        | (Pos, Pos) -> Set.empty.Add(Pos)
        | (Neg, Neg) -> Set.empty.Add(Pos)
let signPow x y =
        match (x, y) with
        | (Pos, Pos) -> Set.empty.Add(Pos)
        | (Pos, Neg) -> Set.empty.Add(Pos)
        | (Neg, Pos) -> Set.empty.Add(Neg).Add(Pos)
        | (_, Zero) -> Set.empty.Add(Pos)
        | (Zero, Neg) -> Set.empty
        | (Zero, Pos) -> Set.empty.Add(Zero)
        | (Neg, Neg) -> Set.empty.Add(Pos).Add(Neg)
let signUMin x =
      match x with
        | Pos -> Set.empty.Add(Neg)
        | Neg -> Set.empty.Add(Pos)
        | Zero -> Set.empty.Add(Zero)

let sign x = if x = 0 then Zero elif x > 0 then Pos else Neg

let rec AsignOpp aExp mem  =
    match(aExp, mem) with
    | (Num(x),_) -> Set.empty.Add (sign x)
    | (Var(x),(xs,_)) -> Set.empty.Add(try (snd (List.find (fun (id, _) -> id = x) xs)) with err -> failwith ("The variable " + x + " might not have been initialized"))
    | (Array(c,a),(_,ys)) -> let index = AsignOpp a mem
                             if (not (Set.intersect index (set [Zero; Pos])).IsEmpty) then (snd (List.find (fun (id,_) -> id=c) ys)) else Set.empty
    | (PlusExpr(x,y),_) ->
        let mutable k = Set.empty
        for i in (AsignOpp x mem) do
           for j in (AsignOpp y mem) do
           k <- Set.union (signAdd i j) k
           printfn "k: %A" k
        k
    |(MinusExpr(x,y),_) ->
        let mutable k = Set.empty
        for i in (AsignOpp x mem) do
           for j in (AsignOpp y mem) do
           k <- Set.union (signSub i j) k
        k
   
    |(TimesExpr(x,y),_) ->
        let mutable k = Set.empty
        for i in (AsignOpp x mem) do
           for j in (AsignOpp y mem) do
           k <- Set.union (signMul i j) k
        k
     
    |(DivExpr(x,y),_) ->
        let mutable k = Set.empty
        for i in ( AsignOpp x mem) do
           for j in (AsignOpp y mem) do
           k <- Set.union (signDiv i j) k
        k
     
    |(UMinusExpr x,_) ->
        let mutable k = Set.empty
        for i in (AsignOpp x mem) do
           k <- Set.union (signUMin i) k
        k
       
    |(PowExpr(x,y),_) ->
        let mutable k = Set.empty
        for i in (AsignOpp x mem) do
           for j in (AsignOpp y mem) do
           k <- Set.union (signPow i j) k
        k

let BsignAnd x y =
        match (x, y) with
        | (true, true) -> Set.empty.Add(true)
        | (true, false) -> Set.empty.Add(false)
        | (false, true) -> Set.empty.Add(false)
        | (false, false) -> Set.empty.Add(false)
let BsignOr x y =
         match (x, y) with
         | (true, true) -> Set.empty.Add(true)
         | (true, false) -> Set.empty.Add(true)
         | (false, true) -> Set.empty.Add(true)
         | (false, false) -> Set.empty.Add(true)
let BsignAndH x y =
        match (x, y) with
        | (false, _) -> Set.empty.Add(false)
        | (true, false) -> Set.empty.Add(false)
        | _ -> Set.empty.Add(true)
let BsignOrH x y =
        match (x, y) with
        | (true, _) -> Set.empty.Add(true)
        | (false, true) -> Set.empty.Add(true)
        | _ -> Set.empty.Add(false)
let BsignNot x =
        match x with
        | true -> Set.empty.Add(false)
        | false -> Set.empty.Add(true)
let BsignEqual x y =
        match (x, y) with
        | (Pos, Pos) -> Set.empty.Add(true).Add(false)
        | (Pos, Neg) -> Set.empty.Add(false)
        | (Pos, Zero) -> Set.empty.Add(false)
        | (Neg, Pos) -> Set.empty.Add(false)
        | (Zero, Pos) -> Set.empty.Add(false)
        | (Neg, Neg) -> Set.empty.Add(true).Add(false)
        | (Neg, Zero) -> Set.empty.Add(false)
        | (Zero, Neg) -> Set.empty.Add(false)
        | (Zero, Zero) -> Set.empty.Add(true)
let BsignNEqual x y =
        match (x, y) with
        | (Pos, Pos) -> Set.empty.Add(true).Add(false)
        | (Pos, Neg) -> Set.empty.Add(true)
        | (Pos, Zero) -> Set.empty.Add(true)
        | (Neg, Pos) -> Set.empty.Add(true)
        | (Zero, Pos) -> Set.empty.Add(true)
        | (Neg, Neg) -> Set.empty.Add(true).Add(false)
        | (Neg, Zero) -> Set.empty.Add(true)
        | (Zero, Neg) -> Set.empty.Add(true)
        | (Zero, Zero) -> Set.empty.Add(false)
let BsignGt x y =
        match (x, y) with
        | (Pos, Pos) -> Set.empty.Add(true).Add(false)
        | (Pos, Neg) -> Set.empty.Add(true)
        | (Pos, Zero) -> Set.empty.Add(true)
        | (Neg, Pos) -> Set.empty.Add(false)
        | (Zero, Pos) -> Set.empty.Add(false)
        | (Neg, Neg) -> Set.empty.Add(true).Add(false)
        | (Neg, Zero) -> Set.empty.Add(false)
        | (Zero, Neg) -> Set.empty.Add(true)
        | (Zero, Zero) -> Set.empty.Add(false)
let BsignGte x y =
        match (x, y) with
        | (Pos, Pos) -> Set.empty.Add(true).Add(false)
        | (Pos, Neg) -> Set.empty.Add(true)
        | (Pos, Zero) -> Set.empty.Add(true)
        | (Neg, Pos) -> Set.empty.Add(false)
        | (Zero, Pos) -> Set.empty.Add(false)
        | (Neg, Neg) -> Set.empty.Add(true).Add(false)
        | (Neg, Zero) -> Set.empty.Add(false)
        | (Zero, Neg) -> Set.empty.Add(true)
        | (Zero, Zero) -> Set.empty.Add(true)
let BsignLt x y =
        match (x, y) with
        | (Pos, Pos) -> Set.empty.Add(true).Add(false)
        | (Pos, Neg) -> Set.empty.Add(false)
        | (Pos, Zero) -> Set.empty.Add(false)
        | (Neg, Pos) -> Set.empty.Add(true)
        | (Zero, Pos) -> Set.empty.Add(true)
        | (Neg, Neg) -> Set.empty.Add(true).Add(false)
        | (Neg, Zero) -> Set.empty.Add(true)
        | (Zero, Neg) -> Set.empty.Add(false)
        | (Zero, Zero) -> Set.empty.Add(false)
let BsignLte x y =
        match (x, y) with
        | (Pos, Pos) -> Set.empty.Add(true).Add(false)
        | (Pos, Neg) -> Set.empty.Add(false)
        | (Pos, Zero) -> Set.empty.Add(false)
        | (Neg, Pos) -> Set.empty.Add(true)
        | (Zero, Pos) -> Set.empty.Add(true)
        | (Neg, Neg) -> Set.empty.Add(true).Add(false)
        | (Neg, Zero) -> Set.empty.Add(true)
        | (Zero, Neg) -> Set.empty.Add(false)
        | (Zero, Zero) -> Set.empty.Add(true)
let rec BsignOpp bExp mem = 
    match bExp with
    | True -> Set.empty.Add(true)
    | False -> Set.empty.Add(false)
    | AndExpr(x, y) ->
        let mutable k = Set.empty
        for i in BsignOpp x mem do
            for j in BsignOpp y mem do
                k <- Set.union (BsignAnd i j) k
        k

    | OrExpr(x, y) ->
        let mutable k = Set.empty
        for i in BsignOpp x mem do
            for j in BsignOpp y mem do
                k <- Set.union (BsignOr i j) k
        k
    | AndHardExpr(x, y) ->
        let mutable k = Set.empty
        for i in BsignOpp x mem do
            for j in BsignOpp y mem do
                k <- Set.union (BsignAndH i j) k
        k
    | OrHardExpr(x, y) ->
        let mutable k = Set.empty
        for i in BsignOpp x mem do
            for j in BsignOpp y mem do
                k <- Set.union (BsignOrH i j) k
        k
    | NotExpr(x) ->
        let mutable k = Set.empty
        for i in BsignOpp x mem do
                k <- Set.union (BsignNot i) k
        k
    | EqualExpr(x, y) ->
        let mutable k = Set.empty
        for i in AsignOpp x mem do
            for j in AsignOpp y mem do
                k <- Set.union (BsignEqual i j) k
        k
    | NEqualExpr(x, y) ->
        let mutable k = Set.empty
        for i in AsignOpp x mem do
            for j in AsignOpp y mem do
                k <- Set.union (BsignNEqual i j) k
        k
    | GtExpr(x, y) ->
        let mutable k = Set.empty
        for i in AsignOpp x mem do
            for j in AsignOpp y mem do
                k <- Set.union (BsignGt i j) k
        k
    | GteExpr(x, y) ->
        let mutable k = Set.empty
        for i in AsignOpp x mem do
            for j in AsignOpp y mem do
                k <- Set.union (BsignGte i j) k
        k
    | LtExpr(x, y) ->
        let mutable k = Set.empty
        for i in AsignOpp x mem do
            for j in AsignOpp y mem do
                k <- Set.union (BsignLt i j) k
        k
    | LteExpr(x, y) ->
        let mutable k = Set.empty
        for i in AsignOpp x mem do
            for j in AsignOpp y mem do
                k <- Set.union (BsignLte i j) k
        k
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

let rec getUserInputChooseEnvironment choice =
    printfn "Choose environment.\nEnter 1 for Step-wise Execution\nEnter 2 for Detection of Signs Analysis\nEnter 3 for Security Analysis"
    let choice = Console.ReadLine()
    try
    if int choice > 3 then
        getUserInputChooseEnvironment choice
    else
        int choice
    with _ -> getUserInputChooseEnvironment choice


let parseInitMem input =
    // translate string into a buffer of characters
    let lexbuf = LexBuffer<char>.FromString input
    // translate the buffer into a stream of tokens and parse them
    let res = MemoryParser.start MemoryLexer.tokenize lexbuf
    // return the result of parsing (i.e. value of type "expr")
    res

let parse input =
    // translate string into a buffer of characters
    let lexbuf = LexBuffer<char>.FromString input
    // translate the buffer into a stream of tokens and parse them
    let res = GCLParser.start GCLLexer.tokenize lexbuf
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
            
            let environmentMode = getUserInputChooseEnvironment ""
            
            if environmentMode = 1 then
                try
                Console.WriteLine("Enter the initial memory: ")
                let initialMem = Console.ReadLine()
                let k = parseInitMem initialMem
                printf "k: %A" k
                let memory2 = initializeConcreteMemory k
                printfn "Initial memory: %A" memory2
                printfn "%s" (generateTerminalInformation (interpret (edgesD "qStart" "qEnd" e 1) memory2))
                with err -> printfn "%s" (err.Message)
            elif environmentMode = 2 then
                try
                Console.WriteLine("Enter the initial abstract memory: ")
                // TODO Implement
                with err -> printfn "%s" (err.Message)
            elif environmentMode = 3 then
                try
                Console.WriteLine("Specify Security Lattice: ")
                // TODO Implement
                with err -> printfn "%s" (err.Message)
        with err -> printfn "Invalid Syntax!"

        guardedCommandLanguageRunner n

// Start interacting with the user
guardedCommandLanguageRunner 3
