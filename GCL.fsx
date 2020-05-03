open System
open System.Collections.Generic
open Microsoft.FSharp.Collections

// This script implements GCL

// We need to import a couple of modules, including the generated lexer and parser
#r "C:/Users/Noah/.nuget/packages/fslexyacc/10.0.0/build/fsyacc/net46/FsLexYacc.Runtime.dll"
open FSharp.Text.Lexing

#load "GCL/GCLTypesAST.fs"

open GCLTypesAST

#load "GCL/GCLParser.fs"

open GCLParser

#load "GCL/GCLLexer.fs"

open GCLLexer

#load "MemoryTypesAST.fs"

open MemoryTypesAST

#load "MemoryParser.fs"

open MemoryParser

#load "MemoryLexer.fs"

open MemoryLexer

#load "StepWiseExecution.fs"

open StepWiseExecution

#load "SecurityTypesAST.fs"

open SecurityTypesAST

#load "SecurityParser.fs"

open SecurityParser

#load "SecurityLexer.fs"

open SecurityLexer

// ------------------------- Stringify functions ------------------------- //
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

let stringToSign x = if x="+" then Pos elif x="-" then Neg else Zero

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
                      graphVizifyHelper pg + "}\n"


let rec stringifyFlow flow =
    match flow with
    | [] -> ""
    | (x,y)::[] -> x + " -> " + y
    | (x,y)::xys -> x + " -> " + y + ", " + stringifyFlow xys
        
// ------------------------- Sign Analysis ------------------------- //

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

let rec opHat set1 set2 acc opBarBin opBarUn =
    match Set.toList set2 with
    | [] -> match Set.toList set1 with
            | [] -> acc
            | x :: xs -> opHat (Set.ofList xs) set2 (Set.union (opBarUn x) acc) opBarBin opBarUn
    | _ -> match Set.toList set1 with
           | [] -> acc
           | x::xs -> opHat (Set.ofList xs) set2 (Set.fold (fun acc y -> Set.union (opBarBin x y) acc) acc set2) opBarBin opBarUn

let sign x = if x = 0 then Zero elif x > 0 then Pos else Neg

let rec ASignOpp aExp absMem  =
    match aExp with
    | Num x -> Set.empty.Add (sign x)
    | Var x -> Set.empty.Add(try (snd (List.find (fun (id, _) -> id = x) (fst absMem) )) with err -> failwith ("The variable " + x + " might not have been initialized"))
    | Array(c,a) -> let index = ASignOpp a absMem
                    if not ((Set.intersect index (set [Zero; Pos])).IsEmpty) then (snd (List.find (fun (id,_) -> id=c) (snd absMem) )) else Set.empty
    | PlusExpr(x,y) -> opHat (ASignOpp x absMem) (ASignOpp y absMem) Set.empty signAdd (fun _ -> Set.empty)
    | MinusExpr(x,y) -> opHat (ASignOpp x absMem) (ASignOpp y absMem) Set.empty signSub (fun _ -> Set.empty)
    | TimesExpr(x,y) -> opHat (ASignOpp x absMem) (ASignOpp y absMem) Set.empty signMul (fun _ -> Set.empty)
    | DivExpr(x,y) -> opHat (ASignOpp x absMem) (ASignOpp y absMem) Set.empty signDiv (fun _ -> Set.empty)
    | UMinusExpr x -> opHat (ASignOpp x absMem) Set.empty Set.empty (fun _ _ -> Set.empty) signUMin 
    | PowExpr(x,y) -> opHat (ASignOpp x absMem) (ASignOpp y absMem) Set.empty signPow (fun _ -> Set.empty)

let BSignAnd x y =
    match (x, y) with
    | (true, true) -> Set.empty.Add(true)
    | (true, false) -> Set.empty.Add(false)
    | (false, true) -> Set.empty.Add(false)
    | (false, false) -> Set.empty.Add(false)
let BSignOr x y =
    match (x, y) with
    | (true, true) -> Set.empty.Add(true)
    | (true, false) -> Set.empty.Add(true)
    | (false, true) -> Set.empty.Add(true)
    | (false, false) -> Set.empty.Add(false)
let BSignAndH x y =
    match (x, y) with
    | (false, _) -> Set.empty.Add(false)
    | (true, false) -> Set.empty.Add(false)
    | _ -> Set.empty.Add(true)
let BSignOrH x y =
    match (x, y) with
    | (true, _) -> Set.empty.Add(true)
    | (false, true) -> Set.empty.Add(true)
    | _ -> Set.empty.Add(false)
let BSignNot x =
    match x with
    | true -> Set.empty.Add(false)
    | false -> Set.empty.Add(true)
let BSignEqual x y =
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
let BSignNEqual x y =
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
let BSignGt x y =
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
let BSignGte x y =
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
let BSignLt x y =
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
let BSignLte x y =
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
    
let rec BSignOpp bExp mem = 
    match bExp with
    | True -> Set.empty.Add(true)
    | False -> Set.empty.Add(false)
    | AndExpr(x, y) -> opHat (BSignOpp x mem) (BSignOpp y mem) Set.empty BSignAnd (fun _ -> Set.empty)
    | OrExpr(x, y) -> opHat (BSignOpp x mem) (BSignOpp y mem) Set.empty BSignOr (fun _ -> Set.empty)
    | AndHardExpr(x, y) -> opHat (BSignOpp x mem) (BSignOpp y mem) Set.empty BSignAndH (fun _ -> Set.empty)
    | OrHardExpr(x, y) -> opHat (BSignOpp x mem) (BSignOpp y mem) Set.empty BSignOrH (fun _ -> Set.empty)
    | NotExpr(x) -> opHat (BSignOpp x mem) Set.empty Set.empty (fun _ _ -> Set.empty) BSignNot
    | EqualExpr(x, y) -> opHat (ASignOpp x mem) (ASignOpp y mem) Set.empty BSignEqual (fun _ -> Set.empty)
    | NEqualExpr(x, y) -> opHat (ASignOpp x mem) (ASignOpp y mem) Set.empty BSignNEqual (fun _ -> Set.empty)
    | GtExpr(x, y) -> opHat (ASignOpp x mem) (ASignOpp y mem) Set.empty BSignGt (fun _ -> Set.empty)
    | GteExpr(x, y) -> opHat (ASignOpp x mem) (ASignOpp y mem) Set.empty BSignGte (fun _ -> Set.empty)
    | LtExpr(x, y) -> opHat (ASignOpp x mem) (ASignOpp y mem) Set.empty BSignLte (fun _ -> Set.empty)
    | LteExpr(x, y) -> opHat (ASignOpp x mem) (ASignOpp y mem) Set.empty BSignLte (fun _ -> Set.empty)
    
let rec updateAbsVar var sign absMem =
    (List.map (fun (absVar,value) -> if absVar = var then (absVar, sign) else (absVar,value)) (fst absMem), snd absMem)

let rec updateAbsArr arr signs absMem =
    (fst absMem, List.map (fun (absArr,absSigns) -> if absArr = arr then (absArr, signs) else (absArr,absSigns)) (snd absMem))

let findArraySigns arr absMem =
    let rec searchAbsArray arr absArr = match absArr with
                                        | [] -> Set.empty
                                        | (c, signs)::_ when c = arr -> signs
                                        | _::cs -> searchAbsArray arr cs
    searchAbsArray arr (snd absMem)
    
let semHat action M =
    match action with
    | Action.Skip -> M
    | Test b -> Set.filter (fun absMem -> Set.contains true (BSignOpp b absMem)) M
    | VAsgn(var, value) -> Set.fold (fun acc absMem -> let s = ASignOpp value absMem
                                                       match s.IsEmpty with
                                                       | true -> acc
                                                       | false -> Set.fold (fun acc sign -> acc.Add(updateAbsVar var sign absMem)) acc s) Set.empty M
    | AAsgn(c, i, a) -> Set.fold (fun acc absMem -> let index = ASignOpp i absMem
                                                    match (Set.intersect index (set [Zero; Pos])).IsEmpty with
                                                    | true -> acc
                                                    | false -> let s = findArraySigns c absMem
                                                               Set.fold (fun acc s' -> Set.fold (fun acc s'' ->
                                                                   Set.union acc (set[updateAbsArr c ((s.Remove s').Add s'') absMem; updateAbsArr c (s.Add s'') absMem])) acc (ASignOpp a absMem)) acc s) Set.empty M

let rec initializeAnaAsgn anaMap = function
    |q::Q -> Map.add q Set.empty (initializeAnaAsgn anaMap Q)
    |[] -> anaMap
let rec getNodes = function
    |(x,_,y)::edges -> Set.union (set [x;y]) (getNodes edges )
    |[] -> Set.empty
let third (_,_,c) = c

let WorklistAlg initAbstractMems edges =
    let nodes = List.filter(fun x -> x <> "qStart") (Set.toList (getNodes edges)) //all nodes except start node
    let mutable map = initializeAnaAsgn Map.empty nodes //initialize map
    map <- Map.add "qStart" initAbstractMems map //start node analysis assignment just consists of given input
    let mutable workList = Set.empty.Add "qStart" //initialize worklist
    while not (Set.isEmpty workList) do
        let q = List.head (Set.toList workList)
        workList <-  Set.remove q workList
        for (qo,A,qc) in edges do
            if qo = q then
                let e1 = semHat (A) (Map.find qo map) 
                let e2 = Map.find (qc) map 
                let e3 = Set.union e1 e2   
                if not (Set.isSubset e1 e2)then
                 map <- Map.add (qc) (e3) map
                 workList <- Set.union workList (set[qc])

                
    map

let signToStringVar x = if x=Pos then "+" elif x=Neg then "-" else "0"
open System.Text.RegularExpressions

let signSetToString x =
    let mutable Set ="{"
    for i in x do
        Set <- Set + signToStringVar i + ","
    Set <- Set + "}"
    let pattern = ",}"
    let k = Regex(pattern)
    Set <- k.Replace(Set, "}")
    Set
let findVarSign varList var = snd (List.find (fun (varName, sign) ->  varName=var) varList)
let findArrSign arrList arr = snd (List.find (fun (arrName, setSign) ->  arrName=arr) arrList)

let rec genVarList lstTup varList =
    match lstTup with
    |(varName, _)::lstTup -> genVarList lstTup (varName::varList)
    |_-> varList
let rec genArrList lstTup arrList =
    match lstTup with
    |(arrName, _ )::lstTup -> genArrList lstTup (arrName::arrList)
    |_ -> arrList
let endMemToLstOfVars mp =
    let setEndMem = Map.find "qEnd" mp
    let lst = Set.toList setEndMem
    genVarList (fst(List.head lst)) []
let endMemToLstOfArrs mp =
    let setEndMem = Map.find "qEnd" mp
    let lst = Set.toList setEndMem
    genArrList (snd(List.head lst)) []
let rec prettyPrintLine varNameLst arrNameLst varList arrList =
    match (varNameLst, arrNameLst) with 
    |(varName::varNameLst, _) -> signToStringVar (findVarSign varList varName) + " " + prettyPrintLine varNameLst arrNameLst varList arrList
    |([], arrName::arrNameLst) -> signSetToString (findArrSign arrList arrName) + " " + prettyPrintLine varNameLst arrNameLst varList arrList
    |_ -> ""
let rec prettyPrint lst varNameLst arrNameLst =
    match lst with
    |x::lst -> "\t \t" + prettyPrintLine varNameLst arrNameLst (fst x) (snd x) + "\n" + prettyPrint lst varNameLst arrNameLst
    | _ -> "\n"
let rec toprow varNameLst arrNameLst =
    match (varNameLst, arrNameLst) with
    |(x::varNameLst, _ ) -> x + " " + toprow varNameLst arrNameLst
    |([], y::arrNameLst) -> (string) y + " " + toprow varNameLst arrNameLst
    |_ -> ""
let initialize mp =
    let setEndMem = Map.find "qEnd" mp
    let lst = Set.toList setEndMem
    let varNameLst = List.sort (endMemToLstOfVars mp)
    let arrNameLst = List.sort (endMemToLstOfArrs mp)
    toprow varNameLst arrNameLst + "\n" +
    prettyPrint lst varNameLst arrNameLst

// ------------------------- Security Analysis ------------------------- //
let rec fvA aExp =
    match aExp with
    | Num _ -> Set.empty
    | Var x -> set[x]
    | Array (c, i) -> Set.union (set[string c]) (fvA i)
    | PlusExpr (x,y) -> Set.union (fvA x) (fvA y)
    | MinusExpr (x,y) -> Set.union (fvA x) (fvA y)
    | TimesExpr (x,y) -> Set.union (fvA x) (fvA y)
    | DivExpr (x,y) -> Set.union (fvA x) (fvA y)
    | UMinusExpr x -> fvA x
    | PowExpr (x,y) -> Set.union (fvA x) (fvA y)
    
let rec fvB bExp =
    match bExp with
    | True -> Set.empty
    | False -> Set.empty
    | AndExpr (x, y) -> Set.union (fvB x) (fvB y)
    | OrExpr (x, y) -> Set.union (fvB x) (fvB y)
    | AndHardExpr (x, y) -> Set.union (fvB x) (fvB y)
    | OrHardExpr (x, y) -> Set.union (fvB x) (fvB y)
    | NotExpr x -> fvB x
    | EqualExpr (x, y) -> Set.union (fvA x) (fvA y)
    | NEqualExpr (x, y) -> Set.union (fvA x) (fvA y)
    | GtExpr (x, y) -> Set.union (fvA x) (fvA y)
    | GteExpr (x, y) -> Set.union (fvA x) (fvA y)
    | LtExpr (x, y) -> Set.union (fvA x) (fvA y)
    | LteExpr (x, y) -> Set.union (fvA x) (fvA y)
    
let rec makeFlow xs ys =
    Set.fold (fun (acc:Set<'a*'a>) x -> Set.fold (fun acc y -> acc.Add(x,y)) acc ys) Set.empty xs

let rec sec c x =
    match c with
    | AssignExpr (var, value) -> makeFlow (Set.union x (fvA value)) (set[var]) 
    | AssignArrExpr (c, i, value) -> makeFlow (Set.union (Set.union x (fvA i)) (fvA value)) (set[string c]) 
    | SeparatorExpr (c1, c2) -> Set.union (sec c1 x) (sec c2 x)
    | IfExpr gc -> let w,_ = sec2 gc (False, x)
                   w
    | DoExpr gc -> let w,_ = sec2 gc (False, x)
                   w
    | Skip -> Set.empty
and sec2 gc (d,x) =
    match gc with
    | FuncExpr (b, c) -> let w = sec c (Set.union (Set.union x (fvB b)) (fvB d))
                         (w, OrExpr (b, d))
    | ConcExpr (gc1, gc2) -> let (w1,d1) = sec2 gc1 (d,x)
                             let (w2,d2) = sec2 gc2 (d1,x)
                             (Set.union w1 w2, d2)

let secure code allowedFlow =
    let actualFlow = sec code Set.empty
    let violation = Set.difference actualFlow (Set.ofList allowedFlow)
    
    printfn "Actual flow: %s" (stringifyFlow (Set.toList actualFlow))
    printfn "Allowed flow: %s" (stringifyFlow allowedFlow)
    printfn "Violations: %s" (stringifyFlow (Set.toList violation))
    printfn "%s\n" (if violation.IsEmpty then "Secure" else "Not Secure")

let rec getSecFlows secLevel secLattice =
    match secLattice with
    | (x, y)::xs when x = secLevel -> y::(getSecFlows y xs)
    | (x, y)::xs -> getSecFlows secLevel xs
    | _ -> []

let rec makeFlows ident permittedFlows secClass =
    match secClass with
    | (var, level)::xs when List.contains level permittedFlows -> (ident,var)::makeFlows ident permittedFlows xs
    | (var, level)::xs -> makeFlows ident permittedFlows xs
    | _ -> []

let rec getAllowedFlows secClassFull secClassLoop secLattice =
    match secClassLoop with
    | (var, secLevel)::xs -> (makeFlows var (secLevel::getSecFlows secLevel secLattice) secClassFull)@getAllowedFlows secClassFull xs secLattice
    | _ -> []
    

// ------------------------- Parser Methods ------------------------- //

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
let parseSecurity input =
    // translate string into a buffer of characters
    let lexbuf = LexBuffer<char>.FromString input
    // translate the buffer into a stream of tokens and parse them
    let res = SecurityParser.start SecurityLexer.tokenize lexbuf
    // return the result of parsing (i.e. value of type "expr")
    res
let rec setupAbsArrAsSet = function
     | Sign x -> Set.empty.Add(stringToSign x)
     | Signs(x, y) -> Set.union (Set.empty.Add(stringToSign x)) (setupAbsArrAsSet y)
let rec initializeAmemory mem = function
     |AbsVar(varName,varSign) -> ((varName, stringToSign varSign) :: (fst mem), snd mem)
     |AbsArr(arrName, arr) -> (fst mem, (arrName, setupAbsArrAsSet arr) :: snd mem)
     |AbsSeq(e1,e2) -> initializeAmemory (initializeAmemory mem e1) e2

let initializeAbstractMemory (inputMem)  = 
    match inputMem with
    |AbstractMemory mem -> initializeAmemory ([],[]) mem
    | _ -> failwith "This is not an abstract memory"

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

// ------------------------- User Interface ------------------------- //
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
        printf "\n"
        getUserInputChooseEnvironment choice
    else
        printf "\n"
        int choice
    with _ -> getUserInputChooseEnvironment choice  
       
// We implement here the function that interacts with the user
let rec guardedCommandLanguageRunner n =
    printfn "Enter a program in the Guarded Commands Language (variable name zero is reserved for sign analysis): "
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
                    printf "k: %A \n" k
                    let memory2 = initializeConcreteMemory k
                    printfn "Initial memory: %A \n" memory2
                    printfn "%s" (generateTerminalInformation (interpret (edgesD "qStart" "qEnd" e 1) memory2))
                with err -> printfn "%s" (err.Message)
            elif environmentMode = 2 then
                try
                    Console.WriteLine("Enter the initial abstract memory (write zero for the sign 0): ")
                    let initialMem = Console.ReadLine()
                    let parsedMemory = parseInitMem initialMem
                    let memory = initializeAbstractMemory parsedMemory
                    printfn "Initial abstract memory: %A \n" memory
                    let mutable collectionOfMems = Set.empty.Add(memory)
                    let mutable reply="Y"
                    while(reply="Y") do
                        Console.WriteLine("Do you want to add another initial abstract memory? (Y/N)")
                        reply <- Console.ReadLine()
                        if reply = "Y" then 
                         Console.WriteLine("Enter the initial abstract memory (write zero for the sign 0): ")
                         let initialMem = Console.ReadLine()
                         let k = parseInitMem initialMem
                         let memory = initializeAbstractMemory k
                         collectionOfMems <- Set.union collectionOfMems (Set.empty.Add memory)                       
                    let configurations = WorklistAlg collectionOfMems (edgesD "qStart" "qEnd" e 1)
                    let str = initialize configurations
                    printfn "\t     endConfig:\n \n \t \t%s" str
                with err -> printfn "%s" (err.Message)
            elif environmentMode = 3 then
                try
                Console.WriteLine("Specify Security Lattice and give security classification for variables and arrays (press enter after each choice) : ")
                let first = Console.ReadLine()
                let parsedFirst = parseSecurity first
                printfn "test1: %A" parsedFirst              
                let second = Console.ReadLine()
                let parsedSecond = parseSecurity second
                printfn "test1: %A" parsedSecond              
                // TODO Implement
                let secLattice = [("public", "public"); ("public", "private"); ("private", "private")]
                let secClass = [("x", "public"); ("y", "public"); ("z", "public")]              
                secure e (getAllowedFlows secClass secClass secLattice)
                
                with err -> printfn "%s" (err.Message)
        with err -> printfn "Invalid Syntax!"

        guardedCommandLanguageRunner n

// Start interacting with the user
guardedCommandLanguageRunner 3
