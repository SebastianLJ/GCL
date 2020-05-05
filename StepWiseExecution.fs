module StepWiseExecution

open GCLTypesAST

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
    let E = List.filter (fun (qFrom, _, _) -> qFrom = q) pg
    let rec trans edges =
        match edges with
        | [] -> []
        | (_, action, qTo) :: edges -> match sem action mem with
                                       | Some mem' -> (qTo, mem') :: trans edges
                                       | None -> trans edges
    trans E

let rec iterate pg sem (q, mem) c =
    match transition pg sem (q, mem) with
    | [] -> (q, mem)
    | t :: _ when c > 0 -> iterate pg sem t (c - 1)
    | _ -> (q, mem)

let rec transSystem pg sem (q, mem) c startConf acc =
    match transition pg sem (q, mem) with
    | [] -> (startConf, (q,mem))::acc
    | ts when c > 0 -> List.fold (fun acc conf -> transSystem pg sem conf (c-1) (q,mem) acc) ((startConf,(q,mem))::acc) ts
    | _ -> (startConf, (q,mem))::acc
    
let makeTransSystem pg memStart =
    transSystem pg sem ("qStart", memStart) 40 ("qStart", memStart) []

let interpret pg memStart =
    iterate pg sem ("qStart", memStart) 40
    
let rec doneGC gc =
    match gc with
    | FuncExpr(b, _) -> NotExpr b
    | ConcExpr(gc1, gc2) -> AndExpr(doneGC gc1, doneGC gc2)

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
