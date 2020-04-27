// This file implements a module where we define a data type "expr"
// to store represent arithmetic expressions
module GCLTypesAST
open System


 type a = 
  | Num of int
  | Var of string
  | Array of (char*a)
  | PlusExpr of (a * a)
  | MinusExpr of (a * a)
  | TimesExpr of (a * a)
  | DivExpr of (a * a)
  | UMinusExpr of (a)
  | PowExpr of (a * a)

 type b =
  | True
  | False
  | AndExpr of (b * b)
  | OrExpr of (b * b)
  | AndHardExpr of (b * b)
  | OrHardExpr of (b * b)
  | NotExpr of (b)
  | EqualExpr of (a * a)
  | NEqualExpr of (a * a)
  | GtExpr of (a * a)
  | GteExpr of (a * a)
  | LtExpr of (a * a)
  | LteExpr of (a * a)
  
type Action = VAsgn of string * a
              | AAsgn of char * a * a
              | Skip
              | Test of b
 type GC =
  | FuncExpr of (b * C)
  | ConcExpr of (GC * GC)
 and C =
  | AssignExpr of (string * a)
  | AssignArrExpr of (char * a * a)
  | SeparatorExpr of (C * C)
  | IfExpr of (GC)
  | DoExpr of (GC)
  | Skip

type Signk  = Neg | Zero | Pos
(* type Signa =
  | Sign
  | Num of int
  | Var of string
  | Array of (char*Signa)
  | PlusExpr of (Signa * Signa)
  | MinusExpr of (Signa * Signa)
  | TimesExpr of (Signa * Signa)
  | DivExpr of (Signa * Signa)
  | UMinusExpr of (Signa)
  | PowExpr of (Signa * Signa)

 type Signb =
  | True
  | False
  | AndExpr of (Signb * Signb)
  | OrExpr of (Signb * Signb)
  | AndHardExpr of (Signb * Signb)
  | OrHardExpr of (Signb * Signb)
  | NotExpr of (Signb)
  | EqualExpr of (Signa * Signa)
  | NEqualExpr of (Signa * Signa)
  | GtExpr of (Signa * Signa)
  | GteExpr of (Signa * Signa)
  | LtExpr of (Signa * Signa)
  | LteExpr of (Signa * Signa)*)
