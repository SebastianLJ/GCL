// This file implements a module where we define a data type "expr"
// to store represent arithmetic expressions
module CalculatorTypesAST
open System


 type a = 
  | N of int
  | X of String
  | A of a
  | PlusExpr of (a * a)
  | MinusExpr of (a * a)
  | TimesExpr of (a * a)
  | DivExpr of (a * a)
  | UMinusExpr of (a)
  | PowExpr of (a * a)

 type b =
  | Tf of bool
  | AndExpr of (b * b)
  | OrExpr of (b * b)
  | AndHardExpr of (b * b)
  | OrHardExpr of (b * b)
  | NotExpr of (b)
  | EqualExpr of (b * b)
  | NEqualExpr of (b * b)
  | GtExpr of (b * b)
  | GteExpr of (b * b)
  | LtExpr of (b * b)
  | LteExpr of (b * b)
 type GC =
  | FuncExpr of (b * C)
  | ConcExpr of (GC * GC)
 and C =
  | AssignExpr of (String * a)
  | AssignArrExpr of (String * a * a)
  | SeperatorExpr of (C * C)
  | IfExpr of (GC)
  | DoExpr of (GC)
  | Skip

