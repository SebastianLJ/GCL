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
  | EqualExpr of (a * a)
  | NEqualExpr of (a * a)
  | GtExpr of (a * a)
  | GteExpr of (a * a)
  | LtExpr of (a * a)
  | LteExpr of (a * a)
 type GC =
  | FuncExpr of (b * C)
  | ConcExpr of (GC * GC)
 and C =
  | AssignExpr of (a)
  | AssignArrExpr of (String * a * a)
  | SeparatorExpr of (C * C)
  | IfExpr of (GC)
  | DoExpr of (GC)
  | Skip

