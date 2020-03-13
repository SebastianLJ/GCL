// This file implements a module where we define a data type "expr"
// to store represent arithmetic expressions
module CalculatorTypesAST
open System


 type a = 
  | Num of double
  | Var of string
  | A of char
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
 type GC =
  | FuncExpr of (b * C)
  | ConcExpr of (GC * GC)
 and C =
  | AssignExpr of (String * a)
  | AssignArrExpr of (char * a * a)
  | SeparatorExpr of (C * C)
  | IfExpr of (GC)
  | DoExpr of (GC)
  | Skip
