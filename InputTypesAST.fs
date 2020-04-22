module InputTypesAST
open System

type arr =
  | NumElem of int
  | Elems of int * arr

type init =
  | VarInit of string * int
  | ArrInit of char * arr
  | SeqInit of init * init


//Move below into separate file
type signArr =
  | SignElem of char
  | SignArrElems of char * signArr
type signInit =
  | SignVarInit of string * char
  | SignArrInit of char * signArr
  | Sign of char