module InputTypesAST
open System

type arr =
  | NumElem of int
  | Elems of int * arr

type init =
  | VarInit of string * int
  | ArrInit of char * arr
  | SeqInit of init * init

type mapInit =
  | VarElem of string
  | ArrElem of string*int
