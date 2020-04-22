module InputTypesAST
open System

type conArrContent =
  | NumElem of int
  | Elems of int * conArrContent

type conElement =
  | ConVar of string * int
  | ConArr of char * conArrContent
  | ConSeq of conElement * conElement

type absArrContent =
  | SignElem of char
  | SignArrElems of char * absArrContent
type absElement =
  | AbsVar of string * char
  | AbsArr of char * absArrContent
  //| Sign of char
  | AbsSeq of absElement * absElement   
type init =
  | Ainit of absElement
  | CInit of conElement

