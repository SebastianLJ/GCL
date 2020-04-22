module MemoryTypesAST
open System

type ConArrContent =
  | ConNum of int
  | ConNums of int * ConArrContent

type ConElement =
  | ConVar of string * int
  | ConArr of char * ConArrContent
  | ConSeq of ConElement * ConElement

type AbsArrContent =
  | Sign of char
  | Signs of char * AbsArrContent
  
type AbsElement =
  | AbsVar of string * char
  | AbsArr of char * AbsArrContent
  | AbsSeq of AbsElement * AbsElement
  
type Memory =
  | AbstractMemory of AbsElement
  | ConcreteMemory of ConElement

