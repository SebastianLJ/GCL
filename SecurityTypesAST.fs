module SecurityTypesAST

type SecurityLattice =
    | MulLevel of string * SecurityLattice
    | Level of string

type SecurityClassification =
    |InitVar of string * string
    |InitArr of char * string
    |InitSeq of SecurityClassification * SecurityClassification

type Choice =
  | SecurityLatInit of SecurityLattice
  | SecurityClassInit of SecurityClassification