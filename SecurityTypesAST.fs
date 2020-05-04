module SecurityTypesAST

type SecurityLattice =
    | Level of string * string
    | MulLevel of SecurityLattice * SecurityLattice

type SecurityClassification =
    |InitVar of string * string
    |InitArr of char * string
    |InitSeq of SecurityClassification * SecurityClassification

type Choice =
  | SecurityLatInit of SecurityLattice
  | SecurityClassInit of SecurityClassification