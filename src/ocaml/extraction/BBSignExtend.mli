open BBCommon
open CNF
open Seq

val bit_blast_signextend :
  int -> generator -> word -> (generator * cnf) * word
