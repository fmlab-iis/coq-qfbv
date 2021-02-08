open BBCommon
open CNF
open Seq

val bit_blast_zeroextend :
  int -> generator -> word -> (generator * cnf) * word
