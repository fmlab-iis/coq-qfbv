open BBCommon
open CNF
open Seq
open Ssrnat

val bit_blast_high :
  generator -> int -> literal list -> (generator * cnf) * word
