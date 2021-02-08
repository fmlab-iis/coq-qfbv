open BBCommon
open CNF
open Seq
open Ssrnat

val bit_blast_extract :
  generator -> int -> int -> literal list -> (generator * cnf) * word
