open BBCommon
open CNF
open NBitsDef

val bit_blast_repeat :
  generator -> int -> literal list -> (generator * cnf) * word
