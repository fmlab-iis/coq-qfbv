open BBCommon
open BBEq
open CNF

val bit_blast_comp :
  generator -> literal list -> literal list -> (generator * cnf) * word
