open BBCommon
open CNF
open EqVar

val bit_blast_var' : generator -> int -> generator * word

val bit_blast_var :
  TypEnv.SSATE.env -> generator -> ssavar -> (generator * cnf) * word
