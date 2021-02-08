open BBCommon
open CNF
open Ssrnat

val rotater1 : literal list -> word

val rotater : int -> literal list -> word

val bit_blast_rotateright :
  generator -> int -> literal list -> (generator * cnf) * word
