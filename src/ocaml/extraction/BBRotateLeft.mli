open BBCommon
open CNF
open Ssrnat

val rotatel1 : word -> word

val rotatel : int -> word -> word

val bit_blast_rotateleft :
  generator -> int -> word -> (generator * cnf) * word
