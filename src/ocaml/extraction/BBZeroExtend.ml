open BBCommon
open CNF
open Seq

(** val bit_blast_zeroextend :
    int -> generator -> word -> (generator * cnf) * word **)

let bit_blast_zeroextend n g ls =
  ((g, []), (cat ls (nseq n lit_ff)))
