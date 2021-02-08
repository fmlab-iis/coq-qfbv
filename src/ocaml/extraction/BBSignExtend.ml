open BBCommon
open CNF
open Seq

(** val bit_blast_signextend :
    int -> generator -> word -> (generator * cnf) * word **)

let bit_blast_signextend n g ls =
  ((g, []), (cat ls (nseq n (msl ls))))
