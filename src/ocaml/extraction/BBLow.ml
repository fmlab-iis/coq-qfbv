open BBCommon
open CNF
open Seq
open Ssrnat

(** val bit_blast_low :
    generator -> int -> literal list -> (generator * cnf) * word **)

let bit_blast_low g n ls =
  ((g, []), (cat (take n ls) (nseq (subn n (size ls)) lit_ff)))
