open BBCommon
open CNF
open Seq
open Ssrnat

(** val bit_blast_high :
    generator -> int -> literal list -> (generator * cnf) * word **)

let bit_blast_high g n ls =
  ((g, []),
    (cat (nseq (subn n (size ls)) lit_ff) (drop (subn (size ls) n) ls)))
