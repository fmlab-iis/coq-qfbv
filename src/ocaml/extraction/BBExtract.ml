open BBCommon
open CNF
open Seq
open Ssrnat

(** val bit_blast_extract :
    generator -> int -> int -> literal list -> (generator * cnf) * word **)

let bit_blast_extract g i j ls =
  let lowls =
    cat (take (addn i (Pervasives.succ 0)) ls)
      (nseq (subn (addn i (Pervasives.succ 0)) (size ls)) lit_ff)
  in
  ((g, []),
  (cat
    (nseq (subn (addn (subn i j) (Pervasives.succ 0)) (size lowls)) lit_ff)
    (drop (subn (size lowls) (addn (subn i j) (Pervasives.succ 0))) lowls)))
