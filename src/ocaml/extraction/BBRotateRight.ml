open BBCommon
open CNF
open Ssrnat

(** val rotater1 : literal list -> word **)

let rotater1 ls =
  droplsl (joinmsl ls (coq_lsl ls))

(** val rotater : int -> literal list -> word **)

let rotater n ls =
  iter n rotater1 ls

(** val bit_blast_rotateright :
    generator -> int -> literal list -> (generator * cnf) * word **)

let bit_blast_rotateright g n ls =
  ((g, []), (rotater n ls))
