open BBCommon
open CNF
open Ssrnat

(** val rotatel1 : word -> word **)

let rotatel1 ls =
  dropmsl (joinlsl (msl ls) ls)

(** val rotatel : int -> word -> word **)

let rotatel n ls =
  iter n rotatel1 ls

(** val bit_blast_rotateleft :
    generator -> int -> word -> (generator * cnf) * word **)

let bit_blast_rotateleft g n ls =
  ((g, []), (rotatel n ls))
