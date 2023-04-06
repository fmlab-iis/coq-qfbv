open BinNums
open BinPos
open CNF
open EqVar

(** val init_vm : word SSAVM.t **)

let init_vm =
  SSAVM.empty

(** val init_gen : positive **)

let init_gen =
  Pos.add var_tt Coq_xH
