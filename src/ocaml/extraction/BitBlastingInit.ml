open BinNums
open BinPos
open CNF
open Var

(** val init_vm : word SSAVM.t **)

let init_vm =
  SSAVM.empty

(** val init_gen : positive **)

let init_gen =
  Pos.add var_tt Coq_xH
