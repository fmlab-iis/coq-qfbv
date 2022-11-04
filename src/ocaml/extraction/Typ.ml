open Eqtype
open Ssrnat

type typ =
| Tuint of int
| Tsint of int

(** val sizeof_typ : typ -> int **)

let sizeof_typ = function
| Tuint w -> w
| Tsint w -> w

(** val typ_eqn : typ -> typ -> bool **)

let typ_eqn x y =
  match x with
  | Tuint wx ->
    (match y with
     | Tuint wy -> eq_op nat_eqType (Obj.magic wx) (Obj.magic wy)
     | Tsint _ -> false)
  | Tsint wx ->
    (match y with
     | Tuint _ -> false
     | Tsint wy -> eq_op nat_eqType (Obj.magic wx) (Obj.magic wy))
