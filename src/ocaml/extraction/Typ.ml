
type typ =
| Tuint of int
| Tsint of int

(** val sizeof_typ : typ -> int **)

let sizeof_typ = function
| Tuint w -> w
| Tsint w -> w
