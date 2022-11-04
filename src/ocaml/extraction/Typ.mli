open Eqtype
open Ssrnat

type typ =
| Tuint of int
| Tsint of int

val sizeof_typ : typ -> int

val typ_eqn : typ -> typ -> bool
