open BinNat
open BinNums
open Datatypes
open Nat0
open Eqtype
open Ssrbool

val eqn : int -> int -> bool

val eqnP : int Equality.axiom

val nat_eqMixin : int Equality.mixin_of

val nat_eqType : Equality.coq_type

val addn_rec : int -> int -> int

val addn : int -> int -> int

val subn_rec : int -> int -> int

val subn : int -> int -> int

val leq : int -> int -> bool

val maxn : int -> int -> int

val minn : int -> int -> int

val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1

val muln_rec : int -> int -> int

val muln : int -> int -> int

val nat_of_bool : bool -> int

val odd : int -> bool

val double_rec : int -> int

val double : int -> int

val half : int -> int

val uphalf : int -> int

val eq_binP : coq_N Equality.axiom

val bin_nat_eqMixin : coq_N Equality.mixin_of

val bin_nat_eqType : Equality.coq_type
