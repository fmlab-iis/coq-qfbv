open BinInt
open BinNat
open BinNums
open BinPos
open Bool
open Eqtype

val pos_eqP : positive -> positive -> reflect

val pos_eqMixin : positive Equality.mixin_of

val pos_eqType : Equality.coq_type

val coq_N_eqP : coq_N -> coq_N -> reflect

val coq_N_eqMixin : coq_N Equality.mixin_of

val coq_N_eqType : Equality.coq_type

val coq_Z_eqP : coq_Z -> coq_Z -> reflect

val coq_Z_eqMixin : coq_Z Equality.mixin_of

val coq_Z_eqType : Equality.coq_type
