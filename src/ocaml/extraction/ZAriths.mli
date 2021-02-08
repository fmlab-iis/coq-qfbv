open BinInt
open BinNat
open BinNums
open BinPos
open Bool
open Datatypes
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

module PositiveOrderMinimal :
 sig
  val t : Equality.coq_type

  val eqn : Equality.sort -> Equality.sort -> bool

  val ltn : Equality.sort -> Equality.sort -> bool

  val compare :
    Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare
 end

module PositiveOrder :
 sig
  val coq_T : Equality.coq_type

  type t = Equality.sort

  val ltn : t -> t -> bool

  val compare : t -> t -> t OrderedType.coq_Compare

  val eq_dec : t -> t -> bool
 end

module NOrderMinimal :
 sig
  val t : Equality.coq_type

  val eqn : Equality.sort -> Equality.sort -> bool

  val ltn : Equality.sort -> Equality.sort -> bool

  val compare :
    Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare
 end

module NOrder :
 sig
  val coq_T : Equality.coq_type

  type t = Equality.sort

  val ltn : t -> t -> bool

  val compare : t -> t -> t OrderedType.coq_Compare

  val eq_dec : t -> t -> bool
 end
