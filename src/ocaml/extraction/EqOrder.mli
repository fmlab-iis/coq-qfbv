open BinNat
open BinPos
open Datatypes
open ZAriths
open Eqtype

module type EqOrderMinimal =
 sig
  val t : Equality.coq_type

  val eqn : Equality.sort -> Equality.sort -> bool

  val ltn : Equality.sort -> Equality.sort -> bool

  val compare :
    Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare
 end

module type EqOrder =
 sig
  val coq_T : Equality.coq_type

  type t = Equality.sort

  val ltn : t -> t -> bool

  val compare : t -> t -> t OrderedType.coq_Compare

  val eq_dec : t -> t -> bool
 end

module MakeEqOrder :
 functor (M:EqOrderMinimal) ->
 sig
  val coq_T : Equality.coq_type

  type t = Equality.sort

  val ltn : t -> t -> bool

  val compare : t -> t -> t OrderedType.coq_Compare

  val eq_dec : t -> t -> bool
 end

module type EqOrderWithDefaultSucc =
 sig
  val coq_T : Equality.coq_type

  type t = Equality.sort

  val ltn : t -> t -> bool

  val compare : t -> t -> t OrderedType.coq_Compare

  val eq_dec : t -> t -> bool

  val default : Equality.sort

  val succ : t -> t
 end

module MakeProdOrderMinimal :
 functor (O1:EqOrder) ->
 functor (O2:EqOrder) ->
 sig
  val t : Equality.coq_type

  val eqn : Equality.sort -> Equality.sort -> bool

  val ltn : Equality.sort -> Equality.sort -> bool

  val compare :
    Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare
 end

module MakeProdOrderWithDefaultSucc :
 functor (O1:EqOrderWithDefaultSucc) ->
 functor (O2:EqOrderWithDefaultSucc) ->
 sig
  module M :
   sig
    val t : Equality.coq_type

    val eqn : Equality.sort -> Equality.sort -> bool

    val ltn : Equality.sort -> Equality.sort -> bool

    val compare :
      Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare
   end

  module P :
   sig
    val coq_T : Equality.coq_type

    type t = Equality.sort

    val ltn : t -> t -> bool

    val compare : t -> t -> t OrderedType.coq_Compare

    val eq_dec : t -> t -> bool
   end

  val coq_T : Equality.coq_type

  type t = Equality.sort

  val ltn : t -> t -> bool

  val compare : t -> t -> t OrderedType.coq_Compare

  val eq_dec : t -> t -> bool

  val default : t

  val succ : t -> t
 end

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
