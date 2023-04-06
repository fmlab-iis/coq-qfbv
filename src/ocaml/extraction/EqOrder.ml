open BinNat
open BinPos
open Datatypes
open ZAriths
open Eqtype

let __ = let rec f _ = Obj.repr f in Obj.repr f

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

module MakeEqOrder =
 functor (M:EqOrderMinimal) ->
 struct
  (** val coq_T : Equality.coq_type **)

  let coq_T =
    M.t

  type t = Equality.sort

  (** val ltn : t -> t -> bool **)

  let ltn =
    M.ltn

  (** val compare : t -> t -> t OrderedType.coq_Compare **)

  let compare =
    M.compare

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    let _evar_0_ = fun _ -> true in
    let _evar_0_0 = fun _ -> false in
    if eq_op coq_T x y then _evar_0_ __ else _evar_0_0 __
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

module MakeProdOrderMinimal =
 functor (O1:EqOrder) ->
 functor (O2:EqOrder) ->
 struct
  (** val t : Equality.coq_type **)

  let t =
    prod_eqType O1.coq_T O2.coq_T

  (** val eqn : Equality.sort -> Equality.sort -> bool **)

  let eqn x y =
    eq_op t x y

  (** val ltn : Equality.sort -> Equality.sort -> bool **)

  let ltn x y =
    (||) (O1.ltn (fst (Obj.magic x)) (fst (Obj.magic y)))
      ((&&) (eq_op O1.coq_T (fst (Obj.magic x)) (fst (Obj.magic y)))
        (O2.ltn (snd (Obj.magic x)) (snd (Obj.magic y))))

  (** val compare :
      Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare **)

  let compare x y =
    let _evar_0_ = fun x1 x2 ->
      let _evar_0_ = fun y1 y2 ->
        let _evar_0_ = fun _ -> OrderedType.LT in
        let _evar_0_0 = fun _ ->
          let _evar_0_0 = fun _ -> OrderedType.LT in
          let _evar_0_1 = fun _ -> OrderedType.EQ in
          let _evar_0_2 = fun _ -> OrderedType.GT in
          (match O2.compare x2 y2 with
           | OrderedType.LT -> _evar_0_0 __
           | OrderedType.EQ -> _evar_0_1 __
           | OrderedType.GT -> _evar_0_2 __)
        in
        let _evar_0_1 = fun _ -> OrderedType.GT in
        (match O1.compare x1 y1 with
         | OrderedType.LT -> _evar_0_ __
         | OrderedType.EQ -> _evar_0_0 __
         | OrderedType.GT -> _evar_0_1 __)
      in
      let (a, b) = Obj.magic y in _evar_0_ a b
    in
    let (a, b) = Obj.magic x in _evar_0_ a b
 end

module MakeProdOrderWithDefaultSucc =
 functor (O1:EqOrderWithDefaultSucc) ->
 functor (O2:EqOrderWithDefaultSucc) ->
 struct
  module M = MakeProdOrderMinimal(O1)(O2)

  module P = MakeEqOrder(M)

  (** val coq_T : Equality.coq_type **)

  let coq_T =
    M.t

  type t = Equality.sort

  (** val ltn : t -> t -> bool **)

  let ltn =
    M.ltn

  (** val compare : t -> t -> t OrderedType.coq_Compare **)

  let compare =
    M.compare

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    P.eq_dec

  (** val default : t **)

  let default =
    Obj.magic (O1.default, O2.default)

  (** val succ : t -> t **)

  let succ x =
    Obj.magic ((O1.succ (fst (Obj.magic x))), O2.default)
 end

module PositiveOrderMinimal =
 struct
  (** val t : Equality.coq_type **)

  let t =
    pos_eqType

  (** val eqn : Equality.sort -> Equality.sort -> bool **)

  let eqn x y =
    eq_op t x y

  (** val ltn : Equality.sort -> Equality.sort -> bool **)

  let ltn x y =
    Pos.ltb (Obj.magic x) (Obj.magic y)

  (** val compare :
      Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare **)

  let compare x y =
    let _evar_0_ = fun _ -> OrderedType.EQ in
    let _evar_0_0 = fun _ -> OrderedType.LT in
    let _evar_0_1 = fun _ -> OrderedType.GT in
    (match Pos.compare (Obj.magic x) (Obj.magic y) with
     | Eq -> _evar_0_ __
     | Lt -> _evar_0_0 __
     | Gt -> _evar_0_1 __)
 end

module PositiveOrder = MakeEqOrder(PositiveOrderMinimal)

module NOrderMinimal =
 struct
  (** val t : Equality.coq_type **)

  let t =
    coq_N_eqType

  (** val eqn : Equality.sort -> Equality.sort -> bool **)

  let eqn x y =
    eq_op t x y

  (** val ltn : Equality.sort -> Equality.sort -> bool **)

  let ltn x y =
    N.ltb (Obj.magic x) (Obj.magic y)

  (** val compare :
      Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare **)

  let compare x y =
    let _evar_0_ = fun _ -> OrderedType.EQ in
    let _evar_0_0 = fun _ -> OrderedType.LT in
    let _evar_0_1 = fun _ -> OrderedType.GT in
    (match N.compare (Obj.magic x) (Obj.magic y) with
     | Eq -> _evar_0_ __
     | Lt -> _evar_0_0 __
     | Gt -> _evar_0_1 __)
 end

module NOrder = MakeEqOrder(NOrderMinimal)
