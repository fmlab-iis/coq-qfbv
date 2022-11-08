open BinNat
open BinNums
open Bool
open Datatypes
open FMaps
open FSets
open Int0
open String0
open Strings
open ZAriths
open Eqtype

type __ = Obj.t

module VarOrder =
 struct
  (** val coq_T : Equality.coq_type **)

  let coq_T =
    NOrderMinimal.t

  type t = Equality.sort

  (** val ltn : t -> t -> bool **)

  let ltn =
    NOrderMinimal.ltn

  (** val compare : t -> t -> t OrderedType.coq_Compare **)

  let compare =
    NOrderMinimal.compare

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    NOrder.eq_dec

  (** val succ : t -> t **)

  let succ =
    Obj.magic N.succ

  (** val default : t **)

  let default =
    Obj.magic N0
 end

module SSAVarOrder = SsrOrder.MakeProdOrderWithDefaultSucc(VarOrder)(VarOrder)

module SSAVarOrderPrinter =
 struct
  type t = SSAVarOrder.t

  (** val to_string : SSAVarOrder.t -> char list **)

  let to_string v =
    append ('v'::[])
      (append (string_of_N (fst (Obj.magic v)))
        (append ('_'::[]) (string_of_N (snd (Obj.magic v)))))
 end

type ssavar = SSAVarOrder.t

module SSAVS = MakeTreeSetWithNew(SSAVarOrder)

module SSAVM = MakeTreeMapWithNew(SSAVarOrder)
