open Bool
open Datatypes

type __ = Obj.t

val addb : bool -> bool -> bool

val is_left : bool -> bool

val iffP : bool -> reflect -> reflect

val idP : bool -> reflect

val andP : bool -> bool -> reflect

type 't pred = 't -> bool

type 't predType =
  __ -> 't pred
  (* singleton inductive, whose constructor was PredType *)

type 't pred_sort = __

type 't rel = 't -> 't pred

type 't mem_pred = 't pred
  (* singleton inductive, whose constructor was Mem *)

val pred_of_mem : 'a1 mem_pred -> 'a1 pred_sort

val in_mem : 'a1 -> 'a1 mem_pred -> bool

val mem : 'a1 predType -> 'a1 pred_sort -> 'a1 mem_pred
