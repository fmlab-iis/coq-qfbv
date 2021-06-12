open Bool
open Datatypes

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val addb : bool -> bool -> bool **)

let addb = function
| true -> negb
| false -> (fun x -> x)

(** val is_left : bool -> bool **)

let is_left = function
| true -> true
| false -> false

(** val iffP : bool -> reflect -> reflect **)

let iffP _ pb =
  let _evar_0_ = fun _ _ _ -> ReflectT in
  let _evar_0_0 = fun _ _ _ -> ReflectF in
  (match pb with
   | ReflectT -> _evar_0_ __ __ __
   | ReflectF -> _evar_0_0 __ __ __)

(** val idP : bool -> reflect **)

let idP = function
| true -> ReflectT
| false -> ReflectF

(** val andP : bool -> bool -> reflect **)

let andP b1 b2 =
  if b1 then if b2 then ReflectT else ReflectF else ReflectF

type 't pred = 't -> bool

type 't predType =
  __ -> 't pred
  (* singleton inductive, whose constructor was PredType *)

type 't pred_sort = __

type 't rel = 't -> 't pred

type 't mem_pred = 't pred
  (* singleton inductive, whose constructor was Mem *)

(** val pred_of_mem : 'a1 mem_pred -> 'a1 pred_sort **)

let pred_of_mem mp =
  Obj.magic mp

(** val in_mem : 'a1 -> 'a1 mem_pred -> bool **)

let in_mem x mp =
  Obj.magic pred_of_mem mp x

(** val mem : 'a1 predType -> 'a1 pred_sort -> 'a1 mem_pred **)

let mem pT =
  pT
