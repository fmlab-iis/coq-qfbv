open Ssrbool

(** val coq_PredType : ('a2 -> 'a1 pred) -> 'a1 predType **)

let coq_PredType x =
  Obj.magic x
