open CNF
open CompTableHash

type expm = word HexpMap.t

type bexpm = literal HbexpMap.t

type simptable = { et : expm; bt : bexpm }

(** val empty : simptable **)

let empty =
  { et = HexpMap.empty; bt = HbexpMap.empty }

(** val find_et : HexpMap.key -> simptable -> word option **)

let find_et e t0 =
  HexpMap.find e t0.et

(** val find_bt : HbexpMap.key -> simptable -> literal option **)

let find_bt e t0 =
  HbexpMap.find e t0.bt

(** val add_et : HexpMap.key -> word -> simptable -> simptable **)

let add_et e ls t0 =
  { et = (HexpMap.add e ls t0.et); bt = t0.bt }

(** val add_bt : HbexpMap.key -> literal -> simptable -> simptable **)

let add_bt e l t0 =
  { et = t0.et; bt = (HbexpMap.add e l t0.bt) }
