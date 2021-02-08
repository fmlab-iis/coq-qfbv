open Bool
open CNF
open FMaps
open Int0
open QFBVHash
open Eqtype

type __ = Obj.t

module HexpMap = MakeTreeMap(HexpOrder)

module HbexpMap = MakeTreeMap(HbexpOrder)

type expm = (cnf list * word) HexpMap.t

type bexpm = (cnf list * literal) HbexpMap.t

type comptable = { et : expm; bt : bexpm }

(** val empty : comptable **)

let empty =
  { et = HexpMap.empty; bt = HbexpMap.empty }

(** val find_et : HexpMap.key -> comptable -> (cnf list * word) option **)

let find_et e t0 =
  HexpMap.find e t0.et

(** val find_bt : HbexpMap.key -> comptable -> (cnf list * literal) option **)

let find_bt e t0 =
  HbexpMap.find e t0.bt

(** val add_et : HexpMap.key -> cnf list -> word -> comptable -> comptable **)

let add_et e cs ls t0 =
  { et = (HexpMap.add e (cs, ls) t0.et); bt = t0.bt }

(** val add_bt :
    HbexpMap.key -> cnf list -> literal -> comptable -> comptable **)

let add_bt e cs l t0 =
  { et = t0.et; bt = (HbexpMap.add e (cs, l) t0.bt) }
