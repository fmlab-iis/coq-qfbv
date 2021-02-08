open CNF
open CompTableHash
open SimpTableHash

type cache = { ht : comptable; ct : simptable }

(** val empty : cache **)

let empty =
  { ht = CompTableHash.empty; ct = empty }

(** val find_het : HexpMap.key -> cache -> (cnf list * word) option **)

let find_het e c =
  CompTableHash.find_et e c.ht

(** val find_hbt : HbexpMap.key -> cache -> (cnf list * literal) option **)

let find_hbt e c =
  CompTableHash.find_bt e c.ht

(** val find_cet : HexpMap.key -> cache -> word option **)

let find_cet e c =
  find_et e c.ct

(** val find_cbt : HbexpMap.key -> cache -> literal option **)

let find_cbt e c =
  find_bt e c.ct

(** val add_het : HexpMap.key -> cnf list -> word -> cache -> cache **)

let add_het e cs ls c =
  { ht = (CompTableHash.add_et e cs ls c.ht); ct = c.ct }

(** val add_hbt : HbexpMap.key -> cnf list -> literal -> cache -> cache **)

let add_hbt e cs l c =
  { ht = (CompTableHash.add_bt e cs l c.ht); ct = c.ct }

(** val add_cet : HexpMap.key -> word -> cache -> cache **)

let add_cet e ls c =
  { ht = c.ht; ct = (add_et e ls c.ct) }

(** val add_cbt : HbexpMap.key -> literal -> cache -> cache **)

let add_cbt e l c =
  { ht = c.ht; ct = (add_bt e l c.ct) }

(** val reset_ct : cache -> cache **)

let reset_ct c =
  { ht = c.ht; ct = SimpTableHash.empty }
