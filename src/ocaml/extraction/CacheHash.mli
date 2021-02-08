open CNF
open CompTableHash
open SimpTableHash

type cache = { ht : comptable; ct : simptable }

val empty : cache

val find_het : HexpMap.key -> cache -> (cnf list * word) option

val find_hbt : HbexpMap.key -> cache -> (cnf list * literal) option

val find_cet : HexpMap.key -> cache -> word option

val find_cbt : HbexpMap.key -> cache -> literal option

val add_het : HexpMap.key -> cnf list -> word -> cache -> cache

val add_hbt : HbexpMap.key -> cnf list -> literal -> cache -> cache

val add_cet : HexpMap.key -> word -> cache -> cache

val add_cbt : HbexpMap.key -> literal -> cache -> cache

val reset_ct : cache -> cache
