open CNF
open CompTableHash

type expm = word HexpMap.t

type bexpm = literal HbexpMap.t

type simptable = { et : expm; bt : bexpm }

val empty : simptable

val find_et : HexpMap.key -> simptable -> word option

val find_bt : HbexpMap.key -> simptable -> literal option

val add_et : HexpMap.key -> word -> simptable -> simptable

val add_bt : HbexpMap.key -> literal -> simptable -> simptable
