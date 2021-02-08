open Seq

val tflatten_rec : 'a1 list -> 'a1 list list -> 'a1 list

val tflatten : 'a1 list list -> 'a1 list

val mapr_rec : ('a1 -> 'a2) -> 'a2 list -> 'a1 list -> 'a2 list

val mapr : ('a1 -> 'a2) -> 'a1 list -> 'a2 list
