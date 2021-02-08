open Seq

(** val tflatten_rec : 'a1 list -> 'a1 list list -> 'a1 list **)

let rec tflatten_rec res = function
| [] -> res
| hd :: tl -> tflatten_rec (catrev hd res) tl

(** val tflatten : 'a1 list list -> 'a1 list **)

let tflatten ss =
  tflatten_rec [] ss

(** val mapr_rec : ('a1 -> 'a2) -> 'a2 list -> 'a1 list -> 'a2 list **)

let rec mapr_rec f res = function
| [] -> res
| hd :: tl -> mapr_rec f ((f hd) :: res) tl

(** val mapr : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let mapr f es =
  mapr_rec f [] es
