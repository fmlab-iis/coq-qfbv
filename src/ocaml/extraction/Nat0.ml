
(** val pred : int -> int **)

let pred = fun n -> Pervasives.max 0 (n-1)

(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Pervasives.max 0 (n-m)


