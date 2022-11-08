open Datatypes
open Decimal

module Nat =
 struct
  (** val pred : int -> int **)

  let pred n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n)
      (fun u -> u)
      n

  (** val compare : int -> int -> comparison **)

  let rec compare = fun n m -> if n=m then Eq else if n<m then Lt else Gt

  (** val to_little_uint : int -> uint -> uint **)

  let rec to_little_uint n acc =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> acc)
      (fun n0 -> to_little_uint n0 (Little.succ acc))
      n

  (** val to_uint : int -> uint **)

  let to_uint n =
    rev (to_little_uint n (D0 Nil))

  (** val log2_iter : int -> int -> int -> int -> int **)

  let rec log2_iter k p q r =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> p)
      (fun k' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        log2_iter k' (Pervasives.succ p) (Pervasives.succ q) q)
        (fun r' -> log2_iter k' p (Pervasives.succ q) r')
        r)
      k

  (** val log2 : int -> int **)

  let log2 n =
    log2_iter (pred n) 0 (Pervasives.succ 0) 0

  (** val log2_up : int -> int **)

  let log2_up a =
    match compare (Pervasives.succ 0) a with
    | Lt -> Pervasives.succ (log2 (pred a))
    | _ -> 0
 end
