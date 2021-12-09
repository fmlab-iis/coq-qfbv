open BinNums
open BinPos
open Datatypes
open Decimal

module N =
 struct
  (** val succ : coq_N -> coq_N **)

  let succ = function
  | N0 -> Npos Coq_xH
  | Npos p -> Npos (Pos.succ p)

  (** val add : coq_N -> coq_N -> coq_N **)

  let add n m =
    match n with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n
                 | Npos q -> Npos (Pos.add p q))

  (** val sub : coq_N -> coq_N -> coq_N **)

  let sub n m =
    match n with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n
       | Npos m' ->
         (match Pos.sub_mask n' m' with
          | Pos.IsPos p -> Npos p
          | _ -> N0))

  (** val mul : coq_N -> coq_N -> coq_N **)

  let mul n m =
    match n with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Npos (Pos.mul p q))

  (** val compare : coq_N -> coq_N -> comparison **)

  let compare n m =
    match n with
    | N0 -> (match m with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' -> (match m with
                  | N0 -> Gt
                  | Npos m' -> Pos.compare n' m')

  (** val eqb : coq_N -> coq_N -> bool **)

  let eqb n m =
    match n with
    | N0 -> (match m with
             | N0 -> true
             | Npos _ -> false)
    | Npos p -> (match m with
                 | N0 -> false
                 | Npos q -> Pos.eqb p q)

  (** val ltb : coq_N -> coq_N -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val to_nat : coq_N -> int **)

  let to_nat = function
  | N0 -> 0
  | Npos p -> Pos.to_nat p

  (** val to_uint : coq_N -> uint **)

  let to_uint = function
  | N0 -> D0 Nil
  | Npos p -> Pos.to_uint p
 end
