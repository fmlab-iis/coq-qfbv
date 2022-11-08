open BinNums
open BinPos
open Datatypes
open Decimal

module N =
 struct
  (** val succ_double : coq_N -> coq_N **)

  let succ_double = function
  | N0 -> Npos Coq_xH
  | Npos p -> Npos (Coq_xI p)

  (** val double : coq_N -> coq_N **)

  let double = function
  | N0 -> N0
  | Npos p -> Npos (Coq_xO p)

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

  (** val leb : coq_N -> coq_N -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : coq_N -> coq_N -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val even : coq_N -> bool **)

  let even = function
  | N0 -> true
  | Npos p -> (match p with
               | Coq_xO _ -> true
               | _ -> false)

  (** val odd : coq_N -> bool **)

  let odd n =
    negb (even n)

  (** val pos_div_eucl : positive -> coq_N -> coq_N * coq_N **)

  let rec pos_div_eucl a b =
    match a with
    | Coq_xI a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r')
    | Coq_xO a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r')
    | Coq_xH ->
      (match b with
       | N0 -> (N0, (Npos Coq_xH))
       | Npos p ->
         (match p with
          | Coq_xH -> ((Npos Coq_xH), N0)
          | _ -> (N0, (Npos Coq_xH))))

  (** val div_eucl : coq_N -> coq_N -> coq_N * coq_N **)

  let div_eucl a b =
    match a with
    | N0 -> (N0, N0)
    | Npos na -> (match b with
                  | N0 -> (N0, a)
                  | Npos _ -> pos_div_eucl na b)

  (** val div : coq_N -> coq_N -> coq_N **)

  let div a b =
    fst (div_eucl a b)

  (** val to_nat : coq_N -> int **)

  let to_nat = function
  | N0 -> 0
  | Npos p -> Pos.to_nat p

  (** val to_uint : coq_N -> uint **)

  let to_uint = function
  | N0 -> D0 Nil
  | Npos p -> Pos.to_uint p
 end
