open BinNums
open BinPosDef
open Datatypes
open Decimal
open Nat0

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | Coq_xI p -> Coq_xO (succ p)
  | Coq_xO p -> Coq_xI p
  | Coq_xH -> Coq_xO Coq_xH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> Coq_xO (add_carry p q)
       | Coq_xO q -> Coq_xI (add p q)
       | Coq_xH -> Coq_xO (succ p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> Coq_xI (add p q)
       | Coq_xO q -> Coq_xO (add p q)
       | Coq_xH -> Coq_xI p)
    | Coq_xH ->
      (match y with
       | Coq_xI q -> Coq_xO (succ q)
       | Coq_xO q -> Coq_xI q
       | Coq_xH -> Coq_xO Coq_xH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> Coq_xI (add_carry p q)
       | Coq_xO q -> Coq_xO (add_carry p q)
       | Coq_xH -> Coq_xI (succ p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> Coq_xO (add_carry p q)
       | Coq_xO q -> Coq_xI (add p q)
       | Coq_xH -> Coq_xO (succ p))
    | Coq_xH ->
      (match y with
       | Coq_xI q -> Coq_xI (succ q)
       | Coq_xO q -> Coq_xO (succ q)
       | Coq_xH -> Coq_xI Coq_xH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | Coq_xI p -> Coq_xI (Coq_xO p)
  | Coq_xO p -> Coq_xI (pred_double p)
  | Coq_xH -> Coq_xH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos Coq_xH
  | IsPos p -> IsPos (Coq_xI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (Coq_xO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | Coq_xI p -> IsPos (Coq_xO (Coq_xO p))
  | Coq_xO p -> IsPos (Coq_xO (pred_double p))
  | Coq_xH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> double_mask (sub_mask p q)
       | Coq_xO q -> succ_double_mask (sub_mask p q)
       | Coq_xH -> IsPos (Coq_xO p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> succ_double_mask (sub_mask_carry p q)
       | Coq_xO q -> double_mask (sub_mask p q)
       | Coq_xH -> IsPos (pred_double p))
    | Coq_xH -> (match y with
                 | Coq_xH -> IsNul
                 | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> succ_double_mask (sub_mask_carry p q)
       | Coq_xO q -> double_mask (sub_mask p q)
       | Coq_xH -> IsPos (pred_double p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> double_mask (sub_mask_carry p q)
       | Coq_xO q -> succ_double_mask (sub_mask_carry p q)
       | Coq_xH -> double_pred_mask p)
    | Coq_xH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | Coq_xI p -> add y (Coq_xO (mul p y))
    | Coq_xO p -> Coq_xO (mul p y)
    | Coq_xH -> y

  (** val div2 : positive -> positive **)

  let div2 = function
  | Coq_xI p0 -> p0
  | Coq_xO p0 -> p0
  | Coq_xH -> Coq_xH

  (** val div2_up : positive -> positive **)

  let div2_up = function
  | Coq_xI p0 -> succ p0
  | Coq_xO p0 -> p0
  | Coq_xH -> Coq_xH

  (** val size : positive -> positive **)

  let rec size = function
  | Coq_xI p0 -> succ (size p0)
  | Coq_xO p0 -> succ (size p0)
  | Coq_xH -> Coq_xH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> compare_cont r p q
       | Coq_xO q -> compare_cont Gt p q
       | Coq_xH -> Gt)
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> compare_cont Lt p q
       | Coq_xO q -> compare_cont r p q
       | Coq_xH -> Gt)
    | Coq_xH -> (match y with
                 | Coq_xH -> r
                 | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val max : positive -> positive -> positive **)

  let max p p' =
    match compare p p' with
    | Gt -> p
    | _ -> p'

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | Coq_xI p0 -> (match q with
                    | Coq_xI q0 -> eqb p0 q0
                    | _ -> false)
    | Coq_xO p0 -> (match q with
                    | Coq_xO q0 -> eqb p0 q0
                    | _ -> false)
    | Coq_xH -> (match q with
                 | Coq_xH -> true
                 | _ -> false)

  (** val ltb : positive -> positive -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | Coq_xI p0 -> op a (iter_op op p0 (op a a))
    | Coq_xO p0 -> iter_op op p0 (op a a)
    | Coq_xH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op Nat0.add x (Pervasives.succ 0)

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Coq_xH)
      (fun x -> succ (of_succ_nat x))
      n

  (** val to_little_uint : positive -> uint **)

  let rec to_little_uint = function
  | Coq_xI p0 -> Little.succ_double (to_little_uint p0)
  | Coq_xO p0 -> Little.double (to_little_uint p0)
  | Coq_xH -> D1 Nil

  (** val to_uint : positive -> uint **)

  let to_uint p =
    rev (to_little_uint p)

  (** val eq_dec : positive -> positive -> bool **)

  let rec eq_dec p x0 =
    match p with
    | Coq_xI p0 -> (match x0 with
                    | Coq_xI p1 -> eq_dec p0 p1
                    | _ -> false)
    | Coq_xO p0 -> (match x0 with
                    | Coq_xO p1 -> eq_dec p0 p1
                    | _ -> false)
    | Coq_xH -> (match x0 with
                 | Coq_xH -> true
                 | _ -> false)
 end
