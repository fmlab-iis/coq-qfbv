open BinNums
open BinPos
open Datatypes

module Z :
 sig
  val double : coq_Z -> coq_Z

  val succ_double : coq_Z -> coq_Z

  val pred_double : coq_Z -> coq_Z

  val pos_sub : positive -> positive -> coq_Z

  val add : coq_Z -> coq_Z -> coq_Z

  val opp : coq_Z -> coq_Z

  val succ : coq_Z -> coq_Z

  val pred : coq_Z -> coq_Z

  val sub : coq_Z -> coq_Z -> coq_Z

  val mul : coq_Z -> coq_Z -> coq_Z

  val compare : coq_Z -> coq_Z -> comparison

  val leb : coq_Z -> coq_Z -> bool

  val ltb : coq_Z -> coq_Z -> bool

  val eqb : coq_Z -> coq_Z -> bool

  val max : coq_Z -> coq_Z -> coq_Z

  val to_nat : coq_Z -> int

  val of_nat : int -> coq_Z

  val even : coq_Z -> bool

  val odd : coq_Z -> bool

  val div2 : coq_Z -> coq_Z

  val log2 : coq_Z -> coq_Z

  val eq_dec : coq_Z -> coq_Z -> bool

  val log2_up : coq_Z -> coq_Z

  val b2z : bool -> coq_Z
 end
