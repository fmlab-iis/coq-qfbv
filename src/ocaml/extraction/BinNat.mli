open BinNums
open BinPos
open Datatypes
open Decimal

module N :
 sig
  val succ : coq_N -> coq_N

  val add : coq_N -> coq_N -> coq_N

  val sub : coq_N -> coq_N -> coq_N

  val mul : coq_N -> coq_N -> coq_N

  val compare : coq_N -> coq_N -> comparison

  val eqb : coq_N -> coq_N -> bool

  val ltb : coq_N -> coq_N -> bool

  val to_nat : coq_N -> int

  val to_uint : coq_N -> uint
 end
