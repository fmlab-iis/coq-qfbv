open Datatypes
open Decimal

module Nat :
 sig
  val pred : int -> int

  val compare : int -> int -> comparison

  val to_little_uint : int -> uint -> uint

  val to_uint : int -> uint

  val log2_iter : int -> int -> int -> int -> int

  val log2 : int -> int

  val log2_up : int -> int
 end
