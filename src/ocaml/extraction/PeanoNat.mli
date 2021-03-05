open Datatypes

module Nat :
 sig
  val pred : int -> int

  val compare : int -> int -> comparison

  val log2_iter : int -> int -> int -> int -> int

  val log2 : int -> int

  val log2_up : int -> int
 end
