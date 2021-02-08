open BBAdd
open BBAnd
open BBCommon
open BBConst
open BBShl
open BinNat
open BinNums
open CNF
open NBitsDef
open Eqtype
open Seq

val bit_blast_mul_rec :
  generator -> literal list -> Equality.sort list -> coq_N ->
  (generator * cnf) * word

val bit_blast_mul :
  generator -> literal list -> Equality.sort list -> (generator * cnf) * word
