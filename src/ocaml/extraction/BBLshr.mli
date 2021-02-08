open BBCommon
open BBConst
open BBEq
open BBExtract
open BBIte
open BinInt
open BinNat
open BinNums
open CNF
open NBitsDef
open Nat0
open Eqtype
open Seq
open Ssrnat

val bit_blast_lshr_int1 :
  generator -> literal list -> (generator * cnf) * word

val bit_blast_lshr_int :
  generator -> word -> coq_N -> (generator * cnf) * word

val bit_blast_lshr_rec :
  generator -> word -> Equality.sort list -> coq_N -> (generator * cnf) * word

val bit_blast_lshr :
  generator -> literal list -> literal list -> (generator * cnf) * word
