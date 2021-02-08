open BBAnd
open BBCommon
open BBEq
open BBIte
open BBOr
open BBSub
open BBUge
open CNF
open Eqtype
open Seq

val bit_blast_udiv_rec :
  generator -> literal list -> literal list -> word -> word ->
  ((generator * cnf) * word) * word

val bit_blast_udiv :
  generator -> literal list -> literal list -> ((generator * cnf) * literal
  list) * literal list

val bit_blast_udiv' :
  generator -> literal list -> literal list -> (generator * cnf) * literal
  list

val bit_blast_umod :
  generator -> literal list -> literal list -> (generator * cnf) * literal
  list
