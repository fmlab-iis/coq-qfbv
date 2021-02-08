open BBAdd
open BBCommon
open BBEq
open BBLneg
open BBNeg
open BBUdiv
open BBXor
open BBZeroExtend
open CNF
open Datatypes
open Eqtype
open Seq

val bit_blast_abs : generator -> word -> (generator * cnf) * word

val bit_blast_sdiv : generator -> word -> word -> (generator * cnf) * word

val bit_blast_srem : generator -> word -> word -> (generator * cnf) * word
