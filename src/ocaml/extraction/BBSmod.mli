open BBAdd
open BBAnd
open BBCommon
open BBEq
open BBNot
open BBOr
open BBSdiv
open CNF
open Datatypes
open Eqtype
open Seq

val bit_blast_smod : generator -> word -> word -> (generator * cnf) * word
