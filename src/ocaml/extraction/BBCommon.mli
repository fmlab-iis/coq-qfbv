open BinNums
open BinPos
open CNF
open EqVar
open NBitsOp

val cnf_lit_eq : literal -> literal -> literal list list

val extzip_ff : literal list -> literal list -> (literal * literal) list

type generator = positive

val gen : generator -> generator * literal

type vm = word SSAVM.t
