open BBAdd
open BBAnd
open BBAshr
open BBCommon
open BBComp
open BBConcat
open BBEq
open BBExtract
open BBHigh
open BBLow
open BBLshr
open BBMul
open BBNeg
open BBNot
open BBOr
open BBRepeat
open BBRotateLeft
open BBRotateRight
open BBSaddo
open BBSdiv
open BBSge
open BBSgt
open BBShl
open BBSignExtend
open BBSle
open BBSlt
open BBSmod
open BBSmulo
open BBSsubo
open BBSub
open BBUaddo
open BBUdiv
open BBUge
open BBUgt
open BBUle
open BBUlt
open BBUmulo
open BBUsubo
open BBXor
open BBZeroExtend
open CNF

val bit_blast_eunop :
  QFBV.QFBV.eunop -> generator -> literal list -> (generator * cnf) * word

val bit_blast_ebinop :
  QFBV.QFBV.ebinop -> generator -> literal list -> literal list ->
  (generator * cnf) * word

val bit_blast_bbinop :
  QFBV.QFBV.bbinop -> generator -> literal list -> literal list ->
  (generator * cnf) * literal
