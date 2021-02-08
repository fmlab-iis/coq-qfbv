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

(** val bit_blast_eunop :
    QFBV.QFBV.eunop -> generator -> literal list -> (generator * cnf) * word **)

let bit_blast_eunop = function
| QFBV.QFBV.Unot -> bit_blast_not
| QFBV.QFBV.Uneg -> bit_blast_neg
| QFBV.QFBV.Uextr (i, j) -> (fun g ls -> bit_blast_extract g i j ls)
| QFBV.QFBV.Uhigh n -> (fun g ls -> bit_blast_high g n ls)
| QFBV.QFBV.Ulow n -> (fun g ls -> bit_blast_low g n ls)
| QFBV.QFBV.Uzext n -> bit_blast_zeroextend n
| QFBV.QFBV.Usext n -> bit_blast_signextend n
| QFBV.QFBV.Urepeat n -> (fun g ls -> bit_blast_repeat g n ls)
| QFBV.QFBV.Urotl n -> (fun g ls -> bit_blast_rotateleft g n ls)
| QFBV.QFBV.Urotr n -> (fun g ls -> bit_blast_rotateright g n ls)

(** val bit_blast_ebinop :
    QFBV.QFBV.ebinop -> generator -> literal list -> literal list ->
    (generator * cnf) * word **)

let bit_blast_ebinop = function
| QFBV.QFBV.Band -> bit_blast_and
| QFBV.QFBV.Bor -> bit_blast_or
| QFBV.QFBV.Bxor -> bit_blast_xor
| QFBV.QFBV.Badd -> bit_blast_add
| QFBV.QFBV.Bsub -> bit_blast_sub
| QFBV.QFBV.Bmul -> Obj.magic bit_blast_mul
| QFBV.QFBV.Bdiv -> bit_blast_udiv'
| QFBV.QFBV.Bmod -> bit_blast_umod
| QFBV.QFBV.Bsdiv -> bit_blast_sdiv
| QFBV.QFBV.Bsrem -> bit_blast_srem
| QFBV.QFBV.Bsmod -> bit_blast_smod
| QFBV.QFBV.Bshl -> bit_blast_shl
| QFBV.QFBV.Blshr -> bit_blast_lshr
| QFBV.QFBV.Bashr -> bit_blast_ashr
| QFBV.QFBV.Bconcat -> bit_blast_concat
| QFBV.QFBV.Bcomp -> bit_blast_comp

(** val bit_blast_bbinop :
    QFBV.QFBV.bbinop -> generator -> literal list -> literal list ->
    (generator * cnf) * literal **)

let bit_blast_bbinop = function
| QFBV.QFBV.Beq -> bit_blast_eq
| QFBV.QFBV.Bult -> bit_blast_ult
| QFBV.QFBV.Bule -> bit_blast_ule
| QFBV.QFBV.Bugt -> bit_blast_ugt
| QFBV.QFBV.Buge -> bit_blast_uge
| QFBV.QFBV.Bslt -> bit_blast_slt
| QFBV.QFBV.Bsle -> bit_blast_sle
| QFBV.QFBV.Bsgt -> bit_blast_sgt
| QFBV.QFBV.Bsge -> bit_blast_sge
| QFBV.QFBV.Buaddo -> bit_blast_uaddo
| QFBV.QFBV.Busubo -> bit_blast_usubo
| QFBV.QFBV.Bumulo -> bit_blast_umulo
| QFBV.QFBV.Bsaddo -> bit_blast_saddo
| QFBV.QFBV.Bssubo -> bit_blast_ssubo
| QFBV.QFBV.Bsmulo -> bit_blast_smulo
