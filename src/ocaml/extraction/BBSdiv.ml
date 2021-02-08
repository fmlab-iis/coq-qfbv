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

(** val bit_blast_abs : generator -> word -> (generator * cnf) * word **)

let bit_blast_abs g ls =
  let ls_tl = fst (splitmsl ls) in
  let ls_sign = snd (splitmsl ls) in
  if eq_op lit_eqType (Obj.magic ls_sign) (Obj.magic lit_tt)
  then bit_blast_neg g ls
  else if eq_op lit_eqType (Obj.magic ls_sign) (Obj.magic lit_ff)
       then ((g, []), ls)
       else let ws = nseq (size ls) ls_sign in
            let (p, rs_xor) = bit_blast_xor g ls ws in
            let (g_xor, cs_xor) = p in
            let (p0, rs_zext) =
              bit_blast_zeroextend (size ls_tl) g_xor (ls_sign :: [])
            in
            let (g_zext, cs_zext) = p0 in
            let (p1, rs_add) = bit_blast_add g_zext rs_xor rs_zext in
            let (g_add, cs_add) = p1 in
            ((g_add, (catrev (catrev cs_xor cs_zext) cs_add)), rs_add)

(** val bit_blast_sdiv :
    generator -> word -> word -> (generator * cnf) * word **)

let bit_blast_sdiv g ls1 ls2 =
  let ls1_tl = fst (splitmsl ls1) in
  let ls1_sign = snd (splitmsl ls1) in
  let ls2_sign = snd (splitmsl ls2) in
  let (p, lrs_abs1) = bit_blast_abs g ls1 in
  let (g_abs1, cs_abs1) = p in
  let (p0, lrs_abs2) = bit_blast_abs g_abs1 ls2 in
  let (g_abs2, cs_abs2) = p0 in
  let (p1, qs_udiv) = bit_blast_udiv' g_abs2 lrs_abs1 lrs_abs2 in
  let (g_udiv, cs_udiv) = p1 in
  if (||)
       ((&&) (eq_op lit_eqType (Obj.magic ls1_sign) (Obj.magic lit_ff))
         (eq_op lit_eqType (Obj.magic ls2_sign) (Obj.magic lit_ff)))
       ((&&) (eq_op lit_eqType (Obj.magic ls1_sign) (Obj.magic lit_tt))
         (eq_op lit_eqType (Obj.magic ls2_sign) (Obj.magic lit_tt)))
  then ((g_udiv, (catrev (catrev cs_abs1 cs_abs2) cs_udiv)), qs_udiv)
  else if (||)
            ((&&) (eq_op lit_eqType (Obj.magic ls1_sign) (Obj.magic lit_ff))
              (eq_op lit_eqType (Obj.magic ls2_sign) (Obj.magic lit_tt)))
            ((&&) (eq_op lit_eqType (Obj.magic ls1_sign) (Obj.magic lit_tt))
              (eq_op lit_eqType (Obj.magic ls2_sign) (Obj.magic lit_ff)))
       then let (p2, lrs_negq) = bit_blast_neg g_udiv qs_udiv in
            let (g_negq, cs_negq) = p2 in
            ((g_negq,
            (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negq)),
            lrs_negq)
       else let (p2, r_eq) =
              bit_blast_eq g_udiv (ls1_sign :: []) (ls2_sign :: [])
            in
            let (g_eq, cs_eq) = p2 in
            let (p3, r_lneg) = bit_blast_lneg g_eq r_eq in
            let (g_lneg, cs_lneg) = p3 in
            let wneq = nseq (size ls1) r_lneg in
            let (p4, rs_xor) = bit_blast_xor g_lneg qs_udiv wneq in
            let (g_xor, cs_xor) = p4 in
            let (p5, rs_zext) =
              bit_blast_zeroextend (size ls1_tl) g_xor (r_lneg :: [])
            in
            let (g_zext, cs_zext) = p5 in
            let (p6, rs_add) = bit_blast_add g_zext rs_xor rs_zext in
            let (g_add, cs_add) = p6 in
            ((g_add,
            (catrev
              (catrev
                (catrev
                  (catrev
                    (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_eq)
                    cs_lneg) cs_xor) cs_zext) cs_add)), rs_add)

(** val bit_blast_srem :
    generator -> word -> word -> (generator * cnf) * word **)

let bit_blast_srem g ls1 ls2 =
  let ls1_tl = fst (splitmsl ls1) in
  let ls1_sign = snd (splitmsl ls1) in
  let ws1 = nseq (size ls1) ls1_sign in
  let (p, lrs_abs1) = bit_blast_abs g ls1 in
  let (g_abs1, cs_abs1) = p in
  let (p0, lrs_abs2) = bit_blast_abs g_abs1 ls2 in
  let (g_abs2, cs_abs2) = p0 in
  let (p1, rs_udiv) = bit_blast_udiv g_abs2 lrs_abs1 lrs_abs2 in
  let (p2, _) = p1 in
  let (g_udiv, cs_udiv) = p2 in
  if eq_op lit_eqType (Obj.magic ls1_sign) (Obj.magic lit_ff)
  then ((g_udiv, (catrev (catrev cs_abs1 cs_abs2) cs_udiv)), rs_udiv)
  else if eq_op lit_eqType (Obj.magic ls1_sign) (Obj.magic lit_tt)
       then let (p3, lrs_negr) = bit_blast_neg g_udiv rs_udiv in
            let (g_negr, cs_negr) = p3 in
            ((g_negr,
            (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negr)),
            lrs_negr)
       else let (p3, rs_xor1) = bit_blast_xor g_udiv rs_udiv ws1 in
            let (g_xor1, cs_xor1) = p3 in
            let (p4, rs_zext1) =
              bit_blast_zeroextend (size ls1_tl) g_xor1 (ls1_sign :: [])
            in
            let (g_zext1, cs_zext1) = p4 in
            let (p5, rs_add1) = bit_blast_add g_zext1 rs_xor1 rs_zext1 in
            let (g_add1, cs_add1) = p5 in
            ((g_add1,
            (catrev
              (catrev
                (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_xor1)
                cs_zext1) cs_add1)), rs_add1)
