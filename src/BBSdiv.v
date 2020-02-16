From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBConst BBXor BBEq BBZeroExtend BBNeg BBAnd BBAdd BBShl BBSub BBMul BBAshr BBUge BBUdiv .
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_sdiv ===== *)
Definition sdivB bs1 bs2 : bits * bits :=
  if (msb bs1 == msb bs2) && negb (msb bs1) then udivB bs1 bs2
  else if (msb bs1 == msb bs2) && (msb bs1) then ((udivB bs1 bs2).1, negB (udivB bs1 bs2).2)
       else if (msb bs1 != msb bs2) && negb (msb bs1) then (negB (udivB bs1 bs2).1, (udivB bs1 bs2).2)
            else (negB (udivB bs1 bs2).1, negB (udivB bs1 bs2).2).

Definition bit_blast_abs g ls : generator * cnf * word :=
  let (ls_tl, ls_sign) := splitmsl ls in
  if (ls_sign == lit_tt) then  bit_blast_neg g ls
  else if (ls_sign == lit_ff) then (g, [::], ls)
       else let ws := copy (size ls_tl) ls_sign in
            let '(g_xor, cs_xor, rs_xor) := bit_blast_xor g ls ws in
            let '(g_zext, cs_zext, rs_zext) := bit_blast_zeroextend (size ls_tl) g_xor (ls_sign::nil) in 
            let '(g_add, cs_add, rs_add) := bit_blast_add g_zext rs_xor rs_zext in
            (g_add, catrev cs_xor (catrev cs_zext cs_add), rs_add).

Definition bit_blast_sdiv g ls1 ls2 : generator * cnf * word * word :=
  let (ls1_tl, ls1_sign) := splitmsl ls1 in
  let (ls2_tl, ls2_sign) := splitmsl ls2 in
  let ws1 := copy (size ls1_tl) ls1_sign in
  let '(g_abs1, cs_abs1, lrs_abs1) := bit_blast_abs g ls1 in
  let '(g_abs2, cs_abs2, lrs_abs2) := bit_blast_abs g_abs1 ls2 in
  let '(g_udiv, cs_udiv, qs_udiv, rs_udiv) := bit_blast_udiv g_abs2 lrs_abs1 lrs_abs2 in
  let '(g_negq, cs_negq, lrs_negq) := bit_blast_neg g_udiv qs_udiv in
  let '(g_negr, cs_negr, lrs_negr) := bit_blast_neg g_udiv rs_udiv in
  if (ls1_sign == ls2_sign) && (ls1_sign == lit_ff) then
    (g_udiv, catrev cs_udiv (catrev cs_abs1 cs_abs2), qs_udiv, rs_udiv)
  else if (ls1_sign == ls2_sign) && (ls1_sign == lit_tt) then
         (g_negr, catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negr, qs_udiv, lrs_negr)
       else if (ls1_sign != ls2_sign) && (ls1_sign == lit_ff) then
              (g_negq, catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negq, lrs_negq, rs_udiv)
            else 
              let '(g_eq, cs_eq, r_eq) := bit_blast_eq g_udiv (ls1_sign::nil) (ls2_sign::nil) in
              let weq := copy (size ls1_tl) r_eq in 
              let '(g_xor, cs_xor, rs_xor) := bit_blast_xor g qs_udiv weq in
              let '(g_zext, cs_zext, rs_zext) := bit_blast_zeroextend (size ls1_tl) g_xor weq in
              let '(g_add, cs_add, rs_add) := bit_blast_add g_zext rs_xor rs_zext in
              let '(g_xor1, cs_xor1, rs_xor1) := bit_blast_xor g rs_udiv ws1 in
              let '(g_zext1, cs_zext1, rs_zext1) := bit_blast_zeroextend (size ls1_tl) g_xor1 (ls1_sign::nil) in
              let '(g_add1, cs_add1, rs_add1) := bit_blast_add g_zext1 rs_xor1 rs_zext1 in
              (g, catrev (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negq) cs_negr, rs_add, rs_add1).


         
