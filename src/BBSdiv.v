From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBConst BBNeg BBAnd BBAdd BBShl BBSub BBMul BBAshr BBUge BBUdiv .
From ssrlib Require Import Var ZAriths Tactics.
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
  if (msl ls == lit_tt) then  bit_blast_neg g ls
  else (g, [::], ls).

Definition bit_blast_sdiv g ls1 ls2 : generator * cnf * word * word :=
  let '(g_abs1, cs_abs1, lrs_abs1) := bit_blast_abs g ls1 in
  let '(g_abs2, cs_abs2, lrs_abs2) := bit_blast_abs g_abs1 ls2 in
  let '(g_udiv, cs_udiv, qs_udiv, rs_udiv) := bit_blast_udiv g_abs2 lrs_abs1 lrs_abs2 in
  let '(g_negq, cs_negq, lrs_negq) := bit_blast_neg g_udiv qs_udiv in
  let '(g_negr, cs_negr, lrs_negr) := bit_blast_neg g_udiv rs_udiv in
  if (msl ls1 == msl ls2) && (msl ls1 == lit_ff) then
    (g_udiv, catrev (catrev cs_abs1 cs_abs2) cs_udiv, qs_udiv, rs_udiv)
  else if (msl ls1 == msl ls2) && (msl ls1 == lit_tt) then
         (g_negr, catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negr, qs_udiv, lrs_negr)
       else if (msl ls1 != msl ls2) && (msl ls1 == lit_ff) then
              (g_negq, catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negq, lrs_negq, rs_udiv)
            else (g_negr, catrev (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negq) cs_negr, lrs_negq, lrs_negr).


         
