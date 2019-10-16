From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBConst BBNeg BBAnd BBAdd BBShl BBSub BBMul BBAshr BBUge BBUdiv BBSdiv.
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ===== bit_blast_smod ===== *)

Definition word0 n := map (lit_of_bool) (zeros n).

Definition bit_blast_smod g ls1 ls2 : generator * cnf * word :=
  let '(g_sdiv, cs_sdiv, q_sdiv, r_sdiv) := bit_blast_sdiv g ls1 ls2 in
  if (msl ls1 == msl ls2) || (r_sdiv == word0 (size ls1)) then
    (g_sdiv, cs_sdiv, r_sdiv)
  else let '(g_add, cs_add, lrs_add) := bit_blast_add g r_sdiv ls2 in
       (g_add, catrev cs_sdiv cs_add, lrs_add).
    