From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBConst BBNeg BBAnd BBAdd BBShl BBSub BBMul BBAshr BBUge BBUdiv BBSdiv BBEq.
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition smodB bs1 bs2 : bits :=
  let (q_sdiv, r_sdiv) := sdivB bs1 bs2 in 
  if (msb bs1 == msb bs2) || (r_sdiv == (zeros (size bs2))) then
    r_sdiv
  else addB r_sdiv bs2.

(* ===== bit_blast_smod ===== *)

Definition word0 n := map (lit_of_bool) (zeros n). 

Definition bit_blast_smod g ls1 ls2 : generator * cnf * word :=
  let (ls1_tl, ls1_sign) := splitmsl ls1 in
  let (ls2_tl, ls2_sign) := splitmsl ls2 in
  let '(g_sdiv, cs_sdiv, q_sdiv, r_sdiv) := bit_blast_sdiv g ls1 ls2 in
  let '(g_and, cs_and, r_eq) := bit_blast_eq g_sdiv r_sdiv (word0 (size r_sdiv)) in
  if (ls1_sign == ls2_sign) || (r_eq == lit_tt) then
    (g_sdiv, cs_sdiv, r_sdiv)
  else let '(g_add, cs_add, lrs_add) := bit_blast_add g r_sdiv ls2 in
       (g_add, catrev cs_sdiv cs_add, lrs_add).
    