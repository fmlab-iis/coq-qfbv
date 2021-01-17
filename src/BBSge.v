From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBSle.
From ssrlib Require Import ZAriths Seqs Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ===== bit_blast_sge ===== *)

Definition bit_blast_sge g ls1 ls2: generator * cnf * literal :=
  bit_blast_sle g ls2 ls1.

Lemma bit_blast_sge_correct g bs1 bs2 E ls1 ls2 g' cs lr:
  bit_blast_sge g ls1 ls2 = (g', cs, lr) ->
  size ls1 = size ls2 ->
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bit E lr (sgeB bs1 bs2).
Proof.
  rewrite /bit_blast_sge /sgeB => Hbb Hsz Henc1 Henc2.
  by apply: (bit_blast_sle_correct Hbb). 
Qed.

Definition mk_env_sge E g ls1 ls2: env * generator * cnf * literal :=
  mk_env_sle E g ls2 ls1.

Lemma mk_env_sge_is_bit_blast_sge E g ls1 ls2 E' g' cs lr:
  mk_env_sge E g ls1 ls2 = (E', g', cs, lr) ->
  bit_blast_sge g ls1 ls2 = (g', cs, lr).
Proof.
  rewrite /mk_env_sge /bit_blast_sge. 
  exact: mk_env_sle_is_bit_blast_sle.
Qed.

Lemma mk_env_sge_newer_gen E g ls1 ls2 E' g' cs lr:
  mk_env_sge E g ls1 ls2 = (E', g', cs, lr) ->
  (g <=? g')%positive.
Proof.
  rewrite /mk_env_sge. exact: mk_env_sle_newer_gen.
Qed.

Lemma mk_env_sge_newer_res E g ls1 ls2 E' g' cs lr:
  mk_env_sge E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g' lr.
Proof.
  rewrite /mk_env_sge. exact: mk_env_sle_newer_res.
Qed.

Lemma mk_env_sge_newer_cnf E g ls1 ls2 E' g' cs lr:
  mk_env_sge E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_sge => Hmksle Hgt Hgl1 Hgl2.
  exact (mk_env_sle_newer_cnf Hmksle Hgt Hgl2 Hgl1).
Qed.

Lemma mk_env_sge_preserve E g ls1 ls2 E' g' cs lr:
  mk_env_sge E g ls1 ls2 = (E', g', cs, lr) ->
  env_preserve E E' g.
Proof.
  rewrite /mk_env_sge. exact: mk_env_sle_preserve.
Qed.

Lemma mk_env_sge_sat E g ls1 ls2 E' g' cs lr:
  mk_env_sge E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  interp_cnf E' cs.
Proof.
  rewrite /mk_env_sge => Hmksle Hgt Hgl1 Hgl2.
  exact: (mk_env_sle_sat Hmksle Hgt Hgl2 Hgl1).
Qed.

Lemma mk_env_sge_env_equal E1 E2 g ls1 ls2 E1' E2' g1' g2' cs1 cs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_sge E1 g ls1 ls2 = (E1', g1', cs1, lrs1) ->
  mk_env_sge E2 g ls1 ls2 = (E2', g2', cs2, lrs2) ->
  env_equal E1' E2' /\ g1' = g2' /\ cs1 = cs2 /\ lrs1 = lrs2.
Proof. exact: mk_env_sle_env_equal. Qed.
