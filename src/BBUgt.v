From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From BitBlasting Require Import QFBV CNF BBCommon BBUlt.
From ssrlib Require Import ZAriths Tactics Bools Seqs.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_ugt ===== *)

Definition bit_blast_ugt g ls1 ls2 :generator * cnf * literal :=
  bit_blast_ult g ls2 ls1.

Definition mk_env_ugt E g ls1 ls2 : env * generator * cnf * literal :=
  mk_env_ult E g ls2 ls1.

Lemma bit_blast_ugt_correct g bs1 bs2 E ls1 ls2 g' cs lr :
    bit_blast_ugt g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (gtB bs1 bs2).
Proof.
  rewrite /gtB.
  rewrite /bit_blast_ugt.
  move => Hult Henc1 Henc2 Hcnf.
  exact: (bit_blast_ult_correct Hult Henc2 Henc1 Hcnf) => Hrult.
Qed.

Lemma mk_env_ugt_is_bit_blast_ugt E g ls1 ls2 E' g' cs lr:
    mk_env_ugt E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_ugt g ls1 ls2 = (g', cs, lr).
Proof.
  rewrite /mk_env_ugt /bit_blast_ugt.
  exact: mk_env_ult_is_bit_blast_ult.
Qed.

Lemma mk_env_ugt_newer_gen E g ls1 ls2 E' g' cs lr:
    mk_env_ugt E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  rewrite /mk_env_ugt.
  exact: mk_env_ult_newer_gen.
Qed.

Lemma mk_env_ugt_newer_res E g ls1 ls2 E' g' cs lr:
    mk_env_ugt E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g' lr.
Proof.
  rewrite /mk_env_ugt. move=> H Hnew_gtt.
  exact: (mk_env_ult_newer_res H Hnew_gtt).
Qed.

Lemma mk_env_ugt_newer_cnf E g ls1 ls2 E' g' cs lr:
  mk_env_ugt E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_ugt.
  move=> H e0 e1 e2.
  exact: (mk_env_ult_newer_cnf H e0 e2 e1).
Qed.

Lemma mk_env_ugt_preserve E g ls1 ls2 E' g' cs lr:
    mk_env_ugt E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  rewrite /mk_env_ugt.
  exact: mk_env_ult_preserve.
Qed.

Lemma mk_env_ugt_sat E g ls1 ls2 E' g' cs lr:
    mk_env_ugt E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  rewrite /mk_env_ugt.
  move=> H e0 e1 e2.
  exact: (mk_env_ult_sat H e0 e2 e1).
Qed.
