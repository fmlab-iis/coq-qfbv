From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From BitBlasting Require Import Var QFBV CNF BBCommon BBUle.
From ssrlib Require Import ZAriths Tactics Bools Seqs.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== bit_blast_uge ===== *)

Definition bit_blast_uge g ls1 ls2 : generator * cnf * literal :=
  bit_blast_ule g ls2 ls1.

Definition mk_env_uge E g ls1 ls2 : env * generator * cnf * literal :=
  mk_env_ule E g ls2 ls1.

Lemma bit_blast_uge_correct g bs1 bs2 E ls1 ls2 g' cs lr :
  bit_blast_uge g ls1 ls2 = (g', cs, lr) ->
  size ls1 = size ls2 ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bit E lr (geB bs1 bs2).
Proof.
  rewrite /geB.
  rewrite /bit_blast_uge.
  move => Hule Hsz Henc1 Henc2 Hcnf.
  symmetry in Hsz.
  exact : (bit_blast_ule_correct Hule Hsz Henc2 Henc1 Hcnf) => Hrule.
Qed.

Lemma mk_env_uge_is_bit_blast_uge E g ls1 ls2 E' g' cs lr:
    mk_env_uge E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_uge g ls1 ls2 = (g', cs, lr).
Proof.
  rewrite /mk_env_uge /bit_blast_uge.
  exact: mk_env_ule_is_bit_blast_ule.
Qed.

Lemma mk_env_uge_newer_gen E g ls1 ls2 E' g' cs lr:
    mk_env_uge E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  rewrite /mk_env_uge.
  exact: mk_env_ule_newer_gen.
Qed.

Lemma mk_env_uge_newer_res E g ls1 ls2 E' g' cs lr:
    mk_env_uge E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g' lr.
Proof.
  rewrite /mk_env_uge. move=> H.
  exact: (mk_env_ule_newer_res H).
Qed.

Lemma mk_env_uge_newer_cnf E g ls1 ls2 E' g' cs lr:
    mk_env_uge E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_uge.
  move=> H e0 e1 e2.
  exact: (mk_env_ule_newer_cnf H e0 e2 e1).
Qed.

Lemma mk_env_uge_preserve E g ls1 ls2 E' g' cs lr:
    mk_env_uge E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  rewrite /mk_env_uge.
  exact: mk_env_ule_preserve.
Qed.

Lemma mk_env_uge_sat E g ls1 ls2 E' g' cs lr:
    mk_env_uge E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  rewrite /mk_env_uge.
  move=> H e0 e1 e2.
  exact: (mk_env_ule_sat H e0 e2 e1).
Qed.
