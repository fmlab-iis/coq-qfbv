From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import Var QFBV CNF BBCommon BBSlt.
From ssrlib Require Import ZAriths Seqs Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ===== bit_blast_sgt ===== *)

Definition bit_blast_sgt g ls1 ls2: generator * cnf * literal :=
  bit_blast_slt g ls2 ls1.

Definition sgtB (bs1 bs2: bits) := sltB bs2 bs1.

Lemma bit_blast_sgt_correct g bs1 bs2 E ls1 ls2 g' cs lr:
  bit_blast_sgt g ls1 ls2 = (g', cs, lr) ->
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bit E lr (sgtB bs1 bs2).
Proof.
  rewrite /bit_blast_sgt /sgtB => Hbb Henc1 Henc2. 
  exact: (bit_blast_slt_correct Hbb Henc2 Henc1).
Qed.

Definition mk_env_sgt E g ls1 ls2: env * generator * cnf * literal :=
  mk_env_slt E g ls2 ls1.

Lemma mk_env_sgt_is_bit_blast_sgt E g ls1 ls2 E' g' cs lr:
  mk_env_sgt E g ls1 ls2 = (E', g', cs, lr) ->
  bit_blast_sgt g ls1 ls2 = (g', cs, lr).
Proof.
  rewrite /mk_env_sgt /bit_blast_sgt. 
  exact: mk_env_slt_is_bit_blast_slt.
Qed.

Lemma mk_env_sgt_newer_gen E g ls1 ls2 E' g' cs lr:
  mk_env_sgt E g ls1 ls2 = (E', g', cs, lr) ->
  (g <=? g')%positive.
Proof.
  rewrite /mk_env_sgt. exact: mk_env_slt_newer_gen.
Qed.

Lemma mk_env_sgt_newer_res E g ls1 ls2 E' g' cs lr:
  mk_env_sgt E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g' lr.
Proof.
  rewrite /mk_env_sgt. exact: mk_env_slt_newer_res.
Qed.  

Lemma mk_env_sgt_newer_cnf E g ls1 ls2 E' g' cs lr:
  mk_env_sgt E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_sgt => Hmkslt Hgt Hgl1 Hgl2.
  exact (mk_env_slt_newer_cnf Hmkslt Hgt Hgl2 Hgl1).
Qed.

Lemma mk_env_sgt_preserve E g ls1 ls2 E' g' cs lr:
  mk_env_sgt E g ls1 ls2 = (E', g', cs, lr) ->
  env_preserve E E' g.
Proof.
  rewrite /mk_env_sgt. exact: mk_env_slt_preserve.
Qed.

Lemma mk_env_sgt_sat E g ls1 ls2 E' g' cs lr:
  mk_env_sgt E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  interp_cnf E' cs.
Proof.
  rewrite /mk_env_sgt => Hmkslt Hgt Hgl1 Hgl2.
  exact: (mk_env_slt_sat Hmkslt Hgt Hgl2 Hgl1).
Qed.
