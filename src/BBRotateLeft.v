
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon.
From ssrlib Require Import ZAriths Seqs Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* auxiliary definitions and lemmas *)

Definition rotatel1 ls : word := dropmsl (joinlsl (msl ls) ls).
Definition rotatel n ls : word := iter n rotatel1 ls.

Lemma enc_bits_rotatel1_rolB1 E ls bs :
  interp_lit E lit_tt -> 
  enc_bits E ls bs -> enc_bits E (rotatel1 ls) (rolB1 bs) .
Proof.
  move=> Htt Henc. rewrite /rotatel1 /rolB1. 
  apply (enc_bits_dropmsb Htt). rewrite enc_bits_joinlsb Henc andbT.
  apply enc_bit_lastd; last exact: Henc. 
  rewrite /= in Htt. by rewrite /enc_bit /= Htt.
Qed.

Lemma enc_bits_rotatel_rolB E n ls bs :
  interp_lit E lit_tt -> 
  enc_bits E ls bs -> enc_bits E (rotatel n ls) (rolB n bs) .
Proof.
  move=> Htt Henc. rewrite /rotatel /rolB.
  elim: n => [| n IH] //=. exact: enc_bits_rotatel1_rolB1.
Qed.

Lemma newer_than_lits_rotatel1 g ls :
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g (rotatel1 ls) .
Proof.
  rewrite /rotatel1 => Hgtt Hgls. apply newer_than_lits_dropmsl.
  apply newer_than_lits_joinlsl; last exact: Hgls.
  exact: newer_than_lits_msl.
Qed.

Lemma newer_than_lits_rotatel g n ls :
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g (rotatel n ls) .
Proof.
  rewrite /rotatel => Hgtt Hgls. 
  elim: n => [| n IH] //=. exact: newer_than_lits_rotatel1.
Qed.


(* ===== bit_blast_rotateleft ===== *)

Definition bit_blast_rotateleft g (n : nat) ls : generator * cnf * word :=
  (g, [::], rotatel n ls).

Definition mk_env_rotateleft E g n ls : env * generator * cnf * word :=
  (E, g, [::], rotatel n ls).

Lemma bit_blast_rotateleft_correct E g n bs ls g' cs lrs :
  bit_blast_rotateleft g n ls = (g', cs, lrs) ->
  enc_bits E ls bs -> interp_cnf E (add_prelude cs) ->
  enc_bits E lrs (rolB n bs) .
Proof.
  rewrite /bit_blast_rotateleft. case=> _ _ <- Henc Hics. 
  move: (add_prelude_tt Hics) => Htt.
  exact: enc_bits_rotatel_rolB.
Qed.

Lemma mk_env_rotateleft_is_bit_blast_rotateleft E g n ls E' g' cs lrs :
  mk_env_rotateleft E g n ls = (E', g', cs, lrs) ->
  bit_blast_rotateleft g n ls = (g', cs, lrs) .
Proof.
  by rewrite /mk_env_rotateleft /bit_blast_rotateleft; case => _ <- <- <- .
Qed.

Lemma mk_env_rotateleft_newer_gen E g n ls E' g' cs lrs :
  mk_env_rotateleft E g n ls = (E', g', cs, lrs) -> (g <=? g')%positive .
Proof.
  rewrite /mk_env_rotateleft; by t_auto_newer.
Qed.

Lemma mk_env_rotateleft_newer_res E g n ls E' g' cs lrs :
  mk_env_rotateleft E g n ls = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g' lrs .
Proof.
  rewrite /mk_env_rotateleft; case => _ <- _ <- Hgtt Hgls. 
  exact: newer_than_lits_rotatel.
Qed.

Lemma mk_env_rotateleft_newer_cnf E g n ls E' g' cs lrs :
  mk_env_rotateleft E g n ls = (E', g', cs, lrs) ->
  newer_than_cnf g' cs .
Proof.
  by rewrite /mk_env_rotateleft; case => _ <- <- _.
Qed.

Lemma mk_env_rotateleft_preserve E g n ls E' g' cs lrs :
  mk_env_rotateleft E g n ls = (E', g', cs, lrs) -> env_preserve E E' g.
Proof.
  by rewrite /mk_env_rotateleft; case => <- _ _ _.
Qed.

Lemma mk_env_rotateleft_sat E g n ls E' g' cs lrs :
  mk_env_rotateleft E g n ls = (E', g', cs, lrs) ->
  interp_cnf E' cs.
Proof.
  by rewrite /mk_env_rotateleft; case => <- _ <- _.
Qed.

Lemma mk_env_rotateleft_env_equal E1 E2 g n ls E1' E2' g1 g2 cs1 cs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_rotateleft E1 g n ls = (E1', g1, cs1, lrs1) ->
  mk_env_rotateleft E2 g n ls = (E2', g2, cs2, lrs2) ->
  env_equal E1' E2' /\ g1 = g2 /\ cs1 = cs2 /\ lrs1 = lrs2.
Proof.
  rewrite /mk_env_rotateleft => Heq.
  case=> ? ? ? ?; case=> ? ? ? ?; subst. done.
Qed.
