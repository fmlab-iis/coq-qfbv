
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon.
From ssrlib Require Import ZAriths Seqs Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* auxiliary definitions and lemmas *)

Definition rotater1 ls : word := droplsl (joinmsl ls (lsl ls)).
Definition rotater n ls : word := iter n rotater1 ls.

Lemma enc_bits_rotater1_rorB1 E ls bs :
  interp_lit E lit_tt -> 
  enc_bits E ls bs -> enc_bits E (rotater1 ls) (rorB1 bs) .
Proof.
  move=> Htt Henc. rewrite /rotater1 /rorB1. 
  apply (enc_bits_droplsb Htt). rewrite enc_bits_joinmsb Henc andTb.
  apply enc_bits_lsl; done. 
Qed.

Lemma enc_bits_rotater_rorB E n ls bs :
  interp_lit E lit_tt -> 
  enc_bits E ls bs -> enc_bits E (rotater n ls) (rorB n bs) .
Proof.
  move=> Htt Henc. rewrite /rotater /rorB.
  elim: n => [| n IH] //=. exact: enc_bits_rotater1_rorB1.
Qed.

Lemma newer_than_lits_rotater1 g ls :
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g (rotater1 ls) .
Proof.
  rewrite /rotater1 => Hgtt Hgls. apply newer_than_lits_droplsl.
  apply newer_than_lits_joinmsl; first exact: Hgls. 
  exact: newer_than_lits_lsl.
Qed.

Lemma newer_than_lits_rotater g n ls :
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g (rotater n ls) .
Proof.
  rewrite /rotater => Hgtt Hgls. 
  elim: n => [| n IH] //=. exact: newer_than_lits_rotater1.
Qed.


(* ===== bit_blast_rotateright ===== *)

Definition bit_blast_rotateright g (n : nat) ls : generator * cnf * word :=
  (g, [::], rotater n ls).

Definition mk_env_rotateright E g n ls : env * generator * cnf * word :=
  (E, g, [::], rotater n ls).

Lemma bit_blast_rotateright_correct E g n bs ls g' cs lrs :
  bit_blast_rotateright g n ls = (g', cs, lrs) ->
  enc_bits E ls bs -> interp_cnf E (add_prelude cs) ->
  enc_bits E lrs (rorB n bs) .
Proof.
  rewrite /bit_blast_rotateright. case=> _ _ <- Henc Hics. 
  move: (add_prelude_tt Hics) => Htt.
  exact: enc_bits_rotater_rorB.
Qed.

Lemma mk_env_rotateright_is_bit_blast_rotateright E g n ls E' g' cs lrs :
  mk_env_rotateright E g n ls = (E', g', cs, lrs) ->
  bit_blast_rotateright g n ls = (g', cs, lrs) .
Proof.
  by rewrite /mk_env_rotateright /bit_blast_rotateright; case => _ <- <- <- .
Qed.

Lemma mk_env_rotateright_newer_gen E g n ls E' g' cs lrs :
  mk_env_rotateright E g n ls = (E', g', cs, lrs) -> (g <=? g')%positive .
Proof.
  rewrite /mk_env_rotateright; by t_auto_newer.
Qed.

Lemma mk_env_rotateright_newer_res E g n ls E' g' cs lrs :
  mk_env_rotateright E g n ls = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g' lrs .
Proof.
  rewrite /mk_env_rotateright; case => _ <- _ <- Hgtt Hgls. 
  exact: newer_than_lits_rotater.
Qed.

Lemma mk_env_rotateright_newer_cnf E g n ls E' g' cs lrs :
  mk_env_rotateright E g n ls = (E', g', cs, lrs) ->
  newer_than_cnf g' cs .
Proof.
  by rewrite /mk_env_rotateright; case => _ <- <- _.
Qed.

Lemma mk_env_rotateright_preserve E g n ls E' g' cs lrs :
  mk_env_rotateright E g n ls = (E', g', cs, lrs) -> env_preserve E E' g.
Proof.
  by rewrite /mk_env_rotateright; case => <- _ _ _.
Qed.

Lemma mk_env_rotateright_sat E g n ls E' g' cs lrs :
  mk_env_rotateright E g n ls = (E', g', cs, lrs) ->
  interp_cnf E' cs.
Proof.
  by rewrite /mk_env_rotateright; case => <- _ <- _.
Qed.

Lemma mk_env_rotateright_env_equal E1 E2 g n ls E1' E2' g1 g2 cs1 cs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_rotateright E1 g n ls = (E1', g1, cs1, lrs1) ->
  mk_env_rotateright E2 g n ls = (E2', g2, cs2, lrs2) ->
  env_equal E1' E2' /\ g1 = g2 /\ cs1 = cs2 /\ lrs1 = lrs2.
Proof.
  rewrite /mk_env_rotateright => Heq.
  case=> ? ? ? ?; case=> ? ? ? ?; subst. done.
Qed.
