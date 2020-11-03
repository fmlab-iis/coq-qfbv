
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon.
From ssrlib Require Import ZAriths Seqs Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* auxiliary lemmas *)

Lemma enc_bits_repeat E n ls bs :
  enc_bits E ls bs -> enc_bits E (repeat n ls) (repeat n bs) .
Proof.
  elim: n => [| n IH] //=. 
  move=> Henc. apply enc_bits_cat; [done | exact: (IH Henc)].
Qed.  

Lemma newer_than_lits_repeat g n ls :
  newer_than_lits g ls -> newer_than_lits g (repeat n ls) .
Proof.
  elim: n => [| n IH] //=.
  move=> Hgls. by rewrite newer_than_lits_cat Hgls (IH Hgls).
Qed.

(* ===== bit_blast_repeat ===== *)

Definition bit_blast_repeat g (n : nat) ls : generator * cnf * word :=
  (g, [::], repeat n ls).

Definition mk_env_repeat E g n ls : env * generator * cnf * word :=
  (E, g, [::], repeat n ls).

Lemma bit_blast_repeat_correct E g n bs ls g' cs lrs :
  bit_blast_repeat g n ls = (g', cs, lrs) ->
  enc_bits E ls bs -> interp_cnf E (add_prelude cs) ->
  enc_bits E lrs (repeat n bs) .
Proof.
  rewrite /bit_blast_repeat. case=> _ _ <- Henc _. exact: enc_bits_repeat.
Qed.

Lemma mk_env_repeat_is_bit_blast_repeat E g n ls E' g' cs lrs :
  mk_env_repeat E g n ls = (E', g', cs, lrs) ->
  bit_blast_repeat g n ls = (g', cs, lrs) .
Proof.
  by rewrite /mk_env_repeat /bit_blast_repeat; case => _ <- <- <- .
Qed.

Lemma mk_env_repeat_newer_gen E g n ls E' g' cs lrs :
  mk_env_repeat E g n ls = (E', g', cs, lrs) -> (g <=? g')%positive .
Proof.
  rewrite /mk_env_repeat; by t_auto_newer.
Qed.

Lemma mk_env_repeat_newer_res E g n ls E' g' cs lrs :
  mk_env_repeat E g n ls = (E', g', cs, lrs) ->
  newer_than_lits g ls -> newer_than_lits g' lrs .
Proof.
  rewrite /mk_env_repeat; case => _ <- _ <- Hgls. exact: newer_than_lits_repeat.
Qed.

Lemma mk_env_repeat_newer_cnf E g n ls E' g' cs lrs :
  mk_env_repeat E g n ls = (E', g', cs, lrs) ->
  newer_than_cnf g' cs .
Proof.
  by rewrite /mk_env_repeat; case => _ <- <- _.
Qed.

Lemma mk_env_repeat_preserve E g n ls E' g' cs lrs :
  mk_env_repeat E g n ls = (E', g', cs, lrs) -> env_preserve E E' g.
Proof.
  by rewrite /mk_env_repeat; case => <- _ _ _.
Qed.

Lemma mk_env_repeat_sat E g n ls E' g' cs lrs :
  mk_env_repeat E g n ls = (E', g', cs, lrs) ->
  interp_cnf E' cs.
Proof.
  by rewrite /mk_env_repeat; case => <- _ <- _.
Qed.
