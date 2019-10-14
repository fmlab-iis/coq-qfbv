
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon.
From ssrlib Require Import ZAriths Seqs Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== bit_blast_concat ===== *)

Definition bit_blast_concat g ls1 ls0 : generator * cnf * word :=
  (g, [::], ls0 ++ ls1) .

Definition mk_env_concat E g ls1 ls0 : env * generator * cnf * word :=
  (E, g, [::], ls0 ++ ls1) .

Lemma bit_blast_concat_correct E g bs0 bs1 ls0 ls1 g' cs lr :
  bit_blast_concat g ls1 ls0 = (g', cs, lr) ->
    enc_bits E ls0 bs0 ->
    enc_bits E ls1 bs1 ->
    enc_bits E lr (cat bs0 bs1) .
Proof .
  case => _ _ <-; exact: enc_bits_cat .
Qed .

Lemma mk_env_concat_is_bit_blast_concat E g ls0 ls1 E' g' cs lr :
  mk_env_concat E g ls1 ls0 = (E', g', cs, lr) ->
  bit_blast_concat g ls1 ls0 = (g', cs, lr) .
Proof .
  rewrite /mk_env_concat /bit_blast_concat .
  case => _ <- <- <- // .
Qed .

Lemma mk_env_concat_newer_gen E g ls0 ls1 E' g' cs lr :
  mk_env_concat E g ls1 ls0 = (E', g', cs, lr) ->
  (g <=? g')%positive .
Proof .
  rewrite /mk_env_concat; case => _ <- _ _ .
  t_auto_newer .
Qed .

Lemma mk_env_concat_newer_res E g ls0 ls1 E' g' cs lrs :
  mk_env_concat E g ls1 ls0 = (E', g', cs, lrs) ->
  newer_than_lits g ls0 -> newer_than_lits g ls1 ->
  newer_than_lits g' lrs .
Proof .
  rewrite /mk_env_concat; case => _ <- _ <- Hls0 Hls1 .
  rewrite newer_than_lits_cat Hls0 Hls1 // .
Qed .

Lemma mk_env_concat_newer_cnf E g ls0 ls1 E' g' cs lrs :
  mk_env_concat E g ls1 ls0 = (E', g', cs, lrs) ->
  newer_than_lits g ls0 -> newer_than_lits g ls1 ->
  newer_than_cnf g' cs .
Proof .
  rewrite /mk_env_concat; case => _ <- <- _ // .
Qed .

Lemma mk_env_concat_preserve E g ls0 ls1 E' g' cs lrs :
  mk_env_concat E g ls1 ls0 = (E', g', cs, lrs) -> env_preserve E E' g .
Proof .
  rewrite /mk_env_concat; case => <- _ _ _ // .
Qed .

Lemma mk_env_concat_sat E g ls0 ls1 E' g' cs lrs :
  mk_env_concat E g ls1 ls0 = (E', g', cs, lrs) ->
  newer_than_lits g ls0 -> newer_than_lits g ls1 ->
  interp_cnf E' cs .
Proof .
  rewrite /mk_env_concat; case => <- _ <- _ // .
Qed .

