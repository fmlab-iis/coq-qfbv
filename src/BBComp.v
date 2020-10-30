
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBEq.
From ssrlib Require Import ZAriths Seqs Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== bit_blast_comp ===== *)

Definition bit_blast_comp g ls1 ls2 : generator * cnf * word :=
  let '(g', cs, lr) := bit_blast_eq g ls1 ls2 in
  (g', cs, [:: lr]).

Definition mk_env_comp E g ls1 ls2 : env * generator * cnf * word :=
  let '(E', g', cs, lr) := mk_env_eq E g ls1 ls2 in
  (E', g', cs, [:: lr]).

Lemma bit_blast_comp_correct E g bs1 bs2 ls1 ls2 g' cs lrs :
  bit_blast_comp g ls1 ls2 = (g', cs, lrs) ->
  size ls1 = size ls2 ->
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 -> interp_cnf E (add_prelude cs) ->
  enc_bits E lrs [:: (bs1 == bs2)].
Proof.
  rewrite /bit_blast_comp. 
  case Hbb : (bit_blast_eq g ls1 ls2) => [[g_eq cs_eq] lr_eq]. 
  case=> _ <- <- Hsz Henc1 Henc2 Hics. rewrite enc_bits_seq1. 
  exact: (bit_blast_eq_correct Hbb).
Qed.

Lemma mk_env_comp_is_bit_blast_comp E g ls1 ls2 E' g' cs lrs :
  mk_env_comp E g ls1 ls2 = (E', g', cs, lrs) ->
  bit_blast_comp g ls1 ls2 = (g', cs, lrs).
Proof.
  rewrite /mk_env_comp /bit_blast_comp.
  case Hmk : (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] lr_eq]. 
  case => _ <- <- <- . by rewrite (mk_env_eq_is_bit_blast_eq Hmk).
Qed.

Lemma mk_env_comp_newer_gen E g ls1 ls2 E' g' cs lrs :
  mk_env_comp E g ls1 ls2 = (E', g', cs, lrs) -> (g <=? g')%positive .
Proof.
  rewrite /mk_env_comp.
  case Hmk : (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] lr_eq]. 
  case=> _ <- _ _. exact: (mk_env_eq_newer_gen Hmk).
Qed.

Lemma mk_env_comp_newer_res E g ls1 ls2 E' g' cs lrs :
  mk_env_comp E g ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_lits g' lrs .
Proof.
  rewrite /mk_env_comp. 
  case Hmk : (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] lr_eq]. 
  case=> _ <- _ <-. rewrite newer_than_lits_cons /= andbT. 
  exact: (mk_env_eq_newer_res Hmk).
Qed.

Lemma mk_env_comp_newer_cnf E g ls1 ls2 E' g' cs lrs :
  mk_env_comp E g ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs .
Proof.
  rewrite /mk_env_comp. 
  case Hmk : (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] lr_eq]. 
  case=> _ <- <- _ Hgtt Hgls1 Hgls2. exact: (mk_env_eq_newer_cnf Hmk).
Qed.

Lemma mk_env_comp_preserve E g ls1 ls2 E' g' cs lrs :
  mk_env_comp E g ls1 ls2 = (E', g', cs, lrs) -> env_preserve E E' g.
Proof.
  rewrite /mk_env_comp. 
  case Hmk : (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] lr_eq]. 
  case=> <- _ _ _. exact: (mk_env_eq_preserve Hmk).
Qed.

Lemma mk_env_comp_sat E g ls1 ls2 E' g' cs lrs :
  mk_env_comp E g ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  interp_cnf E' cs.
Proof.
  rewrite /mk_env_comp. 
  case Hmk : (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] lr_eq]. 
  case=> <- _ <- _ Hgtt Hgls1 Hgls2. exact: (mk_env_eq_sat Hmk).
Qed.
