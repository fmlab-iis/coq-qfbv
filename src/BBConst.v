
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon.
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_const ===== *)

Definition bit_blast_const g (bs : bits) : generator * cnf * word :=
  (g, [::], map lit_of_bool bs).

Definition mk_env_const E g (bs : bits) : env * generator * cnf * word :=
  (E, g, [::], map lit_of_bool bs).

Lemma bit_blast_const_correct g bs E g' cs ls :
  bit_blast_const g bs = (g', cs, ls) -> interp_cnf E (add_prelude cs) ->
  enc_bits E ls bs.
Proof.
  rewrite /bit_blast_const. case=> _ <- <- Hpre. apply: enc_bits_lit_of_bool.
  exact: (add_prelude_enc_bit_tt Hpre).
Qed.

Lemma mk_env_const_is_bit_blast_const E g bs E' g' cs ls :
  mk_env_const E g bs = (E', g', cs, ls) -> bit_blast_const g bs = (g', cs, ls).
Proof. rewrite /mk_env_const /bit_blast_const. by case=> _ <- <- <-. Qed.

Lemma mk_env_const_sat E g bs E' g' cs lrs :
  mk_env_const E g bs = (E', g', cs, lrs) -> interp_cnf E' cs.
Proof. by case=> <- _ <- _. Qed.

Lemma mk_env_const_preserve E g bs E' g' cs lrs :
  mk_env_const E g bs = (E', g', cs, lrs) -> env_preserve E E' g.
Proof. case=> <- _ _ _. exact: env_preserve_refl. Qed.

Lemma mk_env_const_newer_gen E g bs E' g' cs lrs :
  mk_env_const E g bs = (E', g', cs, lrs) -> (g <=? g')%positive.
Proof. case=> _ <- _ _. exact: Pos.leb_refl. Qed.

Lemma mk_env_const_newer_res E g bs E' g' cs lrs :
  mk_env_const E g bs = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  case=> _ <- _ <- Htt {E E' g' cs lrs}. exact: (newer_than_lits_lit_of_bool _ Htt).
Qed.

Lemma mk_env_const_newer_cnf E g bs E' g' cs lrs :
  mk_env_const E g bs = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof. by case => _ <- <- _. Qed.
