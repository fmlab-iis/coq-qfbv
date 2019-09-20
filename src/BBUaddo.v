From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From BitBlasting Require Import Var QFBV CNF BBCommon BBAdd.
From ssrlib Require Import ZAriths Tactics Bools Seqs.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== bit_blast_uaddo ===== *)

Definition bit_blast_uaddo g ls1 ls2: generator * cnf * literal :=
  let '(g', cs, cout, lrs) := bit_blast_full_adder g lit_ff ls1 ls2 in
  (g', cs, cout).

Lemma bit_blast_uaddo_correct g bs1 bs2 E ls1 ls2 g' cs lr :
  bit_blast_uaddo g ls1 ls2 = (g', cs, lr) ->
  size ls1 == size ls2 ->
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bit E lr (carry_addB bs1 bs2).
Proof.
  rewrite /bit_blast_uaddo.
  case Hblast: (bit_blast_full_adder g lit_ff ls1 ls2) => [[[og ocs] olcout] olrs].
  case HadcB: (adcB false bs1 bs2) => [obcout obrs].
  case=> _ Hocs Holr => Hsz Henc1 Henc2 Hcs.
  rewrite -Hocs in Hcs.
  rewrite -Holr.
  move: (add_prelude_enc_bit_ff Hcs) => Hff.
  move: (bit_blast_full_adder_correct2 Hblast Henc1 Henc2 Hff Hcs HadcB (eqP Hsz)).
  by rewrite/carry_addB HadcB.
Qed.

Definition mk_env_uaddo E g ls1 ls2: env * generator * cnf * literal :=
  let '(E', g', cs, cout, lrs) := mk_env_full_adder E g lit_ff ls1 ls2 in
  (E', g', cs, cout).

Lemma mk_env_uaddo_is_bit_blast_uaddo E g ls1 ls2 E' g' cs lr:
    mk_env_uaddo E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_uaddo g ls1 ls2 = (g', cs, lr).
Proof.
  rewrite /mk_env_uaddo /bit_blast_uaddo.
  case Hmk: (mk_env_full_adder E g lit_ff ls1 ls2 ) => [[[[E'0 g'0] cs0] cout] lrs0].
  move : (mk_env_full_adder_is_bit_blast_full_adder Hmk) => Hbb.
  rewrite Hbb. move =>[] _ <- <- <-.
  done.
Qed.

Lemma mk_env_uaddo_newer_gen E g ls1 ls2 E' g' cs lr :
    mk_env_uaddo E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  rewrite /mk_env_uaddo.
  case Hmk: (mk_env_full_adder E g lit_ff ls1 ls2) => [[[[E'0 g'0] cs0] cout] lrs0]. move => [] _ <- _ _.
  apply (mk_env_full_adder_newer_gen Hmk).
Qed.

Lemma mk_env_uaddo_newer_res E g ls1 ls2 E' g' cs lr :
    mk_env_uaddo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g' lr.
Proof.
  rewrite /mk_env_uaddo.
  case Hmk: (mk_env_full_adder E g lit_ff ls1 ls2) => [[[[E'0 g'0] cs0] cout] lrs0].
  move => [] _ <- _ <- Hngtt.
  apply (mk_env_full_adder_newer_cout Hmk Hngtt).
Qed.

Lemma mk_env_uaddo_newer_cnf E g ls1 ls2 E' g' cs lr:
  mk_env_uaddo E g ls1 ls2 = (E', g', cs, lr) ->
  size ls1 == size ls2 ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 ->
  newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_uaddo.
  case Hmk: (mk_env_full_adder E g lit_ff ls1 ls2) => [[[[E'0 g'0] cs0] cout] lrs0].
  case=> _ <- <- _ Hsz Hgtt Hgls1 Hgls2.
  exact (mk_env_full_adder_newer_cnf Hmk Hgls1 Hgls2 Hgtt (eqP Hsz)).
Qed.

Lemma mk_env_uaddo_preserve E g ls1 ls2 E' g' cs lr :
    mk_env_uaddo E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  rewrite /mk_env_uaddo.
  case Hmk: (mk_env_full_adder E g lit_ff ls1 ls2) => [[[[E'0 g'0] cs0] cout] lrs0].
  move => [] <- _ _ _.
  apply (mk_env_full_adder_preserve Hmk).
Qed.

Lemma mk_env_uaddo_sat E g ls1 ls2 E' g' cs lr :
  mk_env_uaddo E g ls1 ls2 = (E', g', cs, lr) ->
  size ls1 == size ls2 ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 ->
  newer_than_lits g ls2 ->
  interp_cnf E' cs.
Proof.
  rewrite /mk_env_uaddo.
  case Hmk: (mk_env_full_adder E g lit_ff ls1 ls2) => [[[[E'0 g'0] cs0] cout] lrs0].
  move => [] <- _ <- _ Hsz Hgtt Hgls1 Hgls2.
  exact: (mk_env_full_adder_sat Hmk Hgls1 Hgls2 Hgtt (eqP Hsz)).
Qed.
