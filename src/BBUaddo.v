From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon BBAdd.
From ssrlib Require Import Var ZAriths Tuples Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== bit_blast_uaddo ===== *)

Definition bit_blast_uaddo w g (ls1 ls2: w.-tuple literal) : generator * cnf * literal :=
  let '(g', cs, cout, lrs) := bit_blast_full_adder g lit_ff ls1 ls2 in
  (g', cs, cout).

Lemma bit_blast_uaddo_correct :
  forall w g (bs1 bs2 : BITS w) E ls1 ls2 br g' cs lr,
    bit_blast_uaddo g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    carry_addB bs1 bs2 = br->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr br.
Proof.
  move=> n g bs1 bs2 E ls1 ls2 br g' cs lrs.
  rewrite /bit_blast_uaddo. case HadcB: (adcB false bs1 bs2) => [obcout obrs].
  case Hblast: (bit_blast_full_adder g lit_ff ls1 ls2) => [[[og ocs] olcout] olrs].
  case=> _ <- <- => Henc1 Henc2 <- Hcs.
  apply: (bit_blast_full_adder_correct2 Hblast Henc1 Henc2 _ Hcs HadcB).
  exact: (add_prelude_enc_bit_ff Hcs).
Qed.

Definition mk_env_uaddo w E (g: generator) (ls1 ls2: w.-tuple literal) : env * generator * cnf * literal :=
  let '(E', g', cs, cout, lrs) := mk_env_full_adder E g lit_ff ls1 ls2 in
  (E', g', cs, cout).

Lemma mk_env_uaddo_is_bit_blast_uaddo :
  forall w E g  (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_uaddo E g ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_uaddo g ls1 ls2 = (g', cs, lrs).
Proof.
  move =>  w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_uaddo /bit_blast_uaddo.
  case Hmk: (mk_env_full_adder E g lit_ff ls1 ls2 ) => [[[[E'0 g'0] cs0] cout] lrs0].
  move : (mk_env_full_adder_is_bit_blast_full_adder Hmk) => Hbb.
  rewrite Hbb. move =>[] _ <- <- <-.
  done.
Qed.

Lemma mk_env_uaddo_newer_gen :
  forall w E g  (ls1 ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_uaddo E g ls1 ls2 = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move =>  w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_uaddo.
  case Hmk: (mk_env_full_adder E g lit_ff ls1 ls2) => [[[[E'0 g'0] cs0] cout] lrs0]. move => [] _ <- _ _.
  apply (mk_env_full_adder_newer_gen Hmk).
Qed.

Lemma mk_env_uaddo_newer_res :
  forall  w E g  (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_uaddo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g' lr.
Proof.
  move =>  w E g ls1 ls2 E' g' cs lr.
  rewrite /mk_env_uaddo.
  case Hmk: (mk_env_full_adder E g lit_ff ls1 ls2) => [[[[E'0 g'0] cs0] cout] lrs0].
  move => [] _ <- _ <- Hngtt.
  apply (mk_env_full_adder_newer_cout Hmk Hngtt).
Qed.

Lemma mk_env_uaddo_newer_cnf:
  forall  w E g  (ls1 ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_uaddo E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  move =>  w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_uaddo.
  case Hmk: (mk_env_full_adder E g lit_ff ls1 ls2) => [[[[E'0 g'0] cs0] cout] lrs0]. move => [] _ <- <- _.
  apply (mk_env_full_adder_newer_cnf Hmk).
Qed.

Lemma mk_env_uaddo_preserve :
  forall  w E g  (ls1 ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_uaddo E g ls1 ls2 = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move =>  w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_uaddo.  case Hmk: (mk_env_full_adder E g lit_ff ls1 ls2) => [[[[E'0 g'0] cs0] cout] lrs0]. move => [] <- _ _ _.
  apply (mk_env_full_adder_preserve Hmk).
Qed.

Lemma mk_env_uaddo_sat :
  forall  w E g  (ls1 ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_uaddo E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt -> newer_than_lits g ls1 ->  newer_than_lits g ls2 -> interp_cnf E' cs.
Proof.
  move =>  w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_uaddo.  case Hmk: (mk_env_full_adder E g lit_ff ls1 ls2) => [[[[E'0 g'0] cs0] cout] lrs0]. move => [] <- _ <- _.
  apply (mk_env_full_adder_sat Hmk).
Qed.
