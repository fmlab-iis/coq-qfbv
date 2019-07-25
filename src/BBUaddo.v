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

Lemma Carry_addB_equiv_Uaddo w (bs1 bs2: BITS w):
  carry_addB bs1 bs2 <-> 2^w <= toNat bs1 + toNat bs2.
Proof.
  case HadcB : (adcB false bs1 bs2) => [carry add].
  Local Transparent adcB.
  rewrite /adcB in HadcB.
  rewrite /=.
  split.
  -
    move=> Hcarry.
    rewrite Hcarry in HadcB.
    have H: ((adcBmain false bs1 bs2) = joinmsb (true,add)) by rewrite -HadcB splitmsbK.
    move: (@toNat_adcBmain w false bs1 bs2) => HtoNat.
    rewrite -HtoNat H.
    rewrite toNat_joinmsb.
    rewrite mul1n.
    exact: leq_addr.
  - move: HadcB; case carry => HadcB.
     + done.
     +
       have H: ((adcBmain false bs1 bs2) = joinmsb (false,add)) by rewrite -HadcB splitmsbK.
       move: (@toNat_adcBmain w false bs1 bs2) => HtoNat.
       rewrite add0n in HtoNat.
       rewrite -HtoNat H.
       rewrite toNat_joinmsb.
       rewrite /= mul0n add0n.
       move=> Hcontra.
       move: (toNatBounded add) => Hbound.
       move: (leq_ltn_trans Hcontra Hbound) => Hno.
       by rewrite ltnn in Hno.
Qed.
(* ltn_neqAle*)
Lemma Uaddo_equiv_uaddo2 w (bs1 bs2: BITS w):
  2^w <= toNat bs1 + toNat bs2 <-> toNat (addB bs1 bs2) != toNat bs1 + toNat bs2.
Proof.
  split.
  - move=> Hle.
    rewrite toNat_addB.
    remember (toNat bs1 + toNat bs2) as sum.
    move: (nat.expn2_gt0 w) => H2w.
    move: (div.ltn_pmod sum H2w) => Hlt.
    move: (nat.ltn_leq_trans Hlt Hle).
    rewrite ltn_neqAle. by move/andP => [H _].
  - move=> Hneq.
    rewrite toNat_addB in Hneq.
    move/eqP: Hneq.
    have re_small: (forall m d: nat, ~ (div.modn m d = m ) -> (d <= m)).
    {
      intros.
      rewrite leqNgt.
      have: (~(m<d)).
      intro.
        by rewrite (div.modn_small H0) in H.
      by move/negP.
    }
    exact: re_small.
Qed.


Lemma bit_blast_uaddo_correct :
  forall w g (bs1 bs2 : BITS w) E ls1 ls2 g' cs lr,
    bit_blast_uaddo g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr ( toNat (addB bs1 bs2) != toNat bs1 + toNat bs2).
Proof.
  move=> n g bs1 bs2 E ls1 ls2 g' cs lr.
  rewrite /bit_blast_uaddo.
  case HadcB: (adcB false bs1 bs2) => [obcout obrs].
  case Hblast: (bit_blast_full_adder g lit_ff ls1 ls2) => [[[og ocs] olcout] olrs].
  case=> _ Hocs Holr => Henc1 Henc2 Hcs.
  have Hcarry: enc_bit E lr (carry_addB bs1 bs2).
  rewrite -Hocs in Hcs.
  rewrite -Holr.
  move: (add_prelude_enc_bit_ff Hcs) => Hff.
  move: (bit_blast_full_adder_correct2 Hblast Henc1 Henc2 Hff Hcs HadcB).
    by rewrite /(carry_addB bs1 bs2) HadcB.
    have -> : snd (obcout, obrs) = addB bs1 bs2.
    {
      by rewrite HadcB.
    }
    case H1: (carry_addB bs1 bs2);
      case H2: (toNat (addB bs1 bs2) != toNat bs1 + toNat bs2);
      rewrite H1 in Hcarry; try done.
    -
      apply Carry_addB_equiv_Uaddo in H1.
      apply Uaddo_equiv_uaddo2 in H1.
        by rewrite H1 in H2.
    -
      apply Uaddo_equiv_uaddo2 in H2.
      apply Carry_addB_equiv_Uaddo in H2.
        by rewrite H2 in H1.
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
