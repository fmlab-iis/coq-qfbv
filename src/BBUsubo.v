From Coq Require Import ZArith List Decidable.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon BBUlt.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits extra.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== bit_blast_usubo ===== *)

Definition bit_blast_usubo w g (ls1 ls2: w.-tuple literal) : generator * cnf * literal :=
  bit_blast_ult g ls1 ls2 .

Definition mk_env_usubo w E g (ls1 ls2: w.-tuple literal) : env * generator * cnf * literal :=
  mk_env_ult E g ls1 ls2.

Lemma ltB_carry_subB:
  forall w (bs1 bs2: BITS w),
    ltB bs1 bs2 <->
    carry_subB bs1 bs2.
Proof.
  move => w bs1 bs2.
  split.
  +
    apply contrapositive.
    - case: (carry_subB bs1 bs2);  rewrite /Decidable.decidable. by left. by right.
    - move => Hinv_carry.
      move /negP /eqP /eqP: Hinv_carry.
      rewrite Bool.negb_true_iff => H.
      move: (sbbB_ltB_leB bs1 bs2).
      rewrite H /=.
      move=> HleB HltB.
      rewrite leBNlt in HleB.
      move /negP : HleB => HleB.
      rewrite HltB in HleB.
      done.
  +
    move=> Hcarry.
    move: (sbbB_ltB_leB bs1 bs2).
    by rewrite Hcarry.
Qed.

Lemma ltB_carry_subB_rewrite:
  forall w (bs1 bs2: BITS w),
    ltB bs1 bs2 =
    carry_subB bs1 bs2.
Proof.
  move=> w bs1 bs2.
  case Hlt: (ltB bs1 bs2); case Hcarry: (carry_subB bs1 bs2); try done.
  - apply ltB_carry_subB in Hlt. by rewrite Hlt in Hcarry.
  - apply ltB_carry_subB in Hcarry. by rewrite Hcarry in Hlt.
Qed.

Lemma carry_subB_equiv_usubo w (bs1 bs2: BITS w):
  carry_subB bs1 bs2 <-> toNat (subB bs1 bs2) != toNat bs1 - toNat bs2.
Proof.
  split.
  -
    move=> Hlt.
    move: (Hlt).
    apply ltB_carry_subB in Hlt.
    rewrite /(carry_subB bs1 bs2).
    case HsbbB: (sbbB false bs1 bs2) => [overflow sub].
    have HsubB: (subB bs1 bs2) = sub by rewrite HsbbB.
    move=> oveflow.
    rewrite /=.
    rewrite -HsubB.
    rewrite subB_equiv_addB_negB.
    rewrite toNat_addB.
    rewrite toNat_negB.
    case Heq: (toNat bs2 == 0).
    + move/eqP: Heq => Heq.
      rewrite ltB_nat in Hlt.
      rewrite Heq in Hlt.
      by rewrite ltn0 in Hlt.
    + rewrite addnBA.
      rewrite addnC.
      have Hsmall: (2^w + toNat bs1 - toNat bs2 < 2^w).
      {

        rewrite -(ltn_add2r (toNat bs2)). rewrite subnK.
        rewrite ltn_add2l.
        by rewrite -ltB_nat.
        assert (H: 2^w <= 2^w + toNat bs1) by apply leq_addr.
        apply: leq_trans H.
        move: (@toNatBounded w bs2) => tmp.
        exact: (ltnW tmp).
      }
      rewrite ltB_nat in Hlt.
      move: (ltnW Hlt) => Hle.
      rewrite -subn_eq0 in Hle.
      move/eqP:Hle => ->.
      assert (toNat bs1 - toNat bs2 < 2^w).
      assert (H := leq_subr (toNat bs2) (toNat bs1)).
      apply: leq_ltn_trans.  apply H. exact:toNatBounded.
      move: (div.modn_small Hsmall) => Hdiv_small.
      rewrite Hdiv_small.
      have Hgt: 2^w + toNat bs1 - toNat bs2 > 0.
      rewrite ltn_subRL.
      rewrite addn0.
      apply ltn_addr.
      exact: (toNatBounded bs2).
      rewrite ltn_neqAle in Hgt.
      move/andP: Hgt => [Hneq _].
      rewrite Bools.neq_sym in Hneq.
      exact: Hneq.
      apply: ltnW. exact: toNatBounded.
  - move: (@toNat_subB_bounded w bs1 bs2) => Hbound.
    case Hc1: (toNat (bs1 - bs2) != toNat bs1 - toNat bs2);
      case Hc2: (carry_subB bs1 bs2); try done.
    move/eqP: Hc2.
    rewrite eqbF_neg.
    move=> Hc2.
    apply Hbound in Hc2.
    move/eqP: Hc1.
    by rewrite Hc2.
Qed.

Lemma bit_blast_usubo_correct :
  forall w g (bs1 bs2 : BITS w) E ls1 ls2 g' cs lr,
    bit_blast_usubo g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (toNat (bs1 - bs2) != toNat bs1 - toNat bs2).
Proof.
  move=> n g bs1 bs2 E ls1 ls2 g' cs lr.
  rewrite /bit_blast_usubo.
  case Hblast: (bit_blast_ult g ls1 ls2) => [[og ocs] olrs].
  case=> _ <- Hlr => Henc1 Henc2 Hcs.
  have Hcarry: enc_bit E lr (carry_subB bs1 bs2).
  rewrite -Hlr.
  move: (bit_blast_ult_correct Hblast Henc1 Henc2 Hcs) => Henc.
    by rewrite -(ltB_carry_subB_rewrite bs1 bs2).

  case H1: (carry_subB bs1 bs2);
      case H2: (toNat (bs1 - bs2) != toNat bs1 - toNat bs2);
      rewrite H1 in Hcarry; try done.
  -
    apply carry_subB_equiv_usubo in H1.
      by rewrite H1 in H2.
  -
    apply carry_subB_equiv_usubo in H2.
      by rewrite H2 in H1.
Qed.

Lemma mk_env_usubo_is_bit_blast_usubo :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_usubo E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_usubo g ls1 ls2 = (g', cs, lr).
Proof.
  exact: (mk_env_ult_is_bit_blast_ult).
Qed.

Lemma mk_env_usubo_newer_gen :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_usubo E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  exact: (mk_env_ult_newer_gen).
Qed.

Lemma mk_env_usubo_newer_res :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_usubo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g' lr.
Proof.
  exact: (mk_env_ult_newer_res).
Qed.


Lemma mk_env_usubo_newer_cnf :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_usubo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  exact: (mk_env_ult_newer_cnf).
Qed.

Lemma mk_env_usubo_preserve :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_usubo E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  exact: (mk_env_ult_preserve).
Qed.

Lemma mk_env_usubo_sat :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_usubo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  exact: (mk_env_ult_sat).
Qed.
