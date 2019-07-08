From Coq Require Import ZArith List Decidable.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon BBUlt.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

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

Lemma bit_blast_usubo_correct :
  forall w g (bs1 bs2 : BITS w) E ls1 ls2 br g' cs lr,
    bit_blast_usubo g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    carry_subB bs1 bs2 = br ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr br.
Proof.
  move=> n g bs1 bs2 E ls1 ls2 br g' cs lrs.
  rewrite /bit_blast_usubo.
  case Hblast: (bit_blast_ult g ls1 ls2) => [[og ocs] olrs].
  case=> _ <- <- => Henc1 Henc2 <- Hcs.
  move: (bit_blast_ult_correct Hblast Henc1 Henc2 Hcs) => Henc.
  by rewrite -(ltB_carry_subB_rewrite bs1 bs2).
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
