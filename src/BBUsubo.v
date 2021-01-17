From Coq Require Import ZArith List Decidable.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From BitBlasting Require Import QFBV CNF BBCommon BBUlt.
From ssrlib Require Import ZAriths Tactics Bools Seqs.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== bit_blast_usubo ===== *)

Definition bit_blast_usubo g ls1 ls2 : generator * cnf * literal :=
  bit_blast_ult g ls1 ls2 .

Definition mk_env_usubo E g ls1 ls2 : env * generator * cnf * literal :=
  mk_env_ult E g ls1 ls2.

(*
Lemma ltB_borrow_subB bs1 bs2:
    ltB bs1 bs2 <->
    borrow_subB bs1 bs2.
Proof.
  split.
  +
    apply contrapositive.
    - case: (borrow_subB bs1 bs2);  rewrite /Decidable.decidable. by left. by right.
    - move => Hinv_carry.
      move /negP /eqP /eqP: Hinv_carry.
      rewrite Bool.negb_true_iff => H.
      move: (sbbB_ltB_leB bs1 bs2).
      rewrite /borrow_subB in H.
      rewrite H /=.
      move=> HleB HltB.
      rewrite leBNlt in HleB.
      move /negP : HleB => HleB.
      rewrite HltB in HleB.
      done.
  +
    move=> Hcarry.
    move: (sbbB_ltB_leB bs1 bs2).
    rewrite /borrow_subB in Hcarry.
    by rewrite Hcarry.
Qed.

Lemma ltB_borrow_subB_rewrite bs1 bs2:
    ltB bs1 bs2 =
    borrow_subB bs1 bs2.
Proof.
  case Hlt: (ltB bs1 bs2); case Hcarry: (borrow_subB bs1 bs2); try done.
  - apply ltB_borrow_subB in Hlt. by rewrite Hlt in Hcarry.
  - apply ltB_borrow_subB in Hcarry. by rewrite Hcarry in Hlt.
Qed.
*)

Lemma bit_blast_usubo_correct g bs1 bs2 E ls1 ls2 g' cs lr :
    bit_blast_usubo g ls1 ls2 = (g', cs, lr) ->
    size ls1 == size ls2 ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (borrow_subB bs1 bs2).
Proof.
  rewrite /bit_blast_usubo.
  case Hblast: (bit_blast_ult g ls1 ls2) => [[og ocs] olrs].
  case=> _ <- Hlr => /eqP Hsize Henc1 Henc2 Hcs.
  rewrite -Hlr.
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2) in Hsize.
  rewrite -(ltB_equiv_borrow_subB Hsize).
  exact: (bit_blast_ult_correct Hblast Henc1 Henc2 Hcs).
Qed.

Lemma mk_env_usubo_is_bit_blast_usubo E g ls1 ls2 E' g' cs lr :
    mk_env_usubo E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_usubo g ls1 ls2 = (g', cs, lr).
Proof.
  exact: (mk_env_ult_is_bit_blast_ult).
Qed.

Lemma mk_env_usubo_newer_gen E g ls1 ls2 E' g' cs lr :
    mk_env_usubo E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  exact: (mk_env_ult_newer_gen).
Qed.

Lemma mk_env_usubo_newer_res E g ls1 ls2 E' g' cs lr :
    mk_env_usubo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g' lr.
Proof.
  exact: (mk_env_ult_newer_res).
Qed.


Lemma mk_env_usubo_newer_cnf E g ls1 ls2 E' g' cs lr :
    mk_env_usubo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  exact: (mk_env_ult_newer_cnf).
Qed.

Lemma mk_env_usubo_preserve E g ls1 ls2 E' g' cs lr :
    mk_env_usubo E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  exact: (mk_env_ult_preserve).
Qed.

Lemma mk_env_usubo_sat E g ls1 ls2 E' g' cs lr :
    mk_env_usubo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  exact: (mk_env_ult_sat).
Qed.

Lemma mk_env_usubo_env_equal E1 E2 g ls1 ls2 E1' E2' g1' g2' cs1 cs2 lr1 lr2 :
  env_equal E1 E2 ->
  mk_env_usubo E1 g ls1 ls2 = (E1', g1', cs1, lr1) ->
  mk_env_usubo E2 g ls1 ls2 = (E2', g2', cs2, lr2) ->
  env_equal E1' E2' /\ g1' = g2' /\ cs1 = cs2 /\ lr1 = lr2.
Proof.
  rewrite /mk_env_usubo => Heq.
  dcase (mk_env_ult E1 g ls1 ls2) => [[[[E_ult1 g_ult1] cs_ult1] lrs_ult1] Hult1].
  dcase (mk_env_ult E2 g ls1 ls2) => [[[[E_ult2 g_ult2] cs_ult2] lrs_ult2] Hult2].
  move: (mk_env_ult_env_equal Heq Hult1 Hult2) => {Heq Hult1 Hult2} [Heq [? [? ?]]]; subst.
  case=> ? ? ? ?; case=> ? ? ? ?; subst. done.
Qed.
