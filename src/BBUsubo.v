From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon BBNot BBAdd BBSub.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== bit_blast_usubo ===== *)

Definition bit_blast_usubo w g (ls1 ls2: w.-tuple literal) : generator * cnf * literal :=
  let '(g_sbb, cs_sbb, l_bout, lr_sbb) := bit_blast_sbb g lit_ff ls1 ls2 in
  (g_sbb, cs_sbb, l_bout).

Definition mk_env_usubo w E g (ls1 ls2: w.-tuple literal) : env * generator * cnf * literal :=
  let '(E_sbb, g_sbb, cs_sbb, l_bout, lr_sbb) := mk_env_sbb E g lit_ff ls1 ls2 in
  (E_sbb, g_sbb, cs_sbb, l_bout).


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
  rewrite /bit_blast_usubo. case HsbbB: (sbbB false bs1 bs2) => [obcout obrs].
  case Hblast: (bit_blast_sbb g lit_ff ls1 ls2) => [[[og ocs] olcout] olrs].
  case=> _ <- <- => Henc1 Henc2 <- Hcs.
  move: (add_prelude_enc_bit_ff Hcs) => Hencff.
  move: (bit_blast_sbb_correct Hblast Hencff Henc1 Henc2 Hcs HsbbB) => [H _].
  done.
Qed.

Lemma mk_env_usubo_is_bit_blast_usubo :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_usubo E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_usubo g ls1 ls2 = (g', cs, lr).
Proof.
  move=> w E g ls1 ls2 E' g' cs lr.
  rewrite /mk_env_usubo /bit_blast_usubo.
  case Henv_sbb: (mk_env_sbb E g lit_ff ls1 ls2) => [[[[E_sbb g_sbb] cs_sbb] l_bout] lr_sbb].
  case => _ <- <- <-.
  dcase_goal.
  move: (mk_env_sbb_is_bit_blast_sbb Henv_sbb).
  by rewrite H; case => <- <- <- _.
Qed.

Lemma mk_env_usubo_newer_gen :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_usubo E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_usubo.
  dcase (mk_env_sbb E g lit_ff ls1 ls2) => [[[[[E_sbb g_sbb] cs_sbb] l_bout] lrs_sbb] Henv_sbb].
  case=> _ <- _ _.
  exact: (mk_env_sbb_newer_gen Henv_sbb).
Qed.

Lemma mk_env_usubo_newer_res :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_usubo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g' lr.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_usubo.
  dcase (mk_env_sbb E g lit_ff ls1 ls2) => [[[[[E_sbb g_sbb] cs_sbb] l_bout] lrs_sbb] Henv_sbb].
  case=> _ <- _ <- Hgtt.
  exact: (mk_env_sbb_newer_bout Henv_sbb Hgtt).
Qed.


Lemma mk_env_usubo_newer_cnf :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_usubo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_usubo.
  dcase (mk_env_sbb E g lit_ff ls1 ls2) => [[[[[E_sbb g_sbb] cs_sbb] l_bout] lrs_sbb] Henv_sbb].
  case=> _ <- <- _. move=> Hnew_gtt Hnew_gls1 Hnew_gls2.
  exact: (mk_env_sbb_newer_cnf Henv_sbb Hnew_gtt Hnew_gls1 Hnew_gls2).
Qed.

Lemma mk_env_usubo_preserve :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_usubo E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_usubo.
  dcase (mk_env_sbb E g lit_ff ls1 ls2) => [[[[[E_sbb g_sbb] cs_sbb] l_bout] lrs_sbb] Henv_sbb].
  case=> <- _ _ _.
  exact: (mk_env_sbb_preserve Henv_sbb).
Qed.

Lemma mk_env_usubo_sat :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_usubo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_usubo.
  dcase (mk_env_sbb E g lit_ff ls1 ls2) => [[[[[E_sbb g_sbb] cs_sbb] l_bout] lrs_sbb] Henv_sbb].
  case=> <- _ <- _. move=> Hnew_gtt Hnew_gls1 Hnew_gls2.
  exact: (mk_env_sbb_sat Henv_sbb Hnew_gtt Hnew_gls1 Hnew_gls2).
Qed.
