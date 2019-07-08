
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_disj ===== *)

Definition bit_blast_disj g (l1 l2: literal) : generator * cnf * literal :=
  let (g', r) := gen g in
  let cs := [:: [:: neg_lit r; l1; l2]; [:: r; neg_lit l1]; [:: r; neg_lit l2]]
  in (g', cs, r).

Definition mk_env_disj E g (l1 l2 : literal) : env * generator * cnf * literal :=
  let (g', r) := gen g in
  let E' := env_upd E (var_of_lit r) (interp_lit E l1 || interp_lit E l2) in
  let cs := [:: [:: neg_lit r; l1; l2]; [:: r; neg_lit l1]; [:: r; neg_lit l2]] in
  (E', g', cs, r).

Lemma bit_blast_disj_correct :
  forall g b1 b2 E g' l1 l2 cs lr,
    bit_blast_disj g l1 l2 = (g', cs, lr) ->
    enc_bit E l1 b1 ->
    enc_bit E l2 b2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (b1 || b2).
Proof.
  move => g ib1 ib2 E g' il1 il2 cs olr.
  rewrite /bit_blast_disj.
  case.
  set r := Pos g.
  move => Hg <- <-.
  rewrite add_prelude_cons !add_prelude_singleton /=.
  rewrite !interp_lit_neg_lit.
  move => Henc1 Henc2 Hcnf.
  move/andP: Hcnf => [Htt Hcnf].
  move/andP: Htt => [Htt Hcnf1].
  move/andP : Hcnf => [_ Hcnf2].
  move/andP : Hcnf2 => [Hcnfil1 Hcnfil2].
  case Heg: (E g).
  - rewrite Heg in Hcnf1; simpl in Hcnf1.
    case Hl1 : (interp_lit E il1).
    + rewrite /enc_bit Hl1 in Henc1.
      move/eqP : Henc1 => Henc1; by rewrite -Henc1/enc_bit/=Heg.
    + rewrite Hl1 orFb in Hcnf1; rewrite /enc_bit Hcnf1 in Henc2.
      move/eqP : Henc2 => Henc2. by rewrite /enc_bit-Henc2/=Heg orbT.
  - rewrite Heg in Hcnfil1, Hcnfil2; simpl in Hcnfil1, Hcnfil2.
    move/eqP/eqP : Hcnfil1 => Hl1; symmetry in Hl1; apply Bool.negb_sym in Hl1.
    move/eqP/eqP : Hcnfil2 => Hl2; symmetry in Hl2; apply Bool.negb_sym in Hl2.
    rewrite /enc_bit in Henc1, Henc2; rewrite Hl1 in Henc1; rewrite Hl2 in Henc2.
    move/eqP : Henc1 => Henc1; symmetry; rewrite -Henc1 orFb.
    move/eqP : Henc2 => Henc2. symmetry; by rewrite /enc_bit/= -Henc2 Heg.
Qed.

Lemma mk_env_disj_is_bit_blast_disj :
  forall E g (l1 l2: literal) E' g' cs lr,
    mk_env_disj E g l1 l2 = (E', g', cs, lr) ->
    bit_blast_disj g l1 l2 = (g', cs, lr).
Proof.
  rewrite /mk_env_disj /bit_blast_disj /=; intros; dcase_hyps; subst; reflexivity.
Qed.

Lemma mk_env_disj_newer_gen :
  forall E g (l1 l2: literal) E' g' cs lr,
    mk_env_disj E g l1 l2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof. move => E g l1 l2 E' g' cs lr. case => _ <- _ _. exact: pos_leb_add_diag_r.
Qed.

Lemma mk_env_disj_newer_res :
  forall E g (l1 l2: literal) E' g' cs lr,
    mk_env_disj E g l1 l2 = (E', g', cs, lr) ->
    newer_than_lit g' lr.
Proof.
  move => E g l1 l2 E' g' cs lr. case => _ <- _ <-.
  exact : newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_disj_newer_cnf :
  forall E g (l1 l2: literal) E' g' cs lr,
    mk_env_disj E g l1 l2 = (E', g', cs, lr) ->
    newer_than_lit g l1 -> newer_than_lit g l2 ->
    newer_than_cnf g' cs.
Proof.
  move => E g l1 l2 E' g' cs lr. case => _ <- <- _ Hnew_l1 Hnew_l2 /=.
  move : (newer_than_lit_add_r 1 Hnew_l1) => {Hnew_l1} Hnew_l1;
  move : (newer_than_lit_add_r 1 Hnew_l2) => {Hnew_l2} Hnew_l2.
  rewrite 2!newer_than_lit_neg Hnew_l1 Hnew_l2.
  replace (g + 1)%positive with (var_of_lit (Neg g) + 1)%positive at 1 2
    by reflexivity.
  rewrite newer_than_lit_add_diag_r.
  replace (g + 1)%positive with (var_of_lit (Pos g) + 1)%positive by reflexivity.
  rewrite newer_than_lit_add_diag_r. done.
Qed.

Lemma mk_env_disj_preserve :
  forall E g (l1 l2 : literal) E' g' cs lr,
    mk_env_disj E g l1 l2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  move=> E g l1 l2 E' g' cs lr. case=> <- _ _ _. exact: env_upd_eq_preserve.
Qed.

Lemma mk_env_disj_sat :
  forall E g (l1 l2 : literal) E' g' cs lr,
    mk_env_disj E g l1 l2 = (E', g', cs, lr) ->
    newer_than_lit g l1 -> newer_than_lit g l2 ->
    interp_cnf E' cs.
Proof.
  move=> E g l1 l2 E' g' cs lr. case=> <- _ <- Hlr /= Hnew1 Hnew2.
  rewrite !interp_lit_neg_lit. rewrite env_upd_eq.
  rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hnew1)).
  rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hnew2)).
  by case: (interp_lit E l1); case: (interp_lit E l2).
Qed.
