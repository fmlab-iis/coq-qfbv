
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_lneg ===== *)

Definition bit_blast_lneg g (a : literal) : generator * cnf * literal :=
  let (g', r) := gen g in
  let cs := [:: [:: r; a]; [:: neg_lit r; neg_lit a]] in
  (g', cs, r).

Definition mk_env_lneg E g (a : literal) : env * generator * cnf * literal :=
  let (g', r) := gen g in
  let E' := env_upd E (var_of_lit r) (~~interp_lit E a) in
  let cs := [:: [:: r; a]; [:: neg_lit r; neg_lit a]] in
  (E', g', cs, r).

Lemma bit_blast_lneg_correct :
  forall g (b : bool) E g' (l: literal) cs lr,
    bit_blast_lneg g l = (g', cs, lr) ->
    enc_bit E l b ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (~~b).
Proof.
  move => g b E g' l cs lr. rewrite /bit_blast_lneg.
  case => _ <- <- Henc. rewrite /enc_bit /=. rewrite !interp_lit_neg_lit.
  rewrite (eqP Henc). move /andP => [_ H]. move: H.
  by case (E g); case b.
Qed.

Lemma mk_env_lneg_is_bit_blast_lneg :
  forall E g (l : literal) E' g' cs lr,
    mk_env_lneg E g l = (E', g', cs, lr) ->
    bit_blast_lneg g l = (g', cs, lr).
Proof.
  rewrite /mk_env_lneg /bit_blast_lneg /=; intros; dcase_hyps; subst; reflexivity.
Qed.

Lemma mk_env_lneg_newer_gen :
  forall E g (l : literal) E' g' cs lr,
    mk_env_lneg E g l = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  move=> E g l E' g' cs lr. case=> _ <- _ _. exact: pos_leb_add_diag_r.
Qed.

Lemma mk_env_lneg_newer_res :
  forall E g (l : literal) E' g' cs lr,
    mk_env_lneg E g l = (E', g', cs, lr) ->
    newer_than_lit g' lr.
Proof.
  move=> E g l E' g' cs lr. case=> _ <- _ <-.
  exact: newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_lneg_newer_cnf :
  forall E g (l : literal) E' g' cs lr,
    mk_env_lneg E g l = (E', g', cs, lr) ->
    newer_than_lit g l ->
    newer_than_cnf g' cs.
Proof.
  move=> E g l E' g' cs lr. case=> _ <- <- _ Hnew_l /=.
  move: (newer_than_lit_add_r 1 Hnew_l) => {Hnew_l} Hnew_l.
  rewrite 1!newer_than_lit_neg Hnew_l.
  replace (g + 1)%positive with (var_of_lit (Pos g) + 1)%positive at 1 1
    by reflexivity.
  rewrite newer_than_lit_add_diag_r.
  replace (g + 1)%positive with (var_of_lit (Neg g) + 1)%positive by reflexivity.
  rewrite newer_than_lit_add_diag_r. done.
Qed.

Lemma mk_env_lneg_preserve :
  forall E g (l : literal) E' g' cs lr,
    mk_env_lneg E g l = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  move=> E g l E' g' cs lr. case=> <- _ _ _. exact: env_upd_eq_preserve.
Qed.

Lemma mk_env_lneg_sat :
  forall E g (l : literal) E' g' cs lr,
    mk_env_lneg E g l = (E', g', cs, lr) ->
    newer_than_lit g l ->
    interp_cnf E' cs.
Proof.
  move=> E g l E' g' cs lr. case=> <- _ <- Hlr /= Hnew.
  rewrite !interp_lit_neg_lit. rewrite env_upd_eq.
  rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hnew)).
  by case: (interp_lit E l).
Qed.
