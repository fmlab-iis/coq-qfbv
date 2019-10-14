From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From BitBlasting Require Import QFBV CNF BBCommon.
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

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
  case=> _ <- <- Henc1 Henc2. rewrite /enc_bit /=.
  rewrite add_prelude_cons !add_prelude_singleton !interp_clause_cons.
  rewrite add_prelude_cons !add_prelude_singleton !interp_clause_cons.
  rewrite !interp_lit_neg_lit /=.
  rewrite (eqP Henc1) (eqP Henc2) => {Henc1 Henc2}.
  move=> Hand. split_andb_hyps.
  move: H2 H3 H4.
  by case: (E g); case: ib1; case: ib2.
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
Proof.
  move => E g l1 l2 E' g' cs lr. case => _ <- _ _. t_auto_newer.
Qed.

Lemma mk_env_disj_newer_res :
  forall E g (l1 l2: literal) E' g' cs lr,
    mk_env_disj E g l1 l2 = (E', g', cs, lr) ->
    newer_than_lit g' lr.
Proof.
  move => E g l1 l2 E' g' cs lr. case => _ <- _ <-.
  t_auto_newer.
Qed.

Lemma mk_env_disj_newer_cnf :
  forall E g (l1 l2: literal) E' g' cs lr,
    mk_env_disj E g l1 l2 = (E', g', cs, lr) ->
    newer_than_lit g l1 -> newer_than_lit g l2 ->
    newer_than_cnf g' cs.
Proof.
  move => E g l1 l2 E' g' cs lr. case => _ <- <- _ Hnew_l1 Hnew_l2 /=.
  split_andb_goal; t_auto_newer.
Qed.

Lemma mk_env_disj_preserve :
  forall E g (l1 l2 : literal) E' g' cs lr,
    mk_env_disj E g l1 l2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  move=> E g l1 l2 E' g' cs lr. case=> <- _ _ _. t_auto_preserve.
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
