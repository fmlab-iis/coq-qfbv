
From Coq Require Import ZArith OrderedType Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import Var FMaps.
From BitBlasting Require Import QFBV CNF State AdhereConform BBCommon.
From BBCache Require Import QFBVHash CompTableFlatten.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Module HexpMap <: SsrFMap := FMaps.MakeTreeMap HexpOrder.
Module HbexpMap <: SsrFMap := FMaps.MakeTreeMap HbexpOrder.

Definition expm := HexpMap.t (seq cnf * word).
Definition bexpm := HbexpMap.t (seq cnf * literal).


(* == A table storing complete results, including CNF and literal(s) == *)

Record comptable :=
  { et : expm;
    bt : bexpm }.

Definition empty : comptable :=
  {| et := HexpMap.empty (seq cnf * word);
     bt := HbexpMap.empty (seq cnf * literal) |}.

Definition find_et e t := HexpMap.find e (et t).
Definition find_bt e t := HbexpMap.find e (bt t).


(* ==== modification ==== *)

Definition add_et e cs ls t :=
  {| et := HexpMap.add e (cs, ls) (et t);
     bt := bt t |}.

Definition add_bt e cs l t :=
  {| et := et t;
     bt := HbexpMap.add e (cs, l) (bt t) |}.

Lemma find_et_add_et_eq e cs ls t :
  find_et e (add_et e cs ls t) = Some (cs, ls).
Proof.
  rewrite /find_et /add_et /=. apply: HexpMap.Lemmas.find_add_eq.
  exact: eqxx.
Qed.

Lemma find_et_add_et_neq e1 e2 cs ls t :
  ~ e1 == e2 -> find_et e1 (add_et e2 cs ls t) = find_et e1 t.
Proof.
  rewrite /find_et /add_et /= => Hneq. apply: HexpMap.Lemmas.find_add_neq.
  assumption.
Qed.

Lemma find_et_add_bt e1 e2 cs l t :
  find_et e1 (add_bt e2 cs l t) = find_et e1 t.
Proof. done. Qed.

Lemma find_bt_add_et e1 e2 cs ls t :
  find_bt e1 (add_et e2 cs ls t) = find_bt e1 t.
Proof. done. Qed.

Lemma find_bt_add_bt_eq e cs l t :
  find_bt e (add_bt e cs l t) = Some (cs, l).
Proof.
  rewrite /find_bt /add_bt /=. apply: HbexpMap.Lemmas.find_add_eq.
  exact: eqxx.
Qed.

Lemma find_bt_add_bt_neq e1 e2 cs l t :
  ~ e1 == e2 -> find_bt e1 (add_bt e2 cs l t) = find_bt e1 t .
Proof.
  rewrite /find_bt /add_bt /= => Hneq. apply: HbexpMap.Lemmas.find_add_neq.
  assumption.
Qed.


(* Compatibility *)

Definition et_compatible (ht : expm) (ft : CompTableFlatten.expm) :=
  forall e, HexpMap.find (hash_exp e) ht = ExpMap.find e ft.

Definition bt_compatible (ht : bexpm) (ft : CompTableFlatten.bexpm) :=
  forall e, HbexpMap.find (hash_bexp e) ht = BexpMap.find e ft.

Definition comptable_compatible (hc : comptable) (fc : CompTableFlatten.comptable) :=
  et_compatible (et hc) (CompTableFlatten.et fc) /\
  bt_compatible (bt hc) (CompTableFlatten.bt fc).

Lemma et_compatible_empty : et_compatible (HexpMap.empty (seq cnf * word))
                                          (ExpMap.empty (seq cnf * word)).
Proof. done. Qed.

Lemma bt_compatible_empty : bt_compatible (HbexpMap.empty (seq cnf * literal))
                                          (BexpMap.empty (seq cnf * literal)).
Proof. done. Qed.

Lemma et_compatible_add ht ft e cs lrs :
  et_compatible ht ft ->
  et_compatible (HexpMap.add (hash_exp e) (cs, lrs) ht) (ExpMap.add e (cs, lrs) ft).
Proof.
  move=> Hc f. case Hfe: (f == e).
  - have Hhfe: (hash_exp f == hash_exp e) by rewrite (eqP Hfe) eqxx.
    rewrite (HexpMap.Lemmas.find_add_eq Hhfe) (ExpMap.Lemmas.find_add_eq Hfe).
    reflexivity.
  - move/negP: Hfe=> Hfe.
    have Hhfe: ~ (hash_exp f == hash_exp e).
    { move/eqP=> H; apply: Hfe. move: (hash_exp_inj H) => ->. exact: eqxx. }
    rewrite (HexpMap.Lemmas.find_add_neq Hhfe) (ExpMap.Lemmas.find_add_neq Hfe).
    exact: (Hc f).
Qed.

Lemma bt_compatible_add ht ft e cs lr :
  bt_compatible ht ft ->
  bt_compatible (HbexpMap.add (hash_bexp e) (cs, lr) ht) (BexpMap.add e (cs, lr) ft).
Proof.
  move=> Hc f. case Hfe: (f == e).
  - have Hhfe: (hash_bexp f == hash_bexp e) by rewrite (eqP Hfe) eqxx.
    rewrite (HbexpMap.Lemmas.find_add_eq Hhfe) (BexpMap.Lemmas.find_add_eq Hfe).
    reflexivity.
  - move/negP: Hfe=> Hfe.
    have Hhfe: ~ (hash_bexp f == hash_bexp e).
    { move/eqP=> H; apply: Hfe. move: (hash_bexp_inj H) => ->. exact: eqxx. }
    rewrite (HbexpMap.Lemmas.find_add_neq Hhfe) (BexpMap.Lemmas.find_add_neq Hfe).
    exact: (Hc f).
Qed.
