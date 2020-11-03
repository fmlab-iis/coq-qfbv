From Coq Require Import ZArith OrderedType Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import FMaps Var.
From BitBlasting Require Import QFBV CNF State AdhereConform BBCommon.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Module ExpMap <: SsrFMap := FMaps.MakeTreeMap QFBV.ExpOrder.
Module BexpMap <: SsrFMap := FMaps.MakeTreeMap QFBV.BexpOrder.

Definition expm := ExpMap.t (seq cnf * word).
Definition bexpm := BexpMap.t (seq cnf * literal).


(* == A table storing complete results, including CNF and literal(s) == *)

Record comptable :=
  { et : expm;
    bt : bexpm }.

Definition empty : comptable :=
  {| et := ExpMap.empty (seq cnf * word);
     bt := BexpMap.empty (seq cnf * literal) |}.

Definition find_et e t := ExpMap.find e (et t).
Definition find_bt e t := BexpMap.find e (bt t).


(* ==== modification ==== *)

Definition add_et e cs ls t :=
  {| et := ExpMap.add e (cs, ls) (et t);
     bt := bt t |}.

Definition add_bt e cs l t :=
  {| et := et t;
     bt := BexpMap.add e (cs, l) (bt t) |}.

Lemma find_et_add_et_eq :
  forall e cs ls t, find_et e (add_et e cs ls t) = Some (cs, ls).
Proof.
  move=> e cs ls t. rewrite /find_et /add_et /=.
  by apply: ExpMap.Lemmas.find_add_eq.
Qed.

Lemma find_et_add_et_neq :
  forall e0 e cs ls t, ~ e0 == e -> find_et e0 (add_et e cs ls t) = find_et e0 t.
Proof.
  move=> e0 e cs ls t Hneq. by apply: ExpMap.Lemmas.find_add_neq.
Qed.

Lemma find_et_add_bt :
  forall e0 e cs l t, find_et e0 (add_bt e cs l t) = find_et e0 t.
Proof.
  move=> e0 e cs l t. done.
Qed.

Lemma find_bt_add_et :
  forall e0 e cs ls t, find_bt e0 (add_et e cs ls t) = find_bt e0 t.
Proof.
  move=> e0 e cs ls t. done.
Qed.

Lemma find_bt_add_bt_eq :
  forall e cs l t, find_bt e (add_bt e cs l t) = Some (cs, l).
Proof.
  move=> e cs l t. rewrite /find_bt /add_bt /=.
  by apply: BexpMap.Lemmas.find_add_eq.
Qed.

Lemma find_bt_add_bt_neq :
  forall e0 e cs l t, ~ e0 == e -> find_bt e0 (add_bt e cs l t) = find_bt e0 t .
Proof.
  move=> e0 e cs l t Hneq. by apply: BexpMap.Lemmas.find_add_neq.
Qed.
