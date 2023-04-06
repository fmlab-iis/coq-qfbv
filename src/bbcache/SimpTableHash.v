From Coq Require Import ZArith OrderedType Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import EqFMaps EqVar.
From BitBlasting Require Import QFBV CNF State BBCommon.
From BBCache Require Import CompTableHash.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Definition expm := HexpMap.t word.
Definition bexpm := HbexpMap.t literal.


(* ==== A table storing only literal(s), no CNFs ==== *)

Record simptable :=
  { et : expm;
    bt : bexpm }.

Definition empty : simptable :=
  {| et := HexpMap.empty word;
     bt := HbexpMap.empty literal |}.

Definition find_et e t := HexpMap.find e (et t).
Definition find_bt e t := HbexpMap.find e (bt t).


(* ==== modification ==== *)

Definition add_et e ls t :=
  {| et := HexpMap.add e ls (et t);
     bt := bt t |}.

Definition add_bt e l t :=
  {| et := et t;
     bt := HbexpMap.add e l (bt t) |}.

Lemma find_et_add_et_eq :
  forall e ls t, find_et e (add_et e ls t) = Some ls.
Proof.
  move=> e ls t. by apply: HexpMap.Lemmas.find_add_eq.
Qed.

Lemma find_et_add_et_neq :
  forall e0 e ls t, ~ e0 == e -> find_et e0 (add_et e ls t) = find_et e0 t.
Proof.
  move=> e0 e ls t Hneq. by apply: HexpMap.Lemmas.find_add_neq.
Qed.

Lemma find_et_add_bt :
  forall e0 e l t, find_et e0 (add_bt e l t) = find_et e0 t.
Proof.
  move=> e0 e l t. done.
Qed.

Lemma find_bt_add_et :
  forall e0 e ls t, find_bt e0 (add_et e ls t) = find_bt e0 t.
Proof.
  move=> e0 e ls t. done.
Qed.

Lemma find_bt_add_bt_eq :
  forall e l t, find_bt e (add_bt e l t) = Some l.
Proof.
  move=> e l t. by apply: HbexpMap.Lemmas.find_add_eq.
Qed.

Lemma find_bt_add_bt_neq :
  forall e0 e l t, ~ e0 == e -> find_bt e0 (add_bt e l t) = find_bt e0 t .
Proof.
  move=> e0 e l t Hneq. by apply: HbexpMap.Lemmas.find_add_neq.
Qed.


(* ==== compatible ==== *)

Definition compatible_et (st : simptable) (ct : comptable) :=
  (forall e ls, find_et e st = Some ls
                -> exists cs, CompTableHash.find_et e ct = Some (cs, ls))
  /\ forall e cs ls, CompTableHash.find_et e ct = Some (cs, ls)
                     -> find_et e st = Some ls.

Definition compatible_bt (st : simptable) (ct : comptable) :=
  (forall e l, find_bt e st = Some l
               -> exists cs, CompTableHash.find_bt e ct = Some (cs, l))
  /\ forall e cs l, CompTableHash.find_bt e ct = Some (cs, l)
                     -> find_bt e st = Some l.

Definition compatible (st : simptable) (ct : comptable) :=
  compatible_et st ct /\ compatible_bt st ct.

Lemma compatible_find_et_some :
  forall t1 t2 e ls,
    compatible t1 t2 -> find_et e t1 = Some ls
    -> exists cs, CompTableHash.find_et e t2 = Some (cs, ls).
Proof.
  move=> t1 t2 e ls [[Ht1t2 Ht2t1] _]. exact: Ht1t2.
Qed.

Lemma compatible_find_et_none :
  forall t1 t2 e,
    compatible t1 t2 -> find_et e t1 = None -> CompTableHash.find_et e t2 = None.
Proof.
  move=> t1 t2 e [[Ht1t2 Ht2t1] _] Hft1.
  case Hft2 : (CompTableHash.find_et e t2) => [[cs ls] | ].
  - rewrite (Ht2t1 _ _ _ Hft2) in Hft1. discriminate.
  - done.
Qed.

Lemma compatible_find_bt_some :
  forall t1 t2 e l,
    compatible t1 t2 -> find_bt e t1 = Some l
    -> exists cs, CompTableHash.find_bt e t2 = Some (cs, l).
Proof.
  move=> t1 t2 e l [_ [Ht1t2 Ht2t1]]. exact: Ht1t2.
Qed.

Lemma compatible_find_bt_none :
  forall t1 t2 e,
    compatible t1 t2 -> find_bt e t1 = None -> CompTableHash.find_bt e t2 = None.
Proof.
  move=> t1 t2 e [_ [Ht1t2 Ht2t1]] Hft1.
  case Hft2 : (CompTableHash.find_bt e t2) => [[cs l] | ].
  - rewrite (Ht2t1 _ _ _ Hft2) in Hft1. discriminate.
  - done.
Qed.

Lemma compatible_add_et :
  forall t1 t2 e cs ls,
    compatible t1 t2 -> compatible (add_et e ls t1) (CompTableHash.add_et e cs ls t2).
Proof.
  move=> t1 t2 e cs ls [[Het1t2 Het2t1] [Hbt1t2 Hbt2t1]]. split; split.
  - move=> e0 ls0. case Heq : (e0 == e).
    + move/eqP: Heq => <-. rewrite find_et_add_et_eq CompTableHash.find_et_add_et_eq.
      case=> ->. exists cs. done.
    + move/negP: Heq => Hneq. rewrite (find_et_add_et_neq _ _ Hneq).
      rewrite (CompTableHash.find_et_add_et_neq _ _ _ Hneq). exact: Het1t2.
  - move=> e0 cs0 ls0. case Heq : (e0 == e).
    + move/eqP: Heq => <-. rewrite find_et_add_et_eq CompTableHash.find_et_add_et_eq.
      case=> _ ->. done.
    + move/negP: Heq => Hneq. rewrite (find_et_add_et_neq _ _ Hneq).
      rewrite (CompTableHash.find_et_add_et_neq _ _ _ Hneq). exact: Het2t1.
  - move=> e0 l0. rewrite find_bt_add_et CompTableHash.find_bt_add_et. exact: Hbt1t2.
  - move=> e0 cs0 l0. rewrite find_bt_add_et CompTableHash.find_bt_add_et. exact: Hbt2t1.
Qed.

Lemma compatible_add_bt :
  forall t1 t2 e cs l,
    compatible t1 t2 -> compatible (add_bt e l t1) (CompTableHash.add_bt e cs l t2).
Proof.
  move=> t1 t2 e cs l [[Het1t2 Het2t1] [Hbt1t2 Hbt2t1]]. split; split.
  - move=> e0 ls0. rewrite find_et_add_bt CompTableHash.find_et_add_bt. exact: Het1t2.
  - move=> e0 cs0 ls0.
    rewrite find_et_add_bt CompTableHash.find_et_add_bt. exact: Het2t1.
  - move=> e0 l0. case Heq : (e0 == e).
    + move/eqP: Heq => <-. rewrite find_bt_add_bt_eq CompTableHash.find_bt_add_bt_eq.
      case=> ->. exists cs. done.
    + move/negP: Heq => Hneq. rewrite (find_bt_add_bt_neq _ _ Hneq).
      rewrite (CompTableHash.find_bt_add_bt_neq _ _ _ Hneq). exact: Hbt1t2.
  - move=> e0 cs0 l0. case Heq : (e0 == e).
    + move/eqP: Heq => <-. rewrite find_bt_add_bt_eq CompTableHash.find_bt_add_bt_eq.
      case=> _ ->. done.
    + move/negP: Heq => Hneq. rewrite (find_bt_add_bt_neq _ _ Hneq).
      rewrite (CompTableHash.find_bt_add_bt_neq _ _ _ Hneq). exact: Hbt2t1.
Qed.
