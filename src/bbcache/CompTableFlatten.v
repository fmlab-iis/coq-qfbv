From Coq Require Import ZArith OrderedType Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import FMaps Var Seqs.
From BitBlasting Require Import QFBV CNF State AdhereConform BBCommon.
From BBCache Require CompTable.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Module ExpMap := CompTable.ExpMap.
Module BexpMap := CompTable.BexpMap.

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



(* Convert comptable to CompTable.comptable *)

Definition tflatten_first {A : Type} (p : seq cnf * A) := (Seqs.tflatten p.1, p.2).

Definition expm_of_fexpm (m : expm) : CompTable.expm :=
  ExpMap.map tflatten_first m.

Definition bexpm_of_fbexpm (m : bexpm) : CompTable.bexpm :=
  BexpMap.map tflatten_first m.

Definition comptable_of_fcomptable (t : comptable) : CompTable.comptable :=
  CompTable.Build_comptable (expm_of_fexpm (et t))
                            (bexpm_of_fbexpm (bt t)).

Definition et_compatible (ft : expm) (t : CompTable.expm) :=
  forall e, ExpMap.mem e ft = ExpMap.mem e t /\
            (forall fcs flrs cs (lrs : seq literal),
                ExpMap.find e ft = Some (fcs, flrs) ->
                ExpMap.find e t = Some (cs, lrs) ->
                cnf_eqsat (tflatten fcs) cs /\
                cnf_eqnew (tflatten fcs) cs /\
                flrs = lrs).

Definition bt_compatible (ft : bexpm) (t : CompTable.bexpm) :=
  forall e, BexpMap.mem e ft = BexpMap.mem e t /\
            (forall fcs flr cs (lr : literal),
                BexpMap.find e ft = Some (fcs, flr) ->
                BexpMap.find e t = Some (cs, lr) ->
                cnf_eqsat (tflatten fcs) cs /\
                cnf_eqnew (tflatten fcs) cs /\
                flr = lr).

Definition comptable_compatible (fc : comptable) (c : CompTable.comptable) :=
  et_compatible (et fc) (CompTable.et c) /\
  bt_compatible (bt fc) (CompTable.bt c).

Lemma expm_of_fexpm_compatible m : et_compatible m (expm_of_fexpm m).
Proof.
  move=> e. split.
  - rewrite ExpMap.Lemmas.map_b. reflexivity.
  - move=> fcs flrs cs lrs Hff Hf.
    rewrite (ExpMap.Lemmas.find_some_map (f:=tflatten_first) Hff) in Hf.
    case: Hf => ? ?; subst. done.
Qed.

Lemma bexpm_of_fbexpm_compatible m : bt_compatible m (bexpm_of_fbexpm m).
Proof.
  move=> e. split.
  - rewrite BexpMap.Lemmas.map_b. reflexivity.
  - move=> fcs flrs cs lrs Hff Hf.
    rewrite (BexpMap.Lemmas.find_some_map (f:=tflatten_first) Hff) in Hf.
    case: Hf => ? ?; subst. done.
Qed.

Lemma comptable_of_fcomptable_compatible t :
  comptable_compatible t (comptable_of_fcomptable t).
Proof.
  split; [exact: expm_of_fexpm_compatible | exact: bexpm_of_fbexpm_compatible].
Qed.

Lemma et_compatible_empty : et_compatible (ExpMap.empty (seq cnf * word))
                                          (CompTable.ExpMap.empty (cnf * word)).
Proof. done. Qed.

Lemma bt_compatible_empty : bt_compatible (BexpMap.empty (seq cnf * literal))
                                          (CompTable.BexpMap.empty (cnf * literal)).
Proof. done. Qed.

Lemma et_compatible_add ft ct e ecs cs lrs :
  et_compatible ft ct ->
  cnf_eqsat (tflatten ecs) cs ->
  cnf_eqnew (tflatten ecs) cs ->
  et_compatible (ExpMap.add e (ecs, lrs) ft) (CompTable.ExpMap.add e (cs, lrs) ct).
Proof.
  move=> Hc Heqs Hewn f. case Hfe: (f == e).
  - rewrite !(ExpMap.Lemmas.mem_add_eq Hfe) !(ExpMap.Lemmas.find_add_eq Hfe).
    split; first reflexivity. move=> ? ? ? ? [] ? ? [] ? ?; subst.
    split; first assumption. split; first assumption. reflexivity.
  - move/negP: Hfe=> Hfe.
    rewrite !(ExpMap.Lemmas.mem_add_neq Hfe) !(ExpMap.Lemmas.find_add_neq Hfe).
    exact: (Hc f).
Qed.

Lemma bt_compatible_add ft ct e ecs cs lr :
  bt_compatible ft ct ->
  cnf_eqsat (tflatten ecs) cs ->
  cnf_eqnew (tflatten ecs) cs ->
  bt_compatible (BexpMap.add e (ecs, lr) ft) (CompTable.BexpMap.add e (cs, lr) ct).
Proof.
  move=> Hc Heqs Hewn f. case Hfe: (f == e).
  - rewrite !(BexpMap.Lemmas.mem_add_eq Hfe) !(BexpMap.Lemmas.find_add_eq Hfe).
    split; first reflexivity. move=> ? ? ? ? [] ? ? [] ? ?; subst.
    split; first assumption. split; first assumption. reflexivity.
  - move/negP: Hfe=> Hfe.
    rewrite !(BexpMap.Lemmas.mem_add_neq Hfe) !(BexpMap.Lemmas.find_add_neq Hfe).
    exact: (Hc f).
Qed.
