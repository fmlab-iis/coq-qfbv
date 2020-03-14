From Coq Require Import ZArith OrderedType Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import FMaps Var. 
From BitBlasting Require Import QFBV CNF State BBCommon.
From newBBCache Require Import CompTable SimpTable CompCache.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ==== A cache with partial information in current tables ==== *)

Record cache :=
  { (* store historical results *)
    ht : comptable;
    (* store current results *)
    ct : simptable }.

Definition empty : cache :=
  {| ht := CompTable.empty;
     ct := SimpTable.empty |}.

Definition find_het e c := CompTable.find_et e (ht c).
Definition find_hbt e c := CompTable.find_bt e (ht c). 
Definition find_cet e c := SimpTable.find_et e (ct c). 
Definition find_cbt e c := SimpTable.find_bt e (ct c). 


(* ==== modification ==== *)

Definition add_het e cs ls c := 
  {| ht := CompTable.add_et e cs ls (ht c);
     ct := ct c |}.

Definition add_hbt e cs l c := 
  {| ht := CompTable.add_bt e cs l (ht c);
     ct := ct c |}.

Definition add_cet e ls c := 
  {| ht := ht c;
     ct := SimpTable.add_et e ls (ct c) |}.

Definition add_cbt e l c := 
  {| ht := ht c;
     ct := SimpTable.add_bt e l (ct c) |}.

Definition reset_ct (c : cache) :=
  {| ht := ht c;
     ct := SimpTable.empty |}.


(* ==== compatible ==== *)

Definition compatible (c1 : cache) (c2 : compcache) :=
  SimpTable.compatible (ct c1) (CompCache.ct c2) 
  /\ (ht c1) = (CompCache.ht c2).

Lemma compatible_find_het :
  forall c1 c2 e, compatible c1 c2 -> find_het e c1 = CompCache.find_het e c2.
Proof. 
  move=> c1 c2 e [Hct Hht] /=. rewrite /find_het Hht. done.
Qed.

Lemma compatible_find_hbt :
  forall c1 c2 e, compatible c1 c2 -> find_hbt e c1 = CompCache.find_hbt e c2.
Proof.
  move=> c1 c2 e [Hct Hht] /=. rewrite /find_hbt Hht. done.
Qed.

Lemma compatible_find_cet_some :
  forall c1 c2 e ls,
    compatible c1 c2 -> find_cet e c1 = Some ls 
    -> exists cs, CompCache.find_cet e c2 = Some (cs, ls).
Proof. 
  move=> c1 c2 e ls [Hct Hht] /=. exact: SimpTable.compatible_find_et_some.
Qed.

Lemma compatible_find_cet_none :
  forall c1 c2 e,
    compatible c1 c2 -> find_cet e c1 = None -> CompCache.find_cet e c2 = None.
Proof.
  move=> c1 c2 e [Hct Hht] /=. exact: SimpTable.compatible_find_et_none.
Qed.

Lemma compatible_find_cbt_some :
  forall c1 c2 e l,
    compatible c1 c2 -> find_cbt e c1 = Some l 
    -> exists cs, CompCache.find_cbt e c2 = Some (cs, l).
Proof.
  move=> c1 c2 e l [Hct Hht] /=. exact: SimpTable.compatible_find_bt_some.
Qed.

Lemma compatible_find_cbt_none :
  forall c1 c2 e,
    compatible c1 c2 -> find_cbt e c1 = None -> CompCache.find_cbt e c2 = None.
Proof.
  move=> c1 c2 e [Hct Hht] /=. exact: SimpTable.compatible_find_bt_none.
Qed.

Lemma compatible_add_het :
  forall c1 c2 e cs ls,
    compatible c1 c2 
    -> compatible (add_het e cs ls c1) (CompCache.add_het e cs ls c2).
Proof.
  move=> c1 c2 e cs ls [Hct Hht]. split; [ done | by rewrite /add_het Hht ].
Qed.

Lemma compatible_add_hbt :
  forall c1 c2 e cs l,
    compatible c1 c2 
    -> compatible (add_hbt e cs l c1) (CompCache.add_hbt e cs l c2).
Proof.
  move=> c1 c2 e cs l [Hct Hht]. split; [ done | by rewrite /add_hbt Hht ].
Qed.

Lemma compatible_add_cet :
  forall c1 c2 e cs ls,
    compatible c1 c2 -> compatible (add_cet e ls c1) (CompCache.add_cet e cs ls c2).
Proof.
  move=> c1 c2 e cs ls [Hct Hht]. 
  split; [ exact: SimpTable.compatible_add_et | done ].
Qed.

Lemma compatible_add_cbt :
  forall c1 c2 e cs l,
    compatible c1 c2 -> compatible (add_cbt e l c1) (CompCache.add_cbt e cs l c2).
Proof.
  move=> c1 c2 e cs ls [Hct Hht]. 
  split; [ exact: SimpTable.compatible_add_bt | done ].
Qed.

Lemma compatible_reset_ct :
  forall c1 c2, 
    compatible c1 c2 -> compatible (reset_ct c1) (CompCache.reset_ct c2).
Proof.
  move=> c1 c2 [Hct Hht]. split; done.
Qed.
