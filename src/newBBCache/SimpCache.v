From Coq Require Import ZArith OrderedType Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import FMaps Var. 
From BitBlasting Require Import QFBV CNF State AdhereConform BBCommon.
From newBBCache Require Import CompTable SimpTable CompCache.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Module ExpMap <: SsrFMap := FMaps.MakeTreeMap QFBV.ExpOrder. *)
(* Module BexpMap <: SsrFMap := FMaps.MakeTreeMap QFBV.BexpOrder. *)

(* Definition cexpm := ExpMap.t (cnf * word). *)
(* Definition cbexpm := BexpMap.t (cnf * literal). *)
(* Definition hexpm := ExpMap.t (cnf * word). *)
(* Definition hbexpm := BexpMap.t (cnf * literal). *)

(* ==== A cache with partial information in current tables ==== *)

Record cache :=
  { (* store historical results *)
    ht : comptable;
    (* store current results *)
    ct : simptable }.

Definition find_het e c := CompTable.find_et e (ht c).
Definition find_hbt e c := CompTable.find_bt e (ht c). 
Definition find_cet e c := SimpTable.find_et e (ct c). 
Definition find_cbt e c := SimpTable.find_bt e (ct c). 

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
     ct := {| et := ExpMap.empty word;
              bt := BexpMap.empty literal |} |}.

Definition compatible_et (st : simptable) (ct : comptable) :=
  (forall e ls, find_et e st = Some ls 
                -> exists cs, CompTable.find_et e ct = Some (cs, ls))
  /\ forall e cs ls, CompTable.find_et e ct = Some (cs, ls) 
                     -> find_et e st = Some ls.

Definition compatible_bt (st : simptable) (ct : comptable) :=
  (forall e l, find_bt e st = Some l
               -> exists cs, CompTable.find_bt e ct = Some (cs, l))
  /\ forall e cs l, CompTable.find_bt e ct = Some (cs, l) 
                     -> find_bt e st = Some l.

Definition compatible (c1 : cache) (c2 : compcache) :=
  SimpTable.compatible (ct c1) (CompCache.ct c2) /\ (ht c1) = (CompCache.ht c2).


Lemma compatible_find_cet_some :
  forall c1 c2 e ls,
    compatible c1 c2 -> find_cet e c1 = Some ls 
    -> exists cs, CompCache.find_cet e c2 = Some (cs, ls).
Proof. Admitted.

Lemma compatible_find_cet_none :
  forall c1 c2 e,
    compatible c1 c2 -> find_cet e c1 = None -> CompCache.find_cet e c2 = None.
Proof. Admitted.

Lemma compatible_find_het :
  forall c1 c2 e, compatible c1 c2 -> find_het e c1 = CompCache.find_het e c2.
Proof. Admitted.

Lemma compatible_add_cet :
  forall c1 c2 e cs ls,
    compatible c1 c2 -> compatible (add_cet e ls c1) (CompCache.add_cet e cs ls c2).
Proof. Admitted.

Lemma compatible_add_het :
  forall c1 c2 e cs ls,
    compatible c1 c2 
    -> compatible (add_het e cs ls c1) (CompCache.add_het e cs ls c2).
Proof. Admitted.

Lemma compatible_find_cbt_some :
  forall c1 c2 e l,
    compatible c1 c2 -> find_cbt e c1 = Some l 
    -> exists cs, CompCache.find_cbt e c2 = Some (cs, l).
Proof. Admitted.

Lemma compatible_find_cbt_none :
  forall c1 c2 e,
    compatible c1 c2 -> find_cbt e c1 = None -> CompCache.find_cbt e c2 = None.
Proof. Admitted.

Lemma compatible_find_hbt :
  forall c1 c2 e, compatible c1 c2 -> find_hbt e c1 = CompCache.find_hbt e c2.
Proof. Admitted.

Lemma compatible_add_cbt :
  forall c1 c2 e cs l,
    compatible c1 c2 -> compatible (add_cbt e l c1) (CompCache.add_cbt e cs l c2).
Proof. Admitted.

Lemma compatible_add_hbt :
  forall c1 c2 e cs l,
    compatible c1 c2 
    -> compatible (add_hbt e cs l c1) (CompCache.add_hbt e cs l c2).
Proof. Admitted.


Lemma compatible_reset_ct :
  forall c cc, compatible c cc -> compatible (SimpCache.reset_ct c) (CompCache.reset_ct cc).
Proof. Admitted.


