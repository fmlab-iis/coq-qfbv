From Coq Require Import ZArith OrderedType Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import FMaps Var.
From BitBlasting Require Import QFBV CNF State BBCommon.
From BBCache Require Import CompTableFlatten SimpTable CompCache.

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
  {| ht := CompTableFlatten.empty;
     ct := SimpTable.empty |}.

Definition find_het e c := CompTableFlatten.find_et e (ht c).
Definition find_hbt e c := CompTableFlatten.find_bt e (ht c).
Definition find_cet e c := SimpTable.find_et e (ct c).
Definition find_cbt e c := SimpTable.find_bt e (ct c).


(* ==== modification ==== *)

Definition add_het e cs ls c :=
  {| ht := CompTableFlatten.add_et e cs ls (ht c);
     ct := ct c |}.

Definition add_hbt e cs l c :=
  {| ht := CompTableFlatten.add_bt e cs l (ht c);
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
