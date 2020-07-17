From Coq Require Import ZArith OrderedType Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import FMaps Var.
From BitBlasting Require Import QFBV CNF State BBCommon.
From BBCache Require Import QFBVHash CompTableHash SimpTableHash CompCache.

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
  {| ht := CompTableHash.empty;
     ct := SimpTableHash.empty |}.

Definition find_het e c := CompTableHash.find_et e (ht c).
Definition find_hbt e c := CompTableHash.find_bt e (ht c).
Definition find_cet e c := SimpTableHash.find_et e (ct c).
Definition find_cbt e c := SimpTableHash.find_bt e (ct c).


(* ==== modification ==== *)

Definition add_het e cs ls c :=
  {| ht := CompTableHash.add_et e cs ls (ht c);
     ct := ct c |}.

Definition add_hbt e cs l c :=
  {| ht := CompTableHash.add_bt e cs l (ht c);
     ct := ct c |}.

Definition add_cet e ls c :=
  {| ht := ht c;
     ct := SimpTableHash.add_et e ls (ct c) |}.

Definition add_cbt e l c :=
  {| ht := ht c;
     ct := SimpTableHash.add_bt e l (ct c) |}.

Definition reset_ct (c : cache) :=
  {| ht := ht c;
     ct := SimpTableHash.empty |}.
