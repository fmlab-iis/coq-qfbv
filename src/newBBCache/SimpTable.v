From Coq Require Import ZArith OrderedType Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import FMaps Var. 
From BitBlasting Require Import QFBV CNF State AdhereConform BBCommon.
From newBBCache Require Import CompTable.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition expm := ExpMap.t word.
Definition bexpm := BexpMap.t literal.

(* ==== A table storing literal(s), no CNFs ==== *)

Record simptable :=
  { et : expm;
    bt : bexpm }.

Definition find_et e t := ExpMap.find e (et t).
Definition find_bt e t := BexpMap.find e (bt t).

Definition add_et e ls t := 
  {| et := ExpMap.add e ls (et t);
     bt := bt t |}.
Definition add_bt e l t := 
  {| et := et t;
     bt := BexpMap.add e l (bt t) |}.

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

Definition compatible (st : simptable) (ct : comptable) :=
  compatible_et st ct /\ compatible_bt st ct.


