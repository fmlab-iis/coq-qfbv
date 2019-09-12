
From mathcomp Require Import ssreflect seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrdered Store.
From BitBlasting Require Import Var.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module ValueType <: HasDefaultTyp.
  Definition t := bits.
  Definition default : t := [::].
End ValueType.

Module State := RealizableTStoreAdapter UVarOrder ValueType.
