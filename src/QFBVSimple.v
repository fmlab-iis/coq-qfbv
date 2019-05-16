
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
From Bits Require Export bits.
From ssrlib Require Import Var Store SsrOrdered.


Module Type Arch.
  Parameter wordsize : nat.
  Parameter wordsize_positive : wordsize > 0.
End Arch.

Module Make (V : SsrOrderedType) (A : Arch).

  Local Notation wordsize := A.wordsize.
  Local Notation var := V.t.

  Inductive exp : nat -> Type :=
  | bvVar : var -> exp wordsize
  | bvConst : forall w, BITS w -> exp w.

  Inductive bexp : Type :=
  | bvFalse : bexp
  | bvTrue : bexp
  | bvEq : forall w, exp w -> exp w -> bexp
  | bvConj : bexp -> bexp -> bexp.

  Module ValueType <: Equalities.Typ.
    Definition t : Set := BITS wordsize.
  End ValueType.

  Module State := TStoreAdapter V ValueType.

  Local Notation state := State.t.

  Fixpoint eval_exp {w} (e : exp w) (s : state) {struct e} : BITS w :=
    match e with
    | bvVar v => State.acc v s
    | bvConst _ n => n
    end.

  Fixpoint eval_bexp (e : bexp) (s : state) : Prop :=
    match e with
    | bvFalse => False
    | bvTrue => True
    | bvEq _ e1 e2 => eval_exp e1 s = eval_exp e2 s
    | bvConj e1 e2 => eval_bexp e1 s /\ eval_bexp e2 s
    end.

  Definition valid (e : bexp) : Prop :=
    forall s, eval_bexp e s.

End Make.
