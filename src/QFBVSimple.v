
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype tuple.
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
  | bvConst : forall w, BITS w -> exp w
  | bvNot : forall w, exp w -> exp w
  | bvAnd : forall w, exp w -> exp w -> exp w
  | bvOr : forall w, exp w -> exp w -> exp w
  | bvXor : forall w, exp w -> exp w -> exp w
  | bvNeg : forall w, exp w -> exp w
  | bvAdd : forall w, exp w -> exp w -> exp w
  | bvSub : forall w, exp w -> exp w -> exp w
  | bvMul : forall w, exp w -> exp w -> exp w
  | bvMod : forall w, exp w -> exp w -> exp w
  | bvSrem : forall w, exp w -> exp w -> exp w
  | bvSmod : forall w, exp w -> exp w -> exp w
  | bvShl : forall w, exp w -> exp w -> exp w
  | bvLshr : forall w, exp w -> exp w -> exp w
  | bvAshr : forall w, exp w -> exp w -> exp w
  | bvConcat : forall w1 w2, exp w1 -> exp w2 -> exp (w2 + w1)
  | bvExtract : forall w i j, exp (j + (i - j + 1) + (w - i - 1)) -> exp (i - j + 1)
  | bvSlice : forall w1 w2 w3, exp (w3 + w2 + w1) -> exp w2
  | bvHigh : forall wh wl, exp (wl + wh) -> exp wh
  | bvLow : forall wh wl, exp (wl + wh) -> exp wl
  | bvZeroExtend : forall w n, exp w -> exp (w + n)
  | bvSignExtend : forall w n, exp (w.+1) -> exp (w.+1 + n)
  | bvIte : forall w, bexp -> exp w -> exp w -> exp w
  with
  bexp : Type :=
  | bvFalse : bexp
  | bvTrue : bexp
  | bvEq : forall w, exp w -> exp w -> bexp
  | bvUlt : forall w, exp w -> exp w -> bexp
  | bvUle : forall w, exp w -> exp w -> bexp
  | bvUgt : forall w, exp w -> exp w -> bexp
  | bvUge : forall w, exp w -> exp w -> bexp
  | bvSlt : forall w, exp w -> exp w -> bexp
  | bvSle : forall w, exp w -> exp w -> bexp
  | bvSgt : forall w, exp w -> exp w -> bexp
  | bvSge : forall w, exp w -> exp w -> bexp
  | bvUaddo : forall w, exp w -> exp w -> bexp
  | bvUsubo : forall w, exp w -> exp w -> bexp
  | bvUmulo : forall w, exp w -> exp w -> bexp
  | bvSaddo : forall w, exp w -> exp w -> bexp
  | bvSsubo : forall w, exp w -> exp w -> bexp
  | bvSmulo : forall w, exp w -> exp w -> bexp
  | bvLneg : bexp -> bexp
  | bvConj : bexp -> bexp -> bexp
  | bvDisj : bexp -> bexp -> bexp.

  Module ValueType <: Equalities.Typ.
    Definition t : Set := BITS wordsize.
  End ValueType.

  Module State := TStoreAdapter V ValueType.

  Local Notation state := State.t.

  Fixpoint eval_exp {w} (e : exp w) (s : state) {struct e} : BITS w :=
    match e with
    | bvVar v => State.acc v s
    | bvConst _ n => n
    | bvNot w e => fromNat 0 (* TODO *)
    | bvAnd w e e2 => fromNat 0 (* TODO *)
    | bvOr w e1 e2 => orB (eval_exp e1 s) (eval_exp e2 s)
    | bvXor w e1 e2 => fromNat 0 (* TODO *)
    | bvNeg w e => fromNat 0 (* TODO *)
    | bvAdd w e1 e2 => fromNat 0 (* TODO *)
    | bvSub w e1 e2 => fromNat 0 (* TODO *)
    | bvMul w e1 e2 => fromNat 0 (* TODO *)
    | bvMod w e1 e2 => fromNat 0 (* TODO *)
    | bvSrem w e1 e2 => fromNat 0 (* TODO *)
    | bvSmod w e1 e2 => fromNat 0 (* TODO *)
    | bvShl w e1 e2 => fromNat 0 (* TODO *)
    | bvLshr w e1 e2 => fromNat 0 (* TODO *)
    | bvAshr w e1 e2 => fromNat 0 (* TODO *)
    | bvConcat w1 w2 e1 e2 => fromNat 0 (* TODO *)
    | bvExtract w i j e => fromNat 0 (* TODO *)
    | bvSlice w1 w2 w3 e => fromNat 0 (* TODO *)
    | bvHigh wh wl e => fromNat 0 (* TODO *)
    | bvLow wh wl e => fromNat 0 (* TODO *)
    | bvZeroExtend w n e => fromNat 0 (* TODO *)
    | bvSignExtend w n e => fromNat 0 (* TODO *)
    | bvIte w b e1 e2 => if eval_bexp b s then eval_exp e1 s else eval_exp e2 s
    end
    with
    eval_bexp (e : bexp) (s : state) : bool :=
      match e with
      | bvFalse => false
      | bvTrue => true
      | bvEq w e1 e2 => eval_exp e1 s == eval_exp e2 s
      | bvUlt w e1 e2 => true (* TODO *)
      | bvUle w e1 e2 => true (* TODO *)
      | bvUgt w e1 e2 => true (* TODO *)
      | bvUge w e1 e2 => true (* TODO *)
      | bvSlt w e1 e2 => true (* TODO *)
      | bvSle w e1 e2 => true (* TODO *)
      | bvSgt w e1 e2 => true (* TODO *)
      | bvSge w e1 e2 => true (* TODO *)
      | bvUaddo w e1 e2 => true (* TODO *)
      | bvUsubo w e1 e2 => true (* TODO *)
      | bvUmulo w e1 e2 => true (* TODO *)
      | bvSaddo w e1 e2 => true (* TODO *)
      | bvSsubo w e1 e2 => true (* TODO *)
      | bvSmulo w e1 e2 => true (* TODO *)
      | bvLneg e => ~~ (eval_bexp e s)
      | bvConj e1 e2 => eval_bexp e1 s && eval_bexp e2 s
      | bvDisj e1 e2 => eval_bexp e1 s || eval_bexp e2 s
      end.

  Definition valid (e : bexp) : Prop :=
    forall s, eval_bexp e s.

End Make.
