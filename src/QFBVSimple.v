
From Coq Require Import Arith OrderedType.
From Coq Require Import Program Program.Equality.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype tuple.
From Bits Require Export bits.
From ssrlib Require Import Var Store SsrOrdered Nats Tactics.


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
  | bvExtract : forall w i j, exp (j + (i - j + 1) + w) -> exp (i - j + 1)
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
    | bvAnd w e1 e2 => andB (eval_exp e1 s) (eval_exp e2 s)
    | bvOr w e1 e2 => orB (eval_exp e1 s) (eval_exp e2 s)
    | bvXor w e1 e2 => xorB (eval_exp e1 s) (eval_exp e2 s)
    | bvNeg w e => fromNat 0 (* TODO *)
    | bvAdd w e1 e2 => (*fromNat 0*) (* TODO *) addB (eval_exp e1 s) (eval_exp e2 s)
    | bvSub w e1 e2 => fromNat 0 (* TODO *)
    | bvMul w e1 e2 => fromNat 0 (* TODO *)
    | bvMod w e1 e2 => fromNat 0 (* TODO *)
    | bvSrem w e1 e2 => fromNat 0 (* TODO *)
    | bvSmod w e1 e2 => fromNat 0 (* TODO *)
    | bvShl w e1 e2 => fromNat 0 (* TODO *)
    | bvLshr w e1 e2 => fromNat 0 (* TODO *)
    | bvAshr w e1 e2 => fromNat 0 (* TODO *)
    | bvConcat w1 w2 e1 e2 => catB (eval_exp e1 s) (eval_exp e2 s)
    | bvExtract w i j e => fromNat 0 (* TODO *)
    | bvSlice w1 w2 w3 e => fromNat 0 (* TODO *)
    | bvHigh wh wl e => fromNat 0 (* TODO *)
    | bvLow wh wl e => fromNat 0 (* TODO *)
    | bvZeroExtend w n e => zeroExtend n (eval_exp e s)
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


  (* Non-dependent expressions *)

  Inductive nexp : Type :=
  | nbvVar : var -> nexp
  | nbvConst : forall w, BITS w -> nexp
  | nbvNot : nexp -> nexp
  | nbvAnd : nexp -> nexp -> nexp
  | nbvOr : nexp -> nexp -> nexp
  | nbvXor : nexp -> nexp -> nexp
  | nbvNeg : nexp -> nexp
  | nbvAdd : nexp -> nexp -> nexp
  | nbvSub : nexp -> nexp -> nexp
  | nbvMul : nexp -> nexp -> nexp
  | nbvMod : nexp -> nexp -> nexp
  | nbvSrem : nexp -> nexp -> nexp
  | nbvSmod : nexp -> nexp -> nexp
  | nbvShl : nexp -> nexp -> nexp
  | nbvLshr : nexp -> nexp -> nexp
  | nbvAshr : nexp -> nexp -> nexp
  | nbvConcat : nexp -> nexp -> nexp
  | nbvExtract : nexp -> nat -> nat -> nexp
  | nbvSlice : nexp -> nat -> nat -> nat -> nexp
  | nbvHigh : nexp -> nat -> nexp
  | nbvLow : nexp -> nat -> nexp
  | nbvZeroExtend : nexp -> nat -> nexp
  | nbvSignExtend : nexp -> nat -> nexp
  | nbvIte : nbexp -> nexp -> nexp -> nexp
  with
  nbexp : Type :=
  | nbvFalse : nbexp
  | nbvTrue : nbexp
  | nbvEq : nexp -> nexp -> nbexp
  | nbvUlt : nexp -> nexp -> nbexp
  | nbvUle : nexp -> nexp -> nbexp
  | nbvUgt : nexp -> nexp -> nbexp
  | nbvUge : nexp -> nexp -> nbexp
  | nbvSlt : nexp -> nexp -> nbexp
  | nbvSle : nexp -> nexp -> nbexp
  | nbvSgt : nexp -> nexp -> nbexp
  | nbvSge : nexp -> nexp -> nbexp
  | nbvUaddo : nexp -> nexp -> nbexp
  | nbvUsubo : nexp -> nexp -> nbexp
  | nbvUmulo : nexp -> nexp -> nbexp
  | nbvSaddo : nexp -> nexp -> nbexp
  | nbvSsubo : nexp -> nexp -> nbexp
  | nbvSmulo : nexp -> nexp -> nbexp
  | nbvLneg : nbexp -> nbexp
  | nbvConj : nbexp -> nbexp -> nbexp
  | nbvDisj : nbexp -> nbexp -> nbexp.

  Fixpoint exp_dedep {w} (e : exp w) : nexp :=
    match e with
    | bvVar v => nbvVar v
    | bvConst w n => nbvConst w n
    | bvNot _ e => nbvNot (exp_dedep e)
    | bvAnd _ e1 e2 => nbvAnd (exp_dedep e1) (exp_dedep e2)
    | bvOr _ e1 e2 => nbvOr (exp_dedep e1) (exp_dedep e2)
    | bvXor _ e1 e2 => nbvXor (exp_dedep e1) (exp_dedep e2)
    | bvNeg _ e => nbvNeg (exp_dedep e)
    | bvAdd _ e1 e2 => nbvAdd (exp_dedep e1) (exp_dedep e2)
    | bvSub _ e1 e2 => nbvSub (exp_dedep e1) (exp_dedep e2)
    | bvMul _ e1 e2 => nbvMul (exp_dedep e1) (exp_dedep e2)
    | bvMod _ e1 e2 => nbvMod (exp_dedep e1) (exp_dedep e2)
    | bvSrem _ e1 e2 => nbvSrem (exp_dedep e1) (exp_dedep e2)
    | bvSmod _ e1 e2 => nbvSmod (exp_dedep e1) (exp_dedep e2)
    | bvShl _ e1 e2 => nbvShl (exp_dedep e1) (exp_dedep e2)
    | bvLshr _ e1 e2 => nbvLshr (exp_dedep e1) (exp_dedep e2)
    | bvAshr _ e1 e2 => nbvAshr (exp_dedep e1) (exp_dedep e2)
    | bvConcat _ _ e1 e2 => nbvConcat (exp_dedep e1) (exp_dedep e2)
    | bvExtract _ i j e => nbvExtract (exp_dedep e) i j
    | bvSlice w1 w2 w3 e => nbvSlice (exp_dedep e) w1 w2 w3
    | bvHigh wh wl e => nbvHigh (exp_dedep e) wh
    | bvLow wh wl e => nbvLow (exp_dedep e) wl
    | bvZeroExtend _ n e => nbvZeroExtend (exp_dedep e) n
    | bvSignExtend _ n e => nbvSignExtend (exp_dedep e) n
    | bvIte w c e1 e2 => nbvIte (bexp_dedep c) (exp_dedep e1) (exp_dedep e2)
    end
    with
    bexp_dedep (e : bexp) : nbexp :=
      match e with
      | bvFalse => nbvFalse
      | bvTrue => nbvTrue
      | bvEq _ e1 e2 => nbvEq (exp_dedep e1) (exp_dedep e2)
      | bvUlt _ e1 e2 => nbvUlt (exp_dedep e1) (exp_dedep e2)
      | bvUle _ e1 e2 => nbvUle (exp_dedep e1) (exp_dedep e2)
      | bvUgt _ e1 e2 => nbvUgt (exp_dedep e1) (exp_dedep e2)
      | bvUge _ e1 e2 => nbvUge (exp_dedep e1) (exp_dedep e2)
      | bvSlt _ e1 e2 => nbvSlt (exp_dedep e1) (exp_dedep e2)
      | bvSle _ e1 e2 => nbvSle (exp_dedep e1) (exp_dedep e2)
      | bvSgt _ e1 e2 => nbvSgt (exp_dedep e1) (exp_dedep e2)
      | bvSge _ e1 e2 => nbvSge (exp_dedep e1) (exp_dedep e2)
      | bvUaddo _ e1 e2 => nbvUaddo (exp_dedep e1) (exp_dedep e2)
      | bvUsubo _ e1 e2 => nbvUsubo (exp_dedep e1) (exp_dedep e2)
      | bvUmulo _ e1 e2 => nbvUmulo (exp_dedep e1) (exp_dedep e2)
      | bvSaddo _ e1 e2 => nbvSaddo (exp_dedep e1) (exp_dedep e2)
      | bvSsubo _ e1 e2 => nbvSsubo (exp_dedep e1) (exp_dedep e2)
      | bvSmulo _ e1 e2 => nbvSmulo (exp_dedep e1) (exp_dedep e2)
      | bvLneg e => nbvLneg (bexp_dedep e)
      | bvConj e1 e2 => nbvConj (bexp_dedep e1) (bexp_dedep e2)
      | bvDisj e1 e2 => nbvDisj (bexp_dedep e1) (bexp_dedep e2)
      end.

  Lemma nconst_inj_jmeq :
    forall {w1 w2} {b1 : BITS w1} {b2 : BITS w2},
      nbvConst w1 b1 = nbvConst w2 b2 ->
      w1 = w2 /\ b1 ~= b2.
  Proof.
    move=> w1 w2 b1 b2 H. injection H. move=> He Hw. split; first by exact: Hw.
    move: b1 H He. rewrite Hw. move=> b1 H He.
    rewrite (Eqdep.EqdepTheory.inj_pair2 nat BITS w2 _ _ He). exact: JMeq_refl.
  Qed.

  Lemma nconst_inj_eq :
    forall {w} {b1 b2 : BITS w},
      nbvConst w b1 = nbvConst w b2 -> b1 = b2.
  Proof.
    move=> w b1 b2 H. move: (nconst_inj_jmeq H). move=> [Hw Hb].
    rewrite Hb. reflexivity.
  Qed.

  Ltac exp_dedep_jmeq1 :=
    move=> /= []; intros He;
    match goal with
    | exp_dedep_jmeq : (forall (w1 w2 : nat) (e1 : exp w1) (e2 : exp w2),
                           exp_dedep e1 = exp_dedep e2 -> w1 = w2 /\ e1 ~= e2),
      e1 : exp ?w1,
      e2 : exp ?w2,
      He : exp_dedep ?e1 = exp_dedep ?e2 |- _ =>
      move: {He} (exp_dedep_jmeq _ _ _ _ He); intros [Hw He]; move: e1 e2 He;
      rewrite Hw; move=> e1 e2 He; rewrite He; split; reflexivity
    end.

  Ltac exp_dedep_jmeq2 :=
    move=> /= []; intros He1 He2;
    match goal with
    | exp_dedep_jmeq : (forall (w1 w2 : nat) (e1 : exp w1) (e2 : exp w2),
                           exp_dedep e1 = exp_dedep e2 -> w1 = w2 /\ e1 ~= e2),
      e1_1 : exp ?w1, e1_2 : exp ?w2,
      e2_1 : exp ?w3, e2_2 : exp ?w4,
      He1 : exp_dedep ?e1_1 = exp_dedep ?e2_1,
      He2 : exp_dedep ?e1_2 = exp_dedep ?e2_2 |- _ =>
      move: {He1 He2} (exp_dedep_jmeq _ _ _ _ He1) (exp_dedep_jmeq _ _ _ _ He2);
      intros [Hw1 He1] [Hw2 He2]; move: e1_1 e1_2 He1 He2;
      try rewrite Hw1; try rewrite Hw2; intros e1_1 e1_2 He1 He2;
      rewrite He1 He2; split; reflexivity
  end.

  Ltac bexp_dedep_eq2 :=
    move=> /= []; move=> He He0;
    match goal with
    | exp_dedep_jmeq : (forall (w1 w2 : nat) (e1 : exp w1) (e2 : exp w2),
                           exp_dedep e1 = exp_dedep e2 -> w1 = w2 /\ e1 ~= e2),
      w : nat,
      e : exp ?w,
      e0 : exp ?w,
      w0 : nat,
      e1 : exp ?w0,
      e2 : exp ?w0,
      He : exp_dedep ?e = exp_dedep ?e1,
      He0 : exp_dedep ?e0 = exp_dedep ?e2 |- _ =>
      move: {He He0} (exp_dedep_jmeq _ _ _ _ He)
                     (exp_dedep_jmeq _ _ _ _ He0);
      intros [Hw He] [_ He0]; move: e e0 He He0; rewrite Hw; intros e e0 He He0;
      rewrite He He0; reflexivity
    end.

  Lemma exp_dedep_jmeq :
    forall {w1 w2} {e1 : exp w1} {e2 : exp w2},
      exp_dedep e1 = exp_dedep e2 ->
      w1 = w2 /\ e1 ~= e2
  with
  bexp_dedep_eq :
    forall {e1 e2 : bexp}, bexp_dedep e1 = bexp_dedep e2 -> e1 = e2.
  Proof.
    (* exp_dedep_jmeq *)
    move=> w1 w2 e1 e2. destruct e1; dependent destruction e2; try discriminate.
    - move=> /= []. move=> ->. split; reflexivity.
    - move=> /= H. move: (nconst_inj_jmeq H) => {H} [Hw Hb].
      move: b Hb. rewrite Hw. move=> b Hb. rewrite Hb. split; reflexivity.
    - exp_dedep_jmeq1.
    - exp_dedep_jmeq2.
    - exp_dedep_jmeq2.
    - exp_dedep_jmeq2.
    - exp_dedep_jmeq1.
    - exp_dedep_jmeq2.
    - exp_dedep_jmeq2.
    - exp_dedep_jmeq2.
    - exp_dedep_jmeq2.
    - exp_dedep_jmeq2.
    - exp_dedep_jmeq2.
    - exp_dedep_jmeq2.
    - exp_dedep_jmeq2.
    - exp_dedep_jmeq2.
    - exp_dedep_jmeq2.
    - move=> /= []. move=> He Hi Hj. move: {He} (exp_dedep_jmeq _ _ _ _ He).
      move=> [Hij He]. move: e1 Hij He. rewrite Hi Hj. move=> e1 Hij He.
      move/eqP: Hij. rewrite eqn_add2l. move/eqP=> Hw. move: e1 He. rewrite Hw.
      move=> e1 H2. rewrite H2. split; reflexivity.
    - move=> /= []. move=> He Hw1 Hw0 Hw3. move: {He} (exp_dedep_jmeq _ _ _ _ He).
      move=> [_ He]. move: e1 He. rewrite Hw1 Hw0 Hw3. move=> e1 He. rewrite He.
      split; reflexivity.
    - move=> /= []. move=> He Hw. move: {He} (exp_dedep_jmeq _ _ _ _ He).
      move=> [Hhl He]. move: e1 Hhl He. rewrite Hw. move=> e1 Hhl He.
      move: (proj1 (Nat.add_cancel_r _ _ _) Hhl) => {Hhl} Hwl.
      move: e1 He; rewrite Hwl => e1 He. rewrite He. split; reflexivity.
    - move=> /= []. move=> He Hw. move: {He} (exp_dedep_jmeq _ _ _ _ He).
      move=> [Hhl He]. move: e1 Hhl He. rewrite Hw. move=> e1 Hhl He.
      move: (proj1 (Nat.add_cancel_l _ _ _) Hhl) => {Hhl} Hwh.
      move: e1 He; rewrite Hwh => e1 He. rewrite He. split; reflexivity.
    - move=> /= []. move=> He Hn. move: {He} (exp_dedep_jmeq _ _ _ _ He).
      move=> [Hw He]. move: e1 He; rewrite Hn Hw=> e1 He. rewrite He.
      split; reflexivity.
    - move=> /= []. move=> He Hn. move: {He} (exp_dedep_jmeq _ _ _ _ He).
      move=> [Hw He]. rewrite -(addn1 w) -(addn1 w0) in Hw.
      move: (proj1 (Nat.add_cancel_r _ _ _) Hw) => {Hw} Hw.
      move: e1 He; rewrite Hn Hw => e1 He. rewrite He. split; reflexivity.
    - move=> /= []. move=> Hb He1 He2.
      move: {Hb He1 He2} (bexp_dedep_eq _ _ Hb)
                         (exp_dedep_jmeq _ _ _ _ He1) (exp_dedep_jmeq _ _ _ _ He2).
      move=> Hb [Hw He1] [_ He2]. move: e1_1 e1_2 He1 He2; rewrite Hb Hw.
      move=> e1_1 e1_2 He1 He2. rewrite He1 He2. split; reflexivity.
    (* bexp_dedep_eq *)
    - move=> e1 e2. destruct e1; dependent destruction e2; try discriminate.
    - reflexivity.
    - reflexivity.
    - bexp_dedep_eq2.
    - bexp_dedep_eq2.
    - bexp_dedep_eq2.
    - bexp_dedep_eq2.
    - bexp_dedep_eq2.
    - bexp_dedep_eq2.
    - bexp_dedep_eq2.
    - bexp_dedep_eq2.
    - bexp_dedep_eq2.
    - bexp_dedep_eq2.
    - bexp_dedep_eq2.
    - bexp_dedep_eq2.
    - bexp_dedep_eq2.
    - bexp_dedep_eq2.
    - bexp_dedep_eq2.
    - move=> /= []. move=> He. move: (bexp_dedep_eq _ _ He). move=> ->. reflexivity.
    - move=> /= []. move=> He1 He2. move: {He1 He2} (bexp_dedep_eq _ _ He1)
                                                    (bexp_dedep_eq _ _ He2).
      move=> -> ->. reflexivity.
    - move=> /= []. move=> He1 He2. move: {He1 He2} (bexp_dedep_eq _ _ He1)
                                                    (bexp_dedep_eq _ _ He2).
      move=> -> ->. reflexivity.
  Qed.

  Lemma exp_dedep_eq :
    forall {w} {e1 e2 : exp w},
      exp_dedep e1 = exp_dedep e2 -> e1 = e2.
  Proof.
    move=> w e1 e2 H. move: (exp_dedep_jmeq H). move=> [_ ->]. reflexivity.
  Qed.

  Lemma exp_dedep_neq :
    forall {w} {e1 e2 : exp w},
      exp_dedep e1 <> exp_dedep e2 -> e1 <> e2.
  Proof.
    move=> w e1 e2 H1 H2. apply: H1. rewrite H2. reflexivity.
  Qed.

  Lemma exp_neq_dedep :
    forall {w} {e1 e2 : exp w},
      e1 <> e2 -> exp_dedep e1 <> exp_dedep e2.
  Proof.
    move=> w e1 e2 H1 H2. apply: H1. exact: (exp_dedep_eq H2).
  Qed.



  (* Equality of non-dependent expressions *)

  Fixpoint nexp_eqb (e1 e2 : nexp) : bool :=
    match e1, e2 with
    | nbvVar v1, nbvVar v2 => v1 == v2
    | nbvConst w1 n1, nbvConst w2 n2 => (w1 == w2) && (toNat n1 == toNat n2)
    | nbvNot e1, nbvNot e2 => nexp_eqb e1 e2
    | nbvAnd e1 e2, nbvAnd e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvOr e1 e2, nbvOr e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvXor e1 e2, nbvXor e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvNeg e1, nbvNeg e2 => nexp_eqb e1 e2
    | nbvAdd e1 e2, nbvAdd e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvSub e1 e2, nbvSub e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvMul e1 e2, nbvMul e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvMod e1 e2, nbvMod e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvSrem e1 e2, nbvSrem e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvSmod e1 e2, nbvSmod e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvShl e1 e2, nbvShl e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvLshr e1 e2, nbvLshr e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvAshr e1 e2, nbvAshr e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvConcat e1 e2, nbvConcat e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvExtract e1 i1 j1, nbvExtract e2 i2 j2 =>
      (nexp_eqb e1 e2) && (i1 == i2) && (j1 == j2)
    | nbvSlice e1 w1 w2 w3, nbvSlice e2 w4 w5 w6 =>
      (nexp_eqb e1 e2) && (w1 == w4) && (w2 == w5) && (w3 == w6)
    | nbvHigh e1 wh1, nbvHigh e2 wh2 => (nexp_eqb e1 e2) && (wh1 == wh2)
    | nbvLow e1 wl1, nbvLow e2 wl2 => (nexp_eqb e1 e2) && (wl1 == wl2)
    | nbvZeroExtend e1 n1, nbvZeroExtend e2 n2 => (nexp_eqb e1 e2) && (n1 == n2)
    | nbvSignExtend e1 n1, nbvSignExtend e2 n2 => (nexp_eqb e1 e2) && (n1 == n2)
    | nbvIte c1 e1 e2, nbvIte c2 e3 e4 =>
      (nbexp_eqb c1 c2) && (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | _, _ => false
    end
  with
  nbexp_eqb (e1 e2 : nbexp) : bool :=
    match e1, e2 with
    | nbvFalse, nbvFalse => true
    | nbvTrue, nbvTrue => true
    | nbvEq e1 e2, nbvEq e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvUlt e1 e2, nbvUlt e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvUle e1 e2, nbvUle e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvUgt e1 e2, nbvUgt e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvUge e1 e2, nbvUge e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvSlt e1 e2, nbvSlt e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvSle e1 e2, nbvSle e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvSgt e1 e2, nbvSgt e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvSge e1 e2, nbvSge e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvUaddo e1 e2, nbvUaddo e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvUsubo e1 e2, nbvUsubo e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvUmulo e1 e2, nbvUmulo e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvSaddo e1 e2, nbvSaddo e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvSsubo e1 e2, nbvSsubo e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvSmulo e1 e2, nbvSmulo e3 e4 => (nexp_eqb e1 e3) && (nexp_eqb e2 e4)
    | nbvLneg e1, nbvLneg e2 => nbexp_eqb e1 e2
    | nbvConj e1 e2, nbvConj e3 e4 => (nbexp_eqb e1 e3) && (nbexp_eqb e2 e4)
    | nbvDisj e1 e2, nbvDisj e3 e4 => (nbexp_eqb e1 e3) && (nbexp_eqb e2 e4)
    | _, _ => false
    end.

  Lemma nexp_eqb_eq {e1 e2 : nexp} : nexp_eqb e1 e2 -> e1 = e2
  with
  nbexp_eqb_eq {e1 e2 : nbexp} : nbexp_eqb e1 e2 -> e1 = e2.
  Proof.
    (* nexp_eqb_eq *)
    case: e1; case: e2 => /=; try discriminate.
    - move=> v1 v2 /eqP ->; reflexivity.
    - move=> w1 b1 w2 b2 /andP [/eqP Hw /eqP Hb]. move: b2 Hb; rewrite Hw => b2 Hb.
      rewrite (toNat_inj Hb). reflexivity.
    - move=> e1 e2 H. rewrite (nexp_eqb_eq _ _ H); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 H. rewrite (nexp_eqb_eq _ _ H); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 i1 j1 e2 i2 j2 /andP [/andP [H1 H2] H3].
      rewrite (nexp_eqb_eq _ _ H1) (eqP H2) (eqP H3); reflexivity.
    - move=> e1 w1 w2 w3 e2 w4 w5 w6 /andP [/andP [/andP [H1 H2] H3] H4].
      rewrite (nexp_eqb_eq _ _ H1) (eqP H2) (eqP H3) (eqP H4); reflexivity.
    - move=> e1 w1 e2 w2 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (eqP H2); reflexivity.
    - move=> e1 w1 e2 w2 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (eqP H2); reflexivity.
    - move=> e1 w1 e2 w2 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (eqP H2); reflexivity.
    - move=> e1 w1 e2 w2 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (eqP H2); reflexivity.
    - move=> c1 e1 e2 c2 e3 e4 /andP [/andP [H1 H2] H3].
      rewrite (nbexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2) (nexp_eqb_eq _ _ H3);
        reflexivity.
    (* nbexp_eqb_eq *)
    case: e1; case: e2 => /=; try discriminate.
    - reflexivity.
    - reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nexp_eqb_eq _ _ H1) (nexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 H. rewrite (nbexp_eqb_eq _ _ H); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nbexp_eqb_eq _ _ H1) (nbexp_eqb_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (nbexp_eqb_eq _ _ H1) (nbexp_eqb_eq _ _ H2); reflexivity.
  Qed.

  Lemma nexp_eqb_refl (e : nexp) : nexp_eqb e e
  with
  nbexp_eqb_refl (e : nbexp) : nbexp_eqb e e.
  Proof.
    (* nexp_eqb_refl *)
    case: e => /=.
    - move=> v; exact: eqxx.
    - move=> w b; by rewrite 2!eqxx.
    - move=> e; exact: nexp_eqb_refl.
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e; exact: nexp_eqb_refl.
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e i j; by rewrite (nexp_eqb_refl e) 2!eqxx.
    - move=> e w1 w2 w3; by rewrite (nexp_eqb_refl e) 3!eqxx.
    - move=> e w; by rewrite (nexp_eqb_refl e) eqxx.
    - move=> e w; by rewrite (nexp_eqb_refl e) eqxx.
    - move=> e w; by rewrite (nexp_eqb_refl e) eqxx.
    - move=> e w; by rewrite (nexp_eqb_refl e) eqxx.
    - move=> c e1 e2; by rewrite (nbexp_eqb_refl c) (nexp_eqb_refl e1)
                                 (nexp_eqb_refl e2).
    (* nbexp_eqb_refl *)
    case: e => /=.
    - done.
    - done.
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nexp_eqb_refl e1) (nexp_eqb_refl e2).
    - move=> e; exact: nbexp_eqb_refl.
    - move=> e1 e2; by rewrite (nbexp_eqb_refl e1) (nbexp_eqb_refl e2).
    - move=> e1 e2; by rewrite (nbexp_eqb_refl e1) (nbexp_eqb_refl e2).
  Qed.

  Lemma nexp_eqb_sym {e1 e2 : nexp} : nexp_eqb e1 e2 -> nexp_eqb e2 e1.
  Proof.
    move=> H. rewrite (nexp_eqb_eq H). exact: nexp_eqb_refl.
  Qed.

  Lemma nbexp_eqb_sym {e1 e2 : nbexp} : nbexp_eqb e1 e2 -> nbexp_eqb e2 e1.
  Proof.
    move=> H. rewrite (nbexp_eqb_eq H). exact: nbexp_eqb_refl.
  Qed.

  Lemma nexp_eqb_trans {e1 e2 e3 : nexp} :
    nexp_eqb e1 e2 -> nexp_eqb e2 e3 -> nexp_eqb e1 e3.
  Proof.
    move=> H1 H2. rewrite (nexp_eqb_eq H1) (nexp_eqb_eq H2). exact: nexp_eqb_refl.
  Qed.

  Lemma nbexp_eqb_trans {e1 e2 e3 : nbexp} :
    nbexp_eqb e1 e2 -> nbexp_eqb e2 e3 -> nbexp_eqb e1 e3.
  Proof.
    move=> H1 H2. rewrite (nbexp_eqb_eq H1) (nbexp_eqb_eq H2). exact: nbexp_eqb_refl.
  Qed.

  Lemma nexp_eqP (e1 e2 : nexp) : reflect (e1 = e2) (nexp_eqb e1 e2).
  Proof.
    case H: (nexp_eqb e1 e2).
    - apply: ReflectT. exact: (nexp_eqb_eq H).
    - apply: ReflectF. move=> Heq. move/negP: H; apply. rewrite Heq.
      exact: nexp_eqb_refl.
  Qed.

  Lemma nbexp_eqP (e1 e2 : nbexp) : reflect (e1 = e2) (nbexp_eqb e1 e2).
  Proof.
    case H: (nbexp_eqb e1 e2).
    - apply: ReflectT. exact: (nbexp_eqb_eq H).
    - apply: ReflectF. move=> Heq. move/negP: H; apply.
      rewrite Heq. exact: nbexp_eqb_refl.
  Qed.

  Definition nexp_eqMixin := EqMixin nexp_eqP.
  Definition nbexp_eqMixin := EqMixin nbexp_eqP.
  Canonical nexp_eqType := Eval hnf in EqType nexp nexp_eqMixin.
  Canonical nbexp_eqType := Eval hnf in EqType nbexp nbexp_eqMixin.



  (* Less-than of non-dependent expressions *)

  Definition nexp_op_id (e : nexp) : nat :=
    match e with
    | nbvVar _ => 0
    | nbvConst _ _ => 1
    | nbvNot _ => 2
    | nbvAnd _ _ => 3
    | nbvOr _ _ => 4
    | nbvXor _ _ => 5
    | nbvNeg _ => 6
    | nbvAdd _ _ => 7
    | nbvSub _ _ => 8
    | nbvMul _ _ => 9
    | nbvMod _ _ => 10
    | nbvSrem _ _ => 11
    | nbvSmod _ _ => 12
    | nbvShl _ _ => 13
    | nbvLshr _ _ => 14
    | nbvAshr _ _ => 15
    | nbvConcat _ _ => 16
    | nbvExtract _ _ _ => 17
    | nbvSlice _ _ _ _ => 18
    | nbvHigh _ _ => 19
    | nbvLow _ _ => 20
    | nbvZeroExtend _ _ => 21
    | nbvSignExtend _ _ => 22
    | nbvIte _ _ _ => 23
    end.

  Definition nbexp_op_id (e : nbexp) : nat :=
    match e with
    | nbvFalse => 0
    | nbvTrue => 1
    | nbvEq _ _ => 2
    | nbvUlt _ _ => 3
    | nbvUle _ _ => 4
    | nbvUgt _ _ => 5
    | nbvUge _ _ => 6
    | nbvSlt _ _ => 7
    | nbvSle _ _ => 8
    | nbvSgt _ _ => 9
    | nbvSge _ _ => 10
    | nbvUaddo _ _ => 11
    | nbvUsubo _ _ => 12
    | nbvUmulo _ _ => 13
    | nbvSaddo _ _ => 14
    | nbvSsubo _ _ => 15
    | nbvSmulo _ _ => 16
    | nbvLneg _ => 17
    | nbvConj _ _ => 18
    | nbvDisj _ _ => 19
    end.

  (* const_ltb b1 b2 does not indicate that toNat b1 < toNat b2 *)
  Definition const_ltb {w1 w2 : nat} (b1 : BITS w1) (b2 : BITS w2) : bool :=
    (w1 < w2) || ((w1 == w2) && (toNat b1 < toNat b2)).

  Lemma const_ltb_irrefl : forall {w : nat} (b : BITS w), ~ const_ltb b b.
  Proof.
    rewrite /const_ltb. move=> w b. rewrite (eqxx w) 2!ltnn /=. done.
  Qed.

  Lemma const_ltb_trans :
    forall {w1 w2 w3 : nat} {b1 : BITS w1} {b2 : BITS w2} {b3 : BITS w3},
      const_ltb b1 b2 -> const_ltb b2 b3 -> const_ltb b1 b3.
  Proof.
    rewrite /const_ltb => w1 w2 w3 b1 b2 b3 H1 H2. case/orP: H1.
    - case/orP: H2.
      + move=> H1 H2. rewrite (ltn_trans H2 H1). done.
      + move/andP=> [Hw Hb]. rewrite (eqP Hw). move=> -> /=. done.
    - move/andP=> [Hw Hb]. move: b1 Hb; rewrite (eqP Hw) => b1 Hb. case/orP: H2.
      + move=> -> /=. done.
      + move/andP=> [H1 H2]. rewrite H1 (ltn_trans Hb H2). rewrite orbT. done.
  Qed.

  Lemma ltB_const_ltb {w : nat} {b1 b2 : BITS w} :
    ltB b1 b2 -> const_ltb b1 b2.
  Proof.
    move=> H. by rewrite /const_ltb eqxx -ltB_nat H orbT.
  Qed.

  Fixpoint nexp_ltb (e1 e2 : nexp) : bool :=
    match e1, e2 with
    | nbvVar v1, nbvVar v2 => V.ltb v1 v2
    | nbvConst w1 n1, nbvConst w2 n2 => const_ltb n1 n2
    | nbvNot e1, nbvNot e2 => nexp_ltb e1 e2
    | nbvAnd e1 e2, nbvAnd e3 e4 => (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
    | nbvOr e1 e2, nbvOr e3 e4 => (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
    | nbvXor e1 e2, nbvXor e3 e4 => (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
    | nbvNeg e1, nbvNeg e2 => nexp_ltb e1 e2
    | nbvAdd e1 e2, nbvAdd e3 e4 => (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
    | nbvSub e1 e2, nbvSub e3 e4 => (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
    | nbvMul e1 e2, nbvMul e3 e4 => (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
    | nbvMod e1 e2, nbvMod e3 e4 => (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
    | nbvSrem e1 e2, nbvSrem e3 e4 =>
      (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
    | nbvSmod e1 e2, nbvSmod e3 e4 =>
      (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
    | nbvShl e1 e2, nbvShl e3 e4 =>
      (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
    | nbvLshr e1 e2, nbvLshr e3 e4 =>
      (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
    | nbvAshr e1 e2, nbvAshr e3 e4 =>
      (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
    | nbvConcat e1 e2, nbvConcat e3 e4 =>
      (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
    | nbvExtract e1 i1 j1, nbvExtract e2 i2 j2 =>
      (nexp_ltb e1 e2)
      || ((e1 == e2) && (i1 < i2))
      || ((e1 == e2) && (i1 == i2) && (j1 < j2))
    | nbvSlice e1 w1 w2 w3, nbvSlice e2 w4 w5 w6 =>
      (nexp_ltb e1 e2)
      || ((e1 == e2) && (w1 < w4))
      || ((e1 == e2) && (w1 == w4) && (w2 < w5))
      || ((e1 == e2) && (w1 == w4) && (w2 == w5) && (w3 < w6))
    | nbvHigh e1 wh1, nbvHigh e2 wh2 => (nexp_ltb e1 e2) || ((e1 == e2) && (wh1 < wh2))
    | nbvLow e1 wl1, nbvLow e2 wl2 => (nexp_ltb e1 e2) || ((e1 == e2) && (wl1 < wl2))
    | nbvZeroExtend e1 n1, nbvZeroExtend e2 n2 =>
      (nexp_ltb e1 e2) || ((e1 == e2) && (n1 < n2))
    | nbvSignExtend e1 n1, nbvSignExtend e2 n2 =>
      (nexp_ltb e1 e2) || ((e1 == e2) && (n1 < n2))
    | nbvIte c1 e1 e2, nbvIte c2 e3 e4 =>
      (nbexp_ltb c1 c2) || ((c1 == c2) && nexp_ltb e1 e3)
      || ((c1 == c2) && (e1 == e3) && nexp_ltb e2 e4)
    | _, _ => nexp_op_id e1 < nexp_op_id e2
    end
    with
    nbexp_ltb (e1 e2 : nbexp) : bool :=
      match e1, e2 with
      | nbvEq e1 e2, nbvEq e3 e4 => (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
      | nbvUlt e1 e2, nbvUlt e3 e4 =>
        (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
      | nbvUle e1 e2, nbvUle e3 e4 =>
        (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
      | nbvUgt e1 e2, nbvUgt e3 e4 =>
        (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
      | nbvUge e1 e2, nbvUge e3 e4 =>
        (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
      | nbvSlt e1 e2, nbvSlt e3 e4 =>
        (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
      | nbvSle e1 e2, nbvSle e3 e4 =>
        (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
      | nbvSgt e1 e2, nbvSgt e3 e4 =>
        (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
      | nbvSge e1 e2, nbvSge e3 e4 =>
        (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
      | nbvUaddo e1 e2, nbvUaddo e3 e4 =>
        (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
      | nbvUsubo e1 e2, nbvUsubo e3 e4 =>
        (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
      | nbvUmulo e1 e2, nbvUmulo e3 e4 =>
        (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
      | nbvSaddo e1 e2, nbvSaddo e3 e4 =>
        (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
      | nbvSsubo e1 e2, nbvSsubo e3 e4 =>
        (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
      | nbvSmulo e1 e2, nbvSmulo e3 e4 =>
        (nexp_ltb e1 e3) || ((e1 == e3) && nexp_ltb e2 e4)
      | nbvLneg e1, nbvLneg e2 => nbexp_ltb e1 e2
      | nbvConj e1 e2, nbvConj e3 e4 =>
        (nbexp_ltb e1 e3) || ((e1 == e3) && nbexp_ltb e2 e4)
      | nbvDisj e1 e2, nbvDisj e3 e4 =>
        (nbexp_ltb e1 e3) || ((e1 == e3) && nbexp_ltb e2 e4)
      | _, _ => nbexp_op_id e1 < nbexp_op_id e2
      end.

  Lemma nexp_ltb_not_eq {e1 e2 : nexp} : nexp_ltb e1 e2 -> e1 <> e2
  with
  nbexp_ltb_not_eq {e1 e2 : nbexp} : nbexp_ltb e1 e2 -> e1 <> e2.
  Proof.
    (* nexp_ltb_not_eq *)
    case: e1; case: e2; try (intros; discriminate).
    - move=> v1 v2 /=. move=> Hlt [] Heq. apply: (V.lt_not_eq Hlt). rewrite Heq.
      exact: V.eq_refl.
    - move=> w1 b1 w2 b2 /=. move=> Hlt []. move=> Hw.
      move: b2 Hlt; rewrite Hw => b2 Hlt Hb.
      move: (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ Hb) => {Hb} Hb.
      rewrite Hb in Hlt. exact: (const_ltb_irrefl b1 Hlt).
    - move=> e1 e2 /=. move=> Hlt [] Heq. exact: (nexp_ltb_not_eq _ _ Hlt Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 /=. move=> Hlt [] Heq. exact: (nexp_ltb_not_eq _ _ Hlt Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 i1 j1 e2 i2 j2 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _ _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq _. rewrite Heq ltnn in b. done.
      + case: Heq. move=> _ _ Heq. rewrite Heq ltnn in b. done.
    - move=> e1 w1 w2 w3 e2 w4 w5 w6 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _ _ _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq _ _. by rewrite Heq ltnn in b.
      + case: Heq. move=> _ _ Heq _. by rewrite Heq ltnn in b.
      + case: Heq. move=> _ _ _ Heq. by rewrite Heq ltnn in b.
    - move=> e1 wh1 e2 wh2 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. by rewrite Heq ltnn in b.
    - move=> e1 wl1 e2 wl2 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. by rewrite Heq ltnn in b.
    - move=> e1 n1 e2 n2 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. by rewrite Heq ltnn in b.
    - move=> e1 n1 e2 n2 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. by rewrite Heq ltnn in b.
    - move=> c1 e1 e2 c2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _ _. exact: (nbexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq _. exact: (nexp_ltb_not_eq _ _ b Heq).
      + case: Heq. move=> _ _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    (* nbexp_ltb_not_eq *)
    case: e1; case: e2; try (intros; discriminate).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 /=. move=> Hlt [] Heq. exact: (nbexp_ltb_not_eq _ _ Hlt Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nbexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nbexp_ltb_not_eq _ _ b Heq).
    - move=> e1 e2 e3 e4 /=. move=> Hlt Heq. caseb_hyps.
      + case: Heq. move=> Heq _. exact: (nbexp_ltb_not_eq _ _ a Heq).
      + case: Heq. move=> _ Heq. exact: (nbexp_ltb_not_eq _ _ b Heq).
  Qed.

  Lemma nexp_ltb_not_eqb (e1 e2 : nexp) : nexp_ltb e1 e2 -> e1 != e2.
  Proof.
    move=> H. apply/eqP. exact: (nexp_ltb_not_eq H).
  Qed.

  Lemma nbexp_ltb_not_eqb (e1 e2 : nbexp) : nbexp_ltb e1 e2 -> e1 != e2.
  Proof.
    move=> H. apply/eqP. exact: (nbexp_ltb_not_eq H).
  Qed.

  Lemma nexp_ltb_trans (e1 e2 e3 : nexp) :
      nexp_ltb e1 e2 -> nexp_ltb e2 e3 -> nexp_ltb e1 e3
  with
  nbexp_ltb_trans (e1 e2 e3 : nbexp) :
      nbexp_ltb e1 e2 -> nbexp_ltb e2 e3 -> nbexp_ltb e1 e3.
  Proof.
    (* nexp_ltb_trans *)
    case: e1.
    - move=> v1; case: e2; case: e3; try done.
      move=> v2 v3 /=. exact: (@V.lt_trans v1 v3 v2).
    - move=> w1 b1; case: e2; case: e3; try done. move=> w2 b2 w3 b3 /=.
      exact: const_ltb_trans.
    - move=> ne1; case: e2; case: e3; try done. move=> ne2 ne3 /=.
      exact: (nexp_ltb_trans ne1 ne3 ne2).
    - move=> ne1 ne2. case: e2; case: e3; try done. move=> ne3 ne4 ne5 ne6 /=.
      move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done. move=> ne3 ne4 ne5 ne6 /=.
      move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done. move=> ne3 ne4 ne5 ne6 /=.
      move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1. case: e2; case: e3; try done. move=> ne2 ne3 /=.
      exact: (nexp_ltb_trans ne1 ne3 ne2).
    - move=> ne1 ne2. case: e2; case: e3; try done. move=> ne3 ne4 ne5 ne6 /=.
      move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done. move=> ne3 ne4 ne5 ne6 /=.
      move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done. move=> ne3 ne4 ne5 ne6 /=.
      move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done. move=> ne3 ne4 ne5 ne6 /=.
      move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done. move=> ne3 ne4 ne5 ne6 /=.
      move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done. move=> ne3 ne4 ne5 ne6 /=.
      move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done. move=> ne3 ne4 ne5 ne6 /=.
      move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done. move=> ne3 ne4 ne5 ne6 /=.
      move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done. move=> ne3 ne4 ne5 ne6 /=.
      move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done. move=> ne3 ne4 ne5 ne6 /=.
      move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 i1 j1. case: e2; case: e3; try done. move=> ne2 i2 j2 ne3 i3 j3 /=.
      move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (ltn_trans b0 b) orbT.
      + by rewrite (eqP a0) (eqP a) (eqP b1) eqxx b orbT.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) -(eqP b0) eqxx b1 orbT.
      + by rewrite (eqP a0) (eqP a) (eqP b2) (eqP b0) 2!eqxx (ltn_trans b1 b) orbT.
    - move=> ne1 w1 w2 w3. case: e2; case: e3; try done.
      move=> ne2 w4 w5 w6 ne3 w7 w8 w9 /=. move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite (eqP a0) a.
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (ltn_trans b0 b) orbT.
      + by rewrite (eqP a0) (eqP a) (eqP b1) eqxx b orbT.
      + by rewrite (eqP a0) (eqP a) (eqP b1) (eqP b2) eqxx b orbT.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) -(eqP b0) eqxx b1 orbT.
      + by rewrite (eqP a0) (eqP a) (eqP b2) (eqP b0) 2!eqxx (ltn_trans b1 b) orbT.
      + by rewrite (eqP a0) (eqP a) (eqP b3) (eqP b2) (eqP b0) 2!eqxx b orbT.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) -(eqP b1) -(eqP b0) eqxx b2 orbT.
      + by rewrite (eqP a0) (eqP a) (eqP b3) (eqP b1) -(eqP b0) 2!eqxx b2 orbT.
      + by rewrite (eqP a0) (eqP a) (eqP b4) (eqP b3) (eqP b1) (eqP b0) 3!eqxx
                   (ltn_trans b2 b) orbT.
    - move=> ne1 w1. case: e2; case: e3; try done. move=> ne2 w2 ne3 w3 /=.
      move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (ltn_trans b0 b) orbT.
    - move=> ne1 w1. case: e2; case: e3; try done. move=> ne2 w2 ne3 w3 /=.
      move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (ltn_trans b0 b) orbT.
    - move=> ne1 w1. case: e2; case: e3; try done. move=> ne2 w2 ne3 w3 /=.
      move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (ltn_trans b0 b) orbT.
    - move=> ne1 w1. case: e2; case: e3; try done. move=> ne2 w2 ne3 w3 /=.
      move=> H1 H2. caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (ltn_trans b0 b) orbT.
    - move=> c1 ne1 ne2. case: e2; case: e3; try done.
      move=> c2 ne3 ne4 c3 ne5 ne6 /=. move=> H1 H2. caseb_hyps.
      + by rewrite (nbexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
      + by rewrite (eqP a0) (eqP a) (eqP b1) eqxx b orbT.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) -(eqP b0) eqxx b1 orbT.
      + by rewrite (eqP a0) (eqP a) (eqP b2) (eqP b0) 2!eqxx
                   (nexp_ltb_trans _ _ _ b1 b) orbT.
    (* nbexp_ltb_trans *)
    case: e1.
    - case: e2; case: e3; try done.
    - case: e2; case: e3; try done.
    - move=> ne1 ne2. case: e2; case: e3; try done.
      move=> ne3 ne4 ne5 ne6 /=. move=> H1 H2; caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done.
      move=> ne3 ne4 ne5 ne6 /=. move=> H1 H2; caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done.
      move=> ne3 ne4 ne5 ne6 /=. move=> H1 H2; caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done.
      move=> ne3 ne4 ne5 ne6 /=. move=> H1 H2; caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done.
      move=> ne3 ne4 ne5 ne6 /=. move=> H1 H2; caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done.
      move=> ne3 ne4 ne5 ne6 /=. move=> H1 H2; caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done.
      move=> ne3 ne4 ne5 ne6 /=. move=> H1 H2; caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done.
      move=> ne3 ne4 ne5 ne6 /=. move=> H1 H2; caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done.
      move=> ne3 ne4 ne5 ne6 /=. move=> H1 H2; caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done.
      move=> ne3 ne4 ne5 ne6 /=. move=> H1 H2; caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done.
      move=> ne3 ne4 ne5 ne6 /=. move=> H1 H2; caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done.
      move=> ne3 ne4 ne5 ne6 /=. move=> H1 H2; caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done.
      move=> ne3 ne4 ne5 ne6 /=. move=> H1 H2; caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done.
      move=> ne3 ne4 ne5 ne6 /=. move=> H1 H2; caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done.
      move=> ne3 ne4 ne5 ne6 /=. move=> H1 H2; caseb_hyps.
      + by rewrite (nexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1. case: e2; case: e3; try done.
      move=> ne2 ne3 /=. move=> H1 H2. exact: (nbexp_ltb_trans _ _ _ H1 H2).
    - move=> ne1 ne2. case: e2; case: e3; try done.
      move=> ne3 ne4 ne5 ne6 /=. move=> H1 H2; caseb_hyps.
      + by rewrite (nbexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nbexp_ltb_trans _ _ _ b0 b) orbT.
    - move=> ne1 ne2. case: e2; case: e3; try done.
      move=> ne3 ne4 ne5 ne6 /=. move=> H1 H2; caseb_hyps.
      + by rewrite (nbexp_ltb_trans _ _ _ a0 a).
      + by rewrite (eqP a0) a.
      + by rewrite -(eqP a) a0.
      + by rewrite (eqP a0) (eqP a) eqxx (nbexp_ltb_trans _ _ _ b0 b) orbT.
  Qed.

  Ltac eqb_ltb_gtb_caseb_auto :=
    caseb_hyps;
    repeat (match goal with
            | H : is_true (_ == _) |- _ => rewrite (eqP H) => {H}
            | H : is_true (nexp_ltb _ _) |- _ => rewrite {}H
            | H : is_true (nbexp_ltb _ _) |- _ => rewrite {}H
            | H : is_true (_ < _) |- _ => rewrite {}H
            end); repeat rewrite eqxx; repeat rewrite orbT; auto.

  Lemma nexp_eqb_ltb_gtb (e1 e2 : nexp) :
    (e1 == e2) || (nexp_ltb e1 e2) || (nexp_ltb e2 e1)
  with
  nbexp_eqb_ltb_gtb (e1 e2 : nbexp) :
    (e1 == e2) || (nbexp_ltb e1 e2) || (nbexp_ltb e2 e1).
  Proof.
    (* nexp_eqb_ltb_gtb *)
    case: e1.
    - move=> v1; case: e2 => /=; try eauto. move=> v2.
      case: (V.compare v1 v2) => H.
      + by rewrite H orbT.
      + by rewrite (eqP H) eqxx.
      + by rewrite H orbT.
    - move=> w1 b1; case: e2 => /=; try eauto. move=> w2 b2.
      move: (eqb_ltn_gtn_cases w1 w2) => H. caseb_hyps.
      + move: b1; rewrite (eqP a)=> b1. move: (eqb_ltB_gtB_cases b1 b2) => H.
        caseb_hyps.
        * by rewrite (eqP a0) eqxx.
        * by rewrite (ltB_const_ltb b) orbT.
        * by rewrite (ltB_const_ltb b) orbT.
      + by rewrite {1}/const_ltb b orbT.
      + by rewrite {2}/const_ltb b orbT.
    - move=> ne1. case: e2 => /=; try eauto. move=> ne2.
      move: (nexp_eqb_ltb_gtb ne1 ne2) => H. eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1. case: e2 => /=; try eauto. move=> ne2.
      move: (nexp_eqb_ltb_gtb ne1 ne2) => H. eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 i1 j1. case: e2 => /=; try eauto. move=> ne2 i2 j2.
      move: (nexp_eqb_ltb_gtb ne1 ne2) (eqb_ltn_gtn_cases i1 i2)
                                       (eqb_ltn_gtn_cases j1 j2)=> H1 H2 H3.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 w1 w2 w3. case: e2 => /=; try eauto. move=> ne2 w4 w5 w6.
      move: (nexp_eqb_ltb_gtb ne1 ne2) (eqb_ltn_gtn_cases w1 w4)
                                       (eqb_ltn_gtn_cases w2 w5)
                                       (eqb_ltn_gtn_cases w3 w6)=> H1 H2 H3 H4.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 w1. case: e2 => /=; try eauto. move=> ne2 w2.
      move: (nexp_eqb_ltb_gtb ne1 ne2) (eqb_ltn_gtn_cases w1 w2)=> H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 w1. case: e2 => /=; try eauto. move=> ne2 w2.
      move: (nexp_eqb_ltb_gtb ne1 ne2) (eqb_ltn_gtn_cases w1 w2)=> H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 w1. case: e2 => /=; try eauto. move=> ne2 w2.
      move: (nexp_eqb_ltb_gtb ne1 ne2) (eqb_ltn_gtn_cases w1 w2)=> H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 w1. case: e2 => /=; try eauto. move=> ne2 w2.
      move: (nexp_eqb_ltb_gtb ne1 ne2) (eqb_ltn_gtn_cases w1 w2)=> H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> c1 ne1 ne2. case: e2 => /=; try eauto. move=> c2 ne3 ne4.
      move: (nbexp_eqb_ltb_gtb c1 c2) (nexp_eqb_ltb_gtb ne1 ne3)
                                      (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2 H3.
      eqb_ltb_gtb_caseb_auto.
    (* nbexp_eq_lt_gt *)
    case: e1.
    - case: e2 => /=; try eauto.
    - case: e2 => /=; try eauto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nexp_eqb_ltb_gtb ne1 ne3) (nexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1. case: e2 => /=; try eauto. move=> ne2.
      move: (nbexp_eqb_ltb_gtb ne1 ne2)=> H. eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nbexp_eqb_ltb_gtb ne1 ne3) (nbexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
    - move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
      move: (nbexp_eqb_ltb_gtb ne1 ne3) (nbexp_eqb_ltb_gtb ne2 ne4) => H1 H2.
      eqb_ltb_gtb_caseb_auto.
  Qed.

  Fixpoint nexp_compare (e1 e2 : nexp) : Compare nexp_ltb nexp_eqb e1 e2
  with nbexp_compare (e1 e2 : nbexp) : Compare nbexp_ltb nbexp_eqb e1 e2.
  Proof.
    (* nexp_compare *)
    move: (nexp_eqb_ltb_gtb e1 e2). case H: (e1 == e2) => /=.
    - move=> _. apply: EQ. rewrite (eqP H). exact: nexp_eqb_refl.
    - move=> {H}. case H: (nexp_ltb e1 e2) => /=.
      + move=> _. apply: LT. exact: H.
      + move=> {H} H. apply: GT. exact: H.
    (* nbexp_compare *)
    move: (nbexp_eqb_ltb_gtb e1 e2). case H: (e1 == e2) => /=.
    - move=> _. apply: EQ. rewrite (eqP H). exact: nbexp_eqb_refl.
    - move=> {H}. case H: (nbexp_ltb e1 e2) => /=.
      + move=> _. apply: LT. exact: H.
      + move=> {H} H. apply: GT. exact: H.
  Defined.

  Module NexpOrderedMinimal : SsrOrderedTypeMinimal.
    Definition t := nexp_eqType.
    Definition eq (e1 e2 : t) : bool := e1 == e2.
    Definition lt (e1 e2 : t) : bool := nexp_ltb e1 e2.
    Lemma lt_trans : forall (e1 e2 e3 : t), lt e1 e2 -> lt e2 e3 -> lt e1 e3.
    Proof.
      exact: nexp_ltb_trans.
    Qed.
    Lemma lt_not_eq (e1 e2 : t) : lt e1 e2 -> e1 != e2.
    Proof.
      exact: nexp_ltb_not_eqb.
    Qed.
    Definition compare (e1 e2 : t) : Compare lt eq e1 e2 := nexp_compare e1 e2.
  End NexpOrderedMinimal.

  Module NexpOrdered := MakeSsrOrderedType NexpOrderedMinimal.

  Module NbexpOrderedMinimal : SsrOrderedTypeMinimal.
    Definition t := nbexp_eqType.
    Definition eq (e1 e2 : t) : bool := e1 == e2.
    Definition lt (e1 e2 : t) : bool := nbexp_ltb e1 e2.
    Lemma lt_trans : forall (e1 e2 e3 : t), lt e1 e2 -> lt e2 e3 -> lt e1 e3.
    Proof.
      exact: nbexp_ltb_trans.
    Qed.
    Lemma lt_not_eq (e1 e2 : t) : lt e1 e2 -> e1 != e2.
    Proof.
      exact: nbexp_ltb_not_eqb.
    Qed.
    Definition compare (e1 e2 : t) : Compare lt eq e1 e2 := nbexp_compare e1 e2.
  End NbexpOrderedMinimal.

  Module NbexpOrdered := MakeSsrOrderedType NbexpOrderedMinimal.

End Make.
