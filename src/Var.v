
From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.
From ssrlib Require Import Types SsrOrdered ZAriths FSets FMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Delimit Scope var_scope with var.

(* Typed variables *)

Section Var.

  Local Open Scope var_scope.

  Record var : Set := mkVar { vname : N; vidx : N }.

  (* Strong equality *)

  Definition var_eqn (x y : var) : bool := (vname x == vname y) && (vidx x == vidx y).

  Notation "x =? y" := (var_eqn x y) : var_scope.

  Lemma var_eqn_eq (x y : var) : x = y <-> x =? y.
  Proof.
    destruct x; destruct y; split; rewrite /var_eqn /=.
    - move=> [] -> ->. by rewrite !eqxx.
    - move=> /andP [/eqP -> /eqP ->]. reflexivity.
  Qed.

  Lemma var_eqP : forall (x y : var), reflect (x = y) (x =? y).
  Proof.
    move=> x y. case H: (var_eqn x y).
    - apply: ReflectT. apply/var_eqn_eq. assumption.
    - apply: ReflectF. move=> Heq. move/var_eqn_eq: Heq => Heq. rewrite Heq in H.
      discriminate.
  Qed.

  Definition var_eqMixin := EqMixin var_eqP.
  Canonical var_eqType := Eval hnf in EqType var var_eqMixin.

  Lemma var_eqn_vname (x y : var) : x == y -> vname x = vname y.
  Proof. by move=> /andP [/eqP -> _]. Qed.

  Lemma var_eqn_vidx (x y : var) : x == y -> vidx x = vidx y.
  Proof. by move=> /andP [_ /eqP ->]. Qed.

  Lemma var_neq_case (x y : var) : x != y = (vname x != vname y) || (vidx x != vidx y).
  Proof.
    case: x => nx ix; case: y => ny iy /=. case H: ((nx != ny) || (ix != iy)).
    - case/orP: H.
      + move=> H. apply/negP => /eqP [] Hn Hi. rewrite Hn eqxx in H. discriminate.
      + move=> H. apply/negP => /eqP [] Hn Hi. rewrite Hi eqxx in H. discriminate.
    - move: (Bool.orb_false_elim _ _ H) => {H} [/negPn Hn /negPn Hi].
      apply/negPn/eqP. by rewrite (eqP Hn) (eqP Hi); reflexivity.
  Qed.

  Definition var_ltn (x y : var) : bool :=
    (vname x <? vname y)%num || (vname x == vname y) && (vidx x <? vidx y)%num.

  Notation "x <? y" := (var_ltn x y).

  Lemma var_ltnn (x : var) : (x <? x) = false.
  Proof. case x=> *; rewrite /var_ltn /=. rewrite !Nltnn !eqxx. reflexivity. Qed.

  Lemma var_ltn_eqF (x y : var) : x <? y -> (x == y) = false.
  Proof.
    move=> Hlt. apply/negP=> /eqP Heq. rewrite Heq var_ltnn in Hlt. discriminate.
  Qed.

  Lemma var_ltn_trans (x y z : var) : x <? y -> y <? z -> x <? z.
  Proof.
    case: x => nx ix; case: y => ny iy; case: z => nz iz;
      rewrite /var_ltn => /=. move=> Hxy Hyz.
    case/orP: Hxy; case/orP: Hyz.
    - move=> Hnyz Hnxy. by rewrite (Nltn_trans Hnxy Hnyz).
    - move/andP=> [Hnyz Hiyz] Hnxy. rewrite (eqP Hnyz) in Hnxy. by rewrite Hnxy.
    - move=> Hnyz /andP [Hnxy Hixy]. rewrite (eqP Hnxy). by rewrite Hnyz.
    - move=> /andP [Hnyz Hiyz] /andP [Hnxy Hixy].
      by rewrite (eqP Hnxy) (eqP Hnyz) eqxx (Nltn_trans Hixy Hiyz) orbT.
  Qed.

  Lemma var_ltn_neqAlt (x y : var) : x <? y = (x != y) && ~~ (y <? x).
  Proof.
    case: x => nx ix; case: y => ny iy; rewrite /var_ltn => /=.
    rewrite var_neq_case /=. rewrite negb_or negb_and. rewrite (eq_sym ny nx).
    case Hnxy: (nx == ny) => /=.
    - rewrite (eqP Hnxy) => {Hnxy}. rewrite Nltnn /=. case Hixy: (ix == iy) => /=.
      + rewrite (eqP Hixy) => {Hixy}. exact: Nltnn.
      + rewrite Nltn_neqAlt. move/idP/negP: Hixy => -> /=. reflexivity.
    - rewrite orbF andbT. rewrite Nltn_neqAlt. by move/idP/negP: Hnxy => ->.
  Qed.

  Lemma var_neq_ltn (x y : var) : (x != y) = (x <? y) || (y <? x).
  Proof.
    case Heq: (x == y).
    - rewrite (eqP Heq) var_ltnn. reflexivity.
    - case Hlt: (x <? y) => //=. symmetry. by rewrite var_ltn_neqAlt eq_sym Heq Hlt.
  Qed.

  Definition var_compare (x y : var) : Compare var_ltn eq_op x y.
  Proof.
    case Heq: (x == y); last case Hlt: (x <? y).
    - exact: (EQ Heq).
    - exact: (LT Hlt).
    - move/idP/negP: Heq. rewrite var_neq_ltn Hlt orFb => Hgt. exact: (GT Hgt).
  Defined.

End Var.

Notation "x =? y" := (var_eqn x y) : var_scope.
Notation "x <? y" := (var_ltn x y) : var_scope.

Module VarOrderedMinimal <: SsrOrderedTypeMinimal.
  Definition t := var_eqType.
  Definition eqn (x y : t) := x == y.
  Definition ltn := var_ltn.
  Definition ltn_trans := var_ltn_trans.
  Lemma ltn_not_eqn (x y : t) : ltn x y -> x != y.
  Proof. move=> H. rewrite (var_ltn_eqF H). done. Qed.
  Definition compare := var_compare.
End VarOrderedMinimal.
Module VarOrder <: SsrOrderedTypeWithFacts := MakeSsrOrderedType VarOrderedMinimal.

Module VarOrderWithDefaultNew <: SsrOrderedWithDefaultSucc.
  Include VarOrder.
  Definition default : t := {| vname := 1; vidx := 1 |}.
  Definition succ (x : t) : t := {| vname := vname x + 1; vidx := 1 |}.
  Lemma ltn_succ (x : t) : ltn x (succ x).
  Proof.
    case: x => [n i]. rewrite /succ /ltn /VarOrderedMinimal.ltn /var_ltn /=.
      by rewrite NltnSn orTb.
  Qed.
End VarOrderWithDefaultNew.

Module VS := MakeTreeSetWithNew VarOrderWithDefaultNew.
Module VM := MakeTreeMapWithNew VarOrderWithDefaultNew.
