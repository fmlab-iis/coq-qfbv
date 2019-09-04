
From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.
From ssrlib Require Import Types SsrOrdered ZAriths FSets FMaps.
From BitBlasting Require Import Typ.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Section Var.

  Record var : Set := mkVar { vname :> N; vtyp : typ }.

  Definition vsize v := sizeof_typ (vtyp v).

  Definition var_eqn (x y : var) : bool := (vname x == vname y) && (vtyp x == vtyp y).

  Lemma var_eqn_eq (x y : var) : x = y <-> var_eqn x y.
  Proof.
    destruct x; destruct y; split; rewrite /var_eqn /=.
    - move=> [] -> ->. by rewrite !eqxx.
    - move/andP => [/eqP -> /eqP ->]. reflexivity.
  Qed.

  Notation "x =? y" := (var_eqn x y).

  Lemma var_eqP : forall (x y : var), reflect (x = y) (x =? y).
  Proof.
    move=> x y. case H: (x =? y).
    - apply: ReflectT. apply/var_eqn_eq. assumption.
    - apply: ReflectF. move=> Heq. move/var_eqn_eq: Heq => Heq. rewrite Heq in H.
      discriminate.
  Qed.

  Definition var_eqMixin := EqMixin var_eqP.
  Canonical var_eqType := Eval hnf in EqType var var_eqMixin.

  Lemma var_eqn_vname (x y : var) : x == y -> vname x = vname y.
  Proof. destruct x; destruct y => /=. move/eqP=> H. by case: H. Qed.

  Lemma var_eqn_vtyp (x y : var) : x == y -> vtyp x = vtyp y.
  Proof. destruct x; destruct y => /=. move/eqP=> H. by case: H. Qed.

  Lemma var_neq_case (x y : var) : x != y = (vname x != vname y) || (vtyp x != vtyp y).
  Proof.
    destruct x; destruct y => /=. case H: ((vname0 != vname1) || (vtyp0 != vtyp1)).
    - case/orP: H.
      + move=> H. apply/negP => /eqP [] Hn Ht. rewrite Hn eqxx in H. discriminate.
      + move=> H. apply/negP => /eqP [] Hn Ht. rewrite Ht eqxx in H. discriminate.
    - move: (Bool.orb_false_elim _ _ H) => {H} [/negPn Hn /negPn Ht].
      apply/negPn/eqP. by rewrite (eqP Hn) (eqP Ht); reflexivity.
  Qed.

  Definition var_ltn (x y : var) : bool :=
    (vname x <? vname y)%num || (vname x == vname y) && (vtyp x <? vtyp y)%typ.

  Notation "x <? y" := (var_ltn x y).

  Lemma var_ltnn (x : var) : (x <? x) = false.
  Proof.
    destruct x; rewrite /var_ltn /=. rewrite Nltnn eqxx typ_ltnn. reflexivity.
  Qed.

  Lemma var_ltn_eqF (x y : var) : x <? y -> x == y = false.
  Proof.
    move=> Hlt. apply/negP=> /eqP Heq. rewrite Heq var_ltnn in Hlt. discriminate.
  Qed.

  Lemma var_ltn_trans (x y z : var) : x <? y -> y <? z -> x <? z.
  Proof.
    destruct x; destruct y; destruct z; rewrite /var_ltn => /=. move=> Hxy Hyz.
    case/orP: Hxy; case/orP: Hyz.
    - move=> Hn12 Hn01. by rewrite (Nltn_trans Hn01 Hn12).
    - move/andP=> [Hn12 Ht12] Hn01. rewrite (eqP Hn12) in Hn01. by rewrite Hn01.
    - move=> Hn12 /andP [Hn01 Ht01]. by rewrite (eqP Hn01) Hn12.
    - move=> /andP [Hn12 Ht12] /andP [Hn01 Ht01]. rewrite (eqP Hn01) (eqP Hn12) eqxx.
      rewrite (typ_ltn_trans Ht01 Ht12). by rewrite orbT.
  Qed.

  Lemma var_ltn_neqAlt (x y : var) : x <? y = (x != y) && ~~ (y <? x).
  Proof.
    destruct x; destruct y; rewrite /var_ltn => /=. rewrite var_neq_case /=.
    rewrite negb_or negb_and. rewrite (eq_sym vname1 vname0).
    case Hneq01: (vname0 == vname1) => /=.
    - rewrite (eqP Hneq01) => {Hneq01}. rewrite Nltnn /=. exact: typ_ltn_neqAlt.
    - rewrite orbF andbT. rewrite Nltn_neqAlt. move/idP/negP: Hneq01 => ->.
      reflexivity.
  Qed.

  Lemma var_neq_ltn (x y : var) : (x != y) = (x <? y) || (y <? x).
  Proof.
    case Heq: (x == y).
    - rewrite (eqP Heq) var_ltnn. reflexivity.
    - case Hlt: (x <? y).
      + reflexivity.
      + symmetry => /=. rewrite var_ltn_neqAlt eq_sym Heq Hlt. reflexivity.
  Qed.

  Definition var_compare (x y : var) : Compare var_ltn eq_op x y.
  Proof.
    case Heq: (x == y); last case Hlt: (x <? y).
    - exact: (EQ Heq).
    - exact: (LT Hlt).
    - move/idP/negP: Heq. rewrite var_neq_ltn Hlt orFb => Hgt. exact: (GT Hgt).
  Defined.

End Var.

Module VarOrderedMinimal : SsrOrderedTypeMinimal.
  Definition t := var_eqType.
  Definition eq (x y : t) := x == y.
  Definition lt := var_ltn.
  Definition lt_trans := var_ltn_trans.
  Lemma lt_not_eq (x y : t) : lt x y -> x != y.
  Proof. move=> H. rewrite (var_ltn_eqF H). done. Qed.
  Definition compare := var_compare.
End VarOrderedMinimal.

Module VarOrder := MakeSsrOrderedType VarOrderedMinimal.

Module VS := MakeTreeSet NOrder.
Module VM := MakeTreeMap NOrder.

Delimit Scope var_scope with var.

Notation "x =? y" := (var_eqn x y) : var_scope.
Notation "x <? y" := (var_ltn x y) : var_scope.
