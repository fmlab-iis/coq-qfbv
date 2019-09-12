
From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.
From ssrlib Require Import Types SsrOrdered ZAriths FSets FMaps.
From BitBlasting Require Import Typ.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Delimit Scope var_scope with var.

(* Typed variables *)

Section Var.

  Local Open Scope var_scope.

  Record var : Set := mkVar { vname : N; vtyp : typ; vidx : N }.

  Definition vsize v := sizeof_typ (vtyp v).

  (* Strong equality *)

  Definition var_eqn (x y : var) : bool :=
    (vname x == vname y) && (vtyp x == vtyp y) && (vidx x == vidx y).

  Notation "x =? y" := (var_eqn x y) : var_scope.

  Lemma var_eqn_eq (x y : var) : x = y <-> var_eqn x y.
  Proof.
    destruct x; destruct y; split; rewrite /var_eqn /=.
    - move=> [] -> -> ->. by rewrite !eqxx.
    - move=> /andP [/andP [/eqP -> /eqP ->] /eqP ->]. reflexivity.
  Qed.

  Lemma var_eqP : forall (x y : var), reflect (x = y) (var_eqn x y).
  Proof.
    move=> x y. case H: (var_eqn x y).
    - apply: ReflectT. apply/var_eqn_eq. assumption.
    - apply: ReflectF. move=> Heq. move/var_eqn_eq: Heq => Heq. rewrite Heq in H.
      discriminate.
  Qed.

  Definition var_eqMixin := EqMixin var_eqP.
  Canonical var_eqType := Eval hnf in EqType var var_eqMixin.

  Lemma var_eqn_vname (x y : var) : x == y -> vname x = vname y.
  Proof. by move=> /andP [/andP [/eqP -> _] _]. Qed.

  Lemma var_eqn_vtyp (x y : var) : x == y -> vtyp x = vtyp y.
  Proof. by move=> /andP [/andP [_ /eqP ->] _]. Qed.

  Lemma var_eqn_vidx (x y : var) : x == y -> vidx x = vidx y.
  Proof. by move=> /andP [/andP [_ _] /eqP ->]. Qed.

  Lemma var_neq_case (x y : var) :
    x != y = (vname x != vname y) || (vtyp x != vtyp y) || (vidx x != vidx y).
  Proof.
    destruct x; destruct y => /=.
    case H: ((vname0 != vname1) || (vtyp0 != vtyp1) || (vidx0 != vidx1)).
    - case/orP: H; first case/orP.
      + move=> H. apply/negP => /eqP [] Hn Ht Hi. rewrite Hn eqxx in H. discriminate.
      + move=> H. apply/negP => /eqP [] Hn Ht Hi. rewrite Ht eqxx in H. discriminate.
      + move=> H. apply/negP => /eqP [] Hn Ht Hi. rewrite Hi eqxx in H. discriminate.
    - move: (Bool.orb_false_elim _ _ H) => {H} [H /negPn Hi].
      move: (Bool.orb_false_elim _ _ H) => {H} [/negPn Hn /negPn Ht].
      apply/negPn/eqP. by rewrite (eqP Hn) (eqP Ht) (eqP Hi); reflexivity.
  Qed.

  Definition var_ltn (x y : var) : bool :=
    (vname x <? vname y)%num
    || (vname x == vname y) && (vtyp x <? vtyp y)%typ
    || (vname x == vname y) && (vtyp x == vtyp y)%typ && (vidx x <? vidx y)%num.

  Notation "x <? y" := (var_ltn x y).

  Lemma var_ltnn (x : var) : (x <? x) = false.
  Proof.
    destruct x; rewrite /var_ltn /=. rewrite !Nltnn !eqxx typ_ltnn. reflexivity.
  Qed.

  Lemma var_ltn_eqF (x y : var) : x <? y -> (x == y) = false.
  Proof.
    move=> Hlt. apply/negP=> /eqP Heq. rewrite Heq var_ltnn in Hlt. discriminate.
  Qed.

  Lemma var_ltn_trans (x y z : var) : x <? y -> y <? z -> x <? z.
  Proof.
    destruct x; destruct y; destruct z; rewrite /var_ltn => /=. move=> Hxy Hyz.
    case/orP: Hxy; first case/orP; case/orP: Hyz; first case/orP.
    - move=> Hn12 Hn01. by rewrite (Nltn_trans Hn01 Hn12).
    - move/andP=> [Hn12 Ht12] Hn01. rewrite (eqP Hn12) in Hn01. by rewrite Hn01.
    - move=> /andP [/andP [Hn12 Ht12] Hv12] Hv01. rewrite (eqP Hn12) in Hv01.
      by rewrite Hv01.
    - move=> Hn12 /andP [Hn01 Ht01]. case/orP: Hn12.
      + move=> Hn12. by rewrite (eqP Hn01) Hn12.
      + move/andP=> [Hn12 Ht12]. rewrite (eqP Hn01) (eqP Hn12) eqxx.
        by rewrite (typ_ltn_trans Ht01 Ht12) orbT.
    - move=> /andP [/andP [Hn12 Ht12] Hi12] /andP [Hn01 Ht01].
      rewrite (eqP Hn01) (eqP Hn12) eqxx. rewrite (eqP Ht12) in Ht01.
      by rewrite Ht01 orbT.
    - case/orP; [move=> Hn12 | move=> /andP [Hn12 Ht12]];
        move=> /andP [/andP [Hn01 Ht01] Hi01].
      + by rewrite (eqP Hn01) Hn12.
      + by rewrite (eqP Hn01) (eqP Hn12) eqxx (eqP Ht01) Ht12 orbT.
    - move=> /andP [/andP [Hn12 Ht12] Hi12] /andP [/andP [Hn01 Ht01] Hi01].
        by rewrite (eqP Hn01) (eqP Hn12) (eqP Ht01) (eqP Ht12) !eqxx
                   (Nltn_trans Hi01 Hi12) orbT.
  Qed.

  Lemma var_ltn_neqAlt (x y : var) : x <? y = (x != y) && ~~ (y <? x).
  Proof.
    destruct x; destruct y; rewrite /var_ltn => /=. rewrite var_neq_case /=.
    rewrite negb_or negb_and. rewrite (eq_sym vname1 vname0).
    case Hnne01: (vname0 == vname1) => /=.
    - rewrite (eqP Hnne01) => {Hnne01}. rewrite Nltnn /=.
      rewrite (eq_sym vtyp1 vtyp0). case Htne01: (vtyp0 == vtyp1) => /=.
      + rewrite (eqP Htne01) => {Htne01}. rewrite typ_ltnn /=. exact: Nltn_neqAlt.
      + rewrite typ_ltn_neqAlt orbF. move/idP/negP: Htne01 => ->. by rewrite andbT.
    - rewrite !orbF andbT. rewrite Nltn_neqAlt. by move/idP/negP: Hnne01 => ->.
  Qed.

  Lemma var_neq_ltn (x y : var) : (x != y) = (x <? y) || (y <? x).
  Proof.
    case Heq: (x == y).
    - rewrite (eqP Heq) var_ltnn. reflexivity.
    - case Hlt: (x <? y) => //=.
      symmetry. by rewrite var_ltn_neqAlt eq_sym Heq Hlt.
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

Module VarOrderedMinimal : SsrOrderedTypeMinimal.
  Definition t := var_eqType.
  Definition eqn (x y : t) := x == y.
  Definition ltn := var_ltn.
  Definition ltn_trans := var_ltn_trans.
  Lemma ltn_not_eqn (x y : t) : ltn x y -> x != y.
  Proof. move=> H. rewrite (var_ltn_eqF H). done. Qed.
  Definition compare := var_compare.
End VarOrderedMinimal.
Module VarOrder <: SsrOrderedTypeWithFacts := MakeSsrOrderedType VarOrderedMinimal.

Module VS := MakeTreeSet VarOrder.
Module VM := MakeTreeMap VarOrder.



(* Untyped variables *)

Definition var_untyped v := (vname v, vidx v).

Coercion var_untyped : var >-> prod.

Module UVarOrder <: SsrOrderedTypeWithFacts := MakeProdOrdered NOrder NOrder.

Module UVS := MakeTreeSet UVarOrder.
Module UVM := MakeTreeMap UVarOrder.

Section UntypedVar.

  Local Open Scope var_scope.

  (* Weak equality *)

  Definition uvar_eqn (x y : var) : bool := var_untyped x == var_untyped y.

  Infix "=??" := uvar_eqn (at level 70) : var_scope.

  Notation "x !=?? y" := (~~ (uvar_eqn x y)) (at level 70, no associativity) : var_scope.

  Lemma uvar_eqn_case (x y : var) :
    (x =?? y) = (vname x == vname y) && (vidx x == vidx y).
  Proof.
    case: x => nx tx ix; case: y => ny ty iy /=. case H: ((nx == ny) && (ix == iy)).
    - move/andP: H=> [/eqP -> /eqP ->]. exact: eqxx.
    - case: (Bool.andb_false_elim _ _ H) => {H} H.
      + apply/negP => /eqP [] Hn Hi; subst. by rewrite eqxx in H.
      + apply/negP => /eqP [] Hn Hi; subst. by rewrite eqxx in H.
  Qed.

  Lemma uvar_eqn_vname (x y : var) : x =?? y -> vname x = vname y.
  Proof. by rewrite uvar_eqn_case => /andP [/eqP -> _]. Qed.

  Lemma uvar_eqn_vidx x y : x =?? y -> vidx x = vidx y.
  Proof. by rewrite uvar_eqn_case => /andP [_ /eqP ->]. Qed.

  Lemma uvar_neq_case (x y : var) :
    x !=?? y = (vname x != vname y) || (vidx x != vidx y).
  Proof. by rewrite uvar_eqn_case negb_and. Qed.

  Lemma uvar_eqn_refl (x : var) : x =?? x.
  Proof. exact: eqxx. Qed.

  Lemma uvar_eqn_sym (x y : var) : (x =?? y) = (y =?? x).
  Proof. by rewrite /uvar_eqn eq_sym. Qed.

  Lemma uvar_eqn_symmetric (x y : var) : (x =?? y) -> (y =?? x).
  Proof. by rewrite uvar_eqn_sym. Qed.

  Lemma uvar_eqn_trans (x y z : var) : x =?? y -> y =?? z -> x =?? z.
  Proof. move=> /eqP H1 /eqP H2. by rewrite /uvar_eqn H1 H2. Qed.

  Global Instance uvar_eqn_Reflexive : Reflexive (@uvar_eqn) := @uvar_eqn_refl.
  Global Instance uvar_eqn_Symmetric : Symmetric (@uvar_eqn) := @uvar_eqn_symmetric.
  Global Instance uvar_eqn_Transitive : Transitive (@uvar_eqn) := @uvar_eqn_trans.
  Instance uvar_eqn_Equivalence : Equivalence uvar_eqn :=
    { Equivalence_Reflexive := uvar_eqn_Reflexive;
      Equivalence_Symmetric := uvar_eqn_Symmetric;
      Equivalence_Transitive := uvar_eqn_Transitive }.

  Definition uvar_ltn (x y : var) : bool := UVarOrder.ltn x y.

  Infix "<??" := uvar_ltn (at level 70) : var_scope.

  Lemma uvar_ltnn (x : var) : (x <?? x) = false.
  Proof. exact: UVarOrder.ltnn. Qed.

  Lemma uvar_ltn_weqF (x y : var) : x <?? y -> x =?? y = false.
  Proof. exact: UVarOrder.ltn_eqF. Qed.

  Lemma uvar_ltn_trans (x y z : var) : x <?? y -> y <?? z -> x <?? z.
  Proof. exact: UVarOrder.ltn_trans. Qed.

  Lemma uvar_ltn_wneqAlt (x y : var) : x <?? y = (x !=?? y) && ~~ (y <?? x).
  Proof. exact: UVarOrder.ltn_neqAlt. Qed.

  Lemma uvar_neq_wltn (x y : var) : (x !=?? y) = (x <?? y) || (y <?? x).
  Proof. exact: UVarOrder.neq_ltn. Qed.

  Definition uvar_compare (x y : var) : Compare uvar_ltn uvar_eqn x y.
  Proof.
    case: (UVarOrder.compare x y) => H.
    - apply: LT. exact: H.
    - apply: EQ. exact: H.
    - apply: GT. exact: H.
  Defined.

End UntypedVar.

Infix "=??" := uvar_eqn (at level 70) : var_scope.
Notation "x !=?? y" := (~~ (uvar_eqn x y)) (at level 70, no associativity) : var_scope.
Infix "<??" := uvar_ltn (at level 70) : var_scope.
