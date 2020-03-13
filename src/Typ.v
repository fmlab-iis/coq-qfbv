
From Coq Require Import Arith RelationClasses OrderedType.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Typ.

  (* Types *)

  Inductive typ : Set :=
    Tuint : nat -> typ
  | Tsint : nat -> typ.



  (* Size of types *)

  Definition sizeof_typ (t : typ) : nat :=
    match t with
    | Tuint w => w
    | Tsint w => w
    end.



  (* Equality of types *)

  Lemma typ_eq_dec (x y : typ) : {x = y} + {x <> y}.
  Proof.
    destruct x; destruct y.
    - case: (Nat.eq_dec n n0) => H.
      + left; rewrite H; reflexivity.
      + right; move=> []; exact: H.
    - right; move=> H; discriminate.
    - right; move=> H; discriminate.
    -case: (Nat.eq_dec n n0) => H.
     + left; rewrite H; reflexivity.
     + right; move=> []; exact: H.
  Qed.

  Definition typ_eqn (x y : typ) : bool :=
    match x, y with
    | Tuint wx, Tuint wy => wx == wy
    | Tsint wx, Tsint wy => wx == wy
    | _, _ => false
    end.

  Notation "x =? y" := (typ_eqn x y).

  Lemma typ_eqn_refl (x : typ) : x =? x.
  Proof.
    destruct x; exact: eqxx.
  Qed.

  Lemma typ_eqn_eq (x y : typ) : x =? y <-> x = y.
  Proof.
    split; first (destruct x; destruct y; move=> /= H).
    - rewrite (eqP H); reflexivity.
    - discriminate.
    - discriminate.
    - rewrite (eqP H); reflexivity.
    - move=> ->. exact: typ_eqn_refl.
  Qed.

  Lemma typ_eqn_sym (x y : typ) : x =? y -> y =? x.
  Proof.
    move/typ_eqn_eq => H. apply/typ_eqn_eq. symmetry. assumption.
  Qed.

  Lemma typ_eqn_trans (x y z : typ) : x =? y -> y =? z -> x =? z.
  Proof.
    move/typ_eqn_eq => Hxy. move/typ_eqn_eq => Hyz. apply/typ_eqn_eq.
    rewrite Hxy. assumption.
  Qed.

  Instance typ_eqn_Reflexive : Reflexive (@typ_eqn) := @typ_eqn_refl.
  Instance typ_eqn_Symmetric : Symmetric (@typ_eqn) := @typ_eqn_sym.
  Instance typ_eqn_Transitive : Transitive (@typ_eqn) := @typ_eqn_trans.
  Instance typ_eqn_Equivalence : Equivalence (@typ_eqn) :=
    { Equivalence_Reflexive := typ_eqn_Reflexive;
      Equivalence_Symmetric := typ_eqn_Symmetric;
      Equivalence_Transitive := typ_eqn_Transitive }.

  Lemma typ_eqP : forall (x y : typ), reflect (x = y) (x =? y).
  Proof.
    move=> x y. case H: (x =? y).
    - apply: ReflectT. apply/typ_eqn_eq. assumption.
    - apply: ReflectF. move=> Heq. move/typ_eqn_eq: Heq => Heq. rewrite Heq in H.
      discriminate.
  Qed.

  Definition typ_eqMixin := EqMixin typ_eqP.
  Canonical typ_eqType := Eval hnf in EqType typ typ_eqMixin.

  Lemma typ_eqn_size (t1 t2 : typ) : t1 == t2 -> sizeof_typ t1 = sizeof_typ t2.
  Proof.
    destruct t1; destruct t2; move/eqP=> H; try discriminate.
    - case: H => ->. reflexivity.
    - case: H => ->. reflexivity.
  Qed.

  Definition typ_ltn (t1 t2 : typ) : bool :=
    match t1, t2 with
    | Tuint n, Tuint m => n < m
    | Tuint _, Tsint _ => true
    | Tsint _, Tuint _ => false
    | Tsint n, Tsint m => n < m
    end.

  Notation "x <? y" := (typ_ltn x y).

  Lemma typ_ltnn (t : typ) : (t <? t) = false.
  Proof. destruct t => /=; by rewrite ltnn. Qed.

  Lemma typ_ltn_eqF (t1 t2 : typ) : t1 <? t2 -> t1 == t2 = false.
  Proof.
    move=> Hlt; apply/negP => /eqP Heq; rewrite Heq typ_ltnn in Hlt; discriminate.
  Qed.

  Lemma typ_ltn_trans (t1 t2 t3 : typ) : t1 <? t2 -> t2 <? t3 -> t1 <? t3.
  Proof.
    destruct t1; destruct t2; destruct t3 => //=.
    - move=> H1 H2. exact: (ltn_trans H1 H2).
    - move=> H1 H2. exact: (ltn_trans H1 H2).
  Qed.

  Lemma typ_ltn_neqAlt (t1 t2 : typ) : t1 <? t2 = (t1 != t2) && ~~ (t2 <? t1).
  Proof.
    destruct t1; destruct t2 => //=.
    - rewrite {1}ltn_neqAle leqNgt. apply: andb_id2r => H. case Heq: (n == n0).
      + rewrite (eqP Heq) eqxx. reflexivity.
      + symmetry => /=. apply/eqP => H1. apply/negPf: Heq. by case: H1 => ->.
    - rewrite {1}ltn_neqAle leqNgt. apply: andb_id2r => H. case Heq: (n == n0).
      + rewrite (eqP Heq) eqxx. reflexivity.
      + symmetry => /=. apply/eqP => H1. apply/negPf: Heq. by case: H1 => ->.
  Qed.

  Lemma typ_neq_ltn (t1 t2 : typ) : (t1 != t2) = (t1 <? t2) || (t2 <? t1).
  Proof.
    case H: (t1 == t2).
    - rewrite (eqP H) typ_ltnn. reflexivity.
    - case H12: (t1 <? t2).
      + reflexivity.
      + symmetry => /=. rewrite typ_ltn_neqAlt eq_sym H H12. reflexivity.
  Qed.

  Definition compare (t1 t2 : typ) : Compare typ_ltn typ_eqn t1 t2.
  Proof.
    case Hlt: (t1 <? t2).
    - exact: (LT Hlt).
    - case Heq: (t1 == t2).
      + exact: (EQ Heq).
      + apply: GT. rewrite typ_ltn_neqAlt Hlt eq_sym Heq. done.
  Defined.



  (* Other functions *)

  (* A bit type is an unsigned type of size 1 *)
  Definition Tbit := Tuint 1.

  Definition is_unsigned (ty : typ) : bool :=
    match ty with
    | Tuint _ => true
    | _ => false
    end.

  Definition is_signed (ty : typ) : bool :=
    match ty with
    | Tsint _ => true
    | _ => false
    end.

  Lemma not_signed_is_unsigned ty : ~~ is_signed ty = is_unsigned ty.
  Proof. by case: ty. Qed.

  Lemma not_unsigned_is_signed ty : ~~ is_unsigned ty = is_signed ty.
  Proof. by case: ty. Qed.

  Definition unsigned_typ (ty : typ) : typ :=
    match ty with
    | Tuint w
    | Tsint w => Tuint w
    end.

  Definition double_typ (ty : typ) : typ :=
    match ty with
    | Tuint w => Tuint (2 * w)
    | Tsint w => Tsint (2 * w)
    end.

  Definition compatible (t1 t2 : typ) : bool :=
    sizeof_typ t1 == sizeof_typ t2.

  Definition tcast (bs : bits) (fty : typ) (tty : typ) : bits :=
    match fty with
    | Tuint w => ucastB bs (sizeof_typ tty)
    | Tsint w => scastB bs (sizeof_typ tty)
    end.

  Lemma size_unsigned_typ ty : sizeof_typ (unsigned_typ ty) = sizeof_typ ty.
  Proof. case ty; done. Qed.

  Lemma size_double_typ ty : sizeof_typ (double_typ ty) = 2 * (sizeof_typ ty).
  Proof. by case: ty. Qed.

  Lemma size_tcast bs s t : size (tcast bs s t) = sizeof_typ t.
  Proof.
    by rewrite /tcast; case s => _; [rewrite size_ucastB // | rewrite size_scastB //].
  Qed.

End Typ.

Delimit Scope typ_scope with typ.

Notation "x =? y" := (typ_eqn x y) : typ_scope.
Notation "x <? y" := (typ_ltn x y) : typ_scope.
