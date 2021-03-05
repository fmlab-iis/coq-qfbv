
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Var Types SsrOrder Store ZAriths FMaps.
From BitBlasting Require Import Typ TypEnv.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module BitsValueType <: HasDefaultTyp.
  Definition t : Type := bits.
  Definition default : t := [::].
End BitsValueType.

Module ZValueType <: HasDefaultTyp.
  Definition t : Type := Z.
  Definition default : t := 0%Z.
End ZValueType.

Module Type BitsStore (V : SsrOrder) (TE : TypEnv with Module SE := V).

  Module Lemmas := FMapLemmas TE.

  Local Notation var := V.t.
  Local Notation value := bits.

  Parameter t : Type.
  Parameter acc : var -> t -> value.
  Parameter upd : var -> value -> t -> t.
  Parameter upd2 : var -> value -> var -> value -> t -> t.
  Parameter acc_upd_eq : forall {x y v s}, x == y -> acc x (upd y v s) = v.
  Parameter acc_upd_neq : forall {x y v s}, x != y -> acc x (upd y v s) = acc x s.
  Parameter acc_upd2_eq1 :
    forall {x y1 v1 y2 v2 s},
      x == y1 -> x != y2 -> acc x (upd2 y1 v1 y2 v2 s) = v1.
  Parameter acc_upd2_eq2 :
    forall {x y1 v1 y2 v2 s},
      x == y2 -> acc x (upd2 y1 v1 y2 v2 s) = v2.
  Parameter acc_upd2_neq :
    forall {x y1 v1 y2 v2 s},
      x != y1 -> x != y2 -> acc x (upd2 y1 v1 y2 v2 s) = acc x s.
  Parameter Upd : var -> value -> t -> t -> Prop.
  Definition Upd2 x1 v1 x2 v2 (s1 s2 : t) : Prop :=
    forall y, acc y s2 = acc y (upd x2 v2 (upd x1 v1 s1)).
  Parameter Equal : t -> t -> Prop.
  Parameter Upd_upd : forall x v s, Upd x v s (upd x v s).
  Parameter Upd2_upd :
    forall x1 v1 x2 v2 s, Upd2 x1 v1 x2 v2 s (upd x2 v2 (upd x1 v1 s)).
  Parameter Upd2_upd2 : forall x1 v1 x2 v2 s, Upd2 x1 v1 x2 v2 s (upd2 x1 v1 x2 v2 s).
  Parameter acc_Upd_eq : forall x y v s1 s2, x == y -> Upd y v s1 s2 -> acc x s2 = v.
  Parameter acc_Upd_neq :
    forall x y v s1 s2, x != y -> Upd y v s1 s2 -> acc x s2 = acc x s1.
  Parameter acc_Upd2_eq1 :
    forall x y1 v1 y2 v2 s1 s2,
      x == y1 -> x != y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = v1.
  Parameter acc_Upd2_eq2 :
    forall x y1 v1 y2 v2 s1 s2, x == y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = v2.
  Parameter acc_Upd2_neq :
    forall x y1 v1 y2 v2 s1 s2,
      x != y1 -> x != y2 -> Upd2 y1 v1 y2 v2 s1 s2 -> acc x s2 = acc x s1.
  Parameter Equal_def :
    forall s1 s2,
      Equal s1 s2 <-> (forall v, acc v s1 = acc v s2).
  Parameter Equal_refl : forall s, Equal s s.
  Parameter Equal_sym : forall s1 s2, Equal s1 s2 -> Equal s2 s1.
  Parameter Equal_trans : forall s1 s2 s3, Equal s1 s2 -> Equal s2 s3 -> Equal s1 s3.
  Parameter Equal_ST : RelationClasses.Equivalence Equal.
  Parameter Equal_upd_Equal :
    forall v e s1 s2, Equal s1 s2 -> Equal (upd v e s1) (upd v e s2).
  Parameter Equal_Upd_Equal :
    forall v e s1 s2 s3 s4,
      Upd v e s1 s2 -> Upd v e s3 s4 -> Equal s1 s3 -> Equal s2 s4.
  Parameter Upd_pred_Equal :
    forall v e s1 s2 s, Upd v e s1 s2 -> Equal s1 s -> Upd v e s s2.
  Parameter Upd_succ_Equal :
    forall v e s1 s2 s, Upd v e s1 s2 -> Equal s2 s -> Upd v e s1 s.

  Parameter conform : t -> TE.env -> Prop.
  Parameter conform_def :
    forall (s : t) (E : TE.env),
      (forall (v : V.t), TE.mem v E -> TE.vsize v E = size (acc v s)) ->
      conform s E.
  Parameter conform_mem :
    forall v s te, conform s te -> TE.mem v te -> TE.vsize v te = size (acc v s).
  Parameter conform_Upd :
    forall x ty v s1 s2 te,
      sizeof_typ ty = size v -> Upd x v s1 s2 -> conform s1 te ->
      conform s2 (TE.add x ty te).
  Parameter conform_Upd2 :
    forall te s1 s2 ty1 ty2 x1 x2 v1 v2,
      x1 != x2 -> sizeof_typ ty1 = size v1 -> sizeof_typ ty2 = size v2 ->
      Upd2 x2 v2 x1 v1 s1 s2 -> conform s1 te ->
      conform s2 (TE.add x1 ty1 (TE.add x2 ty2 te)).
  Parameter conform_upd :
    forall x ty v s te,
      sizeof_typ ty = size v -> conform s te -> conform (upd x v s) (TE.add x ty te).
  Parameter conform_upd2 :
    forall te s ty1 ty2 x1 x2 v1 v2,
      x1 != x2 -> sizeof_typ ty1 = size v1 -> sizeof_typ ty2 = size v2 ->
      conform s te ->
      conform (upd2 x2 v2 x1 v1 s) (TE.add x1 ty1 (TE.add x2 ty2 te)).
  Parameter conform_add_not_mem :
    forall E s x ty,
      conform s (TE.add x ty E) -> ~~ TE.mem x E -> conform s E.
  Parameter conform_submap :
    forall E1 E2 s,
      Lemmas.submap E1 E2 -> conform s E2 -> conform s E1.
  Parameter conform_equal :
    forall E1 E2 s,
      TE.Equal E1 E2 -> conform s E1 <-> conform s E2.
  Parameter equal_conform :
    forall E s1 s2,
      Equal s1 s2 -> conform s1 E <-> conform s2 E.
End BitsStore.

Module MakeBitsStore (V : SsrOrder) (TE : TypEnv with Module SE := V) <:
  BitsStore V TE.

  Include MakeTStoreMap V BitsValueType.
  Module Lemmas := FMapLemmas TE.

  (* A store conforms to a typing environment if for every variable in the typing
     environment, the size of its type in the typing environment is the same as
     the size of its value in the store *)
  Definition conform (s : t) (te : TE.env) : Prop :=
    forall (v : V.t),
      TE.mem v te -> TE.vsize v te = size (acc v s).

  Lemma conform_def :
    forall (s : t) (E : TE.env),
      (forall (v : V.t), TE.mem v E -> TE.vsize v E = size (acc v s)) ->
      conform s E.
  Proof. move=> s E H. assumption. Qed.

  Lemma conform_mem v s te :
    conform s te -> TE.mem v te -> TE.vsize v te = size (acc v s).
  Proof. move=> H1 H2; exact: (H1 _ H2). Qed.

  Lemma conform_Upd x ty v s1 s2 te :
    sizeof_typ ty = size v -> Upd x v s1 s2 -> conform s1 te ->
    conform s2 (TE.add x ty te).
  Proof.
    move=> Hs Hupd Hcon y. case Hyx: (y == x).
    - by rewrite (TE.vsize_add_eq Hyx) (acc_Upd_eq Hyx Hupd).
    - move/negP: Hyx => Hyx. rewrite (Lemmas.mem_add_neq Hyx) => Hmem.
      move/negP: Hyx => Hyx. rewrite (acc_Upd_neq Hyx Hupd) (TE.vsize_add_neq Hyx).
      exact: (Hcon _ Hmem).
  Qed.

  Lemma conform_Upd2 te s1 s2 ty1 ty2 x1 x2 v1 v2 :
    x1 != x2 -> sizeof_typ ty1 = size v1 -> sizeof_typ ty2 = size v2 ->
    Upd2 x2 v2 x1 v1 s1 s2 -> conform s1 te ->
    conform s2 (TE.add x1 ty1 (TE.add x2 ty2 te)).
  Proof.
    move => Hneq Hty1 Hty2 HUpd2 Hcon y Hmem .
    case Heq1 : (y == x1); case Heq2 : (y == x2) .
    - rewrite -(eqP Heq1) -(eqP Heq2) in Hneq . move : Hneq => /eqP // .
    - rewrite (acc_Upd2_eq2 Heq1 HUpd2) (TE.vsize_add_eq Heq1) // .
    - move/idP/negP: Heq1 => Hneq1.
      rewrite (acc_Upd2_eq1 Heq2 Hneq1 HUpd2)
              (TE.vsize_add_neq Hneq1) (TE.vsize_add_eq Heq2) // .
    - move/idP/negP: Heq1 => Hneq1.
      move/idP/negP: Heq2 => Hneq2.
      rewrite (acc_Upd2_neq Hneq2 Hneq1 HUpd2)
              (TE.vsize_add_neq Hneq1) (TE.vsize_add_neq Hneq2) Hcon // .
      move/negP: Hneq1 => Hneq1. move/negP: Hneq2 => Hneq2.
      rewrite (Lemmas.mem_add_neq Hneq1) (Lemmas.mem_add_neq Hneq2) in Hmem.
      assumption.
  Qed.

  Lemma conform_upd x ty v s te :
    sizeof_typ ty = size v ->
    conform s te -> conform (upd x v s) (TE.add x ty te).
  Proof. move=> Hs Hcon. exact: (conform_Upd Hs (Upd_upd x v s) Hcon). Qed.

  Lemma conform_upd2 te s ty1 ty2 x1 x2 v1 v2 :
    x1 != x2 -> sizeof_typ ty1 = size v1 -> sizeof_typ ty2 = size v2 ->
    conform s te ->
    conform (upd2 x2 v2 x1 v1 s) (TE.add x1 ty1 (TE.add x2 ty2 te)).
  Proof.
    move=> Hne Hs1 Hs2 Hcon.
    exact: (conform_Upd2 Hne Hs1 Hs2 (Upd2_upd2 x2 v2 x1 v1 s) Hcon).
  Qed.

  Lemma conform_add_not_mem E s x ty :
    conform s (TE.add x ty E) -> ~~ TE.mem x E -> conform s E.
  Proof.
    move=> Hco Hmem y Hmemy. move: (Hco y). rewrite Lemmas.OP.P.F.add_b Hmemy orbT.
    move=> <-; last by exact: is_true_true. case Hyx: (y == x).
    - rewrite (eqP Hyx) in Hmemy. rewrite Hmemy in Hmem. discriminate.
    - move/idP/negP: Hyx => Hyx. rewrite (TE.vsize_add_neq Hyx). reflexivity.
  Qed.

  Lemma conform_submap E1 E2 s :
    Lemmas.submap E1 E2 -> conform s E2 -> conform s E1.
  Proof.
    move=> Hsubm Hco x Hmem1. move: (Lemmas.submap_mem Hsubm Hmem1) => Hmem2.
    move: (Lemmas.mem_find_some Hmem1) => [ty Hfind1].
    move: (Hsubm x ty Hfind1) => Hfind2. move: (TE.find_some_vtyp Hfind1) => Hty1.
     move: (TE.find_some_vtyp Hfind2) => Hty2. rewrite -(Hco _ Hmem2).
    rewrite (TE.vtyp_vsize Hty1) (TE.vtyp_vsize Hty2). reflexivity.
  Qed.

  Lemma conform_equal E1 E2 s :
    TE.Equal E1 E2 -> conform s E1 <-> conform s E2.
  Proof.
    move=> Heq. move: (Lemmas.Equal_submap Heq) => H12.
    move: (Lemmas.Equal_sym Heq) => {Heq} Heq.
    move: (Lemmas.Equal_submap Heq) => H21. split.
    - exact: (conform_submap H21).
    - exact: (conform_submap H12).
  Qed.

  Lemma equal_conform E s1 s2 :
    Equal s1 s2 -> conform s1 E <-> conform s2 E.
  Proof.
    move=> Heq. split.
    - move=> H1. apply: conform_def. move=> v Hmem.
      rewrite (conform_mem H1 Hmem). rewrite (Heq v). reflexivity.
    - move=> H2. apply: conform_def. move=> v Hmem.
      rewrite (conform_mem H2 Hmem). rewrite (Heq v). reflexivity.
  Qed.

End MakeBitsStore.

Module Store := MakeBitsStore VarOrder TE.
Module SSAStore := MakeBitsStore SSAVarOrder SSATE.
Module ZSSAStore := MakeTStoreMap SSAVarOrder ZValueType.

Section State.

  Variable t : Type.

  Inductive state : Type :=
  | OK of t
  | ERR.

End State.

Module State.
  Definition t : Type := state Store.t.
End State.

Module SSAState.
  Definition t : Type := state SSAStore.t.
End SSAState.

Module ZSSAState.
  Definition t : Type := state ZSSAStore.t.
End ZSSAState.
