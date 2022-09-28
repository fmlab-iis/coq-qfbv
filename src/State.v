
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

Module Type BitsStore (V : SsrOrder) (TE : TypEnv with Module SE := V) <: TStore V BitsValueType.

  Include TStore V BitsValueType.
  Module Lemmas := FMapLemmas TE.

  Local Notation var := V.t.
  Local Notation value := bits.

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
