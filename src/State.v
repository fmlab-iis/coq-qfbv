
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
  Parameter conform_mem :
    forall v s te, conform s te -> TE.mem v te -> TE.vsize v te = size (acc v s).
  Parameter conform_upd :
    forall x ty v s te,
      sizeof_typ ty = size v -> conform s te -> conform (upd x v s) (TE.add x ty te).

End BitsStore.

Module MakeBitsStore (V : SsrOrder) (TE : TypEnv with Module SE := V) <:
  BitsStore V TE.

  Include RealizableTStoreAdapter V BitsValueType.
  Module Lemmas := FMapLemmas TE.

  (* A store conforms to a typing environment if for every variable in the typing
     environment, the size of its type in the typing environment is the same as
     the size of its value in the store *)
  Definition conform (s : t) (te : TE.env) : Prop :=
    forall (v : V.t),
      TE.mem v te -> TE.vsize v te = size (acc v s).

  Lemma conform_mem v s te :
    conform s te -> TE.mem v te -> TE.vsize v te = size (acc v s).
  Proof. move=> H1 H2; exact: (H1 _ H2). Qed.

  Lemma conform_upd x ty v s te :
    sizeof_typ ty = size v ->
    conform s te -> conform (upd x v s) (TE.add x ty te).
  Proof.
    move=> Hs Hcon y. case Hyx: (y == x).
    - by rewrite (TE.vsize_add_eq Hyx) (acc_upd_eq Hyx).
    - move/negP: Hyx => Hyx. rewrite (Lemmas.mem_add_neq Hyx) => Hmem.
      move/negP: Hyx => Hyx. rewrite (acc_upd_neq Hyx) (TE.vsize_add_neq Hyx).
      exact: (Hcon _ Hmem).
  Qed.

End MakeBitsStore.

Module Store := MakeBitsStore VarOrder TE.
Module SSAStore := MakeBitsStore SSAVarOrder SSATE.
Module ZSSAStore := RealizableTStoreAdapter SSAVarOrder ZValueType.

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
