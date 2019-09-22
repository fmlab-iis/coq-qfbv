
From mathcomp Require Import ssreflect ssrbool eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrdered Store.
From BitBlasting Require Import Var Typ TypEnv.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module ValueType <: HasDefaultTyp.
  Definition t := bits.
  Definition default : t := [::].
End ValueType.

Module Store := RealizableTStoreAdapter VarOrder ValueType.

Inductive state : Type :=
| OK of Store.t
| ERR.



(* A store conforms to a typing environment if for every variable in the typing
   environment, the size of its type in the typing environment is the same as
   the size of its value in the store *)

Definition conform (s : Store.t) (te : TypEnv.t) : Prop :=
  forall (v : var),
    TypEnv.mem v te -> TypEnv.vsize v te = size (Store.acc v s).

Lemma conform_upd x ty v s te :
  sizeof_typ ty = size v ->
  conform s te -> conform (Store.upd x v s) (TypEnv.add x ty te).
Proof.
  move=> Hs Hcon y. case Hyx: (y == x).
  - by rewrite (TypEnv.vsize_add_eq Hyx) (Store.acc_upd_eq Hyx).
  - move/idP/negP: Hyx => Hyx. rewrite (TypEnv.mem_add_neq Hyx) => Hmem.
    rewrite (Store.acc_upd_neq Hyx) (TypEnv.vsize_add_neq Hyx). exact: (Hcon _ Hmem).
Qed.
