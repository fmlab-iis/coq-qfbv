
From mathcomp Require Import ssreflect ssrbool eqtype.
From BitBlasting Require Import Typ Var.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module TypEnv.

  (* A typing environment is a map from a variable to its type *)
  Definition t : Type := VM.t typ.

  (* Return the size of a variable in a typing environment.
     If the variable is not in the typing environment, return 0 by default. *)
  Definition vsize (v : var) (e : t) : nat :=
    match VM.find v e with
    | None => 0
    | Some t => sizeof_typ t
    end.

  Definition find (v : var) (e : t) : option typ := VM.find v e.

  Definition add (v : var) (ty : typ) (e : t) := VM.add v ty e.

  Lemma find_add_eq {x y ty e} : x == y -> find x (add y ty e) = Some ty.
  Proof. exact: VM.Lemmas.find_add_eq. Qed.

  Lemma find_add_neq {x y ty e} : x != y -> find x (add y ty e) = find x e.
  Proof. move/negP=> Hxy. exact: (VM.Lemmas.find_add_neq Hxy). Qed.

End TypEnv.
