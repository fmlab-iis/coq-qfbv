
From mathcomp Require Import ssreflect ssrbool eqtype.
From BitBlasting Require Import Typ Var.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module TypEnv.

  (* A typing environment is a map from a variable to its type *)
  Definition t : Type := VM.t typ.

  (* The default type of a variable not in the typing environment *)
  Definition deftyp : typ := Tuint 0.

  (* Find the type of a variable in a typing environment *)
  Definition find (v : var) (e : t) : typ :=
    match VM.find v e with
    | None => deftyp
    | Some ty => ty
    end.

  (* Return the size of a variable in a typing environment *)
  Definition vsize (v : var) (e : t) : nat := sizeof_typ (find v e).

  Definition mem (v : var) (e : t) : bool := VM.mem v e.

  Definition add (v : var) (ty : typ) (e : t) := VM.add v ty e.

  Lemma find_add_eq {x y ty e} : x == y -> find x (add y ty e) = ty.
  Proof. rewrite /find /add => H. by rewrite (VM.Lemmas.find_add_eq H). Qed.

  Lemma find_add_neq {x y ty e} : x != y -> find x (add y ty e) = find x e.
  Proof.
    move/negP=> Hxy. rewrite /find /add. by rewrite (VM.Lemmas.find_add_neq Hxy).
  Qed.

  Lemma vsize_add_eq {x y ty e} : x == y -> vsize x (add y ty e) = sizeof_typ ty.
  Proof. rewrite /vsize=> H. by rewrite (find_add_eq H). Qed.

  Lemma vsize_add_neq {x y ty e} : x != y -> vsize x (add y ty e) = vsize x e.
  Proof. rewrite /vsize => H. by rewrite (find_add_neq H). Qed.

  Lemma not_mem_find_deftyp v e : ~~ mem v e -> find v e = deftyp.
  Proof. rewrite /find => H. by rewrite VM.Lemmas.not_mem_find_none. Qed.

  Lemma mem_add_eq {x y ty e} : x == y -> mem x (add y ty e).
  Proof. exact: VM.Lemmas.mem_add_eq. Qed.

  Lemma mem_add_neq {x y ty e} : x != y -> mem x (add y ty e) = mem x e.
  Proof. move/idP/negP=> H. exact: (VM.Lemmas.mem_add_neq H). Qed.

  Lemma find_vsize x e ty : find x e = ty -> vsize x e = sizeof_typ ty.
  Proof. rewrite /vsize /find. move=> ->. reflexivity. Qed.

End TypEnv.
