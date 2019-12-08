
From mathcomp Require Import ssreflect ssrbool eqtype.
From BitBlasting Require Import Typ.
From ssrlib Require Import SsrOrder FMaps Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* A typing environment is a map from a variable to its type *)
Module Type TypEnv <: SsrFMap.

  Include SsrFMap.

  Definition env : Type := t typ.

  (* The default type of a variable not in the typing environment *)
  Parameter deftyp : typ.

  (* Find the type of a variable in a typing environment.
     If a variable is not in the typing environment, return the default type. *)
  Parameter vtyp : SE.t -> env -> typ.

  (* Return the size of a variable in a typing environment.
     If a variable is not in the typing environment, return the size of the
     default type. *)
  Parameter vsize : SE.t -> env -> nat.

  Axiom find_some_vtyp :
    forall {x : SE.t} {ty : typ} {e : env}, find x e = Some ty -> vtyp x e = ty.
  Axiom find_none_vtyp :
    forall {x : SE.t} {e : env}, find x e = None -> vtyp x e = deftyp.
  Axiom vtyp_find :
    forall {x : SE.t} {ty : typ} {e : env},
      (vtyp x e == ty) = (find x e == Some ty) || ((find x e == None) && (ty == deftyp)).
  Axiom vtyp_add_eq :
    forall {x y : SE.t} {ty : typ} {e : env}, x == y -> vtyp x (add y ty e) = ty.
  Axiom vtyp_add_neq :
    forall {x y : SE.t} {ty : typ} {e : env},
      x != y -> vtyp x (add y ty e) = vtyp x e.
  Axiom vsize_add_eq :
    forall {x y : SE.t} {ty : typ} {e : env},
      x == y -> vsize x (add y ty e) = sizeof_typ ty.
  Axiom vsize_add_neq :
    forall {x y : SE.t} {ty : typ} {e : env},
      x != y -> vsize x (add y ty e) = vsize x e.
  Axiom not_mem_vtyp :
    forall {v : SE.t} {e : env}, ~~ mem v e -> vtyp v e = deftyp.
  Axiom vtyp_vsize :
    forall {x : SE.t} {e : env} {ty : typ},
      vtyp x e = ty -> vsize x e = sizeof_typ ty.

End TypEnv.

Module MakeTypEnv (V : SsrOrder) (VM : SsrFMap with Module SE := V) <:
  TypEnv with Module SE := V.

  Include VM.
  Module Lemmas := FMapLemmas VM.

  Definition env : Type := t typ.

  (* The default type of a variable not in the typing environment *)
  Definition deftyp : typ := Tuint 0.

  (* Find the type of a variable in a typing environment.
     If a variable is not in the typing environment, return the default type. *)
  Definition vtyp (v : V.t) (e : env) : typ :=
    match VM.find v e with
    | None => deftyp
    | Some ty => ty
    end.

  (* Return the size of a variable in a typing environment.
     If a variable is not in the typing environment, return the size of the
     default type. *)
  Definition vsize (v : V.t) (e : env) : nat := sizeof_typ (vtyp v e).

  Lemma find_some_vtyp {x ty e} : find x e = Some ty -> vtyp x e = ty.
  Proof. move=> H. rewrite /vtyp H. reflexivity. Qed.

  Lemma find_none_vtyp {x e} : find x e = None -> vtyp x e = deftyp.
  Proof. move=> H. rewrite /vtyp H. reflexivity. Qed.

  Lemma vtyp_find {x ty e} :
    (vtyp x e == ty) = (find x e == Some ty) || ((find x e == None) && (ty == deftyp)).
  Proof.
    dcase (find x e); case.
    - move=> a Hfind. rewrite (find_some_vtyp Hfind) /= orbF. case Heq: (a == ty).
      + by rewrite (eqP Heq) eqxx.
      + symmetry. apply/eqP => H. case: H => H. rewrite H eqxx in Heq. discriminate.
    - move=> Hnone. rewrite (find_none_vtyp Hnone) eqxx /=. rewrite eq_sym.
      reflexivity.
  Qed.

  Lemma vtyp_add_eq {x y ty e} : x == y -> vtyp x (add y ty e) = ty.
  Proof. rewrite /vtyp /add => H. by rewrite (Lemmas.find_add_eq H). Qed.

  Lemma vtyp_add_neq {x y ty e} : x != y -> vtyp x (add y ty e) = vtyp x e.
  Proof.
    move/negP=> Hxy. rewrite /vtyp /add. by rewrite (Lemmas.find_add_neq Hxy).
  Qed.

  Lemma vsize_add_eq {x y ty e} : x == y -> vsize x (add y ty e) = sizeof_typ ty.
  Proof. rewrite /vsize=> H. by rewrite (vtyp_add_eq H). Qed.

  Lemma vsize_add_neq {x y ty e} : x != y -> vsize x (add y ty e) = vsize x e.
  Proof. rewrite /vsize => H. by rewrite (vtyp_add_neq H). Qed.

  Lemma not_mem_vtyp v e : ~~ mem v e -> vtyp v e = deftyp.
  Proof. rewrite /vtyp => H. by rewrite Lemmas.not_mem_find_none. Qed.

  Lemma vtyp_vsize x e ty : vtyp x e = ty -> vsize x e = sizeof_typ ty.
  Proof. rewrite /vsize /vtyp. move=> ->. reflexivity. Qed.

End MakeTypEnv.

From ssrlib Require Import Var.

Module TE <: TypEnv := MakeTypEnv VarOrder VM.
Module SSATE <: TypEnv := MakeTypEnv SSAVarOrder SSAVM.
