
From Coq Require Import OrderedType.
From mathcomp Require Import ssreflect ssrbool eqtype.
From BitBlasting Require Import Typ.
From ssrlib Require Import EqOrder EqFMaps Tactics EqFSets.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* A typing environment is a map from a variable to its type *)
Module Type TypEnv <: EqFMap.

  Include EqFMap.

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
    forall {x : SE.t} {e : env},
      vsize x e = sizeof_typ (vtyp x e).
  Definition eequal : env -> env -> bool := equal typ_eqn.
  Global Instance add_proper_vtyp : Proper (eq ==> (@Equal typ) ==> eq) vtyp.
  Proof.
    move=> x y ? E1 E2 Heq; subst. case H1: (find y E1); case H2: (find y E2).
    - rewrite (find_some_vtyp H1) (find_some_vtyp H2). rewrite -Heq H1 in H2. by case: H2.
    - rewrite -Heq H1 in H2. discriminate.
    - rewrite -Heq H1 in H2. discriminate.
    - rewrite (find_none_vtyp H1) (find_none_vtyp H2). reflexivity.
  Qed.
  Global Instance add_proper_vsize : Proper (eq ==> (@Equal typ) ==> eq) vsize.
  Proof.
    move=> x y ? E1 E2 Heq; subst. rewrite !vtyp_vsize. rewrite -> Heq. reflexivity.
  Qed.

End TypEnv.


Module TypEnvLemmas (TE : TypEnv).

  Include (FMapLemmas TE).

  Lemma find_same_vtyp E1 E2 x :
    TE.find x E1 = TE.find x E2 -> TE.vtyp x E1 = TE.vtyp x E2.
  Proof.
    move=> Hfind. case Hf2: (TE.find x E2) Hfind => Hf1.
    - rewrite (TE.find_some_vtyp Hf1) (TE.find_some_vtyp Hf2). reflexivity.
    - rewrite (TE.find_none_vtyp Hf1) (TE.find_none_vtyp Hf2). reflexivity.
  Qed.

  Lemma find_same_vsize E1 E2 x :
    TE.find x E1 = TE.find x E2 -> TE.vsize x E1 = TE.vsize x E2.
  Proof.
    move=> Hfind. rewrite !TE.vtyp_vsize. rewrite (find_same_vtyp Hfind). reflexivity.
  Qed.

  Lemma equalP x y : reflect (TE.Equal x y) (TE.equal typ_eqn x y).
  Proof.
    have H: forall e e' : typ, (e =? e')%typ = true <-> e = e'.
    { move=> e1 e2; split; [move/typ_eqP => H | move=> H; apply/typ_eqP]; tauto. }
    case Heq: (TE.equal typ_eqn x y).
    - apply: ReflectT. move: Heq. move/equal_iff. move/(Equal_Equivb H). by apply.
    - apply: ReflectF. move=> Hxy. move/negP: Heq; apply.
      apply/equal_iff. apply/(Equal_Equivb H). assumption.
  Qed.

  Lemma eequalP x y : reflect (TE.Equal x y) (TE.eequal x y).
  Proof. exact: equalP. Qed.

End TypEnvLemmas.


Module MakeTypEnv (V : EqOrder) (VM : EqFMap with Module SE := V) <:
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

  Lemma vtyp_vsize x e : vsize x e = sizeof_typ (vtyp x e).
  Proof. reflexivity. Qed.

  Definition eequal := equal typ_eqn.

  Global Instance add_proper_vtyp : Proper (eq ==> (@Equal typ) ==> eq) vtyp.
  Proof.
    move=> x y ? E1 E2 Heq; subst. rewrite /vtyp. rewrite Heq. reflexivity.
  Qed.

  Global Instance add_proper_vsize : Proper (eq ==> (@Equal typ) ==> eq) vsize.
  Proof.
    move=> x y ? E1 E2 Heq; subst. rewrite /vsize. rewrite Heq. reflexivity.
  Qed.

End MakeTypEnv.

From ssrlib Require Import EqVar.

Module TE <: TypEnv := MakeTypEnv VarOrder VM.
Module SSATE <: TypEnv := MakeTypEnv SSAVarOrder SSAVM.


Module TypEnvAgree
       (V : EqOrder)
       (TE : TypEnv with Module SE := V)
       (VS : EqFSet with Module SE := V).

  Module MA := MapAgree V TE VS.
  Include MA.

  Lemma agree_mem v vs (E1 E2 : TE.env) :
    agree vs E1 E2 -> VS.mem v vs -> TE.mem v E1 = TE.mem v E2.
  Proof.
    move=> Hag Hmem. move: (Hag _ Hmem).
    rewrite VMLemmas.F.mem_find_b. move=> ->.
    rewrite -VMLemmas.F.mem_find_b. reflexivity.
  Qed.

  Lemma agree_mem_singleton v (E1 E2 : TE.env) :
    agree (VS.singleton v) E1 E2 -> TE.mem v E1 = TE.mem v E2.
  Proof.
    move=> Hag. apply: (agree_mem Hag). apply: VSLemmas.mem_singleton2.
    exact: eqxx.
  Qed.

  Lemma agree_vtyp v vs (E1 E2 : TE.env) :
    agree vs E1 E2 -> VS.mem v vs -> TE.vtyp v E1 = TE.vtyp v E2.
  Proof.
    move=> Hag Hmem. move: (Hag _ Hmem) => Hfind.
    case Hf: (TE.find v E2).
    - rewrite Hf in Hfind. rewrite (TE.find_some_vtyp Hf) (TE.find_some_vtyp Hfind).
      reflexivity.
    - rewrite Hf in Hfind. rewrite (TE.find_none_vtyp Hf) (TE.find_none_vtyp Hfind).
      reflexivity.
  Qed.

  Lemma agree_vtyp_singleton v (E1 E2 : TE.env) :
    agree (VS.singleton v) E1 E2 -> TE.vtyp v E1 = TE.vtyp v E2.
  Proof.
    move=> Hag. apply: (agree_vtyp Hag). apply: VSLemmas.mem_singleton2.
    exact: eqxx.
  Qed.

  Lemma agree_vsize v vs (E1 E2 : TE.env) :
    agree vs E1 E2 -> VS.mem v vs -> TE.vsize v E1 = TE.vsize v E2.
  Proof.
    move=> Hag Hmem. rewrite !TE.vtyp_vsize. rewrite (agree_vtyp Hag Hmem). reflexivity.
  Qed.

  Lemma agree_vsize_singleton v (E1 E2 : TE.env) :
    agree (VS.singleton v) E1 E2 -> TE.vsize v E1 = TE.vsize v E2.
  Proof.
    move=> Hag. rewrite !TE.vtyp_vsize. rewrite (agree_vtyp_singleton Hag). reflexivity.
  Qed.

End TypEnvAgree.
