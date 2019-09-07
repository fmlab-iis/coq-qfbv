
From Coq Require Import List ZArith.
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNFSimple.
From ssrlib Require Import Var SsrOrdered Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module Arch64 : Arch.
  Definition wordsize := 64.
  Lemma wordsize_positive : wordsize > 0.
  Proof.
    done.
  Qed.
End Arch64.
Module QFBV64 := QFBVSimple.Make VarOrder Arch64.
Notation wordsize := Arch64.wordsize.


Definition cnf_lit_not a := [:: [:: neg_lit a]].
Definition cnf_lit_xor a1 a2 := [:: [:: a1; a2]; [:: neg_lit a1; neg_lit a2]].
Definition cnf_lit_eq a1 a2 := [:: [:: neg_lit a1; a2]; [:: a1; neg_lit a2]].

Lemma cnf_lit_xor_correct :
  forall b1 b2 E l1 l2,
    enc_bit E l1 b1 -> enc_bit E l2 b2 ->
    interp_cnf E (cnf_lit_xor l1 l2) ->
    b1 != b2.
Proof.
  move=> b1 b2 E l1 l2. rewrite /enc_bit /cnf_lit_xor /=.
  rewrite !interp_lit_neg_lit.
  case: b1; case: b2; try reflexivity.
  - move=> /eqP -> /eqP ->. done.
  - move=> /eqP -> /eqP ->. done.
Qed.

Lemma cnf_lit_eq_correct :
  forall b1 b2 E l1 l2,
    enc_bit E l1 b1 -> enc_bit E l2 b2 ->
    interp_cnf E (cnf_lit_eq l1 l2) ->
    b1 = b2.
Proof.
  move=> b1 b2 E l1 l2. rewrite /enc_bit /cnf_lit_eq /=.
  rewrite !interp_lit_neg_lit.
  case: b1; case: b2; try reflexivity.
  - move=> /eqP -> /eqP ->. done.
  - move=> /eqP -> /eqP ->. done.
Qed.



(* ===== Variable generation ===== *)

Definition generator := positive.

Definition gen (g : generator) : generator * literal := (g + 1, Pos g)%positive.



(* ===== A map from variables to literal representation ===== *)

Definition vm := VM.t (wordsize.-tuple literal).



(* ===== newer_than_vm ===== *)

Definition newer_than_vm g (m : vm) :=
  forall v rs, VM.find v m = Some rs -> newer_than_lits g rs.

Lemma newer_than_vm_add_r :
  forall x (m : vm) y,
    newer_than_vm x m -> newer_than_vm (x + y) m.
Proof.
  move=> x m y Hnew v rs Hfind. move: (Hnew v rs Hfind).
  exact: newer_than_lits_add_r.
Qed.

Lemma newer_than_vm_le_newer :
  forall x (m : vm) y,
    newer_than_vm x m -> (x <=? y)%positive -> newer_than_vm y m.
Proof.
  move=> x m y Hnew Hle v rs Hfind. move: (Hnew v rs Hfind) => {Hnew} Hnew.
  exact: (newer_than_lits_le_newer Hnew Hle).
Qed.



(* ===== Consistent ===== *)

Definition consistent1 m E s v : Prop :=
    match VM.find v m with
    | None => True
    | Some rs => @enc_bits E wordsize rs (QFBV64.State.acc v s)
    end.
Definition consistent m E s := forall v, consistent1 m E s v.

Lemma consistent_env_upd_newer :
  forall m s E g g' b,
    newer_than_vm g m ->
    consistent m E s ->
    (g <=? g')%positive ->
    consistent m (env_upd E g' b) s.
Proof.
  move=> m s E g g' b Hnew Hcon Hle.
  move: (newer_than_vm_le_newer Hnew Hle) => Hnew'. move=> v.
  move: (Hnew' v) (Hcon v) => {Hnew Hnew' Hcon}.
  rewrite /consistent1. case: (VM.find v m); last by done.
  move=> rs Hnew Henc. move: (Hnew rs (Logic.eq_refl (Some rs))) => {Hnew} Hnew.
  rewrite (newer_than_lits_enc_bits_env_upd _ _ _ Hnew). exact: Henc.
Qed.

Lemma env_preserve_consistent :
  forall m E E' g s,
    newer_than_vm g m ->
    env_preserve E E' g ->
    consistent m E s ->
    consistent m E' s.
Proof.
  move=> m E E' g s Hnew_gm Hpre Hcon. move=> x; rewrite /consistent1.
  case Hfind: (VM.find x m); last by done. move: (Hnew_gm x _ Hfind) => Hnew_glsx.
  move: (Hcon x); rewrite /consistent1. rewrite Hfind.
  exact: (env_preserve_enc_bits Hpre Hnew_glsx).
Qed.



(* ===== vm_preserve ===== *)

Definition vm_preserve (m m' : vm) : Prop :=
  forall v ls, VM.find v m = Some ls -> VM.find v m' = Some ls.

Lemma vm_preserve_consistent :
  forall m m' s E,
    vm_preserve m m' -> consistent m' E s -> consistent m E s.
Proof.
  move=> m m' s E Hpre Hcon v. rewrite /consistent1. case Hfind: (VM.find v m).
  - move: (Hpre _ _ Hfind) => Hfind'. move: (Hcon v). rewrite /consistent1.
    rewrite  Hfind'. by apply.
  - done.
Qed.

Lemma vm_preserve_refl : forall m, vm_preserve m m.
Proof.
  move=> m. done.
Qed.

Lemma vm_preserve_trans :
  forall m1 m2 m3, vm_preserve m1 m2 -> vm_preserve m2 m3 -> vm_preserve m1 m3.
Proof.
  move=> m1 m2 m3 H12 H23 v ls Hfind1. move: (H12 _ _ Hfind1) => Hfind2.
  exact: (H23 _ _ Hfind2).
Qed.

Lemma vm_preserve_add_diag :
  forall m v ls,
    VM.find v m = None ->
    vm_preserve m (VM.add v ls m).
Proof.
  move=> m v ls Hfind x xls Hfindx. case Hxv: (x == v).
  - rewrite (eqP Hxv) Hfind in Hfindx. discriminate.
  - move/negP: Hxv => Hxv. rewrite (VM.Lemmas.find_add_neq _ _ Hxv). assumption.
Qed.



(* ===== Tactics ===== *)

Ltac fresh_name t :=
  match t with
  | vm => fresh "m"
  | env => fresh "E"
  | generator => fresh "g"
  | cnf => fresh "cs"
  | _.-tuple literal => fresh "ls"
  | literal => fresh "l"
  | _ => fresh
  end.

Ltac dcase_hyps :=
  match goal with
  | H : context f [let '_ := ?r in _] |- _ =>
    move: H;
    let H1 := fresh in
    let H2 := fresh in
    lazymatch type of r with
    | prod (prod (prod (prod ?t1 ?t2) ?t3) ?t4) ?t5 =>
      let t1 := fresh_name t1 in
      let t2 := fresh_name t2 in
      let t3 := fresh_name t3 in
      let t4 := fresh_name t4 in
      let t5 := fresh_name t5 in
      dcase r; move=> [[[[t1 t2] t3] t4] t5] H1 H2; dcase_hyps
    | prod (prod (prod ?t1 ?t2) ?t3) ?t4 =>
      let t1 := fresh_name t1 in
      let t2 := fresh_name t2 in
      let t3 := fresh_name t3 in
      let t4 := fresh_name t4 in
      dcase r; move=> [[[t1 t2] t3] t4] H1 H2; dcase_hyps
    | prod (prod ?t1 ?t2) ?t3 =>
      let t1 := fresh_name t1 in
      let t2 := fresh_name t2 in
      let t3 := fresh_name t3 in
      dcase r; move=> [[t1 t2] t3] H1 H2; dcase_hyps
    | prod ?t1 ?t2 =>
      let t1 := fresh_name t1 in
      let t2 := fresh_name t2 in
      dcase r; move=> [t1 t2] H1 H2; dcase_hyps
    end
  | H : context f [if ?c then _ else _] |- _ =>
    move: H;
    let H1 := fresh in
    let H2 := fresh in
    dcase c=> H1 H2; dcase_hyps
  | H : (_, _, _, _, _) = (_, _, _, _, _) |- _ =>
    case: H;
    let H1 := fresh in
    let H2 := fresh in
    let H3 := fresh in
    let H4 := fresh in
    let H5 := fresh in
    move=> H1 H2 H3 H4 H5; dcase_hyps
  | H : (_, _, _, _) = (_, _, _, _) |- _ =>
    case: H;
    let H1 := fresh in
    let H2 := fresh in
    let H3 := fresh in
    let H4 := fresh in
    move=> H1 H2 H3 H4; dcase_hyps
  | H : (_, _, _) = (_, _, _) |- _ =>
    case: H;
    let H1 := fresh in
    let H2 := fresh in
    let H3 := fresh in
    move=> H1 H2 H3; dcase_hyps
  | H : (_, _) = (_, _) |- _ =>
    case: H;
    let H1 := fresh in
    let H2 := fresh in
    move=> H1 H2; dcase_hyps
  | H : context f [match ?t with | None => _ | Some _ => _ end] |- _ =>
    move: H;
    let H1 := fresh in
    let H2 := fresh in
    dcase t; case => H1 H2; dcase_hyps
  | H : context f [match ?t with | Some _ => _ | None => _ end] |- _ =>
    move: H;
    let H1 := fresh in
    let H2 := fresh in
    dcase t; case => H1 H2; dcase_hyps
  | |- _ => idtac
  end.

Ltac dcase_goal :=
  match goal with
  | |- context f [let '_ := ?r in _] =>
    let H := fresh in
    lazymatch type of r with
    | prod (prod (prod (prod ?t1 ?t2) ?t3) ?t4) ?t5 =>
      let t1 := fresh_name t1 in
      let t2 := fresh_name t2 in
      let t3 := fresh_name t3 in
      let t4 := fresh_name t4 in
      let t5 := fresh_name t5 in
      dcase r; move=> [[[[t1 t2] t3] t4] t5] H; dcase_goal
    | prod (prod (prod ?t1 ?t2) ?t3) ?t4 =>
      let t1 := fresh_name t1 in
      let t2 := fresh_name t2 in
      let t3 := fresh_name t3 in
      let t4 := fresh_name t4 in
      dcase r; move=> [[[t1 t2] t3] t4] H; dcase_goal
    | prod (prod ?t1 ?t2) ?t3 =>
      let t1 := fresh_name t1 in
      let t2 := fresh_name t2 in
      let t3 := fresh_name t3 in
      dcase r; move=> [[t1 t2] t3] H; dcase_goal
    | prod ?t1 ?t2 =>
      let t1 := fresh_name t1 in
      let t2 := fresh_name t2 in
      dcase r; move=> [t1 t2] H; dcase_goal
    end
  | |- (_, _, _, _, _) = (_, _, _, _, _) =>
    let H1 := fresh in
    let H2 := fresh in
    let H3 := fresh in
    let H4 := fresh in
    let H5 := fresh in
    case=> H1 H2 H3 H4 H5; dcase_goal
  | |- (_, _, _, _) = (_, _, _, _) =>
    let H1 := fresh in
    let H2 := fresh in
    let H3 := fresh in
    let H4 := fresh in
    case=> H1 H2 H3 H4; dcase_goal
  | |- (_, _, _) = (_, _, _) =>
    let H1 := fresh in
    let H2 := fresh in
    let H3 := fresh in
    case=> H1 H2 H3; dcase_goal
  | |- (_, _) = (_, _) =>
    let H1 := fresh in
    let H2 := fresh in
    case=> H1 H2; dcase_goal
  | |- _ => idtac
  end.

Ltac dite_hyps :=
  match goal with
  | H : context f [if ?c then _ else _] |- _ =>
    move: H;
    let H1 := fresh in
    let H2 := fresh in
    dcase c; case=> H1 H2; dite_hyps
  | |- _ => idtac
  end.

Ltac intros_tuple :=
  lazymatch goal with
  | |- forall x : ((_.+1).-tuple _), _ =>
    let hd := fresh x in
    let tl := fresh x in
    case/tupleP=> [hd tl] /=; try rewrite !theadE !beheadCons; intros_tuple
  | |- forall x : _, _ => intro; intros_tuple
  | |- _ => idtac
  end.


(* todo: change to hyps_splitb *)

Ltac split_andb :=
  repeat (match goal with
          | H : is_true (andb ?l ?r) |- _ => move/andP: H;
                                             let H1 := fresh in
                                             let H2 := fresh in
                                             move=> [H1 H2]
          end).