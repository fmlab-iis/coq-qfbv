From Coq Require Import ZArith OrderedType Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import FMaps Var. 
From BitBlasting Require Import QFBV CNF State AdhereConform BBCommon.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module ExpMap <: SsrFMap := FMaps.MakeTreeMap QFBV.ExpOrder.
Module BexpMap <: SsrFMap := FMaps.MakeTreeMap QFBV.BexpOrder.

Definition expm := ExpMap.t (cnf * word).
Definition bexpm := BexpMap.t (cnf * literal).

(* ==== A table storing complete results, including CNF and literal(s) ==== *)

Record comptable :=
  { et : expm;
    bt : bexpm }.

Definition find_et e t := ExpMap.find e (et t).
Definition find_bt e t := BexpMap.find e (bt t).

Definition add_et e cs ls t := 
  {| et := ExpMap.add e (cs, ls) (et t);
     bt := bt t |}.
Definition add_bt e cs l t := 
  {| et := et t;
     bt := BexpMap.add e (cs, l) (bt t) |}.

Lemma find_et_add_et_eq :
  forall e cs ls t, find_et e (add_et e cs ls t) = Some (cs, ls).
Proof.
  move=> e cs ls t. rewrite /find_et /add_et /=. 
  by apply: ExpMap.Lemmas.find_add_eq.
Qed.

Lemma find_bt_add_bt_eq :
  forall e cs l t, find_bt e (add_bt e cs l t) = Some (cs, l).
Proof.
  move=> e cs l t. rewrite /find_bt /add_bt /=. 
  by apply: BexpMap.Lemmas.find_add_eq.
Qed.

Lemma find_et_add_et_neq :
  forall e0 e cs ls t, ~ e0 == e -> find_et e0 (add_et e cs ls t) = find_et e0 t.
Proof.
  move=> e0 e cs ls t Hneq. by apply: ExpMap.Lemmas.find_add_neq.
Qed.

Lemma find_bt_add_bt_neq :
  forall e0 e cs l t, ~ e0 == e -> find_bt e0 (add_bt e cs l t) = find_bt e0 t .
Proof.
  move=> e0 e cs l t Hneq. by apply: BexpMap.Lemmas.find_add_neq. 
Qed.

Lemma find_et_add_bt :
  forall e0 e cs l t, find_et e0 (add_bt e cs l t) = find_et e0 t.
Proof.
  move=> e0 e cs l t. done. 
Qed.

Lemma find_bt_add_et :
  forall e0 e cs ls t, find_bt e0 (add_et e cs ls t) = find_bt e0 t.
Proof.
  move=> e0 e cs ls t. done. 
Qed.


(* ==== interp_table === *)

Definition interp_table (E : env) (t : comptable) :=
  (forall e cs ls, find_et e t = Some (cs, ls) -> interp_cnf E cs)
  /\ forall e cs l, find_bt e t = Some (cs, l) -> interp_cnf E cs.

Lemma interp_table_add_et :
  forall E t e cs ls, interp_table E t /\ interp_cnf E cs ->
                      interp_table E (add_et e cs ls t).
Proof.
  move=> E t e cs ls [[Hre Hrb] Hcs]. rewrite /interp_table /=. split; last done.
  move=> e0 cs0 ls0. case Heq : (e0 == e).
  - move/eqP: Heq => <-. rewrite find_et_add_et_eq. case=> <- _; done.
  - move/negP: Heq => Hneq. rewrite (find_et_add_et_neq _ _ _ Hneq).
    exact: Hre.
Qed.

Lemma interp_table_add_bt :
  forall E t e cs l, interp_table E t /\ interp_cnf E cs ->
                     interp_table E (add_bt e cs l t).
Proof.
  move=> E t e cs l [[Hre Hrb] Hcs]. rewrite /interp_table /=. split; first done.
  move=> e0 cs0 l0. case Heq : (e0 == e).
  - move/eqP: Heq => <-. rewrite find_bt_add_bt_eq. case=> <- _; done.
  - move/negP: Heq => Hneq. rewrite (find_bt_add_bt_neq _ _ _ Hneq). 
    exact: Hrb.
Qed.


(* ==== correct ==== *)

Definition enc_correct_exp e cs ls vm t :=
  match e with
  | QFBV.Evar _
  | QFBV.Econst _ => 
    forall E s, consistent vm E s 
                -> interp_cnf E (add_prelude cs) 
                -> enc_bits E ls (QFBV.eval_exp e s)
  | QFBV.Eunop op e1 => 
    exists cs1 ls1,
    find_et e1 t = Some (cs1, ls1)
    /\ (forall E s, consistent vm E s 
                    -> enc_bits E ls1 (QFBV.eval_exp e1 s) 
                    -> interp_cnf E (add_prelude cs) 
                    -> enc_bits E ls (QFBV.eval_exp e s))
  | QFBV.Ebinop op e1 e2 => 
    exists cs1 ls1 cs2 ls2,
    find_et e1 t = Some (cs1, ls1) /\ find_et e2 t = Some (cs2, ls2)
    /\ (forall E s, consistent vm E s 
                    -> enc_bits E ls1 (QFBV.eval_exp e1 s) 
                    -> enc_bits E ls2 (QFBV.eval_exp e2 s) 
                    -> interp_cnf E (add_prelude cs) 
                    -> enc_bits E ls (QFBV.eval_exp e s))
  | QFBV.Eite c e1 e2 => 
    exists csc lc cs1 ls1 cs2 ls2,
    find_bt c t = Some (csc, lc) 
    /\ find_et e1 t = Some (cs1, ls1) /\ find_et e2 t = Some (cs2, ls2)
    /\ (forall E s, consistent vm E s 
                    -> enc_bit E lc (QFBV.eval_bexp c s) 
                    -> enc_bits E ls1 (QFBV.eval_exp e1 s) 
                    -> enc_bits E ls2 (QFBV.eval_exp e2 s) 
                    -> interp_cnf E (add_prelude cs) 
                    -> enc_bits E ls (QFBV.eval_exp e s))
  end.

Definition enc_correct_bexp e cs l vm t :=
  match e with
  | QFBV.Bfalse
  | QFBV.Btrue => 
    forall E s, consistent vm E s 
                -> interp_cnf E (add_prelude cs) 
                -> enc_bit E l (QFBV.eval_bexp e s)
  | QFBV.Bbinop op e1 e2 => 
    exists cs1 ls1 cs2 ls2,
    find_et e1 t = Some (cs1, ls1) /\ find_et e2 t = Some (cs2, ls2)
    /\ (forall E s, consistent vm E s 
                    -> enc_bits E ls1 (QFBV.eval_exp e1 s) 
                    -> enc_bits E ls2 (QFBV.eval_exp e2 s) 
                    -> interp_cnf E (add_prelude cs) 
                    -> enc_bit E l (QFBV.eval_bexp e s))
  | QFBV.Blneg e1 => 
    exists cs1 l1,
    find_bt e1 t = Some (cs1, l1)
    /\ (forall E s, consistent vm E s 
                    -> enc_bit E l1 (QFBV.eval_bexp e1 s) 
                    -> interp_cnf E (add_prelude cs) 
                    -> enc_bit E l (QFBV.eval_bexp e s))
  | QFBV.Bconj e1 e2 
  | QFBV.Bdisj e1 e2 => 
    exists cs1 l1 cs2 l2,
    find_bt e1 t = Some (cs1, l1) /\ find_bt e2 t = Some (cs2, l2)
    /\ (forall E s, consistent vm E s 
                    -> enc_bit E l1 (QFBV.eval_bexp e1 s) 
                    -> enc_bit E l2 (QFBV.eval_bexp e2 s) 
                    -> interp_cnf E (add_prelude cs) 
                    -> enc_bit E l (QFBV.eval_bexp e s))
  end.

Definition correct (vm : vm) (t : comptable) :=
  (forall e cs ls, find_et e t = Some (cs, ls) -> enc_correct_exp e cs ls vm t)
  /\ forall e cs l, find_bt e t = Some (cs, l) -> enc_correct_bexp e cs l vm t.

(* Ltac subexp_neq :=  *)
(*   let H := fresh in  *)
(*   move=> H; apply (f_equal QFBV.len_exp) in H; simpl in H; omega. *)

Ltac auto_prove_neq :=
  match goal with
  | H1 : find_et ?e1 ?c = Some _ ,
    H2 : find_et ?e2 ?c = None
    |- ~ is_true (?e1 == ?e2) =>
    let Heq := fresh in
    move=> Heq; move/eqP: Heq => Heq; rewrite Heq H2 in H1; discriminate
  | H1 : find_et ?e1 ?c = None ,
    H2 : find_et ?e2 ?c = Some _
    |- ~ is_true (?e1 == ?e2) => 
    let Heq := fresh in
    move=> Heq; move/eqP: Heq => Heq; rewrite Heq H2 in H1; discriminate
  end.

Lemma add_et_find_none_enc_correct_exp :
  forall e t e0 cs0 ls0 vm cs ls,
    find_et e t = None ->
    enc_correct_exp e0 cs0 ls0 vm t ->
    enc_correct_exp e0 cs0 ls0 vm (add_et e cs ls t).
Proof.
  move=> e t e0 cs0 ls0 vm cs ls Hfe.
  case e0 => /=.
  - done.
  - done.
  - move=> op e1 [cs1 [ls1 [Hfe1 Hence]]].
    exists cs1, ls1. split; last done.
    rewrite -Hfe1. apply find_et_add_et_neq. by auto_prove_neq.
  - move=> op e1 e2 [cs1 [ls1 [cs2 [ls2 [Hfe1 [Hfe2 Hence]]]]]].
    exists cs1, ls1, cs2, ls2.     
    split; last split; last done; [rewrite -Hfe1 | rewrite -Hfe2]; 
      apply find_et_add_et_neq; by auto_prove_neq.
  - move=> c e1 e2 [csc [lc [cs1 [ls1 [cs2 [ls2 [Hfc [Hfe1 [Hfe2 Hence]]]]]]]]].
    exists csc, lc, cs1, ls1, cs2, ls2.
    repeat split; last done.
    + rewrite -Hfc. by apply find_bt_add_et. 
    + rewrite -Hfe1. apply find_et_add_et_neq. by auto_prove_neq.
    + rewrite -Hfe2. apply find_et_add_et_neq. by auto_prove_neq.
Qed.

Lemma add_et_find_none_enc_correct_bexp :
  forall e t e0 cs0 l0 vm cs ls,
    find_et e t = None ->
    enc_correct_bexp e0 cs0 l0 vm t ->
    enc_correct_bexp e0 cs0 l0 vm (add_et e cs ls t).
Proof.
  move=> e t e0 cs0 l0 vm cs ls Hfe.
  case e0 => /=.
  - done.
  - done.
  - move=> op e1 e2 [cs1 [ls1 [cs2 [ls2 [Hfe1 [Hfe2 Hence]]]]]].
    exists cs1, ls1, cs2, ls2.     
    split; last split; last done; [rewrite -Hfe1 | rewrite -Hfe2];
      apply find_et_add_et_neq; by auto_prove_neq.
  - move=> e1 [cs1 [l1 [Hfe1 Hence]]].
    exists cs1, l1. split; last done.
    rewrite -Hfe1. by apply find_bt_add_et. 
  - move=> e1 e2 [cs1 [l1 [cs2 [l2 [Hfe1 [Hfe2 Hence]]]]]].
    exists cs1, l1, cs2, l2.     
    split; last split; last done; [rewrite -Hfe1 | rewrite -Hfe2];
      by apply find_bt_add_et.
  - move=> e1 e2 [cs1 [l1 [cs2 [l2 [Hfe1 [Hfe2 Hence]]]]]].
    exists cs1, l1, cs2, l2.     
    split; last split; last done; [rewrite -Hfe1 | rewrite -Hfe2];
      by apply find_bt_add_et.
Qed.

Lemma add_bt_find_none_enc_correct_bexp :
  forall e t e0 cs0 l0 vm cs l,
    find_bt e t = None ->
    enc_correct_bexp e0 cs0 l0 vm t ->
    enc_correct_bexp e0 cs0 l0 vm (add_bt e cs l t).
Proof.
Admitted.

Lemma add_bt_find_none_enc_correct_exp :
  forall e t e0 cs0 ls0 vm cs l,
    find_bt e t = None ->
    enc_correct_exp e0 cs0 ls0 vm t ->
    enc_correct_exp e0 cs0 ls0 vm (add_bt e cs l t).
Proof.
Admitted.

Lemma correct_add_et :
  forall vm t e cs ls, 
    correct vm t
    -> find_et e t = None
    -> enc_correct_exp e cs ls vm t
    -> correct vm (add_et e cs ls t).
Proof.
  move=> vm t e cs ls [Hce Hcb] Hfe Hence. rewrite /correct /=. 
  split. 
  - move=> e0 cs0 ls0. case Heq : (e0 == e).
    + move/eqP: Heq => Heq. rewrite Heq find_et_add_et_eq. case=> <- <-.
      move: Hence.
      exact: add_et_find_none_enc_correct_exp.
    + move/negP: Heq => Hneq. rewrite (find_et_add_et_neq _ _ _ Hneq).
      move=> Hfe0. move: (Hce _ _ _ Hfe0) => {Hence}.
      exact: add_et_find_none_enc_correct_exp.
  - move=> e0 cs0 l0 Hfe0.
    move: (Hcb _ _ _ Hfe0) => {Hence}.
    exact: add_et_find_none_enc_correct_bexp.
Qed.

Lemma correct_add_bt :
  forall vm t e cs l, 
    correct vm t
    -> find_bt e t = None
    -> enc_correct_bexp e cs l vm t
    -> correct vm (add_bt e cs l t).
Proof.
  move=> vm t e cs ls [Hce Hcb] Hfe Hence. rewrite /correct /=. 
  split. 
  - move=> e0 cs0 ls0 Hfe0. 
    move: (Hce _ _ _ Hfe0) => {Hence}.
    exact: add_bt_find_none_enc_correct_exp.
  - move=> e0 cs0 l0. case Heq : (e0 == e).
    + move/eqP: Heq => Heq. rewrite Heq find_bt_add_bt_eq. case=> <- <-. 
      move: Hence.
      exact: add_bt_find_none_enc_correct_bexp.
    + move/negP: Heq => Hneq. rewrite (find_bt_add_bt_neq _ _ _ Hneq).
      move=> Hfe0. move: (Hcb _ _ _ Hfe0) => {Hence}.
      exact: add_bt_find_none_enc_correct_bexp.
Qed.

Lemma vm_preserve_enc_correct_exp :
  forall m m' e cs ls t, 
    vm_preserve m m' -> enc_correct_exp e cs ls m t -> enc_correct_exp e cs ls m' t.
Proof.
  move=> m m' e cs ls t Hpmmp. 
  case e => /=;
    [ move=> v Henc |
      move=> bs Henc |
      move=> op e1 [cs1 [ls1 [Hfe1 Henc]]]; exists cs1, ls1 |
      move=> op e1 e2 [cs1 [ls1 [cs2 [ls2 [Hfe1 [Hfe2 Henc]]]]]]; 
             exists cs1, ls1, cs2, ls2 |
      move=> c e1 e2 [csc [lc [cs1 [ls1 [cs2 [ls2 [Hfc [Hfe1 [Hfe2 Henc]]]]]]]]];
             exists csc, lc, cs1, ls1, cs2, ls2 ];
    repeat (split; first done); move=> E s Hconmp;
    move: (vm_preserve_consistent Hpmmp Hconmp) => Hconm; by apply: Henc.
Qed.

Lemma vm_preserve_enc_correct_bexp :
  forall m m' e cs l t, 
    vm_preserve m m' -> enc_correct_bexp e cs l m t -> enc_correct_bexp e cs l m' t.
Proof.
  move=> m m' e cs l t Hpmmp. 
  case e => /=;
    [ move=> Henc |
      move=> Henc |
      move=> op e1 e2 [cs1 [ls1 [cs2 [ls2 [Hfe1 [Hfe2 Henc]]]]]];
             exists cs1, ls1, cs2, ls2 |
      move=> e1 [cs1 [l1 [Hfe1 Henc]]];
             exists cs1, l1 |
      move=> e1 e2 [cs1 [l1 [cs2 [l2 [Hfe1 [Hfe2 Henc]]]]]];
             exists cs1, l1, cs2, l2 |
      move=> e1 e2 [cs1 [l1 [cs2 [l2 [Hfe1 [Hfe2 Henc]]]]]];
             exists cs1, l1, cs2, l2 ];
    repeat (split; first done); move=> E s Hconmp;
    move: (vm_preserve_consistent Hpmmp Hconmp) => Hconm; by apply: Henc.
Qed.

Lemma vm_preserve_correct :
  forall m m' t, vm_preserve m m' -> correct m t -> correct m' t.
Proof.
  move=> m m' c Hpmmp [Hce Hcb]. rewrite /correct. split.
  - move=> e cs ls Hfind. move: (Hce _ _ _ Hfind) => Hencm.
    by apply: (@vm_preserve_enc_correct_exp m).
  - move=> e cs l Hfind. move: (Hcb _ _ _ Hfind) => Hencm.
    by apply: (@vm_preserve_enc_correct_bexp m).
Qed.


(* ==== newer_than_table ==== *)

Definition newer_than_table g (t : comptable) :=
  (forall e cs ls, find_et e t = Some (cs, ls) 
                   -> newer_than_cnf g cs && newer_than_lits g ls)
  /\ forall e cs l, find_bt e t = Some (cs, l) 
                    -> newer_than_cnf g cs && newer_than_lit g l.

Lemma env_preserve_interp_table E E' g t :
  env_preserve E E' g -> newer_than_table g t ->
  interp_table E' t <-> interp_table E t.
Proof.
  move=> Henv [Hge Hgb]. rewrite /interp_table. split.
  - apply env_preserve_sym in Henv. move=> [H1 H2]. 
    split; move=> e cs ls Hfind.
    + move: (Hge _ _ _ Hfind) => /andP [Hgcs _].
      rewrite (env_preserve_cnf Henv Hgcs). exact: (H1 _ _ _ Hfind).
    + move: (Hgb _ _ _ Hfind) => /andP [Hgcs _].
      rewrite (env_preserve_cnf Henv Hgcs). exact: (H2 _ _ _ Hfind).
  - move=> [H1 H2]. 
    split; move=> e cs ls Hfind.
    + move: (Hge _ _ _ Hfind) => /andP [Hgcs _].
      rewrite (env_preserve_cnf Henv Hgcs). exact: (H1 _ _ _ Hfind).
    + move: (Hgb _ _ _ Hfind) => /andP [Hgcs _].
      rewrite (env_preserve_cnf Henv Hgcs). exact: (H2 _ _ _ Hfind).
Qed.    

(*
Lemma env_preserve_correct E E' s g ca :
  env_preserve E E' g -> newer_than_cache g ca ->
  correct E' s ca <-> correct E s ca.
Proof.
  move=> Henv [Hge Hgb]. rewrite /correct. split.
  - apply env_preserve_sym in Henv. move=> [H1 H2]. 
    split; move=> e cs ls Hfind.
    + move: (Hge _ _ _ Hfind) => /andP [_ Hgls].
      apply (env_preserve_enc_bits Henv Hgls). exact: (H1 _ _ _ Hfind).
    + move: (Hgb _ _ _ Hfind) => /andP [_ Hgls].
      apply (env_preserve_enc_bit Henv Hgls). exact: (H2 _ _ _ Hfind).
  - move=> [H1 H2]. 
    split; move=> e cs ls Hfind.
    + move: (Hge _ _ _ Hfind) => /andP [_ Hgls].
      apply (env_preserve_enc_bits Henv Hgls). exact: (H1 _ _ _ Hfind).
    + move: (Hgb _ _ _ Hfind) => /andP [_ Hgls].
      apply (env_preserve_enc_bit Henv Hgls). exact: (H2 _ _ _ Hfind).
Qed.    
*)


(* ==== bound by vm ==== *)

Definition bound (t : comptable) (vm : vm) :=
  (forall e cs ls, find_et e t = Some (cs, ls) -> bound_exp e vm)
  /\ forall e cs l, find_bt e t = Some (cs, l) -> bound_bexp e vm.

Lemma bound_add_et :
  forall t vm e cs ls, bound t vm /\ bound_exp e vm -> bound (add_et e cs ls t) vm.
Proof.
  move=> t vm e cs ls [[Hbe Hbb] Hbnde]. rewrite /bound /=. split; last done.
  move=> e0 cs0 ls0. case Heq : (e0 == e).
  - move/eqP: Heq => ->. done. 
  - move/negP: Heq => Hneq. rewrite (find_et_add_et_neq _ _ _ Hneq). exact: Hbe.
Qed.

Lemma bound_add_bt :
  forall t vm e cs l, bound t vm /\ bound_bexp e vm -> bound (add_bt e cs l t) vm.
Proof.
  move=> t vm e cs l [[Hbe Hbb] Hbnde]. rewrite /bound /=. split; first done.
  move=> e0 cs0 l0. case Heq : (e0 == e).
  - move/eqP: Heq => ->. done.
  - move/negP: Heq => Hneq. rewrite (find_bt_add_bt_neq _ _ _ Hneq). exact: Hbb.
Qed.

Lemma bound_add_find_none :
  forall t vm v ls,
    bound t vm -> SSAVM.find v vm = None -> bound t (SSAVM.add v ls vm).
Proof.
  move=> t vm v ls [Hbe Hbb] Hfind. 
  move: (vm_preserve_add_diag ls Hfind) => Hpre.
  split. 
  - move=> e0 cs0 ls0 Hfet. move: (Hbe _ _ _ Hfet) => Hbvm.
    exact: (vm_preserve_bound_exp Hbvm Hpre).
  - move=> e0 cs0 l0 Hfbt. move: (Hbb _ _ _ Hfbt) => Hbvm.
    exact: (vm_preserve_bound_bexp Hbvm Hpre).
Qed.


(* ==== CompTable preserve ==== *)

Definition preserve (t t' : comptable) : Prop :=
  (forall e cs ls, find_et e t = Some (cs, ls) -> find_et e t' = Some (cs, ls))
  /\ forall e cs l, find_bt e t = Some (cs, l) -> find_bt e t' = Some (cs, l).
