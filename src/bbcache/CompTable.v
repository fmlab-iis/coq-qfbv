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


(* == A table storing complete results, including CNF and literal(s) == *)

Record comptable :=
  { et : expm;
    bt : bexpm }.

Definition empty : comptable := 
  {| et := ExpMap.empty (cnf * word);
     bt := BexpMap.empty (cnf * literal) |}.

Definition find_et e t := ExpMap.find e (et t).
Definition find_bt e t := BexpMap.find e (bt t).


(* ==== modification ==== *)

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

Lemma find_et_add_et_neq :
  forall e0 e cs ls t, ~ e0 == e -> find_et e0 (add_et e cs ls t) = find_et e0 t.
Proof.
  move=> e0 e cs ls t Hneq. by apply: ExpMap.Lemmas.find_add_neq.
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

Lemma find_bt_add_bt_eq :
  forall e cs l t, find_bt e (add_bt e cs l t) = Some (cs, l).
Proof.
  move=> e cs l t. rewrite /find_bt /add_bt /=. 
  by apply: BexpMap.Lemmas.find_add_eq.
Qed.

Lemma find_bt_add_bt_neq :
  forall e0 e cs l t, ~ e0 == e -> find_bt e0 (add_bt e cs l t) = find_bt e0 t .
Proof.
  move=> e0 e cs l t Hneq. by apply: BexpMap.Lemmas.find_add_neq. 
Qed.


(* ==== interp_table === *)

Definition interp_table (E : env) (t : comptable) :=
  (forall e cs ls, find_et e t = Some (cs, ls) -> interp_cnf E cs)
  /\ forall e cs l, find_bt e t = Some (cs, l) -> interp_cnf E cs.

Lemma interp_table_find_et :
  forall E t e cs ls,
    interp_table E t -> find_et e t = Some (cs, ls) -> interp_cnf E cs.
Proof.
  move=> E t e cs ls [Hie Hib]. by apply Hie.
Qed.

Lemma interp_table_find_bt :
  forall E t e cs l,
    interp_table E t -> find_bt e t = Some (cs, l) -> interp_cnf E cs.
Proof.
  move=> E t e cs l [Hie Hib]. by apply Hib.
Qed.

Lemma interp_table_add_et :
  forall E t e cs ls, interp_table E t -> interp_cnf E cs ->
                      interp_table E (add_et e cs ls t).
Proof.
  move=> E t e cs ls [Hre Hrb] Hcs. rewrite /interp_table /=. split; last done.
  move=> e0 cs0 ls0. case Heq : (e0 == e).
  - move/eqP: Heq => <-. rewrite find_et_add_et_eq. case=> <- _; done.
  - move/negP: Heq => Hneq. rewrite (find_et_add_et_neq _ _ _ Hneq).
    exact: Hre.
Qed.

Lemma interp_table_add_bt :
  forall E t e cs l, interp_table E t -> interp_cnf E cs ->
                     interp_table E (add_bt e cs l t).
Proof.
  move=> E t e cs l [Hre Hrb] Hcs. rewrite /interp_table /=. split; first done.
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
                    -> 0 < size ls1
                    -> size ls1 == size ls2
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
                    -> size ls1 == size ls2
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
                    -> size ls1 == size ls2
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

Lemma correct_find_et :
  forall vm t e cs ls,
    correct vm t -> find_et e t = Some (cs, ls) -> enc_correct_exp e cs ls vm t.
Proof. 
  move=> vm t e cs ls [Hcre Hcrb]. by apply Hcre.
Qed.

Lemma correct_find_bt :
  forall vm t e cs l,
    correct vm t -> find_bt e t = Some (cs, l) -> enc_correct_bexp e cs l vm t.
Proof. 
  move=> vm t e cs l [Hcre Hcrb]. by apply Hcrb.
Qed.

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
  | H1 : find_bt ?e1 ?c = Some _ ,
    H2 : find_bt ?e2 ?c = None
    |- ~ is_true (?e1 == ?e2) =>
    let Heq := fresh in
    move=> Heq; move/eqP: Heq => Heq; rewrite Heq H2 in H1; discriminate
  | H1 : find_bt ?e1 ?c = None ,
    H2 : find_bt ?e2 ?c = Some _
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

Lemma add_bt_find_none_enc_correct_exp :
  forall e t e0 cs0 ls0 vm cs l,
    find_bt e t = None ->
    enc_correct_exp e0 cs0 ls0 vm t ->
    enc_correct_exp e0 cs0 ls0 vm (add_bt e cs l t).
Proof.
  move=> e t e0 cs0 ls0 vm cs l Hfe.
  case e0 => /=.
  - done.
  - done.
  - move=> op e1 [cs1 [ls1 [Hfe1 Hence]]].
    exists cs1, ls1. split; last done.
    rewrite -Hfe1. by rewrite find_et_add_bt.
  - move=> op e1 e2 [cs1 [ls1 [cs2 [ls2 [Hfe1 [Hfe2 Hence]]]]]].
    exists cs1, ls1, cs2, ls2.     
    split; last split; last done; [rewrite -Hfe1 | rewrite -Hfe2];
      by rewrite find_et_add_bt.
  - move=> c e1 e2 [csc [lc [cs1 [ls1 [cs2 [ls2 [Hfc [Hfe1 [Hfe2 Hence]]]]]]]]].
    exists csc, lc, cs1, ls1, cs2, ls2.
    repeat split; last done.
    + rewrite -Hfc. apply find_bt_add_bt_neq. by auto_prove_neq.
    + rewrite -Hfe1. by apply find_et_add_bt. 
    + rewrite -Hfe2. by apply find_et_add_bt.
Qed.

Lemma add_bt_find_none_enc_correct_bexp :
  forall e t e0 cs0 l0 vm cs l,
    find_bt e t = None ->
    enc_correct_bexp e0 cs0 l0 vm t ->
    enc_correct_bexp e0 cs0 l0 vm (add_bt e cs l t).
Proof.
  move=> e t e0 cs0 l0 vm cs l Hfe.
  case e0 => /=.
  - done.
  - done.
  - move=> op e1 e2 [cs1 [ls1 [cs2 [ls2 [Hfe1 [Hfe2 Hence]]]]]].
    exists cs1, ls1, cs2, ls2.     
    split; last split; last done; [rewrite -Hfe1 | rewrite -Hfe2];
      by rewrite find_et_add_bt.
  - move=> e1 [cs1 [l1 [Hfe1 Hence]]].
    exists cs1, l1. split; last done.
    rewrite -Hfe1. apply find_bt_add_bt_neq. by auto_prove_neq. 
  - move=> e1 e2 [cs1 [l1 [cs2 [l2 [Hfe1 [Hfe2 Hence]]]]]].
    exists cs1, l1, cs2, l2.     
    split; last split; last done; [rewrite -Hfe1 | rewrite -Hfe2];
      apply find_bt_add_bt_neq; by auto_prove_neq.       
  - move=> e1 e2 [cs1 [l1 [cs2 [l2 [Hfe1 [Hfe2 Hence]]]]]].
    exists cs1, l1, cs2, l2.     
    split; last split; last done; [rewrite -Hfe1 | rewrite -Hfe2];
      apply find_bt_add_bt_neq; by auto_prove_neq.       
Qed.

Lemma correct_add_et :
  forall vm t e cs ls, 
    correct vm t
    -> find_et e t = None
    -> enc_correct_exp e cs ls vm t
    -> correct vm (add_et e cs ls t).
Proof.
  move=> vm t e cs ls Hcr Hfe Hence. split. 
  - move=> e0 cs0 ls0. case Heq : (e0 == e).
    + move/eqP: Heq => Heq. rewrite Heq find_et_add_et_eq. case=> <- <-.
      move: Hence.
      exact: add_et_find_none_enc_correct_exp.
    + move/negP: Heq => Hneq. rewrite (find_et_add_et_neq _ _ _ Hneq).
      move=> Hfe0. move: (correct_find_et Hcr Hfe0) => {Hence}.
      exact: add_et_find_none_enc_correct_exp.
  - move=> e0 cs0 l0 Hfe0.
    move: (correct_find_bt Hcr Hfe0) => {Hence}.
    exact: add_et_find_none_enc_correct_bexp.
Qed.

Lemma correct_add_bt :
  forall vm t e cs l, 
    correct vm t
    -> find_bt e t = None
    -> enc_correct_bexp e cs l vm t
    -> correct vm (add_bt e cs l t).
Proof.
  move=> vm t e cs ls Hcr Hfe Hence. split. 
  - move=> e0 cs0 ls0 Hfe0. 
    move: (correct_find_et Hcr Hfe0) => {Hence}.
    exact: add_bt_find_none_enc_correct_exp.
  - move=> e0 cs0 l0. case Heq : (e0 == e).
    + move/eqP: Heq => Heq. rewrite Heq find_bt_add_bt_eq. case=> <- <-. 
      move: Hence.
      exact: add_bt_find_none_enc_correct_bexp.
    + move/negP: Heq => Hneq. rewrite (find_bt_add_bt_neq _ _ _ Hneq).
      move=> Hfe0. move: (correct_find_bt Hcr Hfe0) => {Hence}.
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
  move=> m m' c Hpmmp Hcr. split.
  - move=> e cs ls Hfind. move: (correct_find_et Hcr Hfind) => Hencm.
    by apply: (@vm_preserve_enc_correct_exp m).
  - move=> e cs l Hfind. move: (correct_find_bt Hcr Hfind) => Hencm.
    by apply: (@vm_preserve_enc_correct_bexp m).
Qed.

Lemma interp_table_find_et_some_correct :
  forall m E s t e cs ls te,
    consistent m E s -> interp_lit E lit_tt
    -> interp_table E t -> find_et e t = Some (cs, ls) 
    -> QFBV.well_formed_exp e te -> conform_exp e s te
    -> correct m t -> enc_bits E ls (QFBV.eval_exp e s)
  with
    interp_table_find_bt_some_correct :
      forall m E s t e cs l te,
        consistent m E s -> interp_lit E lit_tt
        -> interp_table E t -> find_bt e t = Some (cs, l) 
        -> QFBV.well_formed_bexp e te -> conform_bexp e s te
        -> correct m t -> enc_bit E l (QFBV.eval_bexp e s).
Proof.
  (* interp_table_find_et_some_correct *)
  move=> m E s t.
  elim => [v | bs | op e1 IH1 | op e1 IH1 e2 IH2 | b e1 IH1 e2 IH2];
  move=> cs ls te Hcon Htt HiEt Hfe Hwf Hcf Hcrmt;
  move: (interp_table_find_et HiEt Hfe) => Hics;
  move: (add_prelude_to Htt Hics) => {Hics} Hics.
  - move: (correct_find_et Hcrmt Hfe) => /= Hence.
    by apply Hence.
  - move: (correct_find_et Hcrmt Hfe) => /= Hence.
    by apply (Hence E s).
  - move: Hwf Hcf => /= Hwf1 Hcf1.
    move: (correct_find_et Hcrmt Hfe) => /= 
      [cs1 [ls1 [Hfe1 Hence]]].
    move: (IH1 _ _ _ Hcon Htt HiEt Hfe1 Hwf1 Hcf1 Hcrmt) => Henc1.
    by apply Hence.
  - move: Hwf Hcf => /= /andP [/andP [/andP [Hwf1 Hwf2] Hszgt0] Hsize] /andP [Hcf1 Hcf2].
    rewrite -(eval_conform_exp_size Hwf1 Hcf1) 
    -(eval_conform_exp_size Hwf2 Hcf2) in Hsize.
    rewrite  -(eval_conform_exp_size Hwf1 Hcf1) in Hszgt0.
    move: (correct_find_et Hcrmt Hfe) => /= 
      [cs1 [ls1 [cs2 [ls2 [Hfe1 [Hfe2 Hence]]]]]].
    move: (IH1 _ _ _ Hcon Htt HiEt Hfe1 Hwf1 Hcf1 Hcrmt) 
            (IH2 _ _ _ Hcon Htt HiEt Hfe2 Hwf2 Hcf2 Hcrmt) => Henc1 Henc2.
    rewrite -(enc_bits_size Henc1) -(enc_bits_size Henc2) in Hsize.
    rewrite -(enc_bits_size Henc1) in Hszgt0.
    by apply Hence.
  - move: Hwf => /= /andP [/andP [/andP [Hwfb Hwf1] Hwf2] Hsize].
    move: Hcf => /= /andP [/andP [Hcfb Hcf1] Hcf2].
    rewrite -(eval_conform_exp_size Hwf1 Hcf1) 
            -(eval_conform_exp_size Hwf2 Hcf2) in Hsize.
    move: (correct_find_et Hcrmt Hfe) => /= 
      [csb [lb [cs1 [ls1 [cs2 [ls2 [Hfb [Hfe1 [Hfe2 Hence]]]]]]]]].
    move: (interp_table_find_bt_some_correct _ _ _ _ _ _ _ _ 
                                             Hcon Htt HiEt Hfb Hwfb Hcfb Hcrmt) 
            (IH1 _ _ _ Hcon Htt HiEt Hfe1 Hwf1 Hcf1 Hcrmt) 
            (IH2 _ _ _ Hcon Htt HiEt Hfe2 Hwf2 Hcf2 Hcrmt) => Hencb Henc1 Henc2.
    rewrite -(enc_bits_size Henc1) -(enc_bits_size Henc2) in Hsize.
    by apply Hence.
  (* interp_table_find_bt_some_correct *)
  move=> m E s t.
  elim => [ | | op e1 e2 | e1 IH1 | e1 IH1 e2 IH2 | e1 IH1 e2 IH2];
  move=> cs l te Hcon Htt HiEt Hfe Hwf Hcf Hcrmt;
  move: (interp_table_find_bt HiEt Hfe) => Hics;
  move: (add_prelude_to Htt Hics) => {Hics} Hics.
  - move: (correct_find_bt Hcrmt Hfe) => /= Hence.
    by apply (Hence E s).
  - move: (correct_find_bt Hcrmt Hfe) => /= Hence.
    by apply (Hence E s).
  - move: Hwf Hcf => /= /andP [/andP [Hwf1 Hwf2] Hsize] /andP [Hcf1 Hcf2].
    rewrite -(eval_conform_exp_size Hwf1 Hcf1) 
            -(eval_conform_exp_size Hwf2 Hcf2) in Hsize.
    move: (correct_find_bt Hcrmt Hfe) => /= 
      [cs1 [ls1 [cs2 [ls2 [Hfe1 [Hfe2 Hence]]]]]].
    move: (interp_table_find_et_some_correct _ _ _ _ _ _ _ _ 
                                             Hcon Htt HiEt Hfe1 Hwf1 Hcf1 Hcrmt)
          (interp_table_find_et_some_correct _ _ _ _ _ _ _ _ 
                                             Hcon Htt HiEt Hfe2 Hwf2 Hcf2 Hcrmt)
           => Henc1 Henc2.
    rewrite -(enc_bits_size Henc1) -(enc_bits_size Henc2) in Hsize.
    by apply Hence.
  - move: Hwf Hcf => /= Hwf1 Hcf1.
    move: (correct_find_bt Hcrmt Hfe) => /= 
      [cs1 [l1 [Hfe1 Hence]]].
    move: (IH1 _ _ _ Hcon Htt HiEt Hfe1 Hwf1 Hcf1 Hcrmt) => Henc1.
    by apply Hence.
  - move: Hwf Hcf => /= /andP [Hwf1 Hwf2] /andP [Hcf1 Hcf2].
    move: (correct_find_bt Hcrmt Hfe) => /= 
      [cs1 [l1 [cs2 [l2 [Hfe1 [Hfe2 Hence]]]]]].
    move: (IH1 _ _ _ Hcon Htt HiEt Hfe1 Hwf1 Hcf1 Hcrmt) 
            (IH2 _ _ _ Hcon Htt HiEt Hfe2 Hwf2 Hcf2 Hcrmt) => Henc1 Henc2.
    by apply Hence.
  - move: Hwf Hcf => /= /andP [Hwf1 Hwf2] /andP [Hcf1 Hcf2].
    move: (correct_find_bt Hcrmt Hfe) => /= 
      [cs1 [l1 [cs2 [l2 [Hfe1 [Hfe2 Hence]]]]]].
    move: (IH1 _ _ _ Hcon Htt HiEt Hfe1 Hwf1 Hcf1 Hcrmt) 
            (IH2 _ _ _ Hcon Htt HiEt Hfe2 Hwf2 Hcf2 Hcrmt) => Henc1 Henc2.
    by apply Hence.
Qed. 


(* ==== newer_than_table ==== *)

Definition newer_than_table g (t : comptable) :=
  (forall e cs ls, find_et e t = Some (cs, ls) 
                   -> newer_than_cnf g cs /\ newer_than_lits g ls)
  /\ forall e cs l, find_bt e t = Some (cs, l) 
                    -> newer_than_cnf g cs /\ newer_than_lit g l.

Lemma newer_than_table_find_et :
  forall g t e cs ls,
    newer_than_table g t -> find_et e t = Some (cs, ls) 
    -> newer_than_cnf g cs /\ newer_than_lits g ls.
Proof. 
  move=> g t e cs ls [He Hb] Hfe. exact: (He _ _ _ Hfe).
Qed.

Lemma newer_than_table_find_bt :
  forall g t e cs l,
    newer_than_table g t -> find_bt e t = Some (cs, l) 
    -> newer_than_cnf g cs /\ newer_than_lit g l.
Proof. 
  move=> g t e cs ls [He Hb] Hfe. exact: (Hb _ _ _ Hfe).
Qed.

Lemma newer_than_table_add_et :
  forall g t e cs ls, 
    newer_than_table g t -> newer_than_cnf g cs -> newer_than_lits g ls 
    -> newer_than_table g (add_et e cs ls t).
Proof.
  move=> g t e cs ls Hgt Hgcs Hgls. split.
  - move=> e0 cs0 ls0. case Heq : (e0 == e).
    + move/eqP: Heq => <-. rewrite find_et_add_et_eq. case=> <- <-. split; done.
    + move/negP: Heq => Hneq. rewrite (find_et_add_et_neq _ _ _ Hneq).
      move=> Hfe. exact: (newer_than_table_find_et Hgt Hfe).
  - move=> e0 cs0 ls0. rewrite find_bt_add_et => Hfe. 
    exact: (newer_than_table_find_bt Hgt Hfe).
Qed.

Lemma newer_than_table_add_bt :
  forall g t e cs l, 
    newer_than_table g t -> newer_than_cnf g cs -> newer_than_lit g l 
    -> newer_than_table g (add_bt e cs l t).
Proof. 
  move=> g t e cs l Hgt Hgcs Hgl. split.
  - move=> e0 cs0 ls0. rewrite find_et_add_bt => Hfe. 
    exact: (newer_than_table_find_et Hgt Hfe).
  - move=> e0 cs0 ls0. case Heq : (e0 == e).
    + move/eqP: Heq => <-. rewrite find_bt_add_bt_eq. case=> <- <-. split; done.
    + move/negP: Heq => Hneq. rewrite (find_bt_add_bt_neq _ _ _ Hneq).
      move=> Hfe. exact: (newer_than_table_find_bt Hgt Hfe).
Qed.

Lemma newer_than_table_le_newer g g' t :
  newer_than_table g t -> (g <=? g')%positive -> newer_than_table g' t.
Proof.
  move=> [Hnewe Hnewb] Hgg'. split.
  - move=> e cs ls Hfind. move: (Hnewe _ _ _ Hfind) => [Hgcs Hgls].
    move: (newer_than_cnf_le_newer Hgcs Hgg').
    move: (newer_than_lits_le_newer Hgls Hgg'). done.
  - move=> e cs l Hfind. move: (Hnewb _ _ _ Hfind) => [Hgcs Hgl].
    move: (newer_than_cnf_le_newer Hgcs Hgg').
    move: (newer_than_lit_le_newer Hgl Hgg'). done.
Qed.

Lemma env_preserve_interp_table E E' g t :
  env_preserve E E' g -> newer_than_table g t ->
  interp_table E' t <-> interp_table E t.
Proof.
  move=> Hpre Hgt. split.
  - apply env_preserve_sym in Hpre. move=> HiEpt. 
    split; move=> e cs ls Hfind.
    + move: (newer_than_table_find_et Hgt Hfind) => [Hgcs _].
      rewrite (env_preserve_cnf Hpre Hgcs). 
      exact: (interp_table_find_et HiEpt Hfind).
    + move: (newer_than_table_find_bt Hgt Hfind) => [Hgcs _].
      rewrite (env_preserve_cnf Hpre Hgcs). 
      exact: (interp_table_find_bt HiEpt Hfind).
  - move=> HiEpt. 
    split; move=> e cs ls Hfind.
    + move: (newer_than_table_find_et Hgt Hfind) => [Hgcs _].
      rewrite (env_preserve_cnf Hpre Hgcs). 
      exact: (interp_table_find_et HiEpt Hfind).
    + move: (newer_than_table_find_bt Hgt Hfind) => [Hgcs _].
      rewrite (env_preserve_cnf Hpre Hgcs). 
      exact: (interp_table_find_bt HiEpt Hfind).
Qed.


(* ==== bound by vm ==== *)

Definition bound (t : comptable) (vm : vm) :=
  (forall e cs ls, find_et e t = Some (cs, ls) -> bound_exp e vm)
  /\ forall e cs l, find_bt e t = Some (cs, l) -> bound_bexp e vm.

Lemma bound_find_et :
  forall t m e cs ls, 
    bound t m -> find_et e t = Some (cs, ls) -> bound_exp e m.
Proof. 
  move=> t m e cs ls [Hbe Hbb]. exact: Hbe.
Qed.

Lemma bound_find_bt :
  forall t m e cs l, 
    bound t m -> find_bt e t = Some (cs, l) -> bound_bexp e m.
Proof. 
  move=> t m e cs ls [Hbe Hbb]. exact: Hbb.
Qed.

Lemma bound_add_et :
  forall t vm e cs ls, bound t vm -> bound_exp e vm -> bound (add_et e cs ls t) vm.
Proof.
  move=> t vm e cs ls [Hbe Hbb] Hbnde. split; last done.
  move=> e0 cs0 ls0. case Heq : (e0 == e).
  - move/eqP: Heq => ->. done. 
  - move/negP: Heq => Hneq. rewrite (find_et_add_et_neq _ _ _ Hneq). exact: Hbe.
Qed.

Lemma bound_add_bt :
  forall t vm e cs l, bound t vm -> bound_bexp e vm -> bound (add_bt e cs l t) vm.
Proof.
  move=> t vm e cs l [Hbe Hbb] Hbnde. split; first done.
  move=> e0 cs0 l0. case Heq : (e0 == e).
  - move/eqP: Heq => ->. done.
  - move/negP: Heq => Hneq. rewrite (find_bt_add_bt_neq _ _ _ Hneq). exact: Hbb.
Qed.

Lemma vm_preserve_bound :
  forall m m' t, vm_preserve m m' -> bound t m -> bound t m'.
Proof.
  move=> m m' t Hpre [Hbe Hbb]. split.
  - move=> e cs ls Hfind. move: (Hbe _ _ _ Hfind) => Hbdm.
    exact: (vm_preserve_bound_exp Hbdm Hpre).
  - move=> e cs l Hfind. move: (Hbb _ _ _ Hfind) => Hbdm.
    exact: (vm_preserve_bound_bexp Hbdm Hpre).
Qed.


(* ==== preserve ==== *)

Definition preserve (t t' : comptable) : Prop :=
  (forall e cs ls, find_et e t = Some (cs, ls) -> find_et e t' = Some (cs, ls))
  /\ forall e cs l, find_bt e t = Some (cs, l) -> find_bt e t' = Some (cs, l).

Lemma preserve_refl : forall t, preserve t t.
Proof.
  done.
Qed.

Lemma preserve_trans :
  forall t1 t2 t3, preserve t1 t2 -> preserve t2 t3 -> preserve t1 t3.
Proof. 
  move=> t1 t2 t3 [Hpe12 Hpb12] [Hpe23 Hpb23]. split.
  - move=> e cs ls Hf1. move: (Hpe12 _ _ _ Hf1). exact: Hpe23.
  - move=> e cs l Hf1. move: (Hpb12 _ _ _ Hf1). exact: Hpb23.
Qed.

Lemma preserve_find_et :
  forall t t' e cs ls,
    preserve t t' -> 
    find_et e t = Some (cs, ls) -> find_et e t' = Some (cs, ls).
Proof.
  move=> t t' e cs ls [Hpe Hpb]. exact: Hpe.
Qed.

Lemma preserve_find_bt :
  forall t t' e cs l,
    preserve t t' -> 
    find_bt e t = Some (cs, l) -> find_bt e t' = Some (cs, l).
Proof.
  move=> t t' e cs ls [Hpe Hpb]. exact: Hpb.
Qed.

Lemma preserve_add_et :
  forall t1 t2 e cs ls,
    preserve t1 t2 -> find_et e t2 = None -> preserve t1 (add_et e cs ls t2).
Proof. 
  move=> t1 t2 e cs ls Hpre Hfe. split.
  - move=> e0 cs0 ls0 Hfe0. move: (preserve_find_et Hpre Hfe0) => {Hfe0} Hfe0.
    have Hneq : ~ (e0 == e) by auto_prove_neq.
    rewrite (find_et_add_et_neq _ _ _ Hneq). done.
  - move=> e0 cs0 l0 Hfe0. move: (preserve_find_bt Hpre Hfe0) => {Hfe0} Hfe0.
    by rewrite find_bt_add_et.
Qed.

Lemma preserve_add_bt :
  forall t1 t2 e cs l,
    preserve t1 t2 -> find_bt e t2 = None -> preserve t1 (add_bt e cs l t2).
Proof. 
  move=> t1 t2 e cs l Hpre Hfe. split.
  - move=> e0 cs0 ls0 Hfe0. move: (preserve_find_et Hpre Hfe0) => {Hfe0} Hfe0.
    by rewrite find_et_add_bt.
  - move=> e0 cs0 l0 Hfe0. move: (preserve_find_bt Hpre Hfe0) => {Hfe0} Hfe0.
    have Hneq : ~ (e0 == e) by auto_prove_neq.
    rewrite (find_bt_add_bt_neq _ _ _ Hneq). done.
Qed.
