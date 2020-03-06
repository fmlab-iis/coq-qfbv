From Coq Require Import ZArith OrderedType Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import FMaps Var. 
From BitBlasting Require Import QFBV CNF State AdhereConform BBCommon.
From newBBCache Require Import CompTable.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Module ExpMap <: SsrFMap := FMaps.MakeTreeMap QFBV.ExpOrder. *)
(* Module BexpMap <: SsrFMap := FMaps.MakeTreeMap QFBV.BexpOrder. *)

(* Definition cexpm := ExpMap.t (cnf * word). *)
(* Definition cbexpm := BexpMap.t (cnf * literal). *)
(* Definition hexpm := ExpMap.t (cnf * word). *)
(* Definition hbexpm := BexpMap.t (cnf * literal). *)

(* ==== A cache with complete information in both current and historical tables ==== *)

Record compcache :=
  { (* store historical results *)
    ht : comptable;
    (* store current results *)
    ct : comptable }.

Definition find_het e c := find_et e (ht c).
Definition find_hbt e c := find_bt e (ht c). 
Definition find_cet e c := find_et e (ct c). 
Definition find_cbt e c := find_bt e (ct c). 

(* Definition get_het e c := *)
(*   match find_het e c with *)
(*   | Some (cs, ls) => (cs, ls) *)
(*   | None => ([::], [::lit_tt]) (* default value, in fact never used *) *)
(*   end. *)

(* Definition get_hbt e c := *)
(*   match find_hbt e c with *)
(*   | Some (cs, l) => (cs, l) *)
(*   | None => ([::], lit_tt) (* default value, in fact never used *) *)
(*   end. *)


(* Definition find_cnf_exp e c := *)
(*   match find_het e c with *)
(*   | None => [::] *)
(*   | Some (cs, ls) => cs *)
(*   end. *)
(* Definition find_cnf_bexp e c := *)
(*   match find_hbt e c with *)
(*   | None => [::] *)
(*   | Some (cs, l) => cs *)
(*   end. *)
(* Definition find_lits_exp e c := *)
(*   match find_het e c with *)
(*   | None => [::lit_tt] *)
(*   | Some (cs, ls) => ls *)
(*   end. *)
(* Definition find_lit_bexp e c := *)
(*   match find_hbt e c with *)
(*   | None => lit_tt *)
(*   | Some (cs, l) => l *)
(*   end. *)

Definition add_het e cs ls c := 
  {| ht := add_et e cs ls (ht c);
     ct := ct c |}.
Definition add_hbt e cs l c := 
  {| ht := add_bt e cs l (ht c);
     ct := ct c |}.
Definition add_cet e cs ls c := 
  {| ht := ht c;
     ct := add_et e cs ls (ct c) |}.
Definition add_cbt e cs l c := 
  {| ht := ht c;
     ct := add_bt e cs l (ct c) |}.

Definition reset_ct (c : compcache) :=
  {| ht := ht c;
     ct := {| et := ExpMap.empty (cnf * word);
              bt := BexpMap.empty (cnf * literal) |} |}.

Lemma find_het_add_het_eq :
  forall e cs ls c, find_het e (add_het e cs ls c) = Some (cs, ls).
Proof.
  move=> e cs ls c. rewrite /find_het /add_het /=. 
  by apply: CompTable.find_et_add_et_eq.
Qed.

Lemma find_hbt_add_hbt_eq :
  forall e cs l c, find_hbt e (add_hbt e cs l c) = Some (cs, l).
Proof.
  move=> e cs l c. rewrite /find_hbt /add_hbt /=. 
  by apply: CompTable.find_bt_add_bt_eq.
Qed.

Lemma find_het_add_het_neq :
  forall e0 e cs ls c, ~ e0 == e -> find_het e0 (add_het e cs ls c) = find_het e0 c.
Proof.
  move=> e0 e cs ls c. rewrite /find_het /add_het /=. 
  by apply: CompTable.find_et_add_et_neq.
Qed.

Lemma find_hbt_add_hbt_neq :
  forall e0 e cs l c, ~ e0 == e -> find_hbt e0 (add_hbt e cs l c) = find_hbt e0 c.
Proof.
  move=> e0 e cs l c. rewrite /find_hbt /add_hbt /=.
  by apply: CompTable.find_bt_add_bt_neq.
Qed.

Lemma find_het_add_hbt :
  forall e0 e cs l c, find_het e0 (add_hbt e cs l c) = find_het e0 c.
Proof.
  move=> e0 e cs l c. rewrite /find_het /add_hbt /=.
  by apply: CompTable.find_et_add_bt.
Qed.

Lemma find_hbt_add_het :
  forall e0 e cs ls c, find_hbt e0 (add_het e cs ls c) = find_hbt e0 c.
Proof.
  move=> e0 e cs ls c. rewrite /find_hbt /add_het /=.
  by apply: CompTable.find_bt_add_et.
Qed.

Lemma find_cet_add_cet_eq :
  forall e cs ls c, find_cet e (add_cet e cs ls c) = Some (cs, ls).
Proof.
  move=> e cs ls c. rewrite /find_cet /add_cet /=. 
  by apply: CompTable.find_et_add_et_eq.
Qed.

Lemma find_cbt_add_cbt_eq :
  forall e cs l c, find_cbt e (add_cbt e cs l c) = Some (cs, l).
Proof.
  move=> e cs l c. rewrite /find_cbt /add_cbt /=. 
  by apply: CompTable.find_bt_add_bt_eq.
Qed.

Lemma find_cet_add_cet_neq :
  forall e0 e cs ls c, ~ e0 == e -> find_cet e0 (add_cet e cs ls c) = find_cet e0 c.
Proof.
  move=> e0 e cs ls c. rewrite /find_cet /add_cet /=. 
  by apply: CompTable.find_et_add_et_neq.
Qed.

Lemma find_cbt_add_cbt_neq :
  forall e0 e cs l c, ~ e0 == e -> find_cbt e0 (add_cbt e cs l c) = find_cbt e0 c.
Proof.
  move=> e0 e cs l c. rewrite /find_cbt /add_cbt /=.
  by apply: CompTable.find_bt_add_bt_neq.
Qed.

Lemma find_cet_add_cbt :
  forall e0 e cs l c, find_cet e0 (add_cbt e cs l c) = find_cet e0 c.
Proof.
  move=> e0 e cs l c. rewrite /find_cet /add_cbt /=.
  by apply: CompTable.find_et_add_bt.
Qed.

Lemma find_cbt_add_cet :
  forall e0 e cs ls c, find_cbt e0 (add_cet e cs ls c) = find_cbt e0 c.
Proof.
  move=> e0 e cs ls c. rewrite /find_cbt /add_cet /=.
  by apply: CompTable.find_bt_add_et.
Qed.

Lemma find_cet_add_het :
  forall e0 e cs ls c, find_cet e0 (add_het e cs ls c) = find_cet e0 c.
Proof.
Admitted.

Lemma find_cet_add_hbt :
  forall e0 e cs l c, find_cet e0 (add_hbt e cs l c) = find_cet e0 c.
Proof.
Admitted.

Lemma find_het_add_cet :
  forall e0 e cs ls c, find_het e0 (add_cet e cs ls c) = find_het e0 c.
Proof.
Admitted.

Lemma find_het_add_cbt :
  forall e0 e cs l c, find_het e0 (add_cbt e cs l c) = find_het e0 c.
Proof.
Admitted.






(*
Lemma find_cnf_exp_add_het_eq :
  forall e cs ls c, find_cnf_exp e (add_het e cs ls c) = cs.
Proof.
  move=> e cs ls c. rewrite /find_cnf_exp find_het_add_het_eq. done.
Qed.

Lemma find_lits_exp_add_het_eq :
  forall e cs ls c, find_lits_exp e (add_het e cs ls c) = ls.
Proof.
  move=> e cs ls c. rewrite /find_lits_exp find_het_add_het_eq. done.
Qed.

Lemma find_cnf_bexp_add_hbt_eq :
  forall e cs l c, find_cnf_bexp e (add_hbt e cs l c) = cs.
Proof.
  move=> e cs l c. rewrite /find_cnf_bexp find_hbt_add_hbt_eq. done.
Qed.

Lemma find_lit_bexp_add_hbt_eq :
  forall e cs l c, find_lit_bexp e (add_hbt e cs l c) = l.
Proof.
  move=> e cs l c. rewrite /find_lit_bexp find_hbt_add_hbt_eq. done.
Qed.
*)


(* ==== well_formed ==== *)

Definition well_formed (c : compcache) : Prop := 
  (forall e cs ls, find_cet e c = Some (cs, ls)
                   -> find_het e c = Some (cs, ls))
  /\ forall e cs l, find_cbt e c = Some (cs, l)
                    -> find_hbt e c = Some (cs, l).

Lemma well_formed_find_cet :
  forall c e cs ls,
    well_formed c -> find_cet e c = Some (cs, ls) -> find_het e c = Some (cs, ls).
Proof. Admitted.

Lemma well_formed_find_cbt :
  forall c e cs l,
    well_formed c -> find_cbt e c = Some (cs, l) -> find_hbt e c = Some (cs, l).
Proof. Admitted.

Lemma well_formed_add_cet :
  forall c e cs ls,
    well_formed c -> find_het e c = Some (cs, ls) -> well_formed (add_cet e cs ls c).
Proof. Admitted.

Lemma well_formed_add_cbt :
  forall c e cs l,
    well_formed c -> find_hbt e c = Some (cs, l) -> well_formed (add_cbt e cs l c).
Proof. Admitted.

Lemma well_formed_add_cet_het :
  forall c e cs ls,
    well_formed c -> well_formed (add_cet e cs ls (add_het e cs ls c)).
Proof. Admitted.

Lemma well_formed_add_cbt_hbt :
  forall c e cs l,
    well_formed c -> well_formed (add_cbt e cs l (add_hbt e cs l c)).
Proof. Admitted.

Lemma reset_ct_well_formed :
  forall c, well_formed (reset_ct c).
Proof.
(*   done. *)
(* Qed. *)
Admitted.


(* ==== interp_cache === *)

Definition interp_cache_ct (E : env) (c : compcache) := CompTable.interp_table E (ct c).
Definition interp_cache_ht (E : env) (c : compcache) := CompTable.interp_table E (ht c).
Definition interp_cache := interp_cache_ht.

Lemma interp_cache_ct_find_cet :
  forall E c e cs ls,
    interp_cache_ct E c -> find_cet e c = Some (cs, ls) -> interp_cnf E cs.
Proof.
Admitted.

Lemma interp_cache_ct_find_cbt :
  forall E c e cs l,
    interp_cache_ct E c -> find_cbt e c = Some (cs, l) -> interp_cnf E cs.
Proof.
Admitted.

Lemma interp_cache_find_het :
  forall E c e cs ls,
    interp_cache E c -> find_het e c = Some (cs, ls) -> interp_cnf E cs.
Proof.
Admitted.

Lemma interp_cache_find_hbt :
  forall E c e cs l,
    interp_cache E c -> find_hbt e c = Some (cs, l) -> interp_cnf E cs.
Proof.
Admitted.


Lemma interp_cache_add_cet :
  forall E c e cs ls, interp_cache E c <-> interp_cache E (add_cet e cs ls c).
Proof.
  move=> E c e cs ls. by rewrite /interp_cache. 
Qed.

Lemma interp_cache_add_cbt :
  forall E c e cs l, interp_cache E c <-> interp_cache E (add_cbt e cs l c).
Proof.
  move=> E c e cs ls. by rewrite /interp_cache. 
Qed.

Lemma interp_cache_add_het :
  forall E c e cs ls, interp_cache E c -> interp_cnf E cs ->
                      interp_cache E (add_het e cs ls c).
Proof.
(*   move=> E c e cs ls. rewrite /interp_cache /interp_cache_ht /add_het /=.  *)
(*   by apply: CompTable.interp_table_add_et. *)
(* Qed. *)
Admitted.

Lemma interp_cache_add_hbt :
  forall E c e cs l, interp_cache E c -> interp_cnf E cs ->
                     interp_cache E (add_hbt e cs l c).
Proof.
(*   move=> E c e cs l. rewrite /interp_cache /interp_cache_ht /add_hbt /=.  *)
(*   by apply: CompTable.interp_table_add_bt. *)
(* Qed. *)
Admitted.

Lemma interp_cache_reset_ct :
  forall E c, interp_cache E c <-> interp_cache E (reset_ct c).
Proof.
(*   move=> E c. by rewrite /interp_cache. *)
(* Qed. *)
Admitted.

Lemma interp_cache_ct_add_cet :
  forall E c e cs ls, interp_cache_ct E c -> interp_cnf E cs ->
                      interp_cache_ct E (add_cet e cs ls c).
Proof. Admitted.

Lemma interp_cache_ct_add_cbt :
  forall E c e cs l, interp_cache_ct E c -> interp_cnf E cs ->
                     interp_cache_ct E (add_cbt e cs l c).
Proof. Admitted.

Lemma interp_cache_ct_add_het :
  forall E c e cs ls, interp_cache_ct E c <-> interp_cache_ct E (add_het e cs ls c).
Proof. Admitted.

Lemma interp_cache_ct_add_hbt :
  forall E c e cs l, interp_cache_ct E c <-> interp_cache_ct E (add_hbt e cs l c).
Proof. Admitted.


Lemma interp_cache_ct_reset_ct :
  forall E c, interp_cache_ct E (reset_ct c).
Proof.
Admitted.

(* ==== correct ==== *)

Definition ht_enc_correct_exp e cs ls vm c := 
  CompTable.enc_correct_exp e cs ls vm (ht c).
Definition ht_enc_correct_bexp e cs l vm c := 
  CompTable.enc_correct_bexp e cs l vm (ht c).
Definition ct_enc_correct_exp e cs ls vm c := 
  CompTable.enc_correct_exp e cs ls vm (ct c).
Definition ct_enc_correct_bexp e cs l vm c := 
  CompTable.enc_correct_bexp e cs l vm (ct c).

(* Definition correct_ht (vm : vm) (c : compcache) := CompTable.correct vm (ht c). *)
(* Definition correct_ct (vm : vm) (c : compcache) := CompTable.correct vm (ct c). *)
Definition correct_ht (vm : vm) (c : compcache) :=
  (forall e cs ls, find_het e c = Some (cs, ls) -> ht_enc_correct_exp e cs ls vm c)
  /\ forall e cs l, find_hbt e c = Some (cs, l) -> ht_enc_correct_bexp e cs l vm c.
Definition correct_ct (vm : vm) (c : compcache) :=
  (forall e cs ls, find_cet e c = Some (cs, ls) -> ct_enc_correct_exp e cs ls vm c)
  /\ forall e cs l, find_cbt e c = Some (cs, l) -> ct_enc_correct_bexp e cs l vm c.
Definition correct (vm : vm) (c : compcache) := correct_ht vm c /\ correct_ct vm c.

(*
Lemma add_het_find_none_enc_correct_exp :
  forall e c e0 cs0 ls0 vm cs ls,
    find_het e c = None ->
    ht_enc_correct_exp e0 cs0 ls0 vm c ->
    ht_enc_correct_exp e0 cs0 ls0 vm (add_het e cs ls c).
Proof.
  move=> e cc e0 cs0 ls0 vm cs ls Hfe.
  case e0 => /=.
  - done.
  - done.
  - move=> op e1 [cs1 [ls1 [Hfe1 Hence]]].
    exists cs1, ls1. split; last done.
    rewrite -Hfe1. apply find_het_add_het_neq. by auto_prove_neq.
  - move=> op e1 e2 [cs1 [ls1 [cs2 [ls2 [Hfe1 [Hfe2 Hence]]]]]].
    exists cs1, ls1, cs2, ls2.     
    split; last split; last done; [rewrite -Hfe1 | rewrite -Hfe2]; 
      apply find_het_add_het_neq; by auto_prove_neq.
  - move=> c e1 e2 [csc [lc [cs1 [ls1 [cs2 [ls2 [Hfc [Hfe1 [Hfe2 Hence]]]]]]]]].
    exists csc, lc, cs1, ls1, cs2, ls2.
    repeat split; last done.
    + rewrite -Hfc. by apply find_hbt_add_het. 
    + rewrite -Hfe1. apply find_het_add_het_neq. by auto_prove_neq.
    + rewrite -Hfe2. apply find_het_add_het_neq. by auto_prove_neq.
Qed.

Lemma add_het_find_none_enc_correct_bexp :
  forall e c e0 cs0 l0 vm cs ls,
    find_het e c = None ->
    ht_enc_correct_bexp e0 cs0 l0 vm c ->
    ht_enc_correct_bexp e0 cs0 l0 vm (add_het e cs ls c).
Proof.
  move=> e cc e0 cs0 l0 vm cs ls Hfe.
  case e0 => /=.
  - done.
  - done.
  - move=> op e1 e2 [cs1 [ls1 [cs2 [ls2 [Hfe1 [Hfe2 Hence]]]]]].
    exists cs1, ls1, cs2, ls2.     
    split; last split; last done; [rewrite -Hfe1 | rewrite -Hfe2];
      apply find_het_add_het_neq; by auto_prove_neq.
  - move=> e1 [cs1 [l1 [Hfe1 Hence]]].
    exists cs1, l1. split; last done.
    rewrite -Hfe1. by apply find_hbt_add_het. 
  - move=> e1 e2 [cs1 [l1 [cs2 [l2 [Hfe1 [Hfe2 Hence]]]]]].
    exists cs1, l1, cs2, l2.     
    split; last split; last done; [rewrite -Hfe1 | rewrite -Hfe2];
      by apply find_hbt_add_het.
  - move=> e1 e2 [cs1 [l1 [cs2 [l2 [Hfe1 [Hfe2 Hence]]]]]].
    exists cs1, l1, cs2, l2.     
    split; last split; last done; [rewrite -Hfe1 | rewrite -Hfe2];
      by apply find_hbt_add_het.
Qed.
*)

Lemma correct_find_cet :
  forall m c e cs ls,
  correct m c -> find_cet e c = Some (cs, ls) -> ct_enc_correct_exp e cs ls m c.
Proof.
Admitted.

Lemma correct_find_het :
  forall m c e cs ls,
  correct m c -> find_het e c = Some (cs, ls) -> ht_enc_correct_exp e cs ls m c.
Proof.
Admitted.

Lemma correct_find_cbt :
  forall m c e cs l,
  correct m c -> find_cbt e c = Some (cs, l) -> ct_enc_correct_bexp e cs l m c.
Proof.
Admitted.

Lemma correct_find_hbt :
  forall m c e cs l,
  correct m c -> find_hbt e c = Some (cs, l) -> ht_enc_correct_bexp e cs l m c.
Proof.
Admitted.


Lemma correct_ht_add_het :
  forall vm c e cs ls, 
    correct_ht vm c
    -> find_het e c = None
    -> ht_enc_correct_exp e cs ls vm c
    -> correct_ht vm (add_het e cs ls c).
Proof.
  move=> vm c e cs ls. rewrite /correct_ht /find_het /ht_enc_correct_exp /=.
  by apply: CompTable.correct_add_et.
Qed.

Lemma correct_ct_add_cet :
  forall vm c e cs ls, 
    correct_ct vm c
    -> find_cet e c = None
    -> ct_enc_correct_exp e cs ls vm c
    -> correct_ct vm (add_cet e cs ls c).
Proof.
  move=> vm c e cs ls. rewrite /correct_ct /find_cet /ct_enc_correct_exp /=.
  by apply: CompTable.correct_add_et.
Qed.

Lemma correct_add_cet :
  forall vm c e cs ls, 
    correct vm c
    -> find_cet e c = None
    -> ct_enc_correct_exp e cs ls vm c
    -> correct vm (add_cet e cs ls c).
Proof.
  (* move=> vm c e cs ls. rewrite /correct_ct /find_cet /ct_enc_correct_exp /=. *)
  (* by apply: CompTable.correct_add_et. *)
Admitted.

Lemma correct_add_cet_het :
  forall vm c e cs ls, 
    correct vm c
    -> find_cet e c = None
    -> find_het e c = None
    -> ct_enc_correct_exp e cs ls vm c
    -> ht_enc_correct_exp e cs ls vm c
    -> correct vm (add_cet e cs ls (add_het e cs ls c)).
Proof.
  (* move=> vm c e cs ls. rewrite /correct_ct /find_cet /ct_enc_correct_exp /=. *)
  (* by apply: CompTable.correct_add_et. *)
Admitted.

Lemma correct_add_cbt :
  forall vm c e cs l, 
    correct vm c
    -> find_cbt e c = None
    -> ct_enc_correct_bexp e cs l vm c
    -> correct vm (add_cbt e cs l c).
Proof.
  (* move=> vm c e cs ls. rewrite /correct_ct /find_cet /ct_enc_correct_exp /=. *)
  (* by apply: CompTable.correct_add_et. *)
Admitted.

Lemma correct_add_cbt_hbt :
  forall vm c e cs l, 
    correct vm c
    -> find_cbt e c = None
    -> find_hbt e c = None
    -> ct_enc_correct_bexp e cs l vm c
    -> ht_enc_correct_bexp e cs l vm c
    -> correct vm (add_cbt e cs l (add_hbt e cs l c)).
Proof.
  (* move=> vm c e cs ls. rewrite /correct_ct /find_cet /ct_enc_correct_exp /=. *)
  (* by apply: CompTable.correct_add_et. *)
Admitted.

Lemma correct_reset_ct :
  forall vm c, correct vm c -> correct vm (reset_ct c).
Proof.
Admitted.


(*
Lemma correct_add_cbt :
  forall vm c e cs l, correct vm c <-> correct vm (add_cbt e cs l c).
Proof.
  move=> vm c e cs l. done.
Qed.

Lemma correct_add_het :
  forall vm c e cs ls, 
    correct vm c -> (forall vm, consistent vm vm -> enc_correct_exp e cs ls vm c)
    -> correct vm (add_het e cs ls c).
Proof.
  move=> vm c e cs ls [[Hce Hcb] Hence]. rewrite /strong_correct /=. 
  split; last done.
  move=> e0 cs0 ls0. case Heq : (e0 == e).
  - rewrite (ExpMap.Lemmas.find_add_eq Heq). move/eqP: Heq => Heq.
    rewrite Heq. case=> <- <-; done.
  - move/negP: Heq => Heq. rewrite (ExpMap.Lemmas.find_add_neq Heq).
    exact: Hce.
Qed.
*)

(*
Lemma strong_correct_add_hbt :
  forall vm c e cs l, strong_correct vm c /\ enc_correct_bexp vm e cs l ->
                      strong_correct vm (add_hbt e cs l c).
Proof.
  move=> vm c e cs l [[Hce Hcb] Hence]. rewrite /strong_correct /=.
  split; first done.
  move=> e0 cs0 l0. case Heq : (e0 == e).
  - rewrite (BexpMap.Lemmas.find_add_eq Heq). move/eqP: Heq => Heq.
    rewrite Heq. case=> <- <-; done.
  - move/negP: Heq => Heq. rewrite (BexpMap.Lemmas.find_add_neq Heq).
    exact: Hcb.
Qed.

Lemma strong_correct_reset_ct :
  forall vm c, strong_correct vm c <-> strong_correct vm (reset_ct c).
Proof.
  move=> vm c. done. 
Qed.



Lemma correct_add_cet :
  forall vm c e ls, correct vm c <-> correct vm (add_cet e ls c).
Proof.
  move=> vm c e ls. by rewrite /correct. 
Qed.

Lemma correct_add_cbt :
  forall vm c e l, correct vm c <-> correct vm (add_cbt e l c).
Proof.
  move=> E c e ls. by rewrite /correct. 
Qed.

Lemma correct_add_het :
  forall vm c e cs ls, correct vm c /\ enc_bits E ls (QFBV.eval_exp e s) ->
                        correct vm (add_het e cs ls c).
Proof.
  move=> vm c e cs ls [[Hce Hcb] Hence]. rewrite /correct /=. split; last done.
  move=> e0 cs0 ls0. case Heq : (e0 == e).
  - rewrite (ExpMap.Lemmas.find_add_eq Heq). move/eqP: Heq => Heq.
    rewrite Heq. case=> _ <-; done.
  - move/negP: Heq => Heq. rewrite (ExpMap.Lemmas.find_add_neq Heq).
    exact: Hce.
Qed.

Lemma correct_add_hbt :
  forall vm c e cs l, correct vm c /\ enc_bit E l (QFBV.eval_bexp e s) ->
                       correct vm (add_hbt e cs l c).
Proof.
  move=> vm c e cs l [[Hce Hcb] Hence]. rewrite /correct /=. split; first done.
  move=> e0 cs0 l0. case Heq : (e0 == e).
  - rewrite (BexpMap.Lemmas.find_add_eq Heq). move/eqP: Heq => Heq.
    rewrite Heq. case=> _ <-; done.
  - move/negP: Heq => Heq. rewrite (BexpMap.Lemmas.find_add_neq Heq).
    exact: Hcb.
Qed.
*)

(*
Lemma correct_reset_ct :
  forall vm c, correct vm c <-> correct vm (reset_ct c).
Proof.
  move=> vm c. by rewrite /correct.
Qed.
*)



(*
Lemma vm_preserve_enc_correct_exp :
  forall m m' e cs ls, 
    vm_preserve m m' -> enc_correct_exp m e cs ls -> enc_correct_exp m' e cs ls.
Proof.
  move=> m m' e cs ls Hpmmp. rewrite /enc_correct_exp.
  move=> Henc vm Hconmp Hics.
  move: (vm_preserve_consistent Hpmmp Hconmp) => Hconm.
  by apply: Henc.
Qed.

Lemma vm_preserve_enc_correct_bexp :
  forall m m' e cs l, 
    vm_preserve m m' -> enc_correct_bexp m e cs l -> enc_correct_bexp m' e cs l.
Proof.
  move=> m m' e cs l Hpmmp. rewrite /enc_correct_bexp.
  move=> Henc vm Hconmp Hics.
  move: (vm_preserve_consistent Hpmmp Hconmp) => Hconm.
  by apply: Henc.
Qed.

Lemma vm_preserve_strong_correct :
  forall m m' c, vm_preserve m m' -> strong_correct m c -> strong_correct m' c.
Proof.
  move=> m m' c Hpmmp [Hce Hcb]. rewrite /strong_correct. split.
  - move=> e cs ls Hfind. move: (Hce _ _ _ Hfind) => Hencm.
    by apply: (@vm_preserve_enc_correct_exp m).
  - move=> e cs l Hfind. move: (Hcb _ _ _ Hfind) => Hencm.
    by apply: (@vm_preserve_enc_correct_bexp m).
Qed.
*)

Lemma vm_preserve_correct :
  forall m m' c, vm_preserve m m' -> correct m c -> correct m' c.
Proof.
(*   move=> m m' c Hpmmp [Hce Hcb]. rewrite /correct. split. *)
(*   - move=> e cs ls Hfind. move: (Hce _ _ _ Hfind) => Hencm. *)
(*     by apply: (@vm_preserve_enc_correct_exp m). *)
(*   - move=> e cs l Hfind. move: (Hcb _ _ _ Hfind) => Hencm. *)
(*     by apply: (@vm_preserve_enc_correct_bexp m). *)
(* Qed. *)
Admitted.


Lemma interp_cache_ct_find_cet_some_correct :
  forall m E s c e cs ls,
    consistent m E s -> interp_lit E lit_tt
    -> interp_cache_ct E c -> find_cet e c = Some (cs, ls) 
    -> correct m c -> enc_bits E ls (QFBV.eval_exp e s)
  with
    interp_cache_ct_find_cbt_some_correct :
      forall m E s c e cs l,
        consistent m E s -> interp_lit E lit_tt
        -> interp_cache_ct E c -> find_cbt e c = Some (cs, l) 
        -> correct m c -> enc_bit E l (QFBV.eval_bexp e s).
Proof.
  (* interp_cache_ct_find_cet_some_correct *)
  move=> m E s c.
  elim => [v | bs | op e1 IH1 | op e1 IH1 e2 IH2 | b e1 IH1 e2 IH2];
  move=> cs ls Hcon Htt HrEc Hfe Hcrmc;
  move: (interp_cache_ct_find_cet HrEc Hfe) => Hics;
  move: (add_prelude_to Htt Hics) => {Hics} Hics.
  - move: (correct_find_cet Hcrmc Hfe) => /= Hence.
    by apply Hence.
  - admit.
  - admit.
  - move: (correct_find_cet Hcrmc Hfe) => /= 
      [cs1 [ls1 [cs2 [ls2 [Hfe1 [Hfe2 Hence]]]]]].
    rewrite /find_cet in IH1 IH2.
    move: (IH1 _ _ Hcon Htt HrEc Hfe1 Hcrmc) 
            (IH2 _ _ Hcon Htt HrEc Hfe2 Hcrmc) => Henc1 Henc2.
    by apply Hence.
Admitted.


(* ==== newer_than_cache ==== *)

Definition newer_than_ct g (c : compcache) := CompTable.newer_than_table g (ct c).
Definition newer_than_ht g (c : compcache) := CompTable.newer_than_table g (ht c).
Definition newer_than_cache := newer_than_ht.

Lemma newer_than_cache_well_formed_newer_ct :
  forall g c, newer_than_cache g c -> well_formed c -> newer_than_ct g c.
Proof.
Admitted.

Lemma newer_than_ct_find_cet :
  forall g c e cs ls,
    newer_than_ct g c -> find_cet e c = Some (cs, ls) 
    -> newer_than_cnf g cs /\ newer_than_lits g ls.
Proof. Admitted.

Lemma newer_than_ct_find_cbt :
  forall g c e cs l,
    newer_than_ct g c -> find_cbt e c = Some (cs, l) 
    -> newer_than_cnf g cs /\ newer_than_lit g l.
Proof. Admitted.

Lemma newer_than_cache_find_het :
  forall g c e cs ls,
    newer_than_cache g c -> find_het e c = Some (cs, ls) 
    -> newer_than_cnf g cs /\ newer_than_lits g ls.
Proof. Admitted.

Lemma newer_than_cache_find_hbt :
  forall g c e cs l,
    newer_than_cache g c -> find_hbt e c = Some (cs, l) 
    -> newer_than_cnf g cs /\ newer_than_lit g l.
Proof. Admitted.


Lemma newer_than_cache_add_cet :
  forall g c e cs ls, 
    newer_than_cache g c <-> newer_than_cache g (add_cet e cs ls c).
Proof. Admitted.

Lemma newer_than_cache_add_cbt :
  forall g c e cs l, 
    newer_than_cache g c <-> newer_than_cache g (add_cbt e cs l c).
Proof. Admitted.

Lemma newer_than_cache_add_het :
  forall g c e cs ls, 
    newer_than_cache g c -> newer_than_cnf g cs -> newer_than_lits g ls 
    -> newer_than_cache g (add_het e cs ls c).
Proof. Admitted.

Lemma newer_than_cache_add_hbt :
  forall g c e cs l, 
    newer_than_cache g c -> newer_than_cnf g cs -> newer_than_lit g l 
    -> newer_than_cache g (add_hbt e cs l c).
Proof. Admitted.


Lemma newer_than_cache_le_newer g g' c :
  newer_than_cache g c -> (g <=? g')%positive -> newer_than_cache g' c.
Proof. Admitted.


Lemma newer_than_cache_reset_ct :
  forall g c, newer_than_cache g c <-> newer_than_cache g (reset_ct c).
Proof.
  move=> g c. by rewrite /newer_than_cache.
Qed.


Lemma env_preserve_interp_cache : 
  forall E E' g c,
    env_preserve E E' g -> newer_than_cache g c ->
    interp_cache E' c <-> interp_cache E c.
Proof.
  move=> E E' g c. rewrite /interp_cache /newer_than_cache /=. 
  by apply: CompTable.env_preserve_interp_table.
Qed.    

(*
Lemma env_preserve_correct E E' s g ca :
  env_preserve E E' g -> newer_than_cache g ca ->
  correct E' s ca <-> correct vm ca.
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

Definition bound_ct (c : compcache) (vm : vm) := CompTable.bound (ct c) vm.
Definition bound_ht (c : compcache) (vm : vm) := CompTable.bound (ht c) vm.
Definition bound := bound_ht.

Lemma bound_well_formed_bound_ct :
  forall c vm, bound c vm -> well_formed c -> bound_ct c vm.
Proof.
Admitted.

Lemma bound_ct_find_cet :
  forall c m e cs ls, 
    bound_ct c m -> find_cet e c = Some (cs, ls)  -> bound_exp e m.
Proof. Admitted.

Lemma bound_ct_find_cbt :
  forall c m e cs l, 
    bound_ct c m -> find_cbt e c = Some (cs, l) -> bound_bexp e m.
Proof. Admitted.

Lemma bound_find_het :
  forall c m e cs ls, 
    bound c m -> find_het e c = Some (cs, ls)  -> bound_exp e m.
Proof. Admitted.

Lemma bound_find_hbt :
  forall c m e cs l, 
    bound c m -> find_hbt e c = Some (cs, l) -> bound_bexp e m.
Proof. Admitted.


Lemma bound_add_cet :
  forall c vm e cs ls, bound c vm <-> bound (add_cet e cs ls c) vm.
Proof.
  move=> c vm e cs ls. by rewrite /bound. 
Qed.

Lemma bound_add_cbt :
  forall c vm e cs l, bound c vm <-> bound (add_cbt e cs l c) vm.
Proof.
  move=> c vm e cs l. by rewrite /bound. 
Qed.

Lemma bound_add_het :
  forall c vm e cs ls, bound c vm -> bound_exp e vm -> bound (add_het e cs ls c) vm.
Proof.
(*   move=> c vm e cs ls. rewrite /bound /bound_ht /add_het /=.  *)
(*   by apply: CompTable.bound_add_et. *)
(* Qed. *)
Admitted.

Lemma bound_add_hbt :
  forall c vm e cs l, bound c vm -> bound_bexp e vm -> bound (add_hbt e cs l c) vm.
Proof.
(*   move=> c vm e cs l. rewrite /bound /bound_ht /add_hbt /=.  *)
(*   by apply: CompTable.bound_add_bt. *)
(* Qed. *)
Admitted.

Lemma bound_reset_ct :
  forall c vm, bound c vm <-> bound (reset_ct c) vm.
Proof.
(*   move=> c vm. by rewrite /bound. *)
(* Qed. *)
Admitted.

Lemma vm_preserve_bound :
  forall m m' c, vm_preserve m m' -> bound c m -> bound c m'.
Proof. Admitted.

(* Lemma bound_add_find_none : *)
(*   forall c vm v ls, *)
(*     bound c vm -> SSAVM.find v vm = None -> bound c (SSAVM.add v ls vm). *)
(* Proof. *)
(*   move=> c vm v ls. rewrite /bound /bound_ht /=. *)
(*   by apply: CompTable.bound_add_find_none. *)
(* Qed. *)


(* ==== preserve ==== *)

Definition preserve (c c' : compcache) : Prop :=
  CompTable.preserve (ct c) (ct c') /\ CompTable.preserve (ht c) (ht c').

Lemma preserve_find_cet :
  forall c c' e cs ls,
    preserve c c' -> 
    find_cet e c = Some (cs, ls) -> find_cet e c' = Some (cs, ls).
Proof.
Admitted.

Lemma preserve_find_cbt :
  forall c c' e cs l,
    preserve c c' -> 
    find_cbt e c = Some (cs, l) -> find_cbt e c' = Some (cs, l).
Proof.
Admitted.

Lemma preserve_find_het :
  forall c c' e cs ls,
    preserve c c' -> 
    find_het e c = Some (cs, ls) -> find_het e c' = Some (cs, ls).
Proof.
Admitted.

Lemma preserve_find_hbt :
  forall c c' e cs l,
    preserve c c' -> 
    find_hbt e c = Some (cs, l) -> find_hbt e c' = Some (cs, l).
Proof.
Admitted.

Lemma preserve_add_cet :
  forall c1 c2 e cs ls,
    preserve c1 c2 -> find_cet e c2 = None -> preserve c1 (add_cet e cs ls c2).
Proof. Admitted.

Lemma preserve_add_cbt :
  forall c1 c2 e cs l,
    preserve c1 c2 -> find_cbt e c2 = None -> preserve c1 (add_cbt e cs l c2).
Proof. Admitted.

Lemma preserve_add_het :
  forall c1 c2 e cs ls,
    preserve c1 c2 -> find_het e c2 = None -> preserve c1 (add_het e cs ls c2).
Proof. Admitted.

Lemma preserve_add_hbt :
  forall c1 c2 e cs l,
    preserve c1 c2 -> find_hbt e c2 = None -> preserve c1 (add_hbt e cs l c2).
Proof. Admitted.

Lemma preserve_trans :
  forall c1 c2 c3,
    preserve c1 c2 -> preserve c2 c3 -> preserve c1 c3.
Proof. Admitted.

