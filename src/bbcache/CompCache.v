From Coq Require Import ZArith OrderedType Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import EqFMaps EqVar.
From BitBlasting Require Import QFBV CNF State AdhereConform BBCommon.
From BBCache Require Import CompTable.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* == A cache with complete information in both current and historical tables == *)

Record compcache :=
  { (* store historical results *)
    ht : comptable;
    (* store current results *)
    ct : comptable }.

Definition empty : compcache :=
  {| ht := CompTable.empty;
     ct := CompTable.empty |}.

Definition find_het e c := CompTable.find_et e (ht c).
Definition find_hbt e c := CompTable.find_bt e (ht c).
Definition find_cet e c := CompTable.find_et e (ct c).
Definition find_cbt e c := CompTable.find_bt e (ct c).

Lemma find_het_equation :
  forall e c, find_het e c = CompTable.find_et e (ht c).
Proof. done. Qed.

Lemma find_hbt_equation :
  forall e c, find_hbt e c = CompTable.find_bt e (ht c).
Proof. done. Qed.

Lemma find_cet_equation :
  forall e c, find_cet e c = CompTable.find_et e (ct c).
Proof. done. Qed.

Lemma find_cbt_equation :
  forall e c, find_cbt e c = CompTable.find_bt e (ct c).
Proof. done. Qed.


(* ==== modification ==== *)

Definition add_het e cs ls c :=
  {| ht := CompTable.add_et e cs ls (ht c);
     ct := ct c |}.

Definition add_hbt e cs l c :=
  {| ht := CompTable.add_bt e cs l (ht c);
     ct := ct c |}.

Definition add_cet e cs ls c :=
  {| ht := ht c;
     ct := CompTable.add_et e cs ls (ct c) |}.

Definition add_cbt e cs l c :=
  {| ht := ht c;
     ct := CompTable.add_bt e cs l (ct c) |}.

Definition reset_ct (c : compcache) :=
  {| ht := ht c;
     ct := CompTable.empty |}.

Lemma add_het_cet_comm :
  forall c e1 cs1 ls1 e2 cs2 ls2,
    add_het e1 cs1 ls1 (add_cet e2 cs2 ls2 c)
    = add_cet e2 cs2 ls2 (add_het e1 cs1 ls1 c).
Proof.
  done.
Qed.

Lemma add_het_cbt_comm :
  forall c e1 cs1 ls1 e2 cs2 l2,
    add_het e1 cs1 ls1 (add_cbt e2 cs2 l2 c)
    = add_cbt e2 cs2 l2 (add_het e1 cs1 ls1 c).
Proof.
  done.
Qed.

Lemma add_hbt_cet_comm :
  forall c e1 cs1 l1 e2 cs2 ls2,
    add_hbt e1 cs1 l1 (add_cet e2 cs2 ls2 c)
    = add_cet e2 cs2 ls2 (add_hbt e1 cs1 l1 c).
Proof.
  done.
Qed.

Lemma add_hbt_cbt_comm :
  forall c e1 cs1 l1 e2 cs2 l2,
    add_hbt e1 cs1 l1 (add_cbt e2 cs2 l2 c)
    = add_cbt e2 cs2 l2 (add_hbt e1 cs1 l1 c).
Proof.
  done.
Qed.

Lemma find_het_add_het_eq :
  forall e cs ls c, find_het e (add_het e cs ls c) = Some (cs, ls).
Proof.
  move=> e cs ls c. rewrite /find_het /add_het /=.
  by apply: CompTable.find_et_add_et_eq.
Qed.

Lemma find_het_add_het_neq :
  forall e0 e cs ls c, ~ e0 == e -> find_het e0 (add_het e cs ls c) = find_het e0 c.
Proof.
  move=> e0 e cs ls c. rewrite /find_het /add_het /=.
  by apply: CompTable.find_et_add_et_neq.
Qed.

Lemma find_het_add_hbt :
  forall e0 e cs l c, find_het e0 (add_hbt e cs l c) = find_het e0 c.
Proof.
  move=> e0 e cs l c. rewrite /find_het /add_hbt /=.
  by apply: CompTable.find_et_add_bt.
Qed.

Lemma find_het_add_cet :
  forall e0 e cs ls c, find_het e0 (add_cet e cs ls c) = find_het e0 c.
Proof.
  done.
Qed.

Lemma find_het_add_cbt :
  forall e0 e cs l c, find_het e0 (add_cbt e cs l c) = find_het e0 c.
Proof.
  done.
Qed.

Lemma find_hbt_add_het :
  forall e0 e cs ls c, find_hbt e0 (add_het e cs ls c) = find_hbt e0 c.
Proof.
  move=> e0 e cs ls c. rewrite /find_hbt /add_het /=.
  by apply: CompTable.find_bt_add_et.
Qed.

Lemma find_hbt_add_hbt_eq :
  forall e cs l c, find_hbt e (add_hbt e cs l c) = Some (cs, l).
Proof.
  move=> e cs l c. rewrite /find_hbt /add_hbt /=.
  by apply: CompTable.find_bt_add_bt_eq.
Qed.

Lemma find_hbt_add_hbt_neq :
  forall e0 e cs l c, ~ e0 == e -> find_hbt e0 (add_hbt e cs l c) = find_hbt e0 c.
Proof.
  move=> e0 e cs l c. rewrite /find_hbt /add_hbt /=.
  by apply: CompTable.find_bt_add_bt_neq.
Qed.

Lemma find_hbt_add_cet :
  forall e0 e cs ls c, find_hbt e0 (add_cet e cs ls c) = find_hbt e0 c.
Proof.
  done.
Qed.

Lemma find_hbt_add_cbt :
  forall e0 e cs l c, find_hbt e0 (add_cbt e cs l c) = find_hbt e0 c.
Proof.
  done.
Qed.

Lemma find_cet_add_het :
  forall e0 e cs ls c, find_cet e0 (add_het e cs ls c) = find_cet e0 c.
Proof.
  done.
Qed.

Lemma find_cet_add_hbt :
  forall e0 e cs l c, find_cet e0 (add_hbt e cs l c) = find_cet e0 c.
Proof.
  done.
Qed.

Lemma find_cet_add_cet_eq :
  forall e cs ls c, find_cet e (add_cet e cs ls c) = Some (cs, ls).
Proof.
  move=> e cs ls c. rewrite /find_cet /add_cet /=.
  by apply: CompTable.find_et_add_et_eq.
Qed.

Lemma find_cet_add_cet_neq :
  forall e0 e cs ls c, ~ e0 == e -> find_cet e0 (add_cet e cs ls c) = find_cet e0 c.
Proof.
  move=> e0 e cs ls c. rewrite /find_cet /add_cet /=.
  by apply: CompTable.find_et_add_et_neq.
Qed.

Lemma find_cet_add_cbt :
  forall e0 e cs l c, find_cet e0 (add_cbt e cs l c) = find_cet e0 c.
Proof.
  move=> e0 e cs l c. rewrite /find_cet /add_cbt /=.
  by apply: CompTable.find_et_add_bt.
Qed.

Lemma find_cbt_add_het :
  forall e0 e cs ls c, find_cbt e0 (add_het e cs ls c) = find_cbt e0 c.
Proof.
  done.
Qed.

Lemma find_cbt_add_hbt :
  forall e0 e cs l c, find_cbt e0 (add_hbt e cs l c) = find_cbt e0 c.
Proof.
  done.
Qed.

Lemma find_cbt_add_cet :
  forall e0 e cs ls c, find_cbt e0 (add_cet e cs ls c) = find_cbt e0 c.
Proof.
  move=> e0 e cs ls c. rewrite /find_cbt /add_cet /=.
  by apply: CompTable.find_bt_add_et.
Qed.

Lemma find_cbt_add_cbt_eq :
  forall e cs l c, find_cbt e (add_cbt e cs l c) = Some (cs, l).
Proof.
  move=> e cs l c. rewrite /find_cbt /add_cbt /=.
  by apply: CompTable.find_bt_add_bt_eq.
Qed.

Lemma find_cbt_add_cbt_neq :
  forall e0 e cs l c, ~ e0 == e -> find_cbt e0 (add_cbt e cs l c) = find_cbt e0 c.
Proof.
  move=> e0 e cs l c. rewrite /find_cbt /add_cbt /=.
  by apply: CompTable.find_bt_add_bt_neq.
Qed.


(* ==== well_formed ==== *)

Definition well_formed (c : compcache) : Prop :=
  (forall e cs ls, find_cet e c = Some (cs, ls) -> find_het e c = Some (cs, ls))
  /\ forall e cs l, find_cbt e c = Some (cs, l) -> find_hbt e c = Some (cs, l).

Lemma well_formed_find_cet :
  forall c e cs ls,
    well_formed c -> find_cet e c = Some (cs, ls) -> find_het e c = Some (cs, ls).
Proof.
  move=> c e cs ls [He Hb]. exact: He.
Qed.

Lemma well_formed_find_cbt :
  forall c e cs l,
    well_formed c -> find_cbt e c = Some (cs, l) -> find_hbt e c = Some (cs, l).
Proof.
  move=> c e cs l [He Hb]. exact: Hb.
Qed.

Lemma well_formed_add_cet :
  forall c e cs ls,
    well_formed c -> find_het e c = Some (cs, ls) -> well_formed (add_cet e cs ls c).
Proof.
  move=> c e1 cs1 ls1 Hwfc Hfhete1. split.
  - move=> e2 cs2 ls2. case Heq : (e2 == e1).
    + move/eqP: Heq => ->. rewrite find_cet_add_cet_eq. case=> <- <-.
      rewrite find_het_add_cet. done.
    + move/negP: Heq => Hneq. rewrite (find_cet_add_cet_neq _ _ _ Hneq) => Hfcete2.
      rewrite find_het_add_cet. exact: (well_formed_find_cet Hwfc Hfcete2).
  - move=> e2 cs2 l2. rewrite find_cbt_add_cet find_hbt_add_cet.
    move=> Hfcbte2. exact: (well_formed_find_cbt Hwfc Hfcbte2).
Qed.

Lemma well_formed_add_cbt :
  forall c e cs l,
    well_formed c -> find_hbt e c = Some (cs, l) -> well_formed (add_cbt e cs l c).
Proof.
  move=> c e1 cs1 l1 Hwfc Hfhbte1. split.
  - move=> e2 cs2 ls2. rewrite find_cet_add_cbt find_het_add_cbt.
    move=> Hfcete2. exact: (well_formed_find_cet Hwfc Hfcete2).
  - move=> e2 cs2 l2. case Heq : (e2 == e1).
    + move/eqP: Heq => ->. rewrite find_cbt_add_cbt_eq. case=> <- <-.
      rewrite find_hbt_add_cbt. done.
    + move/negP: Heq => Hneq. rewrite (find_cbt_add_cbt_neq _ _ _ Hneq) => Hfcbte2.
      rewrite find_hbt_add_cbt. exact: (well_formed_find_cbt Hwfc Hfcbte2).
Qed.

Lemma well_formed_add_cet_het :
  forall c e cs ls,
    well_formed c -> well_formed (add_cet e cs ls (add_het e cs ls c)).
Proof.
  move=> c e1 cs1 ls1 Hwfc. split.
  - move=> e2 cs2 ls2. case Heq : (e2 == e1).
    + move/eqP: Heq => ->. rewrite find_cet_add_cet_eq. case=> <- <-.
      rewrite find_het_add_cet find_het_add_het_eq. done.
    + move/negP: Heq => Hneq.
      rewrite (find_cet_add_cet_neq _ _ _ Hneq) find_cet_add_het => Hfcete2.
      rewrite find_het_add_cet (find_het_add_het_neq _ _ _ Hneq).
      exact: (well_formed_find_cet Hwfc Hfcete2).
  - move=> e2 cs2 l2. rewrite find_cbt_add_cet find_cbt_add_het.
    rewrite find_hbt_add_cet find_hbt_add_het.
    move=> Hfcbte2. exact: (well_formed_find_cbt Hwfc Hfcbte2).
Qed.

Lemma well_formed_add_cbt_hbt :
  forall c e cs l,
    well_formed c -> well_formed (add_cbt e cs l (add_hbt e cs l c)).
Proof.
  move=> c e1 cs1 l1 Hwfc. split.
  - move=> e2 cs2 ls2. rewrite find_cet_add_cbt find_cet_add_hbt.
    rewrite find_het_add_cbt find_het_add_hbt.
    move=> Hfcete2. exact: (well_formed_find_cet Hwfc Hfcete2).
  - move=> e2 cs2 l2. case Heq : (e2 == e1).
    + move/eqP: Heq => ->. rewrite find_cbt_add_cbt_eq. case=> <- <-.
      rewrite find_hbt_add_cbt find_hbt_add_hbt_eq. done.
    + move/negP: Heq => Hneq.
      rewrite (find_cbt_add_cbt_neq _ _ _ Hneq) find_cbt_add_hbt => Hfcbte2.
      rewrite find_hbt_add_cbt (find_hbt_add_hbt_neq _ _ _ Hneq).
      exact: (well_formed_find_cbt Hwfc Hfcbte2).
Qed.

Lemma well_formed_reset_ct :
  forall c, well_formed (reset_ct c).
Proof.
  done.
Qed.


(* ==== interp_cache === *)

Definition interp_cache_ct (E : env) (c : compcache) :=
  CompTable.interp_table E (ct c).

Definition interp_cache_ht (E : env) (c : compcache) :=
  CompTable.interp_table E (ht c).

Definition interp_cache := interp_cache_ht.

Lemma interp_cache_well_formed_interp_ct :
  forall E c, interp_cache E c -> well_formed c -> interp_cache_ct E c.
Proof.
  move=> E c [Hie Hib] [Hwfe Hwfb]. split.
  - move=> e cs ls Hfind. move: (Hwfe _ _ _ Hfind). exact: Hie.
  - move=> e cs l Hfind. move: (Hwfb _ _ _ Hfind). exact: Hib.
Qed.

Lemma interp_cache_ct_find_cet :
  forall E c e cs ls,
    interp_cache_ct E c -> find_cet e c = Some (cs, ls) -> interp_cnf E cs.
Proof.
  move=> E c e cs ls. exact: CompTable.interp_table_find_et.
Qed.

Lemma interp_cache_ct_find_cbt :
  forall E c e cs l,
    interp_cache_ct E c -> find_cbt e c = Some (cs, l) -> interp_cnf E cs.
Proof.
  move=> E c e cs l. exact: CompTable.interp_table_find_bt.
Qed.

Lemma interp_cache_find_het :
  forall E c e cs ls,
    interp_cache E c -> find_het e c = Some (cs, ls) -> interp_cnf E cs.
Proof.
  move=> E c e cs ls. exact: CompTable.interp_table_find_et.
Qed.

Lemma interp_cache_find_hbt :
  forall E c e cs l,
    interp_cache E c -> find_hbt e c = Some (cs, l) -> interp_cnf E cs.
Proof.
  move=> E c e cs l. exact: CompTable.interp_table_find_bt.
Qed.

Lemma interp_cache_ct_add_het :
  forall E c e cs ls, interp_cache_ct E c <-> interp_cache_ct E (add_het e cs ls c).
Proof.
  done.
Qed.

Lemma interp_cache_ct_add_hbt :
  forall E c e cs l, interp_cache_ct E c <-> interp_cache_ct E (add_hbt e cs l c).
Proof.
  done.
Qed.

Lemma interp_cache_ct_add_cet :
  forall E c e cs ls, interp_cache_ct E c -> interp_cnf E cs ->
                      interp_cache_ct E (add_cet e cs ls c).
Proof.
  move=> E c e cs ls. rewrite /interp_cache_ct /=.
  exact: CompTable.interp_table_add_et.
Qed.

Lemma interp_cache_ct_add_cbt :
  forall E c e cs l, interp_cache_ct E c -> interp_cnf E cs ->
                     interp_cache_ct E (add_cbt e cs l c).
Proof.
  move=> E c e cs l. rewrite /interp_cache_ct /=.
  exact: CompTable.interp_table_add_bt.
Qed.

Lemma interp_cache_ct_reset_ct :
  forall E c, interp_cache_ct E (reset_ct c).
Proof.
  done.
Qed.

Lemma interp_cache_add_het :
  forall E c e cs ls, interp_cache E c -> interp_cnf E cs ->
                      interp_cache E (add_het e cs ls c).
Proof.
  move=> E c e cs ls. rewrite /interp_cache /interp_cache_ht /=.
  exact: CompTable.interp_table_add_et.
Qed.

Lemma interp_cache_add_hbt :
  forall E c e cs l, interp_cache E c -> interp_cnf E cs ->
                     interp_cache E (add_hbt e cs l c).
Proof.
  move=> E c e cs l. rewrite /interp_cache /interp_cache_ht /=.
  exact: CompTable.interp_table_add_bt.
Qed.

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

Lemma interp_cache_reset_ct :
  forall E c, interp_cache E c <-> interp_cache E (reset_ct c).
Proof.
  done.
Qed.


(* ==== correct ==== *)

Definition ht_enc_correct_exp e cs ls vm c :=
  CompTable.enc_correct_exp e cs ls vm (ht c).

Definition ht_enc_correct_bexp e cs l vm c :=
  CompTable.enc_correct_bexp e cs l vm (ht c).

Definition ct_enc_correct_exp e cs ls vm c :=
  CompTable.enc_correct_exp e cs ls vm (ct c).

Definition ct_enc_correct_bexp e cs l vm c :=
  CompTable.enc_correct_bexp e cs l vm (ct c).

Definition correct_ht (vm : vm) (c : compcache) := CompTable.correct vm (ht c).
Definition correct_ct (vm : vm) (c : compcache) := CompTable.correct vm (ct c).
Definition correct (vm : vm) (c : compcache) := correct_ht vm c /\ correct_ct vm c.

Lemma correct_find_het :
  forall m c e cs ls,
  correct m c -> find_het e c = Some (cs, ls) -> ht_enc_correct_exp e cs ls m c.
Proof.
  move=> m c e cs ls [Hcrht Hcrct]. exact: CompTable.correct_find_et.
Qed.

Lemma correct_find_hbt :
  forall m c e cs l,
  correct m c -> find_hbt e c = Some (cs, l) -> ht_enc_correct_bexp e cs l m c.
Proof.
  move=> m c e cs l [Hcrht Hcrct]. exact: CompTable.correct_find_bt.
Qed.

Lemma correct_find_cet :
  forall m c e cs ls,
  correct m c -> find_cet e c = Some (cs, ls) -> ct_enc_correct_exp e cs ls m c.
Proof.
  move=> m c e cs ls [Hcrht Hcrct]. exact: CompTable.correct_find_et.
Qed.

Lemma correct_find_cbt :
  forall m c e cs l,
  correct m c -> find_cbt e c = Some (cs, l) -> ct_enc_correct_bexp e cs l m c.
Proof.
  move=> m c e cs l [Hcrht Hcrct]. exact: CompTable.correct_find_bt.
Qed.

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

Lemma correct_ht_add_hbt :
  forall vm c e cs l,
    correct_ht vm c
    -> find_hbt e c = None
    -> ht_enc_correct_bexp e cs l vm c
    -> correct_ht vm (add_hbt e cs l c).
Proof.
  move=> vm c e cs l. rewrite /correct_ht /find_hbt /ht_enc_correct_bexp /=.
  by apply: CompTable.correct_add_bt.
Qed.

Lemma correct_ht_add_cet :
  forall vm c e cs ls, correct_ht vm c <-> correct_ht vm (add_cet e cs ls c).
Proof.
  move=> vm c e cs ls. rewrite /correct_ht. done.
Qed.

Lemma correct_ht_add_cbt :
  forall vm c e cs l, correct_ht vm c <-> correct_ht vm (add_cbt e cs l c).
Proof.
  move=> vm c e cs l. rewrite /correct_ht. done.
Qed.

Lemma correct_ct_add_het :
  forall vm c e cs ls, correct_ct vm c <-> correct_ct vm (add_het e cs ls c).
Proof.
  move=> vm c e cs ls. rewrite /correct_ct. done.
Qed.

Lemma correct_ct_add_hbt :
  forall vm c e cs l, correct_ct vm c <-> correct_ct vm (add_hbt e cs l c).
Proof.
  move=> vm c e cs l. rewrite /correct_ct. done.
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

Lemma correct_ct_add_cbt :
  forall vm c e cs l,
    correct_ct vm c
    -> find_cbt e c = None
    -> ct_enc_correct_bexp e cs l vm c
    -> correct_ct vm (add_cbt e cs l c).
Proof.
  move=> vm c e cs l. rewrite /correct_ct /find_cbt /ct_enc_correct_bexp /=.
  by apply: CompTable.correct_add_bt.
Qed.

Lemma correct_add_cet :
  forall vm c e cs ls,
    correct vm c
    -> find_cet e c = None
    -> ct_enc_correct_exp e cs ls vm c
    -> correct vm (add_cet e cs ls c).
Proof.
  move=> vm c e cs ls [Hctc Hhtc] Hfcet Hctenc. split.
  - rewrite -correct_ht_add_cet. done.
  - by apply correct_ct_add_cet.
Qed.

Lemma correct_add_cet_het :
  forall vm c e cs ls,
    correct vm c
    -> find_cet e c = None
    -> find_het e c = None
    -> ct_enc_correct_exp e cs ls vm c
    -> ht_enc_correct_exp e cs ls vm c
    -> correct vm (add_cet e cs ls (add_het e cs ls c)).
Proof.
  move=> vm c e cs ls [Hctc Hhtc] Hfcet Hfhet Hctenc Hhtenc. split.
  - rewrite -correct_ht_add_cet. by apply correct_ht_add_het.
  - rewrite -add_het_cet_comm -correct_ct_add_het. by apply correct_ct_add_cet.
Qed.

Lemma correct_add_cbt :
  forall vm c e cs l,
    correct vm c
    -> find_cbt e c = None
    -> ct_enc_correct_bexp e cs l vm c
    -> correct vm (add_cbt e cs l c).
Proof.
  move=> vm c e cs l [Hctc Hhtc] Hfcbt Hctenc. split.
  - rewrite -correct_ht_add_cbt. done.
  - by apply correct_ct_add_cbt.
Qed.

Lemma correct_add_cbt_hbt :
  forall vm c e cs l,
    correct vm c
    -> find_cbt e c = None
    -> find_hbt e c = None
    -> ct_enc_correct_bexp e cs l vm c
    -> ht_enc_correct_bexp e cs l vm c
    -> correct vm (add_cbt e cs l (add_hbt e cs l c)).
Proof.
  move=> vm c e cs l [Hctc Hhtc] Hfcbt Hfhbt Hctenc Hhtenc. split.
  - rewrite -correct_ht_add_cbt. by apply correct_ht_add_hbt.
  - rewrite -add_hbt_cbt_comm -correct_ct_add_hbt. by apply correct_ct_add_cbt.
Qed.

Lemma correct_reset_ct :
  forall vm c, correct vm c -> correct vm (reset_ct c).
Proof.
  move=> vm c [Hct Hht]. split; done.
Qed.

Lemma vm_preserve_correct :
  forall m m' c, vm_preserve m m' -> correct m c -> correct m' c.
Proof.
  move=> m m' c Hpre [Hht Hct].
  split; by apply (@CompTable.vm_preserve_correct m).
Qed.

Lemma interp_cache_ct_find_cet_some_correct :
  forall m E s c e cs ls te,
    consistent m E s -> interp_lit E lit_tt
    -> interp_cache_ct E c -> find_cet e c = Some (cs, ls)
    -> QFBV.well_formed_exp e te -> conform_exp e s te
    -> correct m c -> enc_bits E ls (QFBV.eval_exp e s).
Proof.
  move=> m E s c e cs ls te Hcon Htt HiEc Hfe Hwf Hcf [Hcrht Hcrct].
  move: HiEc Hfe Hwf Hcf Hcrct.
  by apply CompTable.interp_table_find_et_some_correct.
Qed.

Lemma interp_cache_ct_find_cbt_some_correct :
  forall m E s c e cs l te,
    consistent m E s -> interp_lit E lit_tt
    -> interp_cache_ct E c -> find_cbt e c = Some (cs, l)
    -> QFBV.well_formed_bexp e te -> conform_bexp e s te
    -> correct m c -> enc_bit E l (QFBV.eval_bexp e s).
Proof.
  move=> m E s c e cs l te Hcon Htt HiEc Hfe Hwf Hcf [Hcrht Hcrct].
  move: HiEc Hfe Hwf Hcf Hcrct.
  by apply CompTable.interp_table_find_bt_some_correct.
Qed.


(* ==== newer_than_cache ==== *)

Definition newer_than_ct g (c : compcache) := CompTable.newer_than_table g (ct c).
Definition newer_than_ht g (c : compcache) := CompTable.newer_than_table g (ht c).
Definition newer_than_cache := newer_than_ht.

Lemma newer_than_cache_well_formed_newer_ct :
  forall g c, newer_than_cache g c -> well_formed c -> newer_than_ct g c.
Proof.
  move=> g c [Hnewe Hnewb] [Hwfe Hwfb]. split.
  - move=> e cs ls Hfcet. move: (Hwfe _ _ _ Hfcet). exact: Hnewe.
  - move=> e cs l Hfcbt. move: (Hwfb _ _ _ Hfcbt). exact: Hnewb.
Qed.

Lemma newer_than_ct_find_cet :
  forall g c e cs ls,
    newer_than_ct g c -> find_cet e c = Some (cs, ls)
    -> newer_than_cnf g cs /\ newer_than_lits g ls.
Proof.
  move=> g c e cs ls. exact: CompTable.newer_than_table_find_et.
Qed.

Lemma newer_than_ct_find_cbt :
  forall g c e cs l,
    newer_than_ct g c -> find_cbt e c = Some (cs, l)
    -> newer_than_cnf g cs /\ newer_than_lit g l.
Proof.
  move=> g c e cs l. exact: CompTable.newer_than_table_find_bt.
Qed.

Lemma newer_than_cache_find_het :
  forall g c e cs ls,
    newer_than_cache g c -> find_het e c = Some (cs, ls)
    -> newer_than_cnf g cs /\ newer_than_lits g ls.
Proof.
  move=> g c e cs ls. exact: CompTable.newer_than_table_find_et.
Qed.

Lemma newer_than_cache_find_hbt :
  forall g c e cs l,
    newer_than_cache g c -> find_hbt e c = Some (cs, l)
    -> newer_than_cnf g cs /\ newer_than_lit g l.
Proof.
  move=> g c e cs l. exact: CompTable.newer_than_table_find_bt.
Qed.

Lemma newer_than_cache_add_het :
  forall g c e cs ls,
    newer_than_cache g c -> newer_than_cnf g cs -> newer_than_lits g ls
    -> newer_than_cache g (add_het e cs ls c).
Proof.
  move=> g c e cs ls. exact: CompTable.newer_than_table_add_et.
Qed.

Lemma newer_than_cache_add_hbt :
  forall g c e cs l,
    newer_than_cache g c -> newer_than_cnf g cs -> newer_than_lit g l
    -> newer_than_cache g (add_hbt e cs l c).
Proof.
  move=> g c e cs l. exact: CompTable.newer_than_table_add_bt.
Qed.

Lemma newer_than_cache_add_cet :
  forall g c e cs ls,
    newer_than_cache g c <-> newer_than_cache g (add_cet e cs ls c).
Proof.
  done.
Qed.

Lemma newer_than_cache_add_cbt :
  forall g c e cs l,
    newer_than_cache g c <-> newer_than_cache g (add_cbt e cs l c).
Proof.
  done.
Qed.

Lemma newer_than_cache_reset_ct :
  forall g c, newer_than_cache g c <-> newer_than_cache g (reset_ct c).
Proof.
  done.
Qed.

Lemma newer_than_cache_le_newer g g' c :
  newer_than_cache g c -> (g <=? g')%positive -> newer_than_cache g' c.
Proof.
  exact: CompTable.newer_than_table_le_newer.
Qed.

Lemma env_preserve_interp_cache :
  forall E E' g c,
    env_preserve E E' g -> newer_than_cache g c ->
    interp_cache E' c <-> interp_cache E c.
Proof.
  move=> E E' g c. rewrite /interp_cache /newer_than_cache /=.
  by apply: CompTable.env_preserve_interp_table.
Qed.


(* ==== bound by vm ==== *)

Definition bound_ct (c : compcache) (vm : vm) := CompTable.bound (ct c) vm.
Definition bound_ht (c : compcache) (vm : vm) := CompTable.bound (ht c) vm.
Definition bound := bound_ht.

Lemma bound_well_formed_bound_ct :
  forall c vm, bound c vm -> well_formed c -> bound_ct c vm.
Proof.
  move=> c vm [Hbde Hbdb] [Hwfe Hwfb]. split.
  - move=> e cs ls Hfind. move: (Hwfe _ _ _ Hfind). exact: Hbde.
  - move=> e cs l Hfind. move: (Hwfb _ _ _ Hfind). exact: Hbdb.
Qed.

Lemma bound_ct_find_cet :
  forall c m e cs ls,
    bound_ct c m -> find_cet e c = Some (cs, ls) -> bound_exp e m.
Proof.
  move=> c m e cs ls. exact: CompTable.bound_find_et.
Qed.

Lemma bound_ct_find_cbt :
  forall c m e cs l,
    bound_ct c m -> find_cbt e c = Some (cs, l) -> bound_bexp e m.
Proof.
  move=> c m e cs l. exact: CompTable.bound_find_bt.
Qed.

Lemma bound_find_het :
  forall c m e cs ls,
    bound c m -> find_het e c = Some (cs, ls) -> bound_exp e m.
Proof.
  move=> c m e cs ls. exact: CompTable.bound_find_et.
Qed.

Lemma bound_find_hbt :
  forall c m e cs l,
    bound c m -> find_hbt e c = Some (cs, l) -> bound_bexp e m.
Proof.
  move=> c m e cs l. exact: CompTable.bound_find_bt.
Qed.

Lemma bound_add_het :
  forall c vm e cs ls, bound c vm -> bound_exp e vm -> bound (add_het e cs ls c) vm.
Proof.
  move=> c vm e cs ls. exact: CompTable.bound_add_et.
Qed.

Lemma bound_add_hbt :
  forall c vm e cs l, bound c vm -> bound_bexp e vm -> bound (add_hbt e cs l c) vm.
Proof.
  move=> c vm e cs l. exact: CompTable.bound_add_bt.
Qed.

Lemma bound_add_cet :
  forall c vm e cs ls, bound c vm <-> bound (add_cet e cs ls c) vm.
Proof.
  done.
Qed.

Lemma bound_add_cbt :
  forall c vm e cs l, bound c vm <-> bound (add_cbt e cs l c) vm.
Proof.
  done.
Qed.

Lemma bound_reset_ct :
  forall c vm, bound c vm <-> bound (reset_ct c) vm.
Proof.
  done.
Qed.

Lemma vm_preserve_bound :
  forall m m' c, vm_preserve m m' -> bound c m -> bound c m'.
Proof.
  move=> m m' c. exact: CompTable.vm_preserve_bound.
Qed.


(* ==== preserve ==== *)

Definition preserve (c c' : compcache) : Prop :=
  CompTable.preserve (ct c) (ct c') /\ CompTable.preserve (ht c) (ht c').

Lemma preserve_refl : forall c, preserve c c.
Proof.
  done.
Qed.

Lemma preserve_trans :
  forall c1 c2 c3, preserve c1 c2 -> preserve c2 c3 -> preserve c1 c3.
Proof.
  move=> c1 c2 c3 [Hpct12 Hpht12] [Hpct23 Hpht23]. split.
  - by apply (CompTable.preserve_trans Hpct12).
  - by apply (CompTable.preserve_trans Hpht12).
Qed.

Lemma preserve_find_het :
  forall c c' e cs ls,
    preserve c c' ->
    find_het e c = Some (cs, ls) -> find_het e c' = Some (cs, ls).
Proof.
  move=> c c' e cs ls [Hprect Hpreht]. exact: CompTable.preserve_find_et.
Qed.

Lemma preserve_find_hbt :
  forall c c' e cs l,
    preserve c c' ->
    find_hbt e c = Some (cs, l) -> find_hbt e c' = Some (cs, l).
Proof.
  move=> c c' e cs l [Hprect Hpreht]. exact: CompTable.preserve_find_bt.
Qed.

Lemma preserve_find_cet :
  forall c c' e cs ls,
    preserve c c' ->
    find_cet e c = Some (cs, ls) -> find_cet e c' = Some (cs, ls).
Proof.
  move=> c c' e cs ls [Hprect Hpreht]. exact: CompTable.preserve_find_et.
Qed.

Lemma preserve_find_cbt :
  forall c c' e cs l,
    preserve c c' ->
    find_cbt e c = Some (cs, l) -> find_cbt e c' = Some (cs, l).
Proof.
  move=> c c' e cs l [Hprect Hpreht]. exact: CompTable.preserve_find_bt.
Qed.

Lemma preserve_add_het :
  forall c1 c2 e cs ls,
    preserve c1 c2 -> find_het e c2 = None -> preserve c1 (add_het e cs ls c2).
Proof.
  move=> c1 c2 e cs ls [Hpct Hpht] Hfe.
  split; rewrite /=; [ done | exact: CompTable.preserve_add_et ].
Qed.

Lemma preserve_add_hbt :
  forall c1 c2 e cs l,
    preserve c1 c2 -> find_hbt e c2 = None -> preserve c1 (add_hbt e cs l c2).
Proof.
  move=> c1 c2 e cs l [Hpct Hpht] Hfe.
  split; rewrite /=; [ done | exact: CompTable.preserve_add_bt ].
Qed.

Lemma preserve_add_cet :
  forall c1 c2 e cs ls,
    preserve c1 c2 -> find_cet e c2 = None -> preserve c1 (add_cet e cs ls c2).
Proof.
  move=> c1 c2 e cs ls [Hpct Hpht] Hfe.
  split; rewrite /=; [ exact: CompTable.preserve_add_et | done ].
Qed.

Lemma preserve_add_cbt :
  forall c1 c2 e cs l,
    preserve c1 c2 -> find_cbt e c2 = None -> preserve c1 (add_cbt e cs l c2).
Proof.
  move=> c1 c2 e cs l [Hpct Hpht] Hfe.
  split; rewrite /=; [ exact: CompTable.preserve_add_bt | done ].
Qed.
