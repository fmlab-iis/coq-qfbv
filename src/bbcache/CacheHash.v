From Coq Require Import ZArith OrderedType Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import EqFMaps EqVar.
From BitBlasting Require Import QFBV CNF State BBCommon.
From BBCache Require Import QFBVHash CompTableHash SimpTableHash CompCache.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ==== A cache with partial information in current tables ==== *)

Record cache :=
  { (* store historical results *)
    ht : comptable;
    (* store current results *)
    ct : simptable }.

Definition empty : cache :=
  {| ht := CompTableHash.empty;
     ct := SimpTableHash.empty |}.

Definition find_het e c := CompTableHash.find_et e (ht c).
Definition find_hbt e c := CompTableHash.find_bt e (ht c).
Definition find_cet e c := SimpTableHash.find_et e (ct c).
Definition find_cbt e c := SimpTableHash.find_bt e (ct c).


(* ==== modification ==== *)

Definition add_het e cs ls c :=
  {| ht := CompTableHash.add_et e cs ls (ht c);
     ct := ct c |}.

Definition add_hbt e cs l c :=
  {| ht := CompTableHash.add_bt e cs l (ht c);
     ct := ct c |}.

Definition add_cet e ls c :=
  {| ht := ht c;
     ct := SimpTableHash.add_et e ls (ct c) |}.

Definition add_cbt e l c :=
  {| ht := ht c;
     ct := SimpTableHash.add_bt e l (ct c) |}.

Definition reset_ct (c : cache) :=
  {| ht := ht c;
     ct := SimpTableHash.empty |}.


(* Compatibility beteeen CCacheHash.cache and CacheHash.cache *)

From BBCache Require CCacheHash.

Section Compatible.

  Definition compatible (c1 : cache) (c2 : CCacheHash.ccache) :=
    SimpTableHash.compatible (ct c1) (CCacheHash.ct c2)
    /\ (ht c1) = (CCacheHash.ht c2).

  Lemma compatible_find_het :
    forall c1 c2 e, compatible c1 c2 -> find_het e c1 = CCacheHash.find_het e c2.
  Proof.
    move=> c1 c2 e [Hct Hht] /=. rewrite /find_het Hht. done.
  Qed.

  Lemma compatible_find_hbt :
    forall c1 c2 e, compatible c1 c2 -> find_hbt e c1 = CCacheHash.find_hbt e c2.
  Proof.
    move=> c1 c2 e [Hct Hht] /=. rewrite /find_hbt Hht. done.
  Qed.

  Lemma compatible_find_cet_some :
    forall c1 c2 e ls,
      compatible c1 c2 -> find_cet e c1 = Some ls
      -> exists cs, CCacheHash.find_cet e c2 = Some (cs, ls).
  Proof.
    move=> c1 c2 e ls [Hct Hht] /=. exact: SimpTableHash.compatible_find_et_some.
  Qed.

  Lemma compatible_find_cet_none :
    forall c1 c2 e,
      compatible c1 c2 -> find_cet e c1 = None -> CCacheHash.find_cet e c2 = None.
  Proof.
    move=> c1 c2 e [Hct Hht] /=. exact: SimpTableHash.compatible_find_et_none.
  Qed.

  Lemma compatible_find_cbt_some :
    forall c1 c2 e l,
      compatible c1 c2 -> find_cbt e c1 = Some l
      -> exists cs, CCacheHash.find_cbt e c2 = Some (cs, l).
  Proof.
    move=> c1 c2 e l [Hct Hht] /=. exact: SimpTableHash.compatible_find_bt_some.
  Qed.

  Lemma compatible_find_cbt_none :
    forall c1 c2 e,
      compatible c1 c2 -> find_cbt e c1 = None -> CCacheHash.find_cbt e c2 = None.
  Proof.
    move=> c1 c2 e [Hct Hht] /=. exact: SimpTableHash.compatible_find_bt_none.
  Qed.

  Lemma compatible_add_het :
    forall c1 c2 e cs ls,
      compatible c1 c2
      -> compatible (add_het e cs ls c1) (CCacheHash.add_het e cs ls c2).
  Proof.
    move=> c1 c2 e cs ls [Hct Hht]. split; [ done | by rewrite /add_het Hht ].
  Qed.

  Lemma compatible_add_hbt :
    forall c1 c2 e cs l,
      compatible c1 c2
      -> compatible (add_hbt e cs l c1) (CCacheHash.add_hbt e cs l c2).
  Proof.
    move=> c1 c2 e cs l [Hct Hht]. split; [ done | by rewrite /add_hbt Hht ].
  Qed.

  Lemma compatible_add_cet :
    forall c1 c2 e cs ls,
      compatible c1 c2 -> compatible (add_cet e ls c1) (CCacheHash.add_cet e cs ls c2).
  Proof.
    move=> c1 c2 e cs ls [Hct Hht].
    split; [ exact: SimpTableHash.compatible_add_et | done ].
  Qed.

  Lemma compatible_add_cbt :
    forall c1 c2 e cs l,
      compatible c1 c2 -> compatible (add_cbt e l c1) (CCacheHash.add_cbt e cs l c2).
  Proof.
    move=> c1 c2 e cs ls [Hct Hht].
    split; [ exact: SimpTableHash.compatible_add_bt | done ].
  Qed.

  Lemma compatible_reset_ct :
    forall c1 c2,
      compatible c1 c2 -> compatible (reset_ct c1) (CCacheHash.reset_ct c2).
  Proof.
    move=> c1 c2 [Hct Hht]. split; done.
  Qed.

End Compatible.



(* Compatibility beteeen CacheHash.cache and CacheFlatten.cache *)

From BBCache Require SimpTable CompTableFlatten CacheFlatten.

Section CacheCompatible.

  Import QFBV.

  Definition cet_compatible
             (ht : SimpTableHash.simptable) (ft : SimpTable.simptable) : Prop :=
    forall (e : exp),
      SimpTableHash.find_et (hash_exp e) ht = SimpTable.find_et e ft.

  Definition cbt_compatible
             (ht : SimpTableHash.simptable) (ft : SimpTable.simptable) : Prop :=
    forall (e : bexp),
      SimpTableHash.find_bt (hash_bexp e) ht = SimpTable.find_bt e ft.

  Definition ct_compatible
             (ht : SimpTableHash.simptable) (ft : SimpTable.simptable) : Prop :=
    cet_compatible ht ft /\ cbt_compatible ht ft.

  Definition het_compatible
             (ht : CompTableHash.comptable) (ft : CompTableFlatten.comptable) : Prop :=
    forall (e : exp),
      CompTableHash.find_et (hash_exp e) ht = CompTableFlatten.find_et e ft.

  Definition hbt_compatible
             (ht : CompTableHash.comptable) (ft : CompTableFlatten.comptable) : Prop :=
    forall (e : bexp),
      CompTableHash.find_bt (hash_bexp e) ht = CompTableFlatten.find_bt e ft.

  Definition ht_compatible
             (ht : CompTableHash.comptable) (ft : CompTableFlatten.comptable) : Prop :=
    het_compatible ht ft /\ hbt_compatible ht ft.

  Definition cache_compatible
             (hc : cache) (fc : CacheFlatten.cache) : Prop :=
    ct_compatible (ct hc) (CacheFlatten.ct fc) /\
    ht_compatible (ht hc) (CacheFlatten.ht fc).

  Lemma cache_compatible_find_cet hc fc (e : exp) :
    cache_compatible hc fc ->
    find_cet (hash_exp e) hc = CacheFlatten.find_cet e fc.
  Proof. move=>[[H1 H2] [H3 H4]]. exact: (H1 e). Qed.

  Lemma cache_compatible_find_cbt hc fc (e : bexp) :
    cache_compatible hc fc ->
    find_cbt (hash_bexp e) hc = CacheFlatten.find_cbt e fc.
  Proof. move=>[[H1 H2] [H3 H4]]. exact: (H2 e). Qed.

  Lemma cache_compatible_find_het hc fc (e : exp) :
    cache_compatible hc fc ->
    find_het (hash_exp e) hc = CacheFlatten.find_het e fc.
  Proof. move=>[[H1 H2] [H3 H4]]. exact: (H3 e). Qed.

  Lemma cache_compatible_find_hbt hc fc (e : bexp) :
    cache_compatible hc fc ->
    find_hbt (hash_bexp e) hc = CacheFlatten.find_hbt e fc.
  Proof. move=>[[H1 H2] [H3 H4]]. exact: (H4 e). Qed.

  Lemma cache_compatible_find_cet_hexp hc fc (e : hexp) :
    cache_compatible hc fc ->
    well_formed_hexp e ->
    find_cet e hc = CacheFlatten.find_cet e fc.
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hexp Hwf).
    exact: (cache_compatible_find_cet _ Hcc).
  Qed.

  Lemma cache_compatible_find_cbt_hbexp hc fc (e : hbexp) :
    cache_compatible hc fc ->
    well_formed_hbexp e ->
    find_cbt e hc = CacheFlatten.find_cbt e fc.
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hbexp Hwf).
    exact: (cache_compatible_find_cbt _ Hcc).
  Qed.

  Lemma cache_compatible_find_het_hexp hc fc (e : hexp) :
    cache_compatible hc fc ->
    well_formed_hexp e ->
    find_het e hc = CacheFlatten.find_het e fc.
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hexp Hwf).
    exact: (cache_compatible_find_het _ Hcc).
  Qed.

  Lemma cache_compatible_find_hbt_hbexp hc fc (e : hbexp) :
    cache_compatible hc fc ->
    well_formed_hbexp e ->
    find_hbt e hc = CacheFlatten.find_hbt e fc.
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hbexp Hwf).
    exact: (cache_compatible_find_hbt _ Hcc).
  Qed.

  Lemma cache_compatible_add_cet hc fc (e : exp) ls :
    cache_compatible hc fc ->
    cache_compatible (add_cet (hash_exp e) ls hc)
                     (CacheFlatten.add_cet e ls fc).
  Proof.
    move=> [[H1 H2] [H3 H4]]. repeat split => //=.
    move=> f. case Heq: (f == e).
    - rewrite (eqP Heq) SimpTableHash.find_et_add_et_eq SimpTable.find_et_add_et_eq.
      reflexivity.
    - move/negP: Heq => Hne.
      have Hne_hexp: ~ hash_exp f == hash_exp e.
      { move=> /eqP H; apply: Hne. apply/eqP. exact: (hash_exp_inj H). }
      rewrite (SimpTableHash.find_et_add_et_neq _ _ Hne_hexp).
      rewrite (SimpTable.find_et_add_et_neq _ _ Hne).
      exact: (H1 f).
  Qed.

  Lemma cache_compatible_add_cbt hc fc (e : bexp) ls :
    cache_compatible hc fc ->
    cache_compatible (add_cbt (hash_bexp e) ls hc)
                     (CacheFlatten.add_cbt e ls fc).
  Proof.
    move=> [[H1 H2] [H3 H4]]. repeat split => //=.
    move=> f. case Heq: (f == e).
    - rewrite (eqP Heq) SimpTableHash.find_bt_add_bt_eq SimpTable.find_bt_add_bt_eq.
      reflexivity.
    - move/negP: Heq => Hne.
      have Hne_hbexp: ~ hash_bexp f == hash_bexp e.
      { move=> /eqP H; apply: Hne. apply/eqP. exact: (hash_bexp_inj H). }
      rewrite (SimpTableHash.find_bt_add_bt_neq _ _ Hne_hbexp).
      rewrite (SimpTable.find_bt_add_bt_neq _ _ Hne).
      exact: (H2 f).
  Qed.

  Lemma cache_compatible_add_het hc fc (e : exp) cs ls :
    cache_compatible hc fc ->
    cache_compatible (add_het (hash_exp e) cs ls hc)
                     (CacheFlatten.add_het e cs ls fc).
  Proof.
    move=> [[H1 H2] [H3 H4]]. repeat split => //=.
    move=> f. case Heq: (f == e).
    - rewrite (eqP Heq) CompTableHash.find_et_add_et_eq
              CompTableFlatten.find_et_add_et_eq.
      reflexivity.
    - move/negP: Heq => Hne.
      have Hne_hexp: ~ hash_exp f == hash_exp e.
      { move=> /eqP H; apply: Hne. apply/eqP. exact: (hash_exp_inj H). }
      rewrite (CompTableHash.find_et_add_et_neq _ _ _ Hne_hexp).
      rewrite (CompTableFlatten.find_et_add_et_neq _ _ _ Hne).
      exact: (H3 f).
  Qed.

  Lemma cache_compatible_add_hbt hc fc (e : bexp) cs ls :
    cache_compatible hc fc ->
    cache_compatible (add_hbt (hash_bexp e) cs ls hc)
                     (CacheFlatten.add_hbt e cs ls fc).
  Proof.
    move=> [[H1 H2] [H3 H4]]. repeat split => //=.
    move=> f. case Heq: (f == e).
    - rewrite (eqP Heq) CompTableHash.find_bt_add_bt_eq
              CompTableFlatten.find_bt_add_bt_eq.
      reflexivity.
    - move/negP: Heq => Hne.
      have Hne_hbexp: ~ hash_bexp f == hash_bexp e.
      { move=> /eqP H; apply: Hne. apply/eqP. exact: (hash_bexp_inj H). }
      rewrite (CompTableHash.find_bt_add_bt_neq _ _ _ Hne_hbexp).
      rewrite (CompTableFlatten.find_bt_add_bt_neq _ _ _ Hne).
      exact: (H4 f).
  Qed.

  Lemma cache_compatible_add_cet_hexp hc fc (e : hexp) ls :
    cache_compatible hc fc ->
    well_formed_hexp e ->
    cache_compatible (add_cet e ls hc)
                     (CacheFlatten.add_cet e ls fc).
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hexp Hwf).
    exact: (cache_compatible_add_cet _ _ Hcc).
  Qed.

  Lemma cache_compatible_add_cbt_hbexp hc fc (e : hbexp) ls :
    cache_compatible hc fc ->
    well_formed_hbexp e ->
    cache_compatible (add_cbt e ls hc)
                     (CacheFlatten.add_cbt e ls fc).
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hbexp Hwf).
    exact: (cache_compatible_add_cbt _ _ Hcc).
  Qed.

  Lemma cache_compatible_reset_ct hc fc :
    cache_compatible hc fc ->
    cache_compatible (reset_ct hc) (CacheFlatten.reset_ct fc).
  Proof.
    rewrite /reset_ct /CacheFlatten.reset_ct. move=> [[H1 H2] [H3 H4]].
      by repeat split.
  Qed.

End CacheCompatible.

