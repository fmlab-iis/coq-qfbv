From Coq Require Import ZArith OrderedType Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import FMaps Var Seqs Tactics.
From BitBlasting Require Import QFBV CNF State BBCommon.
From BBCache Require Import CompTableFlatten SimpTable CompCache.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ==== A cache with complete information in current tables ==== *)

Record ccache :=
  { (* store historical results *)
    ht : comptable;
    (* store current results *)
    ct : comptable }.

Definition empty : ccache :=
  {| ht := CompTableFlatten.empty;
     ct := CompTableFlatten.empty |}.

Definition find_het e c := CompTableFlatten.find_et e (ht c).
Definition find_hbt e c := CompTableFlatten.find_bt e (ht c).
Definition find_cet e c := CompTableFlatten.find_et e (ct c).
Definition find_cbt e c := CompTableFlatten.find_bt e (ct c).


(* ==== modification ==== *)

Definition add_het e cs ls c :=
  {| ht := CompTableFlatten.add_et e cs ls (ht c);
     ct := ct c |}.

Definition add_hbt e cs l c :=
  {| ht := CompTableFlatten.add_bt e cs l (ht c);
     ct := ct c |}.

Definition add_cet e cs ls c :=
  {| ht := ht c;
     ct := CompTableFlatten.add_et e cs ls (ct c) |}.

Definition add_cbt e cs l c :=
  {| ht := ht c;
     ct := CompTableFlatten.add_bt e cs l (ct c) |}.

Definition reset_ct (c : ccache) :=
  {| ht := ht c;
     ct := CompTableFlatten.empty |}.


(* Cache compatible *)

From BBCache Require CompCache.

Definition ct_compatible fc c := comptable_compatible (ct fc) (CompCache.ct c).

Definition ht_compatible fc c := comptable_compatible (ht fc) (CompCache.ht c).

Definition ccache_compatible ec c := ct_compatible ec c /\ ht_compatible ec c.

Lemma ccache_compatible_reset_ct ec c :
  ccache_compatible ec c -> ccache_compatible (reset_ct ec)
                                              (CompCache.reset_ct c).
Proof.
  move=> [[Hct_e Hct_b] [Hht_e Hht_b]]. split; [split | split].
  - rewrite /reset_ct /=. done.
  - rewrite /reset_ct /=. done.
  - assumption.
  - assumption.
Qed.

Lemma ccache_compatible_find_cet_none ec c e :
  ccache_compatible ec c -> (find_cet e ec = None <-> CompCache.find_cet e c = None).
Proof.
  move=> [[Hct_e Hct_b] _]. rewrite /find_cet /CompTableFlatten.find_et.
  rewrite /CompCache.find_cet /CompTable.find_et. move: (Hct_e e) => [H1 H2].
  split=> H.
  - apply: CompTable.ExpMap.Lemmas.not_mem_find_none. rewrite -H1. apply/negPf.
    apply: CompTableFlatten.ExpMap.Lemmas.find_none_not_mem. assumption.
  - apply: CompTableFlatten.ExpMap.Lemmas.not_mem_find_none.
    rewrite H1. apply/negPf. apply: CompTable.ExpMap.Lemmas.find_none_not_mem.
    assumption.
Qed.

Lemma ccache_compatible_find_cbt_none ec c e :
  ccache_compatible ec c -> (find_cbt e ec = None <-> CompCache.find_cbt e c = None).
Proof.
  move=> [[Hct_e Hct_b] _]. rewrite /find_cbt /CompTableFlatten.find_bt.
  rewrite /CompCache.find_cbt /CompTable.find_bt. move: (Hct_b e) => [H1 H2].
  split=> H.
  - apply: CompTable.BexpMap.Lemmas.not_mem_find_none. rewrite -H1. apply/negPf.
    apply: CompTableFlatten.BexpMap.Lemmas.find_none_not_mem. assumption.
  - apply: CompTableFlatten.BexpMap.Lemmas.not_mem_find_none.
    rewrite H1. apply/negPf. apply: CompTable.BexpMap.Lemmas.find_none_not_mem.
    assumption.
Qed.

Lemma ccache_compatible_find_cet_some ec c e ecs elrs cs lrs :
  ccache_compatible ec c ->
  find_cet e ec = Some (ecs, elrs) ->
  CompCache.find_cet e c = Some (cs, lrs) ->
  cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs /\ elrs = lrs.
Proof.
  move=> [[Hct_e Hct_b] _] Hfe Hf. move: (Hct_e e) => [H1 H2].
  exact: (H2 _ _ _ _ Hfe Hf).
Qed.

Lemma ccache_compatible_find_cet_some_exists1 ec c e ecs elrs :
  ccache_compatible ec c ->
  find_cet e ec = Some (ecs, elrs) ->
  exists cs, CompCache.find_cet e c = Some (cs, elrs) /\
             cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs.
Proof.
  move=> Hcc Hfe. dcase (CompCache.find_cet e c); case.
  - move=> [cs lrs] Hf. move: (ccache_compatible_find_cet_some Hcc Hfe Hf) => [H1 [H2 H3]].
    exists cs. rewrite H3. done.
  - move=> Hf. move/(ccache_compatible_find_cet_none _ Hcc): Hf. rewrite Hfe.
    discriminate.
Qed.

Lemma ccache_compatible_find_cet_some_exists2 ec c e cs lrs :
  ccache_compatible ec c ->
  CompCache.find_cet e c = Some (cs, lrs) ->
  exists ecs, find_cet e ec = Some (ecs, lrs) /\
              cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs.
Proof.
  move=> Hcc Hf. dcase (find_cet e ec); case.
  - move=> [ecs elrs] Hfe.
    move: (ccache_compatible_find_cet_some Hcc Hfe Hf) => [H1 [H2 H3]].
    exists ecs. rewrite H3. done.
  - move=> Hfe. move/(ccache_compatible_find_cet_none _ Hcc): Hfe. rewrite Hf.
    discriminate.
Qed.

Lemma ccache_compatible_find_cbt_some ec c e ecs elr cs lr :
  ccache_compatible ec c ->
  find_cbt e ec = Some (ecs, elr) ->
  CompCache.find_cbt e c = Some (cs, lr) ->
  cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs /\ elr = lr.
Proof.
  move=> [[Hct_e Hct_b] _] Hfe Hf. move: (Hct_b e) => [H1 H2].
  exact: (H2 _ _ _ _ Hfe Hf).
Qed.

Lemma ccache_compatible_find_cbt_some_exists1 ec c e ecs elr :
  ccache_compatible ec c ->
  find_cbt e ec = Some (ecs, elr) ->
  exists cs, CompCache.find_cbt e c = Some (cs, elr) /\
             cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs.
Proof.
  move=> Hcc Hfe. dcase (CompCache.find_cbt e c); case.
  - move=> [cs lrs] Hf. move: (ccache_compatible_find_cbt_some Hcc Hfe Hf) => [H1 [H2 H3]].
    exists cs. rewrite H3. done.
  - move=> Hf. move/(ccache_compatible_find_cbt_none _ Hcc): Hf. rewrite Hfe.
    discriminate.
Qed.

Lemma ccache_compatible_find_cbt_some_exists2 ec c e cs lr :
  ccache_compatible ec c ->
  CompCache.find_cbt e c = Some (cs, lr) ->
  exists ecs, find_cbt e ec = Some (ecs, lr) /\
              cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs.
Proof.
  move=> Hcc Hf. dcase (find_cbt e ec); case.
  - move=> [ecs elrs] Hfe.
    move: (ccache_compatible_find_cbt_some Hcc Hfe Hf) => [H1 [H2 H3]].
    exists ecs. rewrite H3. done.
  - move=> Hfe. move/(ccache_compatible_find_cbt_none _ Hcc): Hfe. rewrite Hf.
    discriminate.
Qed.

Lemma ccache_compatible_find_het_none ec c e :
  ccache_compatible ec c ->
  (find_het e ec = None <-> CompCache.find_het e c = None).
Proof.
  move=> [_ [Hht_e Hht_b]]. rewrite /find_het /CompTableFlatten.find_et.
  rewrite /CompCache.find_het /CompTable.find_et. move: (Hht_e e) => [H1 H2].
  split=> H.
  - apply: CompTable.ExpMap.Lemmas.not_mem_find_none. rewrite -H1. apply/negPf.
    apply: CompTableFlatten.ExpMap.Lemmas.find_none_not_mem. assumption.
  - apply: CompTableFlatten.ExpMap.Lemmas.not_mem_find_none.
    rewrite H1. apply/negPf. apply: CompTable.ExpMap.Lemmas.find_none_not_mem.
    assumption.
Qed.

Lemma ccache_compatible_find_hbt_none ec c e :
  ccache_compatible ec c ->
  (find_hbt e ec = None <-> CompCache.find_hbt e c = None).
Proof.
  move=> [_ [Hht_e Hht_b]]. rewrite /find_hbt /CompTableFlatten.find_bt.
  rewrite /CompCache.find_hbt /CompTable.find_bt. move: (Hht_b e) => [H1 H2].
  split=> H.
  - apply: CompTable.BexpMap.Lemmas.not_mem_find_none. rewrite -H1. apply/negPf.
    apply: CompTableFlatten.BexpMap.Lemmas.find_none_not_mem. assumption.
  - apply: CompTableFlatten.BexpMap.Lemmas.not_mem_find_none.
    rewrite H1. apply/negPf. apply: CompTable.BexpMap.Lemmas.find_none_not_mem.
    assumption.
Qed.

Lemma ccache_compatible_find_het_some ec c e ecs elrs cs lrs :
  ccache_compatible ec c ->
  find_het e ec = Some (ecs, elrs) ->
  CompCache.find_het e c = Some (cs, lrs) ->
  cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs /\ elrs = lrs.
Proof.
  move=> [_ [Hht_e Hht_b]] Hfe Hf. move: (Hht_e e) => [H1 H2].
  exact: (H2 _ _ _ _ Hfe Hf).
Qed.

Lemma ccache_compatible_find_het_some_exists1 ec c e ecs elrs :
  ccache_compatible ec c ->
  find_het e ec = Some (ecs, elrs) ->
  exists cs, CompCache.find_het e c = Some (cs, elrs) /\
             cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs.
Proof.
  move=> Hcc Hfe. dcase (CompCache.find_het e c); case.
  - move=> [cs lrs] Hf. move: (ccache_compatible_find_het_some Hcc Hfe Hf) => [H1 [H2 H3]].
    exists cs. rewrite H3. done.
  - move=> Hf. move/(ccache_compatible_find_het_none _ Hcc): Hf. rewrite Hfe.
    discriminate.
Qed.

Lemma ccache_compatible_find_het_some_exists2 ec c e cs lrs :
  ccache_compatible ec c ->
  CompCache.find_het e c = Some (cs, lrs) ->
  exists ecs, find_het e ec = Some (ecs, lrs) /\
              cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs.
Proof.
  move=> Hcc Hf. dcase (find_het e ec); case.
  - move=> [ecs elrs] Hfe.
    move: (ccache_compatible_find_het_some Hcc Hfe Hf) => [H1 [H2 H3]].
    exists ecs. rewrite H3. done.
  - move=> Hfe. move/(ccache_compatible_find_het_none _ Hcc): Hfe. rewrite Hf.
    discriminate.
Qed.

Lemma ccache_compatible_find_hbt_some ec c e ecs elr cs lr :
  ccache_compatible ec c ->
  find_hbt e ec = Some (ecs, elr) ->
  CompCache.find_hbt e c = Some (cs, lr) ->
  cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs /\ elr = lr.
Proof.
  move=> [_ [Hht_e Hht_b]] Hfe Hf. move: (Hht_b e) => [H1 H2].
  exact: (H2 _ _ _ _ Hfe Hf).
Qed.

Lemma ccache_compatible_find_hbt_some_exists1 ec c e ecs elr :
  ccache_compatible ec c ->
  find_hbt e ec = Some (ecs, elr) ->
  exists cs, CompCache.find_hbt e c = Some (cs, elr) /\
             cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs.
Proof.
  move=> Hcc Hfe. dcase (CompCache.find_hbt e c); case.
  - move=> [cs lrs] Hf. move: (ccache_compatible_find_hbt_some Hcc Hfe Hf) => [H1 [H2 H3]].
    exists cs. rewrite H3. done.
  - move=> Hf. move/(ccache_compatible_find_hbt_none _ Hcc): Hf. rewrite Hfe.
    discriminate.
Qed.

Lemma ccache_compatible_find_hbt_some_exists2 ec c e cs lr :
  ccache_compatible ec c ->
  CompCache.find_hbt e c = Some (cs, lr) ->
  exists ecs, find_hbt e ec = Some (ecs, lr) /\
              cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs.
Proof.
  move=> Hcc Hf. dcase (find_hbt e ec); case.
  - move=> [ecs elrs] Hfe.
    move: (ccache_compatible_find_hbt_some Hcc Hfe Hf) => [H1 [H2 H3]].
    exists ecs. rewrite H3. done.
  - move=> Hfe. move/(ccache_compatible_find_hbt_none _ Hcc): Hfe. rewrite Hf.
    discriminate.
Qed.

Lemma ccache_compatible_add_cet e ecs cs lrs ec c :
  ccache_compatible ec c ->
  cnf_eqsat (tflatten ecs) cs ->
  cnf_eqnew (tflatten ecs) cs ->
  ccache_compatible (add_cet e ecs lrs ec) (CompCache.add_cet e cs lrs c).
Proof.
  move=> [[Hcet Hcbt] [Hhet Hhbt]]. split; [split | split].
  - rewrite /add_cet /CompCache.add_cet /=. exact: (et_compatible_add _ _ Hcet H).
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma ccache_compatible_add_cbt e ecs cs lr ec c :
  ccache_compatible ec c ->
  cnf_eqsat (tflatten ecs) cs ->
  cnf_eqnew (tflatten ecs) cs ->
  ccache_compatible (add_cbt e ecs lr ec) (CompCache.add_cbt e cs lr c).
Proof.
  move=> [[Hcet Hcbt] [Hhet Hhbt]]. split; [split | split].
  - assumption.
  - rewrite /add_cbt /CompCache.add_cbt /=. exact: (bt_compatible_add _ _ Hcbt H).
  - assumption.
  - assumption.
Qed.

Lemma ccache_compatible_add_het e lrs ec c ecs cs :
  ccache_compatible ec c ->
  cnf_eqsat (tflatten ecs) cs ->
  cnf_eqnew (tflatten ecs) cs ->
  ccache_compatible (add_het e ecs lrs ec) (CompCache.add_het e cs lrs c).
Proof.
  move=> [[Hcet Hcbt] [Hhet Hhbt]] Heqs. split; [split | split].
  - assumption.
  - assumption.
  - rewrite /add_het /CompCache.add_het /=. exact: (et_compatible_add _ _ Hhet Heqs).
  - assumption.
Qed.

Lemma ccache_compatible_add_hbt e lr ec c ecs cs :
  ccache_compatible ec c ->
  cnf_eqsat (tflatten ecs) cs ->
  cnf_eqnew (tflatten ecs) cs ->
  ccache_compatible (add_hbt e ecs lr ec) (CompCache.add_hbt e cs lr c).
Proof.
  move=> [[Hcet Hcbt] [Hhet Hhbt]] Heqs. split; [split | split].
  - assumption.
  - assumption.
  - assumption.
  - rewrite /add_hbt /CompCache.add_hbt /=. exact: (bt_compatible_add _ _ Hhbt Heqs).
Qed.


(* Convert CCacheFlatten.ccache to CompCache.compcache *)

Definition ccache_of_fccache (c : ccache) : CompCache.compcache :=
  CompCache.Build_compcache (comptable_of_fcomptable (ht c))
                            (comptable_of_fcomptable (ct c)).

Lemma cache_of_fcache_compatible fc :
  ccache_compatible fc (ccache_of_fccache fc).
Proof.
  split.
  - exact: (comptable_of_fcomptable_compatible (ct fc)).
  - exact: (comptable_of_fcomptable_compatible (ht fc)).
Qed.
