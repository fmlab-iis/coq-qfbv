From Coq Require Import ZArith OrderedType Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import EqFMaps EqVar Seqs Tactics.
From BitBlasting Require Import QFBV CNF State BBCommon.
From BBCache Require Import CompTableFlatten SimpTable CompCache.

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
  {| ht := CompTableFlatten.empty;
     ct := SimpTable.empty |}.

Definition find_het e c := CompTableFlatten.find_et e (ht c).
Definition find_hbt e c := CompTableFlatten.find_bt e (ht c).
Definition find_cet e c := SimpTable.find_et e (ct c).
Definition find_cbt e c := SimpTable.find_bt e (ct c).


(* ==== modification ==== *)

Definition add_het e cs ls c :=
  {| ht := CompTableFlatten.add_et e cs ls (ht c);
     ct := ct c |}.

Definition add_hbt e cs l c :=
  {| ht := CompTableFlatten.add_bt e cs l (ht c);
     ct := ct c |}.

Definition add_cet e ls c :=
  {| ht := ht c;
     ct := SimpTable.add_et e ls (ct c) |}.

Definition add_cbt e l c :=
  {| ht := ht c;
     ct := SimpTable.add_bt e l (ct c) |}.

Definition reset_ct (c : cache) :=
  {| ht := ht c;
     ct := SimpTable.empty |}.


(* Cache compatible *)

From BBCache Require Cache.

Definition ct_equal fc c := SimpTable.Equal (ct fc) (Cache.ct c).

Definition ht_compatible fc c := comptable_compatible (ht fc) (Cache.ht c).

Definition cache_compatible ec c := ct_equal ec c /\ ht_compatible ec c.

Lemma cache_compatible_reset_ct ec c :
  cache_compatible ec c -> cache_compatible (reset_ct ec)
                                            (Cache.reset_ct c).
Proof.
  move=> [[Hct_e Hct_b] [Hht_e Hht_b]]. split; [split | split].
  - rewrite /reset_ct /=. reflexivity.
  - rewrite /reset_ct /=. reflexivity.
  - assumption.
  - assumption.
Qed.

Lemma cache_compatible_find_cet ec c e :
  cache_compatible ec c -> find_cet e ec = Cache.find_cet e c.
Proof.
  move=> [[Hct_e Hct_b] _]. rewrite /find_cet /SimpTable.find_et.
  rewrite (Hct_e e). reflexivity.
Qed.

Lemma cache_compatible_find_cbt ec c e :
  cache_compatible ec c -> find_cbt e ec = Cache.find_cbt e c.
Proof.
  move=> [[Hct_e Hct_b] _]. rewrite /find_cbt /SimpTable.find_bt.
  rewrite (Hct_b e). reflexivity.
Qed.

Lemma cache_compatible_find_het_none ec c e :
  cache_compatible ec c ->
  (find_het e ec = None <-> Cache.find_het e c = None).
Proof.
  move=> [_ [Hht_e Hht_b]]. rewrite /find_het /CompTableFlatten.find_et.
  rewrite /Cache.find_het /CompTable.find_et. move: (Hht_e e) => [H1 H2].
  split=> H.
  - apply: CompTable.ExpMap.Lemmas.not_mem_find_none. rewrite -H1. apply/negPf.
    apply: CompTableFlatten.ExpMap.Lemmas.find_none_not_mem. assumption.
  - apply: CompTableFlatten.ExpMap.Lemmas.not_mem_find_none.
    rewrite H1. apply/negPf. apply: CompTable.ExpMap.Lemmas.find_none_not_mem.
    assumption.
Qed.

Lemma cache_compatible_find_hbt_none ec c e :
  cache_compatible ec c ->
  (find_hbt e ec = None <-> Cache.find_hbt e c = None).
Proof.
  move=> [_ [Hht_e Hht_b]]. rewrite /find_hbt /CompTableFlatten.find_bt.
  rewrite /Cache.find_hbt /CompTable.find_bt. move: (Hht_b e) => [H1 H2].
  split=> H.
  - apply: CompTable.BexpMap.Lemmas.not_mem_find_none. rewrite -H1. apply/negPf.
    apply: CompTableFlatten.BexpMap.Lemmas.find_none_not_mem. assumption.
  - apply: CompTableFlatten.BexpMap.Lemmas.not_mem_find_none.
    rewrite H1. apply/negPf. apply: CompTable.BexpMap.Lemmas.find_none_not_mem.
    assumption.
Qed.

Lemma cache_compatible_find_het_some ec c e ecs elrs cs lrs :
  cache_compatible ec c ->
  find_het e ec = Some (ecs, elrs) ->
  Cache.find_het e c = Some (cs, lrs) ->
  cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs /\ elrs = lrs.
Proof.
  move=> [_ [Hht_e Hht_b]] Hfe Hf. move: (Hht_e e) => [H1 H2].
  exact: (H2 _ _ _ _ Hfe Hf).
Qed.

Lemma cache_compatible_find_het_some_exists1 ec c e ecs elrs :
  cache_compatible ec c ->
  find_het e ec = Some (ecs, elrs) ->
  exists cs, Cache.find_het e c = Some (cs, elrs) /\
             cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs.
Proof.
  move=> Hcc Hfe. dcase (Cache.find_het e c); case.
  - move=> [cs lrs] Hf. move: (cache_compatible_find_het_some Hcc Hfe Hf) => [H1 [H2 H3]].
    exists cs. rewrite H3. done.
  - move=> Hf. move/(cache_compatible_find_het_none _ Hcc): Hf. rewrite Hfe.
    discriminate.
Qed.

Lemma cache_compatible_find_het_some_exists2 ec c e cs lrs :
  cache_compatible ec c ->
  Cache.find_het e c = Some (cs, lrs) ->
  exists ecs, find_het e ec = Some (ecs, lrs) /\
              cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs.
Proof.
  move=> Hcc Hf. dcase (find_het e ec); case.
  - move=> [ecs elrs] Hfe.
    move: (cache_compatible_find_het_some Hcc Hfe Hf) => [H1 [H2 H3]].
    exists ecs. rewrite H3. done.
  - move=> Hfe. move/(cache_compatible_find_het_none _ Hcc): Hfe. rewrite Hf.
    discriminate.
Qed.

Lemma cache_compatible_find_hbt_some ec c e ecs elr cs lr :
  cache_compatible ec c ->
  find_hbt e ec = Some (ecs, elr) ->
  Cache.find_hbt e c = Some (cs, lr) ->
  cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs /\ elr = lr.
Proof.
  move=> [_ [Hht_e Hht_b]] Hfe Hf. move: (Hht_b e) => [H1 H2].
  exact: (H2 _ _ _ _ Hfe Hf).
Qed.

Lemma cache_compatible_find_hbt_some_exists1 ec c e ecs elr :
  cache_compatible ec c ->
  find_hbt e ec = Some (ecs, elr) ->
  exists cs, Cache.find_hbt e c = Some (cs, elr) /\
             cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs.
Proof.
  move=> Hcc Hfe. dcase (Cache.find_hbt e c); case.
  - move=> [cs lrs] Hf. move: (cache_compatible_find_hbt_some Hcc Hfe Hf) => [H1 [H2 H3]].
    exists cs. rewrite H3. done.
  - move=> Hf. move/(cache_compatible_find_hbt_none _ Hcc): Hf. rewrite Hfe.
    discriminate.
Qed.

Lemma cache_compatible_find_hbt_some_exists2 ec c e cs lr :
  cache_compatible ec c ->
  Cache.find_hbt e c = Some (cs, lr) ->
  exists ecs, find_hbt e ec = Some (ecs, lr) /\
              cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs.
Proof.
  move=> Hcc Hf. dcase (find_hbt e ec); case.
  - move=> [ecs elrs] Hfe.
    move: (cache_compatible_find_hbt_some Hcc Hfe Hf) => [H1 [H2 H3]].
    exists ecs. rewrite H3. done.
  - move=> Hfe. move/(cache_compatible_find_hbt_none _ Hcc): Hfe. rewrite Hf.
    discriminate.
Qed.

Lemma cache_compatible_add_cet e lrs ec c :
  cache_compatible ec c ->
  cache_compatible (add_cet e lrs ec) (Cache.add_cet e lrs c).
Proof.
  move=> [[Hcet Hcbt] [Hhet Hhbt]]. split; [split | split].
  - rewrite /add_cet /Cache.add_cet /=. by apply: CompTable.ExpMap.Lemmas.add_m.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma cache_compatible_add_cbt e lr ec c :
  cache_compatible ec c ->
  cache_compatible (add_cbt e lr ec) (Cache.add_cbt e lr c).
Proof.
  move=> [[Hcet Hcbt] [Hhet Hhbt]]. split; [split | split].
  - assumption.
  - rewrite /add_cbt /Cache.add_cbt /=. by apply: CompTable.BexpMap.Lemmas.add_m.
  - assumption.
  - assumption.
Qed.

Lemma cache_compatible_add_het e lrs ec c ecs cs :
  cache_compatible ec c ->
  cnf_eqsat (tflatten ecs) cs ->
  cnf_eqnew (tflatten ecs) cs ->
  cache_compatible (add_het e ecs lrs ec) (Cache.add_het e cs lrs c).
Proof.
  move=> [[Hcet Hcbt] [Hhet Hhbt]] Heqs. split; [split | split].
  - assumption.
  - assumption.
  - rewrite /add_het /Cache.add_het /=. move=> f. move: (Hhet f) => [H1 H2].
    split.
    + rewrite CompTableFlatten.ExpMap.Lemmas.add_b.
      rewrite CompTable.ExpMap.Lemmas.add_b.
      rewrite H1. reflexivity.
    + move=> ecs' elrs' cs' lrs'.
      rewrite CompTableFlatten.ExpMap.Lemmas.add_o.
      rewrite CompTable.ExpMap.Lemmas.add_o.
      case: (CompTableFlatten.ExpMap.M.E.eq_dec e f);
        case: (CompTable.ExpMap.M.E.eq_dec e f) => //=.
      * move=> /eqP Hef _ [] ? ? [] ? ?; subst. done.
      * move=> _ _ Hfe Hf. exact: (H2 _ _ _ _ Hfe Hf).
  - assumption.
Qed.

Lemma cache_compatible_add_hbt e lr ec c ecs cs :
  cache_compatible ec c ->
  cnf_eqsat (tflatten ecs) cs ->
  cnf_eqnew (tflatten ecs) cs ->
  cache_compatible (add_hbt e ecs lr ec) (Cache.add_hbt e cs lr c).
Proof.
  move=> [[Hcet Hcbt] [Hhet Hhbt]] Heqs. split; [split | split].
  - assumption.
  - assumption.
  - assumption.
  - rewrite /add_hbt /Cache.add_hbt /=. move=> f. move: (Hhbt f) => [H1 H2].
    split.
    + rewrite CompTableFlatten.BexpMap.Lemmas.add_b.
      rewrite CompTable.BexpMap.Lemmas.add_b.
      rewrite H1. reflexivity.
    + move=> ecs' elr' cs' lr'.
      rewrite CompTableFlatten.BexpMap.Lemmas.add_o.
      rewrite CompTable.BexpMap.Lemmas.add_o.
      case: (CompTableFlatten.BexpMap.M.E.eq_dec e f);
        case: (CompTable.BexpMap.M.E.eq_dec e f) => //=.
      * move=> /eqP Hef _ [] ? ? [] ? ?; subst. done.
      * move=> _ _ Hfe Hf. exact: (H2 _ _ _ _ Hfe Hf).
Qed.


(* Convert CacheFlatten to Cache *)

Definition cache_of_fcache (c : cache) : Cache.cache :=
  Cache.Build_cache (comptable_of_fcomptable (ht c))
                    (ct c).

Lemma cache_of_fcache_compatible fc :
  cache_compatible fc (cache_of_fcache fc).
Proof.
  split; [split; reflexivity | exact: comptable_of_fcomptable_compatible].
Qed.
