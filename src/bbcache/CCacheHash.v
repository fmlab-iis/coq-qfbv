From Coq Require Import ZArith OrderedType Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import EqFMaps EqVar.
From BitBlasting Require Import QFBV CNF State BBCommon.
From BBCache Require Import QFBVHash CompTableHash SimpTableHash CompCache.

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
  {| ht := CompTableHash.empty;
     ct := CompTableHash.empty |}.

Definition find_het e c := CompTableHash.find_et e (ht c).
Definition find_hbt e c := CompTableHash.find_bt e (ht c).
Definition find_cet e c := CompTableHash.find_et e (ct c).
Definition find_cbt e c := CompTableHash.find_bt e (ct c).


(* ==== modification ==== *)

Definition add_het e cs ls c :=
  {| ht := CompTableHash.add_et e cs ls (ht c);
     ct := ct c |}.

Definition add_hbt e cs l c :=
  {| ht := CompTableHash.add_bt e cs l (ht c);
     ct := ct c |}.

Definition add_cet e cs ls c :=
  {| ht := ht c;
     ct := CompTableHash.add_et e cs ls (ct c) |}.

Definition add_cbt e cs l c :=
  {| ht := ht c;
     ct := CompTableHash.add_bt e cs l (ct c) |}.

Definition reset_ct (c : ccache) :=
  {| ht := ht c;
     ct := CompTableHash.empty |}.

Lemma find_het_equation e c : find_het e c = CompTableHash.find_et e (ht c).
Proof. done. Qed.

Lemma find_hbt_equation e c : find_hbt e c = CompTableHash.find_bt e (ht c).
Proof. done. Qed.

Lemma find_cet_equation e c : find_cet e c = CompTableHash.find_et e (ct c).
Proof. done. Qed.

Lemma find_cbt_equation e c : find_cbt e c = CompTableHash.find_bt e (ct c).
Proof. done. Qed.

Lemma add_het_cet_comm c e1 cs1 ls1 e2 cs2 ls2 :
  add_het e1 cs1 ls1 (add_cet e2 cs2 ls2 c) = add_cet e2 cs2 ls2 (add_het e1 cs1 ls1 c).
Proof. done. Qed.

Lemma add_het_cbt_comm c e1 cs1 ls1 e2 cs2 l2 :
  add_het e1 cs1 ls1 (add_cbt e2 cs2 l2 c) = add_cbt e2 cs2 l2 (add_het e1 cs1 ls1 c).
Proof. done. Qed.

Lemma add_hbt_cet_comm c e1 cs1 l1 e2 cs2 ls2 :
  add_hbt e1 cs1 l1 (add_cet e2 cs2 ls2 c) = add_cet e2 cs2 ls2 (add_hbt e1 cs1 l1 c).
Proof. done. Qed.

Lemma add_hbt_cbt_comm c e1 cs1 l1 e2 cs2 l2 :
  add_hbt e1 cs1 l1 (add_cbt e2 cs2 l2 c) = add_cbt e2 cs2 l2 (add_hbt e1 cs1 l1 c).
Proof. done. Qed.

Lemma find_het_add_het_eq e cs ls c : find_het e (add_het e cs ls c) = Some (cs, ls).
Proof.
  rewrite /find_het /add_het /=. by apply: CompTableHash.find_et_add_et_eq.
Qed.

Lemma find_het_add_het_neq e0 e cs ls c :
  ~ e0 == e -> find_het e0 (add_het e cs ls c) = find_het e0 c.
Proof.
  rewrite /find_het /add_het /=. by apply: CompTableHash.find_et_add_et_neq.
Qed.

Lemma find_het_add_hbt e0 e cs l c : find_het e0 (add_hbt e cs l c) = find_het e0 c.
Proof.
  rewrite /find_het /add_hbt /=. by apply: CompTableHash.find_et_add_bt.
Qed.

Lemma find_het_add_cet e0 e cs ls c : find_het e0 (add_cet e cs ls c) = find_het e0 c.
Proof. done. Qed.

Lemma find_het_add_cbt e0 e cs l c : find_het e0 (add_cbt e cs l c) = find_het e0 c.
Proof. done. Qed.

Lemma find_hbt_add_het e0 e cs ls c : find_hbt e0 (add_het e cs ls c) = find_hbt e0 c.
Proof.
  rewrite /find_hbt /add_het /=. by apply: CompTableHash.find_bt_add_et.
Qed.

Lemma find_hbt_add_hbt_eq e cs l c : find_hbt e (add_hbt e cs l c) = Some (cs, l).
Proof.
  rewrite /find_hbt /add_hbt /=. by apply: CompTableHash.find_bt_add_bt_eq.
Qed.

Lemma find_hbt_add_hbt_neq e0 e cs l c :
  ~ e0 == e -> find_hbt e0 (add_hbt e cs l c) = find_hbt e0 c.
Proof.
  rewrite /find_hbt /add_hbt /=. by apply: CompTableHash.find_bt_add_bt_neq.
Qed.

Lemma find_hbt_add_cet e0 e cs ls c : find_hbt e0 (add_cet e cs ls c) = find_hbt e0 c.
Proof. done. Qed.

Lemma find_hbt_add_cbt e0 e cs l c : find_hbt e0 (add_cbt e cs l c) = find_hbt e0 c.
Proof. done. Qed.

Lemma find_cet_add_het e0 e cs ls c : find_cet e0 (add_het e cs ls c) = find_cet e0 c.
Proof. done. Qed.

Lemma find_cet_add_hbt e0 e cs l c : find_cet e0 (add_hbt e cs l c) = find_cet e0 c.
Proof. done. Qed.

Lemma find_cet_add_cet_eq e cs ls c : find_cet e (add_cet e cs ls c) = Some (cs, ls).
Proof.
  rewrite /find_cet /add_cet /=. by apply: CompTableHash.find_et_add_et_eq.
Qed.

Lemma find_cet_add_cet_neq e0 e cs ls c :
  ~ e0 == e -> find_cet e0 (add_cet e cs ls c) = find_cet e0 c.
Proof.
  rewrite /find_cet /add_cet /=. by apply: CompTableHash.find_et_add_et_neq.
Qed.

Lemma find_cet_add_cbt e0 e cs l c : find_cet e0 (add_cbt e cs l c) = find_cet e0 c.
Proof.
  rewrite /find_cet /add_cbt /=. by apply: CompTableHash.find_et_add_bt.
Qed.

Lemma find_cbt_add_het e0 e cs ls c : find_cbt e0 (add_het e cs ls c) = find_cbt e0 c.
Proof. done. Qed.

Lemma find_cbt_add_hbt e0 e cs l c : find_cbt e0 (add_hbt e cs l c) = find_cbt e0 c.
Proof. done. Qed.

Lemma find_cbt_add_cet e0 e cs ls c : find_cbt e0 (add_cet e cs ls c) = find_cbt e0 c.
Proof.
  rewrite /find_cbt /add_cet /=. by apply: CompTableHash.find_bt_add_et.
Qed.

Lemma find_cbt_add_cbt_eq e cs l c : find_cbt e (add_cbt e cs l c) = Some (cs, l).
Proof.
  rewrite /find_cbt /add_cbt /=. by apply: CompTableHash.find_bt_add_bt_eq.
Qed.

Lemma find_cbt_add_cbt_neq e0 e cs l c :
  ~ e0 == e -> find_cbt e0 (add_cbt e cs l c) = find_cbt e0 c.
Proof.
  rewrite /find_cbt /add_cbt /=. by apply: CompTableHash.find_bt_add_bt_neq.
Qed.



From BBCache Require CompTableFlatten CCacheFlatten.

Section CCacheCompatible.

  Import QFBV.

  Definition ct_compatible hc fc := comptable_compatible (ct hc) (CCacheFlatten.ct fc).

  Definition ht_compatible hc fc := comptable_compatible (ht hc) (CCacheFlatten.ht fc).

  Definition ccache_compatible hc fc := ct_compatible hc fc /\ ht_compatible hc fc.

  Lemma ccache_compatible_find_cet hc fc (e : exp) :
    ccache_compatible hc fc ->
    find_cet (hash_exp e) hc = CCacheFlatten.find_cet e fc.
  Proof. move=>[[H1 H2] [H3 H4]]. exact: (H1 e). Qed.

  Lemma ccache_compatible_find_cbt hc fc (e : bexp) :
    ccache_compatible hc fc ->
    find_cbt (hash_bexp e) hc = CCacheFlatten.find_cbt e fc.
  Proof. move=>[[H1 H2] [H3 H4]]. exact: (H2 e). Qed.

  Lemma ccache_compatible_find_het hc fc (e : exp) :
    ccache_compatible hc fc ->
    find_het (hash_exp e) hc = CCacheFlatten.find_het e fc.
  Proof. move=>[[H1 H2] [H3 H4]]. exact: (H3 e). Qed.

  Lemma ccache_compatible_find_hbt hc fc (e : bexp) :
    ccache_compatible hc fc ->
    find_hbt (hash_bexp e) hc = CCacheFlatten.find_hbt e fc.
  Proof. move=>[[H1 H2] [H3 H4]]. exact: (H4 e). Qed.

  Lemma ccache_compatible_find_cet_hexp hc fc (e : hexp) :
    ccache_compatible hc fc ->
    well_formed_hexp e ->
    find_cet e hc = CCacheFlatten.find_cet e fc.
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hexp Hwf).
    exact: (ccache_compatible_find_cet _ Hcc).
  Qed.

  Lemma ccache_compatible_find_cbt_hbexp hc fc (e : hbexp) :
    ccache_compatible hc fc ->
    well_formed_hbexp e ->
    find_cbt e hc = CCacheFlatten.find_cbt e fc.
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hbexp Hwf).
    exact: (ccache_compatible_find_cbt _ Hcc).
  Qed.

  Lemma ccache_compatible_find_het_hexp hc fc (e : hexp) :
    ccache_compatible hc fc ->
    well_formed_hexp e ->
    find_het e hc = CCacheFlatten.find_het e fc.
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hexp Hwf).
    exact: (ccache_compatible_find_het _ Hcc).
  Qed.

  Lemma ccache_compatible_find_hbt_hbexp hc fc (e : hbexp) :
    ccache_compatible hc fc ->
    well_formed_hbexp e ->
    find_hbt e hc = CCacheFlatten.find_hbt e fc.
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hbexp Hwf).
    exact: (ccache_compatible_find_hbt _ Hcc).
  Qed.

  Lemma ccache_compatible_add_cet hc fc (e : exp) cs ls :
    ccache_compatible hc fc ->
    ccache_compatible (add_cet (hash_exp e) cs ls hc)
                      (CCacheFlatten.add_cet e cs ls fc).
  Proof.
    move=> [[H1 H2] [H3 H4]]. repeat split => //=.
    apply: et_compatible_add. assumption.
  Qed.

  Lemma ccache_compatible_add_cbt hc fc (e : bexp) cs ls :
    ccache_compatible hc fc ->
    ccache_compatible (add_cbt (hash_bexp e) cs ls hc)
                      (CCacheFlatten.add_cbt e cs ls fc).
  Proof.
    move=> [[H1 H2] [H3 H4]]. repeat split => //=.
    apply: bt_compatible_add. assumption.
  Qed.

  Lemma ccache_compatible_add_het hc fc (e : exp) cs ls :
    ccache_compatible hc fc ->
    ccache_compatible (add_het (hash_exp e) cs ls hc)
                      (CCacheFlatten.add_het e cs ls fc).
  Proof.
    move=> [[H1 H2] [H3 H4]]. repeat split => //=.
    apply: et_compatible_add. assumption.
  Qed.

  Lemma ccache_compatible_add_hbt hc fc (e : bexp) cs ls :
    ccache_compatible hc fc ->
    ccache_compatible (add_hbt (hash_bexp e) cs ls hc)
                      (CCacheFlatten.add_hbt e cs ls fc).
  Proof.
    move=> [[H1 H2] [H3 H4]]. repeat split => //=.
    apply: bt_compatible_add. assumption.
  Qed.

  Lemma ccache_compatible_add_cet_hexp hc fc (e : hexp) cs ls :
    ccache_compatible hc fc ->
    well_formed_hexp e ->
    ccache_compatible (add_cet e cs ls hc)
                      (CCacheFlatten.add_cet e cs ls fc).
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hexp Hwf).
    exact: (ccache_compatible_add_cet _ _ _ Hcc).
  Qed.

  Lemma ccache_compatible_add_cbt_hbexp hc fc (e : hbexp) cs ls :
    ccache_compatible hc fc ->
    well_formed_hbexp e ->
    ccache_compatible (add_cbt e cs ls hc)
                      (CCacheFlatten.add_cbt e cs ls fc).
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hbexp Hwf).
    exact: (ccache_compatible_add_cbt _ _ _ Hcc).
  Qed.

  Lemma ccache_compatible_add_het_hexp hc fc (e : hexp) cs ls :
    ccache_compatible hc fc ->
    well_formed_hexp e ->
    ccache_compatible (add_het e cs ls hc)
                      (CCacheFlatten.add_het e cs ls fc).
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hexp Hwf).
    exact: (ccache_compatible_add_het _ _ _ Hcc).
  Qed.

  Lemma ccache_compatible_add_hbt_hbexp hc fc (e : hbexp) cs ls :
    ccache_compatible hc fc ->
    well_formed_hbexp e ->
    ccache_compatible (add_hbt e cs ls hc)
                      (CCacheFlatten.add_hbt e cs ls fc).
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hbexp Hwf).
    exact: (ccache_compatible_add_hbt _ _ _ Hcc).
  Qed.

  Lemma ccache_compatible_reset_ct hc fc :
    ccache_compatible hc fc ->
    ccache_compatible (reset_ct hc) (CCacheFlatten.reset_ct fc).
  Proof.
    rewrite /reset_ct /CCacheFlatten.reset_ct. move=> [[H1 H2] [H3 H4]].
      by repeat split.
  Qed.

End CCacheCompatible.

