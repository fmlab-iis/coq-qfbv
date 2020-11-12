From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics Seqs.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
From BBCache Require Import BitBlastingInit BitBlastingCCacheDef BitBlastingCacheDef BitBlastingCacheFlatten.
From BBCache Require Import CacheFlatten CacheHash QFBVHash.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ==== bit_blast_exp_hcache and bit_blast_bexp_hcache ==== *)

Fixpoint bit_blast_exp_hcache E m c g (e : hexp) : vm * cache * generator * seq cnf * word :=
  (* = bit_blast_exp_nocet = *)
  let bit_blast_exp_nocet E m c g (e : hexp) : vm * cache * generator * seq cnf * word :=
      match e with
      | epair (HEvar v) _ =>
        match find_het e c with
        | Some (cs, ls) => (m, c, g, cs, ls)
        | None => match SSAVM.find v m with
                  | None => let '(g', cs, rs) := bit_blast_var E g v in
                            (SSAVM.add v rs m, add_het e [:: cs] rs c, g', [:: cs], rs)
                  | Some rs => (m, add_het e [::] rs c, g, [::], rs)
                  end
        end
      | epair (HEconst bs) _ =>
        match find_het e c with
        | Some (cs, ls) => (m, c, g, cs, ls)
        | None => let '(g', cs, rs) := bit_blast_const g bs in
                  (m, add_het e [:: cs] rs c, g', [:: cs], rs)
        end
      | epair (HEunop op e1) _ =>
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_hcache E m c g e1 in
        match find_het e c1 with
        | Some (csop, lsop) => (m1, c1, g1, catrev cs1 csop, lsop)
        | None =>
          let '(gop, csop, lsop) := bit_blast_eunop op g1 ls1 in
          (m1, add_het e [:: csop] lsop c1, gop,
           catrev cs1 [:: csop], lsop)
        end
      | epair (HEbinop op e1 e2) _ =>
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_hcache E m c g e1 in
        let '(m2, c2, g2, cs2, ls2) := bit_blast_exp_hcache E m1 c1 g1 e2 in
        match find_het e c2 with
        | Some (csop, lsop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lsop)
        | None =>
          let '(gop, csop, lsop) := bit_blast_ebinop op g2 ls1 ls2 in
          (m2, add_het e [:: csop] lsop c2, gop,
           catrev cs1 (catrev cs2 [:: csop]), lsop)
        end
      | epair (HEite b e1 e2) _ =>
        let '(mb, cb, gb, csb, lb) := bit_blast_bexp_hcache E m c g b in
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_hcache E mb cb gb e1 in
        let '(m2, c2, g2, cs2, ls2) := bit_blast_exp_hcache E m1 c1 g1 e2 in
        match find_het e c2 with
        | Some (csop, lsop) =>
          (m2, c2, g2, catrev csb (catrev cs1 (catrev cs2 csop)), lsop)
        | None =>
          let '(gop, csop, lsop) := bit_blast_ite g2 lb ls1 ls2 in
          (m2, add_het e [:: csop] lsop c2, gop,
           catrev csb (catrev cs1 (catrev cs2 [:: csop])), lsop)
        end
      end
  (* = = *)
  in
  match find_cet e c with
  | Some ls => (m, c, g, [::], ls)
  | None => let '(m', c', g', cs, lrs) := bit_blast_exp_nocet E m c g e in
            (m', add_cet e lrs c', g', cs, lrs)
  end
with
bit_blast_bexp_hcache E m c g (e : hbexp) : vm * cache * generator * seq cnf * literal :=
  (* = bit_blast_bexp_nocbt = *)
  let bit_blast_bexp_nocbt E m c g (e : hbexp) : vm * cache * generator * seq cnf * literal :=
      match e with
      | bpair HBfalse _ =>
        match find_hbt e c with
        | Some (cs, l) => (m, c, g, cs, l)
        | None => (m, add_hbt e [::] lit_ff c, g, [::], lit_ff)
        end
      | bpair HBtrue _ =>
        match find_hbt e c with
        | Some (cs, l) => (m, c, g, cs, l)
        | None => (m, add_hbt e [::] lit_tt c, g, [::], lit_tt)
        end
      | bpair (HBbinop op e1 e2) _ =>
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_hcache E m c g e1 in
        let '(m2, c2, g2, cs2, ls2) := bit_blast_exp_hcache E m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lop)
        | None =>
          let '(gop, csop, lop) := bit_blast_bbinop op g2 ls1 ls2 in
          (m2, add_hbt e [:: csop] lop c2, gop,
           catrev cs1 (catrev cs2 [:: csop]), lop)
        end
      | bpair (HBlneg e1) _ =>
        let '(m1, c1, g1, cs1, l1) := bit_blast_bexp_hcache E m c g e1 in
        match find_hbt e c1 with
        | Some (csop, lop) => (m1, c1, g1, catrev cs1 csop, lop)
        | None => let '(gop, csop, lop) := bit_blast_lneg g1 l1 in
                  (m1, add_hbt e [:: csop] lop c1, gop,
                   catrev cs1 [:: csop], lop)
        end
      | bpair (HBconj e1 e2) _ =>
        let '(m1, c1, g1, cs1, l1) := bit_blast_bexp_hcache E m c g e1 in
        let '(m2, c2, g2, cs2, l2) := bit_blast_bexp_hcache E m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lop)
        | None => let '(gop, csop, lop) := bit_blast_conj g2 l1 l2 in
                  (m2, add_hbt e [:: csop] lop c2, gop,
                   catrev cs1 (catrev cs2 [:: csop]), lop)
        end
      | bpair (HBdisj e1 e2) _ =>
        let '(m1, c1, g1, cs1, l1) := bit_blast_bexp_hcache E m c g e1 in
        let '(m2, c2, g2, cs2, l2) := bit_blast_bexp_hcache E m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lop)
        | None => let '(gop, csop, lop) := bit_blast_disj g2 l1 l2 in
                  (m2, add_hbt e [:: csop] lop c2, gop,
                   catrev cs1 (catrev cs2 [:: csop]), lop)
        end
      end
  (* = = *)
  in
  match find_cbt e c with
  | Some l => (m, c, g, [::], l)
  | None => let '(m', c', g', cs, lr) := bit_blast_bexp_nocbt E m c g e in
            (m', add_cbt e lr c', g', cs, lr)
  end.



(* ==== relation between bit_blast_exp_hcache and bit_blast_exp_fcache ==== *)

Section WellFormedCache.

  Import QFBV.

  Definition well_formed_cet (ht : SimpTableHash.simptable) : Prop :=
    forall (e : hexp) r, SimpTableHash.find_et e ht = Some r ->
                         well_formed_hexp e.

  Definition well_formed_cbt (ht : SimpTableHash.simptable) : Prop :=
    forall (e : hbexp) r, SimpTableHash.find_bt e ht = Some r ->
                          well_formed_hbexp e.

  Definition well_formed_ct (ht : SimpTableHash.simptable) : Prop :=
    well_formed_cet ht /\ well_formed_cbt ht.

  Definition well_formed_het (ht : CompTableHash.comptable) : Prop :=
    forall (e : hexp) r, CompTableHash.find_et e ht = Some r ->
                         well_formed_hexp e.

  Definition well_formed_hbt (ht : CompTableHash.comptable) : Prop :=
    forall (e : hbexp) r, CompTableHash.find_bt e ht = Some r ->
                          well_formed_hbexp e.

  Definition well_formed_ht (ht : CompTableHash.comptable) : Prop :=
    well_formed_het ht /\ well_formed_hbt ht.

  Definition well_formed_cache (hc : CacheHash.cache) : Prop :=
    well_formed_ct (CacheHash.ct hc) /\ well_formed_ht (CacheHash.ht hc).

  Lemma well_formed_cache_find_cet hc e r :
    well_formed_cache hc -> CacheHash.find_cet e hc = Some r ->
    well_formed_hexp e.
  Proof.
    move=> [[H1 H2] [H3 H4]] Hf. exact: (H1 _ _ Hf).
  Qed.

  Lemma well_formed_cache_find_cbt hc e r :
    well_formed_cache hc -> CacheHash.find_cbt e hc = Some r ->
    well_formed_hbexp e.
  Proof.
    move=> [[H1 H2] [H3 H4]] Hf. exact: (H2 _ _ Hf).
  Qed.

  Lemma well_formed_cache_find_het hc e r :
    well_formed_cache hc -> CacheHash.find_het e hc = Some r ->
    well_formed_hexp e.
  Proof.
    move=> [[H1 H2] [H3 H4]] Hf. exact: (H3 _ _ Hf).
  Qed.

  Lemma well_formed_cache_find_hbt hc e r :
    well_formed_cache hc -> CacheHash.find_hbt e hc = Some r ->
    well_formed_hbexp e.
  Proof.
    move=> [[H1 H2] [H3 H4]] Hf. exact: (H4 _ _ Hf).
  Qed.

  Lemma well_formed_cache_add_cet hc (e : hexp) ls :
    well_formed_cache hc -> well_formed_hexp e ->
    well_formed_cache (CacheHash.add_cet e ls hc).
  Proof.
    move=> [[H1 H2] [H3 H4]] Hwfe. repeat split.
    - rewrite /add_cet /=. move=> f fls. case Hfe: (f == e).
      + rewrite (eqP Hfe). move=> _. assumption.
      + move/negP: Hfe => Hfe. rewrite (SimpTableHash.find_et_add_et_neq _ _ Hfe).
        exact: (H1 f).
    - rewrite /add_cet /=. move=> f fls. rewrite SimpTableHash.find_bt_add_et.
      exact: (H2 f).
    - rewrite /add_cet /=. move=> f fls. exact: (H3 f).
    - rewrite /add_cet /=. move=> f fls. exact: (H4 f).
  Qed.

  Lemma well_formed_cache_add_cbt hc (e : hbexp) ls :
    well_formed_cache hc -> well_formed_hbexp e ->
    well_formed_cache (CacheHash.add_cbt e ls hc).
  Proof.
    move=> [[H1 H2] [H3 H4]] Hwfe. repeat split.
    - rewrite /add_cbt /=. move=> f fls. exact: (H1 f).
    - rewrite /add_cbt /=. move=> f fls. case Hfe: (f == e).
      + rewrite (eqP Hfe). move=> _. assumption.
      + move/negP: Hfe => Hfe. rewrite (SimpTableHash.find_bt_add_bt_neq _ _ Hfe).
        exact: (H2 f).
    - rewrite /add_cbt /=. move=> f fls. exact: (H3 f).
    - rewrite /add_cbt /=. move=> f fls. exact: (H4 f).
  Qed.

  Lemma well_formed_cache_add_het hc (e : hexp) cs ls :
    well_formed_cache hc -> well_formed_hexp e ->
    well_formed_cache (CacheHash.add_het e cs ls hc).
  Proof.
    move=> [[H1 H2] [H3 H4]] Hwfe. repeat split.
    - rewrite /add_het /=. move=> f fls. exact: (H1 f).
    - rewrite /add_het /=. move=> f fls. exact: (H2 f).
    - rewrite /add_het /=. move=> f fls. case Hfe: (f == e).
      + rewrite (eqP Hfe). move=> _; assumption.
      + move/negP: Hfe=> Hfe. rewrite (CompTableHash.find_et_add_et_neq _ _ _ Hfe).
        exact: (H3 f).
    - rewrite /add_het /=. move=> f fls. exact: (H4 f).
  Qed.

  Lemma well_formed_cache_add_hbt hc (e : hbexp) cs ls :
    well_formed_cache hc -> well_formed_hbexp e ->
    well_formed_cache (CacheHash.add_hbt e cs ls hc).
  Proof.
    move=> [[H1 H2] [H3 H4]] Hwfe. repeat split.
    - rewrite /add_hbt /=. move=> f fls. exact: (H1 f).
    - rewrite /add_hbt /=. move=> f fls. exact: (H2 f).
    - rewrite /add_hbt /=. move=> f fls. exact: (H3 f).
    - rewrite /add_hbt /=. move=> f fls. case Hfe: (f == e).
      + rewrite (eqP Hfe). move=> _; assumption.
      + move/negP: Hfe=> Hfe. rewrite (CompTableHash.find_bt_add_bt_neq _ _ _ Hfe).
        exact: (H4 f).
  Qed.

  Lemma well_formed_cache_reset_ct c :
    well_formed_cache c -> well_formed_cache (reset_ct c).
  Proof.
    rewrite /reset_ct. move=>[[H1 H2] [H3 H4]]. by repeat split.
  Qed.

End WellFormedCache.


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
             (hc : CacheHash.cache) (fc : CacheFlatten.cache) : Prop :=
    ct_compatible (CacheHash.ct hc) (CacheFlatten.ct fc) /\
    ht_compatible (CacheHash.ht hc) (CacheFlatten.ht fc).

  Lemma cache_compatible_find_cet hc fc (e : exp) :
    cache_compatible hc fc ->
    CacheHash.find_cet (hash_exp e) hc = CacheFlatten.find_cet e fc.
  Proof. move=>[[H1 H2] [H3 H4]]. exact: (H1 e). Qed.

  Lemma cache_compatible_find_cbt hc fc (e : bexp) :
    cache_compatible hc fc ->
    CacheHash.find_cbt (hash_bexp e) hc = CacheFlatten.find_cbt e fc.
  Proof. move=>[[H1 H2] [H3 H4]]. exact: (H2 e). Qed.

  Lemma cache_compatible_find_het hc fc (e : exp) :
    cache_compatible hc fc ->
    CacheHash.find_het (hash_exp e) hc = CacheFlatten.find_het e fc.
  Proof. move=>[[H1 H2] [H3 H4]]. exact: (H3 e). Qed.

  Lemma cache_compatible_find_hbt hc fc (e : bexp) :
    cache_compatible hc fc ->
    CacheHash.find_hbt (hash_bexp e) hc = CacheFlatten.find_hbt e fc.
  Proof. move=>[[H1 H2] [H3 H4]]. exact: (H4 e). Qed.

  Lemma cache_compatible_find_cet_hexp hc fc (e : hexp) :
    cache_compatible hc fc ->
    well_formed_hexp e ->
    CacheHash.find_cet e hc = CacheFlatten.find_cet e fc.
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hexp Hwf).
    exact: (cache_compatible_find_cet _ Hcc).
  Qed.

  Lemma cache_compatible_find_cbt_hbexp hc fc (e : hbexp) :
    cache_compatible hc fc ->
    well_formed_hbexp e ->
    CacheHash.find_cbt e hc = CacheFlatten.find_cbt e fc.
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hbexp Hwf).
    exact: (cache_compatible_find_cbt _ Hcc).
  Qed.

  Lemma cache_compatible_find_het_hexp hc fc (e : hexp) :
    cache_compatible hc fc ->
    well_formed_hexp e ->
    CacheHash.find_het e hc = CacheFlatten.find_het e fc.
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hexp Hwf).
    exact: (cache_compatible_find_het _ Hcc).
  Qed.

  Lemma cache_compatible_find_hbt_hbexp hc fc (e : hbexp) :
    cache_compatible hc fc ->
    well_formed_hbexp e ->
    CacheHash.find_hbt e hc = CacheFlatten.find_hbt e fc.
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hbexp Hwf).
    exact: (cache_compatible_find_hbt _ Hcc).
  Qed.

  Lemma cache_compatible_add_cet hc fc (e : exp) ls :
    cache_compatible hc fc ->
    cache_compatible (CacheHash.add_cet (hash_exp e) ls hc)
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
    cache_compatible (CacheHash.add_cbt (hash_bexp e) ls hc)
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
    cache_compatible (CacheHash.add_het (hash_exp e) cs ls hc)
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
    cache_compatible (CacheHash.add_hbt (hash_bexp e) cs ls hc)
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
    cache_compatible (CacheHash.add_cet e ls hc)
                     (CacheFlatten.add_cet e ls fc).
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hexp Hwf).
    exact: (cache_compatible_add_cet _ _ Hcc).
  Qed.

  Lemma cache_compatible_add_cet_hbexp hc fc (e : hbexp) ls :
    cache_compatible hc fc ->
    well_formed_hbexp e ->
    cache_compatible (CacheHash.add_cbt e ls hc)
                     (CacheFlatten.add_cbt e ls fc).
  Proof.
    move=> Hcc Hwf. rewrite -{1}(hash_unhash_hbexp Hwf).
    exact: (cache_compatible_add_cbt _ _ Hcc).
  Qed.

  Lemma cache_compatible_reset_ct hc fc :
    cache_compatible hc fc ->
    cache_compatible (CacheHash.reset_ct hc) (CacheFlatten.reset_ct fc).
  Proof.
    rewrite /reset_ct /CacheFlatten.reset_ct. move=> [[H1 H2] [H3 H4]].
      by repeat split.
  Qed.

End CacheCompatible.


Ltac t_auto_hook ::=
  match goal with
  | |- ?e = ?e => reflexivity
  | |- _ /\ _ => split
  | |- well_formed_cache (add_cet (hash_exp _) _ _) =>
    apply: well_formed_cache_add_cet
  | |- well_formed_cache (add_cbt (hash_bexp _) _ _) =>
    apply: well_formed_cache_add_cbt
  | |- well_formed_cache (add_het (hash_exp _) _ _ _) =>
    apply: well_formed_cache_add_het
  | |- well_formed_cache (add_hbt (hash_bexp _) _ _ _) =>
    apply: well_formed_cache_add_hbt
  | |- well_formed_cache (add_cet ?he _ _) =>
    replace he with (hash_exp (unhash_hexp he))
      by (rewrite /=; try rewrite !unhash_hash_exp; try rewrite !unhash_hash_bexp;
          try rewrite !ehval_hash_exp; try rewrite !bhval_hash_bexp; reflexivity);
    apply: well_formed_cache_add_cet
  | |- well_formed_cache (add_cbt ?he _ _) =>
    replace he with (hash_bexp (unhash_hbexp he))
      by (rewrite /=; try rewrite !unhash_hash_exp; try rewrite !unhash_hash_bexp;
          try rewrite !ehval_hash_exp; try rewrite !bhval_hash_bexp; reflexivity);
    apply: well_formed_cache_add_cbt
  | |- cache_compatible (add_cet _ ?rs _) (CacheFlatten.add_cet _ ?rs _) =>
    apply: cache_compatible_add_cet
  | |- cache_compatible (add_cbt _ ?rs _) (CacheFlatten.add_cbt _ ?rs _) =>
    apply: cache_compatible_add_cbt
  | |- cache_compatible (add_het _ ?cs ?rs _) (CacheFlatten.add_het _ ?cs ?rs _) =>
    apply: cache_compatible_add_het
  | |- cache_compatible (add_hbt _ ?cs ?rs _) (CacheFlatten.add_hbt _ ?cs ?rs _) =>
    apply: cache_compatible_add_hbt
  | |- context f [unhash_hexp (hash_exp ?e)] =>
    rewrite (unhash_hash_exp e) /=
  | |- context f [unhash_hbexp (hash_bexp ?e)] =>
    rewrite (unhash_hash_bexp e) /=
  | |- context f [ehval (hash_exp ?e)] =>
    rewrite (ehval_hash_exp e)
  | |- context f [bhval (hash_bexp ?e)] =>
    rewrite (bhval_hash_bexp e)
  | |- context f [well_formed_hexp (hash_exp ?e)] =>
    rewrite (hash_exp_well_formed e)
  | |- context f [well_formed_hbexp (hash_bexp ?e)] =>
    rewrite (hash_bexp_well_formed e)

  | |- context f [CacheHash.add_cet (epair ?he ?hh) _ _] =>
    match goal with
    | |- context g [CacheFlatten.add_cet ?e _ _] =>
      replace (epair he hh) with (hash_exp e)
    end
  | |- hash_exp _ = epair _ _ => rewrite /=
  end.

Lemma bit_blast_exp_hcache_fcache
      E (e : QFBV.exp) m ihc ifc g hm fm
      ohc ofc hg fg hcs fcs hlrs flrs :
  well_formed_cache ihc ->
  cache_compatible ihc ifc ->
  bit_blast_exp_hcache E m ihc g (hash_exp e) =  (hm, ohc, hg, hcs, hlrs) ->
  bit_blast_exp_fcache E m ifc g e =  (fm, ofc, fg, fcs, flrs) ->
  hm = fm
  /\ well_formed_cache ohc
  /\ cache_compatible ohc ofc
  /\ hg = fg
  /\ hcs = fcs
  /\ hlrs = flrs
with bit_blast_bexp_hcache_fcache
       E (e : QFBV.bexp) m ihc ifc g hm fm
       ohc ofc hg fg hcs fcs hlr flr :
       well_formed_cache ihc ->
       cache_compatible ihc ifc ->
       bit_blast_bexp_hcache E m ihc g (hash_bexp e) =  (hm, ohc, hg, hcs, hlr) ->
       bit_blast_bexp_fcache E m ifc g e =  (fm, ofc, fg, fcs, flr) ->
       hm = fm
       /\ well_formed_cache ohc
       /\ cache_compatible ohc ofc
       /\ hg = fg
       /\ hcs = fcs
       /\ hlr = flr.
Proof.
  (* bit_blast_exp_hcache_fcache *)
  - case: e => /=.
    + move=> v Hwf Hcc.
      replace (epair (HEvar v) 1) with (hash_exp (QFBV.Evar v)) by reflexivity.
      rewrite (cache_compatible_find_cet _ Hcc).
      rewrite (cache_compatible_find_het _ Hcc).
      case: (CacheFlatten.find_cet (QFBV.Evar v) ifc).
      * move=> ls [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * case: (CacheFlatten.find_het (QFBV.Evar v) ifc).
        -- move=> [cs ls] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- case Hvm: (SSAVM.find v m).
           ++ move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
                by t_auto.
           ++ dcase (bit_blast_var E g v) => [[[g1 cs1] rs1] Hbbv].
              move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
                by t_auto.
    + move=> bs Hf Hcc.
      replace (epair (HEconst bs) 1) with (hash_exp (QFBV.Econst bs)) by reflexivity.
      rewrite (cache_compatible_find_cet _ Hcc).
      rewrite (cache_compatible_find_het _ Hcc).
      case: (CacheFlatten.find_cet (QFBV.Econst bs) ifc).
      * move=> ls [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * case: (CacheFlatten.find_het (QFBV.Econst bs) ifc).
        -- move=> [cs ls] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
    + move=> op e Hwf Hcc.
      replace (epair (HEunop op (hash_exp e)) (ehval (hash_exp e) + 1))
        with (hash_exp (QFBV.Eunop op e)) by reflexivity.
      rewrite (cache_compatible_find_cet _ Hcc).
      case: (CacheFlatten.find_cet (QFBV.Eunop op e) ifc).
      * move=> ls [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * dcase (bit_blast_exp_hcache E m ihc g (hash_exp e)) =>
        [[[[[hm1 hc1] hg1] hcs1] hls1] Hhbb].
        dcase (bit_blast_exp_fcache E m ifc g e) =>
        [[[[[fm1 fc1] fg1] fcs1] fls1] Hfbb].
        move: (bit_blast_exp_hcache_fcache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf Hcc Hhbb Hfbb).
        move=> [? [Hwf1 [Hcc1 [? [? ?]]]]]; subst.
        rewrite (cache_compatible_find_het _ Hcc1).
        case: (CacheFlatten.find_het (QFBV.Eunop op e) fc1).
        -- move=> [cs ls] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- dcase (bit_blast_eunop op fg1 fls1) => [[[g1 cs1] ls1] Hbb].
           move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
    + move=> op e1 e2 Hwf Hcc.
      replace (epair (HEbinop op (hash_exp e1) (hash_exp e2))
                     (ehval (hash_exp e1) + ehval (hash_exp e2) + 1))
        with (hash_exp (QFBV.Ebinop op e1 e2)) by reflexivity.
      rewrite (cache_compatible_find_cet _ Hcc).
      case: (CacheFlatten.find_cet (QFBV.Ebinop op e1 e2) ifc).
      * move=> ls [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * dcase (bit_blast_exp_hcache E m ihc g (hash_exp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hls1] Hhbb1].
        dcase (bit_blast_exp_hcache E hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hls2] Hhbb2].
        dcase (bit_blast_exp_fcache E m ifc g e1) =>
        [[[[[fm1 fc1] fg1] fcs1] fls1] Hfbb1].
        dcase (bit_blast_exp_fcache E fm1 fc1 fg1 e2) =>
        [[[[[fm2 fc2] fg2] fcs2] fls2] Hfbb2].
        move: (bit_blast_exp_hcache_fcache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf Hcc Hhbb1 Hfbb1).
        move=> [? [Hwf1 [Hcc1 [? [? ?]]]]]; subst.
        move: (bit_blast_exp_hcache_fcache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf1 Hcc1 Hhbb2 Hfbb2).
        move=> [? [Hwf2 [Hcc2 [? [? ?]]]]]; subst.
        rewrite (cache_compatible_find_het _ Hcc2).
        case: (CacheFlatten.find_het (QFBV.Ebinop op e1 e2) fc2).
        -- move=> [cs ls] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- dcase (bit_blast_ebinop op fg2 fls1 fls2) => [[[gop csop] lsop] Hbbop].
           move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
    + move=> e1 e2 e3 Hwf Hcc.
      replace (epair (HEite (hash_bexp e1) (hash_exp e2) (hash_exp e3))
                     (bhval (hash_bexp e1) +
                      ehval (hash_exp e2) + ehval (hash_exp e3) + 1)) with
          (hash_exp (QFBV.Eite e1 e2 e3)) by reflexivity.
      rewrite (cache_compatible_find_cet _ Hcc).
      case: (CacheFlatten.find_cet (QFBV.Eite e1 e2 e3) ifc).
      * move=> ls [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * dcase (bit_blast_bexp_hcache E m ihc g (hash_bexp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hls1] Hhbb1].
        dcase (bit_blast_exp_hcache E hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hls2] Hhbb2].
        dcase (bit_blast_exp_hcache E hm2 hc2 hg2 (hash_exp e3)) =>
        [[[[[hm3 hc3] hg3] hcs3] hls3] Hhbb3].
        dcase (bit_blast_bexp_fcache E m ifc g e1) =>
        [[[[[fm1 fc1] fg1] fcs1] fls1] Hfbb1].
        dcase (bit_blast_exp_fcache E fm1 fc1 fg1 e2) =>
        [[[[[fm2 fc2] fg2] fcs2] fls2] Hfbb2].
        dcase (bit_blast_exp_fcache E fm2 fc2 fg2 e3) =>
        [[[[[fm3 fc3] fg3] fcs3] fls3] Hfbb3].
        move: (bit_blast_bexp_hcache_fcache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf Hcc Hhbb1 Hfbb1).
        move=> [? [Hwf1 [Hcc1 [? [? ?]]]]]; subst.
        move: (bit_blast_exp_hcache_fcache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf1 Hcc1 Hhbb2 Hfbb2).
        move=> [? [Hwf2 [Hcc2 [? [? ?]]]]]; subst.
        move: (bit_blast_exp_hcache_fcache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf2 Hcc2 Hhbb3 Hfbb3).
        move=> [? [Hwf3 [Hcc3 [? [? ?]]]]]; subst.
        rewrite (cache_compatible_find_het _ Hcc3).
        case: (CacheFlatten.find_het (QFBV.Eite e1 e2 e3) fc3).
        -- move=> [cs ls] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- dcase (bit_blast_ite fg3 fls1 fls2 fls3) => [[[gop csop] lsop] Hbbop].
           move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
  (* bit_blast_bexp_hcache_fcache *)
  - case: e => /=.
    + move=> Hwf Hcc.
      replace (bpair HBfalse 1) with (hash_bexp QFBV.Bfalse) by reflexivity.
      rewrite (cache_compatible_find_cbt _ Hcc).
      case: (CacheFlatten.find_cbt QFBV.Bfalse ifc).
      * move=> lr [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * rewrite (cache_compatible_find_hbt _ Hcc).
        case: (CacheFlatten.find_hbt QFBV.Bfalse ifc).
        -- move=> [cs lr] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
    + move=> Hwf Hcc.
      replace (bpair HBtrue 1) with (hash_bexp QFBV.Btrue) by reflexivity.
      rewrite (cache_compatible_find_cbt _ Hcc).
      case: (CacheFlatten.find_cbt QFBV.Btrue ifc).
      * move=> lr [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * rewrite (cache_compatible_find_hbt _ Hcc).
        case: (CacheFlatten.find_hbt QFBV.Btrue ifc).
        -- move=> [cs lr] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
    + move=> op e1 e2 Hwf Hcc.
      replace (bpair (HBbinop op (hash_exp e1) (hash_exp e2))
                     (ehval (hash_exp e1) + ehval (hash_exp e2) + 1)) with
          (hash_bexp (QFBV.Bbinop op e1 e2)) by reflexivity.
      rewrite (cache_compatible_find_cbt _ Hcc).
      case: (CacheFlatten.find_cbt (QFBV.Bbinop op e1 e2) ifc).
      * move=> lr [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * dcase (bit_blast_exp_hcache E m ihc g (hash_exp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_exp_hcache E hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
        dcase (bit_blast_exp_fcache E m ifc g e1) =>
        [[[[[fm1 fc1] fg1] fcs1] flr1] Hfbb1].
        dcase (bit_blast_exp_fcache E fm1 fc1 fg1 e2) =>
        [[[[[fm2 fc2] fg2] fcs2] flr2] Hfbb2].
        move: (bit_blast_exp_hcache_fcache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf Hcc Hhbb1 Hfbb1).
        move=> [? [Hwf1 [Hcc1 [? [? ?]]]]]; subst.
        move: (bit_blast_exp_hcache_fcache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf1 Hcc1 Hhbb2 Hfbb2).
        move=> [? [Hwf2 [Hcc2 [? [? ?]]]]]; subst.
        rewrite (cache_compatible_find_hbt _ Hcc2).
        case: (CacheFlatten.find_hbt (QFBV.Bbinop op e1 e2) fc2).
        -- move=> [cs lr] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- dcase (bit_blast_bbinop op fg2 flr1 flr2) => [[[gop csop] lop] Hbbop].
           move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
    + move=> e Hwf Hcc.
      replace (bpair (HBlneg (hash_bexp e)) (bhval (hash_bexp e) + 1)) with
          (hash_bexp (QFBV.Blneg e)) by reflexivity.
      rewrite (cache_compatible_find_cbt _ Hcc).
      case: (CacheFlatten.find_cbt (QFBV.Blneg e) ifc).
      * move=> lr [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * dcase (bit_blast_bexp_hcache E m ihc g (hash_bexp e)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_bexp_fcache E m ifc g e) =>
        [[[[[fm1 fc1] fg1] fcs1] flr1] Hfbb1].
        move: (bit_blast_bexp_hcache_fcache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                            Hwf Hcc Hhbb1 Hfbb1).
        move=> [? [Hwf1 [Hcc1 [? [? ?]]]]]; subst.
        rewrite (cache_compatible_find_hbt _ Hcc1).
        case: (CacheFlatten.find_hbt (QFBV.Blneg e) fc1).
        -- move=> [cs lr] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
    + move=> e1 e2 Hwf Hcc.
      replace (bpair (HBconj (hash_bexp e1) (hash_bexp e2))
                     (bhval (hash_bexp e1) + bhval (hash_bexp e2) + 1)) with
          (hash_bexp (QFBV.Bconj e1 e2)) by reflexivity.
      rewrite (cache_compatible_find_cbt _ Hcc).
      case: (CacheFlatten.find_cbt (QFBV.Bconj e1 e2) ifc).
      * move=> lr [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * dcase (bit_blast_bexp_hcache E m ihc g (hash_bexp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_bexp_hcache E hm1 hc1 hg1 (hash_bexp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
        dcase (bit_blast_bexp_fcache E m ifc g e1) =>
        [[[[[fm1 fc1] fg1] fcs1] flr1] Hfbb1].
        dcase (bit_blast_bexp_fcache E fm1 fc1 fg1 e2) =>
        [[[[[fm2 fc2] fg2] fcs2] flr2] Hfbb2].
        move: (bit_blast_bexp_hcache_fcache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                            Hwf Hcc Hhbb1 Hfbb1).
        move=> [? [Hwf1 [Hcc1 [? [? ?]]]]]; subst.
        move: (bit_blast_bexp_hcache_fcache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                            Hwf1 Hcc1 Hhbb2 Hfbb2).
        move=> [? [Hwf2 [Hcc2 [? [? ?]]]]]; subst.
        rewrite (cache_compatible_find_hbt _ Hcc2).
        case: (CacheFlatten.find_hbt (QFBV.Bconj e1 e2) fc2).
        -- move=> [cs lr] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
    + move=> e1 e2 Hwf Hcc.
      replace (bpair (HBdisj (hash_bexp e1) (hash_bexp e2))
                     (bhval (hash_bexp e1) + bhval (hash_bexp e2) + 1)) with
          (hash_bexp (QFBV.Bdisj e1 e2)) by reflexivity.
      rewrite (cache_compatible_find_cbt _ Hcc).
      case: (CacheFlatten.find_cbt (QFBV.Bdisj e1 e2) ifc).
      * move=> lr [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * dcase (bit_blast_bexp_hcache E m ihc g (hash_bexp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_bexp_hcache E hm1 hc1 hg1 (hash_bexp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
        dcase (bit_blast_bexp_fcache E m ifc g e1) =>
        [[[[[fm1 fc1] fg1] fcs1] flr1] Hfbb1].
        dcase (bit_blast_bexp_fcache E fm1 fc1 fg1 e2) =>
        [[[[[fm2 fc2] fg2] fcs2] flr2] Hfbb2].
        move: (bit_blast_bexp_hcache_fcache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                            Hwf Hcc Hhbb1 Hfbb1).
        move=> [? [Hwf1 [Hcc1 [? [? ?]]]]]; subst.
        move: (bit_blast_bexp_hcache_fcache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                            Hwf1 Hcc1 Hhbb2 Hfbb2).
        move=> [? [Hwf2 [Hcc2 [? [? ?]]]]]; subst.
        rewrite (cache_compatible_find_hbt _ Hcc2).
        case: (CacheFlatten.find_hbt (QFBV.Bdisj e1 e2) fc2).
        -- move=> [cs lr] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
Qed.



(* ==== basic case ==== *)

(* = bit-blasting only one bexp = *)

Definition init_hcache : cache := CacheHash.empty.

Lemma init_hcache_well_formed : well_formed_cache init_hcache.
Proof. done. Qed.

Lemma init_hcache_fcache_compatible : cache_compatible init_hcache init_fcache.
Proof. done. Qed.

Theorem bit_blast_bexp_hcache_sound E (e : QFBV.bexp) m c g cs lr :
  bit_blast_bexp_hcache
    E init_vm init_hcache init_gen (hash_bexp e) = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexp e E ->
  ~ (sat (add_prelude ([::neg_lit lr]::(tflatten cs)))) ->
  (forall s, AdhereConform.conform_bexp e s E ->
             QFBV.eval_bexp e s).
Proof.
  move=> Hhbb Hwf Hsat.
  dcase (bit_blast_bexp_fcache E init_vm init_fcache init_gen e) =>
  [[[[[m' c'] g'] cs'] lr'] Hfbb].
  move: (bit_blast_bexp_hcache_fcache init_hcache_well_formed
                                      init_hcache_fcache_compatible
                                      Hhbb Hfbb).
  move=> [? [Hwf' [Hcc' [? [? ?]]]]]; subst.
  exact: (bit_blast_bexp_fcache_sound Hfbb Hwf Hsat).
Qed.

Theorem bit_blast_bexp_hcache_complete E (e : QFBV.bexp) m c g cs lr :
  bit_blast_bexp_hcache
    E init_vm init_hcache init_gen (hash_bexp e) = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexp e E ->
  (forall s, AdhereConform.conform_bexp e s E ->
             QFBV.eval_bexp e s) ->
  ~ (sat (add_prelude ([::neg_lit lr]::(tflatten cs)))).
Proof.
  move=> Hhbb Hwf Hev.
  dcase (bit_blast_bexp_fcache E init_vm init_fcache init_gen e) =>
  [[[[[m' c'] g'] cs'] lr'] Hfbb].
  move: (bit_blast_bexp_hcache_fcache init_hcache_well_formed
                                      init_hcache_fcache_compatible
                                      Hhbb Hfbb).
  move=> [? [Hwf' [Hcc' [? [? ?]]]]]; subst.
  exact: (bit_blast_bexp_fcache_complete Hfbb Hwf Hev).
Qed.

Theorem bit_blast_bexp_hcache_sat_sound E (e : QFBV.bexp) m c g cs lr :
  bit_blast_bexp_hcache
    E init_vm init_hcache init_gen (hash_bexp e) = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexp e E ->
  (sat (add_prelude ([:: lr]::(tflatten cs)))) ->
  (exists s, AdhereConform.conform_bexp e s E /\
             QFBV.eval_bexp e s).
Proof.
  move=> Hhbb Hwf Hsat.
  dcase (bit_blast_bexp_fcache E init_vm init_fcache init_gen e) =>
  [[[[[m' c'] g'] cs'] lr'] Hfbb].
  move: (bit_blast_bexp_hcache_fcache init_hcache_well_formed
                                      init_hcache_fcache_compatible
                                      Hhbb Hfbb).
  move=> [? [Hwf' [Hcc' [? [? ?]]]]]; subst.
  exact: (bit_blast_bexp_fcache_sat_sound Hfbb Hwf Hsat).
Qed.

Theorem bit_blast_bexp_hcache_sat_complete E (e : QFBV.bexp) m c g cs lr :
  bit_blast_bexp_hcache
    E init_vm init_hcache init_gen (hash_bexp e) = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexp e E ->
  (exists s, AdhereConform.conform_bexp e s E /\
             QFBV.eval_bexp e s) ->
  (sat (add_prelude ([:: lr]::(tflatten cs)))).
Proof.
  move=> Hhbb Hwf Hev.
  dcase (bit_blast_bexp_fcache E init_vm init_fcache init_gen e) =>
  [[[[[m' c'] g'] cs'] lr'] Hfbb].
  move: (bit_blast_bexp_hcache_fcache init_hcache_well_formed
                                      init_hcache_fcache_compatible
                                      Hhbb Hfbb).
  move=> [? [Hwf' [Hcc' [? [? ?]]]]]; subst.
  exact: (bit_blast_bexp_fcache_sat_complete Hfbb Hwf Hev).
Qed.


(* ==== general case ==== *)

(* = bit-blasting multiple bexps = *)

Definition bit_blast_bexp_hcache_tflatten E m c g e :=
  let '(m', c', g', css', lr') := bit_blast_bexp_hcache E m c g e in
  (m', c', g', tflatten css', lr').

Fixpoint bit_blast_hbexps_hcache E (es : seq hbexp) :=
  match es with
  | [::] => (init_vm, init_hcache, init_gen, add_prelude [::], lit_tt)
  | e :: es' =>
    let '(m, c, g, cs, lr) := bit_blast_hbexps_hcache E es' in
    bit_blast_bexp_hcache_tflatten E m (CacheHash.reset_ct c) g e
  end.

Definition bit_blast_bexps_hcache E (es : seq QFBV.bexp) :=
  bit_blast_hbexps_hcache E (map hash_bexp es).

Lemma bit_blast_bexps_hcache_valid E es hm hc hg hcs hlr fm fc fg fcs flr :
  bit_blast_bexps_hcache E es = (hm, hc, hg, hcs, hlr) ->
  bit_blast_bexps_fcache E es = (fm, fc, fg, fcs, flr) ->
  hm = fm
  /\ well_formed_cache hc
  /\ cache_compatible hc fc
  /\ hg = fg
  /\ hcs = fcs
  /\ hlr = flr.
Proof.
  elim: es hm hc hg hcs hlr fm fc fg fcs flr =>
  [| e es IH]  hm hc hg hcs hlr fm fc fg fcs flr /=.
  - move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
  - rewrite /bit_blast_bexps_hcache /=.
    dcase (bit_blast_hbexps_hcache E [seq hash_bexp i | i <- es]) =>
    [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
    rewrite Hhbb1. rewrite /bit_blast_bexp_hcache_tflatten.
    dcase (bit_blast_bexp_hcache E hm1 (reset_ct hc1) hg1 (hash_bexp e)) =>
    [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
    case=> ? ? ? ? ?; subst.
    dcase (bit_blast_bexps_fcache E es) => [[[[[fm1 fc1] fg1] fcs1] flr1] Hfbb1].
    rewrite /bit_blast_bexp_fcache_tflatten.
    dcase (bit_blast_bexp_fcache E fm1 (CacheFlatten.reset_ct fc1) fg1 e) =>
    [[[[[fm2 fc2] fg2] fcs2] flr2] Hfbb2].
    case=> ? ? ? ? ?; subst.
    move: (IH _ _ _ _ _ _ _ _ _ _ Hhbb1 Hfbb1).
    move=> [Hm [Hwf1 [Hcc1 [Hg [Hcs Hlr]]]]]; subst.
    move: (bit_blast_bexp_hcache_fcache (well_formed_cache_reset_ct Hwf1)
                                        (cache_compatible_reset_ct Hcc1)
                                        Hhbb2 Hfbb2).
    move=> [? [Hwf2 [Hcc2 [? [? ?]]]]]; subst. by repeat split => //=.
Qed.

Theorem bit_blast_bexps_hcache_sound e es E m c g cs lr :
  bit_blast_bexps_hcache E (e::es) = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexps (e::es) E ->
  ~ (sat (add_prelude ([::neg_lit lr]::cs))) ->
  (forall s, AdhereConform.conform_bexps (e::es) s E ->
             QFBV.eval_bexp e s).
Proof.
  move=> Hhbb Hwf Hsat.
  dcase (bit_blast_bexps_fcache E (e::es)) => [[[[[m' c'] g'] cs'] lr'] Hfbb].
  move: (bit_blast_bexps_hcache_valid Hhbb Hfbb).
  move=> [Hm [Hwfc [Hcc [Hg [Hcs Hlr]]]]]; subst.
  exact: (bit_blast_bexps_fcache_sound Hfbb Hwf Hsat).
Qed.

Theorem bit_blast_bexps_hcache_complete e es E m c g cs lr :
  bit_blast_bexps_hcache E (e::es) = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexps (e::es) E ->
  (forall s, AdhereConform.conform_bexps (e::es) s E ->
             QFBV.eval_bexp e s) ->
  ~ (sat (add_prelude ([::neg_lit lr]::cs))).
Proof.
  move=> Hhbb Hwf Hev Hsat.
  dcase (bit_blast_bexps_fcache E (e::es)) => [[[[[m' c'] g'] cs'] lr'] Hfbb].
  move: (bit_blast_bexps_hcache_valid Hhbb Hfbb).
  move=> [Hm [Hwfc [Hcc [Hg [Heqs Hlr]]]]]; subst.
  exact: (bit_blast_bexps_fcache_complete Hfbb Hwf Hev).
Qed.

Definition bexp_to_cnf_hcache E m c g e :=
  let '(m', c', g', cs, lr) := bit_blast_bexp_hcache_tflatten E m c g e in
  (m', c', g', add_prelude ([::neg_lit lr]::cs)).
