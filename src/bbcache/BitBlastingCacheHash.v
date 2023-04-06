From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types EqOrder EqVar Nats ZAriths Tactics Seqs.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
From BitBlasting Require Import AdhereConform.
From BBCache Require Import BitBlastingInit.
From BBCache Require Import BitBlastingCCacheExport BitBlastingCacheExport.
From BBCache Require Import CacheFlatten BitBlastingCCacheFlatten BitBlastingCacheFlatten.
From BBCache Require Import CacheHash QFBVHash BitBlastingCCacheHash.

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

  Definition well_formed_cache (hc : CacheHash.cache) : Prop :=
    well_formed_st (CacheHash.ct hc) /\ well_formed_ct (CacheHash.ht hc).

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

Lemma bit_blast_exp_hcache_well_formed_cache
      E (e : QFBV.exp) m ihc g hm ohc hg hcs hlrs :
  well_formed_cache ihc ->
  bit_blast_exp_hcache E m ihc g (hash_exp e) =  (hm, ohc, hg, hcs, hlrs) ->
  well_formed_cache ohc
with bit_blast_bexp_hcache_well_formed_cache
       E (e : QFBV.bexp) m ihc g hm ohc hg hcs hlr :
       well_formed_cache ihc ->
       bit_blast_bexp_hcache E m ihc g (hash_bexp e) =  (hm, ohc, hg, hcs, hlr) ->
       well_formed_cache ohc.
Proof.
  (* bit_blast_exp_hcache_fcache_well_formed_cache *)
  - case: e => /=.
    + move=> v Hwf.
      replace (epair (HEvar v) 1) with (hash_exp (QFBV.Evar v)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Evar v)) ihc).
      * move=> ls [] ? ? ? ? ?; subst. assumption.
      * case: (find_het (hash_exp (QFBV.Evar v)) ihc).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. by t_auto.
        -- case Hvm: (SSAVM.find v m).
           ++ move=> [] ? ? ? ? ?; subst. by t_auto.
           ++ dcase (bit_blast_var E g v) => [[[g1 cs1] rs1] Hbbv].
              move=> [] ? ? ? ? ?; subst. by t_auto.
    + move=> bs Hf.
      replace (epair (HEconst bs) 1) with (hash_exp (QFBV.Econst bs)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Econst bs)) ihc).
      * move=> ls [] ? ? ? ? ?; subst. assumption.
      * case: (find_het (hash_exp (QFBV.Econst bs)) ihc).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. by t_auto.
    + move=> op e Hwf.
      replace (epair (HEunop op (hash_exp e)) (ehval (hash_exp e) + 1))
        with (hash_exp (QFBV.Eunop op e)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Eunop op e)) ihc).
      * move=> ls [] ? ? ? ? ?; subst. assumption.
      * dcase (bit_blast_exp_hcache E m ihc g (hash_exp e)) =>
        [[[[[hm1 hc1] hg1] hcs1] hls1] Hhbb].
        move: (bit_blast_exp_hcache_well_formed_cache
                 _ _ _ _ _ _ _ _ _ _ Hwf Hhbb) => Hwf_hc1.
        case: (find_het (hash_exp (QFBV.Eunop op e)) hc1).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. by t_auto.
        -- dcase (bit_blast_eunop op hg1 hls1) => [[[g1 cs1] ls1] Hbb].
           move=> [] ? ? ? ? ?; subst. by t_auto.
    + move=> op e1 e2 Hwf.
      replace (epair (HEbinop op (hash_exp e1) (hash_exp e2))
                     (ehval (hash_exp e1) + ehval (hash_exp e2) + 1))
        with (hash_exp (QFBV.Ebinop op e1 e2)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Ebinop op e1 e2)) ihc).
      * move=> ls [] ? ? ? ? ?; subst. assumption.
      * dcase (bit_blast_exp_hcache E m ihc g (hash_exp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hls1] Hhbb1].
        dcase (bit_blast_exp_hcache E hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hls2] Hhbb2].
        move: (bit_blast_exp_hcache_well_formed_cache
                 _ _ _ _ _ _ _ _ _ _ Hwf Hhbb1) => Hwf1.
        move: (bit_blast_exp_hcache_well_formed_cache
                 _ _ _ _ _ _ _ _ _ _ Hwf1 Hhbb2) => Hwf2.
        case: (find_het (hash_exp (QFBV.Ebinop op e1 e2)) hc2).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. by t_auto.
        -- dcase (bit_blast_ebinop op hg2 hls1 hls2) => [[[gop csop] lsop] Hbbop].
           move=> [] ? ? ? ? ?; subst. by t_auto.
    + move=> e1 e2 e3 Hwf.
      replace (epair (HEite (hash_bexp e1) (hash_exp e2) (hash_exp e3))
                     (bhval (hash_bexp e1) +
                      ehval (hash_exp e2) + ehval (hash_exp e3) + 1)) with
          (hash_exp (QFBV.Eite e1 e2 e3)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Eite e1 e2 e3)) ihc).
      * move=> ls [] ? ? ? ? ?; subst. assumption.
      * dcase (bit_blast_bexp_hcache E m ihc g (hash_bexp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hls1] Hhbb1].
        dcase (bit_blast_exp_hcache E hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hls2] Hhbb2].
        dcase (bit_blast_exp_hcache E hm2 hc2 hg2 (hash_exp e3)) =>
        [[[[[hm3 hc3] hg3] hcs3] hls3] Hhbb3].
        move: (bit_blast_bexp_hcache_well_formed_cache
                 _ _ _ _ _ _ _ _ _ _ Hwf Hhbb1) => Hwf1.
        move: (bit_blast_exp_hcache_well_formed_cache
                 _ _ _ _ _ _ _ _ _ _ Hwf1 Hhbb2) => Hwf2.
        move: (bit_blast_exp_hcache_well_formed_cache
                 _ _ _ _ _ _ _ _ _ _ Hwf2 Hhbb3) => Hwf3.
        case: (find_het (hash_exp (QFBV.Eite e1 e2 e3)) hc3).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. by t_auto.
        -- dcase (bit_blast_ite hg3 hls1 hls2 hls3) => [[[gop csop] lsop] Hbbop].
           move=> [] ? ? ? ? ?; subst. by t_auto.
  (* bit_blast_bexp_hcache_fcache_well_formed_cache *)
  - case: e => /=.
    + move=> Hwf.
      replace (bpair HBfalse 1) with (hash_bexp QFBV.Bfalse) by reflexivity.
      case: (find_cbt (hash_bexp QFBV.Bfalse) ihc).
      * move=> lr [] ? ? ? ? ?; subst. assumption.
      * case: (find_hbt (hash_bexp QFBV.Bfalse) ihc).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. by t_auto.
    + move=> Hwf.
      replace (bpair HBtrue 1) with (hash_bexp QFBV.Btrue) by reflexivity.
      case: (find_cbt (hash_bexp QFBV.Btrue) ihc).
      * move=> lr [] ? ? ? ? ?; subst. assumption.
        case: (find_hbt (hash_bexp QFBV.Btrue) ihc).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. by t_auto.
    + move=> op e1 e2 Hwf.
      replace (bpair (HBbinop op (hash_exp e1) (hash_exp e2))
                     (ehval (hash_exp e1) + ehval (hash_exp e2) + 1)) with
          (hash_bexp (QFBV.Bbinop op e1 e2)) by reflexivity.
      case: (find_cbt (hash_bexp (QFBV.Bbinop op e1 e2)) ihc).
      * move=> lr [] ? ? ? ? ?; subst. assumption.
      * dcase (bit_blast_exp_hcache E m ihc g (hash_exp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_exp_hcache E hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
        move: (bit_blast_exp_hcache_well_formed_cache
                 _ _ _ _ _ _ _ _ _ _ Hwf Hhbb1) => Hwf1.
        move: (bit_blast_exp_hcache_well_formed_cache
                 _ _ _ _ _ _ _ _ _ _ Hwf1 Hhbb2) => Hwf2.
        case: (find_hbt (hash_bexp (QFBV.Bbinop op e1 e2)) hc2).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. by t_auto.
        -- dcase (bit_blast_bbinop op hg2 hlr1 hlr2) => [[[gop csop] lop] Hbbop].
           move=> [] ? ? ? ? ?; subst. by t_auto.
    + move=> e Hwf.
      replace (bpair (HBlneg (hash_bexp e)) (bhval (hash_bexp e) + 1)) with
          (hash_bexp (QFBV.Blneg e)) by reflexivity.
      case: (find_cbt (hash_bexp (QFBV.Blneg e)) ihc).
      * move=> lr [] ? ? ? ? ?; subst. assumption.
      * dcase (bit_blast_bexp_hcache E m ihc g (hash_bexp e)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        move: (bit_blast_bexp_hcache_well_formed_cache
                 _ _ _ _ _ _ _ _ _ _ Hwf Hhbb1) => Hwf1.
        case: (find_hbt (hash_bexp (QFBV.Blneg e)) hc1).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. by t_auto.
    + move=> e1 e2 Hwf.
      replace (bpair (HBconj (hash_bexp e1) (hash_bexp e2))
                     (bhval (hash_bexp e1) + bhval (hash_bexp e2) + 1)) with
          (hash_bexp (QFBV.Bconj e1 e2)) by reflexivity.
      case: (find_cbt (hash_bexp (QFBV.Bconj e1 e2)) ihc).
      * move=> lr [] ? ? ? ? ?; subst. done.
      * dcase (bit_blast_bexp_hcache E m ihc g (hash_bexp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_bexp_hcache E hm1 hc1 hg1 (hash_bexp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
        move: (bit_blast_bexp_hcache_well_formed_cache
                 _ _ _ _ _ _ _ _ _ _ Hwf Hhbb1) => Hwf1.
        move: (bit_blast_bexp_hcache_well_formed_cache
                 _ _ _ _ _ _ _ _ _ _ Hwf1 Hhbb2) => Hwf2.
        case: (find_hbt (hash_bexp (QFBV.Bconj e1 e2)) hc2).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. by t_auto.
    + move=> e1 e2 Hwf.
      replace (bpair (HBdisj (hash_bexp e1) (hash_bexp e2))
                     (bhval (hash_bexp e1) + bhval (hash_bexp e2) + 1)) with
          (hash_bexp (QFBV.Bdisj e1 e2)) by reflexivity.
      case: (find_cbt (hash_bexp (QFBV.Bdisj e1 e2)) ihc).
      * move=> lr [] ? ? ? ? ?; subst. assumption.
      * dcase (bit_blast_bexp_hcache E m ihc g (hash_bexp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_bexp_hcache E hm1 hc1 hg1 (hash_bexp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
        move: (bit_blast_bexp_hcache_well_formed_cache
                 _ _ _ _ _ _ _ _ _ _ Hwf Hhbb1) => Hwf1.
        move: (bit_blast_bexp_hcache_well_formed_cache
                 _ _ _ _ _ _ _ _ _ _ Hwf1 Hhbb2) => Hwf2.
        case: (find_hbt (hash_bexp (QFBV.Bdisj e1 e2)) hc2).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. by t_auto.
Qed.

Ltac t_exists :=
  match goal with
  | H : cache_compatible ?ohc ?ifc
    |- exists ofc : CacheFlatten.cache, cache_compatible ?ohc ofc =>
    exists ifc
  | H : cache_compatible ?ihc ?ifc
    |- exists ofc : CacheFlatten.cache,
      cache_compatible (add_cet ?he ?hlrs ?ihc) ofc =>
    exists (CacheFlatten.add_cet (unhash_hexp he) hlrs ifc)
  | H : cache_compatible ?ihc ?ifc
    |- exists ofc : CacheFlatten.cache,
      cache_compatible (add_cbt ?he ?hlr ?ihc) ofc =>
    exists (CacheFlatten.add_cbt (unhash_hbexp he) hlr ifc)
  | H : cache_compatible ?ihc ?ifc
    |- exists ofc : CacheFlatten.cache,
      cache_compatible
        (add_cet ?he1 ?hlrs1
                 (add_het ?he2 ?hcs2 ?hlrs2 ?ihc)) ofc =>
    exists (CacheFlatten.add_cet
              (unhash_hexp he1) hlrs1
              (CacheFlatten.add_het (unhash_hexp he2) hcs2 hlrs2 ifc))
  | H : cache_compatible ?ihc ?ifc
    |- exists ofc : CacheFlatten.cache,
      cache_compatible
        (add_cbt ?he1 ?hlr1
                 (add_hbt ?he2 ?hcs2 ?hlr2 ?ihc)) ofc =>
    exists (CacheFlatten.add_cbt
              (unhash_hbexp he1) hlr1
              (CacheFlatten.add_hbt (unhash_hbexp he2) hcs2 hlr2 ifc))
  end; rewrite /=.

Lemma bit_blast_exp_hcache_cache_compatible
      E (e : QFBV.exp) m ihc ifc g hm ohc hg hcs hlrs :
  cache_compatible ihc ifc ->
  bit_blast_exp_hcache E m ihc g (hash_exp e) =  (hm, ohc, hg, hcs, hlrs) ->
  exists ofc, cache_compatible ohc ofc
with bit_blast_bexp_hcache_cache_compatible
       E (e : QFBV.bexp) m ihc ifc g hm ohc hg hcs hlr :
       cache_compatible ihc ifc ->
       bit_blast_bexp_hcache E m ihc g (hash_bexp e) =  (hm, ohc, hg, hcs, hlr) ->
       exists ofc, cache_compatible ohc ofc.
Proof.
  (* bit_blast_exp_hcache_fcache_cache_compatible *)
  - case: e => /=.
    + move=> v Hcc.
      replace (epair (HEvar v) 1) with (hash_exp (QFBV.Evar v)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Evar v)) ihc).
      * move=> ls [] ? ? ? ? ?; subst. t_exists. assumption.
      * case: (find_het (hash_exp (QFBV.Evar v)) ihc).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- case Hvm: (SSAVM.find v m).
           ++ move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
           ++ dcase (bit_blast_var E g v) => [[[g1 cs1] rs1] Hbbv].
              move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
    + move=> bs Hcc.
      replace (epair (HEconst bs) 1) with (hash_exp (QFBV.Econst bs)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Econst bs)) ihc).
      * move=> ls [] ? ? ? ? ?; subst. t_exists. assumption.
      * case: (find_het (hash_exp (QFBV.Econst bs)) ihc).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
    + move=> op e Hcc.
      replace (epair (HEunop op (hash_exp e)) (ehval (hash_exp e) + 1))
        with (hash_exp (QFBV.Eunop op e)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Eunop op e)) ihc).
      * move=> ls [] ? ? ? ? ?; subst. t_exists. assumption.
      * dcase (bit_blast_exp_hcache E m ihc g (hash_exp e)) =>
        [[[[[hm1 hc1] hg1] hcs1] hls1] Hhbb].
        move: (bit_blast_exp_hcache_cache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc Hhbb) => [fc1 Hcc1].
        case: (find_het (hash_exp (QFBV.Eunop op e)) hc1).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- dcase (bit_blast_eunop op hg1 hls1) => [[[g1 cs1] ls1] Hbb].
           move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
    + move=> op e1 e2 Hcc.
      replace (epair (HEbinop op (hash_exp e1) (hash_exp e2))
                     (ehval (hash_exp e1) + ehval (hash_exp e2) + 1))
        with (hash_exp (QFBV.Ebinop op e1 e2)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Ebinop op e1 e2)) ihc).
      * move=> ls [] ? ? ? ? ?; subst. t_exists. assumption.
      * dcase (bit_blast_exp_hcache E m ihc g (hash_exp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hls1] Hhbb1].
        dcase (bit_blast_exp_hcache E hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hls2] Hhbb2].
        move: (bit_blast_exp_hcache_cache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc Hhbb1) => [fc1 Hcc1].
        move: (bit_blast_exp_hcache_cache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc1 Hhbb2) => [fc2 Hcc2].
        case: (find_het (hash_exp (QFBV.Ebinop op e1 e2)) hc2).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- dcase (bit_blast_ebinop op hg2 hls1 hls2) => [[[gop csop] lsop] Hbbop].
           move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
    + move=> e1 e2 e3 Hcc.
      replace (epair (HEite (hash_bexp e1) (hash_exp e2) (hash_exp e3))
                     (bhval (hash_bexp e1) +
                      ehval (hash_exp e2) + ehval (hash_exp e3) + 1)) with
          (hash_exp (QFBV.Eite e1 e2 e3)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Eite e1 e2 e3)) ihc).
      * move=> ls [] ? ? ? ? ?; subst. t_exists. assumption.
      * dcase (bit_blast_bexp_hcache E m ihc g (hash_bexp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hls1] Hhbb1].
        dcase (bit_blast_exp_hcache E hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hls2] Hhbb2].
        dcase (bit_blast_exp_hcache E hm2 hc2 hg2 (hash_exp e3)) =>
        [[[[[hm3 hc3] hg3] hcs3] hls3] Hhbb3].
        move: (bit_blast_bexp_hcache_cache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc Hhbb1) => [fc1 Hcc1].
        move: (bit_blast_exp_hcache_cache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc1 Hhbb2) => [fc2 Hcc2].
        move: (bit_blast_exp_hcache_cache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc2 Hhbb3) => [fc3 Hcc3].
        case: (find_het (hash_exp (QFBV.Eite e1 e2 e3)) hc3).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- dcase (bit_blast_ite hg3 hls1 hls2 hls3) => [[[gop csop] lsop] Hbbop].
           move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
  (* bit_blast_bexp_hcache_fcache_cache_compatible *)
  - case: e => /=.
    + move=> Hcc.
      replace (bpair HBfalse 1) with (hash_bexp QFBV.Bfalse) by reflexivity.
      case: (find_cbt (hash_bexp QFBV.Bfalse) ihc).
      * move=> lr [] ? ? ? ? ?; subst. t_exists. assumption.
      * case: (find_hbt (hash_bexp QFBV.Bfalse) ihc).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
    + move=> Hcc.
      replace (bpair HBtrue 1) with (hash_bexp QFBV.Btrue) by reflexivity.
      case: (find_cbt (hash_bexp QFBV.Btrue) ihc).
      * move=> lr [] ? ? ? ? ?; subst. t_exists. assumption.
      * case: (find_hbt (hash_bexp QFBV.Btrue) ihc).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
    + move=> op e1 e2 Hcc.
      replace (bpair (HBbinop op (hash_exp e1) (hash_exp e2))
                     (ehval (hash_exp e1) + ehval (hash_exp e2) + 1)) with
          (hash_bexp (QFBV.Bbinop op e1 e2)) by reflexivity.
      case: (find_cbt (hash_bexp (QFBV.Bbinop op e1 e2)) ihc).
      * move=> lr [] ? ? ? ? ?; subst. t_exists. assumption.
      * dcase (bit_blast_exp_hcache E m ihc g (hash_exp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_exp_hcache E hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
        move: (bit_blast_exp_hcache_cache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc Hhbb1) => [fc1 Hcc1].
        move: (bit_blast_exp_hcache_cache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc1 Hhbb2) => [fc2 Hcc2].
        case: (find_hbt (hash_bexp (QFBV.Bbinop op e1 e2)) hc2).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- dcase (bit_blast_bbinop op hg2 hlr1 hlr2) => [[[gop csop] lop] Hbbop].
           move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
    + move=> e Hcc.
      replace (bpair (HBlneg (hash_bexp e)) (bhval (hash_bexp e) + 1)) with
          (hash_bexp (QFBV.Blneg e)) by reflexivity.
      case: (find_cbt (hash_bexp (QFBV.Blneg e)) ihc).
      * move=> lr [] ? ? ? ? ?; subst. t_exists. assumption.
      * dcase (bit_blast_bexp_hcache E m ihc g (hash_bexp e)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        move: (bit_blast_bexp_hcache_cache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc Hhbb1) => [fc1 Hcc1].
        case: (find_hbt (hash_bexp (QFBV.Blneg e)) hc1).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
    + move=> e1 e2 Hcc.
      replace (bpair (HBconj (hash_bexp e1) (hash_bexp e2))
                     (bhval (hash_bexp e1) + bhval (hash_bexp e2) + 1)) with
          (hash_bexp (QFBV.Bconj e1 e2)) by reflexivity.
      case: (find_cbt (hash_bexp (QFBV.Bconj e1 e2)) ihc).
      * move=> lr [] ? ? ? ? ?; subst. t_exists. assumption.
      * dcase (bit_blast_bexp_hcache E m ihc g (hash_bexp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_bexp_hcache E hm1 hc1 hg1 (hash_bexp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
        move: (bit_blast_bexp_hcache_cache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc Hhbb1) => [fc1 Hcc1].
        move: (bit_blast_bexp_hcache_cache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc1 Hhbb2) => [fc2 Hcc2].
        case: (find_hbt (hash_bexp (QFBV.Bconj e1 e2)) hc2).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
    + move=> e1 e2 Hcc.
      replace (bpair (HBdisj (hash_bexp e1) (hash_bexp e2))
                     (bhval (hash_bexp e1) + bhval (hash_bexp e2) + 1)) with
          (hash_bexp (QFBV.Bdisj e1 e2)) by reflexivity.
      case: (find_cbt (hash_bexp (QFBV.Bdisj e1 e2)) ihc).
      * move=> lr [] ? ? ? ? ?; subst. t_exists. assumption.
      * dcase (bit_blast_bexp_hcache E m ihc g (hash_bexp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_bexp_hcache E hm1 hc1 hg1 (hash_bexp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
        move: (bit_blast_bexp_hcache_cache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc Hhbb1) => [fc1 Hcc1].
        move: (bit_blast_bexp_hcache_cache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc1 Hhbb2) => [fc2 Hcc2].
        case: (find_hbt (hash_bexp (QFBV.Bdisj e1 e2)) hc2).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
Qed.

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


Lemma bit_blast_bexp_hcache_preserve
      TE e ihm ihc ihg ohm ohc ohg ohcs ohlr ifc ic icc :
  bit_blast_bexp_hcache TE ihm ihc ihg (hash_bexp e) =  (ohm, ohc, ohg, ohcs, ohlr) ->
  well_formed_cache ihc ->
  cache_compatible ihc ifc ->
  CacheFlatten.cache_compatible ifc ic ->
  Cache.compatible ic icc ->
  vm_preserve ihm ohm.
Proof.
  move=> Hhbb Hwfihc Hccihc Hccifc Hccic.
  dcase (bit_blast_bexp_fcache TE ihm ifc ihg e) =>
  [[[[[ofm ofc] ofg] ofcs] oflr] Hfbb].
  move: (bit_blast_bexp_hcache_fcache Hwfihc Hccihc Hhbb Hfbb) =>
  [? [Hwfohc [Hccohc [? [? ?]]]]]; subst.
  dcase (bit_blast_bexp_cache TE ihm ic ihg e) =>
  [[[[[om oc] og] ocs] olr] Hbb].
  move: (bit_blast_bexp_fcache_valid Hccifc Hfbb Hbb) =>
  [? [Hccofc [? [Heqs ?]]]]; subst.
  move: (bit_blast_bexp_cache_is_bit_blast_bexp_ccache Hccic Hbb)
  => [cicc [Hcbb Hccoc]].
  exact: (bit_blast_bexp_ccache_preserve Hcbb).
Qed.

Lemma bit_blast_bexp_hcache_bound
      TE e ihm ihc ihg ohm ohc ohg ohcs ohlr ifc ic icc :
  bit_blast_bexp_hcache TE ihm ihc ihg (hash_bexp e) =  (ohm, ohc, ohg, ohcs, ohlr) ->
  well_formed_cache ihc ->
  cache_compatible ihc ifc ->
  CacheFlatten.cache_compatible ifc ic ->
  Cache.compatible ic icc ->
  CompCache.well_formed icc ->
  CompCache.bound icc ihm ->
  bound_bexp e ohm.
Proof.
  move=> Hhbb Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc.
  dcase (bit_blast_bexp_fcache TE ihm ifc ihg e) =>
  [[[[[ofm ofc] ofg] ofcs] oflr] Hfbb].
  move: (bit_blast_bexp_hcache_fcache Hwfihc Hccihc Hhbb Hfbb) =>
  [? [Hwfohc [Hccohc [? [? ?]]]]]; subst.
  dcase (bit_blast_bexp_cache TE ihm ic ihg e) =>
  [[[[[om oc] og] ocs] olr] Hbb].
  move: (bit_blast_bexp_fcache_valid Hccifc Hfbb Hbb) =>
  [? [Hccofc [? [Heqs ?]]]]; subst.
  move: (bit_blast_bexp_cache_is_bit_blast_bexp_ccache Hccic Hbb)
  => [cicc [Hcbb Hccoc]].
  exact: (proj1 (bit_blast_bexp_ccache_bound_cache Hcbb Hwficc Hboundicc)).
Qed.

Lemma bit_blast_bexp_hcache_adhere
      TE e ihm ihc ihg ohm ohc ohg ohcs ohlr ifc ic icc :
  bit_blast_bexp_hcache TE ihm ihc ihg (hash_bexp e) =  (ohm, ohc, ohg, ohcs, ohlr) ->
  well_formed_cache ihc ->
  cache_compatible ihc ifc ->
  CacheFlatten.cache_compatible ifc ic ->
  Cache.compatible ic icc ->
  adhere ihm TE ->
  adhere ohm TE.
Proof.
  move=> Hhbb Hwfihc Hccihc Hccifc Hccic Hadihm.
  dcase (bit_blast_bexp_fcache TE ihm ifc ihg e) =>
  [[[[[ofm ofc] ofg] ofcs] oflr] Hfbb].
  move: (bit_blast_bexp_hcache_fcache Hwfihc Hccihc Hhbb Hfbb) =>
  [? [Hwfohc [Hccohc [? [? ?]]]]]; subst.
  dcase (bit_blast_bexp_cache TE ihm ic ihg e) =>
  [[[[[om oc] og] ocs] olr] Hbb].
  move: (bit_blast_bexp_fcache_valid Hccifc Hfbb Hbb) =>
  [? [Hccofc [? [Heqs ?]]]]; subst.
  move: (bit_blast_bexp_cache_is_bit_blast_bexp_ccache Hccic Hbb)
  => [cicc [Hcbb Hccoc]].
  exact: (bit_blast_bexp_ccache_adhere Hadihm Hcbb).
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

Corollary bit_blast_bexp_hcache_sat_sound_and_complete E (e : QFBV.bexp) m c g cs lr :
  bit_blast_bexp_hcache
    E init_vm init_hcache init_gen (hash_bexp e) = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexp e E ->
  ((exists s, AdhereConform.conform_bexp e s E /\ QFBV.eval_bexp e s)
   <->
   (exists (E : env), interp_cnf E (add_prelude ([:: lr]::(tflatten cs))))).
Proof.
  move=> Hbb Hwf. split.
  - exact: (bit_blast_bexp_hcache_sat_complete Hbb).
  - exact: (bit_blast_bexp_hcache_sat_sound Hbb).
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



(* Bit-blasting a sequence of QFBV bexps as a conjunction *)

Fixpoint bit_blast_hbexps_hcache_conjs_rec E m c g rcs rlrs es : vm * cache * generator * seq cnf * cnf :=
  match es with
  | [::] => (m, c, g, rcs, rlrs)
  | hd::tl => let '(m', c', g', cs, lr) := bit_blast_bexp_hcache E m c g hd in
              bit_blast_hbexps_hcache_conjs_rec E m' c' g'
                                                (catrev cs rcs) ([:: lr]::rlrs) tl
  end.

Definition bit_blast_hbexps_hcache_conjs E m c g es :=
  bit_blast_hbexps_hcache_conjs_rec E m c g [::] [::] es.

Lemma bit_blast_hbexps_hcache_conjs_rec_empty E m c g rcs rlrs :
  bit_blast_hbexps_hcache_conjs_rec E m c g rcs rlrs [::] = (m, c, g, rcs, rlrs).
Proof. reflexivity. Qed.

Lemma bit_blast_hbexps_hcache_conjs_rec_singleton E m c g rcs rlrs e :
  bit_blast_hbexps_hcache_conjs_rec E m c g rcs rlrs [:: e] =
  let '(m', c', g', cs, lr) := bit_blast_bexp_hcache E m c g e in
  (m', c', g', (catrev cs rcs), [::lr]::rlrs).
Proof. reflexivity. Qed.

Lemma bit_blast_hbexps_hcache_conjs_rec_cons E m c g rcs rlrs e es :
  bit_blast_hbexps_hcache_conjs_rec E m c g rcs rlrs (e::es) =
  let '(m', c', g', cs, lr) := bit_blast_bexp_hcache E m c g e in
  bit_blast_hbexps_hcache_conjs_rec E m' c' g'
                                    (catrev cs rcs) ([::lr]::rlrs) es.
Proof. reflexivity. Qed.

Lemma bit_blast_hbexps_hcache_conjs_rec_rcons E m c g rcs rlrs es e :
  bit_blast_hbexps_hcache_conjs_rec E m c g rcs rlrs (rcons es e) =
  let '(m', c', g', cs, lrs) := bit_blast_hbexps_hcache_conjs_rec
                                  E m c g rcs rlrs es in
  bit_blast_hbexps_hcache_conjs_rec E m' c' g' cs lrs [:: e].
Proof.
  rewrite /=. elim: es m c g rcs rlrs e => [| hd tl IH] m c g rcs rlrs e //=.
  dcase (bit_blast_bexp_hcache E m c g hd) => [[[[[m1 c1] g1] cs1] lr1] Hbb_hd].
  rewrite -IH. reflexivity.
Qed.

Lemma bit_blast_hbexps_hcache_conjs_rec_cat E m c g rcs rlrs es1 es2 :
  bit_blast_hbexps_hcache_conjs_rec E m c g rcs rlrs (es1 ++ es2) =
  let '(m', c', g', cs1, lrs1) := bit_blast_hbexps_hcache_conjs_rec
                                    E m c g rcs rlrs es1 in
  bit_blast_hbexps_hcache_conjs_rec E m' c' g' cs1 lrs1 es2.
Proof.
  elim: es1 es2 m c g rcs rlrs => [| hd tl IH] es2 m c g rcs rlrs //=.
  dcase (bit_blast_bexp_hcache E m c g hd) => [[[[[m1 c1] g1] cs1] lr1] Hbb_hd].
  rewrite -IH. reflexivity.
Qed.

Lemma bit_blast_hbexps_hcache_conjs_rec_well_formed_cache
      TE es m c g m' c' g' ics ilrs cs lrs :
  bit_blast_hbexps_hcache_conjs_rec
    TE m c g ics ilrs (mapr hash_bexp es) = (m', c', g', cs, lrs) ->
  well_formed_cache c -> well_formed_cache c'.
Proof.
  elim: es m c g m' c' g' ics ilrs cs lrs =>
  [| hd tl IH] im ic ig om oc og ics ilrs ocs olrs //=.
  - case=> ? ? ? ? ?; subst. by apply.
  - rewrite mapr_cons. rewrite bit_blast_hbexps_hcache_conjs_rec_rcons.
    dcase (bit_blast_hbexps_hcache_conjs_rec TE im ic ig ics ilrs (mapr hash_bexp tl))
    => [[[[[m1 c1] g1] cs1] lrs1] Hbb_tl].
    rewrite bit_blast_hbexps_hcache_conjs_rec_singleton.
    dcase (bit_blast_bexp_hcache TE m1 c1 g1 (hash_bexp hd)) =>
    [[[[[m2 c2] g2] cs2] lrs2] Hbb_hd]. case=> ? ? ? ? ?; subst.
    move=> Hwf_ic. move: (IH _ _ _ _ _ _ _ _ _ _ Hbb_tl Hwf_ic) => Hwf_c1.
    exact: (bit_blast_bexp_hcache_well_formed_cache Hwf_c1 Hbb_hd).
Qed.

Lemma bit_blast_hbexps_hcache_conjs_rec_cache_compatible
      TE es m c g m' c' g' ics ilrs cs lrs fc :
  bit_blast_hbexps_hcache_conjs_rec
    TE m c g ics ilrs (mapr hash_bexp es) = (m', c', g', cs, lrs) ->
  cache_compatible c fc -> exists fc', cache_compatible c' fc'.
Proof.
  elim: es m c g m' c' g' ics ilrs cs lrs fc =>
  [| hd tl IH] im ic ig om oc og ics ilrs ocs olrs fc //=.
  - case=> ? ? ? ? ?; subst. move=> Hcomp. exists fc. assumption.
  - rewrite mapr_cons. rewrite bit_blast_hbexps_hcache_conjs_rec_rcons.
    dcase (bit_blast_hbexps_hcache_conjs_rec TE im ic ig ics ilrs (mapr hash_bexp tl))
    => [[[[[m1 c1] g1] cs1] lrs1] Hbb_tl].
    rewrite bit_blast_hbexps_hcache_conjs_rec_singleton.
    dcase (bit_blast_bexp_hcache TE m1 c1 g1 (hash_bexp hd)) =>
    [[[[[m2 c2] g2] cs2] lrs2] Hbb_hd]. case=> ? ? ? ? ?; subst.
    move=> Hcomp. move: (IH _ _ _ _ _ _ _ _ _ _ _ Hbb_tl Hcomp) => [fc1 Hcomp_c1].
    exact: (bit_blast_bexp_hcache_cache_compatible Hcomp_c1 Hbb_hd).
Qed.

Lemma bit_blast_hbexps_hcache_conjs_rec_cache_compatible_chain
      TE es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc :
  bit_blast_hbexps_hcache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  well_formed_cache ihc ->
  cache_compatible ihc ifc ->
  CacheFlatten.cache_compatible ifc ic ->
  Cache.compatible ic icc ->
  exists ofc, exists oc, exists occ,
        cache_compatible ohc ofc
        /\ CacheFlatten.cache_compatible ofc oc
        /\ Cache.compatible oc occ.
Proof.
  elim: es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc =>
  [| hd tl IH] ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc //=.
  - case=> ? ? ? ? ?; subst. move=> ? ? ? ?.
    exists ifc. exists ic. exists icc. tauto.
  - rewrite mapr_cons. rewrite bit_blast_hbexps_hcache_conjs_rec_rcons.
    dcase (bit_blast_hbexps_hcache_conjs_rec
             TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp tl))
    => [[[[[hm1 hc1] hg1] hcs1] hlrs1] Hhbb_tl].
    rewrite bit_blast_hbexps_hcache_conjs_rec_singleton.
    dcase (bit_blast_bexp_hcache TE hm1 hc1 hg1 (hash_bexp hd)) =>
    [[[[[hm2 hc2] hg2] hcs2] hlrs2] Hhbb_hd]. case=> ? ? ? ? ?; subst.
    move=> Hwfihc Hccihc Hccifc Hccic.
    move: (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Hhbb_tl Hwfihc Hccihc Hccifc Hccic)
    => [fc1 [c1 [cc1 [Hcchc1 [Hccfc1 Hccc1]]]]].
    move: (bit_blast_hbexps_hcache_conjs_rec_well_formed_cache Hhbb_tl Hwfihc)
    => Hwfhc1.
    dcase (bit_blast_bexp_fcache TE hm1 fc1 hg1 hd) =>
    [[[[[fm2 fc2] fg2] fcs2] flrs2] Hfbb_hd].
    move: (bit_blast_bexp_hcache_fcache Hwfhc1 Hcchc1 Hhbb_hd Hfbb_hd)
    => [? [Hwfohc [Hccohc [? [? ?]]]]]; subst.
    dcase (bit_blast_bexp_cache TE hm1 c1 hg1 hd) =>
    [[[[[m2 c2] g2] cs2] lrs2] Hbb_hd]; subst.
    move: (bit_blast_bexp_fcache_valid Hccfc1 Hfbb_hd Hbb_hd)
    => [? [Hccfc2 [? [? ?]]]]; subst.
    move: (bit_blast_bexp_cache_is_bit_blast_bexp_ccache Hccc1 Hbb_hd)
    => [cc2 [Hcbb_hd Hccc2]].
    exists fc2. exists c2. exists cc2. tauto.
Qed.

Lemma bit_blast_hbexps_hcache_conjs_rec_cache_compatible_chain_wf_bound
      TE es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc :
  bit_blast_hbexps_hcache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  well_formed_cache ihc ->
  cache_compatible ihc ifc ->
  CacheFlatten.cache_compatible ifc ic ->
  Cache.compatible ic icc ->
  CompCache.well_formed icc ->
  CompCache.bound icc ihm ->
  exists ofc, exists oc, exists occ,
        cache_compatible ohc ofc
        /\ CacheFlatten.cache_compatible ofc oc
        /\ Cache.compatible oc occ
        /\ CompCache.well_formed occ
        /\ CompCache.bound occ ohm.
Proof.
  elim: es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc =>
  [| hd tl IH] ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc //=.
  - case=> ? ? ? ? ?; subst. move=> ? ? ? ? ? ?.
    exists ifc. exists ic. exists icc. tauto.
  - rewrite mapr_cons. rewrite bit_blast_hbexps_hcache_conjs_rec_rcons.
    dcase (bit_blast_hbexps_hcache_conjs_rec
             TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp tl))
    => [[[[[hm1 hc1] hg1] hcs1] hlrs1] Hhbb_tl].
    rewrite bit_blast_hbexps_hcache_conjs_rec_singleton.
    dcase (bit_blast_bexp_hcache TE hm1 hc1 hg1 (hash_bexp hd)) =>
    [[[[[hm2 hc2] hg2] hcs2] hlrs2] Hhbb_hd]. case=> ? ? ? ? ?; subst.
    move=> Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc.
    move: (IH _ _ _ _ _ _ _ _ _ _ _ _ _
              Hhbb_tl Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc)
    => [fc1 [c1 [cc1 [Hcchc1 [Hccfc1 [Hccc1 [Hwfcc1 Hboundcc1]]]]]]].
    move: (bit_blast_hbexps_hcache_conjs_rec_well_formed_cache Hhbb_tl Hwfihc)
    => Hwfhc1.
    dcase (bit_blast_bexp_fcache TE hm1 fc1 hg1 hd) =>
    [[[[[fm2 fc2] fg2] fcs2] flrs2] Hfbb_hd].
    move: (bit_blast_bexp_hcache_fcache Hwfhc1 Hcchc1 Hhbb_hd Hfbb_hd)
    => [? [Hwfohc [Hccohc [? [? ?]]]]]; subst.
    dcase (bit_blast_bexp_cache TE hm1 c1 hg1 hd) =>
    [[[[[m2 c2] g2] cs2] lrs2] Hbb_hd]; subst.
    move: (bit_blast_bexp_fcache_valid Hccfc1 Hfbb_hd Hbb_hd)
    => [? [Hccfc2 [? [? ?]]]]; subst.
    move: (bit_blast_bexp_cache_is_bit_blast_bexp_ccache Hccc1 Hbb_hd)
    => [cc2 [Hcbb_hd Hccc2]].
    move: (bit_blast_bexp_ccache_bound_cache Hcbb_hd Hwfcc1 Hboundcc1) =>
    [Hbbexpcc2 Hboundcc2].
    move: (bit_blast_bexp_ccache_well_formed Hcbb_hd Hwfcc1) => Hwfcc2.
    exists fc2. exists c2. exists cc2. tauto.
Qed.

Lemma bit_blast_hbexps_hcache_conjs_rec_preserve
      TE es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc :
  bit_blast_hbexps_hcache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  well_formed_cache ihc ->
  cache_compatible ihc ifc ->
  CacheFlatten.cache_compatible ifc ic ->
  Cache.compatible ic icc ->
  vm_preserve ihm ohm.
Proof.
  elim: es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc =>
  [| hd tl IH] ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc //=.
  - case=> ? ? ? ? ?; subst. move=> _ _ _ _. exact: vm_preserve_refl.
  - rewrite mapr_cons. rewrite bit_blast_hbexps_hcache_conjs_rec_rcons.
    dcase (bit_blast_hbexps_hcache_conjs_rec TE ihm ihc ihg ihcs ihlrs
                                             (mapr hash_bexp tl))
    => [[[[[hm1 hc1] hg1] hcs1] hlrs1] Hhbb_tl].
    rewrite bit_blast_hbexps_hcache_conjs_rec_singleton.
    dcase (bit_blast_bexp_hcache TE hm1 hc1 hg1 (hash_bexp hd)) =>
    [[[[[hm2 hc2] hg2] hcs2] hlrs2] Hhbb_hd]. case=> ? ? ? ? ?; subst.
    move=> Hwfihc Hccihc Hccifc Hccic.
    move: (IH _ _ _ _ _ _ _ _ _ _ _ _ _
              Hhbb_tl Hwfihc Hccihc Hccifc Hccic) => Hpre1.
    apply: (vm_preserve_trans Hpre1).

    move: (bit_blast_hbexps_hcache_conjs_rec_well_formed_cache Hhbb_tl Hwfihc)
    => Hwfhc1.
    move: (bit_blast_hbexps_hcache_conjs_rec_cache_compatible_chain
             Hhbb_tl Hwfihc Hccihc Hccifc Hccic)
    => [fc1 [c1 [cc1 [Hcchc1 [Hccfc1 Hccc1]]]]].
    exact: (bit_blast_bexp_hcache_preserve Hhbb_hd Hwfhc1 Hcchc1 Hccfc1 Hccc1).
Qed.

Lemma bit_blast_hbexps_hcache_conjs_rec_cache_compatible_full
      TE E es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc :
  bit_blast_hbexps_hcache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  QFBV.well_formed_bexps es TE ->
  well_formed_cache ihc ->
  cache_compatible ihc ifc ->
  CacheFlatten.cache_compatible ifc ic ->
  Cache.compatible ic icc ->
  CompCache.well_formed icc ->
  CompCache.bound icc ihm ->
  interp_cnf E (tflatten ohcs) ->
  CompCache.interp_cache_ct E icc ->
  CompCache.correct ihm icc ->
  exists ofc, exists oc, exists occ,
        cache_compatible ohc ofc
        /\ CacheFlatten.cache_compatible ofc oc
        /\ Cache.compatible oc occ
        /\ CompCache.well_formed occ
        /\ CompCache.bound occ ohm
        /\ CompCache.interp_cache_ct E occ
        /\ CompCache.correct ohm occ.
Proof.
  elim: es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc =>
  [| hd tl IH] ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc //=.
  - case=> ? ? ? ? ?; subst. move=> ? ? ? ? ? ? ? ? ?.
    exists ifc. exists ic. exists icc. tauto.
  - rewrite mapr_cons. rewrite bit_blast_hbexps_hcache_conjs_rec_rcons.
    dcase (bit_blast_hbexps_hcache_conjs_rec
             TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp tl))
    => [[[[[hm1 hc1] hg1] hcs1] hlrs1] Hhbb_tl].
    rewrite bit_blast_hbexps_hcache_conjs_rec_singleton.
    dcase (bit_blast_bexp_hcache TE hm1 hc1 hg1 (hash_bexp hd)) =>
    [[[[[hm2 hc2] hg2] hcs2] hlrs2] Hhbb_hd]. case=> ? ? ? ? ?; subst.
    move=> /andP [Hwf_hd Hwf_tl] Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc
            Hcs Hcticc Hcorrihm.
    rewrite interp_cnf_tflatten_catrev in Hcs. move/andP: Hcs => [Hhcs2 Hhcs1].

    move: (IH _ _ _ _ _ _ _ _ _ _ _ _ _
              Hhbb_tl Hwf_tl Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc
              Hhcs1 Hcticc Hcorrihm)
    => [fc1 [c1 [cc1
                   [Hcchc1 [Hccfc1 [Hccc1 [Hwfcc1 [Hboundcc1 [Hctcc1 Hcorrcc1]]]]]]]]].
    move: (bit_blast_hbexps_hcache_conjs_rec_well_formed_cache Hhbb_tl Hwfihc)
    => Hwfhc1.
    dcase (bit_blast_bexp_fcache TE hm1 fc1 hg1 hd) =>
    [[[[[fm2 fc2] fg2] fcs2] flrs2] Hfbb_hd].
    move: (bit_blast_bexp_hcache_fcache Hwfhc1 Hcchc1 Hhbb_hd Hfbb_hd)
    => [? [Hwfohc [Hccohc [? [? ?]]]]]; subst.
    dcase (bit_blast_bexp_cache TE hm1 c1 hg1 hd) =>
    [[[[[m2 c2] g2] cs2] lrs2] Hbb_hd]; subst.
    move: (bit_blast_bexp_fcache_valid Hccfc1 Hfbb_hd Hbb_hd)
    => [? [Hccfc2 [? [Heqs ?]]]]; subst.
    move: (bit_blast_bexp_cache_is_bit_blast_bexp_ccache Hccc1 Hbb_hd)
    => [cc2 [Hcbb_hd Hccc2]].
    move: (bit_blast_bexp_ccache_bound_cache Hcbb_hd Hwfcc1 Hboundcc1) =>
    [Hbbexpcc2 Hboundcc2].
    move: (bit_blast_bexp_ccache_well_formed Hcbb_hd Hwfcc1) => Hwfcc2.
    rewrite (Heqs E) in Hhcs2.
    move: (bit_blast_bexp_ccache_interp_cache_ct Hcbb_hd Hhcs2 Hctcc1) => Hctcc2.
    move: (bit_blast_hbexps_hcache_conjs_rec_preserve
             Hhbb_tl Hwfihc Hccihc Hccifc Hccic) => Hpreihm.
    move: (bit_blast_bexp_ccache_correct_cache
             Hcbb_hd Hwf_hd Hwfcc1 Hcorrcc1) => Hcorrcc2.
    move: (CompCache.vm_preserve_correct Hpreihm Hcorrihm).
    exists fc2. exists c2. exists cc2. tauto.
Qed.

Lemma bit_blast_hbexps_hcache_conjs_rec_bound
      TE es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc :
  bit_blast_hbexps_hcache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  well_formed_cache ihc ->
  cache_compatible ihc ifc ->
  CacheFlatten.cache_compatible ifc ic ->
  Cache.compatible ic icc ->
  CompCache.well_formed icc ->
  CompCache.bound icc ihm ->
  bound_bexps es ohm.
Proof.
  elim: es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc =>
  [| hd tl IH] ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc //=.
  rewrite mapr_cons. rewrite bit_blast_hbexps_hcache_conjs_rec_rcons.
  dcase (bit_blast_hbexps_hcache_conjs_rec TE ihm ihc ihg ihcs ihlrs
                                           (mapr hash_bexp tl))
  => [[[[[hm1 hc1] hg1] hcs1] hlrs1] Hhbb_tl].
  rewrite bit_blast_hbexps_hcache_conjs_rec_singleton.
  dcase (bit_blast_bexp_hcache TE hm1 hc1 hg1 (hash_bexp hd)) =>
  [[[[[hm2 hc2] hg2] hcs2] hlrs2] Hhbb_hd]. case=> ? ? ? ? ?; subst.
  move=> Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc.
  move: (IH _ _ _ _ _ _ _ _ _ _ _ _ _
            Hhbb_tl Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc) => Hbbexpstlhm1.

  move: (bit_blast_hbexps_hcache_conjs_rec_well_formed_cache Hhbb_tl Hwfihc)
  => Hwfhc1.
  move: (bit_blast_hbexps_hcache_conjs_rec_cache_compatible_chain_wf_bound
           Hhbb_tl Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc)
  => [fc1 [c1 [cc1 [Hcchc1 [Hccfc1 [Hccc1 [Hwfcc1 Hboundcc1]]]]]]].

  move: (bit_blast_bexp_hcache_preserve Hhbb_hd Hwfhc1 Hcchc1 Hccfc1 Hccc1) => Hprehm1.
  move: (vm_preserve_bound_bexps Hprehm1 Hbbexpstlhm1) => Hbbexpstlohm.
  rewrite Hbbexpstlohm andbT.

  exact: (bit_blast_bexp_hcache_bound
            Hhbb_hd Hwfhc1 Hcchc1 Hccfc1 Hccc1 Hwfcc1 Hboundcc1).
Qed.

Lemma bit_blast_hbexps_hcache_conjs_adhere
      TE es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc :
  bit_blast_hbexps_hcache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  well_formed_cache ihc ->
  cache_compatible ihc ifc ->
  CacheFlatten.cache_compatible ifc ic ->
  Cache.compatible ic icc ->
  adhere ihm TE ->
  adhere ohm TE.
Proof.
  elim: es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc =>
  [| hd tl IH] ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc //=.
  - case=> ? ? ? ? ?; subst. move=> _ _ _ _ ?; assumption.
  - rewrite mapr_cons. rewrite bit_blast_hbexps_hcache_conjs_rec_rcons.
    dcase (bit_blast_hbexps_hcache_conjs_rec TE ihm ihc ihg ihcs ihlrs
                                             (mapr hash_bexp tl))
    => [[[[[hm1 hc1] hg1] hcs1] hlrs1] Hhbb_tl].
    rewrite bit_blast_hbexps_hcache_conjs_rec_singleton.
    dcase (bit_blast_bexp_hcache TE hm1 hc1 hg1 (hash_bexp hd)) =>
    [[[[[hm2 hc2] hg2] hcs2] hlrs2] Hhbb_hd]. case=> ? ? ? ? ?; subst.
    move=> Hwfihc Hccihc Hccifc Hccic Hadihm.
    move: (IH _ _ _ _ _ _ _ _ _ _ _ _ _
              Hhbb_tl Hwfihc Hccihc Hccifc Hccic Hadihm) => Hadhm1.
    move: (bit_blast_hbexps_hcache_conjs_rec_well_formed_cache Hhbb_tl Hwfihc)
    => Hwfhc1.
    move: (bit_blast_hbexps_hcache_conjs_rec_cache_compatible_chain
             Hhbb_tl Hwfihc Hccihc Hccifc Hccic)
    => [fc1 [c1 [cc1 [Hcchc1 [Hccfc1 Hccc1]]]]].
    exact: (bit_blast_bexp_hcache_adhere
              Hhbb_hd Hwfhc1 Hcchc1 Hccfc1 Hccc1 Hadhm1).
Qed.

Lemma bit_blast_hbexps_hcache_conjs_rec_conform
      TE E es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc :
  bit_blast_hbexps_hcache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  well_formed_cache ihc ->
  cache_compatible ihc ifc ->
  CacheFlatten.cache_compatible ifc ic ->
  Cache.compatible ic icc ->
  CompCache.well_formed icc ->
  CompCache.bound icc ihm ->
  adhere ihm TE ->
  AdhereConform.conform_bexps es (mk_state E ohm) TE.
Proof.
  move=> Hhbb Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc Hadihm.
  apply: mk_state_conform_bexps.
  - exact: (bit_blast_hbexps_hcache_conjs_rec_bound
              Hhbb Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc).
  - exact: (bit_blast_hbexps_hcache_conjs_adhere
              Hhbb Hwfihc Hccihc Hccifc Hccic Hadihm).
Qed.

Lemma bit_blast_hbexps_hcache_conjs_conform
      TE E es ohm ohc ohg ohcs ohlrs :
  bit_blast_hbexps_hcache_conjs
    TE init_vm init_hcache init_gen (mapr hash_bexp es) =
  (ohm, ohc, ohg, ohcs, ohlrs) ->
  AdhereConform.conform_bexps es (mk_state E ohm) TE.
Proof.
  move=> Hbb.
  exact: (bit_blast_hbexps_hcache_conjs_rec_conform
            E Hbb init_hcache_well_formed init_hcache_fcache_compatible
            init_fcache_compatible init_compatible init_ccache_well_formed
            init_bound_cache (init_vm_adhere TE)).
Qed.



Fixpoint mk_conjs_rec res es :=
  match es with
  | [::] => res
  | hd::tl => mk_conjs_rec (QFBV.Bconj res hd) tl
  end.

Definition mk_conjs es :=
  match es with
  | [::] => QFBV.Btrue
  | hd::tl => mk_conjs_rec hd tl
  end.

Lemma mk_conjs_rec_rcons res es e :
  mk_conjs_rec res (rcons es e) = QFBV.Bconj (mk_conjs_rec res es) e.
Proof.
  by elim: es res e => [| hd tl IH] res e //=.
Qed.

Lemma mk_conjs_rcons es e :
  mk_conjs (rcons es e) = if es == [::] then e
                          else QFBV.Bconj (mk_conjs es) e.
Proof.
  case: es e => [| hd tl] e //=. rewrite mk_conjs_rec_rcons.
  reflexivity.
Qed.

Lemma mk_conjs_rec_eval s res es :
  QFBV.eval_bexp (mk_conjs_rec res es) s = QFBV.eval_bexp res s
                                           && (QFBV.eval_bexp (mk_conjs es) s).
Proof.
  move: es res. apply: last_ind => //=.
  - move=> res. rewrite andbT. reflexivity.
  - move=> es e IH res. rewrite mk_conjs_rec_rcons /=.
    rewrite {}IH. case: (QFBV.eval_bexp res s) => //=.
    rewrite mk_conjs_rcons /=. by case: es.
Qed.

Lemma mk_conjs_eval_cons s e es :
  QFBV.eval_bexp (mk_conjs (e::es)) s = QFBV.eval_bexp e s
                                        && (QFBV.eval_bexp (mk_conjs es) s).
Proof.
  rewrite /=. rewrite mk_conjs_rec_eval. reflexivity.
Qed.

Lemma mk_conjs_eval es s :
  QFBV.eval_bexp (mk_conjs es) s <-> forall e, e \in es -> QFBV.eval_bexp e s.
Proof.
  elim: es => [| hd tl IH] //=. rewrite mk_conjs_rec_eval. split.
  - move/andP=> [Hhd Htl]. move=> e Hin. rewrite in_cons in Hin.
    case/orP: Hin => Hin.
    + rewrite (eqP Hin). assumption.
    + exact: ((proj1 IH) Htl e Hin).
  - move=> H. rewrite (H hd (mem_head hd tl)) /=.
    apply: (proj2 IH). move=> e Hin; apply: H. rewrite in_cons Hin orbT.
    reflexivity.
Qed.

Lemma bound_bexps_rcons es e m :
  bound_bexps (rcons es e) m = (bound_bexps es m) && (bound_bexp e m).
Proof.
  elim: es e => [| hd tl IH] e //=.
  - rewrite andbT. reflexivity.
  - rewrite IH. rewrite Bool.andb_assoc. reflexivity.
Qed.

Lemma mk_conjs_rec_bound res es m :
  bound_bexp res m ->
  bound_bexps es m ->
  bound_bexp (mk_conjs_rec res es) m.
Proof.
  move: es res. apply: last_ind => //=. move=> es e IH res Hbb_res.
  rewrite bound_bexps_rcons. move/andP=> [Hbb_es Hbb_e].
  rewrite mk_conjs_rec_rcons /=. by rewrite (IH _ Hbb_res Hbb_es) Hbb_e.
Qed.

Lemma mk_conjs_bound es m :
  bound_bexps es m ->
  bound_bexp (mk_conjs es) m.
Proof.
  case: es => //=. move=> e es /andP [Hbb_e Hbb_es].
  exact: (mk_conjs_rec_bound Hbb_e Hbb_es).
Qed.

Lemma mk_conjs_rec_conform e es s E :
  conform_bexp (mk_conjs_rec e es) s E =
  conform_bexp e s E && conform_bexp (mk_conjs es) s E.
Proof.
  move: es e. apply: last_ind => /=.
  - move=> e. rewrite andbT. reflexivity.
  - move=> es le IH e. rewrite mk_conjs_rec_rcons /=. rewrite {}IH.
    case: (conform_bexp e s E) => //=. rewrite mk_conjs_rcons. by case: es.
Qed.

Lemma mk_conjs_conform es s E :
  conform_bexp (mk_conjs es) s E = conform_bexps es s E.
Proof.
  elim: es => [| e es IH] //=. rewrite mk_conjs_rec_conform IH. reflexivity.
Qed.

Lemma mk_conjs_rec_well_formed TE e es :
  QFBV.well_formed_bexp (mk_conjs_rec e es) TE =
  QFBV.well_formed_bexp e TE && QFBV.well_formed_bexps es TE.
Proof.
  move: es. apply: last_ind => /=.
  - rewrite andbT. reflexivity.
  - move=> es le IH. rewrite mk_conjs_rec_rcons /=. rewrite IH.
    rewrite QFBV.well_formed_bexps_rcons. rewrite andbA. reflexivity.
Qed.

Lemma mk_conjs_well_formed TE es :
  QFBV.well_formed_bexp (mk_conjs es) TE = QFBV.well_formed_bexps es TE.
Proof.
  case: es => [| e es] //=. rewrite mk_conjs_rec_well_formed. reflexivity.
Qed.



Definition size1 {A : Type} (s : seq A) :=
  size s == 1.

Lemma size1_singleton {A : Type} (s : seq A) :
  size1 s -> exists x, s = [:: x].
Proof. case: s => [| x1 s] //=. case: s => //=. move=> _. by exists x1. Qed.

Lemma interp_cnf_interp_word E cs :
  interp_cnf E cs ->
  all size1 cs ->
  interp_word E (tflatten cs) = ones (size cs).
Proof.
  elim: cs => [| c cs IH] //=. move/andP=> [Hc Hcs]. move/andP=> [Hsc Hscs].
  rewrite tflatten_cons. move: (size1_singleton Hsc) => [x Heq]; subst.
  rewrite /rev /=. rewrite cats1. rewrite interp_word_rcons.
  rewrite ones_cons. rewrite -ones_rcons. rewrite /= orbF in Hc.
  rewrite Hc. rewrite (IH Hcs Hscs). reflexivity.
Qed.

Lemma enc_bits_eval_conjs E s ohlrs es:
  interp_cnf E ohlrs ->
  all size1 ohlrs ->
  enc_bits E (tflatten ohlrs) (mapr (fun e => QFBV.eval_bexp e s) es) ->
  QFBV.eval_bexp (mk_conjs es) s.
Proof.
  move=> Hcs Hs. rewrite /enc_bits. rewrite (interp_cnf_interp_word Hcs Hs).
  clear Hcs Hs. elim: es ohlrs => [| e es IH] ohlrs //=.
  rewrite mapr_cons. case: ohlrs => [| lr ohlrs] //=.
  - move/eqP=> H. have Heq: size ([::] : cnf) =
                            size (rcons
                                    (mapr
                                       (QFBV.eval_bexp^~ s) es) (QFBV.eval_bexp e s))
    by rewrite -H. rewrite size_rcons in Heq. discriminate.
  - rewrite ones_cons -ones_rcons. rewrite mk_conjs_rec_eval.
    move/eqP=> H. move: (rcons_inj H) => {H} [] /eqP H1 H2.
    rewrite -H2 andTb. exact: (IH _ H1).
Qed.



Lemma bit_blast_hbexps_hcache_conjs_rec_enc_bits
      TE E es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc s ies :
  bit_blast_hbexps_hcache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  QFBV.well_formed_bexps es TE ->
  well_formed_cache ihc ->
  cache_compatible ihc ifc ->
  CacheFlatten.cache_compatible ifc ic ->
  Cache.compatible ic icc ->
  CompCache.well_formed icc ->
  CompCache.bound icc ihm ->
  adhere ihm TE ->
  interp_cnf E (add_prelude (tflatten (ohlrs :: ohcs))) ->
  CompCache.interp_cache_ct E icc ->
  CompCache.correct ihm icc ->
  AdhereConform.conform_bexps es s TE ->
  consistent ohm E s ->
  enc_bits E (tflatten ihlrs) (mapr (fun e => QFBV.eval_bexp e s) ies) ->
  enc_bits E (tflatten ohlrs) (mapr (fun e => QFBV.eval_bexp e s) (es ++ ies)).
Proof.
  elim: es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc =>
  [| hd tl IH] ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc //=.
  - case=> ? ? ? ? ?; subst. done.
  - rewrite mapr_cons. rewrite bit_blast_hbexps_hcache_conjs_rec_rcons.
    dcase (bit_blast_hbexps_hcache_conjs_rec TE ihm ihc ihg ihcs ihlrs
                                             (mapr hash_bexp tl))
    => [[[[[hm1 hc1] hg1] hcs1] hlrs1] Hhbb_tl].
    rewrite bit_blast_hbexps_hcache_conjs_rec_singleton.
    dcase (bit_blast_bexp_hcache TE hm1 hc1 hg1 (hash_bexp hd)) =>
    [[[[[hm2 hc2] hg2] hcs2] hlrs2] Hhbb_hd]. case=> ? ? ? ? ?; subst.
    move=> /andP [Hwf_hd Hwf_tl] Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc
          Hadihm Hsat Hcticc Hcorricc /andP [Hco_hd Hco_tl] Hcoohm Hencihlrs.
    move: (bit_blast_hbexps_hcache_conjs_rec_well_formed_cache Hhbb_tl Hwfihc)
    => Hwfhc1.

    rewrite interp_cnf_cons /= orbF in Hsat.
    move/andP: Hsat=> [Hsat_tt Hsat].
    rewrite interp_cnf_tflatten_cons in Hsat.
    move/andP: Hsat=> [Hsat1 Hsat2].
    rewrite interp_cnf_cons /= orbF in Hsat1.
    move/andP: Hsat1=> [Hsat_olr Hsat_hlrs1].
    rewrite interp_cnf_tflatten_catrev in Hsat2.
    move/andP: Hsat2=> [Hsat_ofcs Hsat_hcs1].

    move: (bit_blast_hbexps_hcache_conjs_rec_cache_compatible_full
             Hhbb_tl Hwf_tl Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc
             Hsat_hcs1 Hcticc Hcorricc)
    => [fc1 [c1 [cc1 [Hcchc1 [Hccfc1 [Hccc1 [Hwfcc1
                                               [Hboundcc1 [Hctcc1 Hcorrcc1]]]]]]]]].
    move: (bit_blast_hbexps_hcache_conjs_rec_bound
             Hhbb_tl Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc) => Hbbexp_tlhm1.
    move: (bit_blast_bexp_hcache_preserve Hhbb_hd Hwfhc1 Hcchc1 Hccfc1 Hccc1)
    => Hprehm1.
    move: (bit_blast_bexp_hcache_bound
             Hhbb_hd Hwfhc1 Hcchc1 Hccfc1 Hccc1 Hwfcc1 Hboundcc1)
    => Hbbexp_hdohm.

    dcase (bit_blast_bexp_fcache TE hm1 fc1 hg1 hd) =>
    [[[[[ofm ofc] ofg] ofcs] oflr] Hfbb_hd].
    move: (bit_blast_bexp_hcache_fcache Hwfhc1 Hcchc1 Hhbb_hd Hfbb_hd) =>
    [? [Hwfohc [Hccohc [? [? ?]]]]]; subst.
    dcase (bit_blast_bexp_cache TE hm1 c1 hg1 hd) =>
    [[[[[om oc] og] ocs] olr] Hbb_hd].
    move: (bit_blast_bexp_fcache_valid Hccfc1 Hfbb_hd Hbb_hd) =>
    [? [Hccofc [? [Heqs [Heqn ?]]]]]; subst.
    move: (bit_blast_bexp_cache_is_bit_blast_bexp_ccache Hccc1 Hbb_hd)
    => [cicc [Hcbb_hd Hccoc]].
    move: (bit_blast_hbexps_hcache_conjs_adhere
             Hhbb_tl Hwfihc Hccihc Hccifc Hccic Hadihm) => Hadhm1.
    move: (bit_blast_bexp_hcache_adhere
             Hhbb_hd Hwfhc1 Hcchc1 Hccfc1 Hccc1 Hadhm1) => Hadohm.

    rewrite (Heqs E) in Hsat_ofcs.

    move: (bit_blast_bexp_ccache_correct
             Hcbb_hd Hco_hd Hcoohm Hwf_hd Hwfcc1 (add_prelude_to Hsat_tt Hsat_ofcs)
             Hctcc1 Hcorrcc1) => Hencolr.

    rewrite tflatten_cons. rewrite {1}/rev /=. rewrite cats1.
    rewrite mapr_cons. rewrite enc_bits_rcons.
    rewrite Hencolr andbT.
    move: (vm_preserve_consistent Hprehm1 Hcoohm) => Hcohm1.
    apply: (IH _ _ _ _ _ _ _ _ _ _ _ _ _
               Hhbb_tl Hwf_tl Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc
               Hadihm _ Hcticc Hcorricc Hco_tl Hcohm1 Hencihlrs).
    rewrite add_prelude_expand interp_cnf_tflatten_cons /=.
    rewrite Hsat_tt /=. by rewrite Hsat_hlrs1 Hsat_hcs1.
Qed.

Lemma bit_blast_hbexps_hcache_conjs_enc_bits
      TE E es ohm ohc ohg ohcs ohlrs s :
  bit_blast_hbexps_hcache_conjs
    TE init_vm init_hcache init_gen
    (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  QFBV.well_formed_bexps es TE ->
  interp_cnf E (add_prelude (tflatten (ohlrs :: ohcs))) ->
  AdhereConform.conform_bexps es s TE ->
  consistent ohm E s ->
  enc_bits E (tflatten ohlrs) (mapr (fun e => QFBV.eval_bexp e s) es).
Proof.
  move=> Hbb Hwf_es Hcs Hco_es Hcoohm. rewrite -(cats0 es).
  apply: (bit_blast_hbexps_hcache_conjs_rec_enc_bits
            Hbb Hwf_es init_hcache_well_formed init_hcache_fcache_compatible
            init_fcache_compatible init_compatible init_ccache_well_formed
            init_bound_cache (init_vm_adhere TE) Hcs (init_interp_cache_ct E)
            (init_correct init_vm) Hco_es Hcoohm). done.
Qed.


Lemma bit_blast_hbexps_hcache_conjs_rec_eval_conjs
      TE E es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc s :
  bit_blast_hbexps_hcache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  QFBV.well_formed_bexps es TE ->
  well_formed_cache ihc ->
  cache_compatible ihc ifc ->
  CacheFlatten.cache_compatible ifc ic ->
  Cache.compatible ic icc ->
  CompCache.well_formed icc ->
  CompCache.bound icc ihm ->
  adhere ihm TE ->
  interp_cnf E (add_prelude (tflatten (ohlrs :: ohcs))) ->
  CompCache.interp_cache_ct E icc ->
  CompCache.correct ihm icc ->
  AdhereConform.conform_bexps es s TE ->
  consistent ohm E s ->
  QFBV.eval_bexp (mk_conjs es) s.
Proof.
  elim: es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc =>
  [| hd tl IH] ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc //=.
  rewrite mapr_cons. rewrite bit_blast_hbexps_hcache_conjs_rec_rcons.
  dcase (bit_blast_hbexps_hcache_conjs_rec TE ihm ihc ihg ihcs ihlrs
                                           (mapr hash_bexp tl))
  => [[[[[hm1 hc1] hg1] hcs1] hlrs1] Hhbb_tl].
  rewrite bit_blast_hbexps_hcache_conjs_rec_singleton.
  dcase (bit_blast_bexp_hcache TE hm1 hc1 hg1 (hash_bexp hd)) =>
  [[[[[hm2 hc2] hg2] hcs2] hlrs2] Hhbb_hd]. case=> ? ? ? ? ?; subst.
  move=> /andP [Hwf_hd Hwf_tl] Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc
          Hadihm Hsat Hcticc Hcorricc /andP [Hco_hd Hco_tl] Hcoohm.
  move: (bit_blast_hbexps_hcache_conjs_rec_well_formed_cache Hhbb_tl Hwfihc)
  => Hwfhc1.

  rewrite interp_cnf_cons /= orbF in Hsat.
  move/andP: Hsat=> [Hsat_tt Hsat].
  rewrite interp_cnf_tflatten_cons in Hsat.
  move/andP: Hsat=> [Hsat1 Hsat2].
  rewrite interp_cnf_cons /= orbF in Hsat1.
  move/andP: Hsat1=> [Hsat_olr Hsat_hlrs1].
  rewrite interp_cnf_tflatten_catrev in Hsat2.
  move/andP: Hsat2=> [Hsat_ofcs Hsat_hcs1].

  move: (bit_blast_hbexps_hcache_conjs_rec_cache_compatible_full
           Hhbb_tl Hwf_tl Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc
           Hsat_hcs1 Hcticc Hcorricc)
  => [fc1 [c1 [cc1 [Hcchc1 [Hccfc1 [Hccc1 [Hwfcc1 [Hboundcc1 [Hctcc1 Hcorrcc1]]]]]]]]].
  move: (bit_blast_hbexps_hcache_conjs_rec_bound
           Hhbb_tl Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc) => Hbbexp_tlhm1.
  move: (bit_blast_bexp_hcache_preserve Hhbb_hd Hwfhc1 Hcchc1 Hccfc1 Hccc1)
  => Hprehm1.
  move: (bit_blast_bexp_hcache_bound
           Hhbb_hd Hwfhc1 Hcchc1 Hccfc1 Hccc1 Hwfcc1 Hboundcc1)
  => Hbbexp_hdohm.

  rewrite mk_conjs_rec_eval. apply/andP; split.
  - dcase (bit_blast_bexp_fcache TE hm1 fc1 hg1 hd) =>
    [[[[[ofm ofc] ofg] ofcs] oflr] Hfbb_hd].
    move: (bit_blast_bexp_hcache_fcache Hwfhc1 Hcchc1 Hhbb_hd Hfbb_hd) =>
    [? [Hwfohc [Hccohc [? [? ?]]]]]; subst.
    dcase (bit_blast_bexp_cache TE hm1 c1 hg1 hd) =>
    [[[[[om oc] og] ocs] olr] Hbb_hd].
    move: (bit_blast_bexp_fcache_valid Hccfc1 Hfbb_hd Hbb_hd) =>
    [? [Hccofc [? [Heqs [Heqn ?]]]]]; subst.
    move: (bit_blast_bexp_cache_is_bit_blast_bexp_ccache Hccc1 Hbb_hd)
    => [cicc [Hcbb_hd Hccoc]].
    move: (bit_blast_hbexps_hcache_conjs_adhere
             Hhbb_tl Hwfihc Hccihc Hccifc Hccic Hadihm) => Hadhm1.
    move: (bit_blast_bexp_hcache_adhere
             Hhbb_hd Hwfhc1 Hcchc1 Hccfc1 Hccc1 Hadhm1) => Hadohm.

    rewrite (Heqs E) in Hsat_ofcs.

    move: (bit_blast_bexp_ccache_correct
             Hcbb_hd Hco_hd Hcoohm Hwf_hd Hwfcc1 (add_prelude_to Hsat_tt Hsat_ofcs)
             Hctcc1 Hcorrcc1).
    rewrite /enc_bit. rewrite Hsat_olr. rewrite eq_sym. by move/eqP=> ->.
  - move: (vm_preserve_consistent Hprehm1 Hcoohm) => Hcohm1.
    apply: (IH _ _ _ _ _ _ _ _ _ _ _ _ _
               Hhbb_tl Hwf_tl Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc
               Hadihm _ Hcticc Hcorricc Hco_tl Hcohm1).
    rewrite add_prelude_expand interp_cnf_tflatten_cons /=.
    rewrite Hsat_tt /=. by rewrite Hsat_hlrs1 Hsat_hcs1.
Qed.

Lemma bit_blast_hbexps_hcache_conjs_rec_mk_state
      TE E es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc ic icc :
  bit_blast_hbexps_hcache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  QFBV.well_formed_bexps es TE ->
  well_formed_cache ihc ->
  cache_compatible ihc ifc ->
  CacheFlatten.cache_compatible ifc ic ->
  Cache.compatible ic icc ->
  CompCache.well_formed icc ->
  CompCache.bound icc ihm ->
  adhere ihm TE ->
  interp_cnf E (add_prelude (tflatten (ohlrs :: ohcs))) ->
  CompCache.interp_cache_ct E icc ->
  CompCache.correct ihm icc ->
  QFBV.eval_bexp (mk_conjs es) (mk_state E ohm).
Proof.
  move=> Hbb Hwf_es Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc
             Hadihm Hcs Hcticc Hcorricc.
  apply: (bit_blast_hbexps_hcache_conjs_rec_eval_conjs
            Hbb Hwf_es Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc Hadihm
            Hcs Hcticc Hcorricc).
  - exact: (bit_blast_hbexps_hcache_conjs_rec_conform
              _ Hbb Hwfihc Hccihc Hccifc Hccic Hwficc Hboundicc Hadihm).
  - exact: mk_state_consistent.
Qed.

Lemma bit_blast_hbexps_hcache_conjs_mk_state
      TE E es ohm ohc ohg ohcs ohlrs :
  bit_blast_hbexps_hcache_conjs
    TE init_vm init_hcache init_gen
    (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  QFBV.well_formed_bexps es TE ->
  interp_cnf E (add_prelude (tflatten (ohlrs :: ohcs))) ->
  QFBV.eval_bexp (mk_conjs es) (mk_state E ohm).
Proof.
  rewrite /bit_blast_hbexps_hcache_conjs. move=> Hbb Hwf Hcs.
  exact: (bit_blast_hbexps_hcache_conjs_rec_mk_state
            Hbb Hwf init_hcache_well_formed init_hcache_fcache_compatible
            init_fcache_compatible init_compatible init_ccache_well_formed
            init_bound_cache (init_vm_adhere TE) Hcs
            (init_interp_cache_ct E) (init_correct init_vm)).
Qed.


(* Soundness of bit_blast_hbexps_hcache_conjs *)

Lemma bit_blast_hbexps_hcache_conjs_sat_sound TE es m c g cs lrs :
  bit_blast_hbexps_hcache_conjs
    TE init_vm init_hcache init_gen (mapr hash_bexp es) = (m, c, g, cs, lrs) ->
  QFBV.well_formed_bexps es TE ->
  (sat (add_prelude (tflatten (lrs::cs)))) ->
  (exists s, AdhereConform.conform_bexps es s TE /\
             QFBV.eval_bexp (mk_conjs es) s).
Proof.
  move=> Hhbb Hwf [E Hcs]. exists (mk_state E m). split.
  - exact: (bit_blast_hbexps_hcache_conjs_conform _ Hhbb).
  - exact: (bit_blast_hbexps_hcache_conjs_mk_state Hhbb Hwf Hcs).
Qed.



Definition bit_blast_bexps_hcache_conjs TE es : vm * cache * generator * cnf :=
  let '(m', c', g', cs, lrs) :=
      bit_blast_hbexps_hcache_conjs
        TE init_vm init_hcache init_gen (mapr hash_bexp es) in
  (m', c', g', add_prelude (tflatten (lrs::cs))).

Theorem bit_blast_bexps_hcache_conjs_sat_sound TE es :
  let '(m, c, g, cs) := bit_blast_bexps_hcache_conjs TE es in
  QFBV.well_formed_bexps es TE ->
  sat cs ->
  (exists s, AdhereConform.conform_bexps es s TE /\
             QFBV.eval_bexp (mk_conjs es) s).
Proof.
  rewrite /bit_blast_bexps_hcache_conjs.
  dcase (bit_blast_hbexps_hcache_conjs
           TE init_vm init_hcache init_gen
           (mapr hash_bexp es)) => [[[[[m c] g] cs] lrs] Hbb].
  move=> Hwf Hsat. exact: (bit_blast_hbexps_hcache_conjs_sat_sound Hbb Hwf Hsat).
Qed.


(**)

Lemma init_hcache_hccache_compatible :
  compatible init_hcache init_hccache.
Proof. done. Qed.

Ltac dcase_bb_base :=
  match goal with
  | |- context f [bit_blast_var ?E ?g ?v] =>
    let g' := fresh in
    let cs := fresh in
    let lrs := fresh in
    let H := fresh in
    dcase (bit_blast_var E g v) => [[[g' cs] lrs] H]
  | |- context f [bit_blast_eunop ?op ?g ?lrs] =>
    let g' := fresh in
    let cs' := fresh in
    let lrs' := fresh in
    let H := fresh in
    dcase (bit_blast_eunop op g lrs) => [[[g' cs'] lrs'] H]
  | |- context f [bit_blast_ebinop ?op ?g ?lrs1 ?lrs2] =>
    let g' := fresh in
    let cs' := fresh in
    let lrs' := fresh in
    let H := fresh in
    dcase (bit_blast_ebinop op g lrs1 lrs2) => [[[g' cs'] lrs'] H]
  | |- context f [bit_blast_ite ?g ?lr ?ls1 ?ls2] =>
    let g' := fresh in
    let cs' := fresh in
    let lr' := fresh in
    let H := fresh in
    dcase (bit_blast_ite g lr ls1 ls2) => [[[g' cs'] lr'] H]
  | |- context f [bit_blast_bbinop ?op ?g ?lrs1 ?lrs2] =>
    let g' := fresh in
    let cs' := fresh in
    let lr' := fresh in
    let H := fresh in
    dcase (bit_blast_bbinop op g lrs1 lrs2) => [[[g' cs'] lr'] H]
  end.

Ltac dcase_bb_cache :=
  match goal with
  (**)
  | |- context f [find_cet ?e ?c] =>
    let Hfe_cet := fresh in
    let lrs := fresh in
    dcase (find_cet e c); case=> [lrs|] Hfe_cet
  | |- context f [find_cbt ?e ?c] =>
    let Hfe_cbt := fresh in
    let lr := fresh in
    dcase (find_cbt e c); case=> [lr|] Hfe_cbt
  | |- context f [find_het ?e ?c] =>
    let Hfe_het := fresh in
    let cs := fresh in
    let lrs := fresh in
    dcase (find_het e c); case=> [[cs lrs]|] Hfe_het
  | |- context f [find_hbt ?e ?c] =>
    let Hfe_hbt := fresh in
    let cs := fresh in
    let lr := fresh in
    dcase (find_hbt e c); case=> [[cs lr]|] Hfe_hbt
  (**)
  | |- context f [SSAVM.find ?v ?m] =>
    let lrs := fresh in
    case: (SSAVM.find v m) => [lrs|]
  | |- context f [bit_blast_exp_hcache ?E ?m ?ec ?g ?e] =>
    let m' := fresh in
    let ec' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lrs := fresh in
    let H := fresh in
    dcase (bit_blast_exp_hcache E m ec g e) =>
    [[[[[m' ec'] g'] cs] lrs] H]
  | |- context f [bit_blast_bexp_hcache ?E ?m ?ec ?g ?e] =>
    let m' := fresh in
    let ec' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lr := fresh in
    let H := fresh in
    dcase (bit_blast_bexp_hcache E m ec g e) =>
    [[[[[m' ec'] g'] cs] lr] H]
  | |- context f [bit_blast_exp_fcache ?E ?m ?c ?g ?e] =>
    let m' := fresh in
    let c' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lrs := fresh in
    let H := fresh in
    dcase (bit_blast_exp_fcache E m c g e) =>
    [[[[[m' c'] g'] cs] lrs] H]
  | |- context f [bit_blast_bexp_fcache ?E ?m ?c ?g ?e] =>
    let m' := fresh in
    let c' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lr := fresh in
    let H := fresh in
    dcase (bit_blast_bexp_fcache E m c g e) =>
    [[[[[m' c'] g'] cs] lr] H]
  (**)
  | |- _ => dcase_bb_base
  end.

Ltac dcase_bb_ccache :=
  match goal with
  | |- context f [find_cet ?e ?c] =>
    let Hfe_cet := fresh in
    let cs := fresh in
    let lrs := fresh in
    dcase (find_cet e c); case=> [[cs lrs]|] Hfe_cet
  | |- context f [find_cbt ?e ?c] =>
    let Hfe_cbt := fresh in
    let cs := fresh in
    let lr := fresh in
    dcase (find_cbt e c); case=> [[cs lr]|] Hfe_cbt
  | |- context f [find_het ?e ?c] =>
    let Hfe_het := fresh in
    let cs := fresh in
    let lrs := fresh in
    dcase (find_het e c); case=> [[cs lrs]|] Hfe_het
  | |- context f [find_hbt ?e ?c] =>
    let Hfe_hbt := fresh in
    let cs := fresh in
    let lr := fresh in
    dcase (find_hbt e c); case=> [[cs lr]|] Hfe_hbt
  (**)
  | |- context f [SSAVM.find ?v ?m] =>
    let lrs := fresh in
    case: (SSAVM.find v m) => [lrs|]
  | |- context f [bit_blast_exp_hccache ?E ?m ?ec ?g ?e] =>
    let m' := fresh in
    let ec' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lrs := fresh in
    let H := fresh in
    dcase (bit_blast_exp_hccache E m ec g e) =>
    [[[[[m' ec'] g'] cs] lrs] H]
  | |- context f [bit_blast_bexp_hccache ?E ?m ?ec ?g ?e] =>
    let m' := fresh in
    let ec' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lr := fresh in
    let H := fresh in
    dcase (bit_blast_bexp_hccache E m ec g e) =>
    [[[[[m' ec'] g'] cs] lr] H]
  | |- context f [bit_blast_exp_fccache ?E ?m ?c ?g ?e] =>
    let m' := fresh in
    let c' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lrs := fresh in
    let H := fresh in
    dcase (bit_blast_exp_fccache E m c g e) =>
    [[[[[m' c'] g'] cs] lrs] H]
  | |- context f [bit_blast_bexp_fccache ?E ?m ?c ?g ?e] =>
    let m' := fresh in
    let c' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lr := fresh in
    let H := fresh in
    dcase (bit_blast_bexp_fccache E m c g e) =>
    [[[[[m' c'] g'] cs] lr] H]
  (**)
  | |- _ => dcase_bb_base
  end.

Ltac myauto ::=
  repeat
    match goal with
    | |- _ /\ _ => split
    | |- ?e = ?e => reflexivity
    | H : ?p |- ?p => assumption
    | |- (_, _, _, _, _, _) = (_, _, _, _, _, _) -> _ =>
      case=> ? ? ? ? ? ?; subst
    | |- (_, _, _, _, _) = (_, _, _, _, _) -> _ =>
      case=> ? ? ? ? ?; subst
    | H1 : ?e = Some _, H2 : ?e = None |- _ =>
      rewrite H1 in H2; discriminate
    (**)
    | Hc : compatible ?oc ?cc,
      Hf : find_cet ?e ?oc = Some _
      |- context [CCacheHash.find_cet ?e ?cc] =>
      let cs := fresh in
      let H := fresh in
      (move: (CacheHash.compatible_find_cet_some Hc Hf) => [cs H]);
      rewrite H; clear Hf
    | Hc : compatible ?oc ?cc,
      Hf : find_cet ?e ?oc = None
      |- context [CCacheHash.find_cet ?e ?cc] =>
      let H := fresh in
      (move: (CacheHash.compatible_find_cet_none Hc Hf) => H);
      rewrite H; clear Hf
    | Hc : compatible ?oc ?cc,
      Hf : find_cbt ?e ?oc = Some _
      |- context [CCacheHash.find_cbt ?e ?cc] =>
      let cs := fresh in
      let H := fresh in
      (move: (CacheHash.compatible_find_cbt_some Hc Hf) => [cs H]);
      rewrite H; clear Hf
    | Hc : compatible ?oc ?cc,
      Hf : find_cbt ?e ?oc = None
      |- context [CCacheHash.find_cbt ?e ?cc] =>
      let H := fresh in
      (move: (CacheHash.compatible_find_cbt_none Hc Hf) => H);
      rewrite H; clear Hf
    | Hc : compatible ?oc ?cc |- context [CCacheHash.find_het ?e ?cc] =>
      rewrite -(compatible_find_het e Hc)
    | Hc : compatible ?oc ?cc |- context [CCacheHash.find_hbt ?e ?cc] =>
      rewrite -(compatible_find_hbt e Hc)
    (**)
    | Hf : find_cet ?e ?oc = _ |- context [find_cet ?e ?oc] => rewrite Hf
    | Hf : find_cbt ?e ?oc = _ |- context [find_cbt ?e ?oc] => rewrite Hf
    | Hf : find_het ?e ?oc = _ |- context [find_het ?e ?oc] => rewrite Hf
    | Hf : find_hbt ?e ?oc = _ |- context [find_hbt ?e ?oc] => rewrite Hf
    (* apply induction hypothesis *)
    | bit_blast_exp_hcache_is_bit_blast_exp_hccache :
        (forall (TE : SSATE.env)
                (m : vm) (c : cache)
                (cc : CCacheHash.ccache)
                (g : generator) (e : hexp)
                (om : vm) (oc : cache)
                (og : generator)
                (ocs : seq cnf) (olrs : word),
            compatible c cc ->
            bit_blast_exp_hcache TE m c g e =
            (om, oc, og, ocs, olrs) ->
            exists occ : CCacheHash.ccache,
              bit_blast_exp_hccache TE m cc g e =
              (om, occ, og, ocs, olrs) /\
              compatible oc occ),
        Hc : compatible ?c ?cc,
        Hbb : bit_blast_exp_hcache ?TE ?m ?c ?g ?e = _ |- _ =>
      let occ := fresh in
      let Hcbb := fresh in
      let Hcc := fresh in
      move: (bit_blast_exp_hcache_is_bit_blast_exp_hccache
               _ _ _ _ _ _ _ _ _ _ _ Hc Hbb) => [occ [Hcbb Hcc]]; clear Hbb
    | bit_blast_bexp_hcache_is_bit_blast_bexp_hccache :
        (forall (TE : SSATE.env)
                (m : vm) (c : cache)
                (cc : CCacheHash.ccache)
                (g : generator)
                (e : hbexp) (om : vm)
                (oc : cache) (og : generator)
                (ocs : seq cnf)
                (olrs : literal),
            compatible c cc ->
            bit_blast_bexp_hcache TE m c g e =
            (om, oc, og, ocs, olrs) ->
            exists occ : CCacheHash.ccache,
              bit_blast_bexp_hccache TE m cc g e =
              (om, occ, og, ocs, olrs) /\
              compatible oc occ),
        Hc : compatible ?c ?cc,
        Hbb : bit_blast_bexp_hcache ?TE ?m ?c ?g ?e = _ |- _ =>
      let occ := fresh in
      let Hcbb := fresh in
      let Hcc := fresh in
      move: (bit_blast_bexp_hcache_is_bit_blast_bexp_hccache
               _ _ _ _ _ _ _ _ _ _ _ Hc Hbb) => [occ [Hcbb Hcc]]; clear Hbb
    (**)
    | H1 : bit_blast_eunop ?op ?g ?ls = _,
      H2 : bit_blast_eunop ?op ?g ?ls = _ |- _ =>
      (rewrite H1 in H2); case: H2 => ? ? ?; subst
    | H1 : bit_blast_ebinop ?op ?g ?ls1 ?ls2 = _,
      H2 : bit_blast_ebinop ?op ?g ?ls1 ?ls2 = _ |- _ =>
      (rewrite H1 in H2); case: H2 => ? ? ?; subst
    | H1 : bit_blast_ite ?g ?c ?ls1 ?ls2 = _,
      H2 : bit_blast_ite ?g ?c ?ls1 ?ls2 = _ |- _ =>
      (rewrite H1 in H2); case: H2 => ? ? ?; subst
    | H1 : bit_blast_exp_hccache ?TE ?m ?cc ?g ?e = _,
      H2 : bit_blast_exp_hccache ?TE ?m ?cc ?g ?e = _ |- _ =>
      (rewrite H1 in H2); case: H2 => ? ? ? ? ?; subst
    | H1 : bit_blast_bexp_hccache ?TE ?m ?cc ?g ?e = _,
      H2 : bit_blast_bexp_hccache ?TE ?m ?cc ?g ?e = _ |- _ =>
      (rewrite H1 in H2); case: H2 => ? ? ? ? ?; subst
    | H1 : bit_blast_bbinop ?op ?g ?ls1 ?ls2 = _,
      H2 : bit_blast_bbinop ?op ?g ?ls1 ?ls2 = _ |- _ =>
      (rewrite H1 in H2); case: H2 => ? ? ?; subst
    (**)
    | |- exists occ : CCacheHash.ccache,
        (?om, ?cc, ?og, ?ocs, ?olrs) = (?om, occ, ?og, ?ocs, ?olrs) /\ compatible _ occ =>
      exists cc; (split; first try done)
    | |- compatible (add_cet ?e ?olrs ?c) (CCacheHash.add_cet ?e ?ocs ?olrs ?cc) =>
      apply: compatible_add_cet
    | |- compatible (add_cbt ?e ?olr ?c) (CCacheHash.add_cbt ?e ?ocs ?olrb ?cc) =>
      apply: compatible_add_cbt
    | |- compatible (add_het ?e ?ocs ?olrs ?c) (CCacheHash.add_het ?e ?ocs ?olrs ?cc) =>
      apply: compatible_add_het
    | |- compatible (add_hbt ?e ?ocs ?olr ?c) (CCacheHash.add_hbt ?e ?ocs ?olr ?cc) =>
      apply: compatible_add_hbt
    (**)
    | |- _ => dcase_bb_cache || dcase_bb_ccache
    end.

Lemma bit_blast_exp_hcache_is_bit_blast_exp_hccache
      TE m c cc g e om oc og ocs olrs :
  CacheHash.compatible c cc ->
  bit_blast_exp_hcache TE m c g e = (om, oc, og, ocs, olrs) ->
  exists occ,
    bit_blast_exp_hccache TE m cc g e = (om, occ, og, ocs, olrs)
    /\ CacheHash.compatible oc occ
with
  bit_blast_bexp_hcache_is_bit_blast_bexp_hccache
      TE m c cc g e om oc og ocs olrs :
  CacheHash.compatible c cc ->
  bit_blast_bexp_hcache TE m c g e = (om, oc, og, ocs, olrs) ->
  exists occ,
    bit_blast_bexp_hccache TE m cc g e = (om, occ, og, ocs, olrs)
    /\ CacheHash.compatible oc occ.
Proof.
  (* bit_blast_exp_hcache_is_bit_blast_exp_hccache *)
  case: e. case=> //=.
  - move=> v z Hcc. by myauto.
  - move=> bs z Hcc. by myauto.
  - move=> op e z Hcc. by myauto.
  - move=> op e1 e2 z Hcc. by myauto.
  - move=> e1 e2 e3 z Hcc. by myauto.
  (* bit_blast_bexp_hcache_is_bit_blast_bexp_hccache *)
  case: e. case=> //=.
  - move=> z Hcc. by myauto.
  - move=> z Hcc. by myauto.
  - move=> op e1 e2 z Hcc. by myauto.
  - move=> e z Hcc. by myauto.
  - move=> e1 e2 z Hcc. by myauto.
  - move=> e1 e2 z Hcc. by myauto.
Qed.

Lemma bit_blast_hbexps_hcache_conjs_rec_is_bit_blast_hbexps_hccache_conjs_rec
      TE m c cc g rcs rlrs es om oc og ocs olrs :
  CacheHash.compatible c cc ->
  bit_blast_hbexps_hcache_conjs_rec TE m c g rcs rlrs es = (om, oc, og, ocs, olrs) ->
  exists occ,
    bit_blast_hbexps_hccache_conjs_rec TE m cc g rcs rlrs es = (om, occ, og, ocs, olrs)
    /\ CacheHash.compatible oc occ.
Proof.
  elim: es m c cc g rcs rlrs om oc og ocs olrs
  => [| e es IH] //= im ic icc ig ircs irlrs om oc og ocs olrs Hcc.
  - case=> ? ? ? ? ?; subst. exists icc. done.
  - dcase (bit_blast_bexp_hcache TE im ic ig e) => [[[[[m1 c1] g1] cs1] lrs1] Hbb1] Hbb2.
    move: (bit_blast_bexp_hcache_is_bit_blast_bexp_hccache Hcc Hbb1) => [cc1 [Hcbb1 Hcc1]].
    move: (IH _ _ _ _ _ _ _ _ _ _ _ Hcc1 Hbb2) => [cc2 [Hcbb2 Hcc2]].
    exists cc2. rewrite Hcbb1 Hcbb2. done.
Qed.

Lemma bit_blast_hbexps_hcache_conjs_is_bit_blast_hbexps_hccache_conjs
      TE m c cc g es om oc og ocs olrs :
  CacheHash.compatible c cc ->
  bit_blast_hbexps_hcache_conjs TE m c g es = (om, oc, og, ocs, olrs) ->
  exists occ,
    bit_blast_hbexps_hccache_conjs TE m cc g es = (om, occ, og, ocs, olrs)
    /\ CacheHash.compatible oc occ.
Proof. exact: bit_blast_hbexps_hcache_conjs_rec_is_bit_blast_hbexps_hccache_conjs_rec. Qed.



(* Completeness of bit_blast_hbexps_hcache_conjs *)


Lemma bit_blast_hbexps_hcache_conjs_sat_complete TE es m c g cs lrs :
  bit_blast_hbexps_hcache_conjs
    TE init_vm init_hcache init_gen (mapr hash_bexp es) = (m, c, g, cs, lrs) ->
  QFBV.well_formed_bexps es TE ->
  (exists s, AdhereConform.conform_bexps es s TE /\
             QFBV.eval_bexp (mk_conjs es) s) ->
  (sat (add_prelude (tflatten (lrs::cs)))).
Proof.
  move=> Hbb Hwf Hev.
  move: (bit_blast_hbexps_hcache_conjs_is_bit_blast_hbexps_hccache_conjs
           init_hcache_hccache_compatible Hbb) => [occ [Hcbb Hcocc]].
  exact: (bit_blast_hbexps_hccache_conjs_sat_complete Hcbb Hwf Hev).
Qed.

Theorem bit_blast_bexps_hcache_conjs_sat_complete TE es :
  let '(m, c, g, cs) := bit_blast_bexps_hcache_conjs TE es in
  QFBV.well_formed_bexps es TE ->
  (exists s, AdhereConform.conform_bexps es s TE /\
             QFBV.eval_bexp (mk_conjs es) s) ->
  sat cs.
Proof.
  rewrite /bit_blast_bexps_hcache_conjs.
  dcase (bit_blast_hbexps_hcache_conjs
           TE init_vm init_hcache init_gen
           (mapr hash_bexp es)) => [[[[[m c] g] cs] lrs] Hbb].
  move=> Hwf Hev. exact: (bit_blast_hbexps_hcache_conjs_sat_complete Hbb Hwf Hev).
Qed.


(* agree *)

Lemma agree_bit_blast_exp_hcache E1 E2 m c g (e : hexp) :
  QFBV.MA.agree (QFBV.vars_exp e) E1 E2 ->
  bit_blast_exp_hcache E1 m c g e =
    bit_blast_exp_hcache E2 m c g e
with agree_bit_blast_bexp_hcache E1 E2 m c g (e : hbexp) :
  QFBV.MA.agree (QFBV.vars_bexp e) E1 E2 ->
  bit_blast_bexp_hcache E1 m c g e =
    bit_blast_bexp_hcache E2 m c g e.
Proof.
  - (* agree_bit_blast_exp_hcache *)
    case: e. case; simpl.
    + move=> v z Hag. rewrite (agree_bit_blast_var _ Hag). reflexivity.
    + reflexivity.
    + move=> op e z Hag. rewrite (agree_bit_blast_exp_hcache _ _ _ _ _ _ Hag).
      reflexivity.
    + move=> op e1 e2 z Hag.
      rewrite (agree_bit_blast_exp_hcache _ _ _ _ _ _ (QFBV.MA.agree_union_set_l Hag)).
      dcase (bit_blast_exp_hcache E2 m c g e1) => [[[[[m1 c1] g1] cs1] ls1] Hbb1].
      rewrite (agree_bit_blast_exp_hcache _ _ _ _ _ _ (QFBV.MA.agree_union_set_r Hag)).
      reflexivity.
    + move=> b e1 e2 z Hag.
      rewrite (agree_bit_blast_bexp_hcache _ _ _ _ _ _ (QFBV.MA.agree_union_set_l Hag)).
      move: (QFBV.MA.agree_union_set_r Hag) => {} Hag.
      dcase (bit_blast_bexp_hcache E2 m c g b) => [[[[[mb cb] gb] csb] lsb] Hbbb].
      rewrite (agree_bit_blast_exp_hcache _ _ _ _ _ _ (QFBV.MA.agree_union_set_l Hag)).
      dcase (bit_blast_exp_hcache E2 mb cb gb e1) => [[[[[m1 c1] g1] cs1] ls1] Hbb1].
      rewrite (agree_bit_blast_exp_hcache _ _ _ _ _ _ (QFBV.MA.agree_union_set_r Hag)).
      reflexivity.
  - (* agree_bit_blast_bexp_hcache *)
    case: e. case; simpl.
    + reflexivity.
    + reflexivity.
    + move=> op e1 e2 n Hag.
      rewrite (agree_bit_blast_exp_hcache _ _ _ _ _ _ (QFBV.MA.agree_union_set_l Hag)).
      dcase (bit_blast_exp_hcache E2 m c g e1) => [[[[[m1 c1] g1] cs1] ls1] Hbb1].
      rewrite (agree_bit_blast_exp_hcache _ _ _ _ _ _ (QFBV.MA.agree_union_set_r Hag)).
      reflexivity.
    + move=> e n Hag. rewrite (agree_bit_blast_bexp_hcache _ _ _ _ _ _ Hag).
      reflexivity.
    + move=> e1 e2 n Hag.
      rewrite (agree_bit_blast_bexp_hcache _ _ _ _ _ _ (QFBV.MA.agree_union_set_l Hag)).
      dcase (bit_blast_bexp_hcache E2 m c g e1) => [[[[[m1 c1] g1] cs1] ls1] Hbb1].
      rewrite (agree_bit_blast_bexp_hcache _ _ _ _ _ _ (QFBV.MA.agree_union_set_r Hag)).
      reflexivity.
    + move=> e1 e2 n Hag.
      rewrite (agree_bit_blast_bexp_hcache _ _ _ _ _ _ (QFBV.MA.agree_union_set_l Hag)).
      dcase (bit_blast_bexp_hcache E2 m c g e1) => [[[[[m1 c1] g1] cs1] ls1] Hbb1].
      rewrite (agree_bit_blast_bexp_hcache _ _ _ _ _ _ (QFBV.MA.agree_union_set_r Hag)).
      reflexivity.
Qed.

Lemma agree_bit_blast_bexp_hcache_tflatten E1 E2 m c g (e : hbexp) :
  QFBV.MA.agree (QFBV.vars_bexp e) E1 E2 ->
  bit_blast_bexp_hcache_tflatten E1 m c g e =
    bit_blast_bexp_hcache_tflatten E2 m c g e.
Proof.
  rewrite /bit_blast_bexp_hcache_tflatten => Hag.
  rewrite (agree_bit_blast_bexp_hcache _ _ _ Hag).
  reflexivity.
Qed.
