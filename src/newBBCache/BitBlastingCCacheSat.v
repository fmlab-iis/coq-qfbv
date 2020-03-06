From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
(* From BBCache Require Import Cache BitBlastingCacheDef BitBlastingCacheWF  *)
(*      BitBlastingCacheNewer BitBlastingCachePreserve. *)
From newBBCache Require Import CompCache BitBlastingCCacheDef 
     BitBlastingCCacheWF BitBlastingCCacheNewer BitBlastingCCachePreserve.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* = mk_env_exp_ccache_interp_cache and mk_env_bexp_ccache_interp_cache = *)

Lemma mk_env_exp_ccache_interp_cache_nocet_var :
  forall (t : SSAVarOrder.t) (m : vm) (c : compcache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (c' : compcache) 
         (E' : env) (g' : generator) (cs : cnf) (ls : word),
    find_cet (QFBV.Evar t) c = None ->
    mk_env_exp_ccache m c s E g (QFBV.Evar t) = (m', c', E', g', cs, ls) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    well_formed c ->
    newer_than_cache g c -> interp_cache E c -> 
    interp_cnf E' cs /\ interp_cache E' c'.
Proof.
  move=> v m c s E g m' c' E' g' cs ls Hfcet.
  rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Evar v) c) => [[cse lse] | ].
  - case=> _ <- <- _ <- _. move=> Hgm Hgtt Hwfc Hgc HiEc.
    have HiEcse : interp_cnf E cse by apply (interp_cache_find_het HiEc Hfhet).
    split; [ done | by apply interp_cache_add_cet ].
  - case Hfind: (SSAVM.find v m).
    + case=> _ <- <- _ <- _. move=> Hgm Hgtt Hwfc Hgc HiEc.
      split; [ done | by apply interp_cache_add_cet, interp_cache_add_het].
    + case Henv: (mk_env_var E g (SSAStore.acc v s) v) => [[[Ev gv] csv] lsv].
      case=> _ <- <- _ <- _. move=> Hgm Hgtt Hwfc Hgc HiEc. 
      have HiEvcsv : interp_cnf Ev csv by apply (mk_env_var_sat Henv).
      split.
      * done.
      * apply interp_cache_add_cet, interp_cache_add_het; try done.
        move: (mk_env_var_preserve Henv) => HpEEvg.
        by rewrite (env_preserve_interp_cache HpEEvg Hgc).
Qed.

Lemma mk_env_exp_ccache_interp_cache_nocet_const :
  forall (b : bits) (m : vm) (c : compcache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (c' : compcache) 
         (E' : env) (g' : generator) (cs : cnf) (ls : word),
    find_cet (QFBV.Econst b) c = None ->
    mk_env_exp_ccache m c s E g (QFBV.Econst b) = (m', c', E', g', cs, ls) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    well_formed c ->
    newer_than_cache g c -> interp_cache E c -> 
    interp_cnf E' cs /\ interp_cache E' c'.
Proof.
  move=> bs m c s E g m' c' E' g' cs ls Hfcet.
  rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Econst bs) c) => [[cse lse] | ].
  - case=> _ <- <- _ <- _. move=> Hgm Hgtt Hwfc Hgc HiEc.
    have HiEcse : interp_cnf E cse by apply (interp_cache_find_het HiEc Hfhet).
    split; [ done | by apply interp_cache_add_cet ].
  - case=> _ <- <- _ <- _. move=> Hgm Hgtt Hwfc Hgc HiEc.
    split; [ done | by apply interp_cache_add_cet, interp_cache_add_het].
Qed.

Lemma mk_env_exp_ccache_interp_cache_nocet_unop :
  forall (op : QFBV.eunop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c ->
        interp_cache E c -> interp_cnf E' cs /\ interp_cache E' c') ->
    forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
           (g : generator) (m' : vm) (c' : compcache) (E' : env) 
           (g' : generator) (cs : cnf) (ls : word),
      find_cet (QFBV.Eunop op e1) c = None ->
      mk_env_exp_ccache m c s E g (QFBV.Eunop op e1) = (m', c', E', g', cs, ls) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      well_formed c ->
      newer_than_cache g c -> interp_cache E c -> 
      interp_cnf E' cs /\ interp_cache E' c'.
Proof.
  move=> op e1 IH1 m c s E g m' c' E' g' cs ls Hfcet Hmke Hgm Hgtt Hwfc Hgc HiEc.
  move: Hmke. rewrite /= Hfcet.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm Hgtt Hwfc Hgc HiEc) => [HiE1cs1 HiE1c1].
  case Hfhet : (find_het (QFBV.Eunop op e1) c1) => [[csop lsop] | ].
  - case=> _ <- <- _ <- _. 
    have HiE1csop : interp_cnf E1 csop by apply (interp_cache_find_het HiE1c1 Hfhet).
    split.
    + rewrite !interp_cnf_catrev. by rewrite HiE1cs1 HiE1csop.
    + by apply interp_cache_add_cet.
  - case Hop : (mk_env_eunop op E1 g1 ls1) => [[[Eop gop] csop] lsop].
    case=> _ <- <- _ <- _. 
    move: (mk_env_exp_ccache_newer_gen He1) => Hgg1.
    have HpE1Eopg1 : env_preserve E1 Eop g1.
    { 
      move: Hop. 
      case op=> [ | | i j | n | n | n | n ]; rewrite /mk_env_eunop => Hop;
        [ apply (mk_env_not_preserve Hop) |
          apply (mk_env_neg_preserve Hop) |
          apply (mk_env_extract_preserve Hop) |
          apply (mk_env_high_preserve Hop) |
          apply (mk_env_low_preserve Hop) |
          apply (mk_env_zeroextend_preserve Hop) |
          apply (mk_env_signextend_preserve Hop) ];
        done.
    }      
    have HiEopcsop : interp_cnf Eop csop.
    { 
      move: (mk_env_exp_ccache_newer_res He1 Hgm Hgtt Hwfc Hgc) => Hg1ls1.
      move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
      move: Hop.
      case op=> [ | | i j | n | n | n | n ]; rewrite /mk_env_eunop => Hop;
        [ apply (mk_env_not_sat Hop) |
          apply (mk_env_neg_sat Hop) |
          apply (mk_env_extract_sat Hop) |
          apply (mk_env_high_sat Hop) |
          apply (mk_env_low_sat Hop) |
          apply (mk_env_zeroextend_sat Hop) |
          apply (mk_env_signextend_sat Hop) ];
        done.
    }
    split.
    + rewrite !interp_cnf_catrev.
      move: (mk_env_exp_ccache_newer_cnf He1 Hgm Hgtt Hwfc Hgc) => Hg1cs1.
      rewrite -(env_preserve_cnf HpE1Eopg1 Hg1cs1) in HiE1cs1; 
        move: HiE1cs1 => HiEopcs1.
      by rewrite HiEopcs1 HiEopcsop.
    + apply interp_cache_add_cet, interp_cache_add_het; try done.
      move: (mk_env_exp_ccache_newer_cache He1 Hgm Hgtt Hwfc Hgc) => Hg1c1.
      by rewrite (env_preserve_interp_cache HpE1Eopg1 Hg1c1).     
Qed.

Lemma mk_env_exp_ccache_interp_cache_nocet_binop :
  forall (op : QFBV.ebinop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c ->
        interp_cache E c -> interp_cnf E' cs /\ interp_cache E' c') ->
    forall e2 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed c ->
          newer_than_cache g c ->
          interp_cache E c -> interp_cnf E' cs /\ interp_cache E' c') ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (ls : word),
        find_cet (QFBV.Ebinop op e1 e2) c = None ->
        mk_env_exp_ccache m c s E g (QFBV.Ebinop op e1 e2) = (m', c', E', g', cs, ls) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c -> interp_cache E c -> 
        interp_cnf E' cs /\ interp_cache E' c'.
Proof.
  move=> op e1 IH1 e2 IH2 m c s E g m' c' E' g' cs ls Hfcet 
            Hmke Hgm Hgtt Hwfc Hgc HiEc.
  move: Hmke. rewrite /= Hfcet.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm Hgtt Hwfc Hgc HiEc) => [HiE1cs1 HiE1c1].
  move: (mk_env_exp_ccache_newer_vm He1 Hgm) => Hg1m1.
  move: (mk_env_exp_ccache_newer_gen He1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (mk_env_exp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (mk_env_exp_ccache_newer_cache He1 Hgm Hgtt Hwfc Hgc) => Hg1c1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1 Hg1tt Hwfc1 Hg1c1 HiE1c1) 
        => [HiE2cs2 HiE2c2].
  move: (mk_env_exp_ccache_preserve He2) => HpE1E2g1.
  move: (mk_env_exp_ccache_newer_cnf He1 Hgm Hgtt Hwfc Hgc) => Hg1cs1.
  rewrite -(env_preserve_cnf HpE1E2g1 Hg1cs1) in HiE1cs1; move: HiE1cs1 => HiE2cs1.
  case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csop lsop] | ].
  - case=> _ <- <- _ <- _. 
    have HiE2csop : interp_cnf E2 csop by apply (interp_cache_find_het HiE2c2 Hfhet).
    split.
    + rewrite !interp_cnf_catrev. by rewrite HiE2cs1 HiE2cs2 HiE2csop.
    + by apply interp_cache_add_cet.
  - case Hop : (mk_env_ebinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lsop].
    case=> _ <- <- _ <- _. 
    move: (mk_env_exp_ccache_newer_gen He2) => Hg1g2.
    have HpE2Eopg2 : env_preserve E2 Eop g2.
    { 
      move: Hop. case op; rewrite /mk_env_ebinop => Hop;
        [ apply (mk_env_and_preserve Hop) |
          apply (mk_env_or_preserve Hop) |
          apply (mk_env_xor_preserve Hop) |
          apply (mk_env_add_preserve Hop) |
          apply (mk_env_sub_preserve Hop) |
          apply (mk_env_mul_preserve Hop) |
          admit (* TODO: mod *) |
          admit (* TODO: srem *) |
          admit (* TODO: smod *) |
          apply (mk_env_shl_preserve Hop) |
          apply (mk_env_lshr_preserve Hop) |
          apply (mk_env_ashr_preserve Hop) |
          apply (mk_env_concat_preserve Hop) ];
        done.
    }      
    have HiEopcsop : interp_cnf Eop csop.
    { 
      move: (mk_env_exp_ccache_newer_res He1 Hgm Hgtt Hwfc Hgc) => Hg1ls1.
      move: (newer_than_lits_le_newer Hg1ls1 Hg1g2) => Hg2ls1.
      move: (mk_env_exp_ccache_newer_res He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) => Hg2ls2.
      move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt.
      move: Hop. case op; rewrite /mk_env_ebinop => Hop;
        [ apply (mk_env_and_sat Hop) |
          apply (mk_env_or_sat Hop) |
          apply (mk_env_xor_sat Hop) |
          apply (mk_env_add_sat Hop) |
          apply (mk_env_sub_sat Hop) |
          apply (mk_env_mul_sat Hop) |
          admit (* TODO: mod *) |
          admit (* TODO: srem *) |
          admit (* TODO: smod *) |
          apply (mk_env_shl_sat Hop) |
          apply (mk_env_lshr_sat Hop) |
          apply (mk_env_ashr_sat Hop) |
          apply (mk_env_concat_sat Hop) ];
        done.
    }
    split.
    + rewrite !interp_cnf_catrev.
      move: (newer_than_cnf_le_newer Hg1cs1 Hg1g2) => Hg2cs1.
      rewrite -(env_preserve_cnf HpE2Eopg2 Hg2cs1) in HiE2cs1; 
        move: HiE2cs1 => HiEopcs1.
      move: (mk_env_exp_ccache_newer_cnf He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) => Hg2cs2.
      rewrite -(env_preserve_cnf HpE2Eopg2 Hg2cs2) in HiE2cs2; 
        move: HiE2cs2 => HiEopcs2.
      by rewrite HiEopcs1 HiEopcs2 HiEopcsop.
    + apply interp_cache_add_cet, interp_cache_add_het; try done.
      move: (mk_env_exp_ccache_newer_cache He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) => Hg2c2.
      by rewrite (env_preserve_interp_cache HpE2Eopg2 Hg2c2).     
Admitted.

Lemma mk_env_exp_ccache_interp_cache_nocet_ite :
  forall b : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g b = (m', c', E', g', cs, l) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c ->
        interp_cache E c -> interp_cnf E' cs /\ interp_cache E' c') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed c ->
          newer_than_cache g c ->
          interp_cache E c -> interp_cnf E' cs /\ interp_cache E' c') ->
      forall e2 : QFBV.exp,
        (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
                (g : generator) (m' : vm) (c' : compcache) (E' : env) 
                (g' : generator) (cs : cnf) (ls : word),
            mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
            newer_than_vm g m ->
            newer_than_lit g lit_tt ->
            well_formed c ->
            newer_than_cache g c ->
            interp_cache E c -> interp_cnf E' cs /\ interp_cache E' c') ->
        forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
               (g : generator) (m' : vm) (c' : compcache) (E' : env) 
               (g' : generator) (cs : cnf) (ls : word),
          find_cet (QFBV.Eite b e1 e2) c = None ->
          mk_env_exp_ccache m c s E g (QFBV.Eite b e1 e2) = (m', c', E', g', cs, ls) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed c ->
          newer_than_cache g c -> interp_cache E c -> 
          interp_cnf E' cs /\ interp_cache E' c'.
Proof.
  move=> b IHb e1 IH1 e2 IH2 m c s E g m' c' E' g' cs ls Hfcet 
            Hmke Hgm Hgtt Hwfc Hgc HiEc.
  move: Hmke. rewrite /= Hfcet.
  case Hb : (mk_env_bexp_ccache m c s E g b) => [[[[[mb cb] Eb] gb] csb] lb].
  case He1 : (mk_env_exp_ccache mb cb s Eb gb e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IHb _ _ _ _ _ _ _ _ _ _ _ Hb Hgm Hgtt Hwfc Hgc HiEc) => [HiEbcsb HiEbcb].
  move: (mk_env_bexp_ccache_newer_vm Hb Hgm) => Hgbmb.
  move: (mk_env_bexp_ccache_newer_gen Hb) => Hggb.
  move: (newer_than_lit_le_newer Hgtt Hggb) => Hgbtt.
  move: (mk_env_bexp_ccache_well_formed Hb Hwfc) => Hwfcb.
  move: (mk_env_bexp_ccache_newer_cache Hb Hgm Hgtt Hwfc Hgc) => Hgbcb.
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgbmb Hgbtt Hwfcb Hgbcb HiEbcb) 
        => [HiE1cs1 HiE1c1].
  move: (mk_env_exp_ccache_preserve He1) => HpEbE1gb.
  move: (mk_env_bexp_ccache_newer_cnf Hb Hgm Hgtt Hwfc Hgc) => Hgbcsb.
  rewrite -(env_preserve_cnf HpEbE1gb Hgbcsb) in HiEbcsb; move: HiEbcsb => HiE1csb.
  move: (mk_env_exp_ccache_newer_vm He1 Hgbmb) => Hg1m1.
  move: (mk_env_exp_ccache_newer_gen He1) => Hgbg1.
  move: (newer_than_lit_le_newer Hgbtt Hgbg1) => Hg1tt.
  move: (mk_env_exp_ccache_well_formed He1 Hwfcb) => Hwfc1.
  move: (mk_env_exp_ccache_newer_cache He1 Hgbmb Hgbtt Hwfcb Hgbcb) => Hg1c1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1 Hg1tt Hwfc1 Hg1c1 HiE1c1) 
        => [HiE2cs2 HiE2c2].
  move: (mk_env_exp_ccache_preserve He2) => HpE1E2g1.
  move: (newer_than_cnf_le_newer Hgbcsb Hgbg1) => Hg1csb.
  rewrite -(env_preserve_cnf HpE1E2g1 Hg1csb) in HiE1csb; move: HiE1csb => HiE2csb.
  move: (mk_env_exp_ccache_newer_cnf He1 Hgbmb Hgbtt Hwfcb Hgbcb) => Hg1cs1.
  rewrite -(env_preserve_cnf HpE1E2g1 Hg1cs1) in HiE1cs1; move: HiE1cs1 => HiE2cs1.
  case Hfhet : (find_het (QFBV.Eite b e1 e2) c2) => [[csop lsop] | ].
  - case=> _ <- <- _ <- _. 
    have HiE2csop : interp_cnf E2 csop by apply (interp_cache_find_het HiE2c2 Hfhet).
    split.
    + rewrite !interp_cnf_catrev. by rewrite HiE2csb HiE2cs1 HiE2cs2 HiE2csop.
    + by apply interp_cache_add_cet.
  - case Hop : (mk_env_ite E2 g2 lb ls1 ls2) => [[[Eop gop] csop] lsop].
    case=> _ <- <- _ <- _. 
    move: (mk_env_exp_ccache_newer_gen He2) => Hg1g2.
    have HpE2Eopg2 : env_preserve E2 Eop g2 by apply (mk_env_ite_preserve Hop).
    have HiEopcsop : interp_cnf Eop csop.
    { 
      move: (mk_env_bexp_ccache_newer_res Hb Hgm Hgtt Hwfc Hgc) => Hgblb.
      move: (newer_than_lit_le_newer Hgblb Hgbg1) => Hg1lb.
      move: (newer_than_lit_le_newer Hg1lb Hg1g2) => Hg2lb.
      move: (mk_env_exp_ccache_newer_res He1 Hgbmb Hgbtt Hwfcb Hgbcb) => Hg1ls1.
      move: (newer_than_lits_le_newer Hg1ls1 Hg1g2) => Hg2ls1.
      move: (mk_env_exp_ccache_newer_res He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) => Hg2ls2.
      move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt.
      by apply (mk_env_ite_sat Hop).
    }
    split.
    + rewrite !interp_cnf_catrev.
      move: (newer_than_cnf_le_newer Hg1csb Hg1g2) => Hg2csb.
      rewrite -(env_preserve_cnf HpE2Eopg2 Hg2csb) in HiE2csb; 
        move: HiE2csb => HiEopcsb.
      move: (newer_than_cnf_le_newer Hg1cs1 Hg1g2) => Hg2cs1.
      rewrite -(env_preserve_cnf HpE2Eopg2 Hg2cs1) in HiE2cs1; 
        move: HiE2cs1 => HiEopcs1.
      move: (mk_env_exp_ccache_newer_cnf He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) => Hg2cs2.
      rewrite -(env_preserve_cnf HpE2Eopg2 Hg2cs2) in HiE2cs2; 
        move: HiE2cs2 => HiEopcs2.
      by rewrite HiEopcsb HiEopcs1 HiEopcs2 HiEopcsop.
    + apply interp_cache_add_cet, interp_cache_add_het; try done.
      move: (mk_env_exp_ccache_newer_cache He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) => Hg2c2.
      by rewrite (env_preserve_interp_cache HpE2Eopg2 Hg2c2).     
Qed.

Lemma mk_env_bexp_ccache_interp_cache_nocbt_false :
  forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
         (g : generator) (m' : vm) (c' : compcache) (E' : env) 
         (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Bfalse c = None ->
    mk_env_bexp_ccache m c s E g QFBV.Bfalse = (m', c', E', g', cs, l) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    well_formed c ->
    newer_than_cache g c -> interp_cache E c -> 
    interp_cnf E' cs /\ interp_cache E' c'.
Proof.
  move=> m c s E g m' c' E' g' cs l Hfcbt.
  rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Bfalse) c) => [[cse le] | ].
  - case=> _ <- <- _ <- _. move=> Hgm Hgtt Hwfc Hgc HiEc.
    have HiEcse : interp_cnf E cse by apply (interp_cache_find_hbt HiEc Hfhbt).
    split; [ done | by apply interp_cache_add_cbt ].
  - case=> _ <- <- _ <- _. move=> Hgm Hgtt Hwfc Hgc HiEc.
    split; [ done | by apply interp_cache_add_cbt, interp_cache_add_hbt].
Qed.

Lemma mk_env_bexp_ccache_interp_cache_nocbt_true :
  forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
         (g : generator) (m' : vm) (c' : compcache) (E' : env) 
         (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Btrue c = None ->
    mk_env_bexp_ccache m c s E g QFBV.Btrue = (m', c', E', g', cs, l) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    well_formed c ->
    newer_than_cache g c -> interp_cache E c -> 
    interp_cnf E' cs /\ interp_cache E' c'.
Proof.
  move=> m c s E g m' c' E' g' cs l Hfcbt.
  rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Btrue) c) => [[cse le] | ].
  - case=> _ <- <- _ <- _. move=> Hgm Hgtt Hwfc Hgc HiEc.
    have HiEcse : interp_cnf E cse by apply (interp_cache_find_hbt HiEc Hfhbt).
    split; [ done | by apply interp_cache_add_cbt ].
  - case=> _ <- <- _ <- _. move=> Hgm Hgtt Hwfc Hgc HiEc.
    split; [ done | by apply interp_cache_add_cbt, interp_cache_add_hbt].
Qed.

Lemma mk_env_bexp_ccache_interp_cache_nocbt_binop :
  forall (op : QFBV.bbinop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c ->
        interp_cache E c -> interp_cnf E' cs /\ interp_cache E' c') ->
    forall e2 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed c ->
          newer_than_cache g c ->
          interp_cache E c -> interp_cnf E' cs /\ interp_cache E' c') ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bbinop op e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bbinop op e1 e2) = (m', c', E', g', cs, l) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c -> interp_cache E c -> 
        interp_cnf E' cs /\ interp_cache E' c'.
Proof.
  move=> op e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt 
            Hmke Hgm Hgtt Hwfc Hgc HiEc.
  move: Hmke. rewrite /= Hfcbt.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm Hgtt Hwfc Hgc HiEc) => [HiE1cs1 HiE1c1].
  move: (mk_env_exp_ccache_newer_vm He1 Hgm) => Hg1m1.
  move: (mk_env_exp_ccache_newer_gen He1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (mk_env_exp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (mk_env_exp_ccache_newer_cache He1 Hgm Hgtt Hwfc Hgc) => Hg1c1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1 Hg1tt Hwfc1 Hg1c1 HiE1c1) 
        => [HiE2cs2 HiE2c2].
  move: (mk_env_exp_ccache_preserve He2) => HpE1E2g1.
  move: (mk_env_exp_ccache_newer_cnf He1 Hgm Hgtt Hwfc Hgc) => Hg1cs1.
  rewrite -(env_preserve_cnf HpE1E2g1 Hg1cs1) in HiE1cs1; move: HiE1cs1 => HiE2cs1.
  case Hfhbt : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[csop lop] | ].
  - case=> _ <- <- _ <- _. 
    have HiE2csop : interp_cnf E2 csop by apply (interp_cache_find_hbt HiE2c2 Hfhbt).
    split.
    + rewrite !interp_cnf_catrev. by rewrite HiE2cs1 HiE2cs2 HiE2csop.
    + by apply interp_cache_add_cbt.
  - case Hop : (mk_env_bbinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lop].
    case=> _ <- <- _ <- _. 
    move: (mk_env_exp_ccache_newer_gen He2) => Hg1g2.
    have HpE2Eopg2 : env_preserve E2 Eop g2.
    { 
      move: Hop. case op; rewrite /mk_env_bbinop => Hop;
        [ apply (mk_env_eq_preserve Hop) |
          apply (mk_env_ult_preserve Hop) |
          apply (mk_env_ule_preserve Hop) |
          apply (mk_env_ugt_preserve Hop) |
          apply (mk_env_uge_preserve Hop) |
          apply (mk_env_slt_preserve Hop) |
          apply (mk_env_sle_preserve Hop) |
          apply (mk_env_sgt_preserve Hop) |
          apply (mk_env_sge_preserve Hop) |
          apply (mk_env_uaddo_preserve Hop) |
          apply (mk_env_usubo_preserve Hop) |
          apply (mk_env_umulo_preserve Hop) |
          apply (mk_env_saddo_preserve Hop) |
          apply (mk_env_ssubo_preserve Hop) |
          apply (mk_env_smulo_preserve Hop) ];
        done.
    }      
    have HiEopcsop : interp_cnf Eop csop.
    { 
      move: (mk_env_exp_ccache_newer_res He1 Hgm Hgtt Hwfc Hgc) => Hg1ls1.
      move: (newer_than_lits_le_newer Hg1ls1 Hg1g2) => Hg2ls1.
      move: (mk_env_exp_ccache_newer_res He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) => Hg2ls2.
      move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt.
      move: Hop. case op; rewrite /mk_env_bbinop => Hop;
        [ apply (mk_env_eq_sat Hop) |
          apply (mk_env_ult_sat Hop) |
          apply (mk_env_ule_sat Hop) |
          apply (mk_env_ugt_sat Hop) |
          apply (mk_env_uge_sat Hop) |
          apply (mk_env_slt_sat Hop) |
          apply (mk_env_sle_sat Hop) |
          apply (mk_env_sgt_sat Hop) |
          apply (mk_env_sge_sat Hop) |
          apply (mk_env_uaddo_sat Hop) |
          apply (mk_env_usubo_sat Hop) |
          apply (mk_env_umulo_sat Hop) |
          apply (mk_env_saddo_sat Hop) |
          apply (mk_env_ssubo_sat Hop) |
          apply (mk_env_smulo_sat Hop) ];
        done.
    }
    split.
    + rewrite !interp_cnf_catrev.
      move: (newer_than_cnf_le_newer Hg1cs1 Hg1g2) => Hg2cs1.
      rewrite -(env_preserve_cnf HpE2Eopg2 Hg2cs1) in HiE2cs1; 
        move: HiE2cs1 => HiEopcs1.
      move: (mk_env_exp_ccache_newer_cnf He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) => Hg2cs2.
      rewrite -(env_preserve_cnf HpE2Eopg2 Hg2cs2) in HiE2cs2; 
        move: HiE2cs2 => HiEopcs2.
      by rewrite HiEopcs1 HiEopcs2 HiEopcsop.
    + apply interp_cache_add_cbt, interp_cache_add_hbt; try done.
      move: (mk_env_exp_ccache_newer_cache He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) => Hg2c2.
      by rewrite (env_preserve_interp_cache HpE2Eopg2 Hg2c2).     
Qed.

Lemma mk_env_bexp_ccache_interp_cache_nocbt_lneg :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c ->
        interp_cache E c -> interp_cnf E' cs /\ interp_cache E' c') ->
    forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
           (g : generator) (m' : vm) (c' : compcache) (E' : env) 
           (g' : generator) (cs : cnf) (l : literal),
      find_cbt (QFBV.Blneg e1) c = None ->
      mk_env_bexp_ccache m c s E g (QFBV.Blneg e1) = (m', c', E', g', cs, l) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      well_formed c ->
      newer_than_cache g c -> interp_cache E c ->
      interp_cnf E' cs /\ interp_cache E' c'.
Proof.
  move=> e1 IH1 m c s E g m' c' E' g' cs l Hfcbt Hmke Hgm Hgtt Hwfc Hgc HiEc.
  move: Hmke. rewrite /mk_env_bexp_ccache -/mk_env_bexp_ccache Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm Hgtt Hwfc Hgc HiEc) => [HiE1cs1 HiE1c1].
  case Hfhbt : (find_hbt (QFBV.Blneg e1) c1) => [[csop lop] | ].
  - case=> _ <- <- _ <- _. 
    have HiE1csop : interp_cnf E1 csop by apply (interp_cache_find_hbt HiE1c1 Hfhbt).
    split.
    + rewrite !interp_cnf_catrev. by rewrite HiE1cs1 HiE1csop.
    + by apply interp_cache_add_cbt.
  - case Hop : (mk_env_lneg E1 g1 l1) => [[[Eop gop] csop] lop].
    case=> _ <- <- _ <- _. 
    move: (mk_env_bexp_ccache_newer_gen He1) => Hgg1.
    have HpE1Eopg1 : env_preserve E1 Eop g1 by apply (mk_env_lneg_preserve Hop).
    have HiEopcsop : interp_cnf Eop csop.
    { 
      move: (mk_env_bexp_ccache_newer_res He1 Hgm Hgtt Hwfc Hgc) => Hg1l1.
      move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
      by apply (mk_env_lneg_sat Hop).
    }
    split.
    + rewrite !interp_cnf_catrev.
      move: (mk_env_bexp_ccache_newer_cnf He1 Hgm Hgtt Hwfc Hgc) => Hg1cs1.
      rewrite -(env_preserve_cnf HpE1Eopg1 Hg1cs1) in HiE1cs1; 
        move: HiE1cs1 => HiEopcs1.
      by rewrite HiEopcs1 HiEopcsop.
    + apply interp_cache_add_cbt, interp_cache_add_hbt; try done.
      move: (mk_env_bexp_ccache_newer_cache He1 Hgm Hgtt Hwfc Hgc) => Hg1c1.
      by rewrite (env_preserve_interp_cache HpE1Eopg1 Hg1c1).     
Qed.

Lemma mk_env_bexp_ccache_interp_cache_nocbt_conj :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c ->
        interp_cache E c -> interp_cnf E' cs /\ interp_cache E' c') ->
    forall e2 : QFBV.bexp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (l : literal),
          mk_env_bexp_ccache m c s E g e2 = (m', c', E', g', cs, l) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed c ->
          newer_than_cache g c ->
          interp_cache E c -> interp_cnf E' cs /\ interp_cache E' c') ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bconj e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bconj e1 e2) = (m', c', E', g', cs, l) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c -> interp_cache E c -> 
        interp_cnf E' cs /\ interp_cache E' c'.
Proof.
  move=> e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt Hmke Hgm Hgtt Hwfc Hgc HiEc.
  move: Hmke. rewrite /mk_env_bexp_ccache -/mk_env_bexp_ccache Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  case He2 : (mk_env_bexp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm Hgtt Hwfc Hgc HiEc) => [HiE1cs1 HiE1c1].
  move: (mk_env_bexp_ccache_newer_vm He1 Hgm) => Hg1m1.
  move: (mk_env_bexp_ccache_newer_gen He1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (mk_env_bexp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (mk_env_bexp_ccache_newer_cache He1 Hgm Hgtt Hwfc Hgc) => Hg1c1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1 Hg1tt Hwfc1 Hg1c1 HiE1c1) 
        => [HiE2cs2 HiE2c2].
  move: (mk_env_bexp_ccache_preserve He2) => HpE1E2g1.
  move: (mk_env_bexp_ccache_newer_cnf He1 Hgm Hgtt Hwfc Hgc) => Hg1cs1.
  rewrite -(env_preserve_cnf HpE1E2g1 Hg1cs1) in HiE1cs1; move: HiE1cs1 => HiE2cs1.
  case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csop lop] | ].
  - case=> _ <- <- _ <- _. 
    have HiE2csop : interp_cnf E2 csop by apply (interp_cache_find_hbt HiE2c2 Hfhbt).
    split.
    + rewrite !interp_cnf_catrev. by rewrite HiE2cs1 HiE2cs2 HiE2csop.
    + by apply interp_cache_add_cbt.
  - case Hop : (mk_env_conj E2 g2 l1 l2) => [[[Eop gop] csop] lop].
    case=> _ <- <- _ <- _. 
    move: (mk_env_bexp_ccache_newer_gen He2) => Hg1g2.
    have HpE2Eopg2 : env_preserve E2 Eop g2 by apply (mk_env_conj_preserve Hop).
    have HiEopcsop : interp_cnf Eop csop.
    { 
      move: (mk_env_bexp_ccache_newer_res He1 Hgm Hgtt Hwfc Hgc) => Hg1l1.
      move: (newer_than_lit_le_newer Hg1l1 Hg1g2) => Hg2l1.
      move: (mk_env_bexp_ccache_newer_res He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) => Hg2l2.
      move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt.
      by apply (mk_env_conj_sat Hop).
    }
    split.
    + rewrite !interp_cnf_catrev.
      move: (newer_than_cnf_le_newer Hg1cs1 Hg1g2) => Hg2cs1.
      rewrite -(env_preserve_cnf HpE2Eopg2 Hg2cs1) in HiE2cs1; 
        move: HiE2cs1 => HiEopcs1.
      move: (mk_env_bexp_ccache_newer_cnf He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) => Hg2cs2.
      rewrite -(env_preserve_cnf HpE2Eopg2 Hg2cs2) in HiE2cs2; 
        move: HiE2cs2 => HiEopcs2.
      by rewrite HiEopcs1 HiEopcs2 HiEopcsop.
    + apply interp_cache_add_cbt, interp_cache_add_hbt; try done.
      move: (mk_env_bexp_ccache_newer_cache He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) => Hg2c2.
      by rewrite (env_preserve_interp_cache HpE2Eopg2 Hg2c2).     
Qed.

Lemma mk_env_bexp_ccache_interp_cache_nocbt_disj :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c ->
        interp_cache E c -> interp_cnf E' cs /\ interp_cache E' c') ->
    forall e2 : QFBV.bexp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (l : literal),
          mk_env_bexp_ccache m c s E g e2 = (m', c', E', g', cs, l) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed c ->
          newer_than_cache g c ->
          interp_cache E c -> interp_cnf E' cs /\ interp_cache E' c') ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bdisj e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bdisj e1 e2) = (m', c', E', g', cs, l) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c -> interp_cache E c -> 
        interp_cnf E' cs /\ interp_cache E' c'.
Proof.
  move=> e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt Hmke Hgm Hgtt Hwfc Hgc HiEc.
  move: Hmke. rewrite /mk_env_bexp_ccache -/mk_env_bexp_ccache Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  case He2 : (mk_env_bexp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm Hgtt Hwfc Hgc HiEc) => [HiE1cs1 HiE1c1].
  move: (mk_env_bexp_ccache_newer_vm He1 Hgm) => Hg1m1.
  move: (mk_env_bexp_ccache_newer_gen He1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (mk_env_bexp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (mk_env_bexp_ccache_newer_cache He1 Hgm Hgtt Hwfc Hgc) => Hg1c1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1 Hg1tt Hwfc1 Hg1c1 HiE1c1) 
        => [HiE2cs2 HiE2c2].
  move: (mk_env_bexp_ccache_preserve He2) => HpE1E2g1.
  move: (mk_env_bexp_ccache_newer_cnf He1 Hgm Hgtt Hwfc Hgc) => Hg1cs1.
  rewrite -(env_preserve_cnf HpE1E2g1 Hg1cs1) in HiE1cs1; move: HiE1cs1 => HiE2cs1.
  case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csop lop] | ].
  - case=> _ <- <- _ <- _. 
    have HiE2csop : interp_cnf E2 csop by apply (interp_cache_find_hbt HiE2c2 Hfhbt).
    split.
    + rewrite !interp_cnf_catrev. by rewrite HiE2cs1 HiE2cs2 HiE2csop.
    + by apply interp_cache_add_cbt.
  - case Hop : (mk_env_disj E2 g2 l1 l2) => [[[Eop gop] csop] lop].
    case=> _ <- <- _ <- _. 
    move: (mk_env_bexp_ccache_newer_gen He2) => Hg1g2.
    have HpE2Eopg2 : env_preserve E2 Eop g2 by apply (mk_env_disj_preserve Hop).
    have HiEopcsop : interp_cnf Eop csop.
    { 
      move: (mk_env_bexp_ccache_newer_res He1 Hgm Hgtt Hwfc Hgc) => Hg1l1.
      move: (newer_than_lit_le_newer Hg1l1 Hg1g2) => Hg2l1.
      move: (mk_env_bexp_ccache_newer_res He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) => Hg2l2.
      move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt.
      by apply (mk_env_disj_sat Hop).
    }
    split.
    + rewrite !interp_cnf_catrev.
      move: (newer_than_cnf_le_newer Hg1cs1 Hg1g2) => Hg2cs1.
      rewrite -(env_preserve_cnf HpE2Eopg2 Hg2cs1) in HiE2cs1; 
        move: HiE2cs1 => HiEopcs1.
      move: (mk_env_bexp_ccache_newer_cnf He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) => Hg2cs2.
      rewrite -(env_preserve_cnf HpE2Eopg2 Hg2cs2) in HiE2cs2; 
        move: HiE2cs2 => HiEopcs2.
      by rewrite HiEopcs1 HiEopcs2 HiEopcsop.
    + apply interp_cache_add_cbt, interp_cache_add_hbt; try done.
      move: (mk_env_bexp_ccache_newer_cache He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) => Hg2c2.
      by rewrite (env_preserve_interp_cache HpE2Eopg2 Hg2c2).     
Qed.


Corollary mk_env_exp_ccache_interp_cache :
  forall e m c s E g m' c' E' g' cs ls,
    mk_env_exp_ccache m c s E g e = (m', c', E', g', cs, ls) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    (* QFBV.well_formed_exp e te -> *)
    CompCache.well_formed c -> newer_than_cache g c -> 
    CompCache.interp_cache E c ->
    interp_cnf E' cs /\ CompCache.interp_cache E' c'
  with
    mk_env_bexp_ccache_interp_cache :
      forall e m c s E g m' c' E' g' cs l,
        mk_env_bexp_ccache m c s E g e = (m', c', E', g', cs, l) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_bexp e te -> *)
        CompCache.well_formed c -> newer_than_cache g c -> 
        CompCache.interp_cache E c ->
        interp_cnf E' cs /\ CompCache.interp_cache E' c'.
Proof.
  (* exp *)
  set IHe := mk_env_exp_ccache_interp_cache.
  set IHb := mk_env_bexp_ccache_interp_cache.
  move=> e m c s E g m' c' E' g' cs ls.
  case Hfcet: (find_cet e c) => [[cse lse] | ]. 
  - rewrite mk_env_exp_ccache_equation Hfcet /=.
    case=> _ <- <- _ <- _. move=> _ _ _ _ HiEc. done.
  - move: e m c s E g m' c' E' g' cs ls Hfcet.
    case.
    + exact: mk_env_exp_ccache_interp_cache_nocet_var.
    + exact: mk_env_exp_ccache_interp_cache_nocet_const.
    + move=> op e1; move: op e1 (IHe e1).
      exact: mk_env_exp_ccache_interp_cache_nocet_unop.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_interp_cache_nocet_binop.
    + move=> b e1 e2; move: b (IHb b) e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_interp_cache_nocet_ite.
  (* bexp *)
  set IHe := mk_env_exp_ccache_interp_cache.
  set IHb := mk_env_bexp_ccache_interp_cache.
  move=> e m c s E g m' c' E' g' cs l.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite mk_env_bexp_ccache_equation Hfcbt /=.
    case=> _ <- <- _ <- _. move=> _ _ _ _ HiEc. done.
  - move: e m c s E g m' c' E' g' cs l Hfcbt.
    case.
    + exact: mk_env_bexp_ccache_interp_cache_nocbt_false.
    + exact: mk_env_bexp_ccache_interp_cache_nocbt_true.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_bexp_ccache_interp_cache_nocbt_binop.
    + move=> e1; move: e1 (IHb e1).
      exact: mk_env_bexp_ccache_interp_cache_nocbt_lneg.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_interp_cache_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_interp_cache_nocbt_disj.
Qed.


(* = mk_env_exp_ccache_sat and mk_env_bexp_ccache_sat = *)

Corollary mk_env_exp_ccache_sat :
  forall e m c s E g m' c' E' g' cs ls,
    mk_env_exp_ccache m c s E g e = (m', c', E', g', cs, ls) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    CompCache.well_formed c -> newer_than_cache g c -> 
    CompCache.interp_cache E c ->
    interp_cnf E' cs.
Proof.
  move=> e m c s E g m' c' E' g' cs ls Hmke Hgm Hgt Hwfc Hgc HiEc.
  move: (mk_env_exp_ccache_interp_cache Hmke Hgm Hgt Hwfc Hgc HiEc) => [Hics _].
  done.
Qed.

Corollary mk_env_bexp_ccache_sat :
  forall e m c s E g m' c' E' g' cs l,
    mk_env_bexp_ccache m c s E g e = (m', c', E', g', cs, l) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    CompCache.well_formed c -> newer_than_cache g c -> 
    CompCache.interp_cache E c ->
    interp_cnf E' cs.
Proof.
  move=> e m c s E g m' c' E' g' cs l Hmke Hgm Hgt Hwfc Hgc HiEc.
  move: (mk_env_bexp_ccache_interp_cache Hmke Hgm Hgt Hwfc Hgc HiEc) => [Hics _].
  done.
Qed.  


(* = bit_blast_exp_ccache_interp_cache_ct and bit_blast_bexp_ccache_interp_cache_ct = *)

Lemma bit_blast_exp_ccache_interp_cache_ct_nocet_var :
  forall (t : SSAVarOrder.t) (te : SSATE.env) (m : vm) (c : compcache)
         (g : generator) (m' : vm) (c' : compcache) (g' : generator) 
         (cs : cnf) (ls : word) (E : env),
    find_cet (QFBV.Evar t) c = None ->
    bit_blast_exp_ccache te m c g (QFBV.Evar t) = (m', c', g', cs, ls) ->
    interp_cache_ct E c -> interp_cnf E (add_prelude cs) -> interp_cache_ct E c'.
Proof.
  move=> v te m c g m' c' g' cs ls E Hfcet. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Evar v) c) => [[cse lse] | ].
  - case=> _ <- _ <- _ HiEc HiEcse.
    rewrite add_prelude_expand in HiEcse. move: HiEcse => /andP [_ HiEcse].
    by apply interp_cache_ct_add_cet.
  - case Hfv : (SSAVM.find v m).
    + case=> _ <- _ <- _ HiEc _.
      by apply interp_cache_ct_add_cet; try rewrite -interp_cache_ct_add_het.
    + case Hv : (bit_blast_var te g v) => [[gv csv] lsv].
      case=> _ <- _ <- _ HiEc HiEcsv.
      rewrite add_prelude_expand in HiEcsv. move: HiEcsv => /andP [_ HiEcsv].
      by apply interp_cache_ct_add_cet; try rewrite -interp_cache_ct_add_het.
Qed.

Lemma bit_blast_exp_ccache_interp_cache_ct_nocet_binop :
  forall (op : QFBV.ebinop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
            (ls : word) (E : env),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) ->
        interp_cache_ct E c -> interp_cnf E (add_prelude cs) -> 
        interp_cache_ct E c') ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
              (ls : word) (E : env),
          bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls) ->
          interp_cache_ct E c -> interp_cnf E (add_prelude cs) -> 
          interp_cache_ct E c') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
             (ls : word) (E : env),
        find_cet (QFBV.Ebinop op e1 e2) c = None ->
        bit_blast_exp_ccache te m c g (QFBV.Ebinop op e1 e2) = (m', c', g', cs, ls) ->
        interp_cache_ct E c -> interp_cnf E (add_prelude cs) -> 
        interp_cache_ct E c'.
Proof.
  move=> op e1 IH1 e2 IH2 te m c g m' c' g' cs ls E Hfcet. rewrite /= Hfcet.
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
  case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csop lsop] | ];
    last case Hop : (bit_blast_ebinop op g2 ls1 ls2) => [[gop csop] lsop];
    case=> _ <- _ <- _ HiEc;
    rewrite !add_prelude_catrev => /andP [HiEcs1 /andP [HiEcs2 HiEcsop]];
    move: (IH1 _ _ _ _ _ _ _ _ _ _ He1 HiEc HiEcs1) => HiEc1;
    move: (IH2 _ _ _ _ _ _ _ _ _ _ He2 HiEc1 HiEcs2) => HiEc2;
    rewrite add_prelude_expand in HiEcsop; move: HiEcsop => /andP [_ HiEcsop];
    by apply interp_cache_ct_add_cet; try rewrite -interp_cache_ct_add_het.
Qed.

Lemma bit_blast_bexp_ccache_interp_cache_ct_nocbt_conj :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
            (l : literal) (E : env),
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l) ->
        interp_cache_ct E c -> interp_cnf E (add_prelude cs) -> 
        interp_cache_ct E c') ->
    forall e2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
              (l : literal) (E : env),
          bit_blast_bexp_ccache te m c g e2 = (m', c', g', cs, l) ->
          interp_cache_ct E c -> interp_cnf E (add_prelude cs) -> 
          interp_cache_ct E c') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
             (l : literal) (E : env),
        find_cbt (QFBV.Bconj e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bconj e1 e2) = (m', c', g', cs, l) ->
        interp_cache_ct E c -> interp_cnf E (add_prelude cs) -> 
        interp_cache_ct E c'.
Proof.
  move=> e1 IH1 e2 IH2 te m c g m' c' g' cs l E Hfcbt. 
  rewrite /bit_blast_bexp_ccache -/bit_blast_bexp_ccache Hfcbt.
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
  case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csop lop] | ];
    last case Hop : (bit_blast_conj g2 l1 l2) => [[gop csop] lop];
    case=> _ <- _ <- _ HiEc;
    rewrite !add_prelude_catrev => /andP [HiEcs1 /andP [HiEcs2 HiEcsop]];
    move: (IH1 _ _ _ _ _ _ _ _ _ _ He1 HiEc HiEcs1) => HiEc1;
    move: (IH2 _ _ _ _ _ _ _ _ _ _ He2 HiEc1 HiEcs2) => HiEc2;
    rewrite add_prelude_expand in HiEcsop; move: HiEcsop => /andP [_ HiEcsop];
    by apply interp_cache_ct_add_cbt; try rewrite -interp_cache_ct_add_hbt.
Qed.

Lemma bit_blast_bexp_ccache_interp_cache_ct_nocbt_disj :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
            (l : literal) (E : env),
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l) ->
        interp_cache_ct E c -> interp_cnf E (add_prelude cs) -> 
        interp_cache_ct E c') ->
    forall e2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
              (l : literal) (E : env),
          bit_blast_bexp_ccache te m c g e2 = (m', c', g', cs, l) ->
          interp_cache_ct E c -> interp_cnf E (add_prelude cs) -> 
          interp_cache_ct E c') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
             (l : literal) (E : env),
        find_cbt (QFBV.Bdisj e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bdisj e1 e2) = (m', c', g', cs, l) ->
        interp_cache_ct E c -> interp_cnf E (add_prelude cs) -> 
        interp_cache_ct E c'.
Proof.
  move=> e1 IH1 e2 IH2 te m c g m' c' g' cs l E Hfcbt. 
  rewrite /bit_blast_bexp_ccache -/bit_blast_bexp_ccache Hfcbt.
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
  case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csop lop] | ];
    last case Hop : (bit_blast_disj g2 l1 l2) => [[gop csop] lop];
    case=> _ <- _ <- _ HiEc;
    rewrite !add_prelude_catrev => /andP [HiEcs1 /andP [HiEcs2 HiEcsop]];
    move: (IH1 _ _ _ _ _ _ _ _ _ _ He1 HiEc HiEcs1) => HiEc1;
    move: (IH2 _ _ _ _ _ _ _ _ _ _ He2 HiEc1 HiEcs2) => HiEc2;
    rewrite add_prelude_expand in HiEcsop; move: HiEcsop => /andP [_ HiEcsop];
    by apply interp_cache_ct_add_cbt; try rewrite -interp_cache_ct_add_hbt.
Qed.


Corollary bit_blast_exp_ccache_interp_cache_ct :
  forall (e : QFBV.exp) te m c g m' c' g' cs ls E,
    bit_blast_exp_ccache te m c g e = (m', c', g', cs, ls) ->
    interp_cache_ct E c -> interp_cnf E (add_prelude cs) -> interp_cache_ct E c'
  with
    bit_blast_bexp_ccache_interp_cache_ct :
      forall (e : QFBV.bexp) te m c g m' c' g' cs l E,
        bit_blast_bexp_ccache te m c g e = (m', c', g', cs, l) ->
        interp_cache_ct E c -> interp_cnf E (add_prelude cs) -> interp_cache_ct E c'.
Proof.
  (* exp *)
  set IHe := bit_blast_exp_ccache_interp_cache_ct.
  set IHb := bit_blast_bexp_ccache_interp_cache_ct.
  move=> e te m c g m' c' g' cs ls E.
  case Hfcet: (find_cet e c) => [[cse lse] | ]. 
  - rewrite bit_blast_exp_ccache_equation Hfcet /=.
    case=> _ <- _ <- _. done. 
  - move: e te m c g m' c' g' cs ls E Hfcet.
    case.
    + exact: bit_blast_exp_ccache_interp_cache_ct_nocet_var.
    + admit.
    + admit.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_exp_ccache_interp_cache_ct_nocet_binop.
    + admit.
  (* bexp *)
  set IHe := bit_blast_exp_ccache_interp_cache_ct.
  set IHb := bit_blast_bexp_ccache_interp_cache_ct.
  move=> e te m c g m' c' g' cs l E.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite bit_blast_bexp_ccache_equation Hfcbt /=.
    case=> _ <- _ <- _. done. 
  - move: e te m c g m' c' g' cs l E Hfcbt.
    case.
    + admit.
    + admit.
    + admit.
    + admit.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: bit_blast_bexp_ccache_interp_cache_ct_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: bit_blast_bexp_ccache_interp_cache_ct_nocbt_disj.
Admitted.
      
