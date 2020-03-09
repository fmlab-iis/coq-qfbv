From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport 
     AdhereConform.
(* From BBCache Require Import Cache BitBlastingCacheDef BitBlastingCacheWF  *)
(*      BitBlastingCachePreserve BitBlastingCacheMkEnv. *)
From newBBCache Require Import CompCache BitBlastingCCacheDef 
     BitBlastingCCachePreserve BitBlastingCCacheFind BitBlastingCCacheSat
     BitBlastingCCacheWF.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Ltac subexp_neq :=
  match goal with
  | |- ~ is_true (?e0 == ?e) =>
    match e with
    | context [e0] =>
      let H := fresh in
      move/eqP=> H; move: H; elim e0; congruence
    end
  end.

(* = bit_blast_exp_ccache_correct_cache and bit_blast_bexp_ccache_correct_cache = *)

Lemma bit_blast_eunop_correct op g bs E ls g' cs lrs:
  bit_blast_eunop op g ls = (g', cs, lrs) ->
  enc_bits E ls bs -> interp_cnf E (add_prelude cs) ->
  enc_bits E lrs ((QFBV.eunop_denote op) bs).
Proof.
  case op => [ | | i j | n | n | n | n ] /=;
    [ exact: bit_blast_not_correct |
      exact: bit_blast_neg_correct |
      exact: bit_blast_extract_correct |
      exact: bit_blast_high_correct |
      exact: bit_blast_low_correct |
      exact: bit_blast_zeroextend_correct |
      exact: bit_blast_signextend_correct ].
Qed.

Lemma bit_blast_ebinop_correct op g bs1 bs2 E ls1 ls2 g' cs ls :
  bit_blast_ebinop op g ls1 ls2 = (g', cs, ls) ->
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 -> interp_cnf E (add_prelude cs) ->
  size ls1 == size ls2 -> enc_bits E ls ((QFBV.ebinop_denote op) bs1 bs2).
Proof.
  move=> Hbb Henc1 Henc2 Hics /eqP Hsize; move: Hbb; case op => /= Hbb;
    [ apply (bit_blast_and_correct Hbb) |
      apply (bit_blast_or_correct Hbb) |
      apply (bit_blast_xor_correct Hbb) |
      apply (bit_blast_add_correct Hbb Henc1 Henc2) |
      apply (bit_blast_sub_correct Hbb) |
      apply (bit_blast_mul_correct Hbb) |
      admit (* TODO: mod *) |
      admit (* TODO: srem *) |
      admit (* TODO: smod *) |
      apply (bit_blast_shl_correct Hbb) |
      apply (bit_blast_lshr_correct Hbb) |
      apply (bit_blast_ashr_correct Hbb) |
      apply (bit_blast_concat_correct Hbb) ];
    done.
Admitted.

Lemma bit_blast_bbinop_correct op g bs1 bs2 E ls1 ls2 g' cs l:
  bit_blast_bbinop op g ls1 ls2 = (g', cs, l) ->
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 -> interp_cnf E (add_prelude cs) ->
  size ls1 == size ls2 -> enc_bit E l ((QFBV.bbinop_denote op) bs1 bs2).
Proof.
  move=> Hbb Henc1 Henc2 Hics /eqP Hsize; move: Hbb; case op => /= Hbb;
    [ apply (bit_blast_eq_correct Hbb) |
      apply (bit_blast_ult_correct Hbb) |
      apply (bit_blast_ule_correct Hbb) |
      apply (bit_blast_ugt_correct Hbb) |
      apply (bit_blast_uge_correct Hbb) |
      apply (bit_blast_slt_correct Hbb) |
      apply (bit_blast_sle_correct Hbb) |
      apply (bit_blast_sgt_correct Hbb) |
      apply (bit_blast_sge_correct Hbb) |
      apply (bit_blast_uaddo_correct Hbb); move/eqP: Hsize |
      apply (bit_blast_usubo_correct Hbb) |
      apply (bit_blast_umulo_correct Hbb); move/eqP: Hsize |
      apply (bit_blast_saddo_correct Hbb); move/eqP: Hsize |
      apply (bit_blast_ssubo_correct Hbb); move/eqP: Hsize |
      apply (bit_blast_smulo_correct Hbb); move/eqP: Hsize ];
    done.
Qed.

Lemma bit_blast_exp_ccache_correct_cache_nocet_var :
  forall (t : SSAVarOrder.t) (te : SSATE.env) (m : vm) (c : compcache)
         (g : generator) (m' : vm) (c' : compcache) (g' : generator) 
         (cs : cnf) (ls : word),
    find_cet (QFBV.Evar t) c = None ->
    bit_blast_exp_ccache te m c g (QFBV.Evar t) = (m', c', g', cs, ls) ->
    QFBV.well_formed_exp (QFBV.Evar t) te -> 
    CompCache.well_formed c -> correct m c -> correct m' c'.
Proof.
  move=> v te im ic ig om oc og ocs ols. 
  move=> Hfcet. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Evar v) ic) => [[csh lsh] | ].
  - case=> <- <- _ _ _ _ _ Hcrimic. apply CompCache.correct_add_cet; try done.
    move: (correct_find_het Hcrimic Hfhet).
    rewrite //=.
  - case Hfind: (SSAVM.find v im).
    + case=> <- <- _ _ _ _ _ Hcrimic.
      apply CompCache.correct_add_cet_het => /=; try done;
      move=> E s Hcon _; move: (Hcon v); by rewrite /consistent1 Hfind.
    + case Hblast: (bit_blast_var te ig v) => [[vg vcs] vls].
      case=> <- <- _ _ _ _ _ Hcrimic.
      apply CompCache.correct_add_cet_het => /=; try done.
      * apply (@vm_preserve_correct im); [by apply vm_preserve_add_diag | done].
      * all: move=> E s /= Hcon _; move: (Hcon v); rewrite /consistent1;
             by rewrite (SSAVM.Lemmas.find_add_eq (eq_refl v)).
Qed.

Lemma bit_blast_exp_ccache_correct_cache_nocet_const :
  forall (b : bits) (te : SSATE.env) (m : vm) (c : compcache) 
         (g : generator) (m' : vm) (c' : compcache) (g' : generator) 
         (cs : cnf) (ls : word),
    find_cet (QFBV.Econst b) c = None ->
    bit_blast_exp_ccache te m c g (QFBV.Econst b) = (m', c', g', cs, ls) ->
    QFBV.well_formed_exp (QFBV.Econst b) te ->
    well_formed c -> correct m c -> correct m' c'.
Proof.
  move=> bs te m c g m' c' g' cs ls. move=> Hfcet. 
  rewrite /bit_blast_exp_ccache -/bit_blast_exp_ccache Hfcet.
  case Hfhet : (find_het (QFBV.Econst bs) c) => [[csh lsh] | ].
  - case=> <- <- _ _ _ _ _ Hcrmc. apply CompCache.correct_add_cet; try done.
    move: (correct_find_het Hcrmc Hfhet). rewrite //=.
  - case Hconst : (bit_blast_const g bs) => [[gbs csbs] lsbs].
    case=> <- <- _ _ _ _ _ Hcrmc.
    apply CompCache.correct_add_cet_het => /=; try done;
      move=> E s Hcon; exact: (bit_blast_const_correct Hconst).
Qed.

Lemma bit_blast_exp_ccache_correct_cache_nocet_unop :
  forall (op : QFBV.eunop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) ->
        QFBV.well_formed_exp e1 te -> well_formed c -> 
        correct m c -> correct m' c') ->
    forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
           (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
      find_cet (QFBV.Eunop op e1) c = None ->
      bit_blast_exp_ccache te m c g (QFBV.Eunop op e1) = (m', c', g', cs, ls) ->
      QFBV.well_formed_exp (QFBV.Eunop op e1) te ->
      well_formed c -> correct m c -> correct m' c'.
Proof.
  move=> op e1 IH1 te m c g m' c' g' cs ls Hfcet Hbb /= Hwf1 Hwfc Hcrmc. 
  move: Hbb. rewrite /= Hfcet.
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwf1 Hwfc Hcrmc) => Hcrm1c1.
  rewrite -(@bit_blast_exp_ccache_find_cet e1 _ _ _ _ _ _ _ _ _ _ _ He1) 
    in Hfcet; last by auto_prove_len_lt.
  move: (bit_blast_exp_ccache_in_cet He1) => [cse1c Hfcete1].
  move: (bit_blast_exp_ccache_in_het He1 Hwfc) => [cse1h Hfhete1].
  case Hfhet : (find_het (QFBV.Eunop op e1) c1) => [[csh lsh] | ].
  - case=> <- <- _ _ _.
    apply CompCache.correct_add_cet; try done. rewrite /=.
    exists cse1c, ls1. repeat (split; try done).
    move: (correct_find_het Hcrm1c1 Hfhet). rewrite /=.
    move=> [cs1' [ls1' [Hfe1 Hence]]].
    rewrite /find_het in Hfhete1; rewrite Hfhete1 in Hfe1.
    move: Hence. case: Hfe1 => _ <-. 
    done.
  - case Hr : (bit_blast_eunop op g1 ls1) => [[gr csr] lsr].
    case=> <- <- _ _ _.
    apply CompCache.correct_add_cet_het; (try done);
      rewrite /=;
      [ exists cse1c, ls1 | exists cse1h, ls1 ];
      repeat (split; try done);
      move=> E s Hcon; exact: (bit_blast_eunop_correct Hr).
Qed.

Lemma bit_blast_exp_ccache_correct_cache_nocet_binop :
  forall (op : QFBV.ebinop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) ->
        QFBV.well_formed_exp e1 te -> well_formed c -> 
        correct m c -> correct m' c') ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
          bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls) ->
          QFBV.well_formed_exp e2 te -> well_formed c -> 
          correct m c -> correct m' c') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        find_cet (QFBV.Ebinop op e1 e2) c = None ->
        bit_blast_exp_ccache te m c g (QFBV.Ebinop op e1 e2) = (m', c', g', cs, ls) ->
        QFBV.well_formed_exp (QFBV.Ebinop op e1 e2) te ->
        well_formed c -> correct m c -> correct m' c'.
Proof.
  move=> op e1 IH1 e2 IH2 te m c g m' c' g' cs ls Hfcet Hbb /= 
            /andP [/andP [Hwf1 Hwf2] _] Hwfc Hcrmc. 
  move: Hbb. rewrite /= Hfcet.
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwf1 Hwfc Hcrmc) => Hcrm1c1.
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
  move: (bit_blast_exp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hwf2 Hwfc1 Hcrm1c1) => Hcrm2c2.
  rewrite -(@bit_blast_exp_ccache_find_cet e1 _ _ _ _ _ _ _ _ _ _ _ He1) 
    in Hfcet; last by auto_prove_len_lt.
  rewrite -(@bit_blast_exp_ccache_find_cet e2 _ _ _ _ _ _ _ _ _ _ _ He2)
    in Hfcet; last by auto_prove_len_lt.
  move: (bit_blast_exp_ccache_in_cet He1) => [cse1c Hfcete1].
  move: (bit_blast_exp_ccache_in_het He1 Hwfc) => [cse1h Hfhete1].
  move: (bit_blast_exp_ccache_preserve_cache He2) => Hpc1c2.
  move: (preserve_find_cet Hpc1c2 Hfcete1) => {Hfcete1} Hfcete1.
  move: (preserve_find_het Hpc1c2 Hfhete1) => {Hfhete1} Hfhete1.
  move: (bit_blast_exp_ccache_in_cet He2) => [cse2c Hfcete2].      
  move: (bit_blast_exp_ccache_in_het He2 Hwfc1) => [cse2h Hfhete2].
  case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csh lsh] | ].
  - case=> <- <- _ _ _.
    apply CompCache.correct_add_cet; try done. rewrite /=.
    exists cse1c, ls1, cse2c, ls2. repeat (split; try done).
    move: (correct_find_het Hcrm2c2 Hfhet). rewrite /=.
    move=> [cs1' [ls1' [cs2' [ls2' [Hfe1 [Hfe2 Hence]]]]]].
    rewrite /find_het in Hfhete1; rewrite Hfhete1 in Hfe1.
    rewrite /find_het in Hfhete2; rewrite Hfhete2 in Hfe2.
    move: Hence. case: Hfe1 => _ <-; case: Hfe2 => _ <-. 
    done.
  - case Hr : (bit_blast_ebinop op g2 ls1 ls2) => [[gr csr] lsr].
    case=> <- <- _ _ _.
    apply CompCache.correct_add_cet_het; (try done); rewrite /=;
      [ exists cse1c, ls1, cse2c, ls2 | exists cse1h, ls1, cse2h, ls2 ];
      repeat (split; try done);
      move=> E s Hcon; exact: (bit_blast_ebinop_correct Hr).
Qed.

Lemma bit_blast_exp_ccache_correct_cache_nocet_ite :
  forall b : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        bit_blast_bexp_ccache te m c g b = (m', c', g', cs, l) ->
        QFBV.well_formed_bexp b te -> well_formed c -> 
        correct m c -> correct m' c') ->
    forall e1 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
          bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) ->
          QFBV.well_formed_exp e1 te -> well_formed c -> 
          correct m c -> correct m' c') ->
      forall e2 : QFBV.exp,
        (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
                (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
            bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls) ->
            QFBV.well_formed_exp e2 te -> well_formed c -> 
            correct m c -> correct m' c') ->
        forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
               (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
          find_cet (QFBV.Eite b e1 e2) c = None ->
          bit_blast_exp_ccache te m c g (QFBV.Eite b e1 e2) = (m', c', g', cs, ls) ->
          QFBV.well_formed_exp (QFBV.Eite b e1 e2) te ->
          well_formed c -> correct m c -> correct m' c'.
Proof.
  move=> b IHb e1 IH1 e2 IH2 te m c g m' c' g' cs ls Hfcet Hbb /= 
           /andP [/andP [/andP [Hwfb Hwf1] Hwf2] _] Hwfc Hcrmc. 
  move: Hbb. rewrite /= Hfcet.
  case Hb : (bit_blast_bexp_ccache te m c g b) => [[[[mb cb] gb] csb] lb].
  move: (IHb _ _ _ _ _ _ _ _ _ Hb Hwfb Hwfc Hcrmc) => Hcrmbcb.
  case He1 : (bit_blast_exp_ccache te mb cb gb e1) => [[[[m1 c1] g1] cs1] ls1].
  move: (bit_blast_bexp_ccache_well_formed Hb Hwfc) => Hwfcb.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwf1 Hwfcb Hcrmbcb) => Hcrm1c1.
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
  move: (bit_blast_exp_ccache_well_formed He1 Hwfcb) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hwf2 Hwfc1 Hcrm1c1) => Hcrm2c2.
  rewrite -(@bit_blast_bexp_ccache_find_cet b _ _ _ _ _ _ _ _ _ _ _ Hb) 
    in Hfcet; last by auto_prove_len_lt.
  rewrite -(@bit_blast_exp_ccache_find_cet e1 _ _ _ _ _ _ _ _ _ _ _ He1) 
    in Hfcet; last by auto_prove_len_lt.
  rewrite -(@bit_blast_exp_ccache_find_cet e2 _ _ _ _ _ _ _ _ _ _ _ He2)
    in Hfcet; last by auto_prove_len_lt.
  move: (bit_blast_bexp_ccache_in_cbt Hb) => [csbc Hfcbtb].
  move: (bit_blast_bexp_ccache_in_hbt Hb Hwfc) => [csbh Hfhbtb].
  move: (bit_blast_exp_ccache_preserve_cache He1) => Hpcbc1.
  move: (preserve_find_cbt Hpcbc1 Hfcbtb) => {Hfcbtb} Hfcbtb.
  move: (preserve_find_hbt Hpcbc1 Hfhbtb) => {Hfhbtb} Hfhbtb.
  move: (bit_blast_exp_ccache_preserve_cache He2) => Hpc1c2.
  move: (preserve_find_cbt Hpc1c2 Hfcbtb) => {Hfcbtb} Hfcbtb.
  move: (preserve_find_hbt Hpc1c2 Hfhbtb) => {Hfhbtb} Hfhbtb.
  move: (bit_blast_exp_ccache_in_cet He1) => [cse1c Hfcete1].
  move: (bit_blast_exp_ccache_in_het He1 Hwfcb) => [cse1h Hfhete1].
  move: (preserve_find_cet Hpc1c2 Hfcete1) => {Hfcete1} Hfcete1.
  move: (preserve_find_het Hpc1c2 Hfhete1) => {Hfhete1} Hfhete1.
  move: (bit_blast_exp_ccache_in_cet He2) => [cse2c Hfcete2].      
  move: (bit_blast_exp_ccache_in_het He2 Hwfc1) => [cse2h Hfhete2].
  case Hfhet : (find_het (QFBV.Eite b e1 e2) c2) => [[csh lsh] | ].
  - case=> <- <- _ _ _.
    apply CompCache.correct_add_cet; try done. rewrite /=.
    exists csbc, lb, cse1c, ls1, cse2c, ls2. repeat (split; try done).
    move: (correct_find_het Hcrm2c2 Hfhet). rewrite /=.
    move=> [csb' [lb' [cs1' [ls1' [cs2' [ls2' [Hfb [Hfe1 [Hfe2 Hence]]]]]]]]].
    rewrite /find_hbt in Hfhbtb; rewrite Hfhbtb in Hfb.
    rewrite /find_het in Hfhete1; rewrite Hfhete1 in Hfe1.
    rewrite /find_het in Hfhete2; rewrite Hfhete2 in Hfe2.
    move: Hence. case: Hfb => _ <-; case: Hfe1 => _ <-; case: Hfe2 => _ <-. 
    done.
  - case Hr : (bit_blast_ite g2 lb ls1 ls2) => [[gr csr] lsr].
    case=> <- <- _ _ _.
    apply CompCache.correct_add_cet_het; (try done); rewrite /=;
      [ exists csbc, lb, cse1c, ls1, cse2c, ls2 |
        exists csbh, lb, cse1h, ls1, cse2h, ls2 ];
      repeat (split; try done);
      move=> E s Hcon Hencb Henc1 Henc2 Hics Hsize;
      exact: (bit_blast_ite_correct Hsize Hr).
Qed.

Lemma bit_blast_bexp_ccache_correct_cache_nocbt_false :
  forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
         (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Bfalse c = None ->
    bit_blast_bexp_ccache te m c g QFBV.Bfalse = (m', c', g', cs, l) ->
    QFBV.well_formed_bexp QFBV.Bfalse te ->
    well_formed c -> correct m c -> correct m' c'.
Proof.
  move=> te m c g m' c' g' cs l. move=> Hfcbt. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Bfalse) c) => [[csh lh] | ].
  - case=> <- <- _ _ _ _ _ Hcrmc. apply CompCache.correct_add_cbt; try done.
    move: (correct_find_hbt Hcrmc Hfhbt). rewrite //=.
  - case=> <- <- _ _ _ _ _ Hcrmc.
    apply CompCache.correct_add_cbt_hbt => /=; try done;
      move=> E s Hcon; exact: add_prelude_enc_bit_ff.
Qed.

Lemma bit_blast_bexp_ccache_correct_cache_nocbt_true :
  forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
         (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Btrue c = None ->
    bit_blast_bexp_ccache te m c g QFBV.Btrue = (m', c', g', cs, l) ->
    QFBV.well_formed_bexp QFBV.Btrue te ->
    well_formed c -> correct m c -> correct m' c'.
Proof.
  move=> te m c g m' c' g' cs l. move=> Hfcbt. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Btrue) c) => [[csh lh] | ].
  - case=> <- <- _ _ _ _ _ Hcrmc. apply CompCache.correct_add_cbt; try done.
    move: (correct_find_hbt Hcrmc Hfhbt). rewrite //=.
  - case=> <- <- _ _ _ _ _ Hcrmc.
    apply CompCache.correct_add_cbt_hbt => /=; try done;
      move=> E s Hcon; exact: add_prelude_enc_bit_tt.
Qed.

Lemma bit_blast_bexp_ccache_correct_cache_nocbt_binop :
  forall (op : QFBV.bbinop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) ->
        QFBV.well_formed_exp e1 te -> well_formed c -> 
        correct m c -> correct m' c') ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
          bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls) ->
          QFBV.well_formed_exp e2 te -> well_formed c -> 
          correct m c -> correct m' c') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bbinop op e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bbinop op e1 e2) = (m', c', g', cs, l) ->
        QFBV.well_formed_bexp (QFBV.Bbinop op e1 e2) te ->
        well_formed c -> correct m c -> correct m' c'.
Proof.
  move=> op e1 IH1 e2 IH2 te m c g m' c' g' cs ls Hfcbt Hbb /= 
            /andP [/andP [Hwf1 Hwf2] _] Hwfc Hcrmc. 
  move: Hbb. rewrite /= Hfcbt.
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwf1 Hwfc Hcrmc) => Hcrm1c1.
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
  move: (bit_blast_exp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hwf2 Hwfc1 Hcrm1c1) => Hcrm2c2.
  rewrite -(@bit_blast_exp_ccache_find_cbt e1 _ _ _ _ _ _ _ _ _ _ _ He1) 
    in Hfcbt; last by auto_prove_len_lt.
  rewrite -(@bit_blast_exp_ccache_find_cbt e2 _ _ _ _ _ _ _ _ _ _ _ He2)
    in Hfcbt; last by auto_prove_len_lt.
  move: (bit_blast_exp_ccache_in_cet He1) => [cse1c Hfcete1].
  move: (bit_blast_exp_ccache_in_het He1 Hwfc) => [cse1h Hfhete1].
  move: (bit_blast_exp_ccache_preserve_cache He2) => Hpc1c2.
  move: (preserve_find_cet Hpc1c2 Hfcete1) => {Hfcete1} Hfcete1.
  move: (preserve_find_het Hpc1c2 Hfhete1) => {Hfhete1} Hfhete1.
  move: (bit_blast_exp_ccache_in_cet He2) => [cse2c Hfcete2].      
  move: (bit_blast_exp_ccache_in_het He2 Hwfc1) => [cse2h Hfhete2].
  case Hfhbt : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[csh lh] | ].
  - case=> <- <- _ _ _.
    apply CompCache.correct_add_cbt; try done. rewrite /=.
    exists cse1c, ls1, cse2c, ls2. repeat (split; try done).
    move: (correct_find_hbt Hcrm2c2 Hfhbt). rewrite /=.
    move=> [cs1' [ls1' [cs2' [ls2' [Hfe1 [Hfe2 Hence]]]]]].
    rewrite /find_het in Hfhete1; rewrite Hfhete1 in Hfe1.
    rewrite /find_het in Hfhete2; rewrite Hfhete2 in Hfe2.
    move: Hence. case: Hfe1 => _ <-; case: Hfe2 => _ <-. 
    done.
  - case Hr : (bit_blast_bbinop op g2 ls1 ls2) => [[gr csr] lr].
    case=> <- <- _ _ _.
    apply CompCache.correct_add_cbt_hbt; (try done); rewrite /=;
      [ exists cse1c, ls1, cse2c, ls2 | exists cse1h, ls1, cse2h, ls2 ];
      repeat (split; try done);
      move=> E s Hcon; exact: (bit_blast_bbinop_correct Hr).
Qed.

Lemma bit_blast_bexp_ccache_correct_cache_nocbt_lneg :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l) ->
        QFBV.well_formed_bexp e1 te -> well_formed c -> 
        correct m c -> correct m' c') ->
    forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
           (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
      find_cbt (QFBV.Blneg e1) c = None ->
      bit_blast_bexp_ccache te m c g (QFBV.Blneg e1) = (m', c', g', cs, l) ->
      QFBV.well_formed_bexp (QFBV.Blneg e1) te ->
      well_formed c -> correct m c -> correct m' c'.
Proof.
  move=> e1 IH1 te m c g m' c' g' cs l Hfcbt Hbb /= Hwf1 Hwfc Hcrmc. 
  move: Hbb. 
  rewrite /bit_blast_bexp_ccache -/bit_blast_bexp_ccache Hfcbt.
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwf1 Hwfc Hcrmc) => Hcrm1c1.
  rewrite -(@bit_blast_bexp_ccache_find_cbt e1 _ _ _ _ _ _ _ _ _ _ _ He1) 
    in Hfcbt; last by auto_prove_len_lt.
  move: (bit_blast_bexp_ccache_in_cbt He1) => [cse1c Hfcbte1].
  move: (bit_blast_bexp_ccache_in_hbt He1 Hwfc) => [cse1h Hfhbte1].
  case Hfhbt : (find_hbt (QFBV.Blneg e1) c1) => [[csh lh] | ].
  - case=> <- <- _ _ _.
    apply CompCache.correct_add_cbt; try done. rewrite /=.
    exists cse1c, l1. repeat (split; try done).
    move: (correct_find_hbt Hcrm1c1 Hfhbt). rewrite /=.
    move=> [cs1' [l1' [Hfe1 Hence]]].
    rewrite /find_hbt in Hfhbte1; rewrite Hfhbte1 in Hfe1.
    move: Hence. case: Hfe1 => _ <-.
    done.
  - case Hr : (bit_blast_lneg g1 l1) => [[gr csr] lr].
    case=> <- <- _ _ _.
    apply CompCache.correct_add_cbt_hbt; (try done);
      rewrite /=;
      [ exists cse1c, l1 | exists cse1h, l1 ];
      repeat (split; try done);
      move=> E s Hcon; exact: (bit_blast_lneg_correct Hr).
Qed.

Lemma bit_blast_bexp_ccache_correct_cache_nocbt_conj :
  forall b1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        bit_blast_bexp_ccache te m c g b1 = (m', c', g', cs, l) ->
        QFBV.well_formed_bexp b1 te -> 
        CompCache.well_formed c -> correct m c -> correct m' c') ->
    forall b2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
          bit_blast_bexp_ccache te m c g b2 = (m', c', g', cs, l) ->
          QFBV.well_formed_bexp b2 te -> 
          CompCache.well_formed c -> 
          correct m c -> correct m' c') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bconj b1 b2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bconj b1 b2) = (m', c', g', cs, l) ->
        QFBV.well_formed_bexp (QFBV.Bconj b1 b2) te ->
        CompCache.well_formed c -> correct m c -> correct m' c'.
Proof.
  move=> e1 IH1 e2 IH2 te m c g m' c' g' cs l Hfcbt Hbb /= 
            /andP [Hwf1 Hwf2] Hwfc Hcrmc. 
  move: Hbb. 
  rewrite bit_blast_bexp_ccache_equation (lock bit_blast_conj) Hfcbt /= -lock.
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwf1 Hwfc Hcrmc) => Hcrm1c1.
  case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
  move: (bit_blast_bexp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hwf2 Hwfc1 Hcrm1c1) => Hcrm2c2.
  rewrite -(@bit_blast_bexp_ccache_find_cbt e1 _ _ _ _ _ _ _ _ _ _ _ He1) 
    in Hfcbt; last by auto_prove_len_lt.
  rewrite -(@bit_blast_bexp_ccache_find_cbt e2 _ _ _ _ _ _ _ _ _ _ _ He2)
    in Hfcbt; last by auto_prove_len_lt.
  move: (bit_blast_bexp_ccache_in_cbt He1) => [cse1c Hfcbte1].
  move: (bit_blast_bexp_ccache_in_hbt He1 Hwfc) => [cse1h Hfhbte1].
  move: (bit_blast_bexp_ccache_preserve_cache He2) => Hpc1c2.
  move: (preserve_find_cbt Hpc1c2 Hfcbte1) => {Hfcbte1} Hfcbte1.
  move: (preserve_find_hbt Hpc1c2 Hfhbte1) => {Hfhbte1} Hfhbte1.
  move: (bit_blast_bexp_ccache_in_cbt He2) => [cse2c Hfcbte2].      
  move: (bit_blast_bexp_ccache_in_hbt He2 Hwfc1) => [cse2h Hfhbte2].
  case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csh lh] | ].
  - case=> <- <- _ _ _.
    apply CompCache.correct_add_cbt; try done. rewrite /=.
    exists cse1c, l1, cse2c, l2. repeat (split; try done).
    move: (correct_find_hbt Hcrm2c2 Hfhbt). rewrite /=.
    move=> [cs1' [l1' [cs2' [l2' [Hfe1 [Hfe2 Hence]]]]]].
    rewrite /find_hbt in Hfhbte1; rewrite Hfhbte1 in Hfe1.
    rewrite /find_hbt in Hfhbte2; rewrite Hfhbte2 in Hfe2.
    move: Hence. case: Hfe1 => _ <-; case: Hfe2 => _ <-. 
    done.
  - case Hr : (bit_blast_conj g2 l1 l2) => [[gr csr] lr].
    case=> <- <- _ _ _.
    apply CompCache.correct_add_cbt_hbt; (try done);
      rewrite /=;
      [ exists cse1c, l1, cse2c, l2 | exists cse1h, l1, cse2h, l2 ];
      repeat (split; try done);
      move=> E s Hcon; exact: (bit_blast_conj_correct Hr).
Qed.

Lemma bit_blast_bexp_ccache_correct_cache_nocbt_disj :
  forall b1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        bit_blast_bexp_ccache te m c g b1 = (m', c', g', cs, l) ->
        QFBV.well_formed_bexp b1 te -> 
        CompCache.well_formed c -> correct m c -> correct m' c') ->
    forall b2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
          bit_blast_bexp_ccache te m c g b2 = (m', c', g', cs, l) ->
          QFBV.well_formed_bexp b2 te -> 
          CompCache.well_formed c -> 
          correct m c -> correct m' c') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bdisj b1 b2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bdisj b1 b2) = (m', c', g', cs, l) ->
        QFBV.well_formed_bexp (QFBV.Bdisj b1 b2) te ->
        CompCache.well_formed c -> correct m c -> correct m' c'.
Proof.
  move=> e1 IH1 e2 IH2 te m c g m' c' g' cs l Hfcbt Hbb /= 
            /andP [Hwf1 Hwf2] Hwfc Hcrmc. 
  move: Hbb. 
  rewrite bit_blast_bexp_ccache_equation (lock bit_blast_disj) Hfcbt /= -lock.
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwf1 Hwfc Hcrmc) => Hcrm1c1.
  case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
  move: (bit_blast_bexp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hwf2 Hwfc1 Hcrm1c1) => Hcrm2c2.
  rewrite -(@bit_blast_bexp_ccache_find_cbt e1 _ _ _ _ _ _ _ _ _ _ _ He1) 
    in Hfcbt; last by auto_prove_len_lt.
  rewrite -(@bit_blast_bexp_ccache_find_cbt e2 _ _ _ _ _ _ _ _ _ _ _ He2)
    in Hfcbt; last by auto_prove_len_lt.
  move: (bit_blast_bexp_ccache_in_cbt He1) => [cse1c Hfcbte1].
  move: (bit_blast_bexp_ccache_in_hbt He1 Hwfc) => [cse1h Hfhbte1].
  move: (bit_blast_bexp_ccache_preserve_cache He2) => Hpc1c2.
  move: (preserve_find_cbt Hpc1c2 Hfcbte1) => {Hfcbte1} Hfcbte1.
  move: (preserve_find_hbt Hpc1c2 Hfhbte1) => {Hfhbte1} Hfhbte1.
  move: (bit_blast_bexp_ccache_in_cbt He2) => [cse2c Hfcbte2].      
  move: (bit_blast_bexp_ccache_in_hbt He2 Hwfc1) => [cse2h Hfhbte2].
  case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csh lh] | ].
  - case=> <- <- _ _ _.
    apply CompCache.correct_add_cbt; try done. rewrite /=.
    exists cse1c, l1, cse2c, l2. repeat (split; try done).
    move: (correct_find_hbt Hcrm2c2 Hfhbt). rewrite /=.
    move=> [cs1' [l1' [cs2' [l2' [Hfe1 [Hfe2 Hence]]]]]].
    rewrite /find_hbt in Hfhbte1; rewrite Hfhbte1 in Hfe1.
    rewrite /find_hbt in Hfhbte2; rewrite Hfhbte2 in Hfe2.
    move: Hence. case: Hfe1 => _ <-; case: Hfe2 => _ <-. 
    done.
  - case Hr : (bit_blast_disj g2 l1 l2) => [[gr csr] lr].
    case=> <- <- _ _ _.
    apply CompCache.correct_add_cbt_hbt; (try done);
      rewrite /=;
      [ exists cse1c, l1, cse2c, l2 | exists cse1h, l1, cse2h, l2 ];
      repeat (split; try done);
      move=> E s Hcon; exact: (bit_blast_disj_correct Hr).
Qed.

Corollary bit_blast_exp_ccache_correct_cache :
  forall (e : QFBV.exp) te m c g m' c' g' cs ls,
    bit_blast_exp_ccache te m c g e = (m', c', g', cs, ls) ->
    QFBV.well_formed_exp e te ->
    CompCache.well_formed c ->
    CompCache.correct m c ->
    CompCache.correct m' c'
  with
    bit_blast_bexp_ccache_correct_cache :
      forall (e : QFBV.bexp) te m c g m' c' g' cs l,
        bit_blast_bexp_ccache te m c g e = (m', c', g', cs, l) ->
        QFBV.well_formed_bexp e te ->
        CompCache.well_formed c ->
        CompCache.correct m c ->
        CompCache.correct m' c'.
Proof.
  (* bit_blast_exp_ccache_correct_cache *)
  set IHe := bit_blast_exp_ccache_correct_cache.
  set IHb := bit_blast_bexp_ccache_correct_cache.
  move=> e te m c g m' c' g' cs ls.
  case Hfcet: (find_cet e c) => [[cse lse] | ]. 
  - rewrite bit_blast_exp_ccache_equation Hfcet /=.
    case=> <- <- _ _ _. move=> _ _ Hcmc. 
    done.
  - move: e te m c g m' c' g' cs ls Hfcet.
    case.
    + exact: bit_blast_exp_ccache_correct_cache_nocet_var.
    + exact: bit_blast_exp_ccache_correct_cache_nocet_const.
    + move=> op e1; move: op e1 (IHe e1).
      exact: bit_blast_exp_ccache_correct_cache_nocet_unop.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_exp_ccache_correct_cache_nocet_binop.
    + move=> b e1 e2; move: b (IHb b) e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_exp_ccache_correct_cache_nocet_ite.
  (* bit_blast_bexp_ccache_correct_cache *)
  set IHe := bit_blast_exp_ccache_correct_cache.
  set IHb := bit_blast_bexp_ccache_correct_cache.
  move=> e te m c g m' c' g' cs l.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite bit_blast_bexp_ccache_equation Hfcbt /=.
    case=> <- <- _ _ _. move=> _ _ Hcmc. 
    done.
  - move: e te m c g m' c' g' cs l Hfcbt.
    case.
    + exact: bit_blast_bexp_ccache_correct_cache_nocbt_false.
    + exact: bit_blast_bexp_ccache_correct_cache_nocbt_true.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_bexp_ccache_correct_cache_nocbt_binop.
    + move=> e1; move: e1 (IHb e1).
      exact: bit_blast_bexp_ccache_correct_cache_nocbt_lneg.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: bit_blast_bexp_ccache_correct_cache_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: bit_blast_bexp_ccache_correct_cache_nocbt_disj.
Qed.


(* == bit_blast_exp_ccache_correct and bit_blast_bexp_ccache_correct *)

Lemma bit_blast_exp_ccache_correct_nocet_var :
  forall (t : SSAVarOrder.t) (te : SSATE.env) (m : vm) (c : compcache)
         (g : generator) (m' : vm) (c' : compcache) (g' : generator) 
         (cs : cnf) (ls : word) (s : SSAStore.t) (E : env),
    find_cet (QFBV.Evar t) c = None ->
    bit_blast_exp_ccache te m c g (QFBV.Evar t) = (m', c', g', cs, ls) ->
    conform_exp (QFBV.Evar t) s te ->
    consistent m' E s ->
    QFBV.well_formed_exp (QFBV.Evar t) te ->
    CompCache.well_formed c ->
    interp_cnf E (add_prelude cs) ->
    interp_cache_ct E c -> correct m c -> enc_bits E ls (QFBV.eval_exp (QFBV.Evar t) s).
Proof.
  move=> v te m c g m' c' g' cs ls s E Hfcet /=.
  rewrite Hfcet. 
  case Hfhet : (find_het (QFBV.Evar v) c) => [[csh lsh] | ].
  - case=> <- _ _ <- <-.
    move=> _ Hcon _ _ Hicsh HiEc Hcrmc.
    move: (correct_find_het Hcrmc Hfhet) => /= Hence.
    by apply Hence.
  - case Hfv : (SSAVM.find v m) => [vs | ].
    + case=> <- _ _ <- <-.
      move=> _ Hcon _ _ Hics HiEc Hcrmc.
      move: (Hcon v) => /= {Hcon}. rewrite /consistent1 Hfv. done.
    + case Hbbv: (bit_blast_var te g v) => [[vg vcs] vls].
      case=> <- _ _ <- <-.
      move=> _ Hcon _ _ Hics HiEc Hcrmc.
      move: (Hcon v) => /= {Hcon}. rewrite /consistent1.
      rewrite (SSAVM.Lemmas.find_add_eq (eq_refl v)). done.
Qed.

Lemma bit_blast_exp_ccache_correct_nocet_const :
  forall (b : bits) (te : SSATE.env) (m : vm) (c : compcache) 
         (g : generator) (m' : vm) (c' : compcache) (g' : generator) 
         (cs : cnf) (ls : word) (s : SSAStore.t) (E : env),
    find_cet (QFBV.Econst b) c = None ->
    bit_blast_exp_ccache te m c g (QFBV.Econst b) = (m', c', g', cs, ls) ->
    conform_exp (QFBV.Econst b) s te ->
    consistent m' E s ->
    QFBV.well_formed_exp (QFBV.Econst b) te ->
    well_formed c ->
    interp_cnf E (add_prelude cs) ->
    interp_cache_ct E c ->
    correct m c -> enc_bits E ls (QFBV.eval_exp (QFBV.Econst b) s).
Proof.
  move=> bs te m c g m' c' g' cs ls s E Hfcet.
  rewrite /bit_blast_exp_ccache -/bit_blast_exp_ccache Hfcet. 
  case Hfhet : (find_het (QFBV.Econst bs) c) => [[csh lsh] | ].
  - case=> <- _ _ <- <-.
    move=> _ Hcon _ _ Hicsh HiEc Hcrmc.
    move: (correct_find_het Hcrmc Hfhet) => /= Hence.
    by apply (Hence E s).
  - case Hconst : (bit_blast_const g bs) => [[gbs csbs] lsbs].
    case=> <- _ _ <- <-.
    move=> _ Hcon _ _ Hicsh HiEc Hcrmc. 
    exact: (bit_blast_const_correct Hconst).
Qed.

Lemma bit_blast_exp_ccache_correct_nocet_unop :
  forall (op : QFBV.eunop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
            (ls : word) (s : SSAStore.t) (E : env),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) ->
        conform_exp e1 s te ->
        consistent m' E s ->
        QFBV.well_formed_exp e1 te ->
        well_formed c ->
        interp_cnf E (add_prelude cs) ->
        interp_cache_ct E c -> correct m c -> enc_bits E ls (QFBV.eval_exp e1 s)) ->
    forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
           (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
           (ls : word) (s : SSAStore.t) (E : env),
      find_cet (QFBV.Eunop op e1) c = None ->
      bit_blast_exp_ccache te m c g (QFBV.Eunop op e1) = (m', c', g', cs, ls) ->
      conform_exp (QFBV.Eunop op e1) s te ->
      consistent m' E s ->
      QFBV.well_formed_exp (QFBV.Eunop op e1) te ->
      well_formed c ->
      interp_cnf E (add_prelude cs) ->
      interp_cache_ct E c ->
      correct m c -> enc_bits E ls (QFBV.eval_exp (QFBV.Eunop op e1) s).
Proof.
  move=> op e1 IH1 te m c g m' c' g' cs ls s E Hfcet Hbb Hcf Hcon Hwf Hwfc 
            Hics HiEc Hcrmc. 
  move: (bit_blast_exp_ccache_correct_cache Hbb Hwf Hwfc Hcrmc) => Hcrmpcp.
  move: (bit_blast_exp_ccache_in_cet Hbb) => [cse Hfecp].
  move: (correct_find_cet Hcrmpcp Hfecp) => {Hcrmpcp} /=.
  rewrite -!find_cet_equation.
  move=> [cs1cp [ls1cp [Hfe1cp Hence]]].
  move: (Hence E s Hcon) => {Hence} Hence.
  move: Hcf Hwf Hbb Hcon Hics => /= Hcf1 Hwf1.
  rewrite Hfcet. 
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  move: (bit_blast_exp_ccache_in_cet He1) => [cs1c1 Hfe1c1].
  case Hfhet : (find_het (QFBV.Eunop op e1) c1) => [[csh lsh] | ];
    [ | case Hop : (bit_blast_eunop op g1 ls1) => [[gop csop] lsop] ].
    all: case=> <- Hc _ <- Hls; rewrite <- Hc in *; rewrite -> Hls in *.
    all: rewrite find_cet_add_cet_eq in Hfecp;
         (rewrite find_cet_add_cet_neq in Hfe1cp; last by subexp_neq);
         (try rewrite find_cet_add_het in Hfe1cp).
    all: rewrite Hfe1c1 in Hfe1cp.
    all: move: Hence; case: Hfecp => <-; case: Hfe1cp => _ <-;
         move=> Hence Hconm1 Hcnf.
    all: move: Hcnf; 
         rewrite !add_prelude_catrev => /andP [Hics1 Hicsh].
    all: move: (bit_blast_exp_ccache_interp_cache_ct He1 HiEc Hics1) => HiEc1.
    all: move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hcf1 Hconm1 
                    Hwf1 Hwfc Hics1 HiEc Hcrmc) => Henc1.
    all: by apply Hence. 
Qed.

Lemma bit_blast_exp_ccache_correct_nocet_binop :
  forall (op : QFBV.ebinop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
            (ls : word) (s : SSAStore.t) (E : env),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) ->
        conform_exp e1 s te ->
        consistent m' E s ->
        QFBV.well_formed_exp e1 te ->
        CompCache.well_formed c ->
        interp_cnf E (add_prelude cs) ->
        interp_cache_ct E c -> 
        correct m c -> enc_bits E ls (QFBV.eval_exp e1 s)) ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
              (ls : word) (s : SSAStore.t) (E : env),
          bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls) ->
          conform_exp e2 s te ->
          consistent m' E s ->
          QFBV.well_formed_exp e2 te ->
          CompCache.well_formed c ->
          interp_cnf E (add_prelude cs) ->
          interp_cache_ct E c -> 
          correct m c -> enc_bits E ls (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
             (ls : word) (s : SSAStore.t) (E : env),
        find_cet (QFBV.Ebinop op e1 e2) c = None ->
        bit_blast_exp_ccache te m c g (QFBV.Ebinop op e1 e2) = (m', c', g', cs, ls) ->
        conform_exp (QFBV.Ebinop op e1 e2) s te ->
        consistent m' E s ->
        QFBV.well_formed_exp (QFBV.Ebinop op e1 e2) te ->
        CompCache.well_formed c ->
        interp_cnf E (add_prelude cs) ->
        interp_cache_ct E c ->
        correct m c -> enc_bits E ls (QFBV.eval_exp (QFBV.Ebinop op e1 e2) s).
Proof.  
  move=> op e1 IH1 e2 IH2 te m c g m' c' g' cs ls s E Hfcet Hbb Hcf Hcon Hwf Hwfc 
            Hics HiEc Hcrmc. 
  move: (bit_blast_exp_ccache_correct_cache Hbb Hwf Hwfc Hcrmc) => Hcrmpcp.
  move: (bit_blast_exp_ccache_in_cet Hbb) => [cse Hfecp].
  move: (correct_find_cet Hcrmpcp Hfecp) => {Hcrmpcp} /=.
  rewrite -!find_cet_equation.
  move=> [cs1cp [ls1cp [cs2cp [ls2cp [Hfe1cp [Hfe2cp Hence]]]]]].
  move: (Hence E s Hcon) => {Hence} Hence.
  move: Hcf Hwf Hbb Hcon Hics 
        => /= /andP [Hcf1 Hcf2] /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite -(eval_conform_exp_size Hwf1 Hcf1) 
          -(eval_conform_exp_size Hwf2 Hcf2) in Hsize.
  rewrite Hfcet. 
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
  move: (bit_blast_exp_ccache_in_cet He1) => [cs1c1 Hfe1c1].
  move: (bit_blast_exp_ccache_in_cet He2) => [cs2c2 Hfe2c2].
  move: (bit_blast_exp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (bit_blast_exp_ccache_preserve_cache He2) => Hpc1c2.
  move: (preserve_find_cet Hpc1c2 Hfe1c1) => {Hfe1c1} Hfe1c2.
  case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csh lsh] | ];
    [ | case Hop : (bit_blast_ebinop op g2 ls1 ls2) => [[gop csop] lsop] ].
    all: case=> <- Hc _ <- Hls; rewrite <- Hc in *; rewrite -> Hls in *.
    all: rewrite find_cet_add_cet_eq in Hfecp;
         (rewrite find_cet_add_cet_neq in Hfe1cp; last by subexp_neq);
         (try rewrite find_cet_add_het in Hfe1cp);
         (rewrite find_cet_add_cet_neq in Hfe2cp; last by subexp_neq);
         (try rewrite find_cet_add_het in Hfe2cp).
    all: rewrite Hfe1c2 in Hfe1cp; rewrite Hfe2c2 in Hfe2cp.
    all: move: Hence; case: Hfecp => <-; case: Hfe1cp => _ <-; case: Hfe2cp => _ <-; 
         move=> Hence Hconm2 Hcnf.
    all: move: (bit_blast_exp_ccache_preserve He2)=> Hpm1m2;
         move: (vm_preserve_consistent Hpm1m2 Hconm2) => {Hpm1m2} Hconm1.
    all: move: Hcnf; 
         rewrite !add_prelude_catrev => /andP [Hics1 /andP [Hics2 Hicsh]].
    all: move: (bit_blast_exp_ccache_interp_cache_ct He1 HiEc Hics1) => HiEc1.
    all: move: (bit_blast_exp_ccache_correct_cache He1 Hwf1 Hwfc Hcrmc) => Hcrm1c1.
    all: move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hcf1 Hconm1 
                    Hwf1 Hwfc Hics1 HiEc Hcrmc) => Henc1;
         move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hcf2 Hconm2 
                    Hwf2 Hwfc1 Hics2 HiEc1 Hcrm1c1) => Henc2.
    all: rewrite -(enc_bits_size Henc1) -(enc_bits_size Henc2) in Hsize.
    all: by apply Hence. 
Qed.

Lemma bit_blast_exp_ccache_correct_nocet_ite :
  forall b : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
            (l : literal) (s : SSAStore.t) (E : env),
        bit_blast_bexp_ccache te m c g b = (m', c', g', cs, l) ->
        conform_bexp b s te ->
        consistent m' E s ->
        QFBV.well_formed_bexp b te ->
        well_formed c ->
        interp_cnf E (add_prelude cs) ->
        interp_cache_ct E c -> correct m c -> enc_bit E l (QFBV.eval_bexp b s)) ->
    forall e1 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
              (ls : word) (s : SSAStore.t) (E : env),
          bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) ->
          conform_exp e1 s te ->
          consistent m' E s ->
          QFBV.well_formed_exp e1 te ->
          well_formed c ->
          interp_cnf E (add_prelude cs) ->
          interp_cache_ct E c -> correct m c -> 
          enc_bits E ls (QFBV.eval_exp e1 s)) ->
      forall e2 : QFBV.exp,
        (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
                (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
                (ls : word) (s : SSAStore.t) (E : env),
            bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls) ->
            conform_exp e2 s te ->
            consistent m' E s ->
            QFBV.well_formed_exp e2 te ->
            well_formed c ->
            interp_cnf E (add_prelude cs) ->
            interp_cache_ct E c -> correct m c -> 
            enc_bits E ls (QFBV.eval_exp e2 s)) ->
        forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
               (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
               (ls : word) (s : SSAStore.t) (E : env),
          find_cet (QFBV.Eite b e1 e2) c = None ->
          bit_blast_exp_ccache te m c g (QFBV.Eite b e1 e2) = (m', c', g', cs, ls) ->
          conform_exp (QFBV.Eite b e1 e2) s te ->
          consistent m' E s ->
          QFBV.well_formed_exp (QFBV.Eite b e1 e2) te ->
          well_formed c ->
          interp_cnf E (add_prelude cs) ->
          interp_cache_ct E c ->
          correct m c -> enc_bits E ls (QFBV.eval_exp (QFBV.Eite b e1 e2) s).
Proof.
  move=> b IHb e1 IH1 e2 IH2 te m c g m' c' g' cs ls s E Hfcet Hbb Hcf Hcon Hwf Hwfc 
            Hics HiEc Hcrmc. 
  move: (bit_blast_exp_ccache_correct_cache Hbb Hwf Hwfc Hcrmc) => Hcrmpcp.
  move: (bit_blast_exp_ccache_in_cet Hbb) => [cse Hfecp].
  move: (correct_find_cet Hcrmpcp Hfecp) => {Hcrmpcp} /=.
  rewrite -!find_cet_equation -!find_cbt_equation.
  move=> [csbcp [lbcp [cs1cp [ls1cp [cs2cp [ls2cp 
           [Hfbcp [Hfe1cp [Hfe2cp Hence]]]]]]]]].
  move: (Hence E s Hcon) => {Hence} Hence.
  move: Hcf Hwf Hbb Hcon Hics => /= /andP [/andP [Hcfb Hcf1] Hcf2] 
                                    /andP [/andP [/andP [Hwfb Hwf1] Hwf2] Hsize].
  rewrite -(eval_conform_exp_size Hwf1 Hcf1) 
          -(eval_conform_exp_size Hwf2 Hcf2) in Hsize.
  rewrite Hfcet. 
  case Hb : (bit_blast_bexp_ccache te m c g b) => [[[[mb cb] gb] csb] lb].
  case He1 : (bit_blast_exp_ccache te mb cb gb e1) => [[[[m1 c1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
  move: (bit_blast_bexp_ccache_in_cbt Hb) => [csbcb Hfbcb].
  move: (bit_blast_exp_ccache_in_cet He1) => [cs1c1 Hfe1c1].
  move: (bit_blast_exp_ccache_in_cet He2) => [cs2c2 Hfe2c2].
  move: (bit_blast_bexp_ccache_well_formed Hb Hwfc) => Hwfcb.
  move: (bit_blast_exp_ccache_well_formed He1 Hwfcb) => Hwfc1.
  move: (bit_blast_exp_ccache_preserve_cache He1) => Hpcbc1.
  move: (bit_blast_exp_ccache_preserve_cache He2) => Hpc1c2.
  move: (preserve_find_cbt Hpcbc1 Hfbcb) => {Hfbcb} Hfbc1.
  move: (preserve_find_cbt Hpc1c2 Hfbc1) => {Hfbc1} Hfbc2.
  move: (preserve_find_cet Hpc1c2 Hfe1c1) => {Hfe1c1} Hfe1c2.
  case Hfhet : (find_het (QFBV.Eite b e1 e2) c2) => [[csh lsh] | ];
    [ | case Hop : (bit_blast_ite g2 lb ls1 ls2) => [[gop csop] lsop] ].
    all: case=> <- Hc _ <- Hls; rewrite <- Hc in *; rewrite -> Hls in *.
    all: rewrite find_cet_add_cet_eq in Hfecp;
         rewrite find_cbt_add_cet in Hfbcp;
         (try rewrite find_cbt_add_het in Hfbcp);
         (rewrite find_cet_add_cet_neq in Hfe1cp; last by subexp_neq);
         (try rewrite find_cet_add_het in Hfe1cp);
         (rewrite find_cet_add_cet_neq in Hfe2cp; last by subexp_neq);
         (try rewrite find_cet_add_het in Hfe2cp).
    all: rewrite Hfbc2 in Hfbcp; rewrite Hfe1c2 in Hfe1cp; rewrite Hfe2c2 in Hfe2cp.
    all: move: Hence; case: Hfecp => <-; case: Hfbcp => _ <-; case: Hfe1cp => _ <-;
         case: Hfe2cp => _ <-; move=> Hence Hconm2 Hcnf.
    all: move: (bit_blast_exp_ccache_preserve He2)=> Hpm1m2;
         move: (vm_preserve_consistent Hpm1m2 Hconm2) => {Hpm1m2} Hconm1.
    all: move: (bit_blast_exp_ccache_preserve He1)=> Hpmbm1;
         move: (vm_preserve_consistent Hpmbm1 Hconm1) => {Hpmbm1} Hconmb.
    all: move: Hcnf; 
         rewrite !add_prelude_catrev => 
                    /andP [Hicsb /andP [Hics1 /andP [Hics2 Hicsh]]].
    all: move: (bit_blast_bexp_ccache_interp_cache_ct Hb HiEc Hicsb) => HiEcb.
    all: move: (bit_blast_bexp_ccache_correct_cache Hb Hwfb Hwfc Hcrmc) => Hcrmbcb.
    all: move: (bit_blast_exp_ccache_interp_cache_ct He1 HiEcb Hics1) => HiEc1.
    all: move: (bit_blast_exp_ccache_correct_cache He1 Hwf1 Hwfcb Hcrmbcb) => Hcrm1c1.
    all: move: (IHb _ _ _ _ _ _ _ _ _ _ _ Hb Hcfb Hconmb 
                    Hwfb Hwfc Hicsb HiEc Hcrmc) => Hencb;
         move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hcf1 Hconm1 
                    Hwf1 Hwfcb Hics1 HiEcb Hcrmbcb) => Henc1;
         move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hcf2 Hconm2 
                    Hwf2 Hwfc1 Hics2 HiEc1 Hcrm1c1) => Henc2.
    all: rewrite -(enc_bits_size Henc1) -(enc_bits_size Henc2) in Hsize.
    all: by apply Hence. 
Qed.

Lemma bit_blast_bexp_ccache_correct_nocbt_false :
  forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
         (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
         (l : literal) (s : SSAStore.t) (E : env),
    find_cbt QFBV.Bfalse c = None ->
    bit_blast_bexp_ccache te m c g QFBV.Bfalse = (m', c', g', cs, l) ->
    conform_bexp QFBV.Bfalse s te ->
    consistent m' E s ->
    QFBV.well_formed_bexp QFBV.Bfalse te ->
    well_formed c ->
    interp_cnf E (add_prelude cs) ->
    interp_cache_ct E c -> correct m c -> 
    enc_bit E l (QFBV.eval_bexp QFBV.Bfalse s).
Proof.
  move=> te m c g m' c' g' cs l s E Hfcbt. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Bfalse) c) => [[csh lh] | ].
  - case=> <- _ _ <- <-.
    move=> _ Hcon _ _ Hicsh HiEc Hcrmc.
    move: (correct_find_hbt Hcrmc Hfhbt) => /= Hence.
    by apply (Hence E s).
  - case=> <- _ _ <- <-.
    move=> _ Hcon _ _ Hicsh HiEc Hcrmc. 
    exact: (add_prelude_enc_bit_ff Hicsh).
Qed.

Lemma bit_blast_bexp_ccache_correct_nocbt_true :
  forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
         (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
         (l : literal) (s : SSAStore.t) (E : env),
    find_cbt QFBV.Btrue c = None ->
    bit_blast_bexp_ccache te m c g QFBV.Btrue = (m', c', g', cs, l) ->
    conform_bexp QFBV.Btrue s te ->
    consistent m' E s ->
    QFBV.well_formed_bexp QFBV.Btrue te ->
    well_formed c ->
    interp_cnf E (add_prelude cs) ->
    interp_cache_ct E c -> correct m c -> 
    enc_bit E l (QFBV.eval_bexp QFBV.Btrue s).
Proof.
  move=> te m c g m' c' g' cs l s E Hfcbt. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Btrue) c) => [[csh lh] | ].
  - case=> <- _ _ <- <-.
    move=> _ Hcon _ _ Hicsh HiEc Hcrmc.
    move: (correct_find_hbt Hcrmc Hfhbt) => /= Hence.
    by apply (Hence E s).
  - case=> <- _ _ <- <-.
    move=> _ Hcon _ _ Hicsh HiEc Hcrmc. 
    exact: (add_prelude_enc_bit_tt Hicsh).
Qed.

Lemma bit_blast_bexp_ccache_correct_nocbt_binop :  
  forall (op : QFBV.bbinop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
            (ls : word) (s : SSAStore.t) (E : env),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) ->
        conform_exp e1 s te ->
        consistent m' E s ->
        QFBV.well_formed_exp e1 te ->
        well_formed c ->
        interp_cnf E (add_prelude cs) ->
        interp_cache_ct E c -> correct m c -> enc_bits E ls (QFBV.eval_exp e1 s)) ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
              (ls : word) (s : SSAStore.t) (E : env),
          bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls) ->
          conform_exp e2 s te ->
          consistent m' E s ->
          QFBV.well_formed_exp e2 te ->
          well_formed c ->
          interp_cnf E (add_prelude cs) ->
          interp_cache_ct E c -> correct m c -> 
          enc_bits E ls (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
             (l : literal) (s : SSAStore.t) (E : env),
        find_cbt (QFBV.Bbinop op e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bbinop op e1 e2) = (m', c', g', cs, l) ->
        conform_bexp (QFBV.Bbinop op e1 e2) s te ->
        consistent m' E s ->
        QFBV.well_formed_bexp (QFBV.Bbinop op e1 e2) te ->
        well_formed c ->
        interp_cnf E (add_prelude cs) ->
        interp_cache_ct E c ->
        correct m c -> enc_bit E l (QFBV.eval_bexp (QFBV.Bbinop op e1 e2) s).
Proof.
  move=> op e1 IH1 e2 IH2 te m c g m' c' g' cs l s E Hfcbt Hbb Hcf Hcon Hwf Hwfc 
            Hics HiEc Hcrmc. 
  move: (bit_blast_bexp_ccache_correct_cache Hbb Hwf Hwfc Hcrmc) => Hcrmpcp.
  move: (bit_blast_bexp_ccache_in_cbt Hbb) => [cse Hfecp].
  move: (correct_find_cbt Hcrmpcp Hfecp) => {Hcrmpcp} /=.
  rewrite -!find_cet_equation.
  move=> [cs1cp [ls1cp [cs2cp [ls2cp [Hfe1cp [Hfe2cp Hence]]]]]].
  move: (Hence E s Hcon) => {Hence} Hence.
  move: Hcf Hwf Hbb Hcon Hics 
        => /= /andP [Hcf1 Hcf2] /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite -(eval_conform_exp_size Hwf1 Hcf1) 
          -(eval_conform_exp_size Hwf2 Hcf2) in Hsize.
  rewrite Hfcbt. 
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
  move: (bit_blast_exp_ccache_in_cet He1) => [cs1c1 Hfe1c1].
  move: (bit_blast_exp_ccache_in_cet He2) => [cs2c2 Hfe2c2].
  move: (bit_blast_exp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (bit_blast_exp_ccache_preserve_cache He2) => Hpc1c2.
  move: (preserve_find_cet Hpc1c2 Hfe1c1) => {Hfe1c1} Hfe1c2.
  case Hfhbt : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[csh lh] | ];
    [ | case Hop : (bit_blast_bbinop op g2 ls1 ls2) => [[gop csop] lop] ].
    all: case=> <- Hc _ <- Hls; rewrite <- Hc in *; rewrite -> Hls in *.
    all: rewrite find_cbt_add_cbt_eq in Hfecp;
         rewrite find_cet_add_cbt in Hfe1cp;
         (try rewrite find_cet_add_hbt in Hfe1cp);
         rewrite find_cet_add_cbt in Hfe2cp;
         (try rewrite find_cet_add_hbt in Hfe2cp).
    all: rewrite Hfe1c2 in Hfe1cp; rewrite Hfe2c2 in Hfe2cp.
    all: move: Hence; case: Hfecp => <-; case: Hfe1cp => _ <-; case: Hfe2cp => _ <-; 
         move=> Hence Hconm2 Hcnf.
    all: move: (bit_blast_exp_ccache_preserve He2)=> Hpm1m2;
         move: (vm_preserve_consistent Hpm1m2 Hconm2) => {Hpm1m2} Hconm1.
    all: move: Hcnf; 
         rewrite !add_prelude_catrev => /andP [Hics1 /andP [Hics2 Hicsh]].
    all: move: (bit_blast_exp_ccache_interp_cache_ct He1 HiEc Hics1) => HiEc1.
    all: move: (bit_blast_exp_ccache_correct_cache He1 Hwf1 Hwfc Hcrmc) => Hcrm1c1.
    all: move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hcf1 Hconm1 
                    Hwf1 Hwfc Hics1 HiEc Hcrmc) => Henc1;
         move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hcf2 Hconm2 
                    Hwf2 Hwfc1 Hics2 HiEc1 Hcrm1c1) => Henc2.
    all: rewrite -(enc_bits_size Henc1) -(enc_bits_size Henc2) in Hsize.
    all: by apply Hence. 
Qed.

Lemma bit_blast_bexp_ccache_correct_nocbt_lneg :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
            (l : literal) (s : SSAStore.t) (E : env),
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l) ->
        conform_bexp e1 s te ->
        consistent m' E s ->
        QFBV.well_formed_bexp e1 te ->
        well_formed c ->
        interp_cnf E (add_prelude cs) ->
        interp_cache_ct E c -> correct m c -> enc_bit E l (QFBV.eval_bexp e1 s)) ->
    forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
           (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
           (l : literal) (s : SSAStore.t) (E : env),
      find_cbt (QFBV.Blneg e1) c = None ->
      bit_blast_bexp_ccache te m c g (QFBV.Blneg e1) = (m', c', g', cs, l) ->
      conform_bexp (QFBV.Blneg e1) s te ->
      consistent m' E s ->
      QFBV.well_formed_bexp (QFBV.Blneg e1) te ->
      well_formed c ->
      interp_cnf E (add_prelude cs) ->
      interp_cache_ct E c ->
      correct m c -> enc_bit E l (QFBV.eval_bexp (QFBV.Blneg e1) s).
Proof.
  move=> e1 IH1 te m c g m' c' g' cs l s E Hfcbt Hbb Hcf Hcon Hwf Hwfc 
            Hics HiEc Hcrmc. 
  move: (bit_blast_bexp_ccache_correct_cache Hbb Hwf Hwfc Hcrmc) => Hcrmpcp.
  move: (bit_blast_bexp_ccache_in_cbt Hbb) => [cse Hfecp].
  move: (correct_find_cbt Hcrmpcp Hfecp) => {Hcrmpcp} /=.
  rewrite -!find_cbt_equation.
  move=> [cs1cp [l1cp [Hfe1cp Hence]]].
  move: (Hence E s Hcon) => {Hence} Hence.
  move: Hcf Hwf => /= Hcf1 Hwf1.
  move: Hbb Hcon Hics; rewrite /bit_blast_bexp_ccache -/bit_blast_bexp_ccache Hfcbt. 
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  move: (bit_blast_bexp_ccache_in_cbt He1) => [cs1c1 Hfe1c1].
  case Hfhbt : (find_hbt (QFBV.Blneg e1) c1) => [[csh lh] | ];
    [ | case Hop : (bit_blast_lneg g1 l1) => [[gop csop] lop] ].
    all: case=> <- Hc _ <- Hls; rewrite <- Hc in *; rewrite -> Hls in *.
    all: rewrite find_cbt_add_cbt_eq in Hfecp;
         (rewrite find_cbt_add_cbt_neq in Hfe1cp; last by subexp_neq);
         (try rewrite find_cbt_add_hbt in Hfe1cp).
    all: rewrite Hfe1c1 in Hfe1cp.
    all: move: Hence; case: Hfecp => <-; case: Hfe1cp => _ <-;
         move=> Hence Hconm1 Hcnf.
    all: move: Hcnf; 
         rewrite !add_prelude_catrev => /andP [Hics1 Hicsh].
    all: move: (bit_blast_bexp_ccache_interp_cache_ct He1 HiEc Hics1) => HiEc1.
    all: move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hcf1 Hconm1 
                    Hwf1 Hwfc Hics1 HiEc Hcrmc) => Henc1.
    all: by apply Hence. 
Qed.

Lemma bit_blast_bexp_ccache_correct_nocbt_conj :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
            (l : literal) (s : SSAStore.t) (E : env),
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l) ->
        conform_bexp e1 s te ->
        consistent m' E s ->
        QFBV.well_formed_bexp e1 te ->
        well_formed c ->
        interp_cnf E (add_prelude cs) ->
        interp_cache_ct E c -> correct m c -> enc_bit E l (QFBV.eval_bexp e1 s)) ->
    forall e2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
              (l : literal) (s : SSAStore.t) (E : env),
          bit_blast_bexp_ccache te m c g e2 = (m', c', g', cs, l) ->
          conform_bexp e2 s te ->
          consistent m' E s ->
          QFBV.well_formed_bexp e2 te ->
          well_formed c ->
          interp_cnf E (add_prelude cs) ->
          interp_cache_ct E c -> correct m c -> enc_bit E l (QFBV.eval_bexp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
             (l : literal) (s : SSAStore.t) (E : env),
        find_cbt (QFBV.Bconj e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bconj e1 e2) = (m', c', g', cs, l) ->
        conform_bexp (QFBV.Bconj e1 e2) s te ->
        consistent m' E s ->
        QFBV.well_formed_bexp (QFBV.Bconj e1 e2) te ->
        well_formed c ->
        interp_cnf E (add_prelude cs) ->
        interp_cache_ct E c ->
        correct m c -> enc_bit E l (QFBV.eval_bexp (QFBV.Bconj e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m c g m' c' g' cs l s E Hfcbt Hbb Hcf Hcon Hwf Hwfc 
            Hics HiEc Hcrmc. 
  move: (bit_blast_bexp_ccache_correct_cache Hbb Hwf Hwfc Hcrmc) => Hcrmpcp.
  move: (bit_blast_bexp_ccache_in_cbt Hbb) => [cse Hfecp].
  move: (correct_find_cbt Hcrmpcp Hfecp) => {Hcrmpcp} /=.
  rewrite -!find_cbt_equation.
  move=> [cs1cp [l1cp [cs2cp [l2cp [Hfe1cp [Hfe2cp Hence]]]]]].
  move: (Hence E s Hcon) => {Hence} Hence.
  move: Hcf Hwf => /= /andP [Hcf1 Hcf2] /andP [Hwf1 Hwf2].
  move: Hbb Hcon Hics; rewrite /bit_blast_bexp_ccache -/bit_blast_bexp_ccache Hfcbt. 
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
  move: (bit_blast_bexp_ccache_in_cbt He1) => [cs1c1 Hfe1c1].
  move: (bit_blast_bexp_ccache_in_cbt He2) => [cs2c2 Hfe2c2].
  move: (bit_blast_bexp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (bit_blast_bexp_ccache_preserve_cache He2) => Hpc1c2.
  move: (preserve_find_cbt Hpc1c2 Hfe1c1) => {Hfe1c1} Hfe1c2.
  case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csh lh] | ];
    [ | case Hop : (bit_blast_conj g2 l1 l2) => [[gop csop] lop] ].
    all: case=> <- Hc _ <- Hls; rewrite <- Hc in *; rewrite -> Hls in *.
    all: rewrite find_cbt_add_cbt_eq in Hfecp;
         (rewrite find_cbt_add_cbt_neq in Hfe1cp; last by subexp_neq);
         (try rewrite find_cbt_add_hbt in Hfe1cp);
         (rewrite find_cbt_add_cbt_neq in Hfe2cp; last by subexp_neq);
         (try rewrite find_cbt_add_hbt in Hfe2cp).
    all: rewrite Hfe1c2 in Hfe1cp; rewrite Hfe2c2 in Hfe2cp.
    all: move: Hence; case: Hfecp => <-; case: Hfe1cp => _ <-; case: Hfe2cp => _ <-; 
         move=> Hence Hconm2 Hcnf.
    all: move: (bit_blast_bexp_ccache_preserve He2)=> Hpm1m2;
         move: (vm_preserve_consistent Hpm1m2 Hconm2) => {Hpm1m2} Hconm1.
    all: move: Hcnf; 
         rewrite !add_prelude_catrev => /andP [Hics1 /andP [Hics2 Hicsh]].
    all: move: (bit_blast_bexp_ccache_interp_cache_ct He1 HiEc Hics1) => HiEc1.
    all: move: (bit_blast_bexp_ccache_correct_cache He1 Hwf1 Hwfc Hcrmc) => Hcrm1c1.
    all: move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hcf1 Hconm1 
                    Hwf1 Hwfc Hics1 HiEc Hcrmc) => Henc1;
         move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hcf2 Hconm2 
                    Hwf2 Hwfc1 Hics2 HiEc1 Hcrm1c1) => Henc2.
    all: by apply Hence. 
Qed.

Lemma bit_blast_bexp_ccache_correct_nocbt_disj :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
            (l : literal) (s : SSAStore.t) (E : env),
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l) ->
        conform_bexp e1 s te ->
        consistent m' E s ->
        QFBV.well_formed_bexp e1 te ->
        well_formed c ->
        interp_cnf E (add_prelude cs) ->
        interp_cache_ct E c -> correct m c -> enc_bit E l (QFBV.eval_bexp e1 s)) ->
    forall e2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
              (l : literal) (s : SSAStore.t) (E : env),
          bit_blast_bexp_ccache te m c g e2 = (m', c', g', cs, l) ->
          conform_bexp e2 s te ->
          consistent m' E s ->
          QFBV.well_formed_bexp e2 te ->
          well_formed c ->
          interp_cnf E (add_prelude cs) ->
          interp_cache_ct E c -> correct m c -> enc_bit E l (QFBV.eval_bexp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) 
             (l : literal) (s : SSAStore.t) (E : env),
        find_cbt (QFBV.Bdisj e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bdisj e1 e2) = (m', c', g', cs, l) ->
        conform_bexp (QFBV.Bdisj e1 e2) s te ->
        consistent m' E s ->
        QFBV.well_formed_bexp (QFBV.Bdisj e1 e2) te ->
        well_formed c ->
        interp_cnf E (add_prelude cs) ->
        interp_cache_ct E c ->
        correct m c -> enc_bit E l (QFBV.eval_bexp (QFBV.Bdisj e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m c g m' c' g' cs l s E Hfcbt Hbb Hcf Hcon Hwf Hwfc 
            Hics HiEc Hcrmc. 
  move: (bit_blast_bexp_ccache_correct_cache Hbb Hwf Hwfc Hcrmc) => Hcrmpcp.
  move: (bit_blast_bexp_ccache_in_cbt Hbb) => [cse Hfecp].
  move: (correct_find_cbt Hcrmpcp Hfecp) => {Hcrmpcp} /=.
  rewrite -!find_cbt_equation.
  move=> [cs1cp [l1cp [cs2cp [l2cp [Hfe1cp [Hfe2cp Hence]]]]]].
  move: (Hence E s Hcon) => {Hence} Hence.
  move: Hcf Hwf => /= /andP [Hcf1 Hcf2] /andP [Hwf1 Hwf2].
  move: Hbb Hcon Hics; rewrite /bit_blast_bexp_ccache -/bit_blast_bexp_ccache Hfcbt. 
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
  move: (bit_blast_bexp_ccache_in_cbt He1) => [cs1c1 Hfe1c1].
  move: (bit_blast_bexp_ccache_in_cbt He2) => [cs2c2 Hfe2c2].
  move: (bit_blast_bexp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (bit_blast_bexp_ccache_preserve_cache He2) => Hpc1c2.
  move: (preserve_find_cbt Hpc1c2 Hfe1c1) => {Hfe1c1} Hfe1c2.
  case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csh lh] | ];
    [ | case Hop : (bit_blast_disj g2 l1 l2) => [[gop csop] lop] ].
    all: case=> <- Hc _ <- Hls; rewrite <- Hc in *; rewrite -> Hls in *.
    all: rewrite find_cbt_add_cbt_eq in Hfecp;
         (rewrite find_cbt_add_cbt_neq in Hfe1cp; last by subexp_neq);
         (try rewrite find_cbt_add_hbt in Hfe1cp);
         (rewrite find_cbt_add_cbt_neq in Hfe2cp; last by subexp_neq);
         (try rewrite find_cbt_add_hbt in Hfe2cp).
    all: rewrite Hfe1c2 in Hfe1cp; rewrite Hfe2c2 in Hfe2cp.
    all: move: Hence; case: Hfecp => <-; case: Hfe1cp => _ <-; case: Hfe2cp => _ <-; 
         move=> Hence Hconm2 Hcnf.
    all: move: (bit_blast_bexp_ccache_preserve He2)=> Hpm1m2;
         move: (vm_preserve_consistent Hpm1m2 Hconm2) => {Hpm1m2} Hconm1.
    all: move: Hcnf; 
         rewrite !add_prelude_catrev => /andP [Hics1 /andP [Hics2 Hicsh]].
    all: move: (bit_blast_bexp_ccache_interp_cache_ct He1 HiEc Hics1) => HiEc1.
    all: move: (bit_blast_bexp_ccache_correct_cache He1 Hwf1 Hwfc Hcrmc) => Hcrm1c1.
    all: move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hcf1 Hconm1 
                    Hwf1 Hwfc Hics1 HiEc Hcrmc) => Henc1;
         move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hcf2 Hconm2 
                    Hwf2 Hwfc1 Hics2 HiEc1 Hcrm1c1) => Henc2.
    all: by apply Hence. 
Qed.

Corollary bit_blast_exp_ccache_correct :
  forall (e : QFBV.exp) te m c g m' c' g' cs ls s E,
    bit_blast_exp_ccache te m c g e = (m', c', g', cs, ls) ->
    AdhereConform.conform_exp e s te ->
    consistent m' E s ->
    QFBV.well_formed_exp e te ->
    CompCache.well_formed c ->
    interp_cnf E (add_prelude cs) -> CompCache.interp_cache_ct E c ->
    CompCache.correct m c -> enc_bits E ls (QFBV.eval_exp e s)
  with
    bit_blast_bexp_ccache_correct :
      forall (e : QFBV.bexp) te m c g m' c' g' cs l s E,
        bit_blast_bexp_ccache te m c g e = (m', c', g', cs, l) ->
        AdhereConform.conform_bexp e s te ->
        consistent m' E s ->
        QFBV.well_formed_bexp e te ->
        CompCache.well_formed c ->
        interp_cnf E (add_prelude cs) -> CompCache.interp_cache_ct E c ->
        CompCache.correct m c -> enc_bit E l (QFBV.eval_bexp e s).
Proof.
  (* bit_blast_exp_ccache_correct *)
  set IHe := bit_blast_exp_ccache_correct.
  set IHb := bit_blast_bexp_ccache_correct.
  move=> e te m c g m' c' g' cs ls s E.
  case Hfcet: (find_cet e c) => [[cse lse] | ]. 
  - rewrite bit_blast_exp_ccache_equation Hfcet /=.
    case=> <- _ _ <- <-. move=> Hcf Hcon Hwf _ Hics HiEc Hcrmc.
    move: (add_prelude_tt Hics) => {Hics} Htt.
    exact: (interp_cache_ct_find_cet_some_correct Hcon Htt HiEc Hfcet Hwf Hcf Hcrmc).
  - move: e te m c g m' c' g' cs ls s E Hfcet.
    case.
    + exact: bit_blast_exp_ccache_correct_nocet_var.
    + exact: bit_blast_exp_ccache_correct_nocet_const.
    + move=> op e1; move: op e1 (IHe e1).
      exact: bit_blast_exp_ccache_correct_nocet_unop.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_exp_ccache_correct_nocet_binop.
    + move=> b e1 e2; move: b (IHb b) e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_exp_ccache_correct_nocet_ite.
  (* bit_blast_bexp_ccache_correct *)
  set IHe := bit_blast_exp_ccache_correct.
  set IHb := bit_blast_bexp_ccache_correct.
  move=> e te m c g m' c' g' cs l s E.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite bit_blast_bexp_ccache_equation Hfcbt /=.
    case=> <- _ _ <- <-. move=> Hcf Hcon Hwf _ Hics HiEc Hcrmc.
    move: (add_prelude_tt Hics) => {Hics} Htt.
    exact: (interp_cache_ct_find_cbt_some_correct Hcon Htt HiEc Hfcbt Hwf Hcf Hcrmc).
  - move: e te m c g m' c' g' cs l s E Hfcbt.
    case.
    + exact: bit_blast_bexp_ccache_correct_nocbt_false.
    + exact: bit_blast_bexp_ccache_correct_nocbt_true.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_bexp_ccache_correct_nocbt_binop.
    + move=> e1; move: e1 (IHb e1).
      exact: bit_blast_bexp_ccache_correct_nocbt_lneg.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: bit_blast_bexp_ccache_correct_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: bit_blast_bexp_ccache_correct_nocbt_disj.
Qed.



(** ============================ **)
(*
Lemma bit_blast_exp_cache_correct_nocache_var :
  forall (t : SSAVarOrder.t) (te : SSATE.env) (m : SSAVM.t word) 
         (ca : cache) (g : generator) (s : SSAStore.t) (E : env) 
         (m' : vm) (ca' : cache) (g' : generator) (cs : cnf) (lrs : word),
    find_cet (QFBV.Evar t) ca = None ->
    find_het (QFBV.Evar t) ca = None ->
    bit_blast_exp_cache te m ca g (QFBV.Evar t) = (m', ca', g', cs, lrs) ->
    conform_exp (QFBV.Evar t) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Evar t) te ->
    well_formed ca ->
    correct E s ca ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Evar t) s) /\ correct E s ca'.
Proof.
  move=> v te im ica ig s E om oca og ocs olrs. 
  move=> Hfcet Hfhet Hblast _ Hcon _ Hwf Hwfica HcEsica.
  move: (Hcon v) Hblast => {Hcon} Hcon. rewrite /= Hfcet Hfhet.
  case Hfind: (SSAVM.find v im).
  - case=> Hm Hca Hg Hcs Hlrs. move: Hcon; rewrite /consistent1.
    rewrite -Hm -Hca Hfind Hlrs /=. 
    move=> Henc. split; first done.
    apply correct_add_het. split; last done. by rewrite -correct_add_cet.
  - case Hblast: (bit_blast_var te ig v) => [[vg vcs] vlrs].
    case=> [Hom Hoca Hog Hocs Holrs]. move: Hcon; rewrite /consistent1.
    rewrite -Hom -Hoca. rewrite (SSAVM.Lemmas.find_add_eq (eq_refl v)).
    rewrite Holrs /=. move=> Henc. split; first done.
    apply correct_add_het. split; last done. by rewrite -correct_add_cet.
Qed.

Lemma bit_blast_exp_cache_correct_nocache_and :
  forall e : QFBV.exp,
    (forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
            (g : generator) (s : SSAStore.t) (E : env) (m' : vm) 
            (ca' : cache) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp_cache te m ca g e = (m', ca', g', cs, lrs) ->
        conform_exp e s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e te ->
        well_formed ca ->
        correct E s ca -> 
        enc_bits E lrs (QFBV.eval_exp e s) /\ correct E s ca') ->
    forall e0 : QFBV.exp,
      (forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
              (g : generator) (s : SSAStore.t) (E : env) (m' : vm) 
              (ca' : cache) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp_cache te m ca g e0 = (m', ca', g', cs, lrs) ->
          conform_exp e0 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e0 te ->
          well_formed ca ->
          correct E s ca -> 
          enc_bits E lrs (QFBV.eval_exp e0 s) /\ correct E s ca') ->
      forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
             (g : generator) (s : SSAStore.t) (E : env) (m' : vm) 
             (ca' : cache) (g' : generator) (cs : cnf) (lrs : word),
        find_cet (QFBV.Ebinop QFBV.Band e e0) ca = None ->
        find_het (QFBV.Ebinop QFBV.Band e e0) ca = None ->
        bit_blast_exp_cache te m ca g (QFBV.Ebinop QFBV.Band e e0) =
        (m', ca', g', cs, lrs) ->
  conform_exp (QFBV.Ebinop QFBV.Band e e0) s te ->
  consistent m' E s ->
  interp_cnf E (add_prelude cs) ->
  QFBV.well_formed_exp (QFBV.Ebinop QFBV.Band e e0) te ->
  well_formed ca ->
  correct E s ca ->
  enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Band e e0) s) /\ correct E s ca'.
Proof.
  move=> e1 IH1 e2 IH2 te m ca g s E m' ca' g' cs lrs Hfcet Hfhet.
  rewrite (lock interp_cnf) /= -lock Hfcet Hfhet /=.
  case He1 : (bit_blast_exp_cache te m ca g e1) => [[[[m1 ca1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_cache te m1 ca1 g1 e2) => [[[[m2 ca2] g2] cs2] ls2].
  case Hr : (bit_blast_and g2 ls1 ls2) => [[gr csr] lsr].
  case=> <- <- _ <- <-. move=> /andP [Hcf1 Hcf2] Hcons2.
  move: (vm_preserve_consistent (bit_blast_exp_cache_preserve He2) Hcons2) => Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_cache_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_catrev. move/andP=> [Hic1 /andP [Hic2 Hicr]] .
  move => /andP [/andP [Hwf1 Hwf2] _] .
  move=> Hwfca.
  move: (bit_blast_exp_cache_well_formed He1 Hwfca) => Hwfca1.
  move: (bit_blast_exp_cache_well_formed He2 Hwfca1) => Hwfca2.
  move=> HcEsca.
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcons1 Hic1 Hwf1 Hwfca HcEsca) 
  => [Henc1 HcEsca1].
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcons2 Hic2 Hwf2 Hwfca1 HcEsca1) 
  => [Henc2 HcEsca2].
  have Hencr : enc_bits E lsr (QFBV.eval_exp e1 s &&# QFBV.eval_exp e2 s)%bits
    by apply: (bit_blast_and_correct Hr _ _ Hicr).    
  split; first done.
  (* correct E s ca' *)
  apply correct_add_het. split; last done. by apply correct_add_cet. 
Qed.

Lemma bit_blast_bexp_cache_correct_cache_conj :
forall b1 : QFBV.bexp,
  (forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
          (g : generator) (s : SSAStore.t) (E : env) (m' : vm) 
          (ca' : cache) (g' : generator) (cs : cnf) (lr : literal),
      bit_blast_bexp_cache te m ca g b1 = (m', ca', g', cs, lr) ->
      conform_bexp b1 s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_bexp b1 te ->
      well_formed ca ->
      correct E s ca -> 
      enc_bit E lr (QFBV.eval_bexp b1 s) /\ correct E s ca') ->
  forall b2 : QFBV.bexp,
    (forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
            (g : generator) (s : SSAStore.t) (E : env) (m' : vm) 
            (ca' : cache) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp_cache te m ca g b2 = (m', ca', g', cs, lr) ->
        conform_bexp b2 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp b2 te ->
        well_formed ca ->
        correct E s ca -> 
        enc_bit E lr (QFBV.eval_bexp b2 s) /\ correct E s ca') ->
    forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
           (g : generator) (s : SSAStore.t) (E : env) (m' : vm) 
           (ca' : cache) (g' : generator) (cs : cnf) (lr : literal),
      find_cbt (QFBV.Bconj b1 b2) ca = None ->
      find_hbt (QFBV.Bconj b1 b2) ca = None ->
      bit_blast_bexp_cache te m ca g (QFBV.Bconj b1 b2) = (m', ca', g', cs, lr) ->
      conform_bexp (QFBV.Bconj b1 b2) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_bexp (QFBV.Bconj b1 b2) te ->
      well_formed ca ->
      correct E s ca ->
      enc_bit E lr (QFBV.eval_bexp (QFBV.Bconj b1 b2) s) /\ correct E s ca'.
Proof.
  move=> e1 IH1 e2 IH2 te m ca g s E m' ca' g' cs lr Hfcbt Hfhbt.
  rewrite /bit_blast_bexp_cache /= -/bit_blast_bexp_cache Hfcbt Hfhbt. 
  case Hblast1: (bit_blast_bexp_cache te m ca g e1) => [[[[m1 ca1] g1] cs1] r1].
  case Hblast2: (bit_blast_bexp_cache te m1 ca1 g1 e2) => [[[[m2 ca2] g2] cs2] r2].
  case=> <- <- _ <- <- /andP [Hcf1 Hcf2] Hcon.
  rewrite !add_prelude_catrev .
  move => /andP [Hcs1 /andP [Hcs2 Hocs]] /andP [Hwf1 Hwf2] .
  move: (vm_preserve_consistent (bit_blast_bexp_cache_preserve Hblast2) Hcon) 
  => Hcon1.
  move: (vm_preserve_consistent (bit_blast_bexp_cache_preserve Hblast1) Hcon1) 
  => Hcon0.
  move=> Hwfca.
  move: (bit_blast_bexp_cache_well_formed Hblast1 Hwfca) => Hwfca1.
  move: (bit_blast_bexp_cache_well_formed Hblast2 Hwfca1) => Hwfca2.
  move=> HcEsca.
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon1 Hcs1 Hwf1 Hwfca HcEsca) 
  => [Henc1 HcEsca1].
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2 Hwfca1 HcEsca1) 
  => [Henc2 HcEsca2].
  have Hencr : enc_bit E (Pos g2) (QFBV.eval_bexp e1 s && QFBV.eval_bexp e2 s)
    by apply : (@bit_blast_conj_correct g2 _ _ _ _ _ _ _ _ _ Henc1 Henc2 Hocs) .
  split; first done.
  (* correct E s ca' *)
  apply correct_add_hbt. split; last done. by apply correct_add_cbt. 
Qed.


Corollary bit_blast_exp_cache_correct_cache :
  forall (e : QFBV.exp) te m ca g s E m' ca' g' cs lrs,
    bit_blast_exp_cache te m ca g e = (m', ca', g', cs, lrs) ->
    AdhereConform.conform_exp e s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp e te ->
    Cache.well_formed ca -> Cache.correct E s ca ->
    enc_bits E lrs (QFBV.eval_exp e s) /\ Cache.correct E s ca'
  with
    bit_blast_bexp_cache_correct_cache :
      forall (e : QFBV.bexp) te m ca g s E m' ca' g' cs lr,
        bit_blast_bexp_cache te m ca g e = (m', ca', g', cs, lr) ->
        AdhereConform.conform_bexp e s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp e te ->
        Cache.well_formed ca -> Cache.correct E s ca ->
        enc_bit E lr (QFBV.eval_bexp e s) /\ Cache.correct E s ca'.
Proof.
  (* bit_blast_exp_cache_correct_cache *)
  move=> e te m ca g s E m' ca' g' cs lrs.
  case Hfcet: (find_cet e ca) => [ls|]. 
  - rewrite bit_blast_exp_cache_equation Hfcet /=.
    case=> _ <- _ _ <-. move=> _ _ _ _ Hwfca HcEsca. 
    split; last done.
    move: (Cache.correct_well_formed_correct_ct HcEsca Hwfca) => [Hct _].
    by apply (Hct _ _ Hfcet).
  - case Hfhet: (find_het e ca) => [[csh lsh]|].
    + rewrite bit_blast_exp_cache_equation Hfcet Hfhet /=. 
      case=> _ <- _ _ <-. move=> _ _ _ _ _ HcEsca.
      split; last by rewrite -correct_add_cet.
      move: HcEsca => [Hht _]. by apply (Hht _ _ _ Hfhet).
    + move: e te m ca g s E m' ca' g' cs lrs Hfcet Hfhet.
      case.
      * exact: bit_blast_exp_cache_correct_nocache_var.
      * admit. (* bit_blast_exp_const  *)
      * elim. 
        -- admit. (* bit_blast_exp_not *)
        -- admit. (* bit_blast_exp_neg *)
        -- admit. (* bit_blast_exp_extract *)
        -- admit. (* bit_blast_exp_high *)
        -- admit. (* bit_blast_exp_low *)
        -- admit. (* bit_blast_exp_zeroextend *)
        -- admit. (* : bit_blast_exp_signextend; apply bit_blast_exp_correct . *)
      * elim.
        -- move=> e1 e2; apply bit_blast_exp_cache_correct_nocache_and;
                    by apply bit_blast_exp_cache_correct_cache.
        -- admit. (* apply : bit_blast_exp_or; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_xor; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_add; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_sub; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_mul; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_mod; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_srem; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_smod; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_shl; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_lshr; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_ashr; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_concat; apply bit_blast_exp_correct . *)
      * admit. (* move => b e1 e2; *)
      (* apply bit_blast_exp_ite; *)
      (* first apply : bit_blast_bexp_correct; *)
      (* apply : bit_blast_exp_correct . *)
  (* bit_blast_bexp_cache_correct_cache *)
  move=> e te m ca g s E m' ca' g' cs lr.
  case Hfcbt: (find_cbt e ca) => [l|]. 
  - rewrite bit_blast_bexp_cache_equation Hfcbt /=.
    case=> _ <- _ _ <-. move=> _ _ _ _ Hwfca HcEsca. 
    split; last done.
    move: (Cache.correct_well_formed_correct_ct HcEsca Hwfca) => [_ Hct].
    by apply (Hct _ _ Hfcbt).
  - case Hfhbt: (find_hbt e ca) => [[csh lh]|].
    + rewrite bit_blast_bexp_cache_equation Hfcbt Hfhbt /=. 
      case=> _ <- _ _ <-. move=> _ _ _ _ _ HcEsca.
      split; last by rewrite -correct_add_cbt.
      move: HcEsca => [_ Hht]. by apply (Hht _ _ _ Hfhbt).
    + move: e te m ca g s E m' ca' g' cs lr Hfcbt Hfhbt.
      case.
      * admit. (* exact : bit_blast_bexp_false . *)
      * admit. (* exact : bit_blast_bexp_true . *)
      * elim => e1 e2 .
        -- admit. (* apply : bit_blast_bexp_eq; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_ult; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_ule; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_ugt; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_uge; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_slt; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_sle; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_sgt; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_sge; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_uaddo; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_usubo; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_umulo; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_saddo; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_ssubo; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_smulo; apply : bit_blast_exp_correct . *)
      * admit. (* apply : bit_blast_bexp_lneg . *)
      * move=> b1 b2; apply: bit_blast_bexp_cache_correct_cache_conj;
                 by apply: bit_blast_bexp_cache_correct_cache.
      * admit. (* apply : bit_blast_bexp_disj . *)
Admitted.


(* = bit_blast_exp_cache_correct and bit_blast_bexp_cache_correct = *)

Corollary bit_blast_exp_cache_correct :
  forall (e : QFBV.exp) te m ca g s E m' ca' g' cs lrs,
    bit_blast_exp_cache te m ca g e = (m', ca', g', cs, lrs) ->
    AdhereConform.conform_exp e s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp e te ->
    Cache.well_formed ca -> Cache.correct E s ca ->
    enc_bits E lrs (QFBV.eval_exp e s).
Proof. 
  move=> e te m ca g s E m' ca' g' cs lrs Hbb Hcf Hcon Hcnf Hwf Hwfca Hcr. 
  move: (bit_blast_exp_cache_correct_cache Hbb Hcf Hcon Hcnf Hwf Hwfca Hcr) => [H _].
  done.
Qed.

Corollary bit_blast_bexp_cache_correct :
  forall (e : QFBV.bexp) te m ca g s E m' ca' g' cs lr,
    bit_blast_bexp_cache te m ca g e = (m', ca', g', cs, lr) ->
    AdhereConform.conform_bexp e s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp e te ->
    Cache.well_formed ca -> Cache.correct E s ca ->
    enc_bit E lr (QFBV.eval_bexp e s).
Proof.
  move=> e te m ca g s E m' ca' g' cs lr Hbb Hcf Hcon Hcnf Hwf Hwfca Hcr. 
  move: (bit_blast_bexp_cache_correct_cache Hbb Hcf Hcon Hcnf Hwf Hwfca Hcr) => [H _].
  done.
Qed.
*)


(* ============== strong_correct =============== *)
(*
Lemma bit_blast_exp_cache_in_cache_find_cet_some :
  forall e te m ca g m' ca' g' cs' lrs' ls,
  bit_blast_exp_cache te m ca g e = (m', ca', g', cs', lrs') ->
  Cache.well_formed ca ->
  find_cet e ca = Some ls -> 
  (exists cs, find_het e ca' = Some (cs, ls) /\ cs' = [::] /\ lrs' = ls).
Proof.
Admitted.

Lemma bit_blast_exp_cache_in_cache_find_cet_none :
  forall e te m ca g m' ca' g' cs' lrs' ls,
  bit_blast_exp_cache te m ca g e = (m', ca', g', cs', lrs') ->
  Cache.well_formed ca ->
  find_cet e ca = None -> 
  (exists cs, find_het e ca' = Some (cs, ls) /\ cs' = cs /\ lrs' = ls).
Proof.
Admitted.

Lemma bit_blast_exp_cache_in_cache :
  forall e te m ca g m' ca' g' cs' lrs' ls,
  bit_blast_exp_cache te m ca g e = (m', ca', g', cs', lrs') ->
  Cache.well_formed ca ->
  (exists cs, find_het e ca' = Some (cs, ls) 
              /\ (cs' = [::] \/ cs' = cs) /\ lrs' = ls).
Proof.
Admitted.

Lemma bit_blast_exp_cache_strong_correct_nocache_var :
forall (t : SSAVarOrder.t) (te : SSATE.env) (m : SSAVM.t word) 
       (ca : cache) (g : generator) (m' : vm) (ca' : cache) 
       (g' : generator) (cs : cnf) (lrs : word),
  find_cet (QFBV.Evar t) ca = None ->
  find_het (QFBV.Evar t) ca = None ->
  bit_blast_exp_cache te m ca g (QFBV.Evar t) = (m', ca', g', cs, lrs) ->
  QFBV.well_formed_exp (QFBV.Evar t) te ->
  strong_correct m ca -> strong_correct m' ca'.
Proof.
  move=> v te im ica ig om oca og ocs olrs. 
  move=> Hfcet Hfhet Hblast Hwf Hcimica.
  move: Hblast. rewrite /= Hfcet Hfhet.
  case Hfind: (SSAVM.find v im).
  - case=> <- <- _ _ _. 
    apply strong_correct_add_het. split; first by rewrite -strong_correct_add_cet.
    rewrite /enc_correct_exp.
    move=> E s Hcon _. move: (Hcon v). 
    rewrite /consistent1. rewrite Hfind. done.
  - case Hblast: (bit_blast_var te ig v) => [[vg vcs] vlrs].
    case=> <- <- _ _ _.
    apply strong_correct_add_het. 
    move: (vm_preserve_add_diag vlrs Hfind) => Hpim.
    move: (vm_preserve_strong_correct Hpim Hcimica) => Hcaimica.
    split; first by rewrite -strong_correct_add_cet.
    rewrite /enc_correct_exp. move=> E s Hcon _.
    move: (Hcon v). rewrite /consistent1. 
    rewrite (SSAVM.Lemmas.find_add_eq (eq_refl v)).
    done.
Qed.
*)

(*
Lemma bit_blast_exp_cache_strong_correct_nocache_and :
  forall e1 : QFBV.exp,
    (forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
            (g : generator) (m' : vm) (ca' : cache) (g' : generator) 
            (cs : cnf) (lrs : word),
        bit_blast_exp_cache te m ca g e1 = (m', ca', g', cs, lrs) ->
        QFBV.well_formed_exp e1 te -> strong_correct m ca -> 
        strong_correct m' ca') ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
              (g : generator) (m' : vm) (ca' : cache) (g' : generator) 
              (cs : cnf) (lrs : word),
          bit_blast_exp_cache te m ca g e2 = (m', ca', g', cs, lrs) ->
          QFBV.well_formed_exp e2 te -> strong_correct m ca -> 
          strong_correct m' ca') ->
      forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
             (g : generator) (m' : vm) (ca' : cache) (g' : generator) 
             (cs : cnf) (lrs : word),
        find_cet (QFBV.Ebinop QFBV.Band e1 e2) ca = None ->
        find_het (QFBV.Ebinop QFBV.Band e1 e2) ca = None ->
        bit_blast_exp_cache te m ca g (QFBV.Ebinop QFBV.Band e1 e2) =
        (m', ca', g', cs, lrs) ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Band e1 e2) te ->
        strong_correct m ca -> strong_correct m' ca'.
Proof.
  move=> e1 IH1 e2 IH2 te m ca g m' ca' g' cs lrs Hfcet Hfhet.
  rewrite /= Hfcet Hfhet /=.
  case He1 : (bit_blast_exp_cache te m ca g e1) => [[[[m1 ca1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_cache te m1 ca1 g1 e2) => [[[[m2 ca2] g2] cs2] ls2].
  case Hr : (bit_blast_and g2 ls1 ls2) => [[gr csr] lsr].
  case=> <- <- _ _ _. move => /andP [/andP [Hwf1 Hwf2] _] Hcmca.
  apply strong_correct_add_het.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwf1 Hcmca) => Hcm1ca1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hwf2 Hcm1ca1) => Hcm2ca2.
  split; first by rewrite -strong_correct_add_cet.
  rewrite /enc_correct_exp. move=> E s Hconm2. 
  rewrite !add_prelude_catrev. move/andP=> [Hic1 /andP [Hic2 Hicr]] .
  

  case He1 : (bit_blast_exp_cache te m ca g e1) => [[[[m1 ca1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_cache te m1 ca1 g1 e2) => [[[[m2 ca2] g2] cs2] ls2].
  case Hr : (bit_blast_and g2 ls1 ls2) => [[gr csr] lsr].
  case=> <- <- _ <- <-. move=> /andP [Hcf1 Hcf2] Hcons2.
  move: (vm_preserve_consistent (bit_blast_exp_cache_preserve He2) Hcons2) => Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_cache_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_catrev. move/andP=> [Hic1 /andP [Hic2 Hicr]] .
  move => /andP [/andP [Hwf1 Hwf2] _] .
  move=> Hwfca.
  move: (bit_blast_exp_cache_well_formed He1 Hwfca) => Hwfca1.
  move: (bit_blast_exp_cache_well_formed He2 Hwfca1) => Hwfca2.
  move=> HcEsca.
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcons1 Hic1 Hwf1 Hwfca HcEsca) 
  => [Henc1 HcEsca1].
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcons2 Hic2 Hwf2 Hwfca1 HcEsca1) 
  => [Henc2 HcEsca2].
  have Hencr : enc_bits E lsr (QFBV.eval_exp e1 s &&# QFBV.eval_exp e2 s)%bits
    by apply: (bit_blast_and_correct Hr _ _ Hicr).    
  split; first done.
  (* correct E s ca' *)
  apply correct_add_het. split; last done. by apply correct_add_cet. 
Qed.
*)


(*
Corollary bit_blast_exp_cache_strong_correct :
  forall (e : QFBV.exp) te m ca g m' ca' g' cs lrs,
    bit_blast_exp_cache te m ca g e = (m', ca', g', cs, lrs) ->
    QFBV.well_formed_exp e te ->
    (* Cache.well_formed ca ->  *)
    strong_correct m ca ->
    strong_correct m' ca'
  with
    bit_blast_bexp_cache_strong_correct :
      forall (e : QFBV.bexp) te m ca g m' ca' g' cs lr,
        bit_blast_bexp_cache te m ca g e = (m', ca', g', cs, lr) ->
        QFBV.well_formed_bexp e te ->
        (* Cache.well_formed ca ->  *)
        strong_correct m ca ->
        strong_correct m' ca'.
Proof.
  (* bit_blast_exp_cache_strong_correct *)
  move=> e te m ca g m' ca' g' cs lrs.
  case Hfcet: (find_cet e ca) => [ls|]. 
  - rewrite bit_blast_exp_cache_equation Hfcet /=.
    case=> <- <- _ _ _. move=> _ Hcmca. 
    done.
  - case Hfhet: (find_het e ca) => [[csh lsh]|].
    + rewrite bit_blast_exp_cache_equation Hfcet Hfhet /=. 
      case=> <- <- _ _ _ _ Hcmca.
      by rewrite -strong_correct_add_cet.
    + move: e te m ca g m' ca' g' cs lrs Hfcet Hfhet.
      case.
      * exact: bit_blast_exp_cache_strong_correct_nocache_var.
      * admit. (* bit_blast_exp_const  *)
      * elim. 
        -- admit. (* bit_blast_exp_not *)
        -- admit. (* bit_blast_exp_neg *)
        -- admit. (* bit_blast_exp_extract *)
        -- admit. (* bit_blast_exp_high *)
        -- admit. (* bit_blast_exp_low *)
        -- admit. (* bit_blast_exp_zeroextend *)
        -- admit. (* : bit_blast_exp_signextend; apply bit_blast_exp_correct . *)
      * elim.
        -- move=> e1 e2; move: e1 (bit_blast_exp_cache_strong_correct e1)
e2 (bit_blast_exp_cache_strong_correct e2).

 move=> e1 e2; apply bit_blast_exp_cache_correct_nocache_and;
                    by apply bit_blast_exp_cache_correct_cache.
        -- admit. (* apply : bit_blast_exp_or; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_xor; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_add; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_sub; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_mul; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_mod; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_srem; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_smod; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_shl; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_lshr; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_ashr; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_concat; apply bit_blast_exp_correct . *)
      * admit. (* move => b e1 e2; *)
      (* apply bit_blast_exp_ite; *)
      (* first apply : bit_blast_bexp_correct; *)
      (* apply : bit_blast_exp_correct . *)
  (* bit_blast_bexp_cache_correct_cache *)
  move=> e te m ca g s E m' ca' g' cs lr.
  case Hfcbt: (find_cbt e ca) => [l|]. 
  - rewrite bit_blast_bexp_cache_equation Hfcbt /=.
    case=> _ <- _ _ <-. move=> _ _ _ _ Hwfca HcEsca. 
    split; last done.
    move: (Cache.correct_well_formed_correct_ct HcEsca Hwfca) => [_ Hct].
    by apply (Hct _ _ Hfcbt).
  - case Hfhbt: (find_hbt e ca) => [[csh lh]|].
    + rewrite bit_blast_bexp_cache_equation Hfcbt Hfhbt /=. 
      case=> _ <- _ _ <-. move=> _ _ _ _ _ HcEsca.
      split; last by rewrite -correct_add_cbt.
      move: HcEsca => [_ Hht]. by apply (Hht _ _ _ Hfhbt).
    + move: e te m ca g s E m' ca' g' cs lr Hfcbt Hfhbt.
      case.
      * admit. (* exact : bit_blast_bexp_false . *)
      * admit. (* exact : bit_blast_bexp_true . *)
      * elim => e1 e2 .
        -- admit. (* apply : bit_blast_bexp_eq; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_ult; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_ule; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_ugt; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_uge; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_slt; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_sle; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_sgt; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_sge; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_uaddo; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_usubo; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_umulo; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_saddo; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_ssubo; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_smulo; apply : bit_blast_exp_correct . *)
      * admit. (* apply : bit_blast_bexp_lneg . *)
      * move=> b1 b2; apply: bit_blast_bexp_cache_correct_cache_conj;
                 by apply: bit_blast_bexp_cache_correct_cache.
      * admit. (* apply : bit_blast_bexp_disj . *)
Admitted.




Corollary bit_blast_bexp_cache_correct_test :
  forall (e : QFBV.bexp) te m ca g m' ca' g' cs lr,
    bit_blast_bexp_cache te m ca g e = (m', ca', g', cs, lr) ->
    (* AdhereConform.conform_bexp e s te -> *)
    QFBV.well_formed_bexp e te ->
    Cache.well_formed ca -> strong_correct m ca ->    
    enc_correct_bexp m' e cs lr /\ strong_correct m' ca'.
Proof.
Admitted.

*)




(* = mk_env_exp_cache_correct and mk_env_bexp_cache_correct = *)
(*
Corollary mk_env_exp_cache_correct :
  forall (e : QFBV.exp) te m ca s E g m' ca' E' g' cs lrs,
    mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
    AdhereConform.conform_exp e s te ->
    consistent m' E' s ->
    interp_cnf E' (add_prelude cs) ->
    QFBV.well_formed_exp e te ->
    Cache.well_formed ca -> Cache.correct E s ca ->
    Cache.correct E' s ca'.
Proof. 
  move=> e te m ca s E g m' ca' E' g' cs lrs Hmk Hcf Hcon Hcnf Hwf Hwfca Hcr. 
  move: (mk_env_exp_cache_is_bit_blast_exp_cache Hcf Hwf Hmk) => Hbb.
  move: (bit_blast_exp_cache_correct_cache Hbb Hcf Hcon Hcnf Hwf Hwfca Hcr) => [H _].
  done.
Qed.


Corollary bit_blast_bexp_cache_correct :
  forall (e : QFBV.bexp) te m ca g s E m' ca' g' cs lr,
    bit_blast_bexp_cache te m ca g e = (m', ca', g', cs, lr) ->
    AdhereConform.conform_bexp e s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp e te ->
    Cache.well_formed ca -> Cache.correct E s ca ->
    enc_bit E lr (QFBV.eval_bexp e s).
Proof.
  move=> e te m ca g s E m' ca' g' cs lr Hbb Hcf Hcon Hcnf Hwf Hwfca Hcr. 
  move: (bit_blast_bexp_cache_correct_cache Hbb Hcf Hcon Hcnf Hwf Hwfca Hcr) => [H _].
  done.
Qed.
*)
