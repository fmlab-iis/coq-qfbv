From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF Cache BBExport
     BitBlastingCacheDef BitBlastingCacheWF BitBlastingCacheNewer BitBlastingCachePreserve BitBlastingCorrect .

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* = mk_env_exp_cache_regular and mk_env_bexp_cache_regular = *)

Lemma mk_env_exp_cache_regular_var :
  forall t (m : vm) (ca : cache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
         (g' : generator) (cs : cnf) (lrs : word),
    mk_env_exp_cache m ca s E g (QFBV.Evar t) = (m', ca', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    (* QFBV.well_formed_exp (QFBV.Evar t) te ->  *)
    Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
    interp_cnf E' cs /\ regular E' ca'.
Proof.
  move=> v m ca s E g m' ca' E' g' cs lrs /=. 
  case Hfcet: (find_cet (QFBV.Evar v) ca) => [ls|].
  - case=> _ <- <- _ <- _ Hnew_gm Hnew_gtt _ _ //=.
  - case Hfhet: (find_het (QFBV.Evar v) ca) => [[csh lsh]|].
    + case=> _ <- <- _ <- _ Hnew_gm Hnew_gtt _ _ Hreg_Eca. 
      split; last by rewrite -regular_add_cet.
      move: Hreg_Eca => [Hreg_Eca _]. exact: (Hreg_Eca _ _ _ Hfhet). 
    + case Hfind: (SSAVM.find v m).
      * case=> _ <- <- _ <- _ Hnew_gm Hnew_gtt _ _ Hreg_Eca.
        split; first done. 
        apply regular_add_het. split; first by apply regular_add_cet.
        done.
      * case Henv: (mk_env_var E g (SSAStore.acc v s) v) => [[[E_v g_v] cs_v] lrs_v].
        case=> _ <- <- _ <- _ Hnew_gm Hnew_gtt _ Hnew_gca Hreg_Eca. 
        split; first exact: (mk_env_var_sat Henv).
        (* regular E' ca' *)
        apply regular_add_het. split; last exact: (mk_env_var_sat Henv).
        apply regular_add_cet. 
        move: (mk_env_var_preserve Henv) => HpEEvg.
        by rewrite (env_preserve_regular HpEEvg Hnew_gca).
Qed.

Lemma mk_env_exp_cache_regular_const :
  forall (b : bits) (m : vm) (ca : cache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (ca' : cache) 
         (E' : env) (g' : generator) (cs : cnf) (lrs : word),
    mk_env_exp_cache m ca s E g (QFBV.Econst b) = (m', ca', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    (* QFBV.well_formed_exp (QFBV.Econst b) te ->  *)
    Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
    interp_cnf E' cs /\ regular E' ca'.
Proof.
  move=> bs m ca s E g m' ca' E' g' cs lrs /=. 
  case Hfcet: (find_cet (QFBV.Econst bs) ca) => [ls|].
  - case=> _ <- <- _ <- _ Hnew_gm Hnew_gtt _ _ Hreg_Eca //=.
  - case Hfhet: (find_het (QFBV.Econst bs) ca) => [[csh lsh]|].
    + case=> _ <- <- _ <- _ Hnew_gm Hnew_gtt _ _ Hreg_Eca.
      split; last by rewrite -regular_add_cet.
      move: Hreg_Eca => [Hreg_Eca _]. exact: (Hreg_Eca _ _ _ Hfhet). 
    + case=> _ <- <- _ <- _ Hnew_gm Hnew_gtt _ Hnew_gca Hreg_Eca. 
      split; first done.
      (* regular E' ca' *)
      apply regular_add_het. split; last done.
      apply regular_add_cet. done.
Qed.

Lemma mk_env_exp_cache_regular_not :
  forall e : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te ->  *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall (m : vm) (ca : cache) (s : SSAStore.t) 
           (E : env) (g : generator) (m' : vm) (ca' : cache) 
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp_cache m ca s E g (QFBV.Eunop QFBV.Unot e) = 
      (m', ca', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      (* QFBV.well_formed_exp (QFBV.Eunop QFBV.Unot e) te -> *)
      Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
      interp_cnf E' cs /\ regular E' ca'.
Proof.
  move=> e1 IH1 m ca s E g m' ca' E' g' cs lrs /=.
  case Hfcet: (find_cet (QFBV.Eunop QFBV.Unot e1) ca) => [ls|].
  - case=> _ <- <- _ <- _ Hnew_gm Hnew_gtt _ _ Hreg_Eca //=.
  - case Hfhet: (find_het (QFBV.Eunop QFBV.Unot e1) ca) => [[csh lsh]|].
    + case=> _ <- <- _ <- _ Hnew_gm Hnew_gtt _ _ Hreg_Eca.
      split; last by rewrite -regular_add_cet.
      move: Hreg_Eca => [Hreg_Eca _]. exact: (Hreg_Eca _ _ _ Hfhet). 
    + case Hmke1 : (mk_env_exp_cache m ca s E g e1) 
      => [[[[[m1 ca1] E1] g1] cs1] ls1].
      case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
      case=> _ <- <- _ <- _ Hgm Hgt Hwfca Hgca HrEca.
      have Hcnf : interp_cnf Er (cs1 ++ csr).
      {
        rewrite !interp_cnf_cat.
        (* interp_cnf Er cs1 *)
        move: (IH1 _ _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwfca Hgca HrEca) 
        => [HiE1c1 _].
        move: (mk_env_not_preserve Hmkr) => HpE1Erg1.
        move: (mk_env_exp_cache_newer_cnf Hmke1 Hgm Hgt Hwfca Hgca) => Hg1c1.
        rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
        (* interp_cnf Er csr *)
        move: (mk_env_exp_cache_newer_res Hmke1 Hgm Hgt Hwfca Hgca) => Hg1l1.
        exact: (mk_env_not_sat Hmkr Hg1l1).
      }
      split; first done.
      (* regular E' ca' *)
      apply regular_add_het. split; last done. apply regular_add_cet. 
      move: (IH1 _ _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwfca Hgca HrEca) 
      => [_ HrE1ca1].
      move: (mk_env_not_preserve Hmkr) => HpE1Erg1.
      move: (mk_env_exp_cache_newer_cache Hmke1 Hgm Hgt Hwfca Hgca) => Hg1ca1.
      by rewrite (env_preserve_regular HpE1Erg1 Hg1ca1).
Qed.

Lemma mk_env_exp_cache_regular_neg :
  forall e : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall (m : vm) (ca : cache) (s : SSAStore.t) 
           (E : env) (g : generator) (m' : vm) (ca' : cache) 
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp_cache m ca s E g (QFBV.Eunop QFBV.Uneg e) = 
      (m', ca', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      (* QFBV.well_formed_exp (QFBV.Eunop QFBV.Uneg e) te -> *)
      Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
      interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_exp_cache_regular_extract :
  forall (n n0 : nat) (e : QFBV.exp),
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall (m : vm) (ca : cache) (s : SSAStore.t) 
           (E : env) (g : generator) (m' : vm) (ca' : cache) 
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp_cache m ca s E g (QFBV.Eunop (QFBV.Uextr n n0) e) =
      (m', ca', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      (* QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uextr n n0) e) te -> *)
      Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
      interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_exp_cache_regular_high :
  forall (n : nat) (e : QFBV.exp),
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall (m : vm) (ca : cache) (s : SSAStore.t) 
           (E : env) (g : generator) (m' : vm) (ca' : cache) 
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp_cache m ca s E g (QFBV.Eunop (QFBV.Uhigh n) e) =
      (m', ca', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      (* QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uhigh n) e) te -> *)
      Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
      interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_exp_cache_regular_low :
  forall (n : nat) (e : QFBV.exp),
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall (m : vm) (ca : cache) (s : SSAStore.t) 
           (E : env) (g : generator) (m' : vm) (ca' : cache) 
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp_cache m ca s E g (QFBV.Eunop (QFBV.Ulow n) e) =
      (m', ca', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      (* QFBV.well_formed_exp (QFBV.Eunop (QFBV.Ulow n) e) te -> *)
      Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
      interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_exp_cache_regular_zeroextend :
  forall (n : nat) (e : QFBV.exp),
    (forall (m : vm) (ca : cache) (s : SSAStore.t)
            (E : env) (g : generator) (m' : vm) (ca' : cache)
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall (m : vm) (ca : cache) (s : SSAStore.t) 
           (E : env) (g : generator) (m' : vm) (ca' : cache) 
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp_cache m ca s E g (QFBV.Eunop (QFBV.Uzext n) e) =
      (m', ca', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      (* QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uzext n) e) te -> *)
      Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
      interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_exp_cache_regular_signextend :
  forall (n : nat) (e : QFBV.exp),
    (forall (m : vm) (ca : cache) (s : SSAStore.t)
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall (m : vm) (ca : cache) (s : SSAStore.t) 
           (E : env) (g : generator) (m' : vm) (ca' : cache) 
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp_cache m ca s E g (QFBV.Eunop (QFBV.Usext n) e) =
      (m', ca', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      (* QFBV.well_formed_exp (QFBV.Eunop (QFBV.Usext n) e) te -> *)
      Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
      interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_exp_cache_regular_and :
  forall e : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t)
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e0 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t)
              (E : env) (g : generator) (m' : vm) (ca' : cache) 
              (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          (* QFBV.well_formed_exp e0 te -> *)
          Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) 
             (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g (QFBV.Ebinop QFBV.Band e e0) =
        (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp (QFBV.Ebinop QFBV.Band e e0) te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
  move=> e1 IH1 e2 IH2 m ca s E g m' ca' E' g' cs lrs /=.
  case Hfcet: (find_cet (QFBV.Ebinop QFBV.Band e1 e2) ca) => [ls|].
  - case=> _ <- <- _ <- _ Hnew_gm Hnew_gtt _ _ Hreg_Eca //=.
  - case Hfhet: (find_het (QFBV.Ebinop QFBV.Band e1 e2) ca) => [[csh lsh]|].
    + case=> _ <- <- _ <- _ Hnew_gm Hnew_gtt _ _ Hreg_Eca.
      split; last by rewrite -regular_add_cet.
      move: Hreg_Eca => [Hreg_Eca _]. exact: (Hreg_Eca _ _ _ Hfhet). 
    + case Hmke1 : (mk_env_exp_cache m ca s E g e1) 
      => [[[[[m1 ca1] E1] g1] cs1] ls1].
      case Hmke2 : (mk_env_exp_cache m1 ca1 s E1 g1 e2) 
      => [[[[[m2 ca2] E2] g2] cs2] ls2].
      case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
      case=> _ <- <- _ <- _ Hgm Hgt /= Hwfca Hgca HrEca.
      move: (IH1 _ _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwfca Hgca HrEca) 
      => [HiE1c1 HrE1ca1].
      move: (mk_env_exp_cache_newer_vm Hmke1 Hgm) => Hg1m1.
      move: (mk_env_exp_cache_newer_gen Hmke1) => Hgg1.
      move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
      move: (mk_env_exp_cache_well_formed Hmke1 Hwfca) => Hwfca1.
      move: (mk_env_exp_cache_newer_cache Hmke1 Hgm Hgt Hwfca Hgca) => Hg1ca1.
      move: (IH2 _ _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwfca1 Hg1ca1 HrE1ca1) 
      => [HiE2c2 HrE2ca2].
      have Hcnf : interp_cnf Er (cs1 ++ cs2 ++ csr).
      {
        rewrite !interp_cnf_cat.
        (* interp_cnf Er cs1 *)
        move: (mk_env_exp_cache_preserve Hmke2) => HpE1E2g1.
        move: (mk_env_and_preserve Hmkr) => HpE2Erg2.
        move: (mk_env_exp_cache_newer_gen Hmke2) => Hg1g2.
        move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
        move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
        move: (mk_env_exp_cache_newer_cnf Hmke1 Hgm Hgt Hwfca Hgca) => Hg1c1.
        rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
        (* interp_cnf Er cs2 *)
        move: (mk_env_exp_cache_newer_cnf Hmke2 Hg1m1 Hg1t Hwfca1 Hg1ca1) => Hg2c2.
        rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
        (* interp_cnf Er csr *)
        move: (mk_env_exp_cache_newer_res Hmke1 Hgm Hgt Hwfca Hgca) => Hg1l1.
        move: (mk_env_exp_cache_newer_res Hmke2 Hg1m1 Hg1t Hwfca1 Hg1ca1) => Hg2l2.
        move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
        move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
        exact: (mk_env_and_sat Hmkr Hg2t Hg2l1 Hg2l2).
      }
      split; first done.
      (* regular E' ca' *)
      apply regular_add_het. split; last done. apply regular_add_cet. 
      move: (mk_env_and_preserve Hmkr) => HpE2Erg2.
      move: (mk_env_exp_cache_newer_cache Hmke2 Hg1m1 Hg1t Hwfca1 Hg1ca1) => Hg2ca2.
      by rewrite (env_preserve_regular HpE2Erg2 Hg2ca2).
Qed.

Lemma mk_env_exp_cache_regular_or :
  forall e : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t)
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e0 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t)
              (E : env) (g : generator) (m' : vm) (ca' : cache) 
              (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          (* QFBV.well_formed_exp e0 te -> *)
          Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) 
             (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g (QFBV.Ebinop QFBV.Bor e e0) =
        (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bor e e0) te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_exp_cache_regular_xor :
  forall e : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t)
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e0 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t)
              (E : env) (g : generator) (m' : vm) (ca' : cache) 
              (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          (* QFBV.well_formed_exp e0 te -> *)
          Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) 
             (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g (QFBV.Ebinop QFBV.Bxor e e0) =
        (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bxor e e0) te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_exp_cache_regular_add :
  forall e : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t)
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e0 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t)
              (E : env) (g : generator) (m' : vm) (ca' : cache) 
              (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          (* QFBV.well_formed_exp e0 te -> *)
          Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) 
             (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g (QFBV.Ebinop QFBV.Badd e e0) =
        (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp (QFBV.Ebinop QFBV.Badd e e0) te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_exp_cache_regular_sub :
  forall e : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t)
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e0 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t)
              (E : env) (g : generator) (m' : vm) (ca' : cache) 
              (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          (* QFBV.well_formed_exp e0 te -> *)
          Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) 
             (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g (QFBV.Ebinop QFBV.Bsub e e0) =
        (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsub e e0) te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_exp_cache_regular_mul :
  forall e : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t)
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e0 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t)
              (E : env) (g : generator) (m' : vm) (ca' : cache) 
              (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          (* QFBV.well_formed_exp e0 te -> *)
          Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) 
             (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g (QFBV.Ebinop QFBV.Bmul e e0) =
        (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bmul e e0) te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_exp_cache_regular_mod :
  forall e : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t)
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e0 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t)
              (E : env) (g : generator) (m' : vm) (ca' : cache) 
              (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          (* QFBV.well_formed_exp e0 te -> *)
          Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) 
             (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g (QFBV.Ebinop QFBV.Bmod e e0) =
        (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bmod e e0) te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_exp_cache_regular_srem :
  forall e : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t)
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e0 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t)
              (E : env) (g : generator) (m' : vm) (ca' : cache) 
              (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          (* QFBV.well_formed_exp e0 te -> *)
          Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) 
             (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g (QFBV.Ebinop QFBV.Bsrem e e0) =
        (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsrem e e0) te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_exp_cache_regular_smod :
  forall e : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t)
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e0 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t)
              (E : env) (g : generator) (m' : vm) (ca' : cache) 
              (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          (* QFBV.well_formed_exp e0 te -> *)
          Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) 
             (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g (QFBV.Ebinop QFBV.Bsmod e e0) =
        (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsmod e e0) te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_exp_cache_regular_shl :
  forall e : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t)
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e0 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t)
              (E : env) (g : generator) (m' : vm) (ca' : cache) 
              (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          (* QFBV.well_formed_exp e0 te -> *)
          Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) 
             (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g (QFBV.Ebinop QFBV.Bshl e e0) =
        (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bshl e e0) te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_exp_cache_regular_lshr :
  forall e : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t)
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e0 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t)
              (E : env) (g : generator) (m' : vm) (ca' : cache) 
              (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          (* QFBV.well_formed_exp e0 te -> *)
          Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) 
             (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g (QFBV.Ebinop QFBV.Blshr e e0) =
        (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp (QFBV.Ebinop QFBV.Blshr e e0) te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_exp_cache_regular_ashr :
  forall e : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t)
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e0 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t)
              (E : env) (g : generator) (m' : vm) (ca' : cache) 
              (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          (* QFBV.well_formed_exp e0 te -> *)
          Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) 
             (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g (QFBV.Ebinop QFBV.Bashr e e0) =
        (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bashr e e0) te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_exp_cache_regular_concat :
  forall e : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t)
            (E : env) (g : generator) (m' : vm) (ca' : cache) 
            (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e0 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t)
              (E : env) (g : generator) (m' : vm) (ca' : cache) 
              (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          (* QFBV.well_formed_exp e0 te -> *)
          Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) 
             (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g (QFBV.Ebinop QFBV.Bconcat e e0) =
        (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bconcat e e0) te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_exp_cache_regular_ite :
  forall (b : QFBV.bexp),
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g b = (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e0 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed ca ->
          newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g (QFBV.Eite b e e0) = 
        (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_false :
  forall (m : vm) (ca : cache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
         (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp_cache m ca s E g QFBV.Bfalse = (m', ca', E', g', cs, lr) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    well_formed ca ->
    newer_than_cache g ca -> regular E ca -> 
    interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_true :
  forall (m : vm) (ca : cache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
         (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp_cache m ca s E g QFBV.Btrue = (m', ca', E', g', cs, lr) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    well_formed ca ->
    newer_than_cache g ca -> regular E ca -> 
    interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_eq :
  forall e0 : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e1 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed ca ->
          newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g (QFBV.Bbinop QFBV.Beq e0 e1) =
        (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_ult :
  forall e0 : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e1 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed ca ->
          newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g (QFBV.Bbinop QFBV.Bult e0 e1) =
        (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_ule :
  forall e0 : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e1 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed ca ->
          newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g (QFBV.Bbinop QFBV.Bule e0 e1) =
        (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_ugt :
  forall e0 : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e1 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed ca ->
          newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g (QFBV.Bbinop QFBV.Bugt e0 e1) =
        (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_uge :
  forall e0 : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e1 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed ca ->
          newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g (QFBV.Bbinop QFBV.Buge e0 e1) =
        (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_slt :
  forall e0 : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e1 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed ca ->
          newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g (QFBV.Bbinop QFBV.Bslt e0 e1) =
        (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_sle :
  forall e0 : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e1 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed ca ->
          newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g (QFBV.Bbinop QFBV.Bsle e0 e1) =
        (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_sgt :
  forall e0 : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e1 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed ca ->
          newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g (QFBV.Bbinop QFBV.Bsgt e0 e1) =
        (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_sge :
  forall e0 : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e1 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed ca ->
          newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g (QFBV.Bbinop QFBV.Bsge e0 e1) =
        (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_uaddo :
  forall e0 : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e1 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed ca ->
          newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g (QFBV.Bbinop QFBV.Buaddo e0 e1) =
        (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_usubo :
  forall e0 : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e1 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed ca ->
          newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g (QFBV.Bbinop QFBV.Busubo e0 e1) =
        (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_umulo :
  forall e0 : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e1 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed ca ->
          newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g (QFBV.Bbinop QFBV.Bumulo e0 e1) =
        (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_saddo :
  forall e0 : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e1 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed ca ->
          newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g (QFBV.Bbinop QFBV.Bsaddo e0 e1) =
        (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_ssubo :
  forall e0 : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e1 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed ca ->
          newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g (QFBV.Bbinop QFBV.Bssubo e0 e1) =
        (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_smulo :  
  forall e0 : QFBV.exp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e0 = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e1 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed ca ->
          newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g (QFBV.Bbinop QFBV.Bsmulo e0 e1) =
        (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_lneg :
  forall b : QFBV.bexp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g b = (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall (m : vm) (ca : cache) (s : SSAStore.t) 
           (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
           (g' : generator) (cs : cnf) (lr : literal),
      mk_env_bexp_cache m ca s E g (QFBV.Blneg b) = (m', ca', E', g', cs, lr) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      well_formed ca ->
      newer_than_cache g ca -> regular E ca -> 
      interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.

Lemma mk_env_bexp_cache_regular_conj :
  forall b : QFBV.bexp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g b = (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall b0 : QFBV.bexp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lr : literal),
          mk_env_bexp_cache m ca s E g b0 = (m', ca', E', g', cs, lr) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed ca ->
          newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g (QFBV.Bconj b b0) = (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
  move=> e1 IH1 e2 IH2 m ca s E g m' ca' E' g' cs lr. 
  rewrite /mk_env_bexp_cache -/mk_env_bexp_cache.
  case Hfcbt: (find_cbt (QFBV.Bconj e1 e2) ca) => [l|].
  - case=> _ <- <- _ <- _ Hgm Hgt _ _ HrEca //=.
  - case Hfhbt: (find_hbt (QFBV.Bconj e1 e2) ca) => [[csh lh]|].
    + case=> _ <- <- _ <- _ Hgm Hgt _ _ HrEca.
      split; last by rewrite -regular_add_cbt.
      move: HrEca => [_ HrEca]. exact: (HrEca _ _ _ Hfhbt). 
    + case Hmke1: (mk_env_bexp_cache m ca s E g e1) 
      => [[[[[m1 ca1] E1] g1] cs1] lr1].
      case Hmke2: (mk_env_bexp_cache m1 ca1 s E1 g1 e2) 
      => [[[[[m2 ca2] E2] g2] cs2] lr2].
      case Hmkr: (mk_env_conj E2 g2 lr1 lr2) => [[[oE og] ocs] olr].
      case=> _ <- <- _ <- _ Hgm Hgt /= Hwfca Hgca HrEca. 
      move: (IH1 _ _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwfca Hgca HrEca) 
      => [HiE1c1 HrE1ca1].
      move: (mk_env_bexp_cache_newer_vm Hmke1 Hgm) => Hg1m1.
      move: (mk_env_bexp_cache_newer_gen Hmke1) => Hgg1.
      move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
      move: (mk_env_bexp_cache_well_formed Hmke1 Hwfca) => Hwfca1.
      move: (mk_env_bexp_cache_newer_cache Hmke1 Hgm Hgt Hwfca Hgca) => Hg1ca1.
      move: (IH2 _ _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwfca1 Hg1ca1 HrE1ca1) 
      => [HiE2c2 HrE2ca2].
      have Hcnf : interp_cnf oE (cs1 ++ cs2 ++ ocs).
      {
        rewrite !interp_cnf_cat.
        move: (mk_env_bexp_cache_preserve Hmke2) => HE1E2g1.
        move: (mk_env_bexp_cache_newer_gen Hmke2) => Hg1g2.
        move: (mk_env_bexp_cache_newer_cnf Hmke1 Hgm Hgt Hwfca Hgca) => Hg1cs1.
        move: (newer_than_cnf_le_newer Hg1cs1 Hg1g2) => Hg2cs1.
        move: (newer_than_lit_le_newer Hgt Hgg1) => {Hgg1} Hg1tt.
        move: (mk_env_bexp_cache_newer_cnf Hmke2 Hg1m1 Hg1tt Hwfca1 Hg1ca1) => Hg2cs2.
        move: (mk_env_bexp_cache_newer_res Hmke1 Hgm Hgt Hwfca Hgca) => Hg1lr1.
        move: (mk_env_bexp_cache_newer_res Hmke2 Hg1m1 Hg1tt Hwfca1 Hg1ca1) => Hg2lr2.
        move: (newer_than_lit_le_newer Hg1lr1 Hg1g2) => {Hg1g2 Hg1lr1} Hg2lr1.
        (* interp_cnf E2 cs1 *)
        rewrite (env_preserve_cnf (mk_env_conj_preserve Hmkr) Hg2cs1).
        rewrite (env_preserve_cnf HE1E2g1 Hg1cs1).
        rewrite HiE1c1 /=.
        (* interp_cnf E2 cs2 *)
        rewrite (env_preserve_cnf (mk_env_conj_preserve Hmkr) Hg2cs2).
        rewrite HiE2c2 /=.
        (* interp_cnf oE ocs *)
        apply: (mk_env_conj_sat Hmkr Hg2lr1 Hg2lr2).
      }
      split; first done.
      (* regular E' ca' *)
      apply regular_add_hbt. split; last done. apply regular_add_cbt. 
      move: (mk_env_conj_preserve Hmkr) => HpE2oEg2.
      move: (mk_env_bexp_cache_newer_cache Hmke2 Hg1m1 Hg1t Hwfca1 Hg1ca1) => Hg2ca2.
      by rewrite (env_preserve_regular HpE2oEg2 Hg2ca2).
Qed.

Lemma mk_env_bexp_cache_regular_disj :
  forall b : QFBV.bexp,
    (forall (m : vm) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g b = (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca') ->
    forall b0 : QFBV.bexp,
      (forall (m : vm) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lr : literal),
          mk_env_bexp_cache m ca s E g b0 = (m', ca', E', g', cs, lr) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed ca ->
          newer_than_cache g ca -> regular E ca -> 
          interp_cnf E' cs /\ regular E' ca') ->
      forall (m : vm) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g (QFBV.Bdisj b b0) = (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed ca ->
        newer_than_cache g ca -> regular E ca -> 
        interp_cnf E' cs /\ regular E' ca'.
Proof.
Admitted.


Corollary mk_env_exp_cache_regular :
  forall e m ca s E g m' ca' E' g' cs lrs,
    mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    (* QFBV.well_formed_exp e te -> *)
    Cache.well_formed ca -> newer_than_cache g ca -> Cache.regular E ca ->
    interp_cnf E' cs /\ Cache.regular E' ca'
  with
    mk_env_bexp_cache_regular :
      forall e m ca s E g m' ca' E' g' cs lr,
        mk_env_bexp_cache m ca s E g e = (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_bexp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca -> Cache.regular E ca ->
        interp_cnf E' cs /\ Cache.regular E' ca'.
Proof.
  (* mk_env_exp_cache_regular *)
  elim .
  - exact: mk_env_exp_cache_regular_var .
  - exact: mk_env_exp_cache_regular_const .
  - elim .
    + exact: mk_env_exp_cache_regular_not .
    + exact: mk_env_exp_cache_regular_neg .
    + exact: mk_env_exp_cache_regular_extract .
    + exact: mk_env_exp_cache_regular_high .
    + exact: mk_env_exp_cache_regular_low .
    + exact: mk_env_exp_cache_regular_zeroextend .
    + exact: mk_env_exp_cache_regular_signextend .
  - elim .
    + exact: mk_env_exp_cache_regular_and .
    + exact: mk_env_exp_cache_regular_or .
    + exact: mk_env_exp_cache_regular_xor .
    + exact: mk_env_exp_cache_regular_add .
    + exact: mk_env_exp_cache_regular_sub .
    + exact: mk_env_exp_cache_regular_mul .
    + exact: mk_env_exp_cache_regular_mod .
    + exact: mk_env_exp_cache_regular_srem .
    + exact: mk_env_exp_cache_regular_smod .
    + exact: mk_env_exp_cache_regular_shl .
    + exact: mk_env_exp_cache_regular_lshr .
    + exact: mk_env_exp_cache_regular_ashr .
    + exact: mk_env_exp_cache_regular_concat .
  - move => b;
      move : b (mk_env_bexp_cache_regular b);
      exact: mk_env_exp_cache_regular_ite .
  (* mk_env_bexp_cache_cache_regular *)
  elim .
  - exact: mk_env_bexp_cache_regular_false .
  - exact: mk_env_bexp_cache_regular_true .
  - elim; move => e0 e1;
          move : e0 (mk_env_exp_cache_regular e0)
                 e1 (mk_env_exp_cache_regular e1) .
    + exact: mk_env_bexp_cache_regular_eq .
    + exact: mk_env_bexp_cache_regular_ult .
    + exact: mk_env_bexp_cache_regular_ule .
    + exact: mk_env_bexp_cache_regular_ugt .
    + exact: mk_env_bexp_cache_regular_uge .
    + exact: mk_env_bexp_cache_regular_slt .
    + exact: mk_env_bexp_cache_regular_sle .
    + exact: mk_env_bexp_cache_regular_sgt .
    + exact: mk_env_bexp_cache_regular_sge .
    + exact: mk_env_bexp_cache_regular_uaddo .
    + exact: mk_env_bexp_cache_regular_usubo .
    + exact: mk_env_bexp_cache_regular_umulo .
    + exact: mk_env_bexp_cache_regular_saddo .
    + exact: mk_env_bexp_cache_regular_ssubo .
    + exact: mk_env_bexp_cache_regular_smulo .
  - exact: mk_env_bexp_cache_regular_lneg .
  - exact: mk_env_bexp_cache_regular_conj .
  - exact: mk_env_bexp_cache_regular_disj .
Qed.


(* = mk_env_exp_cache_sat and mk_env_bexp_cache_sat = *)

Corollary mk_env_exp_cache_sat :
  forall e m ca s E g m' ca' E' g' cs lrs,
    mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    Cache.well_formed ca -> newer_than_cache g ca -> Cache.regular E ca ->
    interp_cnf E' cs.
Proof.
  move=> e m ca s E g m' ca' E' g' cs lrs Hmke Hgm Hgt Hwfca Hgca HrEca.
  move: (mk_env_exp_cache_regular Hmke Hgm Hgt Hwfca Hgca HrEca) => [Hi Hr].
  done.
Qed.

Corollary mk_env_bexp_cache_sat :
  forall e m ca s E g m' ca' E' g' cs lr,
    mk_env_bexp_cache m ca s E g e = (m', ca', E', g', cs, lr) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    Cache.well_formed ca -> newer_than_cache g ca -> Cache.regular E ca ->
    interp_cnf E' cs.
Proof.
  move=> e m ca s E g m' ca' E' g' cs lr Hmke Hgm Hgt Hwfca Hgca HrEca.
  move: (mk_env_bexp_cache_regular Hmke Hgm Hgt Hwfca Hgca HrEca) => [Hi Hr].
  done.
Qed.  
