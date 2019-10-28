From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport
     BitBlastingDef BitBlastingNewer BitBlastingPreserve BitBlastingCorrect .

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* = mk_env_exp_sat and mk_env_bexp_sat = *)

Lemma mk_env_exp_sat_var :
  forall t (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Evar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Evar t) te ->
    interp_cnf E' cs.
Proof.
  move=> v te m s E g m' E' g' cs lrs /=. case Hfind: (SSAVM.find v m).
  - case=> _ <- _ <- _ Hnew_gm Hnew_gtt _. done.
  - case Henv: (mk_env_var E g (SSAStore.acc v s) v) => [[[E_v g_v] cs_v] lrs_v].
    case=> _ <- _ <- _ Hnew_gm Hnew_gtt _. exact: (mk_env_var_sat Henv).
Qed.

Lemma mk_env_exp_sat_const :
  forall (b : bits) (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Econst b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Econst b) te ->
    interp_cnf E' cs.
Proof.
  move=> bs te m s E g m' E' g' cs lrs /=. case=> _ <- _ <- _ Hnew_gm Hnew_gtt _. done.
Qed.

Lemma mk_env_exp_sat_not :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop QFBV.Unot e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop QFBV.Unot e1) te ->
      interp_cnf E' cs.
Proof.
  move=> e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt Hwf. rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) => HiE1c1.
  move: (mk_env_not_preserve Hmkr) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  exact: (mk_env_not_sat Hmkr Hg1l1).
Qed.

Lemma mk_env_exp_sat_and :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Band e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Band e1 e2) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_and_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  exact: (mk_env_and_sat Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_sat_or :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bor e0 e1) te ->
      interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_or E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_or_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  exact: (mk_env_or_sat Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_sat_xor :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bxor e1 e2) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_xor_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  exact: (mk_env_xor_sat Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_sat_neg :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop QFBV.Uneg e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Eunop QFBV.Uneg e1) te ->
    interp_cnf E' cs.
Proof.
  move=> e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= Hwf1 .
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_neg_preserve Hmkr) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  exact: (mk_env_neg_sat Hmkr Hg1t Hg1l1).
Qed.

Lemma mk_env_exp_sat_add :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Badd e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Badd e e0) te ->
    interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_add E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_add_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2f.
  rewrite newer_than_lit_tt_ff in Hg2f .
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_add_sat Hmkr Hg2l1 Hg2l2 Hg2f) .
Qed.

Lemma mk_env_exp_sat_sub :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsub e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsub e e0) te ->
    interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sub E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_sub_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_sub_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_exp_sat_mul :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmul e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bmul e e0) te ->
    interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_mul E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_mul_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_mul_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_exp_sat_mod :
  forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
  forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bmod e e0) te ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_srem :
  forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
  forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsrem e e0) te ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_smod :
  forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
  forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsmod e e0) te ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_shl :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bshl e0 e1) te ->
      interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_shl E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_shl_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_shl_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed .

Lemma mk_env_exp_sat_lshr :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Blshr e0 e1) te ->
      interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_lshr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_lshr_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_lshr_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed .

Lemma mk_env_exp_sat_ashr :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bashr e0 e1) te ->
      interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ashr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_ashr_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_ashr_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed .

Lemma mk_env_exp_sat_concat :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bconcat e0 e1) te ->
      interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1E2g1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  rewrite (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) // .
Qed .

Lemma mk_env_exp_sat_extract :
  forall (i j : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uextr i j) e) te ->
      interp_cnf E' cs.
Proof.
  move=> i j e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ <- _ Hgm Hgt Hwf .
  rewrite !interp_cnf_cat /= .
  (* interp_cnf Er cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

(*
Lemma mk_env_exp_sat_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV.exp (w3 + w2 + w1)),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      interp_cnf E' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !interp_cnf_append.
  by rewrite (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .
*)

Lemma mk_env_exp_sat_high :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm)
           (s : SSAStore.t) (E : env) (g : generator) (m' : vm)
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uhigh n) e) te ->
      interp_cnf E' cs.
Proof.
  move=> n e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ <- _ Hgm Hgt Hwf .
  rewrite !interp_cnf_cat /= .
  (* interp_cnf Er cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

Lemma mk_env_exp_sat_low :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Ulow n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Ulow n) e) te ->
      interp_cnf E' cs.
Proof.
  move=> n e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ <- _ Hgm Hgt Hwf .
  rewrite !interp_cnf_cat /= .
  (* interp_cnf Er cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

Lemma mk_env_exp_sat_zeroextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uzext n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uzext n) e) te ->
      interp_cnf E' cs.
Proof.
  move=> n e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ <- _ Hgm Hgt Hwf .
  rewrite !interp_cnf_cat /= .
  (* interp_cnf Er cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

Lemma mk_env_exp_sat_signextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Usext n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Usext n) e) te ->
      interp_cnf E' cs.
Proof.
  move=> n e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ <- _ Hgm Hgt Hwf .
  rewrite !interp_cnf_cat /= .
  (* interp_cnf Er cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

Lemma mk_env_exp_sat_ite :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp b te ->
        interp_cnf E' cs) ->
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
      forall (e0 : QFBV.exp),
        (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : word),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
            newer_than_vm g m ->
            newer_than_lit g lit_tt ->
            QFBV.well_formed_exp e0 te ->
            interp_cnf E' cs) ->
        forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp m s E g (QFBV.Eite b e e0) = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp (QFBV.Eite b e e0) te ->
          interp_cnf E' cs.
Proof.
  move=> c IHc e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmkc : (mk_env_bexp m s E g c) => [[[[mc Ec] gc] csc] lsc].
  case Hmke1 : (mk_env_exp mc s Ec gc e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ite E2 g2 lsc ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [/andP [Hwfc Hwf1] Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er csc *)
  move: (IHc _ _ _ _ _ _ _ _ _ _ Hmkc Hgm Hgt Hwfc) => HiEccc.
  move: (mk_env_exp_preserve Hmke1) => HpEcE1gc.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_ite_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgcg1.
  move: (env_preserve_le HpE1Erg1 Hgcg1) => HpE1Ergc.
  move: (env_preserve_trans HpEcE1gc HpE1Ergc) => HpEcErgc.
  move: (mk_env_bexp_newer_cnf Hmkc Hgm Hgt Hwfc) => Hgccc.
  rewrite (env_preserve_cnf HpEcErgc Hgccc) HiEccc /=.
  (* interp_cnf Er cs1 *)
  move: (mk_env_bexp_newer_vm Hmkc Hgm) => Hgcmc.
  move: (mk_env_bexp_newer_gen Hmkc) => Hggc.
  move: (newer_than_lit_le_newer Hgt Hggc) => Hgct.
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgcmc Hgct Hwf1) => HiE1c1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgcmc Hgct Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgcmc) => Hg1m1.
  move: (newer_than_lit_le_newer Hgct Hgcg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_bexp_newer_res Hmkc Hgm Hgt) => Hgclc.
  move: (mk_env_exp_newer_res Hmke1 Hgcmc Hgct) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hgclc (pos_leb_trans Hgcg1 Hg1g2)) => Hg2lc .
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_ite_sat Hmkr Hg2t Hg2lc Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_false :
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Bfalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt ->
    QFBV.well_formed_bexp QFBV.Bfalse te ->
    interp_cnf E' cs.
Proof.
  move=> te m s E g m' E' g' cs lr /=. case=> _ <- _ <- _ Hnew_gm Hnew_gtt _ // .
Qed.

Lemma mk_env_bexp_sat_true :
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Btrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt ->
    QFBV.well_formed_bexp QFBV.Btrue te ->
    interp_cnf E' cs.
Proof.
  move=> te m s E g m' E' g' cs lr /=. case=> _ <- _ <- _ Hnew_gm Hnew_gtt _ // .
Qed.

Lemma mk_env_bexp_sat_eq :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Beq e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Beq e e0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr /=.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr: (mk_env_eq E2 g2 ls1 ls2) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize]. rewrite !interp_cnf_cat.
  move: (mk_env_exp_preserve Hmke2) => HE1E2g1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgtt Hwf1) => Hg1cs1.
  move: (newer_than_cnf_le_newer Hg1cs1 Hg1g2) => Hg2cs1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2cs2.
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1ls1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2ls2.
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (newer_than_lits_le_newer Hg1ls1 Hg1g2) => Hg2ls1.
  (* interp_cnf oE cs1 *)
  rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkr) Hg2cs1).
  rewrite (env_preserve_cnf HE1E2g1 Hg1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) /= .
  (* interp_cnf oE cs2 *)
  rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkr) Hg2cs2).
  rewrite (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) /= .
  (* interp_cnf oE ocs *)
  apply: (mk_env_eq_sat Hmkr Hg2tt Hg2ls1 Hg2ls2).
Qed.

Lemma mk_env_bexp_sat_ult :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bult e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bult e e0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ult E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_ult_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_ult_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_ule :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bule e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bule e e0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ule E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_ule_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_ule_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_ugt :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bugt e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bugt e e0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ugt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_ugt_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_ugt_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_uge :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buge e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Buge e e0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_uge_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_uge_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_slt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bslt e1 e2) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_slt_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_slt_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_sle :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsle e1 e2) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_sle_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_sle_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_sgt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsgt e1 e2) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_sgt_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_sgt_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_sge :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsge e1 e2) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_sge_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_sge_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_uaddo :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Buaddo e e0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uaddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_uaddo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_uaddo_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_usubo :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Busubo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Busubo e e0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_usubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_usubo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_usubo_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_umulo :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bumulo e e0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_umulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_umulo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_umulo_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_saddo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsaddo e1 e2) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_saddo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_saddo_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_ssubo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bssubo e1 e2) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_ssubo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_ssubo_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_smulo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsmulo e1 e2) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_smulo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_smulo_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_lneg :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp b te ->
        interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Blneg b) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Blneg b) te ->
        interp_cnf E' cs.
Proof.
  move=> e IH te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Hmke: (mk_env_bexp m s E g e) => [[[[m1 E1] g1] cs1] lr1].
  case Hmkr: (mk_env_lneg E1 g1 lr1) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hgm Hgtt Hwf. rewrite !interp_cnf_cat.
  move: (mk_env_bexp_newer_gen Hmke) => Hgg1.
  move: (mk_env_bexp_newer_cnf Hmke Hgm Hgtt Hwf) => Hg1cs1.
  move: (mk_env_bexp_newer_vm Hmke Hgm) => Hg1m1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => {Hgg1} Hg1tt.
  move: (mk_env_bexp_newer_res Hmke Hgm Hgtt) => Hg1lr1.
  (* interp_cnf E2 cs1 *)
  rewrite (env_preserve_cnf (mk_env_lneg_preserve Hmkr) Hg1cs1).
  rewrite (IH _ _ _ _ _ _ _ _ _ _ Hmke Hgm Hgtt Hwf) // .
  (* interp_cnf oE ocs *)
  apply: (mk_env_lneg_sat Hmkr Hg1lr1).
Qed.

Lemma mk_env_bexp_sat_conj :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp b te ->
        interp_cnf E' cs) ->
    forall (b0 : QFBV.bexp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_bexp b0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bconj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bconj b b0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Hmke1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Hmke2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case Hmkr: (mk_env_conj E2 g2 lr1 lr2) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hgm Hgtt /= /andP [Hwf1 Hwf2]. rewrite !interp_cnf_cat.
  move: (mk_env_bexp_preserve Hmke2) => HE1E2g1.
  move: (mk_env_bexp_newer_gen Hmke1) => Hgg1.
  move: (mk_env_bexp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_bexp_newer_cnf Hmke1 Hgm Hgtt Hwf1) => Hg1cs1.
  move: (newer_than_cnf_le_newer Hg1cs1 Hg1g2) => Hg2cs1.
  move: (mk_env_bexp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => {Hgg1} Hg1tt.
  move: (mk_env_bexp_newer_cnf Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2cs2.
  move: (mk_env_bexp_newer_res Hmke1 Hgm Hgtt) => Hg1lr1.
  move: (mk_env_bexp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2lr2.
  move: (newer_than_lit_le_newer Hg1lr1 Hg1g2) => {Hg1g2 Hg1lr1} Hg2lr1.
  (* interp_cnf E2 cs1 *)
  rewrite (env_preserve_cnf (mk_env_conj_preserve Hmkr) Hg2cs1).
  rewrite (env_preserve_cnf HE1E2g1 Hg1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) // .
  (* interp_cnf E2 cs2 *)
  rewrite (env_preserve_cnf (mk_env_conj_preserve Hmkr) Hg2cs2).
  rewrite (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) // .
  (* interp_cnf oE ocs *)
  apply: (mk_env_conj_sat Hmkr Hg2lr1 Hg2lr2).
Qed.

Lemma mk_env_bexp_sat_disj :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp b te ->
        interp_cnf E' cs) ->
    forall (b0 : QFBV.bexp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_bexp b0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bdisj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bdisj b b0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Hmke1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Hmke2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case Hmkr: (mk_env_disj E2 g2 lr1 lr2) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hgm Hgtt /= /andP [Hwf1 Hwf2]. rewrite !interp_cnf_cat.
  move: (mk_env_bexp_preserve Hmke2) => HE1E2g1.
  move: (mk_env_bexp_newer_gen Hmke1) => Hgg1.
  move: (mk_env_bexp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_bexp_newer_cnf Hmke1 Hgm Hgtt Hwf1) => Hg1cs1.
  move: (newer_than_cnf_le_newer Hg1cs1 Hg1g2) => Hg2cs1.
  move: (mk_env_bexp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => {Hgg1} Hg1tt.
  move: (mk_env_bexp_newer_cnf Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2cs2.
  move: (mk_env_bexp_newer_res Hmke1 Hgm Hgtt) => Hg1lr1.
  move: (mk_env_bexp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2lr2.
  move: (newer_than_lit_le_newer Hg1lr1 Hg1g2) => {Hg1g2 Hg1lr1} Hg2lr1.
  (* interp_cnf E2 cs1 *)
  rewrite (env_preserve_cnf (mk_env_disj_preserve Hmkr) Hg2cs1).
  rewrite (env_preserve_cnf HE1E2g1 Hg1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) // .
  (* interp_cnf E2 cs2 *)
  rewrite (env_preserve_cnf (mk_env_disj_preserve Hmkr) Hg2cs2).
  rewrite (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) // .
  (* interp_cnf oE ocs *)
  apply: (mk_env_disj_sat Hmkr Hg2lr1 Hg2lr2).
Qed.

Corollary mk_env_exp_sat :
  forall e te m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp e te ->
    interp_cnf E' cs
  with
    mk_env_bexp_sat :
      forall e te m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp e te ->
        interp_cnf E' cs.
Proof.
  (* mk_env_exp_sat *)
  elim .
  - exact: mk_env_exp_sat_var .
  - exact: mk_env_exp_sat_const .
  - elim .
    + exact: mk_env_exp_sat_not .
    + exact: mk_env_exp_sat_neg .
    + exact: mk_env_exp_sat_extract .
    + exact: mk_env_exp_sat_high .
    + exact: mk_env_exp_sat_low .
    + exact: mk_env_exp_sat_zeroextend .
    + exact: mk_env_exp_sat_signextend .
  - elim .
    + exact: mk_env_exp_sat_and .
    + exact: mk_env_exp_sat_or .
    + exact: mk_env_exp_sat_xor .
    + exact: mk_env_exp_sat_add .
    + exact: mk_env_exp_sat_sub .
    + exact: mk_env_exp_sat_mul .
    + exact: mk_env_exp_sat_mod .
    + exact: mk_env_exp_sat_srem .
    + exact: mk_env_exp_sat_smod .
    + exact: mk_env_exp_sat_shl .
    + exact: mk_env_exp_sat_lshr .
    + exact: mk_env_exp_sat_ashr .
    + exact: mk_env_exp_sat_concat .
  - move => b;
      move : b (mk_env_bexp_sat b);
      exact: mk_env_exp_sat_ite .
  (* mk_env_bexp_sat *)
  elim .
  - exact: mk_env_bexp_sat_false .
  - exact: mk_env_bexp_sat_true .
  - elim; move => e0 e1;
          move : e0 (mk_env_exp_sat e0)
                 e1 (mk_env_exp_sat e1) .
    + exact: mk_env_bexp_sat_eq .
    + exact: mk_env_bexp_sat_ult .
    + exact: mk_env_bexp_sat_ule .
    + exact: mk_env_bexp_sat_ugt .
    + exact: mk_env_bexp_sat_uge .
    + exact: mk_env_bexp_sat_slt .
    + exact: mk_env_bexp_sat_sle .
    + exact: mk_env_bexp_sat_sgt .
    + exact: mk_env_bexp_sat_sge .
    + exact: mk_env_bexp_sat_uaddo .
    + exact: mk_env_bexp_sat_usubo .
    + exact: mk_env_bexp_sat_umulo .
    + exact: mk_env_bexp_sat_saddo .
    + exact: mk_env_bexp_sat_ssubo .
    + exact: mk_env_bexp_sat_smulo .
  - exact: mk_env_bexp_sat_lneg .
  - exact: mk_env_bexp_sat_conj .
  - exact: mk_env_bexp_sat_disj .
Qed.


