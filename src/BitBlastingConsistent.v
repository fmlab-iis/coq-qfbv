
From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport
     BitBlastingDef BitBlastingNewer BitBlastingPreserve .

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* = mk_env_exp_consistent and mk_env_bexp_consistent = *)

Lemma mk_env_exp_consistent_var :
  forall t (m : vm) (s : SSAStore.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Evar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case Hfind: (SSAVM.find v m).
  - case=> <- <- _ _ _ Hnew_gm Hcon. assumption.
  - case Henv: (mk_env_var E g (SSAStore.acc v s) v) => [[[E_v g_v] cs_v] lrs_v].
    case=> <- <- _ _ _ Hnew_gm Hcon. move=> x. rewrite /consistent1.
    case Hxv: (x == v).
    + rewrite (SSAVM.Lemmas.find_add_eq Hxv). rewrite (eqP Hxv).
      exact: (mk_env_var_enc Henv).
    + move/negP: Hxv => Hxv. rewrite (SSAVM.Lemmas.find_add_neq Hxv).
      move: (Hcon x). rewrite /consistent1.
      case Hfind_xm: (SSAVM.find x m); last done .
      move=> Henc. move: (Hnew_gm x _ Hfind_xm) => Hnew.
      exact: (env_preserve_enc_bits (mk_env_var_preserve Henv) Hnew Henc).
Qed.

Lemma mk_env_exp_consistent_const :
  forall (b : bits) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Econst b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> bs m s E g m' E' g' cs lrs /=. case=> <- <- _ _ _ Hnew_gm Hcon.
  assumption.
Qed.

Lemma mk_env_exp_consistent_not :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop QFBV.Unot e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_not_preserve Hmkr) => HpE1Er.
  exact: (env_preserve_consistent Hg1m1 HpE1Er Hcm1E1).
Qed.

Lemma mk_env_exp_consistent_and :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Band e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_and_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_exp_consistent_or :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_or E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_or_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed .

Lemma mk_env_exp_consistent_xor :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_xor_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_exp_consistent_neg :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop QFBV.Uneg e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_neg_preserve Hmkr) => HpE1Er.
  exact: (env_preserve_consistent Hg1m1 HpE1Er Hcm1E1).
Qed.

Lemma mk_env_exp_consistent_add :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Badd e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_add E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_add_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_exp_consistent_sub :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsub e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sub E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_sub_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_exp_consistent_mul :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmul e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_mul E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_mul_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_exp_consistent_mod :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_srem :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_smod :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_shl :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_shl E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_shl_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed .

Lemma mk_env_exp_consistent_lshr :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_lshr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_lshr_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed .

Lemma mk_env_exp_consistent_ashr :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ashr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_ashr_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed .

Lemma mk_env_exp_consistent_concat :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_concat E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  exact: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1).
Qed .

Lemma mk_env_exp_consistent_extract :
  forall (i j : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> i j e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- <- _ _ _ Hgm HcmE.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) .
Qed .

(*
Lemma mk_env_exp_consistent_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV.exp (w3 + w2 + w1)),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .
*)

Lemma mk_env_exp_consistent_high :
    forall (n : nat) (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm)
           (s : SSAStore.t) (E : env) (g : generator) (m' : vm)
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- <- _ _ _ Hgm HcmE.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) .
Qed .

Lemma mk_env_exp_consistent_low :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Ulow n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- <- _ _ _ Hgm HcmE.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) .
Qed .

Lemma mk_env_exp_consistent_zeroextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop (QFBV.Uzext n) e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- <- _ _ _ Hgm HcmE.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) .
Qed .

Lemma mk_env_exp_consistent_signextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Usext n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- <- _ _ _ Hgm HcmE.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) .
Qed .

Lemma mk_env_exp_consistent_ite :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (e0 : QFBV.exp),
        (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : word),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
            newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
        forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp m s E g (QFBV.Eite b e e0) = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> c IHc e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmkc : (mk_env_bexp m s E g c) => [[[[mc Ec] gc] csc] lsc].
  case Hmke1 : (mk_env_exp mc s Ec gc e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ite E2 g2 lsc ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IHc _ _ _ _ _ _ _ _ _ Hmkc Hgm HcmE) => HcmcEc.
  move: (mk_env_bexp_newer_vm Hmkc Hgm) => Hgcmc.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgcmc HcmcEc) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgcmc) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_ite_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_false :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Bfalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> <- <- _ _ _. move=> _ H; exact: H.
Qed.

Lemma mk_env_bexp_consistent_true :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Btrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> <- <- _ _ _. move=> _ H; exact: H.
Qed.

Lemma mk_env_bexp_consistent_eq :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Beq e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_eq_preserve Heq)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_ult :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bult e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hult: (mk_env_ult E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_ult_preserve Hult)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_ule :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bule e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hule: (mk_env_ule E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_ule_preserve Hule)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_ugt :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bugt e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hugt: (mk_env_ugt E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_ugt_preserve Hugt)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_uge :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buge e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Huge: (mk_env_uge E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_uge_preserve Huge)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_slt :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_slt_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_sle :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_sle_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_sgt :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_sgt_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_sge :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_sge_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_uaddo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Huaddo: (mk_env_uaddo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_uaddo_preserve Huaddo)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_usubo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Busubo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Husubo: (mk_env_usubo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_usubo_preserve Husubo)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_umulo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Humulo: (mk_env_umulo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_umulo_preserve Humulo)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_saddo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_saddo_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_ssubo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_ssubo_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_smulo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_smulo_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_lneg :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Blneg b) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e IH m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv: (mk_env_bexp m s E g e)=> [[[[m1 E1] g1] cs1] lr1].
  case Hlneg: (mk_env_lneg E1 g1 lr1)=> [[[oE og] ocs] olr].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_bexp_newer_vm Henv Hnew) => Hnew1.
  apply: (env_preserve_consistent Hnew1 (mk_env_lneg_preserve Hlneg)).
  apply: (IH _ _ _ _ _ _ _ _ _ Henv Hnew). exact: Hcon.
Qed.

Lemma mk_env_bexp_consistent_conj :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (b0 : QFBV.bexp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bconj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case Hconj: (mk_env_conj E2 g2 lr1 lr2)=> [[[oE og] ocs] olr].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_bexp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_bexp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_conj_preserve Hconj)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  apply: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew). exact: Hcon.
Qed.

Lemma mk_env_bexp_consistent_disj :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (b0 : QFBV.bexp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bdisj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case Hdisj: (mk_env_disj E2 g2 lr1 lr2)=> [[[oE og] ocs] olr].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_bexp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_bexp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_disj_preserve Hdisj)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  apply: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew). exact: Hcon.
Qed.

Corollary mk_env_exp_consistent :
  forall (e : QFBV.exp) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    consistent m E s -> consistent m' E' s
  with
    mk_env_bexp_consistent :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        consistent m E s ->
        consistent m' E' s.
Proof.
  (* mk_env_exp_consistent *)
  elim .
  - exact: mk_env_exp_consistent_var .
  - exact: mk_env_exp_consistent_const .
  - elim .
    + exact: mk_env_exp_consistent_not .
    + exact: mk_env_exp_consistent_neg .
    + exact: mk_env_exp_consistent_extract .
    + exact: mk_env_exp_consistent_high .
    + exact: mk_env_exp_consistent_low .
    + exact: mk_env_exp_consistent_zeroextend .
    + exact: mk_env_exp_consistent_signextend .
  - elim .
    + exact: mk_env_exp_consistent_and .
    + exact: mk_env_exp_consistent_or .
    + exact: mk_env_exp_consistent_xor .
    + exact: mk_env_exp_consistent_add .
    + exact: mk_env_exp_consistent_sub .
    + exact: mk_env_exp_consistent_mul .
    + exact: mk_env_exp_consistent_mod .
    + exact: mk_env_exp_consistent_srem .
    + exact: mk_env_exp_consistent_smod .
    + exact: mk_env_exp_consistent_shl .
    + exact: mk_env_exp_consistent_lshr .
    + exact: mk_env_exp_consistent_ashr .
    + exact: mk_env_exp_consistent_concat .
  - move => b;
      move : b (mk_env_bexp_consistent b);
      exact: mk_env_exp_consistent_ite .
  (* mk_env_bexp_consistent *)
  elim .
  - exact: mk_env_bexp_consistent_false .
  - exact: mk_env_bexp_consistent_true .
  - elim;
      move => e0 e1;
      move : e0 (mk_env_exp_consistent e0)
             e1 (mk_env_exp_consistent e1) .
    + exact: mk_env_bexp_consistent_eq .
    + exact: mk_env_bexp_consistent_ult .
    + exact: mk_env_bexp_consistent_ule .
    + exact: mk_env_bexp_consistent_ugt .
    + exact: mk_env_bexp_consistent_uge .
    + exact: mk_env_bexp_consistent_slt .
    + exact: mk_env_bexp_consistent_sle .
    + exact: mk_env_bexp_consistent_sgt .
    + exact: mk_env_bexp_consistent_sge .
    + exact: mk_env_bexp_consistent_uaddo .
    + exact: mk_env_bexp_consistent_usubo .
    + exact: mk_env_bexp_consistent_umulo .
    + exact: mk_env_bexp_consistent_saddo .
    + exact: mk_env_bexp_consistent_ssubo .
    + exact: mk_env_bexp_consistent_smulo .
  - exact: mk_env_bexp_consistent_lneg .
  - exact: mk_env_bexp_consistent_conj .
  - exact: mk_env_bexp_consistent_disj .
Qed.


