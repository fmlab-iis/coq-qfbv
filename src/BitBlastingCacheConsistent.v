From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF Cache BBExport
     BitBlastingCacheDef BitBlastingCacheNewer BitBlastingCachePreserve .

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* = mk_env_exp_cache_consistent and mk_env_bexp_cache_consistent = *)

Lemma mk_env_exp_cache_consistent_nocache_var :
  forall (t : SSAVarOrder.t) (m : SSAVM.t word) (ca : cache) 
         (s : SSAStore.t) (E : env) (g : generator) (m' : vm) 
         (ca' : cache) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
    find_cet (QFBV.Evar t) ca = None ->
    find_het (QFBV.Evar t) ca = None ->
    mk_env_exp_cache m ca s E g (QFBV.Evar t) = (m', ca', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> v m ca s E g m' ca' E' g' cs lrs Hfcet Hfhet /=. 
  rewrite Hfcet Hfhet /=. 
  case Hfind: (SSAVM.find v m).
  - case=> <- _ <- _ _ _ Hnew_gm Hcon. assumption.
  - case Henv: (mk_env_var E g (SSAStore.acc v s) v) => [[[E_v g_v] cs_v] lrs_v].
    case=> <- _ <- _ _ _ Hnew_gm Hcon. move=> x. rewrite /consistent1.
    case Hxv: (x == v).
    + rewrite (SSAVM.Lemmas.find_add_eq Hxv). rewrite (eqP Hxv).
      exact: (mk_env_var_enc Henv).
    + move/negP: Hxv => Hxv. rewrite (SSAVM.Lemmas.find_add_neq Hxv).
      move: (Hcon x). rewrite /consistent1.
      case Hfind_xm: (SSAVM.find x m); last done .
      move=> Henc. move: (Hnew_gm x _ Hfind_xm) => Hnew.
      exact: (env_preserve_enc_bits (mk_env_var_preserve Henv) Hnew Henc).
Qed.

Lemma mk_env_exp_cache_consistent_nocache_const :
  forall (b : bits) (m : SSAVM.t word) (ca : cache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
         (g' : generator) (cs : cnf) (lrs : word),
    find_cet (QFBV.Econst b) ca = None ->
    find_het (QFBV.Econst b) ca = None ->
    mk_env_exp_cache m ca s E g (QFBV.Econst b) = (m', ca', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> bs m ca s E g m' ca' E' g' cs lrs Hfcet Hfhet /=. 
  rewrite Hfcet Hfhet /=. 
  by case=> <- _ <- _ _ _.
Qed.

Lemma mk_env_exp_cache_consistent_nocache_and :
  forall e1 : QFBV.exp,
    (forall (m : SSAVM.t word) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lrs : word),
        mk_env_exp_cache m ca s E g e1 = (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall e2 : QFBV.exp,
      (forall (m : SSAVM.t word) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp_cache m ca s E g e2 = (m', ca', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : SSAVM.t word) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lrs : word),
        find_cet (QFBV.Ebinop QFBV.Band e1 e2) ca = None ->
        find_het (QFBV.Ebinop QFBV.Band e1 e2) ca = None ->
        mk_env_exp_cache m ca s E g (QFBV.Ebinop QFBV.Band e1 e2) =
        (m', ca', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m ca s E g m' ca' E' g' cs lrs Hfcet Hfhet /=.
  rewrite Hfcet Hfhet /=.
  case Hmke1 : (mk_env_exp_cache m ca s E g e1) => [[[[[m1 ca1] E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp_cache m1 ca1 s E1 g1 e2) => [[[[[m2 ca2] E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_cache_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_and_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_cache_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_cache_consistent_nocache_conj :
  forall b1 : QFBV.bexp,
    (forall (m : SSAVM.t word) (ca : cache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
            (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp_cache m ca s E g b1 = (m', ca', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall b2 : QFBV.bexp,
      (forall (m : SSAVM.t word) (ca : cache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
              (g' : generator) (cs : cnf) (lr : literal),
          mk_env_bexp_cache m ca s E g b2 = (m', ca', E', g', cs, lr) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : SSAVM.t word) (ca : cache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (ca' : cache) (E' : env) 
             (g' : generator) (cs : cnf) (lr : literal),
        find_cbt (QFBV.Bconj b1 b2) ca = None ->
        find_hbt (QFBV.Bconj b1 b2) ca = None ->
        mk_env_bexp_cache m ca s E g (QFBV.Bconj b1 b2) = (m', ca', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m ca s E g m' ca' E' g' cs lr Hfcbt Hfhbt. 
  rewrite /mk_env_bexp_cache -/mk_env_bexp_cache Hfcbt Hfhbt.
  case Henv1: (mk_env_bexp_cache m ca s E g e1)=> [[[[[m1 ca1] E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp_cache m1 ca1 s E1 g1 e2)=> [[[[[m2 ca2] E2] g2] cs2] lr2].
  case Hconj: (mk_env_conj E2 g2 lr1 lr2)=> [[[oE og] ocs] olr].
  case=> <- _ <- _ _ _ Hnew Hcon.
  move: (mk_env_bexp_cache_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_bexp_cache_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_conj_preserve Hconj)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  apply: (IH1 _ _ _ _ _ _ _ _ _ _ _ Henv1 Hnew). exact: Hcon.
Qed.


Corollary mk_env_exp_cache_consistent :
  forall (e : QFBV.exp) m ca s E g m' ca' E' g' cs lrs,
    mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
    newer_than_vm g m ->
    consistent m E s -> consistent m' E' s
  with
    mk_env_bexp_cache_consistent :
      forall e m ca s E g m' ca' E' g' cs lr,
        mk_env_bexp_cache m ca s E g e = (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        consistent m E s ->
        consistent m' E' s.
Proof.
  (* mk_env_exp_cache_consistent *)
  move=> e m ca s E g m' ca' E' g' cs lrs.
  case Hfcet: (find_cet e ca) => [ls|]. 
  - rewrite mk_env_exp_cache_equation Hfcet /=.
    case=> <- _ <- _ _ _. done. 
  - case Hfhet: (find_het e ca) => [[csh lsh]|].
    + rewrite mk_env_exp_cache_equation Hfcet Hfhet /=. 
      by case=> <- _ <- _ _ _.
    + move: e m ca s E g m' ca' E' g' cs lrs Hfcet Hfhet.
      case.
      * exact: mk_env_exp_cache_consistent_nocache_var.
      * exact: mk_env_exp_cache_consistent_nocache_const.
      * elim. 
        -- admit. (* bit_blast_exp_not *)
        -- admit. (* bit_blast_exp_neg *)
        -- admit. (* bit_blast_exp_extract *)
        -- admit. (* bit_blast_exp_high *)
        -- admit. (* bit_blast_exp_low *)
        -- admit. (* bit_blast_exp_zeroextend *)
        -- admit. (* : bit_blast_exp_signextend; apply bit_blast_exp_correct . *)
      * elim.
        -- move=> e1 e2; apply mk_env_exp_cache_consistent_nocache_and;
                    by apply mk_env_exp_cache_consistent.
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
  (* mk_env_bexp_cache_consistent *)
  move=> e m ca s E g m' ca' E' g' cs lr.
  case Hfcbt: (find_cbt e ca) => [l|]. 
  - rewrite mk_env_bexp_cache_equation Hfcbt /=.
    case=> <- _ <- _ _ _. done. 
  - case Hfhbt: (find_hbt e ca) => [[csh lh]|].
    + rewrite mk_env_bexp_cache_equation Hfcbt Hfhbt /=. 
      by case=> <- _ <- _ _ _.
    + move: e m ca s E g m' ca' E' g' cs lr Hfcbt Hfhbt.
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
      * move=> b1 b2; apply: mk_env_bexp_cache_consistent_nocache_conj;
                 by apply: mk_env_bexp_cache_consistent.
      * admit. (* apply : bit_blast_bexp_disj . *)
Admitted.

