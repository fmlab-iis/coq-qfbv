From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
From newBBCache Require Import CompCache BitBlastingCCacheDef 
     BitBlastingCCacheNewer BitBlastingCCachePreserve .

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* = mk_env_exp_ccache_consistent and mk_env_bexp_ccache_consistent = *)

Lemma mk_env_exp_ccache_consistent_nocet_var :
  forall (t : SSAVarOrder.t) (m : vm) (c : compcache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (c' : compcache) 
         (E' : env) (g' : generator) (cs : cnf) (ls : word),
    find_cet (QFBV.Evar t) c = None ->
    mk_env_exp_ccache m c s E g (QFBV.Evar t) = (m', c', E', g', cs, ls) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> v m c s E g m' c' E' g' cs ls Hfcet. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Evar v) c) => [[cse lse] | ].
  - case=> <- _ <- _ _ _ Hgm Hcon. done.
  - case Hfv: (SSAVM.find v m).
    + case=> <- _ <- _ _ _ Hgm Hcon. done.
    + case Hv: (mk_env_var E g (SSAStore.acc v s) v) => [[[Ev gv] csv] lsv].
      case=> <- _ <- _ _ _ Hgm Hcon. move=> x. rewrite /consistent1.
      case Hxv: (x == v).
      * rewrite (SSAVM.Lemmas.find_add_eq Hxv). rewrite (eqP Hxv).
        exact: (mk_env_var_enc Hv).
      * move/negP: Hxv => Hxv. rewrite (SSAVM.Lemmas.find_add_neq Hxv).
        move: (Hcon x). rewrite /consistent1.
        case Hfxm: (SSAVM.find x m); last done .
        move=> Henc. move: (Hgm x _ Hfxm) => Hnew.
        exact: (env_preserve_enc_bits (mk_env_var_preserve Hv) Hnew Henc).
Qed.

Lemma mk_env_exp_ccache_consistent_nocet_const :
  forall (b : bits) (m : vm) (c : compcache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (c' : compcache) 
         (E' : env) (g' : generator) (cs : cnf) (ls : word),
    find_cet (QFBV.Econst b) c = None ->
    mk_env_exp_ccache m c s E g (QFBV.Econst b) = (m', c', E', g', cs, ls) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> bs m c s E g m' c' E' g' cs ls Hfcet Hmk Hgm HcmE. 
  move: Hmk. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Econst bs) c) => [[csop lsop] | ];
    case=> <- _ <- _ _ _; done.
Qed.

Lemma mk_env_exp_ccache_consistent_nocet_unop :
  forall (op : QFBV.eunop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
           (g : generator) (m' : vm) (c' : compcache) (E' : env) 
           (g' : generator) (cs : cnf) (ls : word),
      find_cet (QFBV.Eunop op e1) c = None ->
      mk_env_exp_ccache m c s E g (QFBV.Eunop op e1) = (m', c', E', g', cs, ls) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> op e1 IH1 m c s E g m' c' E' g' cs ls Hfcet Hmk Hgm HcmE. 
  move: Hmk. rewrite /= Hfcet.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm HcmE) => Hcm1E1.
  case Hfhet : (find_het (QFBV.Eunop op e1) c1) => [[csop lsop] | ].
  - case=> <- _ <- _ _ _. done.
  - case Hop : (mk_env_eunop op E1 g1 ls1) => [[[Eop gop] csop] lsop].
    case=> <- _ <- _ _ _. 
    move: (mk_env_eunop_preserve Hop) => HpE1Eopg1.
    move: (mk_env_exp_ccache_newer_vm He1 Hgm) => Hg1m1.
    exact: (env_preserve_consistent Hg1m1 HpE1Eopg1 Hcm1E1).
Qed.

Lemma mk_env_exp_ccache_consistent_nocet_binop :
  forall (op : QFBV.ebinop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall e2 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (ls : word),
        find_cet (QFBV.Ebinop op e1 e2) c = None ->
        mk_env_exp_ccache m c s E g (QFBV.Ebinop op e1 e2) = (m', c', E', g', cs, ls) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> op e1 IH1 e2 IH2 m c s E g m' c' E' g' cs ls Hfcet Hmk Hgm HcmE. 
  move: Hmk. rewrite /= Hfcet.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_ccache_newer_vm He1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1 Hcm1E1) => Hcm2E2.
  case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csop lsop] | ].
  - case=> <- _ <- _ _ _. done.
  - case Hop : (mk_env_ebinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lsop].
    case=> <- _ <- _ _ _. 
    move: (mk_env_ebinop_preserve Hop) => HpE2Eopg2.
    move: (mk_env_exp_ccache_newer_vm He2 Hg1m1) => Hg2m2.
    exact: (env_preserve_consistent Hg2m2 HpE2Eopg2 Hcm2E2).
Qed.

Lemma mk_env_exp_ccache_consistent_nocet_ite :
  forall b : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g b = (m', c', E', g', cs, l) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall e2 : QFBV.exp,
        (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
                (g : generator) (m' : vm) (c' : compcache) (E' : env) 
                (g' : generator) (cs : cnf) (ls : word),
            mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
            newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
        forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
               (g : generator) (m' : vm) (c' : compcache) (E' : env) 
               (g' : generator) (cs : cnf) (ls : word),
          find_cet (QFBV.Eite b e1 e2) c = None ->
          mk_env_exp_ccache m c s E g (QFBV.Eite b e1 e2) = (m', c', E', g', cs, ls) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> b IHb e1 IH1 e2 IH2 m c s E g m' c' E' g' cs ls Hfcet Hmk Hgm HcmE. 
  move: Hmk. rewrite /= Hfcet.
  case Hb : (mk_env_bexp_ccache m c s E g b) => [[[[[mb cb] Eb] gb] csb] lb].
  case He1 : (mk_env_exp_ccache mb cb s Eb gb e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IHb _ _ _ _ _ _ _ _ _ _ _ Hb Hgm HcmE) => HcmbEb.
  move: (mk_env_bexp_ccache_newer_vm Hb Hgm) => Hgbmb.
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgbmb HcmbEb) => Hcm1E1.
  move: (mk_env_exp_ccache_newer_vm He1 Hgbmb) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1 Hcm1E1) => Hcm2E2.
  case Hfhet : (find_het (QFBV.Eite b e1 e2) c2) => [[csop lsop] | ].
  - case=> <- _ <- _ _ _. done.
  - case Hop : (mk_env_ite E2 g2 lb ls1 ls2) => [[[Eop gop] csop] lsop].
    case=> <- _ <- _ _ _. 
    move: (mk_env_ite_preserve Hop) => HpE2Eopg2.
    move: (mk_env_exp_ccache_newer_vm He2 Hg1m1) => Hg2m2.
    exact: (env_preserve_consistent Hg2m2 HpE2Eopg2 Hcm2E2).
Qed.

Lemma mk_env_bexp_ccache_consistent_nocbt_false :
  forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
         (g : generator) (m' : vm) (c' : compcache) (E' : env) 
         (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Bfalse c = None ->
    mk_env_bexp_ccache m c s E g QFBV.Bfalse = (m', c', E', g', cs, l) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> m c s E g m' c' E' g' cs l Hfcbt Hmk Hgm HcmE. 
  move: Hmk. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Bfalse) c) => [[csop lop] | ];
    case=> <- _ <- _ _ _; done.
Qed.

Lemma mk_env_bexp_ccache_consistent_nocbt_true :
  forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
         (g : generator) (m' : vm) (c' : compcache) (E' : env) 
         (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Btrue c = None ->
    mk_env_bexp_ccache m c s E g QFBV.Btrue = (m', c', E', g', cs, l) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> m c s E g m' c' E' g' cs l Hfcbt Hmk Hgm HcmE. 
  move: Hmk. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Btrue) c) => [[csop lop] | ];
    case=> <- _ <- _ _ _; done.
Qed.

Lemma mk_env_bexp_ccache_consistent_nocbt_binop :
  forall (op : QFBV.bbinop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall e2 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bbinop op e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bbinop op e1 e2) = (m', c', E', g', cs, l) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> op e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt Hmk Hgm HcmE. 
  move: Hmk. rewrite /= Hfcbt.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_ccache_newer_vm He1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1 Hcm1E1) => Hcm2E2.
  case Hfhbt : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[csop lop] | ].
  - case=> <- _ <- _ _ _. done.
  - case Hop : (mk_env_bbinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lop].
    case=> <- _ <- _ _ _. 
    move: (mk_env_bbinop_preserve Hop) => HpE2Eopg2.
    move: (mk_env_exp_ccache_newer_vm He2 Hg1m1) => Hg2m2.
    exact: (env_preserve_consistent Hg2m2 HpE2Eopg2 Hcm2E2).
Qed.

Lemma mk_env_bexp_ccache_consistent_nocbt_lneg :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
           (g : generator) (m' : vm) (c' : compcache) (E' : env) 
           (g' : generator) (cs : cnf) (l : literal),
      find_cbt (QFBV.Blneg e1) c = None ->
      mk_env_bexp_ccache m c s E g (QFBV.Blneg e1) = (m', c', E', g', cs, l) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 m c s E g m' c' E' g' cs l Hfcbt Hmk Hgm HcmE. 
  move: Hmk. rewrite /mk_env_bexp_ccache -/mk_env_bexp_ccache Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm HcmE) => Hcm1E1.
  case Hfhbt : (find_hbt (QFBV.Blneg e1) c1) => [[csop lop] | ].
  - case=> <- _ <- _ _ _. done.
  - case Hop : (mk_env_lneg E1 g1 l1) => [[[Eop gop] csop] lop].
    case=> <- _ <- _ _ _. 
    move: (mk_env_lneg_preserve Hop) => HpE1Eopg1.
    move: (mk_env_bexp_ccache_newer_vm He1 Hgm) => Hg1m1.
    exact: (env_preserve_consistent Hg1m1 HpE1Eopg1 Hcm1E1).
Qed.

Lemma mk_env_bexp_ccache_consistent_nocbt_conj :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall e2 : QFBV.bexp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (l : literal),
          mk_env_bexp_ccache m c s E g e2 = (m', c', E', g', cs, l) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bconj e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bconj e1 e2) = (m', c', E', g', cs, l) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt Hmk Hgm HcmE. 
  move: Hmk. rewrite /mk_env_bexp_ccache -/mk_env_bexp_ccache Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  case He2 : (mk_env_bexp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_bexp_ccache_newer_vm He1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1 Hcm1E1) => Hcm2E2.
  case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csop lop] | ].
  - case=> <- _ <- _ _ _. done.
  - case Hop : (mk_env_conj E2 g2 l1 l2) => [[[Eop gop] csop] lop].
    case=> <- _ <- _ _ _. 
    have HpE2Eopg2 : env_preserve E2 Eop g2 
      by move: Hop; exact: mk_env_conj_preserve.
    move: (mk_env_bexp_ccache_newer_vm He2 Hg1m1) => Hg2m2.
    exact: (env_preserve_consistent Hg2m2 HpE2Eopg2 Hcm2E2).
Qed.

Lemma mk_env_bexp_ccache_consistent_nocbt_disj :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall e2 : QFBV.bexp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (l : literal),
          mk_env_bexp_ccache m c s E g e2 = (m', c', E', g', cs, l) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bdisj e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bdisj e1 e2) = (m', c', E', g', cs, l) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt Hmk Hgm HcmE. 
  move: Hmk. rewrite /mk_env_bexp_ccache -/mk_env_bexp_ccache Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  case He2 : (mk_env_bexp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_bexp_ccache_newer_vm He1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1 Hcm1E1) => Hcm2E2.
  case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csop lop] | ].
  - case=> <- _ <- _ _ _. done.
  - case Hop : (mk_env_disj E2 g2 l1 l2) => [[[Eop gop] csop] lop].
    case=> <- _ <- _ _ _. 
    have HpE2Eopg2 : env_preserve E2 Eop g2 
      by move: Hop; exact: mk_env_disj_preserve.
    move: (mk_env_bexp_ccache_newer_vm He2 Hg1m1) => Hg2m2.
    exact: (env_preserve_consistent Hg2m2 HpE2Eopg2 Hcm2E2).
Qed.


Corollary mk_env_exp_ccache_consistent :
  forall (e : QFBV.exp) m c s E g m' c' E' g' cs ls,
    mk_env_exp_ccache m c s E g e = (m', c', E', g', cs, ls) ->
    newer_than_vm g m ->
    consistent m E s -> consistent m' E' s
  with
    mk_env_bexp_ccache_consistent :
      forall e m c s E g m' c' E' g' cs l,
        mk_env_bexp_ccache m c s E g e = (m', c', E', g', cs, l) ->
        newer_than_vm g m ->
        consistent m E s -> consistent m' E' s.
Proof.
  (* exp *)
  set IHe := mk_env_exp_ccache_consistent.
  set IHb := mk_env_bexp_ccache_consistent.
  move=> e m c s E g m' c' E' g' cs ls.
  case Hfcet: (find_cet e c) => [[cse lse] | ]. 
  - rewrite mk_env_exp_ccache_equation Hfcet /=.
    case=> <- _ <- _ _ _. done.
  - move: e m c s E g m' c' E' g' cs ls Hfcet.
    case.
    + exact: mk_env_exp_ccache_consistent_nocet_var.
    + exact: mk_env_exp_ccache_consistent_nocet_const.
    + move=> op e1; move: op e1 (IHe e1).
      exact: mk_env_exp_ccache_consistent_nocet_unop.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_consistent_nocet_binop.
    + move=> b e1 e2; move: b (IHb b) e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_consistent_nocet_ite.
  (* bexp *)
  set IHe := mk_env_exp_ccache_consistent.
  set IHb := mk_env_bexp_ccache_consistent.
  move=> e m c s E g m' c' E' g' cs l.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite mk_env_bexp_ccache_equation Hfcbt /=.
    case=> <- _ <- _ _ _. done.
  - move: e m c s E g m' c' E' g' cs l Hfcbt.
    case.
    + exact: mk_env_bexp_ccache_consistent_nocbt_false.
    + exact: mk_env_bexp_ccache_consistent_nocbt_true.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_bexp_ccache_consistent_nocbt_binop.
    + move=> e1; move: e1 (IHb e1).
      exact: mk_env_bexp_ccache_consistent_nocbt_lneg.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_consistent_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_consistent_nocbt_disj.
Qed.
