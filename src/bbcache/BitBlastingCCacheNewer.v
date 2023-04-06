From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types EqOrder EqVar Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
From BBCache Require Import CompCache BitBlastingCCacheDef BitBlastingCCacheWF.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* =  mk_env_exp_ccache_newer_gen and mk_env_bexp_ccache_newer_gen = *)

Lemma mk_env_eunop_newer_gen op E g ls1 E' g' cs ls : 
  mk_env_eunop op E g ls1 = (E', g', cs, ls) -> (g <=? g')%positive.
Proof. 
  case op => [ | | i j | n | n | n | n | n | n | n ];
    [ exact: mk_env_not_newer_gen |
      exact: mk_env_neg_newer_gen |
      exact: mk_env_extract_newer_gen |
      exact: mk_env_high_newer_gen |
      exact: mk_env_low_newer_gen |
      exact: mk_env_zeroextend_newer_gen |
      exact: mk_env_signextend_newer_gen |
      exact: mk_env_repeat_newer_gen |
      exact: mk_env_rotateleft_newer_gen |
      exact: mk_env_rotateright_newer_gen ].
Qed.

Lemma mk_env_ebinop_newer_gen op E g ls1 ls2 E' g' cs ls : 
  mk_env_ebinop op E g ls1 ls2 = (E', g', cs, ls) -> (g <=? g')%positive.
Proof. 
  case op;
    [ exact: mk_env_and_newer_gen |
      exact: mk_env_or_newer_gen |
      exact: mk_env_xor_newer_gen |
      exact: mk_env_add_newer_gen |
      exact: mk_env_sub_newer_gen |
      exact: mk_env_mul_newer_gen |
      exact: mk_env_udiv_newer_gen' |
      exact: mk_env_umod_newer_gen |
      exact: mk_env_sdiv_newer_gen |
      exact: mk_env_srem_newer_gen |
      exact: mk_env_smod_newer_gen |
      exact: mk_env_shl_newer_gen |
      exact: mk_env_lshr_newer_gen |
      exact: mk_env_ashr_newer_gen |
      exact: mk_env_concat_newer_gen |
      exact: mk_env_comp_newer_gen ].
Qed.

Lemma mk_env_bbinop_newer_gen op E g ls1 ls2 E' g' cs l : 
  mk_env_bbinop op E g ls1 ls2 = (E', g', cs, l) -> (g <=? g')%positive.
Proof. 
  case op;
    [ exact: mk_env_eq_newer_gen |
      exact: mk_env_ult_newer_gen |
      exact: mk_env_ule_newer_gen |
      exact: mk_env_ugt_newer_gen |
      exact: mk_env_uge_newer_gen |
      exact: mk_env_slt_newer_gen |
      exact: mk_env_sle_newer_gen |
      exact: mk_env_sgt_newer_gen |
      exact: mk_env_sge_newer_gen |
      exact: mk_env_uaddo_newer_gen |
      exact: mk_env_usubo_newer_gen |
      exact: mk_env_umulo_newer_gen |
      exact: mk_env_saddo_newer_gen |
      exact: mk_env_ssubo_newer_gen |
      exact: mk_env_smulo_newer_gen ].
Qed.

Lemma mk_env_exp_ccache_newer_gen_nocet_var :
  forall (t : SSAVarOrder.t) (m : vm) (c : compcache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (c' : compcache) 
         (E' : env) (g' : generator) (cs : cnf) (ls : word),
    find_cet (QFBV.Evar t) c = None ->
    mk_env_exp_ccache m c s E g (QFBV.Evar t) = (m', c', E', g', cs, ls) ->
    (g <=? g')%positive.
Proof.
  move=> v m c s E g m' c' E' g' cs ls Hfcet. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Evar v) c) => [[cse lse] | ];
    last case Hfv : (SSAVM.find v m);
    last case Hv: (mk_env_var E g (SSAStore.acc v s) v) => [[[Ev gv] csv] lsv];
    case=> _ _ _ <- _ _; 
    exact: Pos.leb_refl || exact: (mk_env_var_newer_gen Hv).
Qed.

Lemma mk_env_exp_ccache_newer_gen_nocet_const :
  forall (b : bits) (m : vm) (c : compcache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (c' : compcache) 
         (E' : env) (g' : generator) (cs : cnf) (ls : word),
    find_cet (QFBV.Econst b) c = None ->
    mk_env_exp_ccache m c s E g (QFBV.Econst b) = (m', c', E', g', cs, ls) ->
    (g <=? g')%positive.
Proof.
  move=> bs m c s E g m' c' E' g' cs ls Hfcet. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Econst bs) c) => [[csop lsop] | ];
    case=> _ _ _ <- _ _; exact: Pos.leb_refl. 
Qed.

Lemma mk_env_exp_ccache_newer_gen_nocet_unop :
  forall (op : QFBV.eunop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) -> 
        (g <=? g')%positive) ->
    forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
           (g : generator) (m' : vm) (c' : compcache) (E' : env) 
           (g' : generator) (cs : cnf) (ls : word),
      find_cet (QFBV.Eunop op e1) c = None ->
      mk_env_exp_ccache m c s E g (QFBV.Eunop op e1) = (m', c', E', g', cs, ls) ->
      (g <=? g')%positive.
Proof.
  move=> op e1 IH1 m c s E g m' c' E' g' cs ls Hfcet. rewrite /= Hfcet.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1) => Hgg1.
  case Hfhet : (find_het (QFBV.Eunop op e1) c1) => [[csop lsop] | ].
  - case=> _ _ _ <- _ _. done.
  - case Hop : (mk_env_eunop op E1 g1 ls1) => [[[Eop gop] csop] lsop].
    case=> _ _ _ <- _ _. 
    move: (mk_env_eunop_newer_gen Hop) => Hg1gop.
    exact: (pos_leb_trans Hgg1 Hg1gop).
Qed.

Lemma mk_env_exp_ccache_newer_gen_nocet_binop :
  forall (op : QFBV.ebinop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) -> 
        (g <=? g')%positive) ->
    forall e2 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) -> 
          (g <=? g')%positive) ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (ls : word),
        find_cet (QFBV.Ebinop op e1 e2) c = None ->
        mk_env_exp_ccache m c s E g (QFBV.Ebinop op e1 e2) = (m', c', E', g', cs, ls) ->
        (g <=? g')%positive.
Proof.
  move=> op e1 IH1 e2 IH2 m c s E g m' c' E' g' cs ls Hfcet. rewrite /= Hfcet.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1) => Hgg1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2) => Hg1g2.
  move: (pos_leb_trans Hgg1 Hg1g2) => Hgg2.
  case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csop lsop] | ].
  - case=> _ _ _ <- _ _. done.
  - case Hop : (mk_env_ebinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lsop].
    case=> _ _ _ <- _ _. 
    move: (mk_env_ebinop_newer_gen Hop) => Hg2gop.
    exact: (pos_leb_trans Hgg2 Hg2gop).
Qed.

Lemma mk_env_exp_ccache_newer_gen_nocet_ite :
  forall b : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g b = (m', c', E', g', cs, l) ->
        (g <=? g')%positive) ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
          (g <=? g')%positive) ->
      forall e2 : QFBV.exp,
        (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
                (g : generator) (m' : vm) (c' : compcache) (E' : env) 
                (g' : generator) (cs : cnf) (ls : word),
            mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
            (g <=? g')%positive) ->
        forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
               (g : generator) (m' : vm) (c' : compcache) (E' : env) 
               (g' : generator) (cs : cnf) (ls : word),
          find_cet (QFBV.Eite b e1 e2) c = None ->
          mk_env_exp_ccache m c s E g (QFBV.Eite b e1 e2) = (m', c', E', g', cs, ls) ->
          (g <=? g')%positive.
Proof.
  move=> b IHb e1 IH1 e2 IH2 m c s E g m' c' E' g' cs ls Hfcet. rewrite /= Hfcet.
  case Hb : (mk_env_bexp_ccache m c s E g b) => [[[[[mb cb] Eb] gb] csb] lb].
  case He1 : (mk_env_exp_ccache mb cb s Eb gb e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IHb _ _ _ _ _ _ _ _ _ _ _ Hb) => Hggb.
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1) => Hgbg1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2) => Hg1g2.
  move: (pos_leb_trans Hggb (pos_leb_trans Hgbg1 Hg1g2)) => Hgg2.
  case Hfhet : (find_het (QFBV.Eite b e1 e2) c2) => [[csop lsop] | ].
  - case=> _ _ _ <- _ _. done.
  - case Hop : (mk_env_ite E2 g2 lb ls1 ls2) => [[[Eop gop] csop] lsop].
    case=> _ _ _ <- _ _. 
    move: (mk_env_ite_newer_gen Hop) => Hg2gop.
    exact: (pos_leb_trans Hgg2 Hg2gop).
Qed.

Lemma mk_env_bexp_ccache_newer_gen_nocbt_false :
  forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
         (g : generator) (m' : vm) (c' : compcache) (E' : env) 
         (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Bfalse c = None ->
    mk_env_bexp_ccache m c s E g QFBV.Bfalse = (m', c', E', g', cs, l) ->
    (g <=? g')%positive.
Proof.
  move=> m c s E g m' c' E' g' cs l Hfcbt. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Bfalse) c) => [[csop lop] | ];
    case=> _ _ _ <- _ _; exact: Pos.leb_refl. 
Qed.

Lemma mk_env_bexp_ccache_newer_gen_nocbt_true :
  forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
         (g : generator) (m' : vm) (c' : compcache) (E' : env) 
         (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Btrue c = None ->
    mk_env_bexp_ccache m c s E g QFBV.Btrue = (m', c', E', g', cs, l) ->
    (g <=? g')%positive.
Proof.
  move=> m c s E g m' c' E' g' cs l Hfcbt. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Btrue) c) => [[csop lop] | ];
    case=> _ _ _ <- _ _; exact: Pos.leb_refl. 
Qed.

Lemma mk_env_bexp_ccache_newer_gen_nocbt_binop :
  forall (op : QFBV.bbinop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) -> 
        (g <=? g')%positive) ->
    forall e2 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
          (g <=? g')%positive) ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bbinop op e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bbinop op e1 e2) = (m', c', E', g', cs, l) ->
        (g <=? g')%positive.
Proof.
  move=> op e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt. rewrite /= Hfcbt.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1) => Hgg1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2) => Hg1g2.
  move: (pos_leb_trans Hgg1 Hg1g2) => Hgg2.
  case Hfhbt : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[csop lop] | ].
  - case=> _ _ _ <- _ _. done.
  - case Hop : (mk_env_bbinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lop].
    case=> _ _ _ <- _ _. 
    move: (mk_env_bbinop_newer_gen Hop) => Hg2gop.
    exact: (pos_leb_trans Hgg2 Hg2gop).
Qed.

Lemma mk_env_bexp_ccache_newer_gen_nocbt_lneg :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        (g <=? g')%positive) ->
    forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
           (g : generator) (m' : vm) (c' : compcache) (E' : env) 
           (g' : generator) (cs : cnf) (l : literal),
      find_cbt (QFBV.Blneg e1) c = None ->
      mk_env_bexp_ccache m c s E g (QFBV.Blneg e1) = (m', c', E', g', cs, l) ->
      (g <=? g')%positive.
Proof.
  move=> e1 IH1 m c s E g m' c' E' g' cs l Hfcbt. 
  rewrite /mk_env_bexp_ccache -/mk_env_bexp_ccache Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1) => Hgg1.
  case Hfhbt : (find_hbt (QFBV.Blneg e1) c1) => [[csop lop] | ].
  - case=> _ _ _ <- _ _. done.
  - case Hop : (mk_env_lneg E1 g1 l1) => [[[Eop gop] csop] lop].
    case=> _ _ _ <- _ _. 
    move: (mk_env_lneg_newer_gen Hop) => Hg1gop.
    exact: (pos_leb_trans Hgg1 Hg1gop).
Qed.

Lemma mk_env_bexp_ccache_newer_gen_nocbt_conj :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) -> 
        (g <=? g')%positive) ->
    forall e2 : QFBV.bexp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (l : literal),
          mk_env_bexp_ccache m c s E g e2 = (m', c', E', g', cs, l) -> 
          (g <=? g')%positive) ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bconj e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bconj e1 e2) = (m', c', E', g', cs, l) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt. 
  rewrite /mk_env_bexp_ccache -/mk_env_bexp_ccache Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  case He2 : (mk_env_bexp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1) => Hgg1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2) => Hg1g2.
  move: (pos_leb_trans Hgg1 Hg1g2) => Hgg2.
  case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csop lop] | ].
  - case=> _ _ _ <- _ _. done.
  - case Hop : (mk_env_conj E2 g2 l1 l2) => [[[Eop gop] csop] lop].
    case=> _ _ _ <- _ _. 
    move: (mk_env_conj_newer_gen Hop) => Hg2gop.
    exact: (pos_leb_trans Hgg2 Hg2gop).
Qed.

Lemma mk_env_bexp_ccache_newer_gen_nocbt_disj :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) -> 
        (g <=? g')%positive) ->
    forall e2 : QFBV.bexp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (l : literal),
          mk_env_bexp_ccache m c s E g e2 = (m', c', E', g', cs, l) -> 
          (g <=? g')%positive) ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bdisj e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bdisj e1 e2) = (m', c', E', g', cs, l) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt. 
  rewrite /mk_env_bexp_ccache -/mk_env_bexp_ccache Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  case He2 : (mk_env_bexp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1) => Hgg1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2) => Hg1g2.
  move: (pos_leb_trans Hgg1 Hg1g2) => Hgg2.
  case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csop lop] | ].
  - case=> _ _ _ <- _ _. done.
  - case Hop : (mk_env_disj E2 g2 l1 l2) => [[[Eop gop] csop] lop].
    case=> _ _ _ <- _ _. 
    move: (mk_env_disj_newer_gen Hop) => Hg2gop.
    exact: (pos_leb_trans Hgg2 Hg2gop).
Qed.


Corollary mk_env_exp_ccache_newer_gen :
  forall (e : QFBV.exp) m c s E g m' c' E' g' cs ls,
    mk_env_exp_ccache m c s E g e = (m', c', E', g', cs, ls) ->
    (g <=? g')%positive
  with
    mk_env_bexp_ccache_newer_gen :
      forall e m c s E g m' c' E' g' cs l,
        mk_env_bexp_ccache m c s E g e = (m', c', E', g', cs, l) ->
        (g <=? g')%positive.
Proof.
  (* exp *)
  set IHe := mk_env_exp_ccache_newer_gen.
  set IHb := mk_env_bexp_ccache_newer_gen.
  move=> e m c s E g m' c' E' g' cs ls.
  case Hfcet: (find_cet e c) => [[cse lse] | ]. 
  - rewrite mk_env_exp_ccache_equation Hfcet /=.
    case=> _ _ _ <- _ _. exact: Pos.leb_refl.
  - move: e m c s E g m' c' E' g' cs ls Hfcet.
    case.
    + exact: mk_env_exp_ccache_newer_gen_nocet_var.
    + exact: mk_env_exp_ccache_newer_gen_nocet_const.
    + move=> op e1; move: op e1 (IHe e1).
      exact: mk_env_exp_ccache_newer_gen_nocet_unop.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_newer_gen_nocet_binop.
    + move=> b e1 e2; move: b (IHb b) e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_newer_gen_nocet_ite.
  (* bexp *)
  set IHe := mk_env_exp_ccache_newer_gen.
  set IHb := mk_env_bexp_ccache_newer_gen.
  move=> e m c s E g m' c' E' g' cs l.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite mk_env_bexp_ccache_equation Hfcbt /=.
    case=> _ _ _ <- _ _. exact: Pos.leb_refl.
  - move: e m c s E g m' c' E' g' cs l Hfcbt.
    case.
    + exact: mk_env_bexp_ccache_newer_gen_nocbt_false.
    + exact: mk_env_bexp_ccache_newer_gen_nocbt_true.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_bexp_ccache_newer_gen_nocbt_binop.
    + move=> e1; move: e1 (IHb e1).
      exact: mk_env_bexp_ccache_newer_gen_nocbt_lneg.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_newer_gen_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_newer_gen_nocbt_disj.
Qed.


(* = mk_env_exp_ccache_newer_vm and mk_env_bexp_ccache_newer_vm = *)

Lemma mk_env_exp_ccache_newer_vm_nocet_var :
  forall (t : SSAVarOrder.t) (m : vm) (c : compcache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (c' : compcache) 
         (E' : env) (g' : generator) (cs : cnf) (ls : word),
    find_cet (QFBV.Evar t) c = None ->
    mk_env_exp_ccache m c s E g (QFBV.Evar t) = (m', c', E', g', cs, ls) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> v m c s E g m' c' E' g' cs ls Hfcet. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Evar v) c) => [[cse lse] | ].
  - case=> <- _ _ <- _ _ Hgm. done.
  - case Hfv : (SSAVM.find v m).
    + case=> <- _ _ <- _ _ Hgm. done.
    + case Hv: (mk_env_var E g (SSAStore.acc v s) v) => [[[Ev gv] csv] lsv].
      case=> <- _ _ <- _ _ Hgm. move=> x lxs. case Hxv: (x == v).
      * rewrite (SSAVM.Lemmas.find_add_eq Hxv) .
        case => <-; exact: (mk_env_var_newer_res Hv).
      * move/negP: Hxv => Hxv. rewrite (SSAVM.Lemmas.find_add_neq Hxv) => Hfindx.
        move: (Hgm x lxs Hfindx) => Hglxs.
        apply: (newer_than_lits_le_newer Hglxs). 
        exact: (mk_env_var_newer_gen Hv).
Qed.

Lemma mk_env_exp_ccache_newer_vm_nocet_const :
  forall (b : bits) (m : vm) (c : compcache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (c' : compcache) 
         (E' : env) (g' : generator) (cs : cnf) (ls : word),
    find_cet (QFBV.Econst b) c = None ->
    mk_env_exp_ccache m c s E g (QFBV.Econst b) = (m', c', E', g', cs, ls) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> bs m c s E g m' c' E' g' cs ls Hfcet Hmk Hgm. 
  move: Hmk. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Econst bs) c) => [[csop lsop] | ];
    case=> <- _ _ <- _ _; done.
Qed.

Lemma mk_env_exp_ccache_newer_vm_nocet_unop :
  forall (op : QFBV.eunop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
           (g : generator) (m' : vm) (c' : compcache) (E' : env) 
           (g' : generator) (cs : cnf) (ls : word),
      find_cet (QFBV.Eunop op e1) c = None ->
      mk_env_exp_ccache m c s E g (QFBV.Eunop op e1) = (m', c', E', g', cs, ls) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> op e1 IH1 m c s E g m' c' E' g' cs ls Hfcet Hmk Hgm. 
  move: Hmk. rewrite /= Hfcet.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm) => Hg1m1.
  case Hfhet : (find_het (QFBV.Eunop op e1) c1) => [[csop lsop] | ].
  - case=> <- _ _ <- _ _. done.
  - case Hop : (mk_env_eunop op E1 g1 ls1) => [[[Eop gop] csop] lsop].
    case=> <- _ _ <- _ _. 
    move: (mk_env_eunop_newer_gen Hop) => Hg1gop.
    exact: (newer_than_vm_le_newer Hg1m1 Hg1gop).
Qed.

Lemma mk_env_exp_ccache_newer_vm_nocet_binop :
  forall (op : QFBV.ebinop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall e2 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (ls : word),
        find_cet (QFBV.Ebinop op e1 e2) c = None ->
        mk_env_exp_ccache m c s E g (QFBV.Ebinop op e1 e2) = (m', c', E', g', cs, ls) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> op e1 IH1 e2 IH2 m c s E g m' c' E' g' cs ls Hfcet Hmk Hgm. 
  move: Hmk. rewrite /= Hfcet.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1) => Hg2m2.
  case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csop lsop] | ].
  - case=> <- _ _ <- _ _. done.
  - case Hop : (mk_env_ebinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lsop].
    case=> <- _ _ <- _ _. 
    move: (mk_env_ebinop_newer_gen Hop) => Hg2gop.
    exact: (newer_than_vm_le_newer Hg2m2 Hg2gop).
Qed.

Lemma mk_env_exp_ccache_newer_vm_nocet_ite :
  forall b : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g b = (m', c', E', g', cs, l) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall e2 : QFBV.exp,
        (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
                (g : generator) (m' : vm) (c' : compcache) (E' : env) 
                (g' : generator) (cs : cnf) (ls : word),
            mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
            newer_than_vm g m -> newer_than_vm g' m') ->
        forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
               (g : generator) (m' : vm) (c' : compcache) (E' : env) 
               (g' : generator) (cs : cnf) (ls : word),
          find_cet (QFBV.Eite b e1 e2) c = None ->
          mk_env_exp_ccache m c s E g (QFBV.Eite b e1 e2) = (m', c', E', g', cs, ls) ->
          newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> b IHb e1 IH1 e2 IH2 m c s E g m' c' E' g' cs ls Hfcet Hmk Hgm. 
  move: Hmk. rewrite /= Hfcet.
  case Hb : (mk_env_bexp_ccache m c s E g b) => [[[[[mb cb] Eb] gb] csb] lb].
  case He1 : (mk_env_exp_ccache mb cb s Eb gb e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IHb _ _ _ _ _ _ _ _ _ _ _ Hb Hgm) => Hgbmb.
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgbmb) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1) => Hg2m2.
  case Hfhet : (find_het (QFBV.Eite b e1 e2) c2) => [[csop lsop] | ].
  - case=> <- _ _ <- _ _. done.
  - case Hop : (mk_env_ite E2 g2 lb ls1 ls2) => [[[Eop gop] csop] lsop].
    case=> <- _ _ <- _ _. 
    move: (mk_env_ite_newer_gen Hop) => Hg2gop.
    exact: (newer_than_vm_le_newer Hg2m2 Hg2gop).
Qed.

Lemma mk_env_bexp_ccache_newer_vm_nocbt_false :
  forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
         (g : generator) (m' : vm) (c' : compcache) (E' : env) 
         (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Bfalse c = None ->
    mk_env_bexp_ccache m c s E g QFBV.Bfalse = (m', c', E', g', cs, l) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> m c s E g m' c' E' g' cs ls Hfcbt Hmk Hgm. 
  move: Hmk. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Bfalse) c) => [[csop lop] | ];
    case=> <- _ _ <- _ _; done.
Qed.

Lemma mk_env_bexp_ccache_newer_vm_nocbt_true :
  forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
         (g : generator) (m' : vm) (c' : compcache) (E' : env) 
         (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Btrue c = None ->
    mk_env_bexp_ccache m c s E g QFBV.Btrue = (m', c', E', g', cs, l) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> m c s E g m' c' E' g' cs ls Hfcbt Hmk Hgm. 
  move: Hmk. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Btrue) c) => [[csop lop] | ];
    case=> <- _ _ <- _ _; done.
Qed.

Lemma mk_env_bexp_ccache_newer_vm_nocbt_binop :
  forall (op : QFBV.bbinop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall e2 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bbinop op e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bbinop op e1 e2) = (m', c', E', g', cs, l) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> op e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt Hmk Hgm. 
  move: Hmk. rewrite /= Hfcbt.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1) => Hg2m2.
  case Hfhbt : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[csop lop] | ].
  - case=> <- _ _ <- _ _. done.
  - case Hop : (mk_env_bbinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lop].
    case=> <- _ _ <- _ _. 
    move: (mk_env_bbinop_newer_gen Hop) => Hg2gop.
    exact: (newer_than_vm_le_newer Hg2m2 Hg2gop).
Qed.

Lemma mk_env_bexp_ccache_newer_vm_nocbt_lneg :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
           (g : generator) (m' : vm) (c' : compcache) (E' : env) 
           (g' : generator) (cs : cnf) (l : literal),
      find_cbt (QFBV.Blneg e1) c = None ->
      mk_env_bexp_ccache m c s E g (QFBV.Blneg e1) = (m', c', E', g', cs, l) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 m c s E g m' c' E' g' cs l Hfcbt Hmk Hgm. 
  move: Hmk. rewrite /mk_env_bexp_ccache -/mk_env_bexp_ccache Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm) => Hg1m1.
  case Hfhbt : (find_hbt (QFBV.Blneg e1) c1) => [[csop lop] | ].
  - case=> <- _ _ <- _ _. done.
  - case Hop : (mk_env_lneg E1 g1 l1) => [[[Eop gop] csop] lop].
    case=> <- _ _ <- _ _. 
    move: (mk_env_lneg_newer_gen Hop) => Hg1gop.
    exact: (newer_than_vm_le_newer Hg1m1 Hg1gop).
Qed.

Lemma mk_env_bexp_ccache_newer_vm_nocbt_conj :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall e2 : QFBV.bexp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (l : literal),
          mk_env_bexp_ccache m c s E g e2 = (m', c', E', g', cs, l) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bconj e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bconj e1 e2) = (m', c', E', g', cs, l) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt Hmk Hgm. 
  move: Hmk. rewrite /mk_env_bexp_ccache -/mk_env_bexp_ccache Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  case He2 : (mk_env_bexp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1) => Hg2m2.
  case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csop lop] | ].
  - case=> <- _ _ <- _ _. done.
  - case Hop : (mk_env_conj E2 g2 l1 l2) => [[[Eop gop] csop] lop].
    case=> <- _ _ <- _ _. 
    move: (mk_env_conj_newer_gen Hop) => Hg2gop.
    exact: (newer_than_vm_le_newer Hg2m2 Hg2gop).
Qed.

Lemma mk_env_bexp_ccache_newer_vm_nocbt_disj :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall e2 : QFBV.bexp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (l : literal),
          mk_env_bexp_ccache m c s E g e2 = (m', c', E', g', cs, l) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bdisj e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bdisj e1 e2) = (m', c', E', g', cs, l) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt Hmk Hgm. 
  move: Hmk. rewrite /mk_env_bexp_ccache -/mk_env_bexp_ccache Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  case He2 : (mk_env_bexp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1) => Hg2m2.
  case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csop lop] | ].
  - case=> <- _ _ <- _ _. done.
  - case Hop : (mk_env_disj E2 g2 l1 l2) => [[[Eop gop] csop] lop].
    case=> <- _ _ <- _ _. 
    move: (mk_env_disj_newer_gen Hop) => Hg2gop.
    exact: (newer_than_vm_le_newer Hg2m2 Hg2gop).
Qed.


Corollary mk_env_exp_ccache_newer_vm :
  forall (e : QFBV.exp) m c s E g m' c' E' g' cs ls,
    mk_env_exp_ccache m c s E g e = (m', c', E', g', cs, ls) ->
    newer_than_vm g m -> newer_than_vm g' m'
  with
    mk_env_bexp_ccache_newer_vm :
      forall e m c s E g m' c' E' g' cs l,
        mk_env_bexp_ccache m c s E g e = (m', c', E', g', cs, l) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  (* exp *)
  set IHe := mk_env_exp_ccache_newer_vm.
  set IHb := mk_env_bexp_ccache_newer_vm.
  move=> e m c s E g m' c' E' g' cs ls.
  case Hfcet: (find_cet e c) => [[cse lse] | ]. 
  - rewrite mk_env_exp_ccache_equation Hfcet /=.
    case=> <- _ _ <- _ _. done.
  - move: e m c s E g m' c' E' g' cs ls Hfcet.
    case.
    + exact: mk_env_exp_ccache_newer_vm_nocet_var.
    + exact: mk_env_exp_ccache_newer_vm_nocet_const.
    + move=> op e1; move: op e1 (IHe e1).
      exact: mk_env_exp_ccache_newer_vm_nocet_unop.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_newer_vm_nocet_binop.
    + move=> b e1 e2; move: b (IHb b) e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_newer_vm_nocet_ite.
  (* bexp *)
  set IHe := mk_env_exp_ccache_newer_vm.
  set IHb := mk_env_bexp_ccache_newer_vm.
  move=> e m c s E g m' c' E' g' cs l.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite mk_env_bexp_ccache_equation Hfcbt /=.
    case=> <- _ _ <- _ _. done.
  - move: e m c s E g m' c' E' g' cs l Hfcbt.
    case.
    + exact: mk_env_bexp_ccache_newer_vm_nocbt_false.
    + exact: mk_env_bexp_ccache_newer_vm_nocbt_true.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_bexp_ccache_newer_vm_nocbt_binop.
    + move=> e1; move: e1 (IHb e1).
      exact: mk_env_bexp_ccache_newer_vm_nocbt_lneg.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_newer_vm_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_newer_vm_nocbt_disj.
Qed.


(* = mk_env_exp_ccache_newer_all_lits and mk_env_bexp_ccache_newer_all_lits = *)

Lemma mk_env_eunop_newer_res op E g ls1 E' g' cs ls :
  mk_env_eunop op E g ls1 = (E', g', cs, ls) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls1 -> 
  newer_than_lits g' ls.
Proof. 
  move=> Hmk Hgtt Hgls1; move: Hmk; 
    case op => [ | | i j | n | n | n | n | n | n | n ] Hmk;
    [ apply (mk_env_not_newer_res Hmk) |
      apply (mk_env_neg_newer_res Hmk) |
      apply (mk_env_extract_newer_res Hmk) |
      apply (mk_env_high_newer_res Hmk) |
      apply (mk_env_low_newer_res Hmk) |
      apply (mk_env_zeroextend_newer_res Hmk) |
      apply (mk_env_signextend_newer_res Hmk) |
      apply (mk_env_repeat_newer_res Hmk) |
      apply (mk_env_rotateleft_newer_res Hmk) |
      apply (mk_env_rotateright_newer_res Hmk) ]; 
    done.
Qed.

Lemma mk_env_ebinop_newer_res op E g ls1 ls2 E' g' cs ls :
  mk_env_ebinop op E g ls1 ls2 = (E', g', cs, ls) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_lits g' ls.
Proof. 
  move=> Hmk Hgtt Hgls1 Hgls2; move: Hmk; case op => Hmk;
    [ apply (mk_env_and_newer_res Hmk) |
      apply (mk_env_or_newer_res Hmk) |
      apply (mk_env_xor_newer_res Hmk) |
      apply (mk_env_add_newer_res Hmk) |
      apply (mk_env_sub_newer_res Hmk) |
      apply (mk_env_mul_newer_res Hmk) |
      apply (mk_env_udiv_newer_res' Hmk) |
      apply (mk_env_umod_newer_res Hmk) |
      apply (mk_env_sdiv_newer_res Hmk) |
      apply (mk_env_srem_newer_res Hmk) |
      apply (mk_env_smod_newer_res Hmk) |
      apply (mk_env_shl_newer_res Hgtt Hgls1 Hgls2 Hmk) |
      apply (mk_env_lshr_newer_res Hgtt Hgls1 Hgls2 Hmk) |
      apply (mk_env_ashr_newer_res Hgtt Hgls1 Hgls2 Hmk) |
      apply (mk_env_concat_newer_res Hmk) |
      apply (mk_env_comp_newer_res Hmk) ]; 
    done.
Qed.

Lemma mk_env_bbinop_newer_res op E g ls1 ls2 E' g' cs l :
  mk_env_bbinop op E g ls1 ls2 = (E', g', cs, l) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_lit g' l.
Proof. 
  move=> Hmk Hgtt Hgls1 Hgls2; move: Hmk; case op => Hmk;
    [ apply (mk_env_eq_newer_res Hmk) |
      apply (mk_env_ult_newer_res Hmk) |
      apply (mk_env_ule_newer_res Hmk) |
      apply (mk_env_ugt_newer_res Hmk) |
      apply (mk_env_uge_newer_res Hmk) |
      apply (mk_env_slt_newer_res Hmk) |
      apply (mk_env_sle_newer_res Hmk) |
      apply (mk_env_sgt_newer_res Hmk) |
      apply (mk_env_sge_newer_res Hmk) |
      apply (mk_env_uaddo_newer_res Hmk) |
      apply (mk_env_usubo_newer_res Hmk) |
      apply (mk_env_umulo_newer_res Hmk) |
      apply (mk_env_saddo_newer_res Hmk) |
      apply (mk_env_ssubo_newer_res Hmk) |
      apply (mk_env_smulo_newer_res Hmk) ];
    done.
Qed.

Lemma mk_env_eunop_newer_cnf op E g ls1 E' g' cs ls :
  mk_env_eunop op E g ls1 = (E', g', cs, ls) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls1 -> 
  newer_than_cnf g' cs.
Proof. 
  move=> Hmk Hgtt Hgls1; move: Hmk; 
    case op => [ | | i j | n | n | n | n | n | n | n ] Hmk;
    [ apply (mk_env_not_newer_cnf Hmk) |
      apply (mk_env_neg_newer_cnf Hmk) |
      apply (mk_env_extract_newer_cnf Hmk) |
      apply (mk_env_high_newer_cnf Hmk) |
      apply (mk_env_low_newer_cnf Hmk) |
      apply (mk_env_zeroextend_newer_cnf Hmk) |
      apply (mk_env_signextend_newer_cnf Hmk) |
      apply (mk_env_repeat_newer_cnf Hmk) |
      apply (mk_env_rotateleft_newer_cnf Hmk) |
      apply (mk_env_rotateright_newer_cnf Hmk) ]; 
    done.
Qed.

Lemma mk_env_ebinop_newer_cnf op E g ls1 ls2 E' g' cs ls :
  mk_env_ebinop op E g ls1 ls2 = (E', g', cs, ls) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof. 
  move=> Hmk Hgtt Hgls1 Hgls2; move: Hmk; case op => Hmk;
    [ apply (mk_env_and_newer_cnf Hmk) |
      apply (mk_env_or_newer_cnf Hmk) |
      apply (mk_env_xor_newer_cnf Hmk) |
      apply (mk_env_add_newer_cnf Hmk) |
      apply (mk_env_sub_newer_cnf Hmk) |
      apply (mk_env_mul_newer_cnf Hmk) |
      apply (mk_env_udiv_newer_cnf' Hmk) |
      apply (mk_env_umod_newer_cnf Hmk) |
      apply (mk_env_sdiv_newer_cnf Hmk) |
      apply (mk_env_srem_newer_cnf Hmk) |
      apply (mk_env_smod_newer_cnf Hmk) |
      apply (mk_env_shl_newer_cnf Hmk) |
      apply (mk_env_lshr_newer_cnf Hmk) |
      apply (mk_env_ashr_newer_cnf Hmk) |
      apply (mk_env_concat_newer_cnf Hmk) |
      apply (mk_env_comp_newer_cnf Hmk) ]; 
    done.
Qed.

Lemma mk_env_bbinop_newer_cnf op E g ls1 ls2 E' g' cs l :
  mk_env_bbinop op E g ls1 ls2 = (E', g', cs, l) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof. 
  move=> Hmk Hgtt Hgls1 Hgls2; move: Hmk; case op => Hmk;
    [ apply (mk_env_eq_newer_cnf Hmk) |
      apply (mk_env_ult_newer_cnf Hmk) |
      apply (mk_env_ule_newer_cnf Hmk) |
      apply (mk_env_ugt_newer_cnf Hmk) |
      apply (mk_env_uge_newer_cnf Hmk) |
      apply (mk_env_slt_newer_cnf Hmk) |
      apply (mk_env_sle_newer_cnf Hmk) |
      apply (mk_env_sgt_newer_cnf Hmk) |
      apply (mk_env_sge_newer_cnf Hmk) |
      apply (mk_env_uaddo_newer_cnf Hmk) |
      apply (mk_env_usubo_newer_cnf Hmk) |
      apply (mk_env_umulo_newer_cnf Hmk) |
      apply (mk_env_saddo_newer_cnf Hmk) |
      apply (mk_env_ssubo_newer_cnf Hmk) |
      apply (mk_env_smulo_newer_cnf Hmk) ];
    done.
Qed.

Lemma mk_env_exp_ccache_newer_all_lits_nocet_var :
  forall (t : SSAVarOrder.t) (m : vm) (c : compcache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (c' : compcache) 
         (E' : env) (g' : generator) (cs : cnf) (ls : word),
    find_cet (QFBV.Evar t) c = None ->
    mk_env_exp_ccache m c s E g (QFBV.Evar t) = (m', c', E', g', cs, ls) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    well_formed c ->
    newer_than_cache g c ->
    newer_than_lits g' ls /\ newer_than_cnf g' cs /\ newer_than_cache g' c'.
Proof.
  move=> v m c s E g m' c' E' g' cs ls Hfcet. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Evar v) c) => [[cse lse] | ].
  - case=> _ <- _ <- <- <- Hgm Hgtt Hwfc Hgc. 
    move: (newer_than_cache_find_het Hgc Hfhet) => [Hgcse Hglse].
    repeat (split; first done). by rewrite -newer_than_cache_add_cet.
  - case Hfv : (SSAVM.find v m) => [lsv | ].
    + case=> _ <- _ <- <- <- Hgm Hgtt Hwfc Hgc. 
      move: (Hgm v _ Hfv) => Hglsv.
      repeat (split; first done). rewrite -newer_than_cache_add_cet.
      by apply newer_than_cache_add_het.
    + case Hv: (mk_env_var E g (SSAStore.acc v s) v) => [[[Ev gv] csv] lsv].
      case=> _ <- _ <- <- <- Hgm Hgtt Hwfc Hgc. 
      move: (mk_env_var_newer_res Hv) => Hgvlsv.
      move: (mk_env_var_newer_cnf Hv) => Hgvcsv.
      move: (mk_env_var_newer_gen Hv) => Hggv.
      move: (newer_than_cache_le_newer Hgc Hggv) => {Hgc} Hgvc.
      repeat (split; first done). rewrite -newer_than_cache_add_cet.
      by apply newer_than_cache_add_het.
Qed.

Lemma mk_env_exp_ccache_newer_all_lits_nocet_const :
  forall (b : bits) (m : vm) (c : compcache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (c' : compcache) 
         (E' : env) (g' : generator) (cs : cnf) (ls : word),
    find_cet (QFBV.Econst b) c = None ->
    mk_env_exp_ccache m c s E g (QFBV.Econst b) = (m', c', E', g', cs, ls) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    well_formed c ->
    newer_than_cache g c ->
    newer_than_lits g' ls /\ newer_than_cnf g' cs /\ newer_than_cache g' c'.
Proof.
  move=> bs m c s E g m' c' E' g' cs ls Hfcet Hmk Hgm Hgtt Hwfc Hgc. 
  move: Hmk. rewrite /mk_env_exp_ccache -/mk_env_exp_ccache Hfcet.
  case Hfhet : (find_het (QFBV.Econst bs) c) => [[csop lsop] | ].
  - case=> _ <- _ <- <- <-.
    move: (newer_than_cache_find_het Hgc Hfhet) => [Hgcsop Hglsop].
    repeat (split; first done).
    by rewrite -newer_than_cache_add_cet.
  - case Hop : (mk_env_const E g bs) => [[[Eop gop] csop] lsop].
    case=> _ <- _ <- <- <-.
    move: (mk_env_const_newer_res Hop Hgtt) => Hgoplsop.
    move: (mk_env_const_newer_cnf Hop Hgtt) => Hgopcsop.
    move: (mk_env_const_newer_gen Hop) => Hggop.
    repeat (split; first done). 
    move: (newer_than_cache_le_newer Hgc Hggop) => {Hgc} Hgopc.
    rewrite -newer_than_cache_add_cet. by apply newer_than_cache_add_het.
Qed.

Lemma mk_env_exp_ccache_newer_all_lits_nocet_unop :
  forall (op : QFBV.eunop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c ->
        newer_than_lits g' ls /\ newer_than_cnf g' cs /\ newer_than_cache g' c') ->
    forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
           (g : generator) (m' : vm) (c' : compcache) (E' : env) 
           (g' : generator) (cs : cnf) (ls : word),
      find_cet (QFBV.Eunop op e1) c = None ->
      mk_env_exp_ccache m c s E g (QFBV.Eunop op e1) = (m', c', E', g', cs, ls) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      well_formed c ->
      newer_than_cache g c ->
      newer_than_lits g' ls /\ newer_than_cnf g' cs /\ newer_than_cache g' c'.
Proof.
  move=> op e1 IH1 m c s E g m' c' E' g' cs ls Hfcet Hmk Hgm Hgtt Hwfc Hgc. 
  move: Hmk. rewrite /= Hfcet.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm Hgtt Hwfc Hgc) => [Hg1ls1 [Hg1cs1 Hg1c1]].
  case Hfhet : (find_het (QFBV.Eunop op e1) c1) => [[csop lsop] | ].
  - case=> _ <- _ <- <- <-.
    move: (newer_than_cache_find_het Hg1c1 Hfhet) => [Hg1csop Hg1lsop].
    split; first done. split.
    + rewrite !newer_than_cnf_catrev. by rewrite Hg1cs1 Hg1csop.
    + by rewrite -newer_than_cache_add_cet.
  - case Hop : (mk_env_eunop op E1 g1 ls1) => [[[Eop gop] csop] lsop].
    case=> _ <- _ <- <- <-.
    move: (mk_env_exp_ccache_newer_gen He1) => Hgg1.
    move: (newer_than_lit_le_newer Hgtt Hgg1) => {Hgtt} Hg1tt.
    move: (mk_env_eunop_newer_res Hop Hg1tt Hg1ls1) => Hgoplsop.
    move: (mk_env_eunop_newer_cnf Hop Hg1tt Hg1ls1) => Hgopcsop.
    move: (mk_env_eunop_newer_gen Hop) => Hg1gop.
    split; first done. split.
    + rewrite !newer_than_cnf_catrev. 
      move: (newer_than_cnf_le_newer Hg1cs1 Hg1gop) => {Hg1cs1} Hgopcs1.
      by rewrite Hgopcs1 Hgopcsop.
    + move: (newer_than_cache_le_newer Hg1c1 Hg1gop) => {Hg1c1} Hgopc1.
      rewrite -newer_than_cache_add_cet. by apply newer_than_cache_add_het.
Qed.

Lemma mk_env_exp_ccache_newer_all_lits_nocet_binop :
  forall (op : QFBV.ebinop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c ->
        newer_than_lits g' ls /\ newer_than_cnf g' cs /\ newer_than_cache g' c') ->
    forall e2 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed c ->
          newer_than_cache g c ->
          newer_than_lits g' ls /\ newer_than_cnf g' cs /\ newer_than_cache g' c') ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (ls : word),
        find_cet (QFBV.Ebinop op e1 e2) c = None ->
        mk_env_exp_ccache m c s E g (QFBV.Ebinop op e1 e2) = (m', c', E', g', cs, ls) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c ->
        newer_than_lits g' ls /\ newer_than_cnf g' cs /\ newer_than_cache g' c'.
Proof.
  move=> op e1 IH1 e2 IH2 m c s E g m' c' E' g' cs ls Hfcet Hmk Hgm Hgtt Hwfc Hgc. 
  move: Hmk. rewrite /= Hfcet.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm Hgtt Hwfc Hgc) => [Hg1ls1 [Hg1cs1 Hg1c1]].
  move: (mk_env_exp_ccache_newer_vm He1 Hgm) => Hg1m1.
  move: (mk_env_exp_ccache_newer_gen He1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => {Hgtt} Hg1tt.
  move: (mk_env_exp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) 
        => [Hg2ls2 [Hg2cs2 Hg2c2]].
  move: (mk_env_exp_ccache_newer_gen He2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1cs1 Hg1g2) => {Hg1cs1} Hg2cs1.
  case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csop lsop] | ].
  - case=> _ <- _ <- <- <-.
    move: (newer_than_cache_find_het Hg2c2 Hfhet) => [Hg2csop Hg2lsop].
    split; first done. split.
    + rewrite !newer_than_cnf_catrev. by rewrite Hg2cs1 Hg2cs2 Hg2csop.
    + by rewrite -newer_than_cache_add_cet.
  - case Hop : (mk_env_ebinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lsop].
    case=> _ <- _ <- <- <-.
    move: (newer_than_lit_le_newer Hg1tt Hg1g2) => {Hg1tt} Hg2tt.
    move: (newer_than_lits_le_newer Hg1ls1 Hg1g2) => {Hg1ls1} Hg2ls1.
    move: (mk_env_ebinop_newer_res Hop Hg2tt Hg2ls1 Hg2ls2) => Hgoplsop.
    move: (mk_env_ebinop_newer_cnf Hop Hg2tt Hg2ls1 Hg2ls2) => Hgopcsop.
    move: (mk_env_ebinop_newer_gen Hop) => Hg2gop.
    split; first done. split.
    + rewrite !newer_than_cnf_catrev. 
      move: (newer_than_cnf_le_newer Hg2cs1 Hg2gop) => {Hg2cs1} Hgopcs1.
      move: (newer_than_cnf_le_newer Hg2cs2 Hg2gop) => {Hg2cs2} Hgopcs2.
      by rewrite Hgopcs1 Hgopcs2 Hgopcsop.
    + move: (newer_than_cache_le_newer Hg2c2 Hg2gop) => {Hg2c2} Hgopc2.
      rewrite -newer_than_cache_add_cet. by apply newer_than_cache_add_het.
Qed.

Lemma mk_env_exp_ccache_newer_all_lits_nocet_ite :
  forall b : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g b = (m', c', E', g', cs, l) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c ->
        newer_than_lit g' l /\ newer_than_cnf g' cs /\ newer_than_cache g' c') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed c ->
          newer_than_cache g c ->
          newer_than_lits g' ls /\ newer_than_cnf g' cs /\ newer_than_cache g' c') ->
      forall e2 : QFBV.exp,
        (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
                (g : generator) (m' : vm) (c' : compcache) (E' : env) 
                (g' : generator) (cs : cnf) (ls : word),
            mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
            newer_than_vm g m ->
            newer_than_lit g lit_tt ->
            well_formed c ->
            newer_than_cache g c ->
            newer_than_lits g' ls /\ newer_than_cnf g' cs 
            /\ newer_than_cache g' c') ->
        forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
               (g : generator) (m' : vm) (c' : compcache) (E' : env) 
               (g' : generator) (cs : cnf) (ls : word),
          find_cet (QFBV.Eite b e1 e2) c = None ->
          mk_env_exp_ccache m c s E g (QFBV.Eite b e1 e2) = (m', c', E', g', cs, ls) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed c ->
          newer_than_cache g c ->
          newer_than_lits g' ls /\ newer_than_cnf g' cs /\ newer_than_cache g' c'.
Proof.
  move=> b IHb e1 IH1 e2 IH2 m c s E g m' c' E' g' cs ls Hfcet 
           Hmk Hgm Hgtt Hwfc Hgc. 
  move: Hmk. rewrite /= Hfcet.
  case Hb : (mk_env_bexp_ccache m c s E g b) => [[[[[mb cb] Eb] gb] csb] lb].
  case He1 : (mk_env_exp_ccache mb cb s Eb gb e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IHb _ _ _ _ _ _ _ _ _ _ _ Hb Hgm Hgtt Hwfc Hgc) => [Hgblb [Hgbcsb Hgbcb]].
  move: (mk_env_bexp_ccache_newer_vm Hb Hgm) => Hgbmb.
  move: (mk_env_bexp_ccache_newer_gen Hb) => Hggb.
  move: (newer_than_lit_le_newer Hgtt Hggb) => {Hgtt} Hgbtt.
  move: (mk_env_bexp_ccache_well_formed Hb Hwfc) => Hwfcb.
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgbmb Hgbtt Hwfcb Hgbcb) 
        => [Hg1ls1 [Hg1cs1 Hg1c1]].
  move: (mk_env_exp_ccache_newer_vm He1 Hgbmb) => Hg1m1.
  move: (mk_env_exp_ccache_newer_gen He1) => Hgbg1.
  move: (newer_than_lit_le_newer Hgbtt Hgbg1) => {Hgbtt} Hg1tt.
  move: (mk_env_exp_ccache_well_formed He1 Hwfcb) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) 
        => [Hg2ls2 [Hg2cs2 Hg2c2]].
  move: (newer_than_cnf_le_newer Hgbcsb Hgbg1) => {Hgbcsb} Hg1csb.
  move: (mk_env_exp_ccache_newer_gen He2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1csb Hg1g2) => {Hg1csb} Hg2csb.
  move: (newer_than_cnf_le_newer Hg1cs1 Hg1g2) => {Hg1cs1} Hg2cs1.
  case Hfhet : (find_het (QFBV.Eite b e1 e2) c2) => [[csop lsop] | ].
  - case=> _ <- _ <- <- <-.
    move: (newer_than_cache_find_het Hg2c2 Hfhet) => [Hg2csop Hg2lsop].
    split; first done. split.
    + rewrite !newer_than_cnf_catrev. by rewrite Hg2csb Hg2cs1 Hg2cs2 Hg2csop.
    + by rewrite -newer_than_cache_add_cet.
  - case Hop : (mk_env_ite E2 g2 lb ls1 ls2) => [[[Eop gop] csop] lsop].
    case=> _ <- _ <- <- <-.
    move: (newer_than_lit_le_newer Hg1tt Hg1g2) => {Hg1tt} Hg2tt.
    move: (newer_than_lit_le_newer Hgblb Hgbg1) => {Hgblb} Hg1lb.
    move: (newer_than_lit_le_newer Hg1lb Hg1g2) => {Hg1lb} Hg2lb.
    move: (newer_than_lits_le_newer Hg1ls1 Hg1g2) => {Hg1ls1} Hg2ls1.
    move: (mk_env_ite_newer_res Hop) => Hgoplsop.
    move: (mk_env_ite_newer_cnf Hop Hg2tt Hg2lb Hg2ls1 Hg2ls2) => Hgopcsop.
    move: (mk_env_ite_newer_gen Hop) => Hg2gop.
    split; first done. split.
    + rewrite !newer_than_cnf_catrev. 
      move: (newer_than_cnf_le_newer Hg2csb Hg2gop) => {Hg2csb} Hgopcsb.
      move: (newer_than_cnf_le_newer Hg2cs1 Hg2gop) => {Hg2cs1} Hgopcs1.
      move: (newer_than_cnf_le_newer Hg2cs2 Hg2gop) => {Hg2cs2} Hgopcs2.
      by rewrite Hgopcsb Hgopcs1 Hgopcs2 Hgopcsop.
    + move: (newer_than_cache_le_newer Hg2c2 Hg2gop) => {Hg2c2} Hgopc2.
      rewrite -newer_than_cache_add_cet. by apply newer_than_cache_add_het.
Qed.

Lemma mk_env_bexp_ccache_newer_all_lits_nocbt_false :
  forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
         (g : generator) (m' : vm) (c' : compcache) (E' : env) 
         (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Bfalse c = None ->
    mk_env_bexp_ccache m c s E g QFBV.Bfalse = (m', c', E', g', cs, l) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    well_formed c ->
    newer_than_cache g c ->
    newer_than_lit g' l /\ newer_than_cnf g' cs /\ newer_than_cache g' c'.
Proof.
  move=> m c s E g m' c' E' g' cs l Hfcbt Hmk Hgm Hgtt Hwfc Hgc. 
  move: Hmk. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Bfalse) c) => [[csop lop] | ].
  - case=> _ <- _ <- <- <-.
    move: (newer_than_cache_find_hbt Hgc Hfhbt) => [Hgcsop Hglop].
    repeat (split; first done).
    by rewrite -newer_than_cache_add_cbt.
  - case=> _ <- _ <- <- <-.
    repeat (split; first done). 
    rewrite -newer_than_cache_add_cbt. by apply newer_than_cache_add_hbt.
Qed.

Lemma mk_env_bexp_ccache_newer_all_lits_nocbt_true :
  forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
         (g : generator) (m' : vm) (c' : compcache) (E' : env) 
         (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Btrue c = None ->
    mk_env_bexp_ccache m c s E g QFBV.Btrue = (m', c', E', g', cs, l) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    well_formed c ->
    newer_than_cache g c ->
    newer_than_lit g' l /\ newer_than_cnf g' cs /\ newer_than_cache g' c'.
Proof.
  move=> m c s E g m' c' E' g' cs l Hfcbt Hmk Hgm Hgtt Hwfc Hgc. 
  move: Hmk. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Btrue) c) => [[csop lop] | ].
  - case=> _ <- _ <- <- <-.
    move: (newer_than_cache_find_hbt Hgc Hfhbt) => [Hgcsop Hglop].
    repeat (split; first done).
    by rewrite -newer_than_cache_add_cbt.
  - case=> _ <- _ <- <- <-.
    repeat (split; first done). 
    rewrite -newer_than_cache_add_cbt. by apply newer_than_cache_add_hbt.
Qed.

Lemma mk_env_bexp_ccache_newer_all_lits_nocbt_binop :
  forall (op : QFBV.bbinop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c ->
        newer_than_lits g' ls /\ newer_than_cnf g' cs /\ newer_than_cache g' c') ->
    forall e2 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed c ->
          newer_than_cache g c ->
          newer_than_lits g' ls /\ newer_than_cnf g' cs /\ newer_than_cache g' c') ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bbinop op e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bbinop op e1 e2) = (m', c', E', g', cs, l) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c ->
        newer_than_lit g' l /\ newer_than_cnf g' cs /\ newer_than_cache g' c'.
Proof.
  move=> op e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt Hmk Hgm Hgtt Hwfc Hgc. 
  move: Hmk. rewrite /= Hfcbt.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm Hgtt Hwfc Hgc) => [Hg1ls1 [Hg1cs1 Hg1c1]].
  move: (mk_env_exp_ccache_newer_vm He1 Hgm) => Hg1m1.
  move: (mk_env_exp_ccache_newer_gen He1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => {Hgtt} Hg1tt.
  move: (mk_env_exp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) 
        => [Hg2ls2 [Hg2cs2 Hg2c2]].
  move: (mk_env_exp_ccache_newer_gen He2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1cs1 Hg1g2) => {Hg1cs1} Hg2cs1.
  case Hfhbt : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[csop lop] | ].
  - case=> _ <- _ <- <- <-.
    move: (newer_than_cache_find_hbt Hg2c2 Hfhbt) => [Hg2csop Hg2lop].
    split; first done. split.
    + rewrite !newer_than_cnf_catrev. by rewrite Hg2cs1 Hg2cs2 Hg2csop.
    + by rewrite -newer_than_cache_add_cbt.
  - case Hop : (mk_env_bbinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lop].
    case=> _ <- _ <- <- <-.
    move: (newer_than_lit_le_newer Hg1tt Hg1g2) => {Hg1tt} Hg2tt.
    move: (newer_than_lits_le_newer Hg1ls1 Hg1g2) => {Hg1ls1} Hg2ls1.
    move: (mk_env_bbinop_newer_res Hop Hg2tt Hg2ls1 Hg2ls2) => Hgoplop.
    move: (mk_env_bbinop_newer_cnf Hop Hg2tt Hg2ls1 Hg2ls2) => Hgopcsop.
    move: (mk_env_bbinop_newer_gen Hop) => Hg2gop.
    split; first done. split.
    + rewrite !newer_than_cnf_catrev. 
      move: (newer_than_cnf_le_newer Hg2cs1 Hg2gop) => {Hg2cs1} Hgopcs1.
      move: (newer_than_cnf_le_newer Hg2cs2 Hg2gop) => {Hg2cs2} Hgopcs2.
      by rewrite Hgopcs1 Hgopcs2 Hgopcsop.
    + move: (newer_than_cache_le_newer Hg2c2 Hg2gop) => {Hg2c2} Hgopc2.
      rewrite -newer_than_cache_add_cbt. by apply newer_than_cache_add_hbt.
Qed.

Lemma mk_env_bexp_ccache_newer_all_lits_nocbt_lneg :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c ->
        newer_than_lit g' l /\ newer_than_cnf g' cs /\ newer_than_cache g' c') ->
    forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
           (g : generator) (m' : vm) (c' : compcache) (E' : env) 
           (g' : generator) (cs : cnf) (l : literal),
      find_cbt (QFBV.Blneg e1) c = None ->
      mk_env_bexp_ccache m c s E g (QFBV.Blneg e1) = (m', c', E', g', cs, l) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      well_formed c ->
      newer_than_cache g c ->
      newer_than_lit g' l /\ newer_than_cnf g' cs /\ newer_than_cache g' c'.
Proof.
  move=> e1 IH1 m c s E g m' c' E' g' cs l Hfcbt Hmk Hgm Hgtt Hwfc Hgc. 
  move: Hmk. rewrite /mk_env_bexp_ccache -/mk_env_bexp_ccache Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm Hgtt Hwfc Hgc) => [Hg1l1 [Hg1cs1 Hg1c1]].
  case Hfhbt : (find_hbt (QFBV.Blneg e1) c1) => [[csop lop] | ].
  - case=> _ <- _ <- <- <-.
    move: (newer_than_cache_find_hbt Hg1c1 Hfhbt) => [Hg1csop Hg1lop].
    split; first done. split.
    + rewrite !newer_than_cnf_catrev. by rewrite Hg1cs1 Hg1csop.
    + by rewrite -newer_than_cache_add_cbt.
  - case Hop : (mk_env_lneg E1 g1 l1) => [[[Eop gop] csop] lop].
    case=> _ <- _ <- <- <-.
    move: (mk_env_lneg_newer_res Hop) => Hgoplop.
    move: (mk_env_lneg_newer_cnf Hop Hg1l1) => Hgopcsop.
    move: (mk_env_lneg_newer_gen Hop) => Hg1gop.
    split; first done. split.
    + rewrite !newer_than_cnf_catrev. 
      move: (newer_than_cnf_le_newer Hg1cs1 Hg1gop) => {Hg1cs1} Hgopcs1.
      by rewrite Hgopcs1 Hgopcsop.
    + move: (newer_than_cache_le_newer Hg1c1 Hg1gop) => {Hg1c1} Hgopc1.
      rewrite -newer_than_cache_add_cbt. by apply newer_than_cache_add_hbt.
Qed.
                                                                      
Lemma mk_env_bexp_ccache_newer_all_lits_nocbt_conj :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c ->
        newer_than_lit g' l /\ newer_than_cnf g' cs /\ newer_than_cache g' c') ->
    forall e2 : QFBV.bexp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (l : literal),
          mk_env_bexp_ccache m c s E g e2 = (m', c', E', g', cs, l) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed c ->
          newer_than_cache g c ->
          newer_than_lit g' l /\ newer_than_cnf g' cs /\ newer_than_cache g' c') ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bconj e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bconj e1 e2) = (m', c', E', g', cs, l) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c ->
        newer_than_lit g' l /\ newer_than_cnf g' cs /\ newer_than_cache g' c'.
Proof.
  move=> e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt Hmk Hgm Hgtt Hwfc Hgc. 
  move: Hmk. rewrite /mk_env_bexp_ccache -/mk_env_bexp_ccache Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  case He2 : (mk_env_bexp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm Hgtt Hwfc Hgc) => [Hg1l1 [Hg1cs1 Hg1c1]].
  move: (mk_env_bexp_ccache_newer_vm He1 Hgm) => Hg1m1.
  move: (mk_env_bexp_ccache_newer_gen He1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => {Hgtt} Hg1tt.
  move: (mk_env_bexp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) 
        => [Hg2l2 [Hg2cs2 Hg2c2]].
  move: (mk_env_bexp_ccache_newer_gen He2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1cs1 Hg1g2) => {Hg1cs1} Hg2cs1.
  case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csop lop] | ].
  - case=> _ <- _ <- <- <-.
    move: (newer_than_cache_find_hbt Hg2c2 Hfhbt) => [Hg2csop Hg2lop].
    split; first done. split.
    + rewrite !newer_than_cnf_catrev. by rewrite Hg2cs1 Hg2cs2 Hg2csop.
    + by rewrite -newer_than_cache_add_cbt.
  - case Hop : (mk_env_conj E2 g2 l1 l2) => [[[Eop gop] csop] lop].
    case=> _ <- _ <- <- <-.
    move: (newer_than_lit_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
    move: (mk_env_conj_newer_res Hop) => Hgoplop.
    move: (mk_env_conj_newer_cnf Hop Hg2l1 Hg2l2) => Hgopcsop.
    move: (mk_env_conj_newer_gen Hop) => Hg2gop.
    split; first done. split.
    + rewrite !newer_than_cnf_catrev. 
      move: (newer_than_cnf_le_newer Hg2cs1 Hg2gop) => {Hg2cs1} Hgopcs1.
      move: (newer_than_cnf_le_newer Hg2cs2 Hg2gop) => {Hg2cs2} Hgopcs2.
      by rewrite Hgopcs1 Hgopcs2 Hgopcsop.
    + move: (newer_than_cache_le_newer Hg2c2 Hg2gop) => {Hg2c2} Hgopc2.
      rewrite -newer_than_cache_add_cbt. by apply newer_than_cache_add_hbt.
Qed.

Lemma mk_env_bexp_ccache_newer_all_lits_nocbt_disj :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c ->
        newer_than_lit g' l /\ newer_than_cnf g' cs /\ newer_than_cache g' c') ->
    forall e2 : QFBV.bexp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (l : literal),
          mk_env_bexp_ccache m c s E g e2 = (m', c', E', g', cs, l) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          well_formed c ->
          newer_than_cache g c ->
          newer_than_lit g' l /\ newer_than_cnf g' cs /\ newer_than_cache g' c') ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bdisj e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bdisj e1 e2) = (m', c', E', g', cs, l) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        well_formed c ->
        newer_than_cache g c ->
        newer_than_lit g' l /\ newer_than_cnf g' cs /\ newer_than_cache g' c'.
Proof.
  move=> e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt Hmk Hgm Hgtt Hwfc Hgc. 
  move: Hmk. rewrite /mk_env_bexp_ccache -/mk_env_bexp_ccache Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  case He2 : (mk_env_bexp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hgm Hgtt Hwfc Hgc) => [Hg1l1 [Hg1cs1 Hg1c1]].
  move: (mk_env_bexp_ccache_newer_vm He1 Hgm) => Hg1m1.
  move: (mk_env_bexp_ccache_newer_gen He1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => {Hgtt} Hg1tt.
  move: (mk_env_bexp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hg1m1 Hg1tt Hwfc1 Hg1c1) 
        => [Hg2l2 [Hg2cs2 Hg2c2]].
  move: (mk_env_bexp_ccache_newer_gen He2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1cs1 Hg1g2) => {Hg1cs1} Hg2cs1.
  case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csop lop] | ].
  - case=> _ <- _ <- <- <-.
    move: (newer_than_cache_find_hbt Hg2c2 Hfhbt) => [Hg2csop Hg2lop].
    split; first done. split.
    + rewrite !newer_than_cnf_catrev. by rewrite Hg2cs1 Hg2cs2 Hg2csop.
    + by rewrite -newer_than_cache_add_cbt.
  - case Hop : (mk_env_disj E2 g2 l1 l2) => [[[Eop gop] csop] lop].
    case=> _ <- _ <- <- <-.
    move: (newer_than_lit_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
    move: (mk_env_disj_newer_res Hop) => Hgoplop.
    move: (mk_env_disj_newer_cnf Hop Hg2l1 Hg2l2) => Hgopcsop.
    move: (mk_env_disj_newer_gen Hop) => Hg2gop.
    split; first done. split.
    + rewrite !newer_than_cnf_catrev. 
      move: (newer_than_cnf_le_newer Hg2cs1 Hg2gop) => {Hg2cs1} Hgopcs1.
      move: (newer_than_cnf_le_newer Hg2cs2 Hg2gop) => {Hg2cs2} Hgopcs2.
      by rewrite Hgopcs1 Hgopcs2 Hgopcsop.
    + move: (newer_than_cache_le_newer Hg2c2 Hg2gop) => {Hg2c2} Hgopc2.
      rewrite -newer_than_cache_add_cbt. by apply newer_than_cache_add_hbt.
Qed.

Corollary mk_env_exp_ccache_newer_all_lits :
  forall (e : QFBV.exp) m c s E g m' c' E' g' cs ls,
    mk_env_exp_ccache m c s E g e = (m', c', E', g', cs, ls) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> 
    CompCache.well_formed c -> newer_than_cache g c ->
    newer_than_lits g' ls /\ newer_than_cnf g' cs /\ newer_than_cache g' c'
  with
    mk_env_bexp_ccache_newer_all_lits :
      forall e m c s E g m' c' E' g' cs l,
        mk_env_bexp_ccache m c s E g e = (m', c', E', g', cs, l) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        CompCache.well_formed c -> newer_than_cache g c ->
        newer_than_lit g' l /\ newer_than_cnf g' cs /\ newer_than_cache g' c'.
Proof.
  (* exp *)
  set IHe := mk_env_exp_ccache_newer_all_lits.
  set IHb := mk_env_bexp_ccache_newer_all_lits.
  move=> e m c s E g m' c' E' g' cs ls.
  case Hfcet: (find_cet e c) => [[cse lse] | ]. 
  - rewrite mk_env_exp_ccache_equation Hfcet /=.
    case=> _ <- _ <- <- <- Hgm Hgtt Hwfc Hgc. repeat (split; try done).
    move: (newer_than_cache_well_formed_newer_ct Hgc Hwfc) => Hctgc.
    move: (newer_than_ct_find_cet Hctgc Hfcet) => [_ Hglse].
    done.
  - move: e m c s E g m' c' E' g' cs ls Hfcet.
    case.
    + exact: mk_env_exp_ccache_newer_all_lits_nocet_var.
    + exact: mk_env_exp_ccache_newer_all_lits_nocet_const.
    + move=> op e1; move: op e1 (IHe e1).
      exact: mk_env_exp_ccache_newer_all_lits_nocet_unop.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_newer_all_lits_nocet_binop.
    + move=> b e1 e2; move: b (IHb b) e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_newer_all_lits_nocet_ite.
  (* bexp *)
  set IHe := mk_env_exp_ccache_newer_all_lits.
  set IHb := mk_env_bexp_ccache_newer_all_lits.
  move=> e m c s E g m' c' E' g' cs l.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite mk_env_bexp_ccache_equation Hfcbt /=.
    case=> _ <- _ <- <- <- Hgm Hgtt Hwfc Hgc. repeat (split; try done).
    move: (newer_than_cache_well_formed_newer_ct Hgc Hwfc) => Hctgc.
    move: (newer_than_ct_find_cbt Hctgc Hfcbt) => [_ Hgle].
    done.
  - move: e m c s E g m' c' E' g' cs l Hfcbt.
    case.
    + exact: mk_env_bexp_ccache_newer_all_lits_nocbt_false.
    + exact: mk_env_bexp_ccache_newer_all_lits_nocbt_true.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_bexp_ccache_newer_all_lits_nocbt_binop.
    + move=> e1; move: e1 (IHb e1).
      exact: mk_env_bexp_ccache_newer_all_lits_nocbt_lneg.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_newer_all_lits_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_newer_all_lits_nocbt_disj.
Qed.


(* = mk_env_exp_ccache_newer_res and mk_env_bexp_ccache_newer_res = *)

Corollary mk_env_exp_ccache_newer_res :
  forall (e : QFBV.exp) m c s E g m' c' E' g' cs ls,
    mk_env_exp_ccache m c s E g e = (m', c', E', g', cs, ls) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> 
    CompCache.well_formed c -> newer_than_cache g c ->
    newer_than_lits g' ls.
Proof.
  move=> e m c s E g m' c' E' g' cs ls Hmk Hgm Hgtt Hwfc Hgc.
  move: (mk_env_exp_ccache_newer_all_lits Hmk Hgm Hgtt Hwfc Hgc) => [H _].
  done.
Qed.

Corollary mk_env_bexp_ccache_newer_res :
  forall e m c s E g m' c' E' g' cs l,
    mk_env_bexp_ccache m c s E g e = (m', c', E', g', cs, l) ->
    newer_than_vm g m -> newer_than_lit g lit_tt ->
    CompCache.well_formed c -> newer_than_cache g c ->
    newer_than_lit g' l.
Proof.
  move=> e m c s E g m' c' E' g' cs l Hmk Hgm Hgtt Hwfc Hgc.
  move: (mk_env_bexp_ccache_newer_all_lits Hmk Hgm Hgtt Hwfc Hgc) => [H _].
  done.
Qed.

(* = mk_env_exp_ccache_newer_cnf and mk_env_bexp_ccache_newer_cnf = *)

Corollary mk_env_exp_ccache_newer_cnf :
  forall (e : QFBV.exp) m c s E g m' c' E' g' cs ls,
    mk_env_exp_ccache m c s E g e = (m', c', E', g', cs, ls) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    (* QFBV.well_formed_exp e te -> *)
    CompCache.well_formed c -> newer_than_cache g c ->
    newer_than_cnf g' cs.
Proof.
  move=> e m c s E g m' c' E' g' cs ls Hmk Hgm Hgtt Hwfc Hgc.
  move: (mk_env_exp_ccache_newer_all_lits Hmk Hgm Hgtt Hwfc Hgc) => [_ [H _]].
  done.
Qed.

Corollary mk_env_bexp_ccache_newer_cnf :
  forall e m c s E g m' c' E' g' cs l,
    mk_env_bexp_ccache m c s E g e = (m', c', E', g', cs, l) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    (* QFBV.well_formed_bexp e te -> *)
    CompCache.well_formed c -> newer_than_cache g c ->
    newer_than_cnf g' cs.
Proof.
  move=> e m c s E g m' c' E' g' cs l Hmk Hgm Hgtt Hwfc Hgc.
  move: (mk_env_bexp_ccache_newer_all_lits Hmk Hgm Hgtt Hwfc Hgc) => [_ [H _]].
  done.
Qed.

(* = mk_env_exp_ccache_newer_cache and mk_env_bexp_ccache_newer_cache = *)

Corollary mk_env_exp_ccache_newer_cache :
  forall (e : QFBV.exp) m c s E g m' c' E' g' cs ls,
    mk_env_exp_ccache m c s E g e = (m', c', E', g', cs, ls) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    (* QFBV.well_formed_exp e te -> *)
    CompCache.well_formed c -> newer_than_cache g c ->
    newer_than_cache g' c'.
Proof.
  move=> e m c s E g m' c' E' g' cs ls Hmk Hgm Hgtt Hwfc Hgc.
  move: (mk_env_exp_ccache_newer_all_lits Hmk Hgm Hgtt Hwfc Hgc) => [_ [_ H]].
  done.
Qed.

Corollary mk_env_bexp_ccache_newer_cache :
  forall e m c s E g m' c' E' g' cs l,
    mk_env_bexp_ccache m c s E g e = (m', c', E', g', cs, l) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    (* QFBV.well_formed_bexp e te -> *)
    CompCache.well_formed c -> newer_than_cache g c ->
    newer_than_cache g' c'.
Proof.
  move=> e m c s E g m' c' E' g' cs l Hmk Hgm Hgtt Hwfc Hgc.
  move: (mk_env_bexp_ccache_newer_all_lits Hmk Hgm Hgtt Hwfc Hgc) => [_ [_ H]].
  done.
Qed.
