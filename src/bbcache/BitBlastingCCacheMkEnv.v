From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport 
     AdhereConform.
From BBCache Require Import CompCache BitBlastingCCacheDef.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* = mk_env_exp_ccache_is_bit_blast_exp_ccache and mk_env_bexp_ccache_is_bit_blast_bexp_ccache = *)

Lemma mk_env_eunop_is_bit_blast_eunop :
  forall op E g ls E' g' cs lrs,
    mk_env_eunop op E g ls = (E', g', cs, lrs) -> 
    bit_blast_eunop op g ls = (g', cs, lrs).
Proof.
  move=> op E g ls E' g' cs lrs.
  case op => [ | | i j | n | n | n | n | n | n | n ]; 
    rewrite /mk_env_eunop /bit_blast_eunop => Hmk;
    [ rewrite (mk_env_not_is_bit_blast_not Hmk) |
      rewrite (mk_env_neg_is_bit_blast_neg Hmk) |
      rewrite (mk_env_extract_is_bit_blast_extract Hmk) |
      rewrite (mk_env_high_is_bit_blast_high Hmk) |
      rewrite (mk_env_low_is_bit_blast_low Hmk) |
      rewrite (mk_env_zeroextend_is_bit_blast_zeroextend Hmk) |
      rewrite (mk_env_signextend_is_bit_blast_signextend Hmk) |
      rewrite (mk_env_repeat_is_bit_blast_repeat Hmk) |
      rewrite (mk_env_rotateleft_is_bit_blast_rotateleft Hmk) |
      rewrite (mk_env_rotateright_is_bit_blast_rotateright Hmk) ];
    done.
Qed.

Lemma mk_env_ebinop_is_bit_blast_ebinop :
  forall op E g ls1 ls2 E' g' cs ls,
    mk_env_ebinop op E g ls1 ls2 = (E', g', cs, ls) -> 
    bit_blast_ebinop op g ls1 ls2 = (g', cs, ls).
Proof.
  move=> op E g ls1 ls2 E' g' cs ls.
  case op; rewrite /mk_env_ebinop /bit_blast_ebinop => Hmk;
    [ rewrite (mk_env_and_is_bit_blast_and Hmk) |
      rewrite (mk_env_or_is_bit_blast_or Hmk) |
      rewrite (mk_env_xor_is_bit_blast_xor Hmk) |
      rewrite (mk_env_add_is_bit_blast_add Hmk) |
      rewrite (mk_env_sub_is_bit_blast_sub Hmk) |
      rewrite (mk_env_mul_is_bit_blast_mul Hmk) |
      rewrite (mk_env_umod_is_bit_blast_umod Hmk) |
      rewrite (mk_env_srem_is_bit_blast_srem Hmk) |
      rewrite (mk_env_smod_is_bit_blast_smod Hmk) |
      rewrite (mk_env_shl_is_bit_blast_shl Hmk) |
      rewrite (mk_env_lshr_is_bit_blast_lshr Hmk) |
      rewrite (mk_env_ashr_is_bit_blast_ashr Hmk) |
      rewrite (mk_env_concat_is_bit_blast_concat Hmk) ];
    done.
Qed.

Lemma mk_env_bbinop_is_bit_blast_bbinop :
  forall op E g ls1 ls2 E' g' cs l,
    mk_env_bbinop op E g ls1 ls2 = (E', g', cs, l) -> 
    bit_blast_bbinop op g ls1 ls2 = (g', cs, l).
Proof.
  move=> op E g ls1 ls2 E' g' cs l.
  case op; rewrite /mk_env_bbinop /bit_blast_bbinop => Hmk;
    [ rewrite (mk_env_eq_is_bit_blast_eq Hmk) |
      rewrite (mk_env_ult_is_bit_blast_ult Hmk) |
      rewrite (mk_env_ule_is_bit_blast_ule Hmk) |
      rewrite (mk_env_ugt_is_bit_blast_ugt Hmk) |
      rewrite (mk_env_uge_is_bit_blast_uge Hmk) |
      rewrite (mk_env_slt_is_bit_blast_slt Hmk) |
      rewrite (mk_env_sle_is_bit_blast_sle Hmk) |
      rewrite (mk_env_sgt_is_bit_blast_sgt Hmk) |
      rewrite (mk_env_sge_is_bit_blast_sge Hmk) |
      rewrite (mk_env_uaddo_is_bit_blast_uaddo Hmk) |
      rewrite (mk_env_usubo_is_bit_blast_usubo Hmk) |
      rewrite (mk_env_umulo_is_bit_blast_umulo Hmk) |
      rewrite (mk_env_saddo_is_bit_blast_saddo Hmk) |
      rewrite (mk_env_ssubo_is_bit_blast_ssubo Hmk) |
      rewrite (mk_env_smulo_is_bit_blast_smulo Hmk) ];
    done.
Qed.
  

Lemma mk_env_exp_ccache_is_bit_blast_exp_ccache_nocet_var :
  forall (t : SSAVarOrder.t) (te : SSATE.env) (m : vm) (c : compcache)
         (s : SSAStore.t) (E : env) (g : generator) (m' : vm) 
         (c' : compcache) (E' : env) (g' : generator) (cs : cnf) (ls : word),
    conform_exp (QFBV.Evar t) s te ->
    QFBV.well_formed_exp (QFBV.Evar t) te ->
    find_cet (QFBV.Evar t) c = None ->
    mk_env_exp_ccache m c s E g (QFBV.Evar t) = (m', c', E', g', cs, ls) ->
    bit_blast_exp_ccache te m c g (QFBV.Evar t) = (m', c', g', cs, ls).
Proof.
  move=> v te m c s E g m' c' E' g' cs ls /= Hsize _ Hfcet. rewrite Hfcet /=.
  case Hfhet : (find_het (QFBV.Evar v) c) => [[cse lse] | ].
  - by case=> <- <- _ <- <- <-.
  - case : (SSAVM.find v m) => [rs | ].
    + by case => <- <- _ <- <- <-.
    + dcase (mk_env_var E g (SSAStore.acc v s) v) => [[[[Ev gv] csv] lsv] Hmkv] .
      move: (mk_env_var_is_bit_blast_var (Logic.eq_sym (eqP Hsize)) Hmkv) => Hbbv.
      rewrite Hbbv.
      by case => <- <- _ <- <- <- .
Qed.

Lemma mk_env_exp_ccache_is_bit_blast_exp_ccache_nocet_const :
  forall (b : bits) (te : SSATE.env) (m : vm) (c : compcache) 
         (s : SSAStore.t) (E : env) (g : generator) (m' : vm) 
         (c' : compcache) (E' : env) (g' : generator) (cs : cnf) (ls : word),
    conform_exp (QFBV.Econst b) s te ->
    QFBV.well_formed_exp (QFBV.Econst b) te ->
    find_cet (QFBV.Econst b) c = None ->
    mk_env_exp_ccache m c s E g (QFBV.Econst b) = (m', c', E', g', cs, ls) ->
    bit_blast_exp_ccache te m c g (QFBV.Econst b) = (m', c', g', cs, ls).
Proof.
  move=> bs te m c s E g m' c' E' g' cs ls /= _ _ Hfcet. rewrite Hfcet /=.
  case Hfhet : (find_het (QFBV.Econst bs) c) => [[cse lse] | ];
    by case=> <- <- _ <- <- <-.
Qed.

Lemma mk_env_exp_ccache_is_bit_blast_exp_ccache_nocet_unop :
  forall (op : QFBV.eunop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (c' : compcache) 
            (E' : env) (g' : generator) (cs : cnf) (ls : word),
        conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls)) ->
    forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
           (E : env) (g : generator) (m' : vm) (c' : compcache) 
           (E' : env) (g' : generator) (cs : cnf) (ls : word),
      conform_exp (QFBV.Eunop op e1) s te ->
      QFBV.well_formed_exp (QFBV.Eunop op e1) te ->
      find_cet (QFBV.Eunop op e1) c = None ->
      mk_env_exp_ccache m c s E g (QFBV.Eunop op e1) = (m', c', E', g', cs, ls) ->
      bit_blast_exp_ccache te m c g (QFBV.Eunop op e1) = (m', c', g', cs, ls).
Proof.
  move=> op e1 IH1 te m c s E g m' c' E' g' cs ls /= Hcf1 Hwf1 Hfcet. 
  rewrite Hfcet /=.  
  case Hmke1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1) => Hbbe1.
  rewrite Hbbe1.
  case Hmkop : (mk_env_eunop op E1 g1 ls1) => [[[Eop gop] csop] lsop].
  case Hfhet : (find_het (QFBV.Eunop op e1) c1) => [[cse lse] | ].
  - by case=> <- <- _ <- <- <-.
  - case=> <- <- _ <- <- <-.
    rewrite (mk_env_eunop_is_bit_blast_eunop Hmkop).
    done.
Qed.

Lemma mk_env_exp_ccache_is_bit_blast_exp_ccache_nocet_binop :
  forall (op : QFBV.ebinop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (c' : compcache) 
            (E' : env) (g' : generator) (cs : cnf) (ls : word),
        conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls)) ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (c' : compcache) 
              (E' : env) (g' : generator) (cs : cnf) (ls : word),
          conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
          bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls)) ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (c' : compcache) 
             (E' : env) (g' : generator) (cs : cnf) (ls : word),
        conform_exp (QFBV.Ebinop op e1 e2) s te ->
        QFBV.well_formed_exp (QFBV.Ebinop op e1 e2) te ->
        find_cet (QFBV.Ebinop op e1 e2) c = None ->
        mk_env_exp_ccache m c s E g (QFBV.Ebinop op e1 e2) = (m', c', E', g', cs, ls) ->
        bit_blast_exp_ccache te m c g (QFBV.Ebinop op e1 e2) = (m', c', g', cs, ls).
Proof.
  move=> op e1 IH1 e2 IH2 te m c s E g m' c' E' g' cs ls /= /andP [Hcf1 Hcf2]
           /andP [/andP [/andP [Hwf1 Hwf2] Hszgt0] Hsize] Hfcet. 
  rewrite Hfcet /=.  
  case Hmke1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1) => Hbbe1.
  case Hmke2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ _ Hcf2 Hwf2 Hmke2) => Hbbe2.
  rewrite Hbbe1 Hbbe2.
  case Hmkop : (mk_env_ebinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lsop].
  case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[cse lse] | ].
  - by case=> <- <- _ <- <- <-.
  - case=> <- <- _ <- <- <-.
    rewrite (mk_env_ebinop_is_bit_blast_ebinop Hmkop).
    done.
Qed.

Lemma mk_env_exp_ccache_is_bit_blast_exp_ccache_nocet_ite :
  forall b : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (c' : compcache) 
            (E' : env) (g' : generator) (cs : cnf) (l : literal),
        conform_bexp b s te ->
        QFBV.well_formed_bexp b te ->
        mk_env_bexp_ccache m c s E g b = (m', c', E', g', cs, l) ->
        bit_blast_bexp_ccache te m c g b = (m', c', g', cs, l)) ->
    forall e1 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (c' : compcache) 
              (E' : env) (g' : generator) (cs : cnf) (ls : word),
          conform_exp e1 s te ->
          QFBV.well_formed_exp e1 te ->
          mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
          bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls)) ->
      forall e2 : QFBV.exp,
        (forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
                (E : env) (g : generator) (m' : vm) (c' : compcache) 
                (E' : env) (g' : generator) (cs : cnf) (ls : word),
            conform_exp e2 s te ->
            QFBV.well_formed_exp e2 te ->
            mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
            bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls)) ->
        forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
               (E : env) (g : generator) (m' : vm) (c' : compcache) 
               (E' : env) (g' : generator) (cs : cnf) (ls : word),
          conform_exp (QFBV.Eite b e1 e2) s te ->
          QFBV.well_formed_exp (QFBV.Eite b e1 e2) te ->
          find_cet (QFBV.Eite b e1 e2) c = None ->
          mk_env_exp_ccache m c s E g (QFBV.Eite b e1 e2) = (m', c', E', g', cs, ls) ->
          bit_blast_exp_ccache te m c g (QFBV.Eite b e1 e2) = (m', c', g', cs, ls).
Proof.
  move=> b IHb e1 IH1 e2 IH2 te m c s E g m' c' E' g' cs ls /= 
           /andP [/andP [Hcfb Hcf1] Hcf2] 
           /andP [/andP [/andP [Hwfb Hwf1] Hwf2] Hsize] Hfcet. 
  rewrite Hfcet /=.  
  case Hmkb : (mk_env_bexp_ccache m c s E g b) => [[[[[mb cb] Eb] gb] csb] lb].
  move: (IHb _ _ _ _ _ _ _ _ _ _ _ _ Hcfb Hwfb Hmkb) => Hbbb.
  case Hmke1 : (mk_env_exp_ccache mb cb s Eb gb e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1) => Hbbe1.
  case Hmke2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ _ Hcf2 Hwf2 Hmke2) => Hbbe2.
  rewrite Hbbb Hbbe1 Hbbe2.
  case Hmkop : (mk_env_ite E2 g2 lb ls1 ls2) => [[[Eop gop] csop] lsop].
  case Hfhet : (find_het (QFBV.Eite b e1 e2) c2) => [[cse lse] | ].
  - by case=> <- <- _ <- <- <-.
  - case=> <- <- _ <- <- <-.
    rewrite (mk_env_ite_is_bit_blast_ite Hmkop). 
    done.
Qed.

Lemma mk_env_bexp_ccache_is_bit_blast_bexp_ccache_nocbt_false :
  forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (c' : compcache) 
         (E' : env) (g' : generator) (cs : cnf) (l : literal),
    conform_bexp QFBV.Bfalse s te ->
    QFBV.well_formed_bexp QFBV.Bfalse te ->
    find_cbt QFBV.Bfalse c = None ->
    mk_env_bexp_ccache m c s E g QFBV.Bfalse = (m', c', E', g', cs, l) ->
    bit_blast_bexp_ccache te m c g QFBV.Bfalse = (m', c', g', cs, l).
Proof.
  move=> te m c s E g m' c' E' g' cs l /= _ _ Hfcbt. rewrite Hfcbt /=.
  case Hfhbt : (find_hbt (QFBV.Bfalse) c) => [[cse le] | ];
    by case=> <- <- _ <- <- <-.
Qed.

Lemma mk_env_bexp_ccache_is_bit_blast_bexp_ccache_nocbt_true :
  forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (c' : compcache) 
         (E' : env) (g' : generator) (cs : cnf) (l : literal),
    conform_bexp QFBV.Btrue s te ->
    QFBV.well_formed_bexp QFBV.Btrue te ->
    find_cbt QFBV.Btrue c = None ->
    mk_env_bexp_ccache m c s E g QFBV.Btrue = (m', c', E', g', cs, l) ->
    bit_blast_bexp_ccache te m c g QFBV.Btrue = (m', c', g', cs, l).
Proof.
  move=> te m c s E g m' c' E' g' cs l /= _ _ Hfcbt. rewrite Hfcbt /=.
  case Hfhbt : (find_hbt (QFBV.Btrue) c) => [[cse le] | ];
    by case=> <- <- _ <- <- <-.
Qed.

Lemma mk_env_bexp_ccache_is_bit_blast_bexp_ccache_nocbt_binop :
  forall (op : QFBV.bbinop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (c' : compcache) 
            (E' : env) (g' : generator) (cs : cnf) (ls : word),
        conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls)) ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (c' : compcache) 
              (E' : env) (g' : generator) (cs : cnf) (ls : word),
          conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
          bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls)) ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (c' : compcache) 
             (E' : env) (g' : generator) (cs : cnf) (l : literal),
        conform_bexp (QFBV.Bbinop op e1 e2) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop op e1 e2) te ->
        find_cbt (QFBV.Bbinop op e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bbinop op e1 e2) = (m', c', E', g', cs, l) ->
        bit_blast_bexp_ccache te m c g (QFBV.Bbinop op e1 e2) = (m', c', g', cs, l).
Proof.
  move=> op e1 IH1 e2 IH2 te m c s E g m' c' E' g' cs l /= /andP [Hcf1 Hcf2]
           /andP [/andP [Hwf1 Hwf2] Hsize] Hfcbt. 
  rewrite Hfcbt /=.  
  case Hmke1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1) => Hbbe1.
  case Hmke2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ _ Hcf2 Hwf2 Hmke2) => Hbbe2.
  rewrite Hbbe1 Hbbe2.
  case Hmkop : (mk_env_bbinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lop].
  case Hfhbt : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[cse le] | ].
  - by case=> <- <- _ <- <- <-.
  - case=> <- <- _ <- <- <-.
    rewrite (mk_env_bbinop_is_bit_blast_bbinop Hmkop).
    done.
Qed.

Lemma mk_env_bexp_ccache_is_bit_blast_bexp_ccache_nocbt_lneg :  
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (c' : compcache) 
            (E' : env) (g' : generator) (cs : cnf) (l : literal),
        conform_bexp e1 s te ->
        QFBV.well_formed_bexp e1 te ->
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l)) ->
    forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
           (E : env) (g : generator) (m' : vm) (c' : compcache) 
           (E' : env) (g' : generator) (cs : cnf) (l : literal),
      conform_bexp (QFBV.Blneg e1) s te ->
      QFBV.well_formed_bexp (QFBV.Blneg e1) te ->
      find_cbt (QFBV.Blneg e1) c = None ->
      mk_env_bexp_ccache m c s E g (QFBV.Blneg e1) = (m', c', E', g', cs, l) ->
      bit_blast_bexp_ccache te m c g (QFBV.Blneg e1) = (m', c', g', cs, l).
Proof.
  move=> e1 IH1 te m c s E g m' c' E' g' cs l /= Hcf1 Hwf1 Hfcbt. 
  rewrite Hfcbt /=.  
  case Hmke1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1) => Hbbe1.
  rewrite Hbbe1.
  (* case Hmkop : (mk_env_lneg op E1 g1 ls1) => [[[Eop gop] csop] lop]. *)
  case Hfhet : (find_hbt (QFBV.Blneg e1) c1) => [[cse le] | ];
    by case=> <- <- _ <- <- <-.
Qed.

Lemma mk_env_bexp_ccache_is_bit_blast_bexp_ccache_nocbt_conj :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (c' : compcache) 
            (E' : env) (g' : generator) (cs : cnf) (l : literal),
        conform_bexp e1 s te ->
        QFBV.well_formed_bexp e1 te ->
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l)) ->
    forall e2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (c' : compcache) 
              (E' : env) (g' : generator) (cs : cnf) (l : literal),
          conform_bexp e2 s te ->
          QFBV.well_formed_bexp e2 te ->
          mk_env_bexp_ccache m c s E g e2 = (m', c', E', g', cs, l) ->
          bit_blast_bexp_ccache te m c g e2 = (m', c', g', cs, l)) ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (c' : compcache) 
             (E' : env) (g' : generator) (cs : cnf) (l : literal),
        conform_bexp (QFBV.Bconj e1 e2) s te ->
        QFBV.well_formed_bexp (QFBV.Bconj e1 e2) te ->
        find_cbt (QFBV.Bconj e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bconj e1 e2) = (m', c', E', g', cs, l) ->
        bit_blast_bexp_ccache te m c g (QFBV.Bconj e1 e2) = (m', c', g', cs, l).
Proof.
  move=> e1 IH1 e2 IH2 te m c s E g m' c' E' g' cs l /= /andP [Hcf1 Hcf2]
            /andP [Hwf1 Hwf2] Hfcbt. 
  rewrite Hfcbt /=.  
  case Hmke1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1) => Hbbe1.
  case Hmke2 : (mk_env_bexp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] l2].
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ _ Hcf2 Hwf2 Hmke2) => Hbbe2.
  rewrite Hbbe1 Hbbe2.
  (* case Hmkop : (mk_env_bbinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lop]. *)
  case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[cse le] | ];
    by case=> <- <- _ <- <- <-.
Qed.

Lemma mk_env_bexp_ccache_is_bit_blast_bexp_ccache_nocbt_disj :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
            (E : env) (g : generator) (m' : vm) (c' : compcache) 
            (E' : env) (g' : generator) (cs : cnf) (l : literal),
        conform_bexp e1 s te ->
        QFBV.well_formed_bexp e1 te ->
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l)) ->
    forall e2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
              (E : env) (g : generator) (m' : vm) (c' : compcache) 
              (E' : env) (g' : generator) (cs : cnf) (l : literal),
          conform_bexp e2 s te ->
          QFBV.well_formed_bexp e2 te ->
          mk_env_bexp_ccache m c s E g e2 = (m', c', E', g', cs, l) ->
          bit_blast_bexp_ccache te m c g e2 = (m', c', g', cs, l)) ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (s : SSAStore.t) 
             (E : env) (g : generator) (m' : vm) (c' : compcache) 
             (E' : env) (g' : generator) (cs : cnf) (l : literal),
        conform_bexp (QFBV.Bdisj e1 e2) s te ->
        QFBV.well_formed_bexp (QFBV.Bdisj e1 e2) te ->
        find_cbt (QFBV.Bdisj e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bdisj e1 e2) = (m', c', E', g', cs, l) ->
        bit_blast_bexp_ccache te m c g (QFBV.Bdisj e1 e2) = (m', c', g', cs, l).
Proof.
  move=> e1 IH1 e2 IH2 te m c s E g m' c' E' g' cs l /= /andP [Hcf1 Hcf2]
            /andP [Hwf1 Hwf2] Hfcbt. 
  rewrite Hfcbt /=.  
  case Hmke1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1) => Hbbe1.
  case Hmke2 : (mk_env_bexp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] l2].
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ _ Hcf2 Hwf2 Hmke2) => Hbbe2.
  rewrite Hbbe1 Hbbe2.
  (* case Hmkop : (mk_env_bbinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lop]. *)
  case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[cse le] | ];
    by case=> <- <- _ <- <- <-.
Qed.


Corollary mk_env_exp_ccache_is_bit_blast_exp_ccache :
  forall (e : QFBV.exp) te m c s E g m' c' E' g' cs ls,
    AdhereConform.conform_exp e s te ->
    QFBV.well_formed_exp e te ->
    mk_env_exp_ccache m c s E g e = (m', c', E', g', cs, ls) ->
    bit_blast_exp_ccache te m c g e = (m', c', g', cs, ls)
  with
    mk_env_bexp_ccache_is_bit_blast_bexp_ccache :
      forall e te m c s E g m' c' E' g' cs l,
        AdhereConform.conform_bexp e s te ->
        QFBV.well_formed_bexp e te ->
        mk_env_bexp_ccache m c s E g e = (m', c', E', g', cs, l) ->
        bit_blast_bexp_ccache te m c g e = (m', c', g', cs, l).
Proof.
  (* mk_env_exp_ccache_is_bit_blast_exp_ccache *)
  set IHe := mk_env_exp_ccache_is_bit_blast_exp_ccache.
  set IHb := mk_env_bexp_ccache_is_bit_blast_bexp_ccache.
  move=> e te m c s E g m' c' E' g' cs ls Hcf Hwf.
  case Hfcet: (find_cet e c) => [[cse lse ] | ]. 
  - rewrite mk_env_exp_ccache_equation bit_blast_exp_ccache_equation Hfcet /=.
    case=> <- <- _ <- <- <-. done. 
  - move: e te m c s E g m' c' E' g' cs ls Hcf Hwf Hfcet.
    case.
    + exact: mk_env_exp_ccache_is_bit_blast_exp_ccache_nocet_var.
    + exact: mk_env_exp_ccache_is_bit_blast_exp_ccache_nocet_const.
    + move=> op e1; move: op e1 (IHe e1).
      exact: mk_env_exp_ccache_is_bit_blast_exp_ccache_nocet_unop.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_is_bit_blast_exp_ccache_nocet_binop.
    + move=> b e1 e2; move: b (IHb b) e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_is_bit_blast_exp_ccache_nocet_ite.
  (* mk_env_bexp_ccache_is_bit_blast_bexp_ccache *)
  set IHe := mk_env_exp_ccache_is_bit_blast_exp_ccache.
  set IHb := mk_env_bexp_ccache_is_bit_blast_bexp_ccache.
  move=> e te m c s E g m' c' E' g' cs l Hcf Hwf.
  case Hfcbt: (find_cbt e c) => [[cse le ] | ]. 
  - rewrite mk_env_bexp_ccache_equation bit_blast_bexp_ccache_equation Hfcbt /=.
    case=> <- <- _ <- <- <-. done. 
  - move: e te m c s E g m' c' E' g' cs l Hcf Hwf Hfcbt.
    case.
    + exact: mk_env_bexp_ccache_is_bit_blast_bexp_ccache_nocbt_false.
    + exact: mk_env_bexp_ccache_is_bit_blast_bexp_ccache_nocbt_true.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_bexp_ccache_is_bit_blast_bexp_ccache_nocbt_binop.
    + move=> e1; move: e1 (IHb e1).
      exact: mk_env_bexp_ccache_is_bit_blast_bexp_ccache_nocbt_lneg.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_is_bit_blast_bexp_ccache_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_is_bit_blast_bexp_ccache_nocbt_disj.
Qed.
