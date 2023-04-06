From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types EqOrder EqVar Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
From BBCache Require Import CompCache BitBlastingCCacheDef BitBlastingCCacheFind
     BitBlastingCCacheNewer.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* = bit_blast_exp_ccache_preserve and bit_blast_bexp_ccache_preserve = *)

Lemma bit_blast_exp_ccache_preserve_nocet_var :
  forall (t : SSAVarOrder.t) (te : SSATE.env) (m : vm) (c : compcache)
         (g : generator) (m' : vm) (c' : compcache) (g' : generator) 
         (cs : cnf) (ls : word),
    find_cet (QFBV.Evar t) c = None ->
    bit_blast_exp_ccache te m c g (QFBV.Evar t) = (m', c', g', cs, ls) ->
    vm_preserve m m'.
Proof.
  move=> v te m c g m' c' g' cs ls Hfcet. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Evar v) c) => [[cse lse] | ];
    last case Hfv : (SSAVM.find v m);                                          
    last case Hv : (bit_blast_var te g v) => [[gv csv] lsv];
    case=> <- _ _ _ _;
    (exact: vm_preserve_refl || exact: vm_preserve_add_diag).
Qed.

Lemma bit_blast_exp_ccache_preserve_nocet_const :
  forall (b : bits) (te : SSATE.env) (m : vm) (c : compcache) 
         (g : generator) (m' : vm) (c' : compcache) (g' : generator) 
         (cs : cnf) (ls : word),
    find_cet (QFBV.Econst b) c = None ->
    bit_blast_exp_ccache te m c g (QFBV.Econst b) = (m', c', g', cs, ls) ->
    vm_preserve m m'.
Proof.
  move=> bs te m c g m' c' g' cs ls Hfcet. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Econst bs) c) => [[csop lsop] | ];
    by case=> <- _ _ _ _.
Qed.

Lemma bit_blast_exp_ccache_preserve_nocet_unop :
  forall (op : QFBV.eunop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) -> 
        vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
           (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
      find_cet (QFBV.Eunop op e1) c = None ->
      bit_blast_exp_ccache te m c g (QFBV.Eunop op e1) = (m', c', g', cs, ls) ->
      vm_preserve m m'.
Proof.
  move=> op e1 IH1 te m c g m' c' g' cs ls Hfcet. rewrite /= Hfcet.
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1) => Hpmm1.
  case Hfhet : (find_het (QFBV.Eunop op e1) c1) => [[csop lsop] | ];
    last case Hop : (bit_blast_eunop op g1 ls1) => [[gop csop] lsop];
    by case=> <- _ _ _ _.
Qed.

Lemma bit_blast_exp_ccache_preserve_nocet_binop :
  forall (op : QFBV.ebinop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) -> 
        vm_preserve m m') ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
          bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls) -> 
          vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        find_cet (QFBV.Ebinop op e1 e2) c = None ->
        bit_blast_exp_ccache te m c g (QFBV.Ebinop op e1 e2) = (m', c', g', cs, ls) ->
        vm_preserve m m'.
Proof.
  move=> op e1 IH1 e2 IH2 te m c g m' c' g' cs ls Hfcet. rewrite /= Hfcet.
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1) => Hpmm1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2) => Hpm1m2.
  move: (vm_preserve_trans Hpmm1 Hpm1m2) => Hpmm2.
  case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csop lsop] | ];
    last case Hop : (bit_blast_ebinop op g2 ls1 ls2) => [[gop csop] lsop];
    by case=> <- _ _ _ _.
Qed.

Lemma bit_blast_exp_ccache_preserve_nocet_ite :
  forall b : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        bit_blast_bexp_ccache te m c g b = (m', c', g', cs, l) -> 
        vm_preserve m m') ->
    forall e1 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
          bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) ->
          vm_preserve m m') ->
      forall e2 : QFBV.exp,
        (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
                (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
            bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls) -> 
            vm_preserve m m') ->
        forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
               (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
          find_cet (QFBV.Eite b e1 e2) c = None ->
          bit_blast_exp_ccache te m c g (QFBV.Eite b e1 e2) = (m', c', g', cs, ls) ->
          vm_preserve m m'.
Proof.
  move=> b IHb e1 IH1 e2 IH2 te m c g m' c' g' cs ls Hfcet. rewrite /= Hfcet.
  case Hb : (bit_blast_bexp_ccache te m c g b) => [[[[mb cb] gb] csb] lb].
  case He1 : (bit_blast_exp_ccache te mb cb gb e1) => [[[[m1 c1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
  move: (IHb _ _ _ _ _ _ _ _ _ Hb) => Hpmmb.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1) => Hpmbm1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2) => Hpm1m2.
  move: (vm_preserve_trans Hpmmb (vm_preserve_trans Hpmbm1 Hpm1m2)) => Hpmm2.
  case Hfhet : (find_het (QFBV.Eite b e1 e2) c2) => [[csop lsop] | ];
    last case Hop : (bit_blast_ite g2 lb ls1 ls2) => [[gop csop] lsop];
    by case=> <- _ _ _ _.
Qed.

Lemma bit_blast_bexp_ccache_preserve_nocbt_false :
  forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
         (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Bfalse c = None ->
    bit_blast_bexp_ccache te m c g QFBV.Bfalse = (m', c', g', cs, l) ->
    vm_preserve m m'.
Proof.
  move=> te m c g m' c' g' cs l Hfcbt. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Bfalse) c) => [[csop lop] | ];
    by case=> <- _ _ _ _.
Qed.

Lemma bit_blast_bexp_ccache_preserve_nocbt_true :
  forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
         (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Btrue c = None ->
    bit_blast_bexp_ccache te m c g QFBV.Btrue = (m', c', g', cs, l) ->
    vm_preserve m m'.
Proof.
  move=> te m c g m' c' g' cs l Hfcbt. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Btrue) c) => [[csop lop] | ];
    by case=> <- _ _ _ _.
Qed.

Lemma bit_blast_bexp_ccache_preserve_nocbt_binop :
  forall (op : QFBV.bbinop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) -> 
        vm_preserve m m') ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
          bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls) -> 
          vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bbinop op e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bbinop op e1 e2) = (m', c', g', cs, l) ->
        vm_preserve m m'.
Proof.
  move=> op e1 IH1 e2 IH2 te m c g m' c' g' cs l Hfcbt. rewrite /= Hfcbt.
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1) => Hpmm1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2) => Hpm1m2.
  move: (vm_preserve_trans Hpmm1 Hpm1m2) => Hpmm2.
  case Hfhbt : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[csop lop] | ];
    last case Hop : (bit_blast_bbinop op g2 ls1 ls2) => [[gop csop] lop];
    by case=> <- _ _ _ _.
Qed.

Lemma bit_blast_bexp_ccache_preserve_nocbt_lneg :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l) -> 
        vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
           (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
      find_cbt (QFBV.Blneg e1) c = None ->
      bit_blast_bexp_ccache te m c g (QFBV.Blneg e1) = (m', c', g', cs, l) ->
      vm_preserve m m'.
Proof.
  move=> e1 IH1 te m c g m' c' g' cs l Hfcbt. rewrite /= Hfcbt.
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1) => Hpmm1.
  case Hfhbt : (find_hbt (QFBV.Blneg e1) c1) => [[csop lop] | ];
    by case=> <- _ _ _ _.
Qed.

Lemma bit_blast_bexp_ccache_preserve_nocbt_conj :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l) -> 
        vm_preserve m m') ->
    forall e2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
          bit_blast_bexp_ccache te m c g e2 = (m', c', g', cs, l) -> 
          vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bconj e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bconj e1 e2) = (m', c', g', cs, l) ->
        vm_preserve m m'.
Proof.
  move=> e1 IH1 e2 IH2 te m c g m' c' g' cs l Hfcbt. rewrite /= Hfcbt.
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1) => Hpmm1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2) => Hpm1m2.
  move: (vm_preserve_trans Hpmm1 Hpm1m2) => Hpmm2.
  case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csop lop] | ];
    by case=> <- _ _ _ _.
Qed.

Lemma bit_blast_bexp_ccache_preserve_nocbt_disj :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l) -> 
        vm_preserve m m') ->
    forall e2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
          bit_blast_bexp_ccache te m c g e2 = (m', c', g', cs, l) -> 
          vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bdisj e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bdisj e1 e2) = (m', c', g', cs, l) ->
        vm_preserve m m'.
Proof.
  move=> e1 IH1 e2 IH2 te m c g m' c' g' cs l Hfcbt. rewrite /= Hfcbt.
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1) => Hpmm1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2) => Hpm1m2.
  move: (vm_preserve_trans Hpmm1 Hpm1m2) => Hpmm2.
  case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csop lop] | ];
    by case=> <- _ _ _ _.
Qed.


Corollary bit_blast_exp_ccache_preserve :
  forall (e : QFBV.exp) te m c g m' c' g' cs ls,
    bit_blast_exp_ccache te m c g e = (m', c', g', cs, ls) ->
    vm_preserve m m'
  with
    bit_blast_bexp_ccache_preserve :
      forall (e : QFBV.bexp) te m c g m' c' g' cs l,
        bit_blast_bexp_ccache te m c g e = (m', c', g', cs, l) ->
        vm_preserve m m'.
Proof.
  (* exp *)
  set IHe := bit_blast_exp_ccache_preserve.
  set IHb := bit_blast_bexp_ccache_preserve.
  move=> e te m c g m' c' g' cs ls.
  case Hfcet: (find_cet e c) => [[cse lse] | ]. 
  - rewrite bit_blast_exp_ccache_equation Hfcet /=.
    case=> <- _ _ _ _. done. 
  - move: e te m c g m' c' g' cs ls Hfcet.
    case.
    + exact: bit_blast_exp_ccache_preserve_nocet_var.
    + exact: bit_blast_exp_ccache_preserve_nocet_const.
    + move=> op e1; move: op e1 (IHe e1).
      exact: bit_blast_exp_ccache_preserve_nocet_unop.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_exp_ccache_preserve_nocet_binop.
    + move=> b e1 e2; move: b (IHb b) e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_exp_ccache_preserve_nocet_ite.
  (* bexp *)
  set IHe := bit_blast_exp_ccache_preserve.
  set IHb := bit_blast_bexp_ccache_preserve.
  move=> e te m c g m' c' g' cs l.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite bit_blast_bexp_ccache_equation Hfcbt /=.
    case=> <- _ _ _ _. done. 
  - move: e te m c g m' c' g' cs l Hfcbt.
    case.
    + exact: bit_blast_bexp_ccache_preserve_nocbt_false.
    + exact: bit_blast_bexp_ccache_preserve_nocbt_true.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_bexp_ccache_preserve_nocbt_binop.
    + move=> e1; move: e1 (IHb e1).
      exact: bit_blast_bexp_ccache_preserve_nocbt_lneg.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: bit_blast_bexp_ccache_preserve_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: bit_blast_bexp_ccache_preserve_nocbt_disj.
Qed.


(* = mk_env_exp_ccache_preserve and mk_env_bexp_ccache_preserve = *)

Lemma mk_env_eunop_preserve op E g ls1 E' g' cs ls :
  mk_env_eunop op E g ls1 = (E', g', cs, ls) -> env_preserve E E' g.
Proof.
  case op => [ | | i j | n | n | n | n | n | n | n ] /=;
    [ exact: mk_env_not_preserve |
      exact: mk_env_neg_preserve |
      exact: mk_env_extract_preserve |
      exact: mk_env_high_preserve |
      exact: mk_env_low_preserve |
      exact: mk_env_zeroextend_preserve |
      exact: mk_env_signextend_preserve |
      exact: mk_env_repeat_preserve |
      exact: mk_env_rotateleft_preserve |
      exact: mk_env_rotateright_preserve ].
Qed.

Lemma mk_env_ebinop_preserve op E g ls1 ls2 E' g' cs ls :
  mk_env_ebinop op E g ls1 ls2 = (E', g', cs, ls) -> env_preserve E E' g.
Proof.
  case op;
    [ exact: mk_env_and_preserve |
      exact: mk_env_or_preserve |
      exact: mk_env_xor_preserve |
      exact: mk_env_add_preserve |
      exact: mk_env_sub_preserve |
      exact: mk_env_mul_preserve |
      exact: mk_env_udiv_preserve' |
      exact: mk_env_umod_preserve |
      exact: mk_env_sdiv_preserve |
      exact: mk_env_srem_preserve |
      exact: mk_env_smod_preserve |
      exact: mk_env_shl_preserve |
      exact: mk_env_lshr_preserve |
      exact: mk_env_ashr_preserve |
      exact: mk_env_concat_preserve |
      exact: mk_env_comp_preserve ].
Qed.

Lemma mk_env_bbinop_preserve op E g ls1 ls2 E' g' cs l :
  mk_env_bbinop op E g ls1 ls2 = (E', g', cs, l) -> env_preserve E E' g.
Proof.
  case op => /=;
    [ exact: mk_env_eq_preserve |
      exact: mk_env_ult_preserve |
      exact: mk_env_ule_preserve |
      exact: mk_env_ugt_preserve |
      exact: mk_env_uge_preserve |
      exact: mk_env_slt_preserve |
      exact: mk_env_sle_preserve |
      exact: mk_env_sgt_preserve |
      exact: mk_env_sge_preserve |
      exact: mk_env_uaddo_preserve |
      exact: mk_env_usubo_preserve |
      exact: mk_env_umulo_preserve |
      exact: mk_env_saddo_preserve |
      exact: mk_env_ssubo_preserve |
      exact: mk_env_smulo_preserve ].
Qed.

Lemma mk_env_exp_ccache_preserve_nocet_var :
  forall (t : SSAVarOrder.t) (m : vm) (c : compcache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (c' : compcache) 
         (E' : env) (g' : generator) (cs : cnf) (ls : word),
    find_cet (QFBV.Evar t) c = None ->
    mk_env_exp_ccache m c s E g (QFBV.Evar t) = (m', c', E', g', cs, ls) ->
    env_preserve E E' g.
Proof.
  move=> v m c s E g m' c' E' g' cs ls Hfcet. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Evar v) c) => [[cse lse] | ];
    last case Hfv : (SSAVM.find v m);
    last case Hv: (mk_env_var E g (SSAStore.acc v s) v) => [[[Ev gv] csv] lsv];
    case=> _ _ <- _ _ _;
    (exact: env_preserve_refl || exact: (mk_env_var_preserve Hv)).
Qed.

Lemma mk_env_exp_ccache_preserve_nocet_const :
  forall (b : bits) (m : vm) (c : compcache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (c' : compcache) 
         (E' : env) (g' : generator) (cs : cnf) (ls : word),
    find_cet (QFBV.Econst b) c = None ->
    mk_env_exp_ccache m c s E g (QFBV.Econst b) = (m', c', E', g', cs, ls) ->
    env_preserve E E' g.
Proof.
  move=> bs m c s E g m' c' E' g' cs ls Hfcet. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Econst bs) c) => [[csop lsop] | ];
    by case=> _ _ <- _ _ _.
Qed.

Lemma mk_env_exp_ccache_preserve_nocet_unop :
  forall (op : QFBV.eunop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) -> env_preserve E E' g) ->
    forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
           (g : generator) (m' : vm) (c' : compcache) (E' : env) 
           (g' : generator) (cs : cnf) (ls : word),
      find_cet (QFBV.Eunop op e1) c = None ->
      mk_env_exp_ccache m c s E g (QFBV.Eunop op e1) = (m', c', E', g', cs, ls) ->
      env_preserve E E' g.
Proof.
  move=> op e1 IH1 m c s E g m' c' E' g' cs ls Hfcet. rewrite /= Hfcet.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1) => HpEE1g.
  case Hfhet : (find_het (QFBV.Eunop op e1) c1) => [[csop lsop] | ].
  - case=> _ _ <- _ _ _. done.
  - case Hop : (mk_env_eunop op E1 g1 ls1) => [[[Eop gop] csop] lsop].
    case=> _ _ <- _ _ _. 
    move: (mk_env_eunop_preserve Hop) => HpE1Eopg1.
    move: (mk_env_exp_ccache_newer_gen He1) => Hgg1.
    move: (env_preserve_le HpE1Eopg1 Hgg1) => {HpE1Eopg1} HpE1Eopg.
    exact: (env_preserve_trans HpEE1g HpE1Eopg).
Qed.

Lemma mk_env_exp_ccache_preserve_nocet_binop :
  forall (op : QFBV.ebinop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) -> 
        env_preserve E E' g) ->
    forall e2 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
          env_preserve E E' g) ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (ls : word),
        find_cet (QFBV.Ebinop op e1 e2) c = None ->
        mk_env_exp_ccache m c s E g (QFBV.Ebinop op e1 e2) = (m', c', E', g', cs, ls) ->
        env_preserve E E' g.
Proof.
  move=> op e1 IH1 e2 IH2 m c s E g m' c' E' g' cs ls Hfcet. rewrite /= Hfcet.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2) => HpE1E2g1.
  move: (mk_env_exp_ccache_newer_gen He1) => Hgg1.
  move: (env_preserve_le HpE1E2g1 Hgg1) => {HpE1E2g1} HpE1E2g.
  move: (env_preserve_trans HpEE1g HpE1E2g) => HpEE2g.
  case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csop lsop] | ].
  - case=> _ _ <- _ _ _. done.
  - case Hop : (mk_env_ebinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lsop].
    case=> _ _ <- _ _ _. 
    move: (mk_env_ebinop_preserve Hop) => HpE2Eopg2.
    move: (mk_env_exp_ccache_newer_gen He2) => Hg1g2.
    move: (pos_leb_trans Hgg1 Hg1g2) => Hgg2.
    move: (env_preserve_le HpE2Eopg2 Hgg2) => {HpE2Eopg2} HpE2Eopg.
    exact: (env_preserve_trans HpEE2g HpE2Eopg).
Qed.

Lemma mk_env_exp_ccache_preserve_nocet_ite :
  forall b : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g b = (m', c', E', g', cs, l) -> 
        env_preserve E E' g) ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) -> 
          env_preserve E E' g) ->
      forall e2 : QFBV.exp,
        (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
                (g : generator) (m' : vm) (c' : compcache) (E' : env) 
                (g' : generator) (cs : cnf) (ls : word),
            mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) -> 
            env_preserve E E' g) ->
        forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
               (g : generator) (m' : vm) (c' : compcache) (E' : env) 
               (g' : generator) (cs : cnf) (ls : word),
          find_cet (QFBV.Eite b e1 e2) c = None ->
          mk_env_exp_ccache m c s E g (QFBV.Eite b e1 e2) = (m', c', E', g', cs, ls) ->
          env_preserve E E' g.
Proof.
  move=> b IHb e1 IH1 e2 IH2 m c s E g m' c' E' g' cs ls Hfcet. rewrite /= Hfcet.
  case Hb : (mk_env_bexp_ccache m c s E g b) => [[[[[mb cb] Eb] gb] csb] lb].
  case He1 : (mk_env_exp_ccache mb cb s Eb gb e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IHb _ _ _ _ _ _ _ _ _ _ _ Hb) => HpEEbg.
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1) => HpEbE1gb.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2) => HpE1E2g1.
  move: (mk_env_bexp_ccache_newer_gen Hb) => Hggb.
  move: (env_preserve_le HpEbE1gb Hggb) => {HpEbE1gb} HpEbE1g.
  move: (mk_env_exp_ccache_newer_gen He1) => Hgbg1.
  move: (env_preserve_le HpE1E2g1 Hgbg1) => {HpE1E2g1} HpE1E2gb.
  move: (env_preserve_le HpE1E2gb Hggb) => {HpE1E2gb} HpE1E2g.
  move: (env_preserve_trans HpEEbg (env_preserve_trans HpEbE1g HpE1E2g)) => HpEE2g.
  case Hfhet : (find_het (QFBV.Eite b e1 e2) c2) => [[csop lsop] | ].
  - case=> _ _ <- _ _ _. done.
  - case Hop : (mk_env_ite E2 g2 lb ls1 ls2) => [[[Eop gop] csop] lsop].
    case=> _ _ <- _ _ _. 
    move: (mk_env_ite_preserve Hop) => HpE2Eopg2.
    move: (mk_env_exp_ccache_newer_gen He2) => Hg1g2.
    move: (pos_leb_trans Hggb (pos_leb_trans Hgbg1 Hg1g2)) => Hgg2.
    move: (env_preserve_le HpE2Eopg2 Hgg2) => {HpE2Eopg2} HpE2Eopg.
    exact: (env_preserve_trans HpEE2g HpE2Eopg).
Qed.

Lemma mk_env_bexp_ccache_preserve_nocbt_false :
  forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
         (g : generator) (m' : vm) (c' : compcache) (E' : env) 
         (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Bfalse c = None ->
    mk_env_bexp_ccache m c s E g QFBV.Bfalse = (m', c', E', g', cs, l) ->
    env_preserve E E' g.
Proof.
  move=> m c s E g m' c' E' g' cs l Hfcbt. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Bfalse) c) => [[csop lop] | ];
    by case=> _ _ <- _ _ _.
Qed.

Lemma mk_env_bexp_ccache_preserve_nocbt_true :
  forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
         (g : generator) (m' : vm) (c' : compcache) (E' : env) 
         (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Btrue c = None ->
    mk_env_bexp_ccache m c s E g QFBV.Btrue = (m', c', E', g', cs, l) ->
    env_preserve E E' g.
Proof.
  move=> m c s E g m' c' E' g' cs l Hfcbt. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Btrue) c) => [[csop lop] | ];
    by case=> _ _ <- _ _ _.
Qed.

Lemma mk_env_bexp_ccache_preserve_nocbt_binop :
  forall (op : QFBV.bbinop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) -> 
        env_preserve E E' g) ->
    forall e2 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
          env_preserve E E' g) ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bbinop op e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bbinop op e1 e2) = (m', c', E', g', cs, l) ->
        env_preserve E E' g.
Proof.
  move=> op e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt. rewrite /= Hfcbt.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2) => HpE1E2g1.
  move: (mk_env_exp_ccache_newer_gen He1) => Hgg1.
  move: (env_preserve_le HpE1E2g1 Hgg1) => {HpE1E2g1} HpE1E2g.
  move: (env_preserve_trans HpEE1g HpE1E2g) => HpEE2g.
  case Hfhbt : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[csop lop] | ].
  - case=> _ _ <- _ _ _. done.
  - case Hop : (mk_env_bbinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lop].
    case=> _ _ <- _ _ _. 
    move: (mk_env_bbinop_preserve Hop) => HpE2Eopg2.
    move: (mk_env_exp_ccache_newer_gen He2) => Hg1g2.
    move: (pos_leb_trans Hgg1 Hg1g2) => Hgg2.
    move: (env_preserve_le HpE2Eopg2 Hgg2) => {HpE2Eopg2} HpE2Eopg.
    exact: (env_preserve_trans HpEE2g HpE2Eopg).
Qed.

Lemma mk_env_bexp_ccache_preserve_nocbt_lneg :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) -> 
        env_preserve E E' g) ->
    forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
           (g : generator) (m' : vm) (c' : compcache) (E' : env) 
           (g' : generator) (cs : cnf) (l : literal),
      find_cbt (QFBV.Blneg e1) c = None ->
      mk_env_bexp_ccache m c s E g (QFBV.Blneg e1) = (m', c', E', g', cs, l) ->
      env_preserve E E' g.
Proof.
  move=> e1 IH1 m c s E g m' c' E' g' cs l Hfcbt. 
  rewrite /mk_env_bexp_ccache -/mk_env_bexp_ccache Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1) => HpEE1g.
  case Hfhbt : (find_hbt (QFBV.Blneg e1) c1) => [[csop lop] | ].
  - case=> _ _ <- _ _ _. done.
  - case Hop : (mk_env_lneg E1 g1 l1) => [[[Eop gop] csop] lop].
    case=> _ _ <- _ _ _. 
    move: (mk_env_lneg_preserve Hop) => HpE1Eopg1.
    move: (mk_env_bexp_ccache_newer_gen He1) => Hgg1.
    move: (env_preserve_le HpE1Eopg1 Hgg1) => {HpE1Eopg1} HpE1Eopg.
    exact: (env_preserve_trans HpEE1g HpE1Eopg).
Qed.

Lemma mk_env_bexp_ccache_preserve_nocbt_conj :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) -> 
        env_preserve E E' g) ->
    forall e2 : QFBV.bexp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (l : literal),
          mk_env_bexp_ccache m c s E g e2 = (m', c', E', g', cs, l) -> 
          env_preserve E E' g) ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bconj e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bconj e1 e2) = (m', c', E', g', cs, l) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt. 
  rewrite /mk_env_bexp_ccache -/mk_env_bexp_ccache Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  case He2 : (mk_env_bexp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2) => HpE1E2g1.
  move: (mk_env_bexp_ccache_newer_gen He1) => Hgg1.
  move: (env_preserve_le HpE1E2g1 Hgg1) => {HpE1E2g1} HpE1E2g.
  move: (env_preserve_trans HpEE1g HpE1E2g) => HpEE2g.
  case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csop lop] | ].
  - case=> _ _ <- _ _ _. done.
  - case Hop : (mk_env_conj E2 g2 l1 l2) => [[[Eop gop] csop] lop].
    case=> _ _ <- _ _ _. 
    move: (mk_env_conj_preserve Hop) => HpE2Eopg2.
    move: (mk_env_bexp_ccache_newer_gen He2) => Hg1g2.
    move: (pos_leb_trans Hgg1 Hg1g2) => Hgg2.
    move: (env_preserve_le HpE2Eopg2 Hgg2) => {HpE2Eopg2} HpE2Eopg.
    exact: (env_preserve_trans HpEE2g HpE2Eopg).
Qed.

Lemma mk_env_bexp_ccache_preserve_nocbt_disj :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) -> 
        env_preserve E E' g) ->
    forall e2 : QFBV.bexp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (l : literal),
          mk_env_bexp_ccache m c s E g e2 = (m', c', E', g', cs, l) -> 
          env_preserve E E' g) ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bdisj e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bdisj e1 e2) = (m', c', E', g', cs, l) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt. 
  rewrite /mk_env_bexp_ccache -/mk_env_bexp_ccache Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  case He2 : (mk_env_bexp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2) => HpE1E2g1.
  move: (mk_env_bexp_ccache_newer_gen He1) => Hgg1.
  move: (env_preserve_le HpE1E2g1 Hgg1) => {HpE1E2g1} HpE1E2g.
  move: (env_preserve_trans HpEE1g HpE1E2g) => HpEE2g.
  case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csop lop] | ].
  - case=> _ _ <- _ _ _. done.
  - case Hop : (mk_env_disj E2 g2 l1 l2) => [[[Eop gop] csop] lop].
    case=> _ _ <- _ _ _. 
    move: (mk_env_disj_preserve Hop) => HpE2Eopg2.
    move: (mk_env_bexp_ccache_newer_gen He2) => Hg1g2.
    move: (pos_leb_trans Hgg1 Hg1g2) => Hgg2.
    move: (env_preserve_le HpE2Eopg2 Hgg2) => {HpE2Eopg2} HpE2Eopg.
    exact: (env_preserve_trans HpEE2g HpE2Eopg).
Qed.


Corollary mk_env_exp_ccache_preserve :
  forall (e : QFBV.exp) m c s E g m' c' E' g' cs ls,
    mk_env_exp_ccache m c s E g e = (m', c', E', g', cs, ls) ->
    env_preserve E E' g
  with
    mk_env_bexp_ccache_preserve :
      forall e m c s E g m' c' E' g' cs l,
        mk_env_bexp_ccache m c s E g e = (m', c', E', g', cs, l) ->
        env_preserve E E' g.
Proof.
  (* exp *)
  set IHe := mk_env_exp_ccache_preserve.
  set IHb := mk_env_bexp_ccache_preserve.
  move=> e m c s E g m' c' E' g' cs ls.
  case Hfcet: (find_cet e c) => [[cse lse] | ]. 
  - rewrite mk_env_exp_ccache_equation Hfcet /=.
    case=> _ _ <- _ _ _. exact: env_preserve_refl.
  - move: e m c s E g m' c' E' g' cs ls Hfcet.
    case.
    + exact: mk_env_exp_ccache_preserve_nocet_var.
    + exact: mk_env_exp_ccache_preserve_nocet_const.
    + move=> op e1; move: op e1 (IHe e1).
      exact: mk_env_exp_ccache_preserve_nocet_unop.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_preserve_nocet_binop.
    + move=> b e1 e2; move: b (IHb b) e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_preserve_nocet_ite.
  (* bexp *)
  set IHe := mk_env_exp_ccache_preserve.
  set IHb := mk_env_bexp_ccache_preserve.
  move=> e m c s E g m' c' E' g' cs l.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite mk_env_bexp_ccache_equation Hfcbt /=.
    case=> _ _ <- _ _ _. exact: env_preserve_refl.
  - move: e m c s E g m' c' E' g' cs l Hfcbt.
    case.
    + exact: mk_env_bexp_ccache_preserve_nocbt_false.
    + exact: mk_env_bexp_ccache_preserve_nocbt_true.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_bexp_ccache_preserve_nocbt_binop.
    + move=> e1; move: e1 (IHb e1).
      exact: mk_env_bexp_ccache_preserve_nocbt_lneg.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_preserve_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_preserve_nocbt_disj.
Qed.


(* = bit_blast_exp_ccache_preserve_cache and bit_blast_bexp_ccache_preserve_cache = *)

Lemma bit_blast_exp_ccache_preserve_cache_nocet_var :
  forall (t : SSAVarOrder.t) (te : SSATE.env) (m : vm) (c : compcache)
         (g : generator) (m' : vm) (c' : compcache) (g' : generator) 
         (cs : cnf) (ls : word),
    find_cet (QFBV.Evar t) c = None ->
    bit_blast_exp_ccache te m c g (QFBV.Evar t) = (m', c', g', cs, ls) ->
    preserve c c'.
Proof.
  move=> v te m c g m' c' g' cs ls Hfcet. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Evar v) c) => [[cse lse] | ].
  - case=> _ <- _ _ _. by apply preserve_add_cet. 
  - case Hfv : (SSAVM.find v m);
      last case Hv : (bit_blast_var te g v) => [[gv csv] lsv];
      case=> _ <- _ _ _; apply preserve_add_cet;
      by (apply preserve_add_het || rewrite find_cet_add_het). 
Qed.

Lemma bit_blast_exp_ccache_preserve_cache_nocet_const :
  forall (b : bits) (te : SSATE.env) (m : vm) (c : compcache) 
         (g : generator) (m' : vm) (c' : compcache) (g' : generator) 
         (cs : cnf) (ls : word),
    find_cet (QFBV.Econst b) c = None ->
    bit_blast_exp_ccache te m c g (QFBV.Econst b) = (m', c', g', cs, ls) ->
    preserve c c'.
Proof.
  move=> bs te m c g m' c' g' cs ls Hfcet. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Econst bs) c) => [[csop lsop] | ];
    case=> _ <- _ _ _; apply preserve_add_cet;
    try (apply preserve_add_het || rewrite find_cet_add_het);
    done.
Qed.

Lemma bit_blast_exp_ccache_preserve_cache_nocet_unop :
  forall (op : QFBV.eunop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, lrs) -> preserve c c') ->
    forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
           (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
      find_cet (QFBV.Eunop op e1) c = None ->
      bit_blast_exp_ccache te m c g (QFBV.Eunop op e1) = (m', c', g', cs, ls) ->
      preserve c c'.
Proof.
  move=> op e1 IH1 te m c g m' c' g' cs ls Hfcet. rewrite /= Hfcet.
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1) => Hpcc1.
  rewrite -(bit_blast_exp_ccache_find_cet _ He1) in Hfcet; try by auto_prove_len_lt. 
  case Hfhet : (find_het (QFBV.Eunop op e1) c1) => [[csop lsop] | ];
    last case Hop : (bit_blast_eunop op g1 ls1) => [[gop csop] lsop];
    case=> _ <- _ _ _; apply preserve_add_cet;
    try (apply preserve_add_het || rewrite find_cet_add_het);
    done.
Qed.

Lemma bit_blast_exp_ccache_preserve_cache_nocet_binop :
  forall (op : QFBV.ebinop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, lrs) -> 
        preserve c c') ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, lrs) -> 
          preserve c c') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        find_cet (QFBV.Ebinop op e1 e2) c = None ->
        bit_blast_exp_ccache te m c g (QFBV.Ebinop op e1 e2) = (m', c', g', cs, ls) ->
        preserve c c'.
Proof.
  move=> op e1 IH1 e2 IH2 te m c g m' c' g' cs ls Hfcet. rewrite /= Hfcet.
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].  
  move: (IH1 _ _ _ _ _ _ _ _ _ He1) => Hpcc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2) => Hpc1c2.
  move: (preserve_trans Hpcc1 Hpc1c2) => Hpcc2.
  rewrite -(bit_blast_exp_ccache_find_cet _ He1) in Hfcet; try by auto_prove_len_lt. 
  rewrite -(bit_blast_exp_ccache_find_cet _ He2) in Hfcet; try by auto_prove_len_lt.
  case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csop lsop] | ];
    last case Hop : (bit_blast_ebinop op g2 ls1 ls2) => [[gop csop] lsop];
    case=> _ <- _ _ _; apply preserve_add_cet;
    try (apply preserve_add_het || rewrite find_cet_add_het);
    done.
Qed.

Lemma bit_blast_exp_ccache_preserve_cache_nocet_ite :
  forall b : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (lrs : literal),
        bit_blast_bexp_ccache te m c g b = (m', c', g', cs, lrs) -> preserve c c') ->
    forall e1 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, lrs) -> 
          preserve c c') ->
      forall e2 : QFBV.exp,
        (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
                (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (lrs : word),
            bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, lrs) -> 
            preserve c c') ->
        forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
               (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
          find_cet (QFBV.Eite b e1 e2) c = None ->
          bit_blast_exp_ccache te m c g (QFBV.Eite b e1 e2) = (m', c', g', cs, ls) ->
          preserve c c'.
Proof.
  move=> b IHb e1 IH1 e2 IH2 te m c g m' c' g' cs ls Hfcet. rewrite /= Hfcet.
  case Hb : (bit_blast_bexp_ccache te m c g b) => [[[[mb cb] gb] csb] lb].  
  case He1 : (bit_blast_exp_ccache te mb cb gb e1) => [[[[m1 c1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].  
  move: (IHb _ _ _ _ _ _ _ _ _ Hb) => Hpccb.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1) => Hpcbc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2) => Hpc1c2.
  move: (preserve_trans Hpccb (preserve_trans Hpcbc1 Hpc1c2)) => Hpcc2.
  rewrite -(bit_blast_bexp_ccache_find_cet _ Hb) in Hfcet; try by auto_prove_len_lt. 
  rewrite -(bit_blast_exp_ccache_find_cet _ He1) in Hfcet; try by auto_prove_len_lt. 
  rewrite -(bit_blast_exp_ccache_find_cet _ He2) in Hfcet; try by auto_prove_len_lt.
  case Hfhet : (find_het (QFBV.Eite b e1 e2) c2) => [[csop lsop] | ];
    last case Hop : (bit_blast_ite g2 lb ls1 ls2) => [[gop csop] lsop];
    case=> _ <- _ _ _; apply preserve_add_cet;
    try (apply preserve_add_het || rewrite find_cet_add_het);
    done.
Qed.

Lemma bit_blast_bexp_ccache_preserve_cache_nocbt_false :
  forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
         (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Bfalse c = None ->
    bit_blast_bexp_ccache te m c g QFBV.Bfalse = (m', c', g', cs, l) -> 
    preserve c c'.
Proof.
  move=> te m c g m' c' g' cs l Hfcbt. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Bfalse) c) => [[csop lop] | ];
    case=> _ <- _ _ _; apply preserve_add_cbt;
    try (apply preserve_add_hbt || rewrite find_cbt_add_hbt);
    done.
Qed.

Lemma bit_blast_bexp_ccache_preserve_cache_nocbt_true :
  forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
         (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Btrue c = None ->
    bit_blast_bexp_ccache te m c g QFBV.Btrue = (m', c', g', cs, l) -> 
    preserve c c'.
Proof.
  move=> te m c g m' c' g' cs l Hfcbt. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Btrue) c) => [[csop lop] | ];
    case=> _ <- _ _ _; apply preserve_add_cbt;
    try (apply preserve_add_hbt || rewrite find_cbt_add_hbt);
    done.
Qed.

Lemma bit_blast_bexp_ccache_preserve_cache_nocbt_binop :
  forall (op : QFBV.bbinop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, lrs) -> preserve c c') ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, lrs) -> 
          preserve c c') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bbinop op e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bbinop op e1 e2) = (m', c', g', cs, l) ->
        preserve c c'.
Proof.
  move=> op e1 IH1 e2 IH2 te m c g m' c' g' cs l Hfcbt. rewrite /= Hfcbt.
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].  
  move: (IH1 _ _ _ _ _ _ _ _ _ He1) => Hpcc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2) => Hpc1c2.
  move: (preserve_trans Hpcc1 Hpc1c2) => Hpcc2.
  rewrite -(bit_blast_exp_ccache_find_cbt _ He1) in Hfcbt; try by auto_prove_len_lt. 
  rewrite -(bit_blast_exp_ccache_find_cbt _ He2) in Hfcbt; try by auto_prove_len_lt.
  case Hfhbt : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[csop lop] | ];
    last case Hop : (bit_blast_bbinop op g2 ls1 ls2) => [[gop csop] lop];
    case=> _ <- _ _ _; apply preserve_add_cbt;
    try (apply preserve_add_hbt || rewrite find_cbt_add_hbt);
    done.
Qed.

Lemma bit_blast_bexp_ccache_preserve_cache_nocbt_lneg :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (lrs : literal),
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, lrs) -> 
        preserve c c') ->
    forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
           (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
      find_cbt (QFBV.Blneg e1) c = None ->
      bit_blast_bexp_ccache te m c g (QFBV.Blneg e1) = (m', c', g', cs, l) ->
      preserve c c'.
Proof.
  move=> e1 IH1 te m c g m' c' g' cs l Hfcbt. 
  rewrite /bit_blast_bexp_ccache -/bit_blast_bexp_ccache Hfcbt.
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1) => Hpcc1.
  rewrite -(bit_blast_bexp_ccache_find_cbt _ He1) in Hfcbt; try by auto_prove_len_lt.
  case Hfhbt : (find_hbt (QFBV.Blneg e1) c1) => [[csop lop] | ];
    last case Hop : (bit_blast_lneg g1 l1) => [[gop csop] lop];
    case=> _ <- _ _ _; apply preserve_add_cbt;
    try (apply preserve_add_hbt || rewrite find_cbt_add_hbt);
    done.
Qed.
                                                                                 
Lemma bit_blast_bexp_ccache_preserve_cache_nocbt_conj :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (lrs : literal),
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, lrs) -> 
        preserve c c') ->
    forall e2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (lrs : literal),
          bit_blast_bexp_ccache te m c g e2 = (m', c', g', cs, lrs) -> 
          preserve c c') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bconj e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bconj e1 e2) = (m', c', g', cs, l) ->
        preserve c c'.
Proof.
  move=> e1 IH1 e2 IH2 te m c g m' c' g' cs l Hfcbt. 
  rewrite /bit_blast_bexp_ccache -/bit_blast_bexp_ccache Hfcbt.
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1) => Hpcc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2) => Hpc1c2.
  move: (preserve_trans Hpcc1 Hpc1c2) => Hpcc2.
  rewrite -(bit_blast_bexp_ccache_find_cbt _ He1) in Hfcbt; try by auto_prove_len_lt.
  rewrite -(bit_blast_bexp_ccache_find_cbt _ He2) in Hfcbt; try by auto_prove_len_lt.
  case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csop lop] | ];
    last case Hop : (bit_blast_conj g2 l1 l2) => [[gop csop] lop];
    case=> _ <- _ _ _; apply preserve_add_cbt;
    try (apply preserve_add_hbt || rewrite find_cbt_add_hbt);
    done.
Qed.

Lemma bit_blast_bexp_ccache_preserve_cache_nocbt_disj :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (lrs : literal),
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, lrs) -> 
        preserve c c') ->
    forall e2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (lrs : literal),
          bit_blast_bexp_ccache te m c g e2 = (m', c', g', cs, lrs) -> 
          preserve c c') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bdisj e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bdisj e1 e2) = (m', c', g', cs, l) ->
        preserve c c'.
Proof.
  move=> e1 IH1 e2 IH2 te m c g m' c' g' cs l Hfcbt. 
  rewrite /bit_blast_bexp_ccache -/bit_blast_bexp_ccache Hfcbt.
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1) => Hpcc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2) => Hpc1c2.
  move: (preserve_trans Hpcc1 Hpc1c2) => Hpcc2.
  rewrite -(bit_blast_bexp_ccache_find_cbt _ He1) in Hfcbt; try by auto_prove_len_lt.
  rewrite -(bit_blast_bexp_ccache_find_cbt _ He2) in Hfcbt; try by auto_prove_len_lt.
  case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csop lop] | ];
    last case Hop : (bit_blast_disj g2 l1 l2) => [[gop csop] lop];
    case=> _ <- _ _ _; apply preserve_add_cbt;
    try (apply preserve_add_hbt || rewrite find_cbt_add_hbt);
    done.
Qed.

Corollary bit_blast_exp_ccache_preserve_cache :
  forall (e : QFBV.exp) te m c g m' c' g' cs lrs,
    bit_blast_exp_ccache te m c g e = (m', c', g', cs, lrs) ->
    CompCache.preserve c c'
  with
    bit_blast_bexp_ccache_preserve_cache :
      forall (e : QFBV.bexp) te m c g m' c' g' cs lrs,
        bit_blast_bexp_ccache te m c g e = (m', c', g', cs, lrs) ->
        CompCache.preserve c c'.
Proof.
  (* exp *)
  set IHe := bit_blast_exp_ccache_preserve_cache.
  set IHb := bit_blast_bexp_ccache_preserve_cache.
  move=> e te m c g m' c' g' cs ls.
  case Hfcet: (find_cet e c) => [[cse lse] | ]. 
  - rewrite bit_blast_exp_ccache_equation Hfcet /=.
    case=> _ <- _ _ _. done. 
  - move: e te m c g m' c' g' cs ls Hfcet.
    case.
    + exact: bit_blast_exp_ccache_preserve_cache_nocet_var.
    + exact: bit_blast_exp_ccache_preserve_cache_nocet_const.
    + move=> op e1; move: op e1 (IHe e1).
      exact: bit_blast_exp_ccache_preserve_cache_nocet_unop.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_exp_ccache_preserve_cache_nocet_binop.
    + move=> b e1 e2; move: b (IHb b) e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_exp_ccache_preserve_cache_nocet_ite.
  (* bexp *)
  set IHe := bit_blast_exp_ccache_preserve_cache.
  set IHb := bit_blast_bexp_ccache_preserve_cache.
  move=> e te m c g m' c' g' cs l.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite bit_blast_bexp_ccache_equation Hfcbt /=.
    case=> _ <- _ _ _. done. 
  - move: e te m c g m' c' g' cs l Hfcbt.
    case.
    + exact: bit_blast_bexp_ccache_preserve_cache_nocbt_false.
    + exact: bit_blast_bexp_ccache_preserve_cache_nocbt_true.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_bexp_ccache_preserve_cache_nocbt_binop.
    + move=> e1; move: e1 (IHb e1).
      exact: bit_blast_bexp_ccache_preserve_cache_nocbt_lneg.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: bit_blast_bexp_ccache_preserve_cache_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: bit_blast_bexp_ccache_preserve_cache_nocbt_disj.
Qed.
