From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types EqOrder EqVar Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
From BBCache Require Import CompCache BitBlastingCCacheDef.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* = bit_blast_exp_ccache_well_formed and bit_blast_bexp_ccache_well_formed = *)

Lemma bit_blast_exp_ccache_well_formed_nocet_var :
  forall (t : SSAVarOrder.t) (te : SSATE.env) (m : vm) (c : compcache)
         (g : generator) (m' : vm) (c' : compcache) (g' : generator) 
         (cs : cnf) (ls : word),
    find_cet (QFBV.Evar t) c = None ->
    bit_blast_exp_ccache te m c g (QFBV.Evar t) = (m', c', g', cs, ls) ->
    well_formed c -> well_formed c'.
Proof.
  move=> v te m c g m' c' g' cs ls Hfcet. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Evar v) c) => [[cse lse] | ];
    last case Hfv : (SSAVM.find v m);
    last case Hv : (bit_blast_var te g v) => [[gv csv] lsv];
    case=> _ <- _ _ _ Hwfc; 
    (apply well_formed_add_cet_het || apply well_formed_add_cet); done.
Qed.

Lemma bit_blast_exp_ccache_well_formed_nocet_const :
  forall (b : bits) (te : SSATE.env) (m : vm) (c : compcache) 
         (g : generator) (m' : vm) (c' : compcache) (g' : generator) 
         (cs : cnf) (ls : word),
    find_cet (QFBV.Econst b) c = None ->
    bit_blast_exp_ccache te m c g (QFBV.Econst b) = (m', c', g', cs, ls) ->
    well_formed c -> well_formed c'.
Proof.
  move=> bs te m c g m' c' g' cs ls Hfcet Hbb Hwfc.
  move: Hbb. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Econst bs) c) => [[csop lsop] | ];
    case=> _ <- _ _ _; 
    (apply well_formed_add_cet_het || apply well_formed_add_cet); done.
Qed.

Lemma bit_blast_exp_ccache_well_formed_nocet_unop :
  forall (op : QFBV.eunop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) ->
        well_formed c -> well_formed c') ->
    forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
           (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
      find_cet (QFBV.Eunop op e1) c = None ->
      bit_blast_exp_ccache te m c g (QFBV.Eunop op e1) = (m', c', g', cs, ls) ->
      well_formed c -> well_formed c'.
Proof.
  move=> op e1 IH1 te m c g m' c' g' cs ls Hfcet Hbb Hwfc.
  move: Hbb. rewrite /= Hfcet.
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwfc) => Hwfc1.
  case Hfhet : (find_het (QFBV.Eunop op e1) c1) => [[csop lsop] | ];
    last case Hop : (bit_blast_eunop op g1 ls1) => [[gop csop] lsop];
    case=> _ <- _ _ _; 
    (apply well_formed_add_cet_het || apply well_formed_add_cet); done.
Qed.
  
Lemma bit_blast_exp_ccache_well_formed_nocet_binop :
  forall (op : QFBV.ebinop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) ->
        well_formed c -> well_formed c') ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
          bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls) ->
          well_formed c -> well_formed c') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        find_cet (QFBV.Ebinop op e1 e2) c = None ->
        bit_blast_exp_ccache te m c g (QFBV.Ebinop op e1 e2) = (m', c', g', cs, ls) ->
        well_formed c -> well_formed c'.
Proof.
  move=> op e1 IH1 e2 IH2 te m c g m' c' g' cs ls Hfcet Hbb Hwfc.
  move: Hbb. rewrite /= Hfcet.
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hwfc1) => Hwfc2.
  case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csop lsop] | ];
    last case Hop : (bit_blast_ebinop op g2 ls1 ls2) => [[gop csop] lsop];
    case=> _ <- _ _ _; 
    (apply well_formed_add_cet_het || apply well_formed_add_cet); done.
Qed.

Lemma bit_blast_exp_ccache_well_formed_nocet_ite :
  forall b : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        bit_blast_bexp_ccache te m c g b = (m', c', g', cs, l) ->
        well_formed c -> well_formed c') ->
    forall e1 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
          bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) ->
          well_formed c -> well_formed c') ->
      forall e2 : QFBV.exp,
        (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
                (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
            bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls) ->
            well_formed c -> well_formed c') ->
        forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
               (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
          find_cet (QFBV.Eite b e1 e2) c = None ->
          bit_blast_exp_ccache te m c g (QFBV.Eite b e1 e2) = (m', c', g', cs, ls) ->
          well_formed c -> well_formed c'.
Proof.
  move=> b IHb e1 IH1 e2 IH2 te m c g m' c' g' cs ls Hfcet Hbb Hwfc.
  move: Hbb. rewrite /= Hfcet.
  case Hb : (bit_blast_bexp_ccache te m c g b) => [[[[mb cb] gb] csb] lb].
  case He1 : (bit_blast_exp_ccache te mb cb gb e1) => [[[[m1 c1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
  move: (IHb _ _ _ _ _ _ _ _ _ Hb Hwfc) => Hwfcb.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwfcb) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hwfc1) => Hwfc2.
  case Hfhet : (find_het (QFBV.Eite b e1 e2) c2) => [[csop lsop] | ];
    last case Hop : (bit_blast_ite g2 lb ls1 ls2) => [[gop csop] lsop];
    case=> _ <- _ _ _; 
    (apply well_formed_add_cet_het || apply well_formed_add_cet); done.
Qed.

Lemma bit_blast_bexp_ccache_well_formed_nocbt_false :
  forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
         (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Bfalse c = None ->
    bit_blast_bexp_ccache te m c g QFBV.Bfalse = (m', c', g', cs, l) ->
    well_formed c -> well_formed c'.
Proof.
  move=> te m c g m' c' g' cs l Hfcbt Hbb Hwfc.
  move: Hbb. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Bfalse) c) => [[csop lop] | ];
    case=> _ <- _ _ _; 
    (apply well_formed_add_cbt_hbt || apply well_formed_add_cbt); done.
Qed.

Lemma bit_blast_bexp_ccache_well_formed_nocbt_true :
  forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
         (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Btrue c = None ->
    bit_blast_bexp_ccache te m c g QFBV.Btrue = (m', c', g', cs, l) ->
    well_formed c -> well_formed c'.
Proof.
  move=> te m c g m' c' g' cs l Hfcbt Hbb Hwfc.
  move: Hbb. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Btrue) c) => [[csop lop] | ];
    case=> _ <- _ _ _; 
    (apply well_formed_add_cbt_hbt || apply well_formed_add_cbt); done.
Qed.

Lemma bit_blast_bexp_ccache_well_formed_nocbt_binop :
  forall (op : QFBV.bbinop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) ->
        well_formed c -> well_formed c') ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
          bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls) ->
          well_formed c -> well_formed c') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bbinop op e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bbinop op e1 e2) = (m', c', g', cs, l) ->
        well_formed c -> well_formed c'.
Proof.
  move=> op e1 IH1 e2 IH2 te m c g m' c' g' cs l Hfcbt Hbb Hwfc.
  move: Hbb. rewrite /= Hfcbt.
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hwfc1) => Hwfc2.
  case Hfhbt : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[csop lop] | ];
    last case Hop : (bit_blast_bbinop op g2 ls1 ls2) => [[gop csop] lop];
    case=> _ <- _ _ _; 
    (apply well_formed_add_cbt_hbt || apply well_formed_add_cbt); done.
Qed.

Lemma bit_blast_bexp_ccache_well_formed_nocbt_lneg :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l) ->
        well_formed c -> well_formed c') ->
    forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
           (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
      find_cbt (QFBV.Blneg e1) c = None ->
      bit_blast_bexp_ccache te m c g (QFBV.Blneg e1) = (m', c', g', cs, l) ->
      well_formed c -> well_formed c'.
Proof.
  move=> e1 IH1 te m c g m' c' g' cs l Hfcbt Hbb Hwfc.
  move: Hbb. rewrite /= Hfcbt.
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwfc) => Hwfc1.
  case Hfhbt : (find_hbt (QFBV.Blneg e1) c1) => [[csop lop] | ];
    (* last case Hop : (bit_blast_lneg g1 l1) => [[gop csop] lop]; *)
    case=> _ <- _ _ _; 
    (apply well_formed_add_cbt_hbt || apply well_formed_add_cbt); done.
Qed.

Lemma bit_blast_bexp_ccache_well_formed_nocbt_conj :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l) ->
        well_formed c -> well_formed c') ->
    forall e2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
          bit_blast_bexp_ccache te m c g e2 = (m', c', g', cs, l) ->
          well_formed c -> well_formed c') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bconj e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bconj e1 e2) = (m', c', g', cs, l) ->
        well_formed c -> well_formed c'.
Proof.
  move=> e1 IH1 e2 IH2 te m c g m' c' g' cs l Hfcbt Hbb Hwfc.
  move: Hbb. rewrite /= Hfcbt.
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hwfc1) => Hwfc2.
  case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csop lop] | ];
    (* last case Hop : (bit_blast_conj g2 l1 l2) => [[gop csop] lop]; *)
    case=> _ <- _ _ _; 
    (apply well_formed_add_cbt_hbt || apply well_formed_add_cbt); done.
Qed.

Lemma bit_blast_bexp_ccache_well_formed_nocbt_disj :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l) ->
        well_formed c -> well_formed c') ->
    forall e2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
          bit_blast_bexp_ccache te m c g e2 = (m', c', g', cs, l) ->
          well_formed c -> well_formed c') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bdisj e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bdisj e1 e2) = (m', c', g', cs, l) ->
        well_formed c -> well_formed c'.
Proof.
  move=> e1 IH1 e2 IH2 te m c g m' c' g' cs l Hfcbt Hbb Hwfc.
  move: Hbb. rewrite /= Hfcbt.
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hwfc1) => Hwfc2.
  case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csop lop] | ];
    (* last case Hop : (bit_blast_disj g2 l1 l2) => [[gop csop] lop]; *)
    case=> _ <- _ _ _; 
    (apply well_formed_add_cbt_hbt || apply well_formed_add_cbt); done.
Qed.

Corollary bit_blast_exp_ccache_well_formed :
  forall (e : QFBV.exp) te m c g m' c' g' cs ls,
    bit_blast_exp_ccache te m c g e = (m', c', g', cs, ls) ->
    CompCache.well_formed c -> CompCache.well_formed c'
  with
    bit_blast_bexp_ccache_well_formed :
      forall (e : QFBV.bexp) te m c g m' c' g' cs l,
        bit_blast_bexp_ccache te m c g e = (m', c', g', cs, l) ->
        CompCache.well_formed c -> CompCache.well_formed c'.
Proof.
  (* exp *)
  set IHe := bit_blast_exp_ccache_well_formed.
  set IHb := bit_blast_bexp_ccache_well_formed.
  move=> e te m c g m' c' g' cs ls.
  case Hfcet: (find_cet e c) => [[cse lse] | ]. 
  - rewrite bit_blast_exp_ccache_equation Hfcet /=.
    case=> _ <- _ _ _. done. 
  - move: e te m c g m' c' g' cs ls Hfcet.
    case.
    + exact: bit_blast_exp_ccache_well_formed_nocet_var.
    + exact: bit_blast_exp_ccache_well_formed_nocet_const.
    + move=> op e1; move: op e1 (IHe e1).
      exact: bit_blast_exp_ccache_well_formed_nocet_unop.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_exp_ccache_well_formed_nocet_binop.
    + move=> b e1 e2; move: b (IHb b) e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_exp_ccache_well_formed_nocet_ite.
  (* bexp *)
  set IHe := bit_blast_exp_ccache_well_formed.
  set IHb := bit_blast_bexp_ccache_well_formed.
  move=> e te m c g m' c' g' cs l.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite bit_blast_bexp_ccache_equation Hfcbt /=.
    case=> _ <- _ _ _. done. 
  - move: e te m c g m' c' g' cs l Hfcbt.
    case.
    + exact: bit_blast_bexp_ccache_well_formed_nocbt_false.
    + exact: bit_blast_bexp_ccache_well_formed_nocbt_true.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_bexp_ccache_well_formed_nocbt_binop.
    + move=> e1; move: e1 (IHb e1).
      exact: bit_blast_bexp_ccache_well_formed_nocbt_lneg.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: bit_blast_bexp_ccache_well_formed_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: bit_blast_bexp_ccache_well_formed_nocbt_disj.
Qed.


(* = mk_env_exp_ccache_well_formed and mk_env_bexp_ccache_well_formed = *)

Lemma mk_env_exp_ccache_well_formed_nocet_var :
  forall (t : SSAVarOrder.t) (m : vm) (c : compcache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (c' : compcache) 
         (E' : env) (g' : generator) (cs : cnf) (ls : word),
    find_cet (QFBV.Evar t) c = None ->
    mk_env_exp_ccache m c s E g (QFBV.Evar t) = (m', c', E', g', cs, ls) ->
    well_formed c -> well_formed c'.
Proof.
  move=> v m c s E g m' c' E' g' cs ls Hfcet. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Evar v) c) => [[cse lse] | ];
    last case Hfv : (SSAVM.find v m);
    last case Hv : (mk_env_var E g (SSAStore.acc v s) v) => [[[Ev gv] csv] lsv];
    case=> _ <- _ _ _ _ Hwfc; 
    (apply well_formed_add_cet_het || apply well_formed_add_cet); done.
Qed.

Lemma mk_env_exp_ccache_well_formed_nocet_const :
  forall (b : bits) (m : vm) (c : compcache) (s : SSAStore.t) 
         (E : env) (g : generator) (m' : vm) (c' : compcache) 
         (E' : env) (g' : generator) (cs : cnf) (ls : word),
    find_cet (QFBV.Econst b) c = None ->
    mk_env_exp_ccache m c s E g (QFBV.Econst b) = (m', c', E', g', cs, ls) ->
    well_formed c -> well_formed c'.
Proof.
  move=> bs m c s E g m' c' E' g' cs ls Hfcet Hmk Hwfc.
  move: Hmk. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Econst bs) c) => [[csop lsop] | ];
    case=> _ <- _ _ _ _; 
    (apply well_formed_add_cet_het || apply well_formed_add_cet); done.
Qed.

Lemma mk_env_exp_ccache_well_formed_nocet_unop :
  forall (op : QFBV.eunop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
        well_formed c -> well_formed c') ->
    forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
           (g : generator) (m' : vm) (c' : compcache) (E' : env) 
           (g' : generator) (cs : cnf) (ls : word),
      find_cet (QFBV.Eunop op e1) c = None ->
      mk_env_exp_ccache m c s E g (QFBV.Eunop op e1) = (m', c', E', g', cs, ls) ->
      well_formed c -> well_formed c'.
Proof.
  move=> op e1 IH1 m c s E g m' c' E' g' cs ls Hfcet Hmk Hwfc.
  move: Hmk. rewrite /= Hfcet.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hwfc) => Hwfc1.
  case Hfhet : (find_het (QFBV.Eunop op e1) c1) => [[csop lsop] | ];
    last case Hop : (mk_env_eunop op E1 g1 ls1) => [[[Eop gop] csop] lsop];
    case=> _ <- _ _ _ _; 
    (apply well_formed_add_cet_het || apply well_formed_add_cet); done.
Qed.

Lemma mk_env_exp_ccache_well_formed_nocet_binop :
  forall (op : QFBV.ebinop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
        well_formed c -> well_formed c') ->
    forall e2 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
          well_formed c -> well_formed c') ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (ls : word),
        find_cet (QFBV.Ebinop op e1 e2) c = None ->
        mk_env_exp_ccache m c s E g (QFBV.Ebinop op e1 e2) = (m', c', E', g', cs, ls) ->
        well_formed c -> well_formed c'.
Proof.
  move=> op e1 IH1 e2 IH2 m c s E g m' c' E' g' cs ls Hfcet Hmk Hwfc.
  move: Hmk. rewrite /= Hfcet.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hwfc1) => Hwfc2.
  case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csop lsop] | ];
    last case Hop : (mk_env_ebinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lsop];
    case=> _ <- _ _ _ _; 
    (apply well_formed_add_cet_het || apply well_formed_add_cet); done.
Qed.

Lemma mk_env_exp_ccache_well_formed_nocet_ite :
  forall b : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g b = (m', c', E', g', cs, l) ->
        well_formed c -> well_formed c') ->
    forall e1 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
          well_formed c -> well_formed c') ->
      forall e2 : QFBV.exp,
        (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
                (g : generator) (m' : vm) (c' : compcache) (E' : env) 
                (g' : generator) (cs : cnf) (ls : word),
            mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
            well_formed c -> well_formed c') ->
        forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
               (g : generator) (m' : vm) (c' : compcache) (E' : env) 
               (g' : generator) (cs : cnf) (ls : word),
          find_cet (QFBV.Eite b e1 e2) c = None ->
          mk_env_exp_ccache m c s E g (QFBV.Eite b e1 e2) = (m', c', E', g', cs, ls) ->
          well_formed c -> well_formed c'.
Proof.
  move=> b IHb e1 IH1 e2 IH2 m c s E g m' c' E' g' cs ls Hfcet Hmk Hwfc.
  move: Hmk. rewrite /= Hfcet.
  case Hb : (mk_env_bexp_ccache m c s E g b) => [[[[[mb cb] Eb] gb] csb] lb].
  case He1 : (mk_env_exp_ccache mb cb s Eb gb e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IHb _ _ _ _ _ _ _ _ _ _ _ Hb Hwfc) => Hwfcb.
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hwfcb) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hwfc1) => Hwfc2.
  case Hfhet : (find_het (QFBV.Eite b e1 e2) c2) => [[csop lsop] | ];
    last case Hop : (mk_env_ite E2 g2 lb ls1 ls2) => [[[Eop gop] csop] lsop];
    case=> _ <- _ _ _ _; 
    (apply well_formed_add_cet_het || apply well_formed_add_cet); done.
Qed.

Lemma mk_env_bexp_ccache_well_formed_nocbt_false :
  forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
         (g : generator) (m' : vm) (c' : compcache) (E' : env) 
         (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Bfalse c = None ->
    mk_env_bexp_ccache m c s E g QFBV.Bfalse = (m', c', E', g', cs, l) ->
    well_formed c -> well_formed c'.
Proof.
  move=> m c s E g m' c' E' g' cs l Hfcbt Hmk Hwfc.
  move: Hmk. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Bfalse) c) => [[csop lop] | ];
    case=> _ <- _ _ _ _; 
    (apply well_formed_add_cbt_hbt || apply well_formed_add_cbt); done.
Qed.

Lemma mk_env_bexp_ccache_well_formed_nocbt_true :
  forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
         (g : generator) (m' : vm) (c' : compcache) (E' : env) 
         (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Btrue c = None ->
    mk_env_bexp_ccache m c s E g QFBV.Btrue = (m', c', E', g', cs, l) ->
    well_formed c -> well_formed c'.
Proof.
  move=> m c s E g m' c' E' g' cs l Hfcbt Hmk Hwfc.
  move: Hmk. rewrite /= Hfcbt.
  case Hfhbt : (find_hbt (QFBV.Btrue) c) => [[csop lop] | ];
    case=> _ <- _ _ _ _; 
    (apply well_formed_add_cbt_hbt || apply well_formed_add_cbt); done.
Qed.

Lemma mk_env_bexp_ccache_well_formed_nocbt_binop :
  forall (op : QFBV.bbinop) (e1 : QFBV.exp),
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (ls : word),
        mk_env_exp_ccache m c s E g e1 = (m', c', E', g', cs, ls) ->
        well_formed c -> well_formed c') ->
    forall e2 : QFBV.exp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (ls : word),
          mk_env_exp_ccache m c s E g e2 = (m', c', E', g', cs, ls) ->
          well_formed c -> well_formed c') ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bbinop op e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bbinop op e1 e2) = (m', c', E', g', cs, l) ->
        well_formed c -> well_formed c'.
Proof.
  move=> op e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt Hmk Hwfc.
  move: Hmk. rewrite /= Hfcbt.
  case He1 : (mk_env_exp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] ls1].
  case He2 : (mk_env_exp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hwfc1) => Hwfc2.
  case Hfhbt : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[csop lop] | ];
    last case Hop : (mk_env_bbinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lop];
    case=> _ <- _ _ _ _; 
    (apply well_formed_add_cbt_hbt || apply well_formed_add_cbt); done.
Qed.

Lemma mk_env_bexp_ccache_well_formed_nocbt_lneg :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        well_formed c -> well_formed c') ->
    forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
           (g : generator) (m' : vm) (c' : compcache) (E' : env) 
           (g' : generator) (cs : cnf) (l : literal),
      find_cbt (QFBV.Blneg e1) c = None ->
      mk_env_bexp_ccache m c s E g (QFBV.Blneg e1) = (m', c', E', g', cs, l) ->
      well_formed c -> well_formed c'.
Proof.
  move=> e1 IH1 m c s E g m' c' E' g' cs l Hfcbt Hmk Hwfc.
  move: Hmk. rewrite /= Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hwfc) => Hwfc1.
  case Hfhbt : (find_hbt (QFBV.Blneg e1) c1) => [[csop lop] | ];
    case=> _ <- _ _ _ _; 
    (apply well_formed_add_cbt_hbt || apply well_formed_add_cbt); done.
Qed.

Lemma mk_env_bexp_ccache_well_formed_nocbt_conj :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        well_formed c -> well_formed c') ->
    forall e2 : QFBV.bexp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (l : literal),
          mk_env_bexp_ccache m c s E g e2 = (m', c', E', g', cs, l) ->
          well_formed c -> well_formed c') ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bconj e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bconj e1 e2) = (m', c', E', g', cs, l) ->
        well_formed c -> well_formed c'.
Proof.
  move=> e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt Hmk Hwfc.
  move: Hmk. rewrite /= Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  case He2 : (mk_env_bexp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hwfc1) => Hwfc2.
  case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csop lop] | ];
    case=> _ <- _ _ _ _; 
    (apply well_formed_add_cbt_hbt || apply well_formed_add_cbt); done.
Qed.

Lemma mk_env_bexp_ccache_well_formed_nocbt_disj :
  forall e1 : QFBV.bexp,
    (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
            (g : generator) (m' : vm) (c' : compcache) (E' : env) 
            (g' : generator) (cs : cnf) (l : literal),
        mk_env_bexp_ccache m c s E g e1 = (m', c', E', g', cs, l) ->
        well_formed c -> well_formed c') ->
    forall e2 : QFBV.bexp,
      (forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
              (g : generator) (m' : vm) (c' : compcache) (E' : env) 
              (g' : generator) (cs : cnf) (l : literal),
          mk_env_bexp_ccache m c s E g e2 = (m', c', E', g', cs, l) ->
          well_formed c -> well_formed c') ->
      forall (m : vm) (c : compcache) (s : SSAStore.t) (E : env) 
             (g : generator) (m' : vm) (c' : compcache) (E' : env) 
             (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bdisj e1 e2) c = None ->
        mk_env_bexp_ccache m c s E g (QFBV.Bdisj e1 e2) = (m', c', E', g', cs, l) ->
        well_formed c -> well_formed c'.
Proof.
  move=> e1 IH1 e2 IH2 m c s E g m' c' E' g' cs l Hfcbt Hmk Hwfc.
  move: Hmk. rewrite /= Hfcbt.
  case He1 : (mk_env_bexp_ccache m c s E g e1) => [[[[[m1 c1] E1] g1] cs1] l1].
  case He2 : (mk_env_bexp_ccache m1 c1 s E1 g1 e2) => [[[[[m2 c2] E2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hwfc1) => Hwfc2.
  case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csop lop] | ];
    case=> _ <- _ _ _ _; 
    (apply well_formed_add_cbt_hbt || apply well_formed_add_cbt); done.
Qed.

Corollary mk_env_exp_ccache_well_formed :
  forall (e : QFBV.exp) m c s E g m' c' E' g' cs ls,
    mk_env_exp_ccache m c s E g e = (m', c', E', g', cs, ls) ->
    CompCache.well_formed c -> CompCache.well_formed c'
  with
    mk_env_bexp_ccache_well_formed :
      forall e m c s E g m' c' E' g' cs l,
        mk_env_bexp_ccache m c s E g e = (m', c', E', g', cs, l) ->
        CompCache.well_formed c -> CompCache.well_formed c'.
Proof.
  (* exp *)
  set IHe := mk_env_exp_ccache_well_formed.
  set IHb := mk_env_bexp_ccache_well_formed.
  move=> e m c s E g m' c' E' g' cs ls.
  case Hfcet: (find_cet e c) => [[cse lse] | ]. 
  - rewrite mk_env_exp_ccache_equation Hfcet /=.
    case=> _ <- _ _ _ _. done. 
  - move: e m c s E g m' c' E' g' cs ls Hfcet.
    case.
    + exact: mk_env_exp_ccache_well_formed_nocet_var.
    + exact: mk_env_exp_ccache_well_formed_nocet_const.
    + move=> op e1; move: op e1 (IHe e1).
      exact: mk_env_exp_ccache_well_formed_nocet_unop.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_well_formed_nocet_binop.
    + move=> b e1 e2; move: b (IHb b) e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_well_formed_nocet_ite.
  (* bexp *)
  set IHe := mk_env_exp_ccache_well_formed.
  set IHb := mk_env_bexp_ccache_well_formed.
  move=> e m c s E g m' c' E' g' cs l.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite mk_env_bexp_ccache_equation Hfcbt /=.
    case=> _ <- _ _ _ _. done. 
  - move: e m c s E g m' c' E' g' cs l Hfcbt.
    case.
    + exact: mk_env_bexp_ccache_well_formed_nocbt_false.
    + exact: mk_env_bexp_ccache_well_formed_nocbt_true.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_bexp_ccache_well_formed_nocbt_binop.
    + move=> e1; move: e1 (IHb e1).
      exact: mk_env_bexp_ccache_well_formed_nocbt_lneg.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_well_formed_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_well_formed_nocbt_disj.
Qed.
