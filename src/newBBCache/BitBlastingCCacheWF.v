From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
(* From BBCache Require Import Cache BitBlastingCacheDef. *)
From newBBCache Require Import CompCache BitBlastingCCacheDef.

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
    last case Hop : (bit_blast_conj g2 l1 l2) => [[gop csop] lop];
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
    last case Hop : (bit_blast_disj g2 l1 l2) => [[gop csop] lop];
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
    + admit.
    + admit.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_exp_ccache_well_formed_nocet_binop.
    + admit.
  (* bexp *)
  set IHe := bit_blast_exp_ccache_well_formed.
  set IHb := bit_blast_bexp_ccache_well_formed.
  move=> e te m c g m' c' g' cs l.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite bit_blast_bexp_ccache_equation Hfcbt /=.
    case=> _ <- _ _ _. done. 
  - move: e te m c g m' c' g' cs l Hfcbt.
    case.
    + admit.
    + admit.
    + admit.
    + admit.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: bit_blast_bexp_ccache_well_formed_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: bit_blast_bexp_ccache_well_formed_nocbt_disj.
Admitted.


(* = mk_env_exp_ccache_well_formed and mk_env_bexp_ccache_well_formed = *)

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
Admitted.


