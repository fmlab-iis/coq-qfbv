From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport 
     AdhereConform.
(* From BBCache Require Import Cache BitBlastingCacheDef BitBlastingCachePreserve *)
(*      BitBlastingCacheWF. *)
From newBBCache Require Import CompCache BitBlastingCCacheDef 
     BitBlastingCCachePreserve BitBlastingCCacheWF.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Lemma bit_blast_exp_ccache_bound_cache_nocet_var :
  forall (t : SSAVarOrder.t) (te : SSATE.env) (m : vm) (c : compcache)
         (g : generator) (m' : vm) (c' : compcache) (g' : generator) 
         (cs : cnf) (ls : word),
    find_cet (QFBV.Evar t) c = None ->
    bit_blast_exp_ccache te m c g (QFBV.Evar t) = (m', c', g', cs, ls) ->
    well_formed c -> bound c m -> bound_exp (QFBV.Evar t) m' /\ bound c' m'.
Proof.
  move=> v te m c g m' c' g' cs ls Hfcet. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Evar v) c) => [[cse lse] | ].
  - case=> <- <- _ _ _ Hwfc Hbcm. split; last by rewrite -bound_add_cet.
    exact: (bound_find_het Hbcm Hfhet).
  - case Hfv : (SSAVM.find v m) .
    + case=> <- <- _ _ _ Hwfc Hbcm. 
      move : (SSAVM.Lemmas.find_some_mem Hfv) => Hmem.
      split; first done.
      rewrite -bound_add_cet; by apply bound_add_het.
    + dcase (bit_blast_var te g v) => [[[gv csv] lsv] Hbbv] .
      case => <- <- _ _ _  Hwfc Hbcm.
      have Hmem : SSAVM.mem v (SSAVM.add v lsv m) by apply SSAVM.Lemmas.mem_add_eq .
      split; first done. 
      rewrite -bound_add_cet; apply bound_add_het; try done.
      apply (@vm_preserve_bound m); try done; by apply vm_preserve_add_diag.
Qed.

Lemma bit_blast_exp_ccache_bound_cache_nocet_const :
  forall (b : bits) (te : SSATE.env) (m : vm) (c : compcache) 
         (g : generator) (m' : vm) (c' : compcache) (g' : generator) 
         (cs : cnf) (ls : word),
    find_cet (QFBV.Econst b) c = None ->
    bit_blast_exp_ccache te m c g (QFBV.Econst b) = (m', c', g', cs, ls) ->
    well_formed c -> bound c m -> bound_exp (QFBV.Econst b) m' /\ bound c' m'.
Proof.
  move=> bs te m c g m' c' g' cs ls Hfcet Hbb Hwfc Hbcm. 
  move: Hbb. rewrite /= Hfcet. 
  case Hfhet : (find_het (QFBV.Econst bs) c) => [[csop lsop] | ];
    case=> <- <- _ _ _; split; try done;
    rewrite -bound_add_cet; try apply bound_add_het; done.
Qed.

Lemma bit_blast_exp_ccache_bound_cache_nocet_unop :
  forall (op : QFBV.eunop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) ->
        well_formed c -> bound c m -> bound_exp e1 m' /\ bound c' m') ->
    forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
           (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
      find_cet (QFBV.Eunop op e1) c = None ->
      bit_blast_exp_ccache te m c g (QFBV.Eunop op e1) = (m', c', g', cs, ls) ->
      well_formed c -> bound c m -> bound_exp (QFBV.Eunop op e1) m' /\ bound c' m'.
Proof.
  move=> op e1 IH1 te m c g m' c' g' cs ls Hfcet Hbb Hwfc Hbcm. 
  move: Hbb. rewrite /= Hfcet. 
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwfc Hbcm) => [Hbe1m1 Hbc1m1].
  case Hfhet : (find_het (QFBV.Eunop op e1) c1) => [[csop lsop] | ];
    last case Hop : (bit_blast_eunop op g1 ls1) => [[gop csop] lsop];
    case=> <- <- _ _ _; split; try done;
    rewrite -bound_add_cet; try apply bound_add_het; done.
Qed.

Lemma bit_blast_exp_ccache_bound_cache_nocet_binop :
  forall (op : QFBV.ebinop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) ->
        well_formed c -> bound c m -> bound_exp e1 m' /\ bound c' m') ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
          bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls) ->
          well_formed c -> bound c m -> bound_exp e2 m' /\ bound c' m') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        find_cet (QFBV.Ebinop op e1 e2) c = None ->
        bit_blast_exp_ccache te m c g (QFBV.Ebinop op e1 e2) = (m', c', g', cs, ls) ->
        well_formed c -> bound c m -> 
        bound_exp (QFBV.Ebinop op e1 e2) m' /\ bound c' m'.
Proof.
  move=> op e1 IH1 e2 IH2 te m c g m' c' g' cs ls Hfcet Hbb Hwfc Hbcm. 
  move: Hbb. rewrite /= Hfcet. 
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwfc Hbcm) => [Hbe1m1 Hbc1m1].
  move: (bit_blast_exp_ccache_preserve He2) => Hpm1m2.
  move: (vm_preserve_bound_exp Hbe1m1 Hpm1m2) => {Hbe1m1} Hbe1m2.
  move: (bit_blast_exp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hwfc1 Hbc1m1) => [Hbe2m2 Hbc2m2].
  have Hbem2 : bound_exp e1 m2 && bound_exp e2 m2 by rewrite Hbe1m2 Hbe2m2.
  case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csop lsop] | ];
    last case Hop : (bit_blast_ebinop op g2 ls1 ls2) => [[gop csop] lsop];
    case=> <- <- _ _ _; split; try done;
    rewrite -bound_add_cet; try apply bound_add_het; done.
Qed.

Lemma bit_blast_exp_ccache_bound_cache_nocet_ite :
  forall b : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        bit_blast_bexp_ccache te m c g b = (m', c', g', cs, l) ->
        well_formed c -> bound c m -> bound_bexp b m' /\ bound c' m') ->
    forall e1 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
          bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) ->
          well_formed c -> bound c m -> bound_exp e1 m' /\ bound c' m') ->
      forall e2 : QFBV.exp,
        (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
                (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
            bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls) ->
            well_formed c -> bound c m -> bound_exp e2 m' /\ bound c' m') ->
        forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
               (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
          find_cet (QFBV.Eite b e1 e2) c = None ->
          bit_blast_exp_ccache te m c g (QFBV.Eite b e1 e2) = (m', c', g', cs, ls) ->
          well_formed c -> bound c m -> 
          bound_exp (QFBV.Eite b e1 e2) m' /\ bound c' m'.
Proof.
  move=> b IHb e1 IH1 e2 IH2 te m c g m' c' g' cs ls Hfcet Hbb Hwfc Hbcm. 
  move: Hbb. rewrite /= Hfcet. 
  case Hb : (bit_blast_bexp_ccache te m c g b) => [[[[mb cb] gb] csb] lb].
  case He1 : (bit_blast_exp_ccache te mb cb gb e1) => [[[[m1 c1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
  move: (IHb _ _ _ _ _ _ _ _ _ Hb Hwfc Hbcm) => [Hbbmb Hbcbmb].
  move: (bit_blast_exp_ccache_preserve He1) => Hpmbm1.
  move: (vm_preserve_bound_bexp Hbbmb Hpmbm1) => {Hbbmb} Hbbm1.
  move: (bit_blast_exp_ccache_preserve He2) => Hpm1m2.
  move: (vm_preserve_bound_bexp Hbbm1 Hpm1m2) => {Hbbm1} Hbbm2.
  move: (bit_blast_bexp_ccache_well_formed Hb Hwfc) => Hwfcb.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwfcb Hbcbmb) => [Hbe1m1 Hbc1m1].
  move: (vm_preserve_bound_exp Hbe1m1 Hpm1m2) => {Hbe1m1} Hbe1m2.
  move: (bit_blast_exp_ccache_well_formed He1 Hwfcb) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hwfc1 Hbc1m1) => [Hbe2m2 Hbc2m2].
  have Hbem2 : bound_bexp b m2 && bound_exp e1 m2 && bound_exp e2 m2 
    by rewrite Hbbm2 Hbe1m2 Hbe2m2.
  case Hfhet : (find_het (QFBV.Eite b e1 e2) c2) => [[csop lsop] | ];
    last case Hop : (bit_blast_ite g2 lb ls1 ls2) => [[gop csop] lsop];
    case=> <- <- _ _ _; split; try done;
    rewrite -bound_add_cet; try apply bound_add_het; done.
Qed.

Lemma bit_blast_bexp_ccache_bound_cache_nocbt_false :
  forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
         (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Bfalse c = None ->
    bit_blast_bexp_ccache te m c g QFBV.Bfalse = (m', c', g', cs, l) ->
    well_formed c -> bound c m -> bound_bexp QFBV.Bfalse m' /\ bound c' m'.
Proof.
  move=> te m c g m' c' g' cs l Hfcbt Hbb Hwfc Hbcm. 
  move: Hbb. rewrite /= Hfcbt. 
  case Hfhbt : (find_hbt (QFBV.Bfalse) c) => [[csop lop] | ];
    case=> <- <- _ _ _; split; try done;
    rewrite -bound_add_cbt; try apply bound_add_hbt; done.
Qed.

Lemma bit_blast_bexp_ccache_bound_cache_nocbt_true :
  forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
         (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
    find_cbt QFBV.Btrue c = None ->
    bit_blast_bexp_ccache te m c g QFBV.Btrue = (m', c', g', cs, l) ->
    well_formed c -> bound c m -> bound_bexp QFBV.Btrue m' /\ bound c' m'.
Proof.
  move=> te m c g m' c' g' cs l Hfcbt Hbb Hwfc Hbcm. 
  move: Hbb. rewrite /= Hfcbt. 
  case Hfhbt : (find_hbt (QFBV.Btrue) c) => [[csop lop] | ];
    case=> <- <- _ _ _; split; try done;
    rewrite -bound_add_cbt; try apply bound_add_hbt; done.
Qed.

Lemma bit_blast_bexp_ccache_bound_cache_nocbt_binop :
  forall (op : QFBV.bbinop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) ->
        well_formed c -> bound c m -> bound_exp e1 m' /\ bound c' m') ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
          bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls) ->
          well_formed c -> bound c m -> bound_exp e2 m' /\ bound c' m') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bbinop op e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bbinop op e1 e2) = (m', c', g', cs, l) ->
        well_formed c -> bound c m -> 
        bound_bexp (QFBV.Bbinop op e1 e2) m' /\ bound c' m'.
Proof.
  move=> op e1 IH1 e2 IH2 te m c g m' c' g' cs l Hfcbt Hbb Hwfc Hbcm. 
  move: Hbb. rewrite /= Hfcbt. 
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwfc Hbcm) => [Hbe1m1 Hbc1m1].
  move: (bit_blast_exp_ccache_preserve He2) => Hpm1m2.
  move: (vm_preserve_bound_exp Hbe1m1 Hpm1m2) => {Hbe1m1} Hbe1m2.
  move: (bit_blast_exp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hwfc1 Hbc1m1) => [Hbe2m2 Hbc2m2].
  have Hbem2 : bound_exp e1 m2 && bound_exp e2 m2 by rewrite Hbe1m2 Hbe2m2.
  case Hfhbt : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[csop lop] | ];
    last case Hop : (bit_blast_bbinop op g2 ls1 ls2) => [[gop csop] lop];
    case=> <- <- _ _ _; split; try done;
    rewrite -bound_add_cbt; try apply bound_add_hbt; done.
Qed.

Lemma bit_blast_bexp_ccache_bound_cache_nocbt_lneg :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l) ->
        well_formed c -> bound c m -> bound_bexp e1 m' /\ bound c' m') ->
    forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
           (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
      find_cbt (QFBV.Blneg e1) c = None ->
      bit_blast_bexp_ccache te m c g (QFBV.Blneg e1) = (m', c', g', cs, l) ->
      well_formed c -> bound c m -> bound_bexp (QFBV.Blneg e1) m' /\ bound c' m'.
Proof.
  move=> e1 IH1 te m c g m' c' g' cs l Hfcbt Hbb Hwfc Hbcm. 
  move: Hbb. rewrite /= Hfcbt. 
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwfc Hbcm) => [Hbe1m1 Hbc1m1].
  case Hfhbt : (find_hbt (QFBV.Blneg e1) c1) => [[csop lop] | ];
    case=> <- <- _ _ _; split; try done;
    rewrite -bound_add_cbt; try apply bound_add_hbt; done.
Qed.

Lemma bit_blast_bexp_ccache_bound_cache_nocbt_conj :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l) ->
        well_formed c -> bound c m -> bound_bexp e1 m' /\ bound c' m') ->
    forall e2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
          bit_blast_bexp_ccache te m c g e2 = (m', c', g', cs, l) ->
          well_formed c -> bound c m -> bound_bexp e2 m' /\ bound c' m') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bconj e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bconj e1 e2) = (m', c', g', cs, l) ->
        well_formed c -> bound c m -> 
        bound_bexp (QFBV.Bconj e1 e2) m' /\ bound c' m'.
Proof.
  move=> e1 IH1 e2 IH2 te m c g m' c' g' cs l Hfcbt Hbb Hwfc Hbcm. 
  move: Hbb. rewrite /= Hfcbt. 
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwfc Hbcm) => [Hbe1m1 Hbc1m1].
  move: (bit_blast_bexp_ccache_preserve He2) => Hpm1m2.
  move: (vm_preserve_bound_bexp Hbe1m1 Hpm1m2) => {Hbe1m1} Hbe1m2.
  move: (bit_blast_bexp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hwfc1 Hbc1m1) => [Hbe2m2 Hbc2m2].
  have Hbem2 : bound_bexp e1 m2 && bound_bexp e2 m2 by rewrite Hbe1m2 Hbe2m2.
  case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csop lop] | ];
    case=> <- <- _ _ _; split; try done;
    rewrite -bound_add_cbt; try apply bound_add_hbt; done.
Qed.

Lemma bit_blast_bexp_ccache_bound_cache_nocbt_disj :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l) ->
        well_formed c -> bound c m -> bound_bexp e1 m' /\ bound c' m') ->
    forall e2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
          bit_blast_bexp_ccache te m c g e2 = (m', c', g', cs, l) ->
          well_formed c -> bound c m -> bound_bexp e2 m' /\ bound c' m') ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        find_cbt (QFBV.Bdisj e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bdisj e1 e2) = (m', c', g', cs, l) ->
        well_formed c -> bound c m -> 
        bound_bexp (QFBV.Bdisj e1 e2) m' /\ bound c' m'.
Proof.
  move=> e1 IH1 e2 IH2 te m c g m' c' g' cs l Hfcbt Hbb Hwfc Hbcm. 
  move: Hbb. rewrite /= Hfcbt. 
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hwfc Hbcm) => [Hbe1m1 Hbc1m1].
  move: (bit_blast_bexp_ccache_preserve He2) => Hpm1m2.
  move: (vm_preserve_bound_bexp Hbe1m1 Hpm1m2) => {Hbe1m1} Hbe1m2.
  move: (bit_blast_bexp_ccache_well_formed He1 Hwfc) => Hwfc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hwfc1 Hbc1m1) => [Hbe2m2 Hbc2m2].
  have Hbem2 : bound_bexp e1 m2 && bound_bexp e2 m2 by rewrite Hbe1m2 Hbe2m2.
  case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csop lop] | ];
    case=> <- <- _ _ _; split; try done;
    rewrite -bound_add_cbt; try apply bound_add_hbt; done.
Qed.


Corollary bit_blast_exp_ccache_bound_cache :
  forall e te m c g m' c' g' cs ls,
    bit_blast_exp_ccache te m c g e = (m', c', g', cs, ls) ->
    CompCache.well_formed c -> CompCache.bound c m ->
    AdhereConform.bound_exp e m' /\ CompCache.bound c' m'
with
bit_blast_bexp_ccache_bound_cache :
  forall e te m c g m' c' g' cs l,
    bit_blast_bexp_ccache te m c g e = (m', c', g', cs, l) ->
    CompCache.well_formed c -> CompCache.bound c m ->
    AdhereConform.bound_bexp e m' /\ CompCache.bound c' m' .
Proof.
  (* exp *)
  set IHe := bit_blast_exp_ccache_bound_cache.
  set IHb := bit_blast_bexp_ccache_bound_cache.
  move=> e te m c g m' c' g' cs ls.
  case Hfcet: (find_cet e c) => [[cse lse] | ]. 
  - rewrite bit_blast_exp_ccache_equation Hfcet /=.
    case=> <- <- _ _ _ Hwfc Hbcm. split; last done.
    move: (CompCache.bound_well_formed_bound_ct Hbcm Hwfc) => Hbctcm.
    exact: (bound_ct_find_cet Hbctcm Hfcet).
  - move: e te m c g m' c' g' cs ls Hfcet.
    case.
    + exact: bit_blast_exp_ccache_bound_cache_nocet_var.
    + exact: bit_blast_exp_ccache_bound_cache_nocet_const.
    + move=> op e1; move: op e1 (IHe e1).
      exact: bit_blast_exp_ccache_bound_cache_nocet_unop.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_exp_ccache_bound_cache_nocet_binop.
    + move=> b e1 e2; move: b (IHb b) e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_exp_ccache_bound_cache_nocet_ite.
  (* bexp *)
  set IHe := bit_blast_exp_ccache_bound_cache.
  set IHb := bit_blast_bexp_ccache_bound_cache.
  move=> e te m c g m' c' g' cs l.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite bit_blast_bexp_ccache_equation Hfcbt /=.
    case=> <- <- _ _ _ Hwfc Hbcm. split; last done.
    move: (CompCache.bound_well_formed_bound_ct Hbcm Hwfc) => Hbctcm.
    exact: (bound_ct_find_cbt Hbctcm Hfcbt).
  - move: e te m c g m' c' g' cs l Hfcbt.
    case.
    + exact: bit_blast_bexp_ccache_bound_cache_nocbt_false.
    + exact: bit_blast_bexp_ccache_bound_cache_nocbt_true.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_bexp_ccache_bound_cache_nocbt_binop.
    + move=> e1; move: e1 (IHb e1).
      exact: bit_blast_bexp_ccache_bound_cache_nocbt_lneg.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: bit_blast_bexp_ccache_bound_cache_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: bit_blast_bexp_ccache_bound_cache_nocbt_disj.
Qed.


Corollary bit_blast_exp_ccache_bound :
  forall e te m c g m' c' g' cs ls,
    bit_blast_exp_ccache te m c g e = (m', c', g', cs, ls) ->
    CompCache.well_formed c -> CompCache.bound c m ->
    AdhereConform.bound_exp e m'.
Proof.
  move=> e te m c g m' c' g' cs ls Hbb Hwfc Hbcm.
  move: (bit_blast_exp_ccache_bound_cache Hbb Hwfc Hbcm) => [Hbe _].
  done.
Qed.

Corollary bit_blast_bexp_ccache_bound :
  forall e te m c g m' c' g' cs l,
    bit_blast_bexp_ccache te m c g e = (m', c', g', cs, l) ->
    CompCache.well_formed c -> CompCache.bound c m ->
    AdhereConform.bound_bexp e m'.
Proof.
  move=> e te m c g m' c' g' cs l Hbb Hwfc Hbcm.
  move: (bit_blast_bexp_ccache_bound_cache Hbb Hwfc Hbcm) => [Hbe _].
  done.
Qed.
