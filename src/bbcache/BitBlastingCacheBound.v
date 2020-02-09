From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport 
     AdhereConform.
From BBCache Require Import Cache BitBlastingCacheDef BitBlastingCachePreserve
     BitBlastingCacheWF.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Lemma bit_blast_exp_cache_bound_nocache_var :
  forall (t : SSAVarOrder.t) (te : SSATE.env) (m : SSAVM.t word) 
         (m' : vm) (ca ca' : cache) (g g' : generator) (cs : cnf) (lrs : word),
    find_cet (QFBV.Evar t) ca = None ->
    find_het (QFBV.Evar t) ca = None ->
    bit_blast_exp_cache te m ca g (QFBV.Evar t) = (m', ca', g', cs, lrs) ->
    well_formed ca -> bound ca m -> bound_exp (QFBV.Evar t) m' /\ bound ca' m'.
Proof.
  move=> v te m m' ca ca' g g' cs lrs Hfcet Hfhet /=.
  rewrite Hfcet Hfhet.
  case Hf : (SSAVM.find v m) .
  - case => <- <- _ _ _ Hwfca Hbcam. 
    move : (SSAVM.Lemmas.find_some_mem Hf) => Hmem.
    split; first done.
    apply bound_add_het. split; last done.
    by rewrite -bound_add_cet.
  - dcase (bit_blast_var te g v) => [[[gv csv] lsv] Hbbv] .
    case => <- <- _ _ _  Hwfca Hbcam.
    split; first exact: SSAVM.Lemmas.mem_add_eq .
    apply bound_add_het. split; last exact: SSAVM.Lemmas.mem_add_eq .
    rewrite -bound_add_cet. exact: (bound_add_find_none lsv Hbcam Hf).
Qed.

Lemma bit_blast_exp_cache_bound_nocache_const :
  forall (b : bits) (te : SSATE.env) (m : SSAVM.t word) 
         (m' : vm) (ca ca' : cache) (g g' : generator) (cs : cnf) (lrs : word),
    find_cet (QFBV.Econst b) ca = None ->
    find_het (QFBV.Econst b) ca = None ->
    bit_blast_exp_cache te m ca g (QFBV.Econst b) = (m', ca', g', cs, lrs) ->
    well_formed ca -> bound ca m -> bound_exp (QFBV.Econst b) m' /\ bound ca' m'.
Proof.
  move=> v te m m' ca ca' g g' cs lrs Hfcet Hfhet /=.
  rewrite Hfcet Hfhet. case=> <- <- _ _ _ Hwfca Hbcam.
  split; first done.
  apply bound_add_het. split; last done.
  by rewrite -bound_add_cet.
Qed.

Lemma bit_blast_exp_cache_bound_nocache_extract :
  forall (i j : nat) (e : QFBV.exp),
    (forall (te : SSATE.env) (m : SSAVM.t word) (m' : vm) 
            (ca ca' : cache) (g g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp_cache te m ca g e = (m', ca', g', cs, lrs) ->
        well_formed ca -> bound ca m -> bound_exp e m' /\ bound ca' m') ->
    forall (te : SSATE.env) (m : SSAVM.t word) (m' : vm) (ca ca' : cache)
           (g g' : generator) (cs : cnf) (lrs : word),
      find_cet (QFBV.Eunop (QFBV.Uextr i j) e) ca = None ->
      find_het (QFBV.Eunop (QFBV.Uextr i j) e) ca = None ->
      bit_blast_exp_cache te m ca g (QFBV.Eunop (QFBV.Uextr i j) e) =
      (m', ca', g', cs, lrs) ->
      well_formed ca ->
      bound ca m -> bound_exp (QFBV.Eunop (QFBV.Uextr i j) e) m' /\ bound ca' m'.
Proof.
(* case => <- _ _ _; exact : (IHe _ _ _ _ _ _ _ Hbbe) . *)
Admitted.

Lemma bit_blast_exp_cache_bound_nocache_and :
  forall e1 : QFBV.exp,
    (forall (te : SSATE.env) (m : SSAVM.t word) (m' : vm) 
            (ca ca' : cache) (g g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp_cache te m ca g e1 = (m', ca', g', cs, lrs) ->
        well_formed ca -> bound ca m -> bound_exp e1 m' /\ bound ca' m') ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : SSAVM.t word) (m' : vm) 
              (ca ca' : cache) (g g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp_cache te m ca g e2 = (m', ca', g', cs, lrs) ->
          well_formed ca -> bound ca m -> bound_exp e2 m' /\ bound ca' m') ->
      forall (te : SSATE.env) (m : SSAVM.t word) (m' : vm) (ca ca' : cache)
             (g g' : generator) (cs : cnf) (lrs : word),
        find_cet (QFBV.Ebinop QFBV.Band e1 e2) ca = None ->
        find_het (QFBV.Ebinop QFBV.Band e1 e2) ca = None ->
        bit_blast_exp_cache te m ca g (QFBV.Ebinop QFBV.Band e1 e2) =
        (m', ca', g', cs, lrs) ->
        well_formed ca ->
        bound ca m -> bound_exp (QFBV.Ebinop QFBV.Band e1 e2) m' /\ bound ca' m'.
Proof.
  move=> e1 IH1 e2 IH2 te m m' ca ca' g g' cs lrs Hfcet Hfhet /=.
  rewrite Hfcet Hfhet.
  dcase (bit_blast_exp_cache te m ca g e1) => [[[[[m1 ca1] g1] cs1] ls1] Hbbe1].
  dcase (bit_blast_exp_cache te m1 ca1 g1 e2) => [[[[[m2 ca2] g2] cs2] ls2] Hbbe2].
  move : (bit_blast_exp_cache_preserve Hbbe1)
           (bit_blast_exp_cache_preserve Hbbe2) => Hmm1 Hm1m2 .
  dcase (bit_blast_and g2 ls1 ls2) => [[[gr csr] lsr] Hbbr].
  case => <- <- _ _ _ Hwfca Hbcam.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hbbe1 Hwfca Hbcam) => [Hbe1m1 Hbca1m1].
  move: (bit_blast_exp_cache_well_formed Hbbe1 Hwfca) => Hwfca1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hbbe2 Hwfca1 Hbca1m1) => [Hbe2m2 Hbca2m2].
  have Hbnde : bound_exp e1 m2 && bound_exp e2 m2
    by rewrite (vm_preserve_bound_exp Hbe1m1 Hm1m2) Hbe2m2.
  split; first done.
  apply bound_add_het. split; last done.
  by rewrite -bound_add_cet. 
Qed.

Lemma bit_blast_bexp_cache_bound_nocache_conj :
  forall b1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : SSAVM.t word) (m' : vm) 
            (ca ca' : cache) (g g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp_cache te m ca g b1 = (m', ca', g', cs, lr) ->
        well_formed ca -> bound ca m -> bound_bexp b1 m' /\ bound ca' m') ->
    forall b2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : SSAVM.t word) (m' : vm) 
              (ca ca' : cache) (g g' : generator) (cs : cnf) (lr : literal),
          bit_blast_bexp_cache te m ca g b2 = (m', ca', g', cs, lr) ->
          well_formed ca -> bound ca m -> bound_bexp b2 m' /\ bound ca' m') ->
      forall (te : SSATE.env) (m : SSAVM.t word) (m' : vm) (ca ca' : cache)
             (g g' : generator) (cs : cnf) (lr : literal),
        find_cbt (QFBV.Bconj b1 b2) ca = None ->
        find_hbt (QFBV.Bconj b1 b2) ca = None ->
        bit_blast_bexp_cache te m ca g (QFBV.Bconj b1 b2) = (m', ca', g', cs, lr) ->
        well_formed ca -> bound ca m -> 
        bound_bexp (QFBV.Bconj b1 b2) m' /\ bound ca' m'.
Proof.
  move=> e1 IH1 e2 IH2 te m m' ca ca' g g' cs lr Hfcbt Hfhbt /=.
  rewrite Hfcbt Hfhbt.
  dcase (bit_blast_bexp_cache te m ca g e1) => [[[[[m1 ca1] g1] cs1] l1] Hbbe1].
  dcase (bit_blast_bexp_cache te m1 ca1 g1 e2) => [[[[[m2 ca2] g2] cs2] l2] Hbbe2].
  move : (bit_blast_bexp_cache_preserve Hbbe1)
           (bit_blast_bexp_cache_preserve Hbbe2) => Hmm1 Hm1m2 .
  (* dcase (bit_blast_and g2 ls1 ls2) => [[[gr csr] lsr] Hbbr]. *)
  case => <- <- _ _ _ Hwfca Hbcam.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hbbe1 Hwfca Hbcam) => [Hbe1m1 Hbca1m1].
  move: (bit_blast_bexp_cache_well_formed Hbbe1 Hwfca) => Hwfca1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hbbe2 Hwfca1 Hbca1m1) => [Hbe2m2 Hbca2m2].
  have Hbnde : bound_bexp e1 m2 && bound_bexp e2 m2
    by rewrite (vm_preserve_bound_bexp Hbe1m1 Hm1m2) Hbe2m2.
  split; first done.
  apply bound_add_hbt. split; last done.
  by rewrite -bound_add_cbt. 
Qed.


Corollary bit_blast_exp_cache_bound_cache :
  forall e te m m' ca ca' g g' cs lrs,
    bit_blast_exp_cache te m ca g e = (m', ca', g', cs, lrs) ->
    Cache.well_formed ca -> Cache.bound ca m ->
    AdhereConform.bound_exp e m' /\ Cache.bound ca' m'
with
bit_blast_bexp_cache_bound_cache :
  forall e te m m' ca ca' g g' cs lr,
    bit_blast_bexp_cache te m ca g e = (m', ca', g', cs, lr) ->
    Cache.well_formed ca -> Cache.bound ca m ->
    AdhereConform.bound_bexp e m' /\ Cache.bound ca' m' .
Proof .
  (* bit_blast_exp_cache_bound_cache *)
  move=> e te m m' ca ca' g g' cs lrs.
  case Hfcet: (find_cet e ca) => [ls|]. 
  - rewrite bit_blast_exp_cache_equation Hfcet /=.
    case=> <- <- _ _ _ Hwfca Hbcam. split; last done.
    move: (Cache.bound_well_formed_bound_ct Hbcam Hwfca) => [Hct _].
    by apply (Hct _ _ Hfcet).
  - case Hfhet: (find_het e ca) => [[csh lsh]|].
    + rewrite bit_blast_exp_cache_equation Hfcet Hfhet /=. 
      case=> <- <- _ _ _ Hwfca Hbcam.
      split; last by rewrite -bound_add_cet.
      move: Hbcam => [Hht _]. by apply (Hht _ _ _ Hfhet).
    + move: e te m m' ca ca' g g' cs lrs Hfcet Hfhet.
      case.
      * exact: bit_blast_exp_cache_bound_nocache_var.
      * exact: bit_blast_exp_cache_bound_nocache_const.
      * elim => [e | e | i j e | n e | n e | n e | n e ];
                  move: e (bit_blast_exp_cache_bound_cache e).
        -- admit.
(* dcase (bit_blast_not g1 ls1) => [[[gr csr] lsr] Hbbr]; *)
(*         case => <- _ _ _; *)
(*         exact : (IHe _ _ _ _ _ _ _ Hbbe) . *)
        -- admit. (* dcase (bit_blast_neg g1 ls1) => [[[gr csr] lsr] Hbbr]; *)
        (* case => <- _ _ _; *)
        (* exact : (IHe _ _ _ _ _ _ _ Hbbe) . *)
        -- exact: bit_blast_exp_cache_bound_nocache_extract. 
        -- admit. (* case => <- _ _ _; exact : (IHe _ _ _ _ _ _ _ Hbbe) . *)
        -- admit. (* case => <- _ _ _; exact : (IHe _ _ _ _ _ _ _ Hbbe) . *)
        -- admit. (* case => <- _ _ _; exact : (IHe _ _ _ _ _ _ _ Hbbe) . *)
        -- admit.  (* case => <- _ _ _; exact : (IHe _ _ _ _ _ _ _ Hbbe) . *)
      * elim => e1 e2;
        move: e1 (bit_blast_exp_cache_bound_cache e1)
                 e2 (bit_blast_exp_cache_bound_cache e2).
        -- exact: bit_blast_exp_cache_bound_nocache_and.
        -- admit. (* dcase (bit_blast_or g2 ls1 ls2) => [[[gr csr] lsr] Hbbr]; *)
                  (*                               case => <- _ _ _; *)
                  (*                                         rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
                  (*                                                 (IH1 _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (*  dcase (bit_blast_xor g2 ls1 ls2) => [[[gr csr] lsr] Hbbr]; *)
      (* case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (IH1 _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (*  dcase (bit_blast_add g2 ls1 ls2) => [[[gr csr] lsr] Hbbr]; *)
      (* case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (IH1 _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (* dcase (bit_blast_sub g2 ls1 ls2) => [[[gr csr] lsr] Hbbr]; *)
      (* case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (IH1 _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (* dcase (bit_blast_mul g2 ls1 ls2) => [[[gr csr] lsr] Hbbr]; *)
      (* case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (IH1 _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (*  case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (IH1 _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (* case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (IH1 _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (* case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (IH1 _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (*  dcase (bit_blast_shl g2 ls1 ls2) => [[[gr csr] lsr] Hbbr]; *)
      (* case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (IH1 _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (*  dcase (bit_blast_lshr g2 ls1 ls2) => [[[gr csr] lsr] Hbbr]; *)
      (* case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (IH1 _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (*  dcase (bit_blast_ashr g2 ls1 ls2) => [[[gr csr] lsr] Hbbr]; *)
      (* case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (IH1 _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (* case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (IH1 _ _ _ _ _ _ _ Hbbe1) // . *)
      * move => c e1 e2.
        move: c (bit_blast_bexp_cache_bound_cache c)
                e1 (bit_blast_exp_cache_bound_cache e1)
                e2 (bit_blast_exp_cache_bound_cache e2).
        admit.
    (*     dcase (bit_blast_bexp te m g c) => [[[[mc gc] csc] lc] Hbbc] . *)
    (* dcase (bit_blast_exp te mc gc e0) => [[[[m1 g1] cs1] ls1] Hbb0] . *)
    (* dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hbb1] . *)
    (* dcase (bit_blast_ite g2 lc ls1 ls2) => [[[gr csr] lsr] Hbbr] . *)
    (* case => <- _ _ _ . *)
    (* move : (bit_blast_exp_preserve Hbb0) *)
    (*        (bit_blast_exp_preserve Hbb1) => Hmcm1 Hm1m2 . *)
    (* move : (vm_preserve_trans Hmcm1 Hm1m2) => Hmcm2 . *)
    (* rewrite (vm_preserve_bound_bexp (bit_blast_bound_bexp c _ _ _ _ _ _ _ Hbbc) Hmcm2) *)
    (*         (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbb0) Hm1m2) *)
    (*         (IH1 _ _ _ _ _ _ _ Hbb1) // . *)
  (* bit_blast_bexp_cache_bound_cache *)
  move=> e te m m' ca ca' g g' cs lr.
  case Hfcbt: (find_cbt e ca) => [l|]. 
  - rewrite bit_blast_bexp_cache_equation Hfcbt /=.
    case=> <- <- _ _ _ Hwfca Hbcam. split; last done.
    move: (Cache.bound_well_formed_bound_ct Hbcam Hwfca) => [_ Hct].
    by apply (Hct _ _ Hfcbt).
  - case Hfhbt: (find_hbt e ca) => [[csh lh]|].
    + rewrite bit_blast_bexp_cache_equation Hfcbt Hfhbt /=. 
      case=> <- <- _ _ _ Hwfca Hbcam.
      split; last by rewrite -bound_add_cbt.
      move: Hbcam => [_ Hht]. by apply (Hht _ _ _ Hfhbt).
    + move: e te m m' ca ca' g g' cs lr Hfcbt Hfhbt.
      case.
      * admit.  (* done . *)
      * admit.  (* done . *)
      * elim => e1 e2;
        move: e1 (bit_blast_exp_cache_bound_cache e1)
                 e2 (bit_blast_exp_cache_bound_cache e2).
        -- admit.  
(*       dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] ls1] Hbbe0]; *)
(*       dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hbbe1]; *)
(*       move : (bit_blast_exp_preserve Hbbe1) => Hm1m2 . *)

(* dcase (bit_blast_eq g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _; *)
(*       rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
(*               (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (* dcase (bit_blast_ult g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (* dcase (bit_blast_ule g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (* dcase (bit_blast_ugt g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (*  dcase (bit_blast_uge g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (*  dcase (bit_blast_slt g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (*  dcase (bit_blast_sle g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (*  dcase (bit_blast_sgt g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (*  dcase (bit_blast_sge g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (*  dcase (bit_blast_uaddo g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (*  dcase (bit_blast_usubo g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (*  dcase (bit_blast_umulo g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (*  dcase (bit_blast_saddo g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (* dcase (bit_blast_ssubo g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // . *)
        -- admit. (*  dcase (bit_blast_smulo g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _; *)
      (* rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2) *)
      (*         (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // . *)
      * admit. (*  move => c IHc te m m' g g' cs' lrs' . *)
    (* dcase (bit_blast_bexp te m g c) => [[[[m1 g1] cs1] l1] Hbbc] . *)
    (* case => <- _ _ _ ; rewrite (IHc _ _ _ _ _ _ _ Hbbc) // . *)
      * move => b1 b2;
        move: b1 (bit_blast_bexp_cache_bound_cache b1)
                 b2 (bit_blast_bexp_cache_bound_cache b2).
        exact: bit_blast_bexp_cache_bound_nocache_conj.
      * admit. (*  move => b0 IH0 b1 IH1 te m m' g g' cs' lrs' . *)
    (* dcase (bit_blast_bexp te m g b0) => [[[[m1 g1] cs1] l1] Hbb0] . *)
    (* dcase (bit_blast_bexp te m1 g1 b1) => [[[[m2 g2] cs2] l2] Hbb1] . *)
    (* case => <- _ _ _ . *)
    (* move : (bit_blast_bexp_preserve Hbb1) => Hm1m2 . *)
    (* rewrite (vm_preserve_bound_bexp (IH0 _ _ _ _ _ _ _ Hbb0) Hm1m2) *)
    (*         (IH1 _ _ _ _ _ _ _ Hbb1) // . *)
Admitted.


Corollary bit_blast_exp_cache_bound :
  forall e te m m' ca ca' g g' cs lrs,
    bit_blast_exp_cache te m ca g e = (m', ca', g', cs, lrs) ->
    Cache.well_formed ca -> Cache.bound ca m ->
    AdhereConform.bound_exp e m'.
Proof.
  move=> e te m m' ca ca' g g' cs lrs Hbb Hwfca Hbcam.
  move: (bit_blast_exp_cache_bound_cache Hbb Hwfca Hbcam) => [Hbe _].
  done.
Qed.

Corollary bit_blast_bexp_cache_bound :
  forall e te m m' ca ca' g g' cs lr,
    bit_blast_bexp_cache te m ca g e = (m', ca', g', cs, lr) ->
    Cache.well_formed ca -> Cache.bound ca m ->
    AdhereConform.bound_bexp e m'.
Proof.
  move=> e te m m' ca ca' g g' cs lr Hbb Hwfca Hbcam.
  move: (bit_blast_bexp_cache_bound_cache Hbb Hwfca Hbcam) => [Hbe _].
  done.
Qed.
