From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport 
     AdhereConform.
(* From BBCache Require Import Cache BitBlastingCacheDef. *)
From newBBCache Require Import CompCache BitBlastingCCacheDef.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* = bit_blast_exp_ccache_adhere and bit_blast_bexp_ccache_adhere = *)

Lemma size_bit_blast_var' g n g' vs' :
  bit_blast_var' g n = (g', vs') -> size vs' = n .
Proof .
  elim : n g g' vs' => [ |n IH] g g' vs' .
  - case => _ <- // .
  - rewrite /bit_blast_var' /= -/bit_blast_var' .
    dcase (bit_blast_var' (g+1)%positive n) => [[g'' tl] Hbbr] .
    case => _ <- /= .
    rewrite (IH _ _ _ Hbbr) // .
Qed .

Lemma bit_blast_exp_ccache_adhere_nocet_var :
  forall (t : SSAVarOrder.t) (te : SSATE.env) (m : vm) (c : compcache)
         (g : generator) (m' : vm) (c' : compcache) (g' : generator) 
         (cs : cnf) (ls : word),
    adhere m te ->
    find_cet (QFBV.Evar t) c = None ->
    bit_blast_exp_ccache te m c g (QFBV.Evar t) = (m', c', g', cs, ls) -> 
    adhere m' te.
Proof.
  move=> v te m c g m' c' g' cs ls Hadm Hfcet. rewrite /= Hfcet.
  case Hfhet : (find_het (QFBV.Evar v) c) => [[cse lse] | ].
  - case=> <- _ _ _ _. done.
  - case Hfv : (SSAVM.find v m) .
    + case => <- _ _ _ _. done.
    + rewrite /bit_blast_var .
      dcase (bit_blast_var' g (SSATE.vsize v te)) => [[g'0 vs] Hbbr ] .
      case => <- _ _ _ _ .
      rewrite /adhere => u .
      case Heq : (u == v) .
      * rewrite (eqP Heq) => _ .
        have Hfind : (SSAVM.M.find v (SSAVM.M.add v vs m) = Some vs) .
        { apply : SSAVM.Lemmas.find_add_eq; done . }
        exists vs .
        rewrite Hfind (size_bit_blast_var' Hbbr) // .
      * have Hneq : ~(SSAVM.E.eq u v) .
        { rewrite /SSAVM.E.eq Heq // . }
        rewrite (SSAVM.Lemmas.mem_add_neq Hneq) => Hmem .
        rewrite (SSAVM.Lemmas.find_add_neq Hneq) .
        apply : (Hadm u Hmem) .
Qed.

Lemma bit_blast_exp_ccache_adhere_nocet_binop :
  forall (op : QFBV.ebinop) (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        adhere m te ->
        bit_blast_exp_ccache te m c g e1 = (m', c', g', cs, ls) -> adhere m' te) ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
          adhere m te ->
          bit_blast_exp_ccache te m c g e2 = (m', c', g', cs, ls) -> adhere m' te) ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (ls : word),
        adhere m te ->
        find_cet (QFBV.Ebinop op e1 e2) c = None ->
        bit_blast_exp_ccache te m c g (QFBV.Ebinop op e1 e2) = (m', c', g', cs, ls) ->
        adhere m' te.
Proof.
  move=> op e1 IH1 e2 IH2 te m c g m' c' g' cs ls Hadm Hfcet. rewrite /= Hfcet.
  case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
  move: (IH1 _ _ _ _ _ _ _ _ _ Hadm He1) => Hadm1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hadm1 He2) => Hadm2.
  case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csop lsop] | ];
    last case Hop : (bit_blast_ebinop op g2 ls1 ls2) => [[gop csop] lsop];
    case=> <- _ _ _ _; done.
Qed.

Lemma bit_blast_bexp_ccache_adhere_nocbt_conj :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        adhere m te ->
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l) -> adhere m' te) ->
    forall e2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
          adhere m te ->
          bit_blast_bexp_ccache te m c g e2 = (m', c', g', cs, l) -> adhere m' te) ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        adhere m te ->
        find_cbt (QFBV.Bconj e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bconj e1 e2) = (m', c', g', cs, l) ->
        adhere m' te.
Proof.
  move=> e1 IH1 e2 IH2 te m c g m' c' g' cs l Hadm Hfcbt. rewrite /= Hfcbt.
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ Hadm He1) => Hadm1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hadm1 He2) => Hadm2.
  case Hfhet : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csop lop] | ];
    case=> <- _ _ _ _; done.
Qed.

Lemma bit_blast_bexp_ccache_adhere_nocbt_disj :
  forall e1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
            (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        adhere m te ->
        bit_blast_bexp_ccache te m c g e1 = (m', c', g', cs, l) -> adhere m' te) ->
    forall e2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
              (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
          adhere m te ->
          bit_blast_bexp_ccache te m c g e2 = (m', c', g', cs, l) -> adhere m' te) ->
      forall (te : SSATE.env) (m : vm) (c : compcache) (g : generator) 
             (m' : vm) (c' : compcache) (g' : generator) (cs : cnf) (l : literal),
        adhere m te ->
        find_cbt (QFBV.Bdisj e1 e2) c = None ->
        bit_blast_bexp_ccache te m c g (QFBV.Bdisj e1 e2) = (m', c', g', cs, l) ->
        adhere m' te.
Proof.
  move=> e1 IH1 e2 IH2 te m c g m' c' g' cs l Hadm Hfcbt. rewrite /= Hfcbt.
  case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
  case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
  move: (IH1 _ _ _ _ _ _ _ _ _ Hadm He1) => Hadm1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hadm1 He2) => Hadm2.
  case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csop lop] | ];
    case=> <- _ _ _ _; done.
Qed.


Corollary bit_blast_exp_ccache_adhere :
  forall e te m c g m' c' g' cs ls,
    AdhereConform.adhere m te ->
    bit_blast_exp_ccache te m c g e = (m', c', g', cs, ls) ->
    AdhereConform.adhere m' te
with
bit_blast_bexp_ccache_adhere :
  forall e te m c g m' c' g' cs l,
    AdhereConform.adhere m te ->
    bit_blast_bexp_ccache te m c g e = (m', c', g', cs, l) ->
    AdhereConform.adhere m' te .
Proof.
  (* exp *)
  set IHe := bit_blast_exp_ccache_adhere.
  set IHb := bit_blast_bexp_ccache_adhere.
  move=> e te m c g m' c' g' cs ls Hadm.
  case Hfcet: (find_cet e c) => [[cse lse] | ]. 
  - rewrite bit_blast_exp_ccache_equation Hfcet /=.
    case=> <- _ _ _ _. done. 
  - move: e te m c g m' c' g' cs ls Hadm Hfcet.
    case.
    + exact: bit_blast_exp_ccache_adhere_nocet_var.
    + admit.
    + admit.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: bit_blast_exp_ccache_adhere_nocet_binop.
    + admit.
  (* bexp *)
  set IHe := bit_blast_exp_ccache_adhere.
  set IHb := bit_blast_bexp_ccache_adhere.
  move=> e te m c g m' c' g' cs l Hadm.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite bit_blast_bexp_ccache_equation Hfcbt /=.
    case=> <- _ _ _ _. done. 
  - move: e te m c g m' c' g' cs l Hadm Hfcbt.
    case.
    + admit.
    + admit.
    + admit.
    + admit.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: bit_blast_bexp_ccache_adhere_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: bit_blast_bexp_ccache_adhere_nocbt_disj.
Admitted.

