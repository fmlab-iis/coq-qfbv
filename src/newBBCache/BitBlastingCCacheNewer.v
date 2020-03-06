From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
(* From BBCache Require Import Cache BitBlastingCacheDef. *)
From newBBCache Require Import CompCache BitBlastingCCacheDef BitBlastingCCacheWF.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* =  mk_env_exp_ccache_newer_gen and mk_env_bexp_ccache_newer_gen = *)

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
      admit (* TODO: mod *) |
      admit (* TODO: srem *) |
      admit (* TODO: smod *) |
      exact: mk_env_shl_newer_gen |
      exact: mk_env_lshr_newer_gen |
      exact: mk_env_ashr_newer_gen |
      exact: mk_env_concat_newer_gen ].
Admitted.


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
  case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[cse lse] | ].
  - case=> _ _ _ <- _ _. done.
  - case Hop : (mk_env_ebinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lsop].
    case=> _ _ _ <- _ _. 
    move: (mk_env_ebinop_newer_gen Hop) => Hg2gop.
    exact: (pos_leb_trans Hgg2 Hg2gop).
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
  case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[cse le] | ].
  - case=> _ _ _ <- _ _. by t_auto_newer.
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
  case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[cse le] | ].
  - case=> _ _ _ <- _ _. by t_auto_newer.
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
    + admit.
    + admit.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_newer_gen_nocet_binop.
    + admit.
  (* bexp *)
  set IHe := mk_env_exp_ccache_newer_gen.
  set IHb := mk_env_bexp_ccache_newer_gen.
  move=> e m c s E g m' c' E' g' cs l.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite mk_env_bexp_ccache_equation Hfcbt /=.
    case=> _ _ _ <- _ _. exact: Pos.leb_refl.
  - move: e m c s E g m' c' E' g' cs l Hfcbt.
    case.
    + admit.
    + admit.
    + admit.
    + admit.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_newer_gen_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_newer_gen_nocbt_disj.
Admitted.


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
  case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[cse lse] | ].
  - case=> <- _ _ <- _ _. done.
  - case Hop : (mk_env_ebinop op E2 g2 ls1 ls2) => [[[Eop gop] csop] lsop].
    case=> <- _ _ <- _ _. 
    move: (mk_env_ebinop_newer_gen Hop) => Hg2gop.
    exact: (newer_than_vm_le_newer Hg2m2 Hg2gop).
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
  case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[cse le] | ].
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
  case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[cse le] | ].
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
    + admit.
    + admit.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_newer_vm_nocet_binop.
    + admit.
  (* bexp *)
  set IHe := mk_env_exp_ccache_newer_vm.
  set IHb := mk_env_bexp_ccache_newer_vm.
  move=> e m c s E g m' c' E' g' cs l.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite mk_env_bexp_ccache_equation Hfcbt /=.
    case=> <- _ _ <- _ _. done.
  - move: e m c s E g m' c' E' g' cs l Hfcbt.
    case.
    + admit.
    + admit.
    + admit.
    + admit.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_newer_vm_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_newer_vm_nocbt_disj.
Admitted.


(* = mk_env_exp_ccache_newer_all_lits and mk_env_bexp_ccache_newer_all_lits = *)

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
      admit (* TODO: mod *) |
      admit (* TODO: srem *) |
      admit (* TODO: smod *) |
      apply (mk_env_shl_newer_res Hgtt Hgls1 Hgls2 Hmk) |
      apply (mk_env_lshr_newer_res Hgtt Hgls1 Hgls2 Hmk) |
      apply (mk_env_ashr_newer_res Hgtt Hgls1 Hgls2 Hmk) |
      apply (mk_env_concat_newer_res Hmk) ]; 
    done.
Admitted.

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
      admit (* TODO: mod *) |
      admit (* TODO: srem *) |
      admit (* TODO: smod *) |
      apply (mk_env_shl_newer_cnf Hmk) |
      apply (mk_env_lshr_newer_cnf Hmk) |
      apply (mk_env_ashr_newer_cnf Hmk) |
      apply (mk_env_concat_newer_cnf Hmk) ]; 
    done.
Admitted.


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
      move: (newer_than_cache_le_newer Hgc Hggv) => Hgvc.
      repeat (split; first done). rewrite -newer_than_cache_add_cet.
      by apply newer_than_cache_add_het.
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
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
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
    move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt.
    move: (newer_than_lits_le_newer Hg1ls1 Hg1g2) => Hg2ls1.
    move: (mk_env_ebinop_newer_res Hop Hg2tt Hg2ls1 Hg2ls2) => Hgoplsop.
    move: (mk_env_ebinop_newer_cnf Hop Hg2tt Hg2ls1 Hg2ls2) => Hgopcsop.
    move: (mk_env_ebinop_newer_gen Hop) => Hg2gop.
    split; first done. split.
    + rewrite !newer_than_cnf_catrev. 
      move: (newer_than_cnf_le_newer Hg2cs1 Hg2gop) => Hgopcs1.
      move: (newer_than_cnf_le_newer Hg2cs2 Hg2gop) => Hgopcs2.
      by rewrite Hgopcs1 Hgopcs2 Hgopcsop.
    + move: (newer_than_cache_le_newer Hg2c2 Hg2gop) => Hgopc2.
      rewrite -newer_than_cache_add_cet. by apply newer_than_cache_add_het.
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
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
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
    move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt.
    move: (newer_than_lit_le_newer Hg1l1 Hg1g2) => Hg2l1.
    move: (mk_env_conj_newer_res Hop) => Hgoplop.
    move: (mk_env_conj_newer_cnf Hop Hg2l1 Hg2l2) => Hgopcsop.
    move: (mk_env_conj_newer_gen Hop) => Hg2gop.
    split; first done. split.
    + rewrite !newer_than_cnf_catrev. 
      move: (newer_than_cnf_le_newer Hg2cs1 Hg2gop) => Hgopcs1.
      move: (newer_than_cnf_le_newer Hg2cs2 Hg2gop) => Hgopcs2.
      by rewrite Hgopcs1 Hgopcs2 Hgopcsop.
    + move: (newer_than_cache_le_newer Hg2c2 Hg2gop) => Hgopc2.
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
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
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
    move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt.
    move: (newer_than_lit_le_newer Hg1l1 Hg1g2) => Hg2l1.
    move: (mk_env_disj_newer_res Hop) => Hgoplop.
    move: (mk_env_disj_newer_cnf Hop Hg2l1 Hg2l2) => Hgopcsop.
    move: (mk_env_disj_newer_gen Hop) => Hg2gop.
    split; first done. split.
    + rewrite !newer_than_cnf_catrev. 
      move: (newer_than_cnf_le_newer Hg2cs1 Hg2gop) => Hgopcs1.
      move: (newer_than_cnf_le_newer Hg2cs2 Hg2gop) => Hgopcs2.
      by rewrite Hgopcs1 Hgopcs2 Hgopcsop.
    + move: (newer_than_cache_le_newer Hg2c2 Hg2gop) => Hgopc2.
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
    + admit.
    + admit.
    + move=> op e1 e2; move: op e1 (IHe e1) e2 (IHe e2).
      exact: mk_env_exp_ccache_newer_all_lits_nocet_binop.
    + admit.
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
    + admit.
    + admit.
    + admit.
    + admit.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_newer_all_lits_nocbt_conj.
    + move=> e1 e2; move: e1 (IHb e1) e2 (IHb e2).
      exact: mk_env_bexp_ccache_newer_all_lits_nocbt_disj.
Admitted.


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
