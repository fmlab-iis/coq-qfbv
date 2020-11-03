From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport
     BitBlastingDef .

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* = mk_env_exp_newer_gen and mk_env_bexp_newer_gen = *)

Lemma mk_env_exp_newer_gen_var :
  forall t (m : vm) (s : SSAStore.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Evar t) = (m', E', g', cs, lrs) -> (g <=? g')%positive.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case: (SSAVM.find v m).
  - move=> ls [] _ _ <- _ _. exact: Pos.leb_refl.
  - case Henv: (mk_env_var E g (SSAStore.acc v s) v) => [[[oE og] ocs] olrs].
    case=> _ _ <- _ _. exact: (mk_env_var_newer_gen Henv).
Qed.

Lemma mk_env_exp_newer_gen_const :
  forall (b : bits) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Econst b) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> bs m s E g m' E' g' cs lrs /=. case=> _ _ <- _ _. exact: Pos.leb_refl.
Qed.

Lemma mk_env_exp_newer_gen_not :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop QFBV.Unot e1) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (mk_env_not_newer_gen Hmkr) => Hg1gr.
  apply: (pos_leb_trans Hg0g1). done.
Qed.

Lemma mk_env_exp_newer_gen_and :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Band e1 e2) = (m', E', g', cs, lrs) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_and_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_exp_newer_gen_or :
    forall (e0: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_or E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_or_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed .

Lemma mk_env_exp_newer_gen_xor :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', E', g', cs, lrs) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_xor_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_exp_newer_gen_neg :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop QFBV.Uneg e1) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (mk_env_neg_newer_gen Hmkr) => Hg1gr.
  apply: (pos_leb_trans Hg0g1). done.
Qed.

Lemma mk_env_exp_newer_gen_add :
    forall (e0: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Badd e0 e1) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_add E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_add_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_exp_newer_gen_sub :
    forall (e0: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsub e0 e1) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sub E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_sub_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_exp_newer_gen_mul :
    forall (e: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmul e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_mul E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_mul_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_exp_newer_gen_mod :
  forall (e : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
  forall (e0 : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmod e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_umod E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_umod_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_exp_newer_gen_srem :
  forall (e : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
  forall (e0 : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_srem E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_srem_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_exp_newer_gen_smod :
  forall (e : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
  forall (e0 : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smod E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_smod_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_exp_newer_gen_shl :
    forall (e0 : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1 : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_shl E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_shl_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed .

Lemma mk_env_exp_newer_gen_lshr :
    forall (e0 : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1 : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_lshr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_lshr_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed .

Lemma mk_env_exp_newer_gen_ashr :
    forall (e0 : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1 : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ashr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_ashr_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed .

Lemma mk_env_exp_newer_gen_concat :
    forall (e0: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_concat E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_concat_newer_gen Hmkr) => Hg2gr.
  by apply: (pos_leb_trans _ Hg1g2).
Qed .

Lemma mk_env_exp_newer_gen_extract :
  forall (i j : nat),
    forall (e : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> i j e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ _.
  exact : (IH1 _ _ _ _ _ _ _ _ _ Hmke1) .
Qed .

(*
Lemma mk_env_exp_newer_gen_slice :
  forall (w1 w2 w3 : nat),
    forall (e : exp (w3 + w2 + w1)),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .
*)

Lemma mk_env_exp_newer_gen_high :
    forall (n : nat) (e : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm)
           (s : SSAStore.t) (E : env) (g : generator) (m' : vm)
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ _.
  exact : (IH1 _ _ _ _ _ _ _ _ _ Hmke1) .
Qed .

Lemma mk_env_exp_newer_gen_low :
    forall (n : nat) (e : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Ulow n) e) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ _.
  exact : (IH1 _ _ _ _ _ _ _ _ _ Hmke1) .
Qed .

Lemma mk_env_exp_newer_gen_zeroextend :
  forall (n : nat),
    forall (e: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop (QFBV.Uzext n) e) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ _.
  exact : (IH1 _ _ _ _ _ _ _ _ _ Hmke1) .
Qed .

Lemma mk_env_exp_newer_gen_signextend :
  forall (n : nat),
    forall (e: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Usext n) e) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ _.
  exact : (IH1 _ _ _ _ _ _ _ _ _ Hmke1) .
Qed .

Lemma mk_env_exp_newer_gen_ite :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (e0 : QFBV.exp),
        (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : word),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
        forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp m s E g (QFBV.Eite b e e0) = (m', E', g', cs, lrs) ->
          (g <=? g')%positive.
Proof.
  move=> c IHc e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmkc : (mk_env_bexp m s E g c) => [[[[mc Ec] gc] csc] lc].
  case Hmke1 : (mk_env_exp mc s Ec gc e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ite E2 g2 lc ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IHc _ _ _ _ _ _ _ _ _ Hmkc) => Hggc.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hgcg1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_ite_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_false :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Bfalse = (m', E', g', cs, lr) -> (g <=? g')%positive.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- _ _. exact: Pos.leb_refl.
Qed.

Lemma mk_env_bexp_newer_gen_true :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Btrue = (m', E', g', cs, lr) -> (g <=? g')%positive.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- _ _. exact: Pos.leb_refl.
Qed.

Lemma mk_env_bexp_newer_gen_eq :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Beq e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_eq E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_eq_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_ult :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bult e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ult E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_ult_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_ule :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bule e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ule E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_ule_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_ugt :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bugt e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ugt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_ugt_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.


Lemma mk_env_bexp_newer_gen_uge :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buge e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_uge_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_slt :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_slt_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_sle :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_sle_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_sgt :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_sgt_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_sge :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_sge_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_uaddo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uaddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_uaddo_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_usubo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Busubo e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_usubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_usubo_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_umulo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_umulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_umulo_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_saddo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_saddo_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_ssubo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_ssubo_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_smulo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_smulo_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_lneg :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Blneg b) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
   t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_conj :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
    forall (b0 : QFBV.bexp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bconj b b0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_disj :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
    forall (b0 : QFBV.bexp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bdisj b b0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  t_auto_newer .
Qed.

Corollary mk_env_exp_newer_gen :
  forall (e : QFBV.exp) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    (g <=? g')%positive
  with
    mk_env_bexp_newer_gen :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  (* mk_env_exp_newer_gen *)
  elim .
  - exact: mk_env_exp_newer_gen_var.
  - exact: mk_env_exp_newer_gen_const.
  - elim .
    + apply :mk_env_exp_newer_gen_not .
    + apply :mk_env_exp_newer_gen_neg .
    + apply :mk_env_exp_newer_gen_extract .
    + apply :mk_env_exp_newer_gen_high .
    + apply :mk_env_exp_newer_gen_low .
    + apply :mk_env_exp_newer_gen_zeroextend .
    + apply :mk_env_exp_newer_gen_signextend .
  - elim .
    + apply :mk_env_exp_newer_gen_and .
    + apply :mk_env_exp_newer_gen_or .
    + apply :mk_env_exp_newer_gen_xor .
    + apply :mk_env_exp_newer_gen_add .
    + apply :mk_env_exp_newer_gen_sub .
    + apply :mk_env_exp_newer_gen_mul .
    + apply :mk_env_exp_newer_gen_mod .
    + apply :mk_env_exp_newer_gen_srem .
    + apply :mk_env_exp_newer_gen_smod .
    + apply :mk_env_exp_newer_gen_shl .
    + apply :mk_env_exp_newer_gen_lshr .
    + apply :mk_env_exp_newer_gen_ashr .
    + apply :mk_env_exp_newer_gen_concat .
  - move => b; move : b (mk_env_bexp_newer_gen b) .
    apply :mk_env_exp_newer_gen_ite .
  (* mk_env_bexp_newer_gen *)
  elim .
  - apply : mk_env_bexp_newer_gen_false .
  - apply : mk_env_bexp_newer_gen_true .
  - elim;
      move => e1 e2;
      move : e1 (mk_env_exp_newer_gen e1)
             e2 (mk_env_exp_newer_gen e2) .
    + apply : mk_env_bexp_newer_gen_eq .
    + apply : mk_env_bexp_newer_gen_ult .
    + apply : mk_env_bexp_newer_gen_ule .
    + apply : mk_env_bexp_newer_gen_ugt .
    + apply : mk_env_bexp_newer_gen_uge .
    + apply : mk_env_bexp_newer_gen_slt .
    + apply : mk_env_bexp_newer_gen_sle .
    + apply : mk_env_bexp_newer_gen_sgt .
    + apply : mk_env_bexp_newer_gen_sge .
    + apply : mk_env_bexp_newer_gen_uaddo .
    + apply : mk_env_bexp_newer_gen_usubo .
    + apply : mk_env_bexp_newer_gen_umulo .
    + apply : mk_env_bexp_newer_gen_saddo .
    + apply : mk_env_bexp_newer_gen_ssubo .
    + apply : mk_env_bexp_newer_gen_smulo .
  - apply : mk_env_bexp_newer_gen_lneg .
  - apply : mk_env_bexp_newer_gen_conj .
  - apply : mk_env_bexp_newer_gen_disj .
Qed.



(* = mk_env_exp_newer_vm and mk_env_bexp_newer_vm = *)

Lemma mk_env_exp_newer_vm_var :
  forall t (m : vm) (s : SSAStore.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Evar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case Hfind: (SSAVM.find v m).
  - case=> <- _ <- _ _ Hnew_gm // .
  - case Henv: (mk_env_var E g (SSAStore.acc v s) v) => [[[oE og] ocs] olrs].
    case=> <- _ <- _ _ Hnew_gm.
    move=> x lxs. case Hxv: (x == v).
    + rewrite (SSAVM.Lemmas.find_add_eq Hxv) .
      case => <-; exact: (mk_env_var_newer_res Henv).
    + move/negP: Hxv => Hxv. rewrite (SSAVM.Lemmas.find_add_neq Hxv) => Hfindx.
      move: (Hnew_gm x lxs Hfindx) => Hnew_og.
      apply: (newer_than_lits_le_newer Hnew_og). exact: (mk_env_var_newer_gen Henv).
Qed.

Lemma mk_env_exp_newer_vm_const :
  forall (b : bits) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Econst b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> b m s E g m' E' g' cs lrs. case=> <- _ <- _ _. by apply.
Qed.

Lemma mk_env_exp_newer_vm_not :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop QFBV.Unot e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (mk_env_not_newer_gen Hmkr) => Hg1gr.
  exact: (newer_than_vm_le_newer Hg1m1 Hg1gr).
Qed.

Lemma mk_env_exp_newer_vm_and :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Band e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_and_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_exp_newer_vm_or :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_or E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_or_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed .

Lemma mk_env_exp_newer_vm_xor :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_xor_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_exp_newer_vm_neg :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop QFBV.Uneg e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (mk_env_neg_newer_gen Hmkr) => Hg1gr.
  exact: (newer_than_vm_le_newer Hg1m1 Hg1gr).
Qed.

Lemma mk_env_exp_newer_vm_add :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Badd e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_add E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_add_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_exp_newer_vm_sub :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsub e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sub E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_sub_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_exp_newer_vm_mul :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmul e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_mul E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_mul_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_exp_newer_vm_mod :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_srem :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_smod :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_shl :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_shl E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_shl_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed .

Lemma mk_env_exp_newer_vm_lshr :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_lshr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_lshr_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed .

Lemma mk_env_exp_newer_vm_ashr :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ashr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_ashr_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed .

Lemma mk_env_exp_newer_vm_concat :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_concat E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  apply : (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) .
Qed .

Lemma mk_env_exp_newer_vm_extract :
  forall (i j : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> i j e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- _ _ Hg0m0.
  apply: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) .
Qed .

(*
Lemma mk_env_exp_newer_vm_slice :
  forall (w1 w2 w3 : nat),
    forall (e : exp (w3 + w2 + w1)),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  by apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .
*)

Lemma mk_env_exp_newer_vm_high :
    forall (n : nat) (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm)
           (s : SSAStore.t) (E : env) (g : generator) (m' : vm)
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- _ _ Hg0m0.
  apply : (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) .
Qed .

Lemma mk_env_exp_newer_vm_low :
    forall (n : nat) (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Ulow n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- _ _ Hg0m0.
  apply : (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) .
Qed .

Lemma mk_env_exp_newer_vm_zeroextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : word),
        mk_env_exp m s E g (QFBV.Eunop (QFBV.Uzext n) e) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- _ _ Hg0m0.
  apply : (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) .
Qed .

Lemma mk_env_exp_newer_vm_signextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Usext n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- _ _ Hg0m0.
  apply : (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) . 
Qed .

Lemma mk_env_exp_newer_vm_ite :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (e0 : QFBV.exp),
        (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : word),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
            newer_than_vm g m -> newer_than_vm g' m') ->
        forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp m s E g (QFBV.Eite b e e0) = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> c IHc e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmkc : (mk_env_bexp m s E g c) => [[[[mc Ec] gc] csc] lsc].
  case Hmke1 : (mk_env_exp mc s Ec gc e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ite E2 g2 lsc ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IHc _ _ _ _ _ _ _ _ _ Hmkc Hg0m0) => Hgcmc.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgcmc) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_ite_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_false :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Bfalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> m s E g m' E' g' cs lr. case=> <- _ <- _ _ // .
Qed.

Lemma mk_env_bexp_newer_vm_true :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Btrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> m s E g m' E' g' cs lr. case=> <- _ <- _ _ // .
Qed.

Lemma mk_env_bexp_newer_vm_eq :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Beq e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_eq E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_eq_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_ult :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bult e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ult E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_ult_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_ule :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bule e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ule E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_ule_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_ugt :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bugt e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ugt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_ugt_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_uge :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buge e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_uge_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.


Lemma mk_env_bexp_newer_vm_slt :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_slt_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_sle :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_sle_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_sgt :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_sgt_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_sge :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_sge_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_uaddo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uaddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_uaddo_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_usubo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Busubo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_usubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_usubo_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_umulo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_umulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_umulo_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_saddo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_saddo_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_ssubo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_ssubo_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_smulo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_smulo_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_lneg :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Blneg b) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e IH m s E g m' E' g' cs lr /=.
  case Henv: (mk_env_bexp m s E g e) => [[[[m1 E1] g1] cs1] lr1].
  case => <- _ <- _ _ Hnew. apply newer_than_vm_add_r.
  apply: (IH _ _ _ _ _ _ _ _ _ Henv).
  exact.
Qed.

Lemma mk_env_bexp_newer_vm_conj :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (b0 : QFBV.bexp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bconj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /=.
  case Henv1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case=> <- _ <- _ _ Hnew. apply: newer_than_vm_add_r.
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2). apply: (IH1 _ _ _ _ _ _ _ _ _ Henv1).
  exact: Hnew.
Qed.

Lemma mk_env_bexp_newer_vm_disj :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (b0 : QFBV.bexp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bdisj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /=.
  case Henv1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case=> <- _ <- _ _ Hnew. apply: newer_than_vm_add_r.
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2). apply: (IH1 _ _ _ _ _ _ _ _ _ Henv1).
  exact: Hnew.
Qed.

Corollary mk_env_exp_newer_vm :
  forall (e : QFBV.exp) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_vm g' m'
  with
    mk_env_bexp_newer_vm :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  (* mk_env_exp_newer_vm *)
  elim .
  - exact: mk_env_exp_newer_vm_var .
  - exact: mk_env_exp_newer_vm_const .
  - elim .
    + exact: mk_env_exp_newer_vm_not .
    + exact: mk_env_exp_newer_vm_neg .
    + exact: mk_env_exp_newer_vm_extract .
    + exact: mk_env_exp_newer_vm_high .
    + exact: mk_env_exp_newer_vm_low .
    + exact: mk_env_exp_newer_vm_zeroextend .
    + exact: mk_env_exp_newer_vm_signextend .
  - elim .
    + exact: mk_env_exp_newer_vm_and .
    + exact: mk_env_exp_newer_vm_or .
    + exact: mk_env_exp_newer_vm_xor .
    + exact: mk_env_exp_newer_vm_add .
    + exact: mk_env_exp_newer_vm_sub .
    + exact: mk_env_exp_newer_vm_mul .
    + exact: mk_env_exp_newer_vm_mod .
    + exact: mk_env_exp_newer_vm_srem .
    + exact: mk_env_exp_newer_vm_smod .
    + exact: mk_env_exp_newer_vm_shl .
    + exact: mk_env_exp_newer_vm_lshr .
    + exact: mk_env_exp_newer_vm_ashr .
    + exact: mk_env_exp_newer_vm_concat .
  - move => b; move : b (mk_env_bexp_newer_vm b) .
    exact: mk_env_exp_newer_vm_ite .
  (* mk_env_bexp_newer_vm *)
  elim .
  - exact: mk_env_bexp_newer_vm_false .
  - exact: mk_env_bexp_newer_vm_true .
  - elim;
      move => e0 e1;
      move : e0 (mk_env_exp_newer_vm e0)
             e1 (mk_env_exp_newer_vm e1) .
    + exact: mk_env_bexp_newer_vm_eq .
    + exact: mk_env_bexp_newer_vm_ult .
    + exact: mk_env_bexp_newer_vm_ule .
    + exact: mk_env_bexp_newer_vm_ugt .
    + exact: mk_env_bexp_newer_vm_uge .
    + exact: mk_env_bexp_newer_vm_slt .
    + exact: mk_env_bexp_newer_vm_sle .
    + exact: mk_env_bexp_newer_vm_sgt .
    + exact: mk_env_bexp_newer_vm_sge .
    + exact: mk_env_bexp_newer_vm_uaddo .
    + exact: mk_env_bexp_newer_vm_usubo .
    + exact: mk_env_bexp_newer_vm_umulo .
    + exact: mk_env_bexp_newer_vm_saddo .
    + exact: mk_env_bexp_newer_vm_ssubo .
    + exact: mk_env_bexp_newer_vm_smulo .
  - exact: mk_env_bexp_newer_vm_lneg .
  - exact: mk_env_bexp_newer_vm_conj .
  - exact: mk_env_bexp_newer_vm_disj .
Qed.



(* = mk_env_exp_newer_res and mk_env_bexp_newer_res = *)

Lemma mk_env_exp_newer_res_var :
  forall t (m : vm) (s : SSAStore.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Evar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case Hfind: (SSAVM.find v m).
  - case=> _ _ <- _ <- Hnew_gm Hnew_gtt. exact: (Hnew_gm v _ Hfind).
  - case Henv: (mk_env_var E g (SSAStore.acc v s) v)=> [[[Ev gv] csv] lrsv].
    case=> _ _ <- _ <- Hnew_gm Hnew_gtt. exact: (mk_env_var_newer_res Henv).
Qed.

Lemma mk_env_exp_newer_res_const :
  forall (b : bits) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Econst b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> bs m s E g m' E' g' cs lrs. rewrite /mk_env_exp.
  case Henv: (mk_env_const E g bs)=> [[[oE og] ocs] olrs].
  case=> _ _ <- _ <- Hnew_gm Hnew_tt. exact: (mk_env_const_newer_res Henv Hnew_tt).
Qed.

Lemma mk_env_exp_newer_res_not :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator)
            (cs : cnf) (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop QFBV.Unot e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  exact: (mk_env_not_newer_res Hmkr Hg1l1).
Qed.

Lemma mk_env_exp_newer_res_and :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator)
            (cs : cnf) (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        newer_than_lits g' lrs) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Band e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  (* now mk_env_and_newer_res is available *)
  exact: (mk_env_and_newer_res Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_newer_res_or :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_or E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  (* now mk_env_or_newer_res is available *)
  exact: (mk_env_or_newer_res Hmkr Hg2t Hg2l1 Hg2l2).
Qed .

Lemma mk_env_exp_newer_res_xor :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator)
            (cs : cnf) (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        newer_than_lits g' lrs) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  (* now mk_env_xor_newer_res is available *)
  exact: (mk_env_xor_newer_res Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_newer_res_neg :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator)
            (cs : cnf) (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop QFBV.Uneg e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  (* now mk_env_neg_newer_res is available *)
  exact: (mk_env_neg_newer_res Hmkr Hg1t Hg1l1).
Qed.

Lemma mk_env_exp_newer_res_add :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Badd e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_add E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  exact: (mk_env_add_newer_res Hmkr).
Qed.

Lemma mk_env_exp_newer_res_sub :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsub e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sub E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  (* now mk_env_sub_newer_res is available *)
  exact: (mk_env_sub_newer_res Hmkr).
Qed.

Lemma mk_env_exp_newer_res_mul :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmul e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_mul E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  (* now mk_env_mul_newer_res is available *)
  exact: (mk_env_mul_newer_res Hmkr Hg2t).
Qed.

Lemma mk_env_exp_newer_res_mod :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_srem :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_smod :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_shl :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_shl E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  (* now mk_env_shl_newer_res is available *)
  exact: (mk_env_shl_newer_res Hg2t Hg2l1 Hg2l2 Hmkr) .
Qed .

Lemma mk_env_exp_newer_res_lshr :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_lshr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  (* now mk_env_lshr_newer_res is available *)
  exact: (mk_env_lshr_newer_res Hg2t Hg2l1 Hg2l2 Hmkr) .
Qed .

Lemma mk_env_exp_newer_res_ashr :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ashr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  (* now mk_env_ashr_newer_res is available *)
  exact: (mk_env_ashr_newer_res Hg2t Hg2l1 Hg2l2 Hmkr) .
Qed .

Lemma mk_env_exp_newer_res_concat :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  rewrite newer_than_lits_cat Hg2l1 Hg2l2 // .
Qed .

Lemma mk_env_exp_newer_res_extract :
  forall (i j : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> i j e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  apply : (@mk_env_extract_newer_res E _ _ _  _ _ _ _ _ _ Hg1t Hg1l1) .
  rewrite /mk_env_extract // .
Qed .

(*
Lemma mk_env_exp_newer_res_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV.exp (w3 + w2 + w1)),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move => w1 w2 w3 e IHe .
  rewrite /=; intros; dcase_hyps; subst .
  move: (IHe _ _ _ _ _ _ _ _ _ H H0 H1) => Hg'ls .
  apply: newer_than_lits_get_high_aux .
  by apply: newer_than_lits_get_low_aux .
Qed .
*)

Lemma mk_env_exp_newer_res_high :
    forall (n : nat) (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm)
         (s : SSAStore.t) (E : env) (g : generator) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  (* now mk_env_high_newer_res is available *)
  exact : (@mk_env_high_newer_res E _ _ _ _ _ _ _ _ Hg1t Hg1l1) .
Qed .

Lemma mk_env_exp_newer_res_low :
    forall (n : nat) (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Ulow n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  (* now mk_env_low_newer_res is available *)
  exact : (@mk_env_low_newer_res E _ _ _ _ _ _ _ _ Hg1t Hg1l1) .
Qed .

Lemma mk_env_exp_newer_res_zeroextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uzext n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  (* now mk_env_zeroextend_newer_res is available *)
  exact: (@mk_env_zeroextend_newer_res _ E _ _ _ _ _ _ _ Hg1t Hg1l1) .
Qed .

Lemma mk_env_exp_newer_res_signextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Usext n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  (* now mk_env_signextend_newer_res is available *)
  exact: (@mk_env_signextend_newer_res _ E _ _ _ _ _ _ _ Hg1t Hg1l1) .
Qed .

Lemma mk_env_exp_newer_res_ite :
  forall (b : QFBV.bexp) (e e0 : QFBV.exp)
         (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Eite b e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> c e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmkc : (mk_env_bexp m s E g c) => [[[[mc Ec] gc] csc] lsc].
  case Hmke1 : (mk_env_exp mc s Ec gc e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ite E2 g2 lsc ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  exact : mk_env_ite_newer_res Hmkr .
Qed.

Lemma mk_env_bexp_newer_res_false :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Bfalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- _ <- Hnvm Hnew. exact: Hnew.
Qed.

Lemma mk_env_bexp_newer_res_true :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Btrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- _ <- Hnvm Hnew. exact: Hnew.
Qed.

Lemma mk_env_bexp_newer_res_eq :
  forall (e e0 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Beq e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_eq E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  exact : (mk_env_eq_newer_res Hmkr) .
Qed.

Lemma mk_env_bexp_newer_res_ult :
  forall (e e0 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bult e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ult E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_ult_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_ult_newer_res Hmkr) .
  t_auto_newer .
Qed.


Lemma mk_env_bexp_newer_res_ule :
  forall (e e0 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bule e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ule E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_ule_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_ule_newer_res Hmkr) .
Qed.

Lemma mk_env_bexp_newer_res_ugt :
  forall (e e0 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bugt e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ugt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_ugt_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_ugt_newer_res Hmkr) .
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_res_uge :
  forall (e e0 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buge e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_uge_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_uge_newer_res Hmkr) .
Qed.

Lemma mk_env_bexp_newer_res_slt :
  forall (e1 e2 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_slt_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_slt_newer_res Hmkr) .
Qed.

Lemma mk_env_bexp_newer_res_sle :
  forall (e1 e2 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_sle_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_sle_newer_res Hmkr) .
Qed.

Lemma mk_env_bexp_newer_res_sgt :
  forall (e1 e2 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_sgt_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_sgt_newer_res Hmkr) .
Qed.

Lemma mk_env_bexp_newer_res_sge :
  forall (e1 e2 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_sge_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_sge_newer_res Hmkr) .
Qed.

Lemma mk_env_bexp_newer_res_uaddo :
  forall (e e0 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uaddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_uaddo_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_uaddo_newer_res Hmkr) .
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_res_usubo :
  forall (e e0 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Busubo e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_usubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_usubo_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_usubo_newer_res Hmkr) .
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_res_umulo :
  forall (e e0 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_umulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_umulo_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_umulo_newer_res Hmkr) .
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_res_saddo :
  forall (e1 e2 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_saddo_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_saddo_newer_res Hmkr) .
Qed.

Lemma mk_env_bexp_newer_res_ssubo :
  forall (e1 e2 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_ssubo_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_ssubo_newer_res Hmkr) .
Qed.

Lemma mk_env_bexp_newer_res_smulo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator)
            (cs : cnf) (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        newer_than_lits g' lrs) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  (* now mk_env_smulo_newer_res is available *)
  exact: (mk_env_smulo_newer_res Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_newer_res_lneg :
  forall (b : QFBV.bexp) (m : vm) (s : SSAStore.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Blneg b) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  exact: newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_bexp_newer_res_conj :
  forall (b b0 : QFBV.bexp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bconj b b0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  exact: newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_bexp_newer_res_disj :
  forall (b b0 : QFBV.bexp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bdisj b b0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite/=; intros; dcase_hyps; subst.
  exact: newer_than_lit_add_diag_r.
Qed.

Corollary mk_env_exp_newer_res :
  forall (e : QFBV.exp) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs
  with
    mk_env_bexp_newer_res :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_lit g' lr.
Proof.
  (* mk_env_exp_newer_res *)
  elim .
  - exact : mk_env_exp_newer_res_var .
  - exact : mk_env_exp_newer_res_const .
  - elim .
    + exact : mk_env_exp_newer_res_not .
    + exact : mk_env_exp_newer_res_neg .
    + exact : mk_env_exp_newer_res_extract .
    + exact : mk_env_exp_newer_res_high .
    + exact : mk_env_exp_newer_res_low .
    + exact : mk_env_exp_newer_res_zeroextend .
    + exact : mk_env_exp_newer_res_signextend .
  - elim .
    + exact : mk_env_exp_newer_res_and .
    + exact : mk_env_exp_newer_res_or .
    + exact : mk_env_exp_newer_res_xor .
    + exact : mk_env_exp_newer_res_add .
    + exact : mk_env_exp_newer_res_sub .
    + exact : mk_env_exp_newer_res_mul .
    + exact : mk_env_exp_newer_res_mod .
    + exact : mk_env_exp_newer_res_srem .
    + exact : mk_env_exp_newer_res_smod .
    + exact : mk_env_exp_newer_res_shl .
    + exact : mk_env_exp_newer_res_lshr .
    + exact : mk_env_exp_newer_res_ashr .
    + exact : mk_env_exp_newer_res_concat .
  - move => b e0 _ e1 _;
    move: b e0 e1; exact : mk_env_exp_newer_res_ite .
  (* mk_env_bexp_newer_res *)
  elim .
  - exact : mk_env_bexp_newer_res_false .
  - exact : mk_env_bexp_newer_res_true .
  - elim .
    + exact : mk_env_bexp_newer_res_eq .
    + exact : mk_env_bexp_newer_res_ult .
    + exact : mk_env_bexp_newer_res_ule .
    + exact : mk_env_bexp_newer_res_ugt .
    + exact : mk_env_bexp_newer_res_uge .
    + exact : mk_env_bexp_newer_res_slt .
    + exact : mk_env_bexp_newer_res_sle .
    + exact : mk_env_bexp_newer_res_sgt .
    + exact : mk_env_bexp_newer_res_sge .
    + exact : mk_env_bexp_newer_res_uaddo .
    + exact : mk_env_bexp_newer_res_usubo .
    + exact : mk_env_bexp_newer_res_umulo .
    + exact : mk_env_bexp_newer_res_saddo .
    + exact : mk_env_bexp_newer_res_ssubo .
    + move => e e0;
        move : e (mk_env_exp_newer_res e)
               e0 (mk_env_exp_newer_res e0);
        exact : mk_env_bexp_newer_res_smulo .
  - move => b _; exact : mk_env_bexp_newer_res_lneg .
  - move => b0 _ b1 _; exact : mk_env_bexp_newer_res_conj .
  - move => b0 _ b1 _; exact : mk_env_bexp_newer_res_disj .
Qed.



(* = mk_env_exp_newer_cnf and mk_env_bexp_newer_cnf = *)

Lemma mk_env_exp_newer_cnf_var :
  forall t (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Evar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Evar t) te ->
    newer_than_cnf g' cs.
Proof.
  move=> v te m s E g m' E' g' cs lrs /=. case: (SSAVM.find v m).
  - move=> lxs [] _ _ <- <- _ Hnew_gm Hnew_gtt _. done.
  - case Henv: (mk_env_var E g (SSAStore.acc v s) v)=> [[[Ev gv] csv] lrsv].
    case=> _ _ <- <- _ Hnew_gm Hnew_gtt _. exact: (mk_env_var_newer_cnf Henv).
Qed.

Lemma mk_env_exp_newer_cnf_const :
  forall (b : bits) (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Econst b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Econst b) te ->
    newer_than_cnf g' cs.
Proof.
  move=> bs te m s E g m' E' g' cs lrs /=. case=> _ _ <- <- _ Hnew_gm Hnew_gtt _. done.
Qed.

Lemma mk_env_exp_newer_cnf_not :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop QFBV.Unot e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop QFBV.Unot e1) te ->
      newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt Hwf.
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) => Hg1c1.
  move: (mk_env_not_newer_gen Hmkr) => Hg1gr.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1gr) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  exact: (mk_env_not_newer_cnf Hmkr Hg1l1).
Qed.

Lemma mk_env_exp_newer_cnf_and :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Band e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Band e1 e2) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [/andP [Hwf1 Hwf2] _] _] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_and_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  exact: (mk_env_and_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_newer_cnf_or :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bor e0 e1) te ->
    newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_or E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [/andP [Hwf1 Hwf2] _] _] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_or_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  exact: (mk_env_or_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_newer_cnf_xor :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bxor e1 e2) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [/andP [Hwf1 Hwf2] _] _] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_xor_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  exact: (mk_env_xor_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_newer_cnf_neg :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop QFBV.Uneg e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop QFBV.Uneg e1) te ->
      newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt Hwf .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) => Hg1c1.
  move: (mk_env_neg_newer_gen Hmkr) => Hg1gr.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1gr) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  exact : (mk_env_neg_newer_cnf Hmkr (newer_than_lit_le_newer Hgt (mk_env_exp_newer_gen Hmke1)) Hg1l1).
Qed.

Lemma mk_env_exp_newer_cnf_add :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Badd e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Badd e e0) te ->
    newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_add E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [/andP [Hwf1 Hwf2] Hszgt0] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_add_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2f.
  rewrite newer_than_lit_tt_ff in Hg2f .
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply : (mk_env_add_newer_cnf Hmkr Hg2l1 Hg2l2 Hg2f).
Qed.

Lemma mk_env_exp_newer_cnf_sub :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsub e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsub e e0) te ->
    newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sub E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [/andP [Hwf1 Hwf2] Hszgt0] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_sub_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2f.
  rewrite newer_than_lit_tt_ff in Hg2f .
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply : (mk_env_sub_newer_cnf Hmkr Hg2f Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_newer_cnf_mul :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmul e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsub e e0) te ->
    newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_mul E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [/andP [Hwf1 Hwf2] Hszgt0] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_mul_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply : (mk_env_mul_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_newer_cnf_mod :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        newer_than_cnf g' cs) ->
  forall (e0 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e0 te ->
        newer_than_cnf g' cs) ->
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bmod e e0) te ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_srem :
  forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
  forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsrem e e0) te ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_smod :
  forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
  forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsmod e e0) te ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_shl :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bshl e0 e1) te ->
      newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_shl E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [/andP [Hwf1 Hwf2] Hszgt0] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_shl_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply : (mk_env_shl_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed .

Lemma mk_env_exp_newer_cnf_lshr :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Blshr e0 e1) te ->
      newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_lshr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [/andP [Hwf1 Hwf2] Hszgt0] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_lshr_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply : (mk_env_lshr_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed .

Lemma mk_env_exp_newer_cnf_ashr :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bashr e0 e1) te ->
      newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ashr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [/andP [Hwf1 Hwf2] Hszgt0] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_ashr_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply : (mk_env_ashr_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed .

Lemma mk_env_exp_newer_cnf_concat :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bconcat e0 e1) te ->
      newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [/andP [Hwf1 Hwf2] Hszgt0] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => Hg2c1.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite Hg2c1 Hg2c2 // .
Qed .

Lemma mk_env_exp_newer_cnf_extract :
  forall (i j : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uextr i j) e) te ->
      newer_than_cnf g' cs.
Proof.
  move=> i j e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- <- _ Hgm Hgt Hwf .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

(*
Lemma mk_env_exp_newer_cnf_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV.exp (w3 + w2 + w1)),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      newer_than_cnf g' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !newer_than_cnf_append.
  move: (mk_env_exp_newer_gen H0) => Hgg0 .
  (* newer_than_cnf g' cs0 *)
  by rewrite (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .
*)

Lemma mk_env_exp_newer_cnf_high :
    forall (n : nat) (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm)
           (s : SSAStore.t) (E : env) (g : generator) (m' : vm)
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uhigh n) e) te ->
      newer_than_cnf g' cs.
Proof.
  move=> n e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- <- _ Hgm Hgt Hwf .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

Lemma mk_env_exp_newer_cnf_low :
    forall (n : nat) (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Ulow n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Ulow n) e) te ->
      newer_than_cnf g' cs.
Proof.
  move=> n e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- <- _ Hgm Hgt Hwf .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

Lemma mk_env_exp_newer_cnf_zeroextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop (QFBV.Uzext n) e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uzext n) e) te ->
    newer_than_cnf g' cs.
Proof.
  move=> n e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- <- _ Hgm Hgt Hwf .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

Lemma mk_env_exp_newer_cnf_signextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Usext n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Usext n) e) te ->
      newer_than_cnf g' cs.
Proof.
  move=> n e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- <- _ Hgm Hgt Hwf .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

Lemma mk_env_exp_newer_cnf_ite :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> 
        QFBV.well_formed_bexp b te ->
        newer_than_cnf g' cs) ->
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
      forall (e0 : QFBV.exp),
        (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : word),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
            newer_than_vm g m ->
            newer_than_lit g lit_tt ->
            QFBV.well_formed_exp e0 te ->
            newer_than_cnf g' cs) ->
        forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp m s E g (QFBV.Eite b e e0) = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp (QFBV.Eite b e e0) te ->
          newer_than_cnf g' cs.
Proof.
  move=> c IHc e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmkc : (mk_env_bexp m s E g c) => [[[[mc Ec] gc] csc] lsc].
  case Hmke1 : (mk_env_exp mc s Ec gc e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ite E2 g2 lsc ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [/andP [Hwfc Hwf1] Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr csc *)
  move: (IHc _ _ _ _ _ _ _ _ _ _ Hmkc Hgm Hgt Hwfc) => Hgccc.
  move: (mk_env_bexp_newer_gen Hmkc) => Hggc.
  move: (mk_env_exp_newer_gen Hmke1) => Hgcg1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_ite_newer_gen Hmkr) => Hg2gr.
  move: (pos_leb_trans Hgcg1 Hg1g2) => Hgcg2 .
  move: (pos_leb_trans Hg1g2 Hg2gr) => Hg1gr .
  move: (pos_leb_trans Hgcg1 Hg1gr) => Hgcgr .
  move: (mk_env_bexp_newer_res Hmkc Hgm Hgt) => Hgclsc .
  move: (newer_than_lit_le_newer Hgclsc Hgcg2) => Hg2lsc {Hgclsc}.
  rewrite (newer_than_cnf_le_newer Hgccc Hgcgr) /= {Hgcgr}.
  (* newer_than_cnf gr cs1 *)
  move: (mk_env_bexp_newer_vm Hmkc Hgm) => Hg1m1.
  move: (newer_than_lit_le_newer Hgt Hggc) => Hgct.
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hg1m1 Hgct Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_res Hmke1 Hg1m1 Hgct) => Hg1l1 .
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1 {Hg1l1} .
  rewrite (newer_than_cnf_le_newer Hg1c1 Hg1gr) /= {Hg1gr} .
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hg1m1) => Hg2m2.
  move: (newer_than_lit_le_newer Hgct Hgcg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg2m2 Hg1t Hwf2) => Hg2c2.
  move: (mk_env_exp_newer_res Hmke2 Hg2m2 Hg1t) => Hg2l2 .
  rewrite (newer_than_cnf_le_newer Hg2c2 Hg2gr) /= .
  (* newer_than_cnf gr csr *)
  apply: (mk_env_ite_newer_cnf Hmkr (newer_than_lit_le_newer Hg1t Hg1g2) Hg2lsc Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_newer_cnf_false :
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Bfalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt ->
    QFBV.well_formed_bexp QFBV.Bfalse te ->
    newer_than_cnf g' cs.
Proof.
  move=> te m s E g m' E' g' cs lr /=. case=> _ _ <- <- _ Hnew_gm Hnew_gtt _. done.
Qed.

Lemma mk_env_bexp_newer_cnf_true :
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Btrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt ->
    QFBV.well_formed_bexp QFBV.Btrue te ->
    newer_than_cnf g' cs.
Proof.
  move=> te m s E g m' E' g' cs lr /=. case=> _ _ <- <- _ Hnew_gm Hnew_gtt _. done.
Qed.

Lemma mk_env_bexp_newer_cnf_eq :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Beq e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Beq e e0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_eq E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_eq_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_eq_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_ult :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bult e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bult e e0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_ult E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_ult_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_ult_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_ule :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bule e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bule e e0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_ule E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_ule_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_ule_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_ugt :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bugt e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bugt e e0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_ugt E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_ugt_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_ugt_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_uge :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buge e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Buge e e0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_uge E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_uge_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_uge_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_slt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bslt e1 e2) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_slt E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_slt_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_slt_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_sle :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsle e1 e2) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_sle E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_sle_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_sle_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_sgt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsgt e1 e2) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_sgt E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_sgt_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_sgt_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_sge :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsge e1 e2) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_sge E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_sge_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_sge_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_uaddo :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Buaddo e e0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_uaddo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_uaddo_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply : (mk_env_uaddo_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_usubo :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Busubo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Busubo e e0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_usubo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_usubo_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_usubo_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_umulo :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bumulo e e0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_umulo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_umulo_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply : (mk_env_umulo_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_saddo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsaddo e1 e2) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_saddo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_saddo_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply : (mk_env_saddo_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_ssubo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bssubo e1 e2) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_ssubo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_ssubo_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply : (mk_env_ssubo_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_smulo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsmulo e1 e2) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_smulo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_smulo_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply : (mk_env_smulo_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_lneg :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp b te ->
        newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Blneg b) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Blneg b) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e IH te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv: (mk_env_bexp m s E g e) => [[[[m1 E1] g1] cs1] lr1].
  case Hlneg: (mk_env_lneg E1 g1 lr1) => [[[oE og] ocs] olr].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt Hwf. rewrite newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH _ _ _ _ _ _ _ _ _ _ Henv Hnew_gm Hnew_gtt Hwf) => Hnew_g1cs1.
  move: (mk_env_lneg_newer_gen Hlneg) => H_g1og.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1og). move => {Hnew_g1cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_bexp_newer_res Henv Hnew_gm Hnew_gtt) => Hnew_g1lr1.
  exact: (mk_env_lneg_newer_cnf Hlneg Hnew_g1lr1).
Qed.


Lemma mk_env_bexp_newer_cnf_conj :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp b te ->
        newer_than_cnf g' cs) ->
    forall (b0 : QFBV.bexp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_bexp b0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bconj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bconj b b0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case Hconj: (mk_env_conj E2 g2 lr1 lr2)=> [[[oE og] ocs] olr].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt /= /andP [Hwf1 Hwf2]. rewrite !newer_than_cnf_cat.
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt Hwf1) => Hnew_g1cs1.
  move: (mk_env_bexp_newer_gen Henv2) => H_g1g2.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => {Hnew_g1cs1} Hnew_g2cs1.
  move: (mk_env_conj_newer_gen Hconj) => H_g2og.
  move: (newer_than_cnf_le_newer Hnew_g2cs1 H_g2og) => {Hnew_g2cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og cs2 *)
  move: (mk_env_bexp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (mk_env_bexp_newer_gen Henv1) => H_gg1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt Hwf2) => Hnew_g2cs2.
  move: (newer_than_cnf_le_newer Hnew_g2cs2 H_g2og) => {Hnew_g2cs2} Hnew_ogcs2.
  rewrite Hnew_ogcs2 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_bexp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1lr1.
  move: (newer_than_lit_le_newer Hnew_g1lr1 H_g1g2) => {Hnew_g1lr1} Hnew_g2lr1.
  move: (mk_env_bexp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2lr2.
  exact: (mk_env_conj_newer_cnf Hconj Hnew_g2lr1 Hnew_g2lr2).
Qed.

Lemma mk_env_bexp_newer_cnf_disj :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp b te ->
        newer_than_cnf g' cs) ->
    forall (b0 : QFBV.bexp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_bexp b0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bdisj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bdisj b b0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case Hdisj: (mk_env_disj E2 g2 lr1 lr2)=> [[[oE og] ocs] olr].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt /= /andP [Hwf1 Hwf2]. rewrite !newer_than_cnf_cat.
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt Hwf1) => Hnew_g1cs1.
  move: (mk_env_bexp_newer_gen Henv2) => H_g1g2.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => {Hnew_g1cs1} Hnew_g2cs1.
  move: (mk_env_disj_newer_gen Hdisj) => H_g2og.
  move: (newer_than_cnf_le_newer Hnew_g2cs1 H_g2og) => {Hnew_g2cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og cs2 *)
  move: (mk_env_bexp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (mk_env_bexp_newer_gen Henv1) => H_gg1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt Hwf2) => Hnew_g2cs2.
  move: (newer_than_cnf_le_newer Hnew_g2cs2 H_g2og) => {Hnew_g2cs2} Hnew_ogcs2.
  rewrite Hnew_ogcs2 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_bexp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1lr1.
  move: (newer_than_lit_le_newer Hnew_g1lr1 H_g1g2) => {Hnew_g1lr1} Hnew_g2lr1.
  move: (mk_env_bexp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2lr2.
  exact: (mk_env_disj_newer_cnf Hdisj Hnew_g2lr1 Hnew_g2lr2).
Qed.

Corollary mk_env_exp_newer_cnf :
  forall (e : QFBV.exp) te m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp e te ->
    newer_than_cnf g' cs
  with
    mk_env_bexp_newer_cnf :
      forall e te m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp e te ->
        newer_than_cnf g' cs.
Proof.
  (* mk_env_exp_newer_cnf *)
  elim .
  - exact: mk_env_exp_newer_cnf_var .
  - exact: mk_env_exp_newer_cnf_const .
  - elim .
    + exact: mk_env_exp_newer_cnf_not .
    + exact: mk_env_exp_newer_cnf_neg .
    + exact: mk_env_exp_newer_cnf_extract .
    + exact: mk_env_exp_newer_cnf_high .
    + exact: mk_env_exp_newer_cnf_low .
    + exact: mk_env_exp_newer_cnf_zeroextend .
    + exact: mk_env_exp_newer_cnf_signextend .
  - elim .
    + exact: mk_env_exp_newer_cnf_and .
    + exact: mk_env_exp_newer_cnf_or .
    + exact: mk_env_exp_newer_cnf_xor .
    + exact: mk_env_exp_newer_cnf_add .
    + exact: mk_env_exp_newer_cnf_sub .
    + exact: mk_env_exp_newer_cnf_mul .
    + exact: mk_env_exp_newer_cnf_mod .
    + exact: mk_env_exp_newer_cnf_srem .
    + exact: mk_env_exp_newer_cnf_smod .
    + exact: mk_env_exp_newer_cnf_shl .
    + exact: mk_env_exp_newer_cnf_lshr .
    + exact: mk_env_exp_newer_cnf_ashr .
    + exact: mk_env_exp_newer_cnf_concat .
  - move => b;
      move : b (mk_env_bexp_newer_cnf b);
      exact: mk_env_exp_newer_cnf_ite .
  (* mk_env_bexp_newer_cnf *)
  elim .
  - exact: mk_env_bexp_newer_cnf_false .
  - exact: mk_env_bexp_newer_cnf_true .
  - elim; move => e0 e1;
          move : e0 (mk_env_exp_newer_cnf e0)
                 e1 (mk_env_exp_newer_cnf e1) .
    + exact: mk_env_bexp_newer_cnf_eq .
    + exact: mk_env_bexp_newer_cnf_ult .
    + exact: mk_env_bexp_newer_cnf_ule .
    + exact: mk_env_bexp_newer_cnf_ugt .
    + exact: mk_env_bexp_newer_cnf_uge .
    + exact: mk_env_bexp_newer_cnf_slt .
    + exact: mk_env_bexp_newer_cnf_sle .
    + exact: mk_env_bexp_newer_cnf_sgt .
    + exact: mk_env_bexp_newer_cnf_sge .
    + exact: mk_env_bexp_newer_cnf_uaddo .
    + exact: mk_env_bexp_newer_cnf_usubo .
    + exact: mk_env_bexp_newer_cnf_umulo .
    + exact: mk_env_bexp_newer_cnf_saddo .
    + exact: mk_env_bexp_newer_cnf_ssubo .
    + exact: mk_env_bexp_newer_cnf_smulo .
  - exact: mk_env_bexp_newer_cnf_lneg .
  - exact: mk_env_bexp_newer_cnf_conj .
  - exact: mk_env_bexp_newer_cnf_disj .
Qed.
