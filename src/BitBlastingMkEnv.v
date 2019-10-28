From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport AdhereConform
     BitBlastingDef .

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* = mk_env_exp_is_bit_blast_exp and mk_env_bexp_is_bit_blast_bexp = *)

Lemma mk_env_exp_is_bit_blast_exp_var :
  forall t (te : SSATE.env) (m : vm) (E : env) (g : generator)
         (s : SSAStore.t) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    AdhereConform.conform_exp (QFBV.Evar t) s te ->
    QFBV.well_formed_exp (QFBV.Evar t) te ->
    mk_env_exp m s E g (QFBV.Evar t) = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g (QFBV.Evar t) = (m', g', cs, lrs).
Proof.
  rewrite /= .
  move => t te m E g s m' E' g' cs lrs Hsize _ .
  case : (SSAVM.find t m) .
  - move => a; case => <- _ <- <- <- // .
  - dcase (mk_env_var E g (SSAStore.acc t s) t) => [[[[E'0 g'0] cs0] rs] Hmkr] .
    dcase (bit_blast_var te g t) => [[[g'1 cs1] rs0] Hbst] .
    case => <- _ <- <- <- .
    rewrite (mk_env_var_is_bit_blast_var (Logic.eq_sym (eqP Hsize)) Hmkr) in Hbst .
    move : Hbst; case => <- <- <- // .
Qed.

Lemma mk_env_exp_is_bit_blast_exp_const :
  forall (b : bits) (te : SSATE.env) (m : vm) (E : env) (g : generator)
         (s : SSAStore.t) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    AdhereConform.conform_exp (QFBV.Econst b) s te ->
    QFBV.well_formed_exp (QFBV.Econst b) te ->
    mk_env_exp m s E g (QFBV.Econst b) = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g (QFBV.Econst b) = (m', g', cs, lrs).
Proof.
  rewrite /=; move => b te m E g s m' E' g' cs lrs Hcf _ .
  case => <- _ <- <- <- // .
Qed.

Lemma mk_env_exp_is_bit_blast_exp_not :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      AdhereConform.conform_exp (QFBV.Eunop QFBV.Unot e1) s te ->
      QFBV.well_formed_exp (QFBV.Eunop QFBV.Unot e1) te ->
      mk_env_exp m s E g (QFBV.Eunop QFBV.Unot e1) = (m', E', g', cs, lrs) ->
      bit_blast_exp te m g (QFBV.Eunop QFBV.Unot e1) = (m', g', cs, lrs).
Proof.
  move=> e1 IH1 te m E g s m' E' g' cs lrs /= Hcf Hwf .
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case => <- _ <- <- <- .
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf Hwf Hmke1).
  by rewrite (mk_env_not_is_bit_blast_not Hmkr).
Qed.

Lemma mk_env_exp_is_bit_blast_exp_and :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e2 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        AdhereConform.conform_exp (QFBV.Ebinop QFBV.Band e1 e2) s te ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Band e1 e2) te ->
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Band e1 e2) = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g (QFBV.Ebinop QFBV.Band e1 e2) = (m', g', cs, lrs).
Proof.
  move=> e1 IH1 e2 IH2 te m E g s m' E' g' cs lrs /andP [Hcf1 Hcf2] /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1)
          (IH2 _ _ _ _ _ _ _ _ _ _ Hcf2 Hwf2 Hmke2) .
  by rewrite (mk_env_and_is_bit_blast_and Hmkr).
Qed.

Lemma mk_env_exp_is_bit_blast_exp_or :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e1 s te ->
          QFBV.well_formed_exp e1 te ->
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bor e0 e1) s te ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bor e0 e1) te ->
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', E', g', cs, lrs) ->
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', g', cs, lrs).
Proof.
  move => e0 IH0 e1 IH1 te m E g s m' E' g' cs lrs /andP [Hcf0 Hcf1] /= /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1] .
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2] .
  case Hmkr  : (mk_env_or E2 g2 ls1 ls2) => [[[E'0 g'0] cs0] ls] .
  case => <- _ <- <- <- .
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0) .
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1) .
  rewrite (mk_env_or_is_bit_blast_or Hmkr). reflexivity.
Qed .

Lemma mk_env_exp_is_bit_blast_exp_xor :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e2 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bxor e1 e2) s te ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bxor e1 e2) te ->
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', g', cs, lrs).
Proof.
  move=> e1 IH1 e2 IH2 te m E g s m' E' g' cs lrs /andP [Hcf1 Hcf2] /= /andP [/andP [Hwf1 Hwf2] _] .
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1) (IH2 _ _ _ _ _ _ _ _ _ _ Hcf2 Hwf2 Hmke2).
  by rewrite (mk_env_xor_is_bit_blast_xor Hmkr).
Qed.

Lemma mk_env_exp_is_bit_blast_exp_neg :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      AdhereConform.conform_exp (QFBV.Eunop QFBV.Uneg e1) s te ->
      QFBV.well_formed_exp (QFBV.Eunop QFBV.Uneg e1) te ->
    mk_env_exp m s E g (QFBV.Eunop QFBV.Uneg e1) = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g (QFBV.Eunop QFBV.Uneg e1) = (m', g', cs, lrs).
Proof.
  move=> e1 IH1 te m E g s m' E' g' cs lrs /= Hcf Hwf .
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf Hwf Hmke1).
  by rewrite (mk_env_neg_is_bit_blast_neg Hmkr).
Qed.

Lemma mk_env_exp_is_bit_blast_exp_add :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        AdhereConform.conform_exp (QFBV.Ebinop QFBV.Badd e e0) s te ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Badd e e0) te ->
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Badd e e0) = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g (QFBV.Ebinop QFBV.Badd e e0) = (m', g', cs, lrs).
Proof.
  move=> e0 IH0 e1 IH1 te m E g s m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_add E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  by rewrite (mk_env_add_is_bit_blast_add Hmkr).
Qed.

Lemma mk_env_exp_is_bit_blast_exp_sub :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bsub e e0) s te ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsub e e0) te ->
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsub e e0) = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g (QFBV.Ebinop QFBV.Bsub e e0) = (m', g', cs, lrs).
Proof.
  move=> e0 IH0 e1 IH1 te m E g s m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sub E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  by rewrite (mk_env_sub_is_bit_blast_sub Hmkr).
Qed.

Lemma mk_env_exp_is_bit_blast_exp_mul :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bmul e e0) s te ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bmul e e0) te ->
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmul e e0) = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g (QFBV.Ebinop QFBV.Bmul e e0) = (m', g', cs, lrs).
Proof.
  move=> e0 IH0 e1 IH1 te m E g s m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_mul E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  by rewrite (mk_env_mul_is_bit_blast_mul Hmkr).
Qed.

Lemma mk_env_exp_is_bit_blast_exp_mod :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
  forall (e0 : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e0 s te ->
        QFBV.well_formed_exp e0 te ->
        mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
  forall (te : SSATE.env) (m : vm) (E : env)
         (g : generator) (s : SSAStore.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : word),
    AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bmod e e0) s te ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bmod e e0) te ->
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmod e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bmod e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_srem :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
  forall (e0 : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e0 s te ->
        QFBV.well_formed_exp e0 te ->
        mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
  forall (te : SSATE.env) (m : vm) (E : env)
         (g : generator) (s : SSAStore.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : word),
    AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bsrem e e0) s te ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsrem e e0) te ->
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_smod :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
  forall (e0 : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e0 s te ->
        QFBV.well_formed_exp e0 te ->
        mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
  forall (te : SSATE.env) (m : vm) (E : env)
         (g : generator) (s : SSAStore.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : word),
    AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bsmod e e0) s te ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsmod e e0) te ->
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_shl :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e1 s te ->
          QFBV.well_formed_exp e1 te ->
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bshl e0 e1) s te ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bshl e0 e1) te ->
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', E', g', cs, lrs) ->
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', g', cs, lrs).
Proof.
  move=> e0 IH0 e1 IH1 te m E g s m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_shl E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  by rewrite (mk_env_shl_is_bit_blast_shl Hmkr).
Qed .

Lemma mk_env_exp_is_bit_blast_exp_lshr :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e1 s te ->
          QFBV.well_formed_exp e1 te ->
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Blshr e0 e1) s te ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Blshr e0 e1) te ->
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', E', g', cs, lrs) ->
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', g', cs, lrs).
Proof.
  move=> e0 IH0 e1 IH1 te m E g s m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_lshr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  by rewrite (mk_env_lshr_is_bit_blast_lshr Hmkr).
Qed .

Lemma mk_env_exp_is_bit_blast_exp_ashr :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e1 s te ->
          QFBV.well_formed_exp e1 te ->
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bashr e0 e1) s te ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bashr e0 e1) te ->
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', E', g', cs, lrs) ->
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', g', cs, lrs).
Proof.
  move=> e0 IH0 e1 IH1 te m E g s m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ashr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  by rewrite (mk_env_ashr_is_bit_blast_ashr Hmkr).
Qed .

Lemma mk_env_exp_is_bit_blast_exp_concat :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e1 s te ->
          QFBV.well_formed_exp e1 te ->
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bconcat e0 e1) s te ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bconcat e0 e1) te ->
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', g', cs, lrs).
Proof.
  move=> e0 IH0 e1 IH1 te m E g s m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1) //.
Qed .

Lemma mk_env_exp_is_bit_blast_exp_extract :
  forall (i j : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e s te ->
          QFBV.well_formed_exp e te ->
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      AdhereConform.conform_exp (QFBV.Eunop (QFBV.Uextr i j) e) s te ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uextr i j) e) te ->
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', E', g', cs, lrs) ->
      bit_blast_exp te m g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', g', cs, lrs).
Proof.
  move=> i j e0 IH0 te m E g s m' E' g' cs lrs /= Hcf Hwf .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf Hwf Hmke0) // .
Qed .

(*
Lemma mk_env_exp_is_bit_blast_exp_slice :
  forall (w1 w2 w3 : nat),
    forall (e : exp (w3 + w2 + w1)),
      (forall (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      bit_blast_exp m g (QFBV64.bvSlice w1 w2 w3 e) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
    by rewrite (H _ _ _ _ _ _ _ _ _ H0) .
Qed .
*)

Lemma mk_env_exp_is_bit_blast_exp_high :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e s te ->
          QFBV.well_formed_exp e te ->
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm)
         (E : env) (g : generator) (s : SSAStore.t) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      AdhereConform.conform_exp (QFBV.Eunop (QFBV.Uhigh n) e) s te ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uhigh n) e) te ->
    mk_env_exp m s E g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', g', cs, lrs).
Proof.
  move=> n e0 IH0 te m E g s m' E' g' cs lrs /= Hcf Hwf .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf Hwf Hmke0) //.
Qed .

Lemma mk_env_exp_is_bit_blast_exp_low :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e s te ->
          QFBV.well_formed_exp e te ->
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      AdhereConform.conform_exp (QFBV.Eunop (QFBV.Ulow n) e) s te ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Ulow n) e) te ->
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Ulow n) e) = (m', E', g', cs, lrs) ->
      bit_blast_exp te m g (QFBV.Eunop (QFBV.Ulow n) e) = (m', g', cs, lrs).
Proof.
  move=> n e0 IH0 te m E g s m' E' g' cs lrs /= Hcf Hwf0 .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf Hwf0 Hmke0) // .
Qed .

Lemma mk_env_exp_is_bit_blast_exp_zeroextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e s te ->
          QFBV.well_formed_exp e te ->
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (E : env)
             (g : generator) (s : SSAStore.t) (m' : vm) (E' : env)
             (g' : generator) (cs : cnf) (lrs : word),
        AdhereConform.conform_exp (QFBV.Eunop (QFBV.Uzext n) e) s te ->
        QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uzext n) e) te ->
        mk_env_exp m s E g (QFBV.Eunop (QFBV.Uzext n) e) = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g (QFBV.Eunop (QFBV.Uzext n) e) = (m', g', cs, lrs).
Proof.
  move=> n e0 IH0 te m E g s m' E' g' cs lrs /= Hcf Hwf0 .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf Hwf0 Hmke0) //.
Qed .

Lemma mk_env_exp_is_bit_blast_exp_signextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e s te ->
          QFBV.well_formed_exp e te ->
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env)
         (g : generator) (s : SSAStore.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : word),
      AdhereConform.conform_exp (QFBV.Eunop (QFBV.Usext n) e) s te ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Usext n) e) te ->
    mk_env_exp m s E g (QFBV.Eunop (QFBV.Usext n) e) = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g (QFBV.Eunop (QFBV.Usext n) e) = (m', g', cs, lrs).
Proof.
  move=> n e0 IH0 te m E g s m' E' g' cs lrs /= Hcf Hwf0 .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf Hwf0 Hmke0) //.
Qed .

Lemma mk_env_exp_is_bit_blast_exp_ite :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        AdhereConform.conform_bexp b s te ->
        QFBV.well_formed_bexp b te ->
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g b = (m', g', cs, lr)) ->
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e0 s te ->
        QFBV.well_formed_exp e0 te ->
        mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      AdhereConform.conform_exp (QFBV.Eite b e e0) s te ->
      QFBV.well_formed_exp (QFBV.Eite b e e0) te ->
      mk_env_exp m s E g (QFBV.Eite b e e0) = (m', E', g', cs, lrs) ->
      bit_blast_exp te m g (QFBV.Eite b e e0) = (m', g', cs, lrs).
Proof.
  move=> c IHc e0 IH0 e1 IH1 te m E g s m' E' g' cs lrs /= /andP [/andP [Hcfc Hcf0] Hcf1] /andP [/andP [/andP [Hwfc Hwf0] Hwf1] _] .
  case Hmkec : (mk_env_bexp m s E g c) => [[[[mc Ec] gc] csc] lc].
  case Hmke0 : (mk_env_exp mc s Ec gc e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ite E2 g2 lc ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IHc _ _ _ _ _ _ _ _ _ _ Hcfc Hwfc Hmkec).
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  by rewrite (mk_env_ite_is_bit_blast_ite Hmkr).
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_false :
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    AdhereConform.conform_bexp QFBV.Bfalse s te ->
    QFBV.well_formed_bexp QFBV.Bfalse te ->
    mk_env_bexp m s E g QFBV.Bfalse = (m', E', g', cs, lr) ->
    bit_blast_bexp te m g QFBV.Bfalse = (m', g', cs, lr).
Proof.
  move => te m s E g m' E' g' cs lr Hcf _ .
  rewrite /=; case => <- _ <- <- <- // .
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_true :
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    AdhereConform.conform_bexp QFBV.Btrue s te ->
    QFBV.well_formed_bexp QFBV.Btrue te ->
    mk_env_bexp m s E g QFBV.Btrue = (m', E', g', cs, lr) ->
    bit_blast_bexp te m g QFBV.Btrue = (m', g', cs, lr).
Proof.
  move => te m s E g m' E' g' cs lr Hcf _ .
  rewrite /=; case => <- _ <- <- <- // .
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_eq :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Beq e e0) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Beq e e0) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Beq e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Beq e e0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_eq E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  by rewrite (mk_env_eq_is_bit_blast_eq Hmkr).
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_ult :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bult e e0) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bult e e0) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bult e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bult e e0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ult E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  by rewrite (mk_env_ult_is_bit_blast_ult Hmkr).
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_ule :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bule e e0) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bule e e0) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bule e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bule e e0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ule E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_ule_is_bit_blast_ule Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_ugt :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bugt e e0) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bugt e e0) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bugt e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bugt e e0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ugt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_ugt_is_bit_blast_ugt Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_uge :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Buge e e0) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Buge e e0) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buge e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Buge e e0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_uge_is_bit_blast_uge Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_slt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e2 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bslt e1 e2) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bslt e1 e2) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_slt_is_bit_blast_slt Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_sle :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e2 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsle e1 e2) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsle e1 e2) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_sle_is_bit_blast_sle Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_sgt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e2 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsgt e1 e2) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsgt e1 e2) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_sgt_is_bit_blast_sgt Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_sge :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e2 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsge e1 e2) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsge e1 e2) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_sge_is_bit_blast_sge Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_uaddo :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Buaddo e e0) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Buaddo e e0) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uaddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_uaddo_is_bit_blast_uaddo Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_usubo :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Busubo e e0) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Busubo e e0) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Busubo e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Busubo e e0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_usubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_usubo_is_bit_blast_usubo Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_umulo :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bumulo e e0) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bumulo e e0) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_umulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_umulo_is_bit_blast_umulo Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_saddo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e2 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsaddo e1 e2) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsaddo e1 e2) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_saddo_is_bit_blast_saddo Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_ssubo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e2 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bssubo e1 e2) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bssubo e1 e2) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_ssubo_is_bit_blast_ssubo Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_smulo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e2 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsmulo e1 e2) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsmulo e1 e2) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_smulo_is_bit_blast_smulo Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_lneg :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp b s te ->
        QFBV.well_formed_bexp b te ->
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g b = (m', g', cs, lr)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Blneg b) s te ->
        QFBV.well_formed_bexp (QFBV.Blneg b) te ->
        mk_env_bexp m s E g (QFBV.Blneg b) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Blneg b) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 te m s E g m' E' g' cs lrs /= Hcf Hwf0 .
  case Hmke0 : (mk_env_bexp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf Hwf0 Hmke0) // .
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_conj :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp b s te ->
        QFBV.well_formed_bexp b te ->
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g b = (m', g', cs, lr)) ->
    forall (b0 : QFBV.bexp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          AdhereConform.conform_bexp b0 s te ->
          QFBV.well_formed_bexp b0 te ->
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          bit_blast_bexp te m g b0 = (m', g', cs, lr)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bconj b b0) s te ->
        QFBV.well_formed_bexp (QFBV.Bconj b b0) te ->
        mk_env_bexp m s E g (QFBV.Bconj b b0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bconj b b0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [Hwf0 Hwf1] .
  case Hmke0 : (mk_env_bexp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_bexp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_disj :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp b s te ->
        QFBV.well_formed_bexp b te ->
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g b = (m', g', cs, lr)) ->
    forall (b0 : QFBV.bexp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          AdhereConform.conform_bexp b0 s te ->
          QFBV.well_formed_bexp b0 te ->
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          bit_blast_bexp te m g b0 = (m', g', cs, lr)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bdisj b b0) s te ->
        QFBV.well_formed_bexp (QFBV.Bdisj b b0) te ->
        mk_env_bexp m s E g (QFBV.Bdisj b b0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bdisj b b0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [Hwf0 Hwf1] .
  case Hmke0 : (mk_env_bexp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_bexp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1) //.
Qed.

Corollary mk_env_exp_is_bit_blast_exp :
  forall (e : QFBV.exp) te m E g s m' E' g' cs lrs,
    AdhereConform.conform_exp e s te ->
    QFBV.well_formed_exp e te ->
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g e = (m', g', cs, lrs)
  with
    mk_env_bexp_is_bit_blast_bexp :
      forall e te m s E g m' E' g' cs lr,
        AdhereConform.conform_bexp e s te ->
        QFBV.well_formed_bexp e te ->
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g e = (m', g', cs, lr).
Proof.
  (* mk_env_exp_is_bit_blast_exp *)
  elim .
  - move => v; apply : mk_env_exp_is_bit_blast_exp_var .
  - move => b; apply : mk_env_exp_is_bit_blast_exp_const .
  - elim .
    + apply : mk_env_exp_is_bit_blast_exp_not .
    + apply : mk_env_exp_is_bit_blast_exp_neg .
    + apply : mk_env_exp_is_bit_blast_exp_extract .
    + apply : mk_env_exp_is_bit_blast_exp_high .
    + apply : mk_env_exp_is_bit_blast_exp_low .
    + apply : mk_env_exp_is_bit_blast_exp_zeroextend .
    + apply : mk_env_exp_is_bit_blast_exp_signextend .
  - elim .
    + apply : mk_env_exp_is_bit_blast_exp_and .
    + apply : mk_env_exp_is_bit_blast_exp_or .
    + apply : mk_env_exp_is_bit_blast_exp_xor .
    + apply : mk_env_exp_is_bit_blast_exp_add .
    + apply : mk_env_exp_is_bit_blast_exp_sub .
    + apply : mk_env_exp_is_bit_blast_exp_mul .
    + apply : mk_env_exp_is_bit_blast_exp_mod .
    + apply : mk_env_exp_is_bit_blast_exp_srem .
    + apply : mk_env_exp_is_bit_blast_exp_smod .
    + apply : mk_env_exp_is_bit_blast_exp_shl .
    + apply : mk_env_exp_is_bit_blast_exp_lshr .
    + apply : mk_env_exp_is_bit_blast_exp_ashr .
    + apply : mk_env_exp_is_bit_blast_exp_concat .
  - move => b .
    move : (mk_env_bexp_is_bit_blast_bexp b) .
    apply : mk_env_exp_is_bit_blast_exp_ite .
  (* mk_env_bexp_is_bit_blast_bexp *)
  elim .
  - apply: mk_env_bexp_is_bit_blast_bexp_false.
  - apply: mk_env_bexp_is_bit_blast_bexp_true.
  - elim;
      move => e e0;
      move :  e (mk_env_exp_is_bit_blast_exp e)
             e0 (mk_env_exp_is_bit_blast_exp e0) .
    + apply : mk_env_bexp_is_bit_blast_bexp_eq .
    + apply : mk_env_bexp_is_bit_blast_bexp_ult .
    + apply : mk_env_bexp_is_bit_blast_bexp_ule .
    + apply : mk_env_bexp_is_bit_blast_bexp_ugt .
    + apply : mk_env_bexp_is_bit_blast_bexp_uge .
    + apply : mk_env_bexp_is_bit_blast_bexp_slt .
    + apply : mk_env_bexp_is_bit_blast_bexp_sle .
    + apply : mk_env_bexp_is_bit_blast_bexp_sgt .
    + apply : mk_env_bexp_is_bit_blast_bexp_sge .
    + apply : mk_env_bexp_is_bit_blast_bexp_uaddo .
    + apply : mk_env_bexp_is_bit_blast_bexp_usubo .
    + apply : mk_env_bexp_is_bit_blast_bexp_umulo .
    + apply : mk_env_bexp_is_bit_blast_bexp_saddo .
    + apply : mk_env_bexp_is_bit_blast_bexp_ssubo .
    + apply : mk_env_bexp_is_bit_blast_bexp_smulo .
  - apply : mk_env_bexp_is_bit_blast_bexp_lneg .
  - apply : mk_env_bexp_is_bit_blast_bexp_conj .
  - apply : mk_env_bexp_is_bit_blast_bexp_disj .
Qed.

