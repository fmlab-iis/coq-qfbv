
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNFSimple BBCommonSimple.
From ssrlib Require Import Var.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_concat ===== *)

Definition bit_blast_concat w0 w1 (g: generator) (ls0 : w0.-tuple literal) (ls1 : w1.-tuple literal) : generator * cnf * (w1 + w0).-tuple literal :=
  (g, [::], cat_tuple ls1 ls0) .

Definition mk_env_concat w0 w1 (E : env) (g : generator) (ls0 : w0.-tuple literal) (ls1 : w1.-tuple literal) : env * generator * cnf * (w1 + w0).-tuple literal :=
  (E, g, [::], cat_tuple ls1 ls0) .

Lemma bit_blast_concat_correct :
  forall w0 w1 (bs0 : BITS w0) (bs1 : BITS w1) E ls0 ls1,
    enc_bits E ls0 bs0 ->
    enc_bits E ls1 bs1 ->
    enc_bits E (cat_tuple ls1 ls0) (catB bs0 bs1).
Proof.
  move=> w0 w1 bs0 bs1 E ls0 ls1 H1 H2.
  exact: (enc_bits_concat H1 H2).
Qed.
