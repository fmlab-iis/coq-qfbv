
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon BBHigh BBLow.
From ssrlib Require Import Var.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_slice ===== *)

Definition bit_blast_slice w1 w2 w3 (g : generator) (ls : (w3+w2+w1).-tuple literal) : generator * cnf * w2.-tuple literal :=
  (g, [::], get_high_aux (get_low_aux ls)) .

Definition mk_env_slice w1 w2 w3 (E : env) (g : generator) (ls : (w3+w2+w1).-tuple literal) : env * generator * cnf * w2.-tuple literal :=
  (E, g, [::], get_high_aux (get_low_aux ls)) .

Lemma bit_blast_slice_correct :
  forall w1 w2 w3 (bs : BITS (w3+w2+w1)) E ls cs,
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E (get_high_aux (get_low_aux ls)) (slice w3 w2 w1 bs) .
Proof.
  move => w1 w2 w3 bs E ls cs Hlsbs Hinterp .
  rewrite /slice /= .
  move: (bit_blast_low_correct Hlsbs Hinterp) => Hlow .
  apply: (bit_blast_high_correct Hlow Hinterp) .
Qed .
