
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_zeroextend ===== *)

Definition bit_blast_zeroextend w n (g: generator) (ls : w.-tuple literal) : generator * cnf * (w + n).-tuple literal :=
  (g, [::], cat_tuple ls (nseq_tuple n lit_ff)) .

Definition mk_env_zeroextend w n (E : env) (g : generator) (ls : w.-tuple literal) : env * generator * cnf * (w + n).-tuple literal :=
  (E, g, [::], cat_tuple ls (nseq_tuple n lit_ff)) .

Lemma bit_blast_zeroextend_correct :
  forall w n (bs : BITS w) E ls cs,
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E (cat_tuple ls (nseq_tuple n lit_ff)) (zeroExtend n bs) .
Proof.
  move => w n bs E ls cs Hlsbs Hprelude .
  rewrite /zeroExtend /zero .
  move: (enc_bit_copy n (add_prelude_enc_bit_ff Hprelude)) Hlsbs .
  rewrite /copy /catB .
  apply: enc_bits_concat .
Qed .
