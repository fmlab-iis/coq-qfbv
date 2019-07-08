
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_signextend ===== *)

Definition bit_blast_signextend w n (g: generator) (ls : (w.+1).-tuple literal) : generator * cnf * (w.+1 + n).-tuple literal :=
  (g, [::], cat_tuple ls (nseq_tuple n (last lit_ff ls))) .

Definition mk_env_signextend w n (E : env) (g : generator) (ls : (w.+1).-tuple literal) : env * generator * cnf * (w.+1 + n).-tuple literal :=
  (E, g, [::], cat_tuple ls (nseq_tuple n (last lit_ff ls))) .

Lemma bit_blast_signextend_correct :
  forall w n (bs : BITS w.+1) E ls cs,
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E (cat_tuple ls (nseq_tuple n (last lit_ff ls))) (signExtend n bs) .
Proof.
  move => w n bs E ls cs Hlsbs Hprelude .
  rewrite /signExtend /msb /catB /copy .
  move: (enc_bits_nseq n (enc_bits_last false lit_ff Hlsbs)) => Hlastlsbs .
  exact: (enc_bits_concat Hlastlsbs Hlsbs) .
Qed .
