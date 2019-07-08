
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon.
From ssrlib Require Import Var.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_high ===== *)

Fixpoint get_high_aux {wh} wl : (wl+wh).-tuple literal -> wh.-tuple literal :=
  if wl is _.+1 then
    fun ls => let: (ls', _) := eta_expand (splitlsb ls) in
              get_high_aux ls'
  else
    fun ls => ls .

Definition bit_blast_high wh wl (g: generator) (ls : (wl+wh).-tuple literal) : generator * cnf * wh.-tuple literal :=
  (g, [::], @get_high_aux wh wl ls) .

Definition mk_env_high wh wl (E : env) (g : generator) (ls : (wl+wh).-tuple literal) : env * generator * cnf * wh.-tuple literal :=
  (E, g, [::], @get_high_aux wh wl ls) .

Lemma bit_blast_high_correct :
  forall wh wl (bs : BITS (wl+wh)) E ls cs,
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E (get_high_aux ls) (high wh bs) .
Proof.
  move => wh wl bs E ls cs Hlsbs Hinterp .
  move : wl ls bs Hlsbs .
  elim .
  - move => ls bs Hlsbs .
    by rewrite /get_high_aux /high .
  - move => n IH ls bs Hlsbs .
    apply: IH .
    rewrite /splitlsb /= .
    by apply enc_bits_behead .
Qed .

Lemma newer_than_lits_get_high_aux :
  forall wh wl g (ls : (wl + wh).-tuple literal),
    newer_than_lits g ls -> newer_than_lits g (get_high_aux ls) .
Proof .
  move => wh .
  elim .
  - move => g ls Hgls .
    by rewrite /get_high_aux /= .
  - move => n IH g ls Hgls .
    apply IH .
    rewrite /splitlsb /= .
    by apply: newer_than_lits_behead .
Qed .
