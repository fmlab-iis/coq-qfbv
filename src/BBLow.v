
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNFSimple BBCommon.
From ssrlib Require Import Var.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_low ===== *)

Fixpoint get_low_aux {wh} wl : (wl+wh).-tuple literal -> wl.-tuple literal :=
  if wl is _.+1 then
    fun ls => let: (ls', l') := eta_expand (splitlsb ls) in
              cons_tuple l' (get_low_aux ls')
  else
    fun _ => [tuple] .

Definition bit_blast_low wh wl (g: generator) (ls : (wl+wh).-tuple literal) : generator * cnf * wl.-tuple literal :=
  (g, [::], @get_low_aux wh wl ls) .

Definition mk_env_low wh wl (E : env) (g : generator) (ls : (wl+wh).-tuple literal) : env * generator * cnf * wl.-tuple literal :=
  (E, g, [::], @get_low_aux wh wl ls) .

Lemma bit_blast_low_correct :
  forall wh wl (bs : BITS (wl+wh)) E ls cs,
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E (get_low_aux ls) (low wl bs) .
Proof.
  move => wh .
  elim .
  - move => bs e ls cs Hlsbs _ .
    by rewrite /get_low_aux /low /= .
  - move => n IH bs E ls cs Hlsbs Hinterp .
    rewrite /= !theadCons !beheadCons /= .
    apply /andP; split .
    + by apply : enc_bits_thead .
    + apply: IH .
      * by apply : enc_bits_behead .
      * exact: Hinterp .
Qed .

Lemma newer_than_lits_get_low_aux :
  forall wh wl g (ls : (wl + wh).-tuple literal),
    newer_than_lits g ls -> newer_than_lits g (get_low_aux ls) .
Proof .
  move => wh .
  elim .
  - move => g ls Hgls .
    by rewrite /get_low_aux /= .
  - move => n IH g ls /= .
    rewrite (tuple_eta ls) newer_than_lits_cons => /andP [Hhd Htl] .
    apply /andP; split .
    + done .
    + rewrite beheadCons .
      by apply IH .
Qed .
