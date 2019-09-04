From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNFSimple BBCommonSimple.
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

Lemma mk_env_signextend_is_bit_blast_signextend :
  forall w n E g E' g' (ls:(w.+1).-tuple literal) cs lrs,
    mk_env_signextend n E g ls = (E', g', cs, lrs) ->
    bit_blast_signextend n g ls = (g', cs, lrs).
Proof.
  rewrite /mk_env_signextend /bit_blast_signextend.
  intros; dcase_hyps.
    by rewrite H0 H1 H2.
Qed.

Lemma mk_env_signextend_newer_gen:
  forall w n E g E' g' (ls:(w.+1).-tuple literal) cs lrs,
    mk_env_signextend n E g ls = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  rewrite /mk_env_signextend.
  intros. dcase_hyps; subst.
  exact /Pos.leb_refl.
Qed.

Lemma mk_env_signextend_newer_res :
  forall w n E g E' g' (ls:(w.+1).-tuple literal) cs lrs,
    mk_env_signextend n E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    newer_than_lits g' lrs.
Proof.
  intros. case :(H) => _ <- _ <- .
  move:(H0).
  rewrite -newer_than_lit_neg => Hg'ff .
  rewrite newer_than_lits_append .
  rewrite -[neg_lit lit_tt]/lit_ff in Hg'ff .
  rewrite H1 /=.
  apply newer_than_lits_nseq_lit.
  by apply: newer_than_lits_last.
Qed.

Lemma mk_env_signextend_newer_cnf :
  forall w n E g E' g' (ls:(w.+1).-tuple literal) cs lrs,
    mk_env_signextend n E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    newer_than_cnf g' cs.
Proof.
  intros.
    by case: H => _ <- <- _ .
Qed.

Lemma mk_env_signextend_preserve :
  forall w n E g E' g' (ls:(w.+1).-tuple literal) cs lrs,
    mk_env_signextend n E g ls = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  intros.
    by case: H => <- _ _ _ .
Qed.

Lemma mk_env_signextend_sat :
  forall w n E g E' g' (ls:(w.+1).-tuple literal) cs lrs,
    mk_env_signextend n E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    interp_cnf E' cs.
Proof.
  intros.
    by case: H => <- _ <- _ .
Qed.
