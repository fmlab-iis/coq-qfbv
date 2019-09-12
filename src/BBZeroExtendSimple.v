From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNFSimple BBCommonSimple.
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

Lemma mk_env_zeroextend_is_bit_blast_zeroextend :
  forall w n E g E' g' (ls:w.-tuple literal) cs lrs,
    mk_env_zeroextend n E g ls = (E', g', cs, lrs) ->
    bit_blast_zeroextend n g ls = (g', cs, lrs).
Proof.
  rewrite /mk_env_zeroextend /bit_blast_zeroextend.
  intros; dcase_hyps.
    by rewrite H0 H1 H2.
Qed.

Lemma mk_env_zeroextend_newer_gen:
  forall w n E g E' g' (ls:w.-tuple literal) cs lrs,
    mk_env_zeroextend n E g ls = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  rewrite /mk_env_zeroextend.
  intros. dcase_hyps; subst.
  exact /Pos.leb_refl.
Qed.

Lemma mk_env_zeroextend_newer_res :
  forall w n E g E' g' (ls:w.-tuple literal) cs lrs,
    mk_env_zeroextend n E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    newer_than_lits g' lrs.
Proof.
  intros. case :(H) => _ <- _ <- .
  move:(H0).
  rewrite -newer_than_lit_neg => Hg'ff .
  rewrite newer_than_lits_append .
  rewrite -[neg_lit lit_tt]/lit_ff in Hg'ff .
  rewrite (newer_than_lits_nseq_lit n Hg'ff) .
  by rewrite H1.
Qed.

Lemma mk_env_zeroextend_newer_cnf :
  forall w n E g E' g' (ls:w.-tuple literal) cs lrs,
    mk_env_zeroextend n E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    newer_than_cnf g' cs.
Proof.
  intros.
    by case: H => _ <- <- _ .
Qed.

Lemma mk_env_zeroextend_preserve :
  forall w n E g E' g' (ls:w.-tuple literal) cs lrs,
    mk_env_zeroextend n E g ls = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  intros.
    by case: H => <- _ _ _ .
Qed.

Lemma mk_env_zeroextend_sat :
  forall w n E g E' g' (ls:w.-tuple literal) cs lrs,
    mk_env_zeroextend n E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    interp_cnf E' cs.
Proof.
  intros.
    by case: H => <- _ <- _ .
Qed.
