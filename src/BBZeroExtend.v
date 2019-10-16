From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From BitBlasting Require Import QFBV CNF BBCommon.
From ssrlib Require Import ZAriths Tactics Bools Seqs.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_zeroextend ===== *)

Definition bit_blast_zeroextend n (g: generator) (ls: word) : generator * cnf * word :=
  (g, [::], cat ls (nseq n lit_ff)) .

Definition mk_env_zeroextend n (E: env) (g: generator) (ls: word) : env * generator * cnf * word :=
  (E, g, [::], cat ls (nseq n lit_ff)) .

Lemma bit_blast_zeroextend_correct n g bs E ls g' cs lrs :
  bit_blast_zeroextend n g ls = (g', cs, lrs) ->
  enc_bits E ls bs ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E lrs (zext n bs).
Proof.
  rewrite /bit_blast_zeroextend.
  case=> _ <- <- /= => Henc Hicnf.
  rewrite /zext /zeros.
  move: Henc (enc_bits_copy n (add_prelude_enc_bit_ff Hicnf)).
  exact: (enc_bits_cat).
Qed.

Lemma mk_env_zeroextend_is_bit_blast_zeroextend n E g ls E' g' cs lrs :
    mk_env_zeroextend n E g ls = (E', g', cs, lrs) ->
    bit_blast_zeroextend n g ls = (g', cs, lrs).
Proof.
  rewrite /mk_env_zeroextend /bit_blast_zeroextend.
  intros; dcase_hyps.
    by rewrite H0 H1 H2.
Qed.

Lemma mk_env_zeroextend_newer_gen n E g ls E' g' cs lrs :
    mk_env_zeroextend n E g ls = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  rewrite /mk_env_zeroextend.
  intros. dcase_hyps; subst.
  exact /Pos.leb_refl.
Qed.

Lemma mk_env_zeroextend_newer_res n E g ls E' g' cs lrs :
    mk_env_zeroextend n E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    newer_than_lits g' lrs.
Proof.
  case=> _ <- _ <- .
  rewrite -newer_than_lit_neg => Hg'ff .
  move=> Hgls.
  rewrite newer_than_lits_cat.
  rewrite -[neg_lit lit_tt]/lit_ff in Hg'ff .
  rewrite (newer_than_lits_copy n Hg'ff) .
  by rewrite Hgls.
Qed.

Lemma mk_env_zeroextend_newer_cnf n E g ls E' g' cs lrs :
    mk_env_zeroextend n E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    newer_than_cnf g' cs.
Proof.
    by case=> _ <- <- _ .
Qed.

Lemma mk_env_zeroextend_preserve n E g ls E' g' cs lrs :
    mk_env_zeroextend n E g ls = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
    by case=> <- _ _ _ .
Qed.

Lemma mk_env_zeroextend_sat n E g ls E' g' cs lrs :
    mk_env_zeroextend n E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    interp_cnf E' cs.
Proof.
    by case=> <- _ <- _ .
Qed.
