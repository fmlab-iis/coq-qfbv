
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import Var QFBV CNF BBCommon.
From ssrlib Require Import ZAriths Seqs Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* auxiliary lemmas *)

Lemma enc_bits_drop E n ls bs :
  enc_bits E ls bs -> enc_bits E (drop n ls) (drop n bs) .
Proof .
  move => Hlsbs .
  move : (enc_bits_size Hlsbs) => Hsize .
  move : ls bs Hsize Hlsbs n .
  apply : seq_ind2 => [|ls_hd bs_hd ls_tl bs_tl Hsize IH] .
  - by rewrite /= .
  - rewrite enc_bits_cons => /andP [Hlsbshd Hlsbstl] .
    case => [|n] .
    + by rewrite /= enc_bits_cons Hlsbshd Hlsbstl .
    + by rewrite /= (IH Hlsbstl) .
Qed .

Lemma newer_than_lits_drop g n ls :
  newer_than_lits g ls -> newer_than_lits g (drop n ls) .
Proof .
  elim : ls n => [|ls_hd ls_tl IH] n .
  - by rewrite /= .
  - rewrite newer_than_lits_cons => /andP [Hlshd Hlstl] .
    case : n => [|n] .
    + rewrite /=; apply /andP; split; assumption .
    + by rewrite /= (IH n) .
Qed .

(* ===== bit_blast_high ===== *)

Definition bit_blast_high g n ls : generator * cnf * word :=
  (g, [::], drop (size ls - n) ls ++ copy (n - size ls) lit_ff) .

Definition mk_env_high E g n ls : env * generator * cnf * word :=
  (E, g, [::], drop (size ls - n) ls ++ copy (n - size ls) lit_ff) .

Lemma bit_blast_high_correct E g n bs ls g' cs lrs :
  bit_blast_high g n ls = (g', cs, lrs) ->
  enc_bits E ls bs -> interp_cnf E (add_prelude cs) ->
  enc_bits E lrs (high n bs) .
Proof .
  rewrite /bit_blast_high /high; case => _ <- <- Hlsbs Hcnf .
  rewrite (enc_bits_size Hlsbs) /zeros /b0 enc_bits_cat; first done .
  - exact : (enc_bits_drop (size bs - n) Hlsbs) => Henc .
  - move : (add_prelude_enc_bit_ff Hcnf);
      apply : enc_bits_copy .
Qed .

Lemma mk_env_high_is_bit_blast_high E g n ls E' g' cs lrs :
  mk_env_high E g n ls = (E', g', cs, lrs) ->
  bit_blast_high g n ls = (g', cs, lrs) .
Proof .
  by rewrite /mk_env_high /bit_blast_high; case => _ <- <- <- .
Qed .

Lemma mk_env_high_newer_gen E g n ls E' g' cs lrs :
  mk_env_high E g n ls = (E', g', cs, lrs) -> (g <=? g')%positive .
Proof .
  rewrite /mk_env_high; by t_auto_newer .
Qed .

Lemma mk_env_high_newer_res E g n ls E' g' cs lrs :
  mk_env_high E g n ls = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls -> newer_than_lits g' lrs .
Proof .
  rewrite /mk_env_high; case => _ <- _ <- Htt Hls .
  rewrite newer_than_lits_cat .
  apply /andP; split .
  - exact : newer_than_lits_drop .
  - exact : newer_than_lits_copy .
Qed .

Lemma mk_env_high_newer_cnf E g n ls E' g' cs lrs :
  mk_env_high E g n ls = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls ->
  newer_than_cnf g' cs .
Proof .
  by rewrite /mk_env_high; case => _ <- <- _ .
Qed .

Lemma mk_env_high_preserve E g n ls E' g' cs lrs :
  mk_env_high E g n ls = (E', g', cs, lrs) -> env_preserve E E' g .
Proof .
  by rewrite /mk_env_high; case => <- _ _ _ .
Qed .

Lemma mk_env_high_sat E g n ls E' g' cs lrs :
  mk_env_high E g n ls = (E', g', cs, lrs) ->
  newer_than_lits g ls -> interp_cnf E' cs .
Proof .
  by rewrite /mk_env_high; case => <- _ <- _ _ .
Qed .
