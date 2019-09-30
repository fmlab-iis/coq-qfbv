
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import Var QFBV CNF BBCommon.
From ssrlib Require Import ZAriths Seqs Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* auxiliary lemmas *)

Lemma enc_bits_take E n ls bs :
  enc_bits E ls bs -> enc_bits E (take n ls) (take n bs) .
Proof .
  move => Hlsbs .
  move : (enc_bits_size Hlsbs) => Hsize .
  move : ls bs Hsize Hlsbs n .
  apply : seq_ind2 => [|ls_hd bs_hd ls_tl bs_tl Hsize IH] .
  - by rewrite /= .
  - rewrite enc_bits_cons => /andP [Hlsbshd Hlsbstl] .
    case => [| n ] .
    + by rewrite /= .
    + by rewrite /= enc_bits_cons Hlsbshd (IH Hlsbstl n) .
Qed .

Lemma newer_than_lits_take g n ls :
  newer_than_lits g ls -> newer_than_lits g (take n ls) .
Proof .
  elim : ls n => [| ls_hd ls_tl IH] n .
  - by rewrite /= .
  - rewrite newer_than_lits_cons => /andP [Hlshd Hlstl] .
    case : n => [|n]; first by rewrite /= .
    by rewrite /= Hlshd (IH n Hlstl) .
Qed .

(* ===== bit_blast_low ===== *)

Definition bit_blast_low g n ls : generator * cnf * word :=
  (g, [::], take n ls ++ copy (n - size ls) lit_ff) .

Definition mk_env_low E g n ls : env * generator * cnf * word :=
  (E, g, [::], take n ls ++ copy (n - size ls) lit_ff) .

Lemma bit_blast_low_correct E g n bs ls g' cs lr :
  bit_blast_low g n ls = (g', cs, lr) ->
  enc_bits E ls bs ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E lr (low n bs) .
Proof .
  rewrite /bit_blast_low /low /zeros .
  case => _ _ <- Hlsbs Hcnf .
  rewrite enc_bits_cat /=; first done .
  - exact : enc_bits_take .
  - rewrite /b0 (enc_bits_size Hlsbs) .
    move : (add_prelude_enc_bit_ff Hcnf) .
    exact : enc_bits_copy .
Qed .

Lemma mk_env_low_is_bit_blast_low E g n ls E' g' cs lr :
  mk_env_low E g n ls = (E', g', cs, lr) -> bit_blast_low g n ls = (g', cs, lr) .
Proof .
  rewrite /mk_env_low /bit_blast_low .
  by case => _ <- <- <- .
Qed .

Lemma mk_env_low_newer_gen E g n ls E' g' cs lr :
  mk_env_low E g n ls = (E', g', cs, lr) -> (g <=? g')%positive.
Proof .
  rewrite /mk_env_low .
  t_auto_newer .
Qed .

Lemma mk_env_low_newer_res E g n ls E' g' cs lrs :
  mk_env_low E g n ls = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls ->
  newer_than_lits g' lrs .
Proof .
  rewrite /mk_env_low .
  case => _ <- _ <- Htt Hls .
  rewrite newer_than_lits_cat .
  apply /andP; split .
  - exact : newer_than_lits_take .
  - exact : newer_than_lits_copy .
Qed .

Lemma mk_env_low_newer_cnf E g n ls E' g' cs lrs :
  mk_env_low E g n ls = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls ->
  newer_than_cnf g' cs .
Proof .
  rewrite /mk_env_low .
  by case => _ <- <- _ .
Qed .

Lemma mk_env_low_preserve E g n ls E' g' cs lrs :
  mk_env_low E g n ls = (E', g', cs, lrs) -> env_preserve E E' g .
Proof .
  by rewrite /mk_env_low; case => <- _ _ _ .
Qed .

Lemma mk_env_and_sat E g n ls E' g' cs lrs :
  mk_env_low E g n ls = (E', g', cs, lrs) ->
  newer_than_lits g ls -> interp_cnf E' cs .
Proof .
  by rewrite /mk_env_low; case => <- _ <- _ .
Qed .
