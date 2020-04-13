
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBLow BBHigh .
From ssrlib Require Import ZAriths Seqs Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* auxiliary lemmas *)

Lemma size_take T n (ls : seq T) : size (take n ls) = minn n (size ls) .
Proof .
  elim : ls n => [| ls_hd ls_tl IH] n .
  - by rewrite /= .
  - case : n => [| n]; first by rewrite /= .
    rewrite /= .
    by rewrite !(IH n) minnSS .
Qed .

Lemma size_copy T n (l : T) : size (copy n l) = n .
Proof .
  elim : n .
  - done .
  - move => n Hn .
    by rewrite /copy size_ncons addn0 .
Qed .

Lemma size_take_eq S T n (ls1 : seq S) (ls2 : seq T) :
  size ls1 = size ls2 -> size (take n ls1) = size (take n ls2) .
Proof .
  move => Hsize .
  by rewrite !size_take Hsize .
Qed .

Lemma size_take_copy n (ls : word) :
  size (take n ls ++
        copy (n - size ls) lit_ff) = n .
Proof .
  rewrite seq.size_cat size_take size_copy .
  rewrite minnE .
  apply : subnK; apply : leq_subr .
Qed .

Lemma enc_bits_extract E i j ls bs :
  enc_bit E lit_tt true ->
  enc_bits E ls bs ->
  enc_bits E (copy (i-j+1-(i+1)) lit_ff ++
                   drop (i+1-(i-j+1)) (take (i + 1) ls ++ copy (i+1-size ls) lit_ff))
           (extract i j bs) .
Proof .
  rewrite enc_bit_tt_ff => Hff Hlsbs .
  move : (enc_bits_size Hlsbs) => Hsize .
  rewrite /extract /b0 !Hsize enc_bits_cat; first done .
  - rewrite size_low /zeros /b0; exact : enc_bits_copy .
  - rewrite size_low /low .
    apply : enc_bits_drop .
    rewrite enc_bits_cat; first done .
    + exact : enc_bits_take .
    + rewrite /zeros /b0; exact : enc_bits_copy .
Qed .

Lemma newer_than_lits_extract g i j ls :
  newer_than_lit g lit_tt ->
  newer_than_lits g ls ->
  newer_than_lits g (copy (i-j+1-(i+1)) lit_ff ++
                          drop (i+1-(i-j+1))
                          (take (i + 1) ls ++ copy (i+1-size ls) lit_ff)) .
Proof .
  move => Htt Hls .
  rewrite newer_than_lits_cat .
  apply /andP; split .
  - exact : newer_than_lits_copy .
  - apply : newer_than_lits_drop .
    rewrite newer_than_lits_cat; apply /andP; split .
    + exact : newer_than_lits_take .
    + exact : newer_than_lits_copy .
Qed .

(* ===== bit_blast_extract ===== *)

Definition bit_blast_extract g i j ls : generator * cnf * word :=
  let lowls := take (i + 1) ls ++ copy (i + 1 - size ls) lit_ff in
  (g, [::], copy (i - j + 1 - size lowls) lit_ff ++
                 drop (size lowls - (i - j + 1)) lowls) .

Definition mk_env_extract E g i j ls : env * generator * cnf * word :=
  let lowls := take (i + 1) ls ++ copy (i + 1 - size ls) lit_ff in
  (E, g, [::], copy (i - j + 1 - size lowls) lit_ff ++
                    drop (size lowls - (i - j + 1)) lowls) .

Lemma bit_blast_extract_correct E g i j bs ls g' cs lr :
  bit_blast_extract g i j ls = (g', cs, lr) ->
  enc_bits E ls bs -> interp_cnf E (add_prelude cs) ->
  enc_bits E lr (extract i j bs) .
Proof .
  rewrite /bit_blast_extract; case => _ _ <- Hlsbs Hcnf .
  move : (add_prelude_enc_bit_tt Hcnf) => Htt .
  rewrite !size_take_copy .
  exact : enc_bits_extract .
Qed .

Lemma mk_env_extract_is_bit_blast_extract E g i j ls E' g' cs lrs :
  mk_env_extract E g i j ls = (E', g', cs, lrs) ->
  bit_blast_extract g i j ls = (g', cs, lrs) .
Proof .
  by rewrite /mk_env_extract /bit_blast_extract; case => _ <- <- <- .
Qed .

Lemma mk_env_extract_newer_gen E g i j ls E' g' cs lrs :
  mk_env_extract E g i j ls = (E', g', cs, lrs) -> (g <=? g')%positive .
Proof .
  rewrite /mk_env_extract; case => _ <- _ _ .
  exact : Pos.leb_refl .
Qed .

Lemma mk_env_extract_newer_res E g i j ls E' g' cs lrs :
  mk_env_extract E g i j ls = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls ->
  newer_than_lits g' lrs .
Proof .
  rewrite /mk_env_extract; case => _ <- _ <- Hlsbs Htt .
  rewrite newer_than_lits_cat; apply /andP; split .
  - exact : newer_than_lits_copy .
  - apply : newer_than_lits_drop .
    rewrite newer_than_lits_cat; apply/andP; split .
    + exact : newer_than_lits_take .
    + exact : newer_than_lits_copy .
Qed .

Lemma mk_env_extract_newer_cnf E g i j ls E' g' cs lrs :
  mk_env_extract E g i j ls = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls ->
  newer_than_cnf g' cs .
Proof .
  rewrite /mk_env_extract; case => _ <- <- _ .
  by t_auto_newer .
Qed .

Lemma mk_env_extract_preserve E g i j ls E' g' cs lrs :
  mk_env_extract E g i j ls = (E', g', cs, lrs) -> env_preserve E E' g .
Proof .
  rewrite /mk_env_extract; case => <- _ _ _; by t_auto_preserve .
Qed .

Lemma mk_env_extract_sat E g i j ls E' g' cs lrs :
  mk_env_extract E g i j ls = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls ->
  interp_cnf E' cs .
Proof .
  by rewrite /mk_env_extract; case => <- _ <- _ _ .
Qed .
