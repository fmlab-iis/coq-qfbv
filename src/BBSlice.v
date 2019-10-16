
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBLow BBHigh BBExtract .
From ssrlib Require Import ZAriths Seqs Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== bit_blast_slice ===== *)

Definition bit_blast_slice g i m ls : generator * cnf * word :=
  bit_blast_extract g i (i + m - 1) ls .

Definition mk_env_slice E g i m ls : env * generator * cnf * word :=
  mk_env_extract E g i (i + m - 1) ls .

Lemma bit_blast_slice_correct E g i m bs ls g' cs lr :
  bit_blast_slice g i m ls = (g', cs, lr) ->
  enc_bits E ls bs -> interp_cnf E (add_prelude cs) ->
  enc_bits E lr (slice i m bs) .
Proof .
  exact : bit_blast_extract_correct .
Qed .

Lemma mk_env_slice_is_bit_blast_slice E g i m ls E' g' cs lrs :
  mk_env_slice E g i m ls = (E', g', cs, lrs) ->
  bit_blast_slice g i m ls = (g', cs, lrs) .
Proof .
  exact : mk_env_extract_is_bit_blast_extract .
Qed .

Lemma mk_env_slice_newer_gen E g i m ls E' g' cs lrs :
  mk_env_extract E g i m ls = (E', g', cs, lrs) -> (g <=? g')%positive .
Proof .
  exact : mk_env_extract_newer_gen .
Qed .

Lemma mk_env_slice_newer_res E g i m ls E' g' cs lrs :
  mk_env_slice E g i m ls = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls ->
  newer_than_lits g' lrs .
Proof .
  exact : mk_env_extract_newer_res .
Qed .

Lemma mk_env_slice_newer_cnf E g i m ls E' g' cs lrs :
  mk_env_slice E g i m ls = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls ->
  newer_than_cnf g' cs .
Proof .
  exact : mk_env_extract_newer_cnf .
Qed .

Lemma mk_env_slice_preserve E g i m ls E' g' cs lrs :
  mk_env_slice E g i m ls = (E', g', cs, lrs) -> env_preserve E E' g .
Proof .
  exact : mk_env_extract_preserve .
Qed .

Lemma mk_env_slice_sat E g i m ls E' g' cs lrs :
  mk_env_extract E g i m ls = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls ->
  interp_cnf E' cs .
Proof .
  exact : mk_env_extract_sat .
Qed .
