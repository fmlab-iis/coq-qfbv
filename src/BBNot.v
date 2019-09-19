From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import Var QFBV CNF BBCommon.
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_not ===== *)

Definition bit_blast_not1 (g: generator) (a:literal) : generator * cnf * literal :=
  let (g', r):= gen g in
  let cs := [::
        [:: r; a]; [:: neg_lit r; neg_lit a]
            ] in (g', cs , r).

Fixpoint bit_blast_not g a : generator * cnf * word :=
  match a with
  | [::] => (g, [::], [::])
  | hd :: tl =>
    let '(g_hd, cs_hd, lrs_hd) := bit_blast_not1 g hd in
    let '(g_tl, cs_tl, lrs_tl) := bit_blast_not g tl in
    (g_tl, catrev cs_hd cs_tl, lrs_hd :: lrs_tl)
  end.

Definition mk_env_not1 E g a : env * generator * cnf * literal :=
  let (g', r) := gen g in
  let E' := env_upd E (var_of_lit r) (~~ (interp_lit E a)) in
  let cs := [:: [:: r; a]; [:: neg_lit r; neg_lit a]] in
  (E', g', cs, r).

Fixpoint mk_env_not E g a : env * generator * cnf * word :=
  match a with
  | [::] => (E, g, [::], [::])
  | hd :: tl =>
    let '(E_hd, g_hd, cs_hd, lrs_hd) := mk_env_not1 E g hd in
    let '(E_tl, g_tl, cs_tl, lrs_tl) := mk_env_not E_hd g_hd tl in
    (E_tl, g_tl, catrev cs_hd cs_tl, lrs_hd :: lrs_tl)
  end.

Lemma bit_blast_not1_correct :
  forall g b br E l g' cs lr,
    bit_blast_not1 g l = (g', cs, lr) ->
    enc_bit E l b ->
    interp_cnf E (add_prelude cs) ->
    br = ~~ b ->
    enc_bit E lr br.
Proof.
Admitted.

Lemma bit_blast_not_correct :
  forall g bs E ls g' cs lrs,
    bit_blast_not g ls = (g', cs, lrs) ->
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (invB bs).
Proof.
Admitted.

Lemma mk_env_not1_is_bit_blast_not1 :
  forall E g l E' g' cs lr,
    mk_env_not1 E g l = (E', g', cs, lr) ->
    bit_blast_not1 g l = (g', cs, lr).
Proof.
Admitted.

Lemma mk_env_not_is_bit_blast_not :
  forall E g ls E' g' cs lrs,
    mk_env_not E g ls = (E', g', cs, lrs) ->
    bit_blast_not g ls = (g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_not1_newer_gen :
  forall E g l E' g' cs lr,
    mk_env_not1 E g l = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_not_newer_gen :
  forall E g ls E' g' cs lrs,
    mk_env_not E g ls = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_not1_newer_res :
  forall E g l E' g' cs lr,
    mk_env_not1 E g l = (E', g', cs, lr) ->
    newer_than_lit g l ->
    newer_than_lit g' lr.
Proof.
Admitted.

Lemma mk_env_not_newer_res :
  forall E g ls E' g' cs lrs,
    mk_env_not E g ls = (E', g', cs, lrs) ->
    newer_than_lits g ls ->
    newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_not1_newer_cnf :
  forall E g l E' g' cs lr,
    mk_env_not1 E g l = (E', g', cs, lr) ->
    newer_than_lit g l ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_not_newer_cnf :
  forall E g ls E' g' cs lrs,
    mk_env_not E g ls = (E', g', cs, lrs) ->
    newer_than_lits g ls ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_not1_preserve :
  forall E g l E' g' cs lr,
    mk_env_not1 E g l = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_not_preserve :
  forall E g ls E' g' cs lrs,
    mk_env_not E g ls = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_not1_sat :
  forall E g l E' g' cs lr,
    mk_env_not1 E g l = (E', g', cs, lr) ->
    newer_than_lit g l ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_not_sat :
  forall E g ls E' g' cs lrs,
    mk_env_not E g ls = (E', g', cs, lrs) ->
    newer_than_lits g ls ->
    interp_cnf E' cs.
Proof.
Admitted.
