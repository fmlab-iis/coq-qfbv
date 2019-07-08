
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon.
From ssrlib Require Import ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_const ===== *)

Definition bit_blast_const w g (n : BITS w) : generator * cnf * w.-tuple literal :=
  (g, [::], map_tuple (fun b => if b then lit_tt else lit_ff) n).

Definition mk_env_const w E g (n : BITS w) : env * generator * cnf * w.-tuple literal :=
  (E, g, [::], map_tuple (fun b => if b then lit_tt else lit_ff) n).

Lemma bit_blast_const_correct :
  forall w g (bv : BITS w) E g' cs ls,
    bit_blast_const g bv = (g', cs, ls) ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E ls bv.
Proof.
  rewrite /bit_blast_const /add_prelude. elim; first by done.
  move=> w IH g. case/tupleP => bv_hd bv_tl E g' cs.
  case/tupleP => ls_hd ls_tl. move=> [] Hg Hcs Hls_hd Hls_tl.
  rewrite -Hcs. move=> /= Hprelude. rewrite !theadE !beheadCons. apply/andP; split.
  - rewrite -{}Hls_hd /enc_bit. case: bv_hd => /=; by rewrite Hprelude.
  - apply: (IH _ _ E g' [::]); last by rewrite /interp_cnf /= Hprelude.
    rewrite -Hg. apply: injective_projections => /=; first by reflexivity.
    apply: val_inj; rewrite /=. exact: Hls_tl.
Qed.

Lemma mk_env_const_is_bit_blast_env :
  forall w E g (bv : BITS w) E' g' cs ls,
    mk_env_const E g bv = (E', g', cs, ls) ->
    bit_blast_const g bv = (g', cs, ls).
Proof.
  rewrite /mk_env_const /bit_blast_const; intros; dcase_hyps; subst; reflexivity.
Qed.

Lemma mk_env_cont_sat :
  forall w E g (bv : BITS w) E' g' cs lrs,
    mk_env_const E g bv = (E', g', cs, lrs) ->
    interp_cnf E' cs.
Proof.
  rewrite /mk_env_const=> w E g bv E' g' cs lrs.
  case=> <- _ <- _. done.
Qed.

Lemma mk_env_const_env_preserve :
  forall w E g (bv : BITS w) E' g' cs lrs,
    mk_env_const E g bv = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> w E g bv E' g' cs lrs. case=> <- _ _ _. exact: env_preserve_refl.
Qed.

Lemma mk_env_const_newer_gen :
  forall w E g (bv : BITS w) E' g' cs lrs,
    mk_env_const E g bv = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> w E g bv E' g' cs lrs. case=> _ <- _ _. exact: Pos.leb_refl.
Qed.

Lemma mk_env_const_newer_res :
  forall w E g (bs : BITS w) E' g' cs lrs,
    mk_env_const E g bs = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g' lrs.
Proof.
  move=> w E g bs E' g' cs lrs /=. case=> _ <- _ <- Hnew_gtt {E E' g' cs lrs}.
  elim: w bs.
  - move=> bs /=. rewrite tuple0. done.
  - move=> w IH. case/tupleP=> [bs_hd bs_tl] /=. rewrite (IH _) andbT. case: bs_hd.
    + exact: Hnew_gtt.
    + exact: Hnew_gtt.
Qed.
