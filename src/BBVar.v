
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From BitBlasting Require Import Var TypEnv QFBV CNF BBCommon.
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_var ===== *)

Fixpoint bit_blast_var' (g : generator) (w : nat) : generator * word :=
  match w with
  | O => (g, [::])
  | S n => let (g', hd) := gen g in
           let (g'', tl) := bit_blast_var' g' n in
           (g'', hd::tl)
  end.

Fixpoint mk_env_var' E g bs : env * generator * word :=
  match bs with
  | [::] => (E, g, [::])
  | bs_hd::bs_tl => let (g', hd) := gen g in
                    let E' := env_upd E (var_of_lit hd) bs_hd in
                    let '(E'', g'', tl) := mk_env_var' E' g' bs_tl in
                    (E'', g'', hd::tl)
  end.

Definition bit_blast_var (tenv : TypEnv.t) g (v : var) : generator * cnf * word :=
  let (g', vs) := bit_blast_var' g (TypEnv.vsize v tenv) in
  (g', [::], vs).

Definition mk_env_var E g (bs : bits) (v : var) : env * generator * cnf * word :=
  let '(E', g', vs) := mk_env_var' E g bs in
  (E', g', [::], vs).

Lemma bit_blast_var_cnf_empty tenv g v g' cs lrs :
  bit_blast_var tenv g v = (g', cs, lrs) -> cs = [::].
Proof.
  rewrite /bit_blast_var. dcase (bit_blast_var' g (TypEnv.vsize v tenv)).
  move=> [g_v lrs_v] Hbb. by case=> _ <- _.
Qed.

Lemma mk_env_var'_is_bit_blast_var' E g bs E' g' lrs :
  mk_env_var' E g bs = (E', g', lrs) -> bit_blast_var' g (size bs) = (g', lrs).
Proof.
  elim: bs g E E' g' lrs => [|bs_hd bs_tl IH] /=.
  - by move=> ? ? ? ? ? [] _ <- <-.
  - move=> ig iE oE og olrs.
    dcase (mk_env_var' (env_upd iE ig bs_hd) (ig+1)%positive bs_tl).
    move=> [[E g] lrs] Henv. case=> _ <- <-. by rewrite (IH _ _ _ _ _ Henv).
Qed.

Lemma mk_env_var_is_bit_blast_var tenv E g bs v E' g' cs lrs :
  size bs = TypEnv.vsize v tenv -> mk_env_var E g bs v = (E', g', cs, lrs) ->
  bit_blast_var tenv g v = (g', cs, lrs).
Proof.
  rewrite /mk_env_var /bit_blast_var. dcase (mk_env_var' E g bs).
  move=> [[E_env g_env] ls_env] Henv <-. rewrite (mk_env_var'_is_bit_blast_var' Henv).
  by case=> _ <- <- <-.
Qed.

Lemma mk_env_var_sat E g bs v E' g' cs lrs :
  mk_env_var E g bs v = (E', g', cs, lrs) -> interp_cnf E' cs.
Proof.
  rewrite /mk_env_var. dcase (mk_env_var' E g bs) => [[[oE og] olrs] Henv].
  by case=> <- _ <- _.
Qed.

Lemma mk_env_var'_preserve E g bs E' g' lrs :
  mk_env_var' E g bs = (E', g', lrs) -> env_preserve E E' g.
Proof.
  elim: bs E g E' g' lrs => [| bs_hd bs_tl IH] /=.
  - move=> ? ? ? ? ? [] <- _ _. exact: env_preserve_refl.
  - move=> E g E' g' lrs.
    dcase (mk_env_var' (env_upd E g bs_hd) (g + 1)%positive bs_tl).
    move=> [[oE og] olrs] Henv. case=> <- _ _. move: (IH _ _ _ _ _ Henv).
    exact: env_preserve_env_upd_succ.
Qed.

Lemma mk_env_var_preserve E g bs v E' g' cs lrs :
  mk_env_var E g bs v = (E', g', cs, lrs) -> env_preserve E E' g.
Proof.
  rewrite /mk_env_var. dcase (mk_env_var' E g bs) => [[[oE og] olrs] Henv].
  case=> <- _ _ _. exact: (mk_env_var'_preserve Henv).
Qed.

Lemma mk_env_var'_newer_gen E g bs E' g' lrs :
  mk_env_var' E g bs = (E', g', lrs) -> (g <=? g')%positive.
Proof.
  elim: bs E g E' g' lrs => [| bs_hd bs_tl IH] /=.
  - move=> ? ? ? ? ? [] _ <- _. exact: Pos.leb_refl.
  - move=> E g E' g' lrs.
    dcase (mk_env_var' (env_upd E g bs_hd) (g + 1)%positive bs_tl).
    move=> [[oE og] olrs] Henv. case=> _ <- _. move: (IH _ _ _ _ _ Henv).
    apply: pos_leb_trans. exact: pos_leb_add_diag_r.
Qed.

Lemma mk_env_var_newer_gen E g bs v E' g' cs lrs :
  mk_env_var E g bs v = (E', g', cs, lrs) -> (g <=? g')%positive.
Proof.
  rewrite /mk_env_var. dcase (mk_env_var' E g bs) => [[[oE og] olrs] Henv].
  case=> _ <- _ _. exact: (mk_env_var'_newer_gen Henv).
Qed.

Lemma mk_env_var'_newer_res E g bs E' g' lrs :
  mk_env_var' E g bs = (E', g', lrs) -> newer_than_lits g' lrs.
Proof.
  elim: bs E g E' g' lrs => [| bs_hd bs_tl IH] /=.
  - by move=> ? ? ? ? ? [] _ <- <-.
  - move=> E g E' g' lrs.
    dcase (mk_env_var' (env_upd E g bs_hd) (g + 1)%positive bs_tl).
    move=> [[oE og] olrs] Henv. case=> _ <- <-. rewrite newer_than_lits_cons.
    rewrite (IH _ _ _ _ _ Henv) andbT. rewrite /newer_than_lit /newer_than_var /=.
    move: (mk_env_var'_newer_gen Henv) => H. apply: (pos_ltb_leb_trans _ H).
    exact: pos_ltb_add_diag_r.
Qed.

Lemma mk_env_var_newer_res E g bs v E' g' cs lrs :
  mk_env_var E g bs v = (E', g', cs, lrs) -> newer_than_lits g' lrs.
Proof.
  rewrite /mk_env_var. dcase (mk_env_var' E g bs) => [[[oE og] olrs] Henv].
  case=> _ <- _ <-. exact: (mk_env_var'_newer_res Henv).
Qed.

Lemma mk_env_var_newer_cnf E g bs v E' g' cs lrs :
  mk_env_var E g bs v = (E', g', cs, lrs) -> newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_var. dcase (mk_env_var' E g bs) => [[[oE og] olrs] Henv].
  by case=> _ <- <- _.
Qed.

Lemma mk_env_var'_enc E g bs E' g' lrs :
  mk_env_var' E g bs = (E', g', lrs) -> enc_bits E' lrs bs.
Proof.
  elim: bs E g E' g' lrs => [| bs_hd bs_tl IH] //=.
  - by move=> ? ? ? ? ? [] <- _ <-.
  - move=> E g E' g' lrs.
    dcase (mk_env_var' (env_upd E g bs_hd) (g + 1)%positive bs_tl).
    move=> [[oE og] olrs] Henv. case=> <- _ <-. rewrite enc_bits_cons.
    rewrite (IH _ _ _ _ _ Henv) andbT. move: (mk_env_var'_preserve Henv) => Hpre.
    apply: (env_preserve_enc_bit Hpre (newer_than_lit_add_diag_r (Pos g) 1)).
    exact: enc_bit_env_upd_eq_pos.
Qed.

Lemma mk_env_var_enc E g bs v E' g' cs lrs :
  mk_env_var E g bs v = (E', g', cs, lrs) -> enc_bits E' lrs bs.
Proof.
  rewrite /mk_env_var. dcase (mk_env_var' E g bs) => [[[oE og] olrs] Henv].
  case=> <- _ _ <-. exact: (mk_env_var'_enc Henv).
Qed.
