
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From BitBlasting Require Import TypEnv State QFBV CNF BBCommon.
From ssrlib Require Import EqVar ZAriths Tactics.
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

Definition bit_blast_var (tenv : SSATE.env) g (v : ssavar) : generator * cnf * word :=
  let (g', vs) := bit_blast_var' g (SSATE.vsize v tenv) in
  (g', [::], vs).

Definition mk_env_var E g (bs : bits) (v : ssavar) : env * generator * cnf * word :=
  let '(E', g', vs) := mk_env_var' E g bs in
  (E', g', [::], vs).

Lemma bit_blast_var_cnf_empty tenv g v g' cs lrs :
  bit_blast_var tenv g v = (g', cs, lrs) -> cs = [::].
Proof.
  rewrite /bit_blast_var. dcase (bit_blast_var' g (SSATE.vsize v tenv)).
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
  size bs = SSATE.vsize v tenv -> mk_env_var E g bs v = (E', g', cs, lrs) ->
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

Lemma mk_env_var'_env_equal E1 E2 g bs E1' E2' g1 g2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_var' E1 g bs = (E1', g1, lrs1) ->
  mk_env_var' E2 g bs = (E2', g2, lrs2) ->
  env_equal E1' E2' /\ g1 = g2 /\ lrs1 = lrs2.
Proof.
  elim: bs E1 E2 g g1 g2 lrs1 lrs2 => [| b bs IH] //= E1 E2 g g1 g2 lrs1 lrs2 Heq.
  - case=> ? ? ?; subst. case=> ? ? ?; subst. done.
  - dcase (mk_env_var' (env_upd E1 g b) (g + 1)%positive bs) => [[[E1'' g1''] tl1] Hv1].
    dcase (mk_env_var' (env_upd E2 g b) (g + 1)%positive bs) => [[[E2'' g2''] tl2] Hv2].
    case=> ? ? ?; case=> ? ? ?; subst.
    move: (IH _ _ _ _ _ _ _ (env_equal_upd g b Heq) Hv1 Hv2) => [H1 [H2 H3]].
    rewrite H2 H3. done.
Qed.

Lemma mk_env_var_env_equal E1 E2 g bs v E1' E2' g1 g2 cs1 cs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_var E1 g bs v = (E1', g1, cs1, lrs1) ->
  mk_env_var E2 g bs v = (E2', g2, cs2, lrs2) ->
  env_equal E1' E2' /\ g1 = g2 /\ cs1 = cs2 /\ lrs1 = lrs2.
Proof.
  rewrite /mk_env_var => Heq.
  dcase (mk_env_var' E1 g bs) => [[[E1'' g1''] lrs1''] Hv1].
  dcase (mk_env_var' E2 g bs) => [[[E2'' g2''] lrs2''] Hv2].
  case=> ? ? ? ?; case=> ? ? ? ?; subst.
  move: (mk_env_var'_env_equal Heq Hv1 Hv2) => [H1 [H2 H3]]. done.
Qed.

Lemma mk_env_var_consistent s iE im ig v oE og ocs olrs :
  mk_env_var iE ig (SSAStore.acc v s) v = (oE, og, ocs, olrs) ->
  newer_than_vm ig im ->
  consistent im iE s ->
  consistent (SSAVM.add v olrs im) oE s.
Proof.
  move=> Henv Hnew Hcon. move=> x. rewrite /consistent1.
  dcase (SSAVM.find x (SSAVM.add v olrs im)); case => //=.
  move=> xls. case Hxv: (x == v).
  - rewrite (SSAVM.Lemmas.find_add_eq Hxv). case=> ?; subst.
    rewrite (eqP Hxv). exact: (mk_env_var_enc Henv).
  - move/negP: Hxv => Hxv. rewrite (SSAVM.Lemmas.find_add_neq Hxv) => Hfx.
    move: (Hcon x). rewrite /consistent1. rewrite Hfx => Henc.
    move: (Hnew x _ Hfx) => Hnew_igxls.
    exact: (env_preserve_enc_bits (mk_env_var_preserve Henv) Hnew_igxls Henc).
Qed.


(* agree *)

Lemma agree_bit_blast_var E1 E2 g v :
  QFBV.MA.agree (SSAVS.singleton v) E1 E2 ->
  bit_blast_var E1 g v = bit_blast_var E2 g v.
Proof.
  move=> Hag. rewrite /bit_blast_var. rewrite (QFBV.MA.agree_vsize_singleton Hag).
  reflexivity.
Qed.

