From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon.
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_not ===== *)

Definition bit_blast_not1 (g: generator) (l:literal) : generator * cnf * literal :=
  let (g', r):= gen g in
  let cs := [::
        [:: r; l]; [:: neg_lit r; neg_lit l]
            ] in (g', cs , r).

Fixpoint bit_blast_not g ls : generator * cnf * word :=
  match ls with
  | [::] => (g, [::], [::])
  | hd :: tl =>
    let '(g_hd, cs_hd, lrs_hd) := bit_blast_not1 g hd in
    let '(g_tl, cs_tl, lrs_tl) := bit_blast_not g_hd tl in
    (g_tl, catrev cs_hd cs_tl, lrs_hd :: lrs_tl)
  end.

Definition mk_env_not1 E g l : env * generator * cnf * literal :=
  let (g', r) := gen g in
  let E' := env_upd E (var_of_lit r) (~~ (interp_lit E l)) in
  let cs := [:: [:: r; l]; [:: neg_lit r; neg_lit l]] in
  (E', g', cs, r).

Fixpoint mk_env_not E g ls : env * generator * cnf * word :=
  match ls with
  | [::] => (E, g, [::], [::])
  | hd :: tl =>
    let '(E_hd, g_hd, cs_hd, lrs_hd) := mk_env_not1 E g hd in
    let '(E_tl, g_tl, cs_tl, lrs_tl) := mk_env_not E_hd g_hd tl in
    (E_tl, g_tl, catrev cs_hd cs_tl, lrs_hd :: lrs_tl)
  end.

Lemma bit_blast_not1_correct g b br E l g' cs lr :
    bit_blast_not1 g l = (g', cs, lr) ->
    enc_bit E l b ->
    interp_cnf E (add_prelude cs) ->
    br = ~~ b ->
    enc_bit E lr br.
Proof.
  rewrite /bit_blast_not1 /enc_bit. case=> _ <- <- /=.
  rewrite add_prelude_expand /= interp_lit_neg_lit /=. move/eqP ->.
  move/andP => [Htt Hcs] ->; t_clear.
  move: Hcs. by case (E g); case b. 
Qed.

Lemma bit_blast_not_correct g bs E ls g' cs lrs:
    bit_blast_not g ls = (g', cs, lrs) ->
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (invB bs).
Proof.
  elim: ls g bs E g' cs lrs.
  - move=> g bs E g' cs lr /=. case=> _ <- <- /=.
    rewrite enc_bits_nil_l. move/eqP ->. done.
  - move=> ls_hd ls_tl IH g bs E g' cs lrs.
    rewrite /bit_blast_not -/bit_blast_not. 
    case Hbb_hd : (bit_blast_not1 g ls_hd) => [[g_hd cs_hd] lrs_hd].
    case Hbb_tl : (bit_blast_not g_hd ls_tl) => [[g_tl cs_tl] lrs_tl].
    case=> _ <- <-. case: bs => [| bs_hd bs_tl] //=.
    rewrite !enc_bits_cons add_prelude_catrev.
    move => /andP [Henc_hd Henc_tl] /andP [Hi_hd Hi_tl].
    rewrite (bit_blast_not1_correct Hbb_hd Henc_hd Hi_hd) /=; try done.
    exact: (IH _ _ _ _ _ _ Hbb_tl Henc_tl Hi_tl).
Qed.

Lemma mk_env_not1_is_bit_blast_not1 E g l E' g' cs lr:
    mk_env_not1 E g l = (E', g', cs, lr) ->
    bit_blast_not1 g l = (g', cs, lr).
Proof.
  rewrite /mk_env_not1 /bit_blast_not1; intros;
    dite_hyps; dcase_hyps; subst; reflexivity.
Qed.

Lemma mk_env_not_is_bit_blast_not E g ls E' g' cs lrs:
    mk_env_not E g ls = (E', g', cs, lrs) ->
    bit_blast_not g ls = (g', cs, lrs).
Proof.
  elim: ls E g E' g' cs lrs => [| ls_hd ls_tl IH] E g E' g' cs lrs.
  - by case=> _ <- <- <-.
  - rewrite /bit_blast_not -/bit_blast_not /mk_env_not -/mk_env_not.
    case Hmk_hd : (mk_env_not1 E g ls_hd) => [[[E_hd g_hd] cs_hd] lrs_hd].
    case Hmk_tl : (mk_env_not E_hd g_hd ls_tl) => [[[E_tl g_tl] cs_tl] lrs_tl].
    rewrite (mk_env_not1_is_bit_blast_not1 Hmk_hd).
    rewrite (IH _ _ _ _ _ _ Hmk_tl).
    by case=> _ <- <- <-.
Qed.

Lemma mk_env_not1_newer_gen E g l E' g' cs lr:
    mk_env_not1 E g l = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  rewrite /mk_env_not1 /=. case=> _ <- _ _.
  by t_auto_newer.
Qed.

Lemma mk_env_not_newer_gen E g ls E' g' cs lrs:
    mk_env_not E g ls = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  elim: ls E g E' g' cs lrs => [| ls_hd ls_tl IH] E g E' g' cs lrs.
  - case=> _ <- _ _; by t_auto_newer.
  - rewrite /mk_env_not -/mk_env_not.
    case Hmk_hd : (mk_env_not1 E g ls_hd) => [[[E_hd g_hd] cs_hd] lrs_hd].
    case Hmk_tl : (mk_env_not E_hd g_hd ls_tl) => [[[E_tl g_tl] cs_tl] lrs_tl].
    case=> _ <- _ _.
    move: (mk_env_not1_newer_gen Hmk_hd) => Hggh. 
    move: (IH _ _ _ _ _ _ Hmk_tl) => Hghgt.
    by apply: (pos_leb_trans Hggh Hghgt).
Qed.

Lemma mk_env_not1_newer_res E g l E' g' cs lr:
    mk_env_not1 E g l = (E', g', cs, lr) ->
    newer_than_lit g l ->
    newer_than_lit g' lr.
Proof.
  rewrite /mk_env_not1 /=. case=> _ <- _ <-.
  by t_auto_newer.
Qed.

Lemma mk_env_not_newer_res E g ls E' g' cs lrs:
    mk_env_not E g ls = (E', g', cs, lrs) ->
    newer_than_lits g ls ->
    newer_than_lits g' lrs.
Proof.
  elim: ls E g E' g' cs lrs => [| ls_hd ls_tl IH] E g E' g' cs lrs.
  - case=> _ <- _ <-; by t_auto_newer.
  - rewrite /mk_env_not -/mk_env_not.
    case Hmk_hd : (mk_env_not1 E g ls_hd) => [[[E_hd g_hd] cs_hd] lrs_hd].
    case Hmk_tl : (mk_env_not E_hd g_hd ls_tl) => [[[E_tl g_tl] cs_tl] lrs_tl].
    case=> _ <- _ <- /=.
    move/andP => [Hglh Hglt].
    move: (mk_env_not1_newer_gen Hmk_hd) => Hggh.
    move: (mk_env_not_newer_gen Hmk_tl) => Hghgt.
    move: (mk_env_not1_newer_res Hmk_hd Hglh) => Hghlrh.
    apply/andP; split.
    + by apply (newer_than_lit_le_newer Hghlrh).
    + move: (newer_than_lits_le_newer Hglt Hggh) => Hghlt.
      exact: (IH _ _ _ _ _ _ Hmk_tl Hghlt).
Qed.

Lemma mk_env_not1_newer_cnf E g l E' g' cs lr:
    mk_env_not1 E g l = (E', g', cs, lr) ->
    newer_than_lit g l ->
    newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_not1 /=. case=> _ <- <- _.
  by t_auto_newer.
Qed.

Lemma mk_env_not_newer_cnf E g ls E' g' cs lrs:
    mk_env_not E g ls = (E', g', cs, lrs) ->
    newer_than_lits g ls ->
    newer_than_cnf g' cs.
Proof.
  elim: ls E g E' g' cs lrs => [| ls_hd ls_tl IH] E g E' g' cs lrs.
  - case=> _ <- <- _; by t_auto_newer.
  - rewrite /mk_env_not -/mk_env_not.
    case Hmk_hd : (mk_env_not1 E g ls_hd) => [[[E_hd g_hd] cs_hd] lrs_hd].
    case Hmk_tl : (mk_env_not E_hd g_hd ls_tl) => [[[E_tl g_tl] cs_tl] lrs_tl].
    case=> _ <- <- _ /=. move/andP => [Hglh Hglt].
    rewrite newer_than_cnf_catrev. 
    move: (mk_env_not_newer_gen Hmk_tl) => Hghgt.
    apply/andP; split.
    + move: (mk_env_not1_newer_cnf Hmk_hd Hglh) => Hghch.
      by apply (newer_than_cnf_le_newer Hghch).
    + move: (mk_env_not1_newer_gen Hmk_hd) => Hggh.
      move: (newer_than_lits_le_newer Hglt Hggh) => Hghlt.
      exact: (IH _ _ _ _ _ _ Hmk_tl Hghlt).
Qed.

Lemma mk_env_not1_preserve E g l E' g' cs lr:
    mk_env_not1 E g l = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  rewrite /mk_env_not1 /=. case=> <- _ _ _.
  by t_auto_preserve.
Qed.

Lemma mk_env_not_preserve E g ls E' g' cs lrs:
    mk_env_not E g ls = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  elim: ls E g E' g' cs lrs => [| ls_hd ls_tl IH] E g E' g' cs lrs.
  - case=> <- _ _ _; by t_auto_preserve.
  - rewrite /mk_env_not -/mk_env_not.
    case Hmk_hd : (mk_env_not1 E g ls_hd) => [[[E_hd g_hd] cs_hd] lrs_hd].
    case Hmk_tl : (mk_env_not E_hd g_hd ls_tl) => [[[E_tl g_tl] cs_tl] lrs_tl].
    case=> <- _ _ _ /=. 
    move: (mk_env_not1_preserve Hmk_hd) => HEEhg.
    move: (IH _ _ _ _ _ _ Hmk_tl) => HEhEtgh.
    move: (mk_env_not1_newer_gen Hmk_hd) => Hggh.
    apply (env_preserve_trans HEEhg).
    exact: (env_preserve_le HEhEtgh Hggh).
Qed.

Lemma mk_env_not1_sat E g l E' g' cs lr:
    mk_env_not1 E g l = (E', g', cs, lr) ->
    newer_than_lit g l ->
    interp_cnf E' cs.
Proof.
  rewrite /mk_env_not1 /=. case=> <- _ <- _ Hgl.
  move: (newer_than_lit_neq Hgl) => Hngl /=.
  rewrite !env_upd_eq !interp_lit_neg_lit.
  rewrite (interp_lit_env_upd_neq _ _ Hngl).
  by case (interp_lit E l).
Qed.

Lemma mk_env_not_sat E g ls E' g' cs lrs:
    mk_env_not E g ls = (E', g', cs, lrs) ->
    newer_than_lits g ls ->
    interp_cnf E' cs.
Proof.
  elim: ls E g E' g' cs lrs => [| ls_hd ls_tl IH] E g E' g' cs lrs.
  - by case=> <- _ <- _.
  - rewrite /mk_env_not -/mk_env_not.
    case Hmk_hd : (mk_env_not1 E g ls_hd) => [[[E_hd g_hd] cs_hd] lrs_hd].
    case Hmk_tl : (mk_env_not E_hd g_hd ls_tl) => [[[E_tl g_tl] cs_tl] lrs_tl].
    case=> <- _ <- _ /=. move/andP => [Hglh Hglt].
    rewrite interp_cnf_catrev; apply/andP; split.
    + move: (mk_env_not_preserve Hmk_tl) => HpEhEtgh.
      move: (mk_env_not1_newer_cnf Hmk_hd Hglh) => Hghch.
      rewrite (env_preserve_cnf HpEhEtgh Hghch).
      exact: (mk_env_not1_sat Hmk_hd Hglh).
    + apply: (IH _ _ _ _ _ _ Hmk_tl).
      move: (mk_env_not1_newer_gen Hmk_hd).
      by apply: newer_than_lits_le_newer.
Qed.

Lemma mk_env_not_env_equal E1 E2 g ls E1' E2' g1' g2' cs1 cs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_not E1 g ls = (E1', g1', cs1, lrs1) ->
  mk_env_not E2 g ls = (E2', g2', cs2, lrs2) ->
  env_equal E1' E2' /\ g1' = g2' /\ cs1 = cs2 /\ lrs1 = lrs2.
Proof.
  elim: ls E1 E2 g E1' E2' g1' g2' cs1 cs2 lrs1 lrs2
  => [| l ls IH] //= E1 E2 g E1' E2' g1' g2' cs1 cs2 lrs1 lrs2 Heq.
  - case=> ? ? ? ?; case=> ? ? ? ?; subst. done.
  - dcase (mk_env_not (env_upd E1 g (~~ interp_lit E1 l)) (g + 1)%positive ls)
    => [[[[Etl1 gtl1] cstl1] lrstl1] Htl1].
    dcase (mk_env_not (env_upd E2 g (~~ interp_lit E2 l)) (g + 1)%positive ls)
    => [[[[Etl2 gtl2] cstl2] lrstl2] Htl2].
    case=> ? ? ? ?; case=> ? ? ? ?; subst.
    have Heq': env_equal (env_upd E1 g (~~ interp_lit E1 l))
                         (env_upd E2 g (~~ interp_lit E2 l)).
    { rewrite (env_equal_interp_lit l Heq). apply: env_equal_upd. assumption. }
    move: (IH _ _ _ _ _ _ _ _ _ _ _ Heq' Htl1 Htl2) => [H1 [H2 [H3 H4]]]; subst.
    done.
Qed.
