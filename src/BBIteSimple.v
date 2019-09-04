
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNFSimple BBCommonSimple.
From ssrlib Require Import Var ZAriths Bools Tuples Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_ite ===== *)

Definition bit_blast_ite1 (g : generator) (c : literal) (a1 a2 : literal) : generator * cnf * literal :=
  let (g', r) := gen g in
  let cs := [::
        [:: neg_lit r; neg_lit c; a1]; [:: neg_lit r; c; a2];
        [:: r; c; neg_lit a2]; [:: r; neg_lit c; neg_lit a1]; [:: r; neg_lit a1; neg_lit a2]
      ] in
  (g', cs, r).

Definition mk_env_ite1 E (g : generator) (c : literal) (a1 a2 : literal) : env * generator * cnf * literal :=
  let (g', r) := gen g in
  let E' := env_upd E (var_of_lit r)
                    (if interp_lit E c then interp_lit E a1 else interp_lit E a2)
                    in
  let cs := [::
        [:: neg_lit r; neg_lit c; a1]; [:: neg_lit r; c; a2];
        [:: r; c; neg_lit a2]; [:: r; neg_lit c; neg_lit a1]; [:: r; neg_lit a1; neg_lit a2]
      ] in
  (E', g', cs, r).

Fixpoint bit_blast_ite w (g : generator) (c : literal) : w.-tuple literal -> w.-tuple literal -> generator * cnf * w.-tuple literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(g_hd, cs_hd, lrs_hd) := bit_blast_ite1 g c ls1_hd ls2_hd in
      let '(g_tl, cs_tl, lrs_tl) := bit_blast_ite g_hd c ls1_tl ls2_tl in
      (g_tl, cs_hd++cs_tl, cons_tuple lrs_hd lrs_tl)
  else
    fun _ _ =>
      (g, [::], [tuple]).

Fixpoint mk_env_ite w E (g : generator) (c : literal) : w.-tuple literal -> w.-tuple literal -> env * generator * cnf * w.-tuple literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(E_hd, g_hd, cs_hd, lrs_hd) := mk_env_ite1 E g c ls1_hd ls2_hd in
      let '(E_tl, g_tl, cs_tl, lrs_tl) := mk_env_ite E_hd g_hd c ls1_tl ls2_tl in
      (E_tl, g_tl, cs_hd++cs_tl, cons_tuple lrs_hd lrs_tl)
  else
    fun _ _ =>
      (E, g, [::], [tuple]).

Lemma bit_blast_ite1_correct :
  forall g bc b1 b2 br E lc l1 l2 g' cs lr,
    bit_blast_ite1 g lc l1 l2 = (g', cs, lr) ->
    enc_bit E lc bc -> enc_bit E l1 b1 -> enc_bit E l2 b2 ->
    interp_cnf E (add_prelude cs) ->
    (if bc then b1 else b2) = br ->
    enc_bit E lr br.
Proof.
  move=> g bc b1 b2 br E lc l1 l2 g' cs lr.
  rewrite /bit_blast_ite1 /enc_bit. case=> _ <- <- /eqP <- /eqP <- /eqP <-.
  rewrite /interp_cnf /= !interp_lit_neg_lit.
  move=> H <-. split_andb. move: H0 H1 H2 H3 H4.
  case: (interp_lit E lc) => /=.
  - move=> H1 _ _ H2 _. rewrite expand_eq. by rewrite H1 H2.
  - move=> _ H1 H2 _ _. rewrite expand_eq. by rewrite H1 H2.
Qed.

Lemma bit_blast_ite_correct :
  forall w g bc (bs1 bs2 : BITS w) brs E lc (ls1 ls2 : w.-tuple literal) g' cs lrs,
    bit_blast_ite g lc ls1 ls2 = (g', cs, lrs) ->
    enc_bit E lc bc -> enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    (if bc then bs1 else bs2) = brs ->
    enc_bits E lrs brs.
Proof.
  elim.
  - done.
  - move=> n IH g bc. case/tupleP => [ibs1_hd ibs1_tl].
    case/tupleP => [ibs2_hd ibs2_tl]. case/tupleP => [obrs_hd obrs_tl].
    move=> E lc. case/tupleP => [ils1_hd ils1_tl]. case/tupleP => [ils2_hd ils2_tl].
    move=> og cs. case/tupleP => [olrs_hd olrs_tl].
    rewrite /bit_blast_ite (lock bit_blast_ite1)
            (lock interp_cnf) /= !theadE !beheadCons -!lock -/bit_blast_ite.
    case Hite_hd: (bit_blast_ite1 g lc ils1_hd ils2_hd) => [[g_hd cs_hd] lrs_hd].
    case Hite_tl: (bit_blast_ite g_hd lc ils1_tl ils2_tl) => [[g_tl cs_tl] lrs_tl].
    case => Hog <- Holrs_hd Holrs_tl => {cs}.
    move=> Henc_c /andP [Henc_hd1 Henc_tl1] /andP [Henc_hd2 Henc_tl2] Hcnf.
    rewrite ite_cons. case => Hobrs_hd Hobrs_tl.
    rewrite add_prelude_append in Hcnf. move/andP: Hcnf => [Hcnf_hd Hcnf_tl].
    apply/andP; split.
    + rewrite -Holrs_hd.
      exact: (bit_blast_ite1_correct Hite_hd Henc_c Henc_hd1 Henc_hd2
                                     Hcnf_hd Hobrs_hd).
    + apply: (IH g_hd bc ibs1_tl ibs2_tl obrs_tl E lc ils1_tl ils2_tl
                 g_tl cs_tl olrs_tl _ Henc_c Henc_tl1 Henc_tl2 Hcnf_tl).
      * rewrite Hite_tl. apply: injective_projections => /=; first by reflexivity.
        apply: val_inj. exact: Holrs_tl.
      * apply: val_inj. exact: Hobrs_tl.
Qed.

Lemma mk_env_ite_is_bit_blast_ite :
  forall w E g lc (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_ite E g lc ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_ite g lc ls1 ls2 = (g', cs, lrs).
Proof.
  elim.
  - rewrite /mk_env_ite /bit_blast_ite => E g lc ls1 ls2 E' g' cs lrs [] _ <- <- <-.
    reflexivity.
  - intros_tuple. dcase_hyps; subst. move=> Hls Henv.
    rewrite (H _ _ _ _ _ _ _ _ _ Henv). rewrite (tval_eq Hls). reflexivity.
Qed.

Lemma mk_env_ite_newer_gen :
  forall w E g lc (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_ite E g lc ls1 ls2 = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  elim.
  - move=> E g lc ls1 ls2 E' g' cs lrs [] _ <- _ _. exact: Pos.leb_refl.
  - intros_tuple. dcase_hyps; subst. move=> Hls Henv.
    move: (H _ _ _ _ _ _ _ _ _ Henv) => Hg1g. apply: (pos_leb_trans _ Hg1g).
    exact: (pos_leb_add_diag_r g 1).
Qed.

Lemma mk_env_ite_newer_res :
  forall w E g lc (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_ite E g lc ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lits g' lrs.
Proof.
  elim.
  - move=> E g lc ls1 ls2 E' g' cs lrs [] _ <- _ <-. done.
  - intros_tuple. dcase_hyps; subst. move=> Hls Henv. rewrite -(tval_eq Hls).
    move: (H _ _ _ _ _ _ _ _ _ Henv) => Hnew. rewrite {}Hnew andbT.
    move: (mk_env_ite_newer_gen Henv) => Hg1g. apply: (newer_than_var_le_newer _ Hg1g).
    exact: newer_than_var_add_diag_r.
Qed.

Lemma mk_env_ite_newer_cnf :
  forall w E g lc (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_ite E g lc ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lc ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  elim.
  - move=> E g lc ls1 ls2 E' g' cs lrs [] _ <- <- _ Hnew_glc Hnew_gls1 Hnew_gls2.
    done.
  - intros_tuple. dcase_hyps; subst. move=> _ Henv /=.
    rewrite !newer_than_lit_neg.
    move/andP: H2 => [Hnew_gls1 Hnew_gls0]. move/andP: H3 => [Hnew_gls2 Hnew_gls3].
    move: (mk_env_ite_newer_gen Henv) => Hg1g'.
    move: (newer_than_lit_add_r 1 H1) => Hnew_g1lc.
    move: (newer_than_lit_add_r 1 Hnew_gls1) => Hnew_g1ls1.
    move: (newer_than_lit_add_r 1 Hnew_gls2) => Hnew_g1ls2.
    move: (newer_than_lits_add_r 1 Hnew_gls0) => Hnew_g1ls0.
    move: (newer_than_lits_add_r 1 Hnew_gls3) => Hnew_g1ls3.
    move: (H _ _ _ _ _ _ _ _ _ Henv Hnew_g1lc Hnew_g1ls0 Hnew_g1ls3) => ->.
    move: (newer_than_lit_le_newer Hnew_g1lc Hg1g') => ->.
    move: (newer_than_lit_le_newer Hnew_g1ls1 Hg1g') => ->.
    move: (newer_than_lit_le_newer Hnew_g1ls2 Hg1g') => ->.
    rewrite /newer_than_lit /newer_than_var /=.
    rewrite (pos_ltb_leb_trans (pos_ltb_add_diag_r g 1) Hg1g'). done.
Qed.

Lemma mk_env_ite_preserve :
  forall w E g lc (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_ite E g lc ls1 ls2 = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  elim.
  - move=> E g lc ls1 ls2 E' g' cs lrs /=. case=> <- _ _ _. exact: env_preserve_refl.
  - intros_tuple. dcase_hyps; intros; subst. move: (H _ _ _ _ _ _ _ _ _ H7) => Hpre.
    exact: (env_preserve_env_upd_succ Hpre).
Qed.

Lemma mk_env_ite_sat :
  forall w E g lc (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_ite E g lc ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lc -> newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  elim.
  - move=> E g lc ls1 ls2 E' g' cs lrs. case=> <- _ <- _ Hnew_lc Hnew_ls1 Hnew_ls2.
    done.
  - intros_tuple. dcase_hyps; intros; subst. rewrite !interp_cnf_cons.
    move/andP: H2 => [Hnew_gls1 Hnew_gls0]. move/andP: H3 => [Hnew_gls2 Hnew_gls3].
    move: (newer_than_lit_le_newer H1 (pos_leb_add_diag_r g 1)) => Hnew_g1lc.
    move: (newer_than_lits_le_newer Hnew_gls0 (pos_leb_add_diag_r g 1)) => Hnew_g1ls0.
    move: (newer_than_lits_le_newer Hnew_gls3 (pos_leb_add_diag_r g 1)) => Hnew_g1ls3.
    rewrite (H _ _ _ _ _ _ _ _ _ H10 Hnew_g1lc Hnew_g1ls0 Hnew_g1ls3) /=.
    rewrite !interp_lit_neg_lit. move: (mk_env_ite_preserve H10) => Hpre.
    move: (newer_than_lit_le_newer Hnew_gls1 (pos_leb_add_diag_r g 1)) => Hnew_g1ls1.
    move: (newer_than_lit_le_newer Hnew_gls2 (pos_leb_add_diag_r g 1)) => Hnew_g1ls2.
    move: (Hpre g (newer_than_var_add_diag_r g 1)). rewrite env_upd_eq.
    move: (env_preserve_lit Hpre Hnew_g1ls1).
    rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hnew_gls1)).
    move: (env_preserve_lit Hpre Hnew_g1ls2).
    rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hnew_gls2)).
    move: (env_preserve_lit Hpre Hnew_g1lc).
    rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq H1)).
    move=> -> -> -> ->.
    by case: (interp_lit E lc); case: (interp_lit E ls1); case: (interp_lit E ls2).
Qed.
