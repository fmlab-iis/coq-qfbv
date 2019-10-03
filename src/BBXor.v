From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import Var QFBV CNF BBCommon.
From ssrlib Require Import ZAriths Tactics Bools Seqs.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== bit_blast_xor ===== *)

Definition bit_blast_xor1 (g: generator) (a1 a2: literal) : generator * cnf * literal :=
  let (g', r) := gen g in
  let cs := [:: [:: neg_lit r; a1; a2]; [:: neg_lit r; neg_lit a1; neg_lit a2];
               [:: r; neg_lit a1; a2]; [:: r; a1; neg_lit a2]] in
  (g', cs, r).

Definition mk_env_xor1 E g a1 a2 : env * generator * cnf * literal :=
  let (g', r) := gen g in
  let E' := env_upd E (var_of_lit r)
                    (xorb (interp_lit E a1) (interp_lit E a2)) in
  let cs := [:: [:: neg_lit r; a1; a2]; [:: neg_lit r; neg_lit a1; neg_lit a2];
               [:: r; neg_lit a1; a2]; [:: r; a1; neg_lit a2]] in
  (E', g', cs, r).

Fixpoint bit_blast_xor_zip g lsp : generator * cnf * word :=
  match lsp with
  | [::] => (g, [::], [::])
  | (l1, l2)::tl =>
      let '(g_hd, cs_hd, lrs_hd) := bit_blast_xor1 g l1 l2 in
      let '(g_tl, cs_tl, lrs_tl) := bit_blast_xor_zip g_hd tl in
      (g_tl, catrev cs_hd cs_tl, lrs_hd::lrs_tl)
  end.

Fixpoint mk_env_xor_zip E g lsp : env * generator * cnf * word :=
  match lsp with
  | [::] => (E, g, [::], [::])
  | (l1, l2)::tl =>
    let '(E_hd, g_hd, cs_hd, lrs_hd) := mk_env_xor1 E g l1 l2 in
    let '(E_tl, g_tl, cs_tl, lrs_tl) := mk_env_xor_zip E_hd g_hd tl in
    (E_tl, g_tl, catrev cs_hd cs_tl, lrs_hd::lrs_tl)
  end.


Definition bit_blast_xor g ls1 ls2 := bit_blast_xor_zip g (extzip_ff ls1 ls2).

Definition mk_env_xor E g ls1 ls2 := mk_env_xor_zip E g (extzip_ff ls1 ls2).

Lemma bit_blast_xor1_correct E g b1 b2 l1 l2 g' cs lr:
    bit_blast_xor1 g l1 l2 = (g', cs, lr) ->
    enc_bit E l1 b1 -> enc_bit E l2 b2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (xorb b1 b2).
Proof.
  rewrite /bit_blast_xor1 /enc_bit.
  case => _ <- <-. move=> /eqP <- /eqP <-.
  repeat rewrite add_prelude_cons add_prelude_singleton /=.
  rewrite !interp_lit_neg_lit. move=> Hcs.
  split_andb_hyps. move: H4 H5 H6 H7.
  by case: (E g); case: (interp_lit E l1); case: (interp_lit E l2).
Qed.

Lemma mk_env_xor1_is_bit_blast_xor1 E g l1 l2 E' g' cs lr:
    mk_env_xor1 E g l1 l2 = (E', g', cs, lr) ->
    bit_blast_xor1 g l1 l2 = (g', cs, lr).
Proof.
  rewrite /mk_env_xor1 /bit_blast_xor1; intros;
    dite_hyps; dcase_hyps; subst; reflexivity.
Qed.

Lemma mk_env_xor1_newer_gen E g l1 l2 E' g' cs lr:
    mk_env_xor1 E g l1 l2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  rewrite /mk_env_xor1 /=.
  case=> _ <- _ _. exact: pos_leb_add_diag_r.
Qed.

Lemma mk_env_xor1_newer_res E g l1 l2 E' g' cs lr:
    mk_env_xor1 E g l1 l2 = (E', g', cs, lr) ->
    newer_than_lit g l1 ->
    newer_than_lit g l2 ->
    newer_than_lit g' lr.
Proof.
  rewrite /mk_env_xor1 => /=.
  case=> _ <- _ <-. move=> _ _; by apply newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_xor1_newer_cnf E g l1 l2 E' g' cs lr:
    mk_env_xor1 E g l1 l2 = (E', g', cs, lr) ->
    newer_than_lit g l1 -> newer_than_lit g l2 ->
    newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_xor1 /=.
  case=> _ <- <- _. move=> Hgl1 Hgl2 /=. rewrite !newer_than_lit_neg.
  rewrite (newer_than_lit_add_diag_r (Pos g)).
  rewrite (newer_than_lit_add_diag_r (Neg g)).
  by rewrite !newer_than_lit_add_r.
Qed.

Lemma mk_env_xor1_preserve E g l1 l2 E' g' cs lr:
    mk_env_xor1 E g l1 l2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  rewrite /mk_env_xor1 /=.
  case=> <- _ _ _. by apply env_upd_eq_preserve.
Qed.

Lemma mk_env_xor1_sat E g l1 l2 E' g' cs lr:
    mk_env_xor1 E g l1 l2 = (E', g', cs, lr) ->
    newer_than_lit g l1 -> newer_than_lit g l2 ->
    interp_cnf E' cs.
Proof.
  rewrite /mk_env_xor1 /=.
  case=> <- _ <- _ Hgl1 Hgl2.
  move: (newer_than_lit_neq Hgl1) (newer_than_lit_neq Hgl2) => Hngl1 Hngl2.
  rewrite /= !env_upd_eq !interp_lit_neg_lit.
  rewrite (interp_lit_env_upd_neq _ _ Hngl1).
  rewrite (interp_lit_env_upd_neq _ _ Hngl2).
  by case (interp_lit E l1); case (interp_lit E l2).
Qed.

Lemma bit_blast_xor_zip_correct E g bsp lsp g' cs lrs :
  bit_blast_xor_zip g lsp = (g', cs, lrs) ->
  enc_bits E (unzip1 lsp) (unzip1 bsp) -> enc_bits E (unzip2 lsp) (unzip2 bsp) ->
  interp_cnf E (add_prelude cs) -> enc_bits E lrs (map (fun e => xorb e.1 e.2) bsp).
Proof.
  elim: lsp E g bsp g' cs lrs => [| [l1_hd l2_hd] lsp_tl IH] E g bsp g' cs lrs.
  - rewrite !enc_bits_nil_l unzip1_l_nil. case=> _ <- <- /eqP -> _ _ /=.
    exact: enc_bits_nil.
  - rewrite /bit_blast_xor_zip -/bit_blast_xor_zip.
    dcase (bit_blast_xor1 g l1_hd l2_hd) => [[[g_hd cs_hd] lrs_hd] Hbb_hd].
    dcase (bit_blast_xor_zip g_hd lsp_tl) => [[[g_tl cs_tl] lrs_tl] Hbb_tl].
    case=> _ <- <- /=. case: bsp => [| [bsp_hd1 bsp_hd2] bsp_tl] //=.
    rewrite !enc_bits_cons. move=> /andP [Henc1hd Henc1tl] /andP [Henc2hd Henc2tl].
    rewrite add_prelude_catrev => /andP [Hpre_hd Hpre_tl].
    rewrite (bit_blast_xor1_correct Hbb_hd Henc1hd Henc2hd Hpre_hd) andTb.
    by rewrite (IH _ _ _ _ _ _ Hbb_tl Henc1tl Henc2tl Hpre_tl).
Qed.

Lemma bit_blast_xor_correct g bs1 bs2 E ls1 ls2 g' cs lrs :
  bit_blast_xor g ls1 ls2 = (g', cs, lrs) ->
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 -> interp_cnf E (add_prelude cs) ->
  enc_bits E lrs (xorB bs1 bs2).
Proof.
  rewrite /bit_blast_xor => Hbb Henc1 Henc2 Hcs.
  move: (enc_bits_size Henc1) (enc_bits_size Henc2) => Hs1 Hs2.
  move: (add_prelude_enc_bit_tt Hcs) => Henctt.
  exact: (bit_blast_xor_zip_correct Hbb
                                    (enc_bits_unzip1_extzip Henctt Henc1 Henc2)
                                    (enc_bits_unzip2_extzip Henctt Henc1 Henc2) Hcs).
Qed.

Lemma mk_env_xor_zip_is_bit_blast_xor_zip E g lsp E' g' cs lrs :
  mk_env_xor_zip E g lsp = (E', g', cs, lrs) ->
  bit_blast_xor_zip g lsp = (g', cs, lrs).
Proof.
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs.
  - by case=> _ <- <- <-.
  - rewrite /bit_blast_xor_zip -/bit_blast_xor_zip /mk_env_xor_zip -/mk_env_xor_zip.
    dcase (mk_env_xor1 E g ls1_hd ls2_hd) => [[[[E_hd g_hd] cs_hd] lrs_hd] Henv_hd].
    dcase (mk_env_xor_zip E_hd g_hd lsp_tl) => [[[[E_tl g_tl] cs_tl] lrs_tl] Henv_tl].
    case=> _ <- <- <-. rewrite (mk_env_xor1_is_bit_blast_xor1 Henv_hd).
    by rewrite (IH _ _ _ _ _ _ Henv_tl).
Qed.

Lemma mk_env_xor_is_bit_blast_xor E g ls1 ls2 E' g' cs lrs :
  mk_env_xor E g ls1 ls2 = (E', g', cs, lrs) ->
  bit_blast_xor g ls1 ls2 = (g', cs, lrs).
Proof. exact: mk_env_xor_zip_is_bit_blast_xor_zip. Qed.

Lemma mk_env_xor_zip_newer_gen E g lsp E' g' cs lrs :
  mk_env_xor_zip E g lsp = (E', g', cs, lrs) -> (g <=? g')%positive.
Proof.
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs.
  - case=> _ <- _ _. exact: Pos.leb_refl.
  - rewrite /mk_env_xor_zip -/mk_env_xor_zip.
    dcase (mk_env_xor1 E g ls1_hd ls2_hd) => [[[[E_hd g_hd] cs_hd] lsr_hd] Henv_hd].
    dcase (mk_env_xor_zip E_hd g_hd lsp_tl) => [[[[E_tl g_tl] cs_tl] lsr_tl] Henv_tl].
    case=> _ <- _ _. apply: (pos_leb_trans (mk_env_xor1_newer_gen Henv_hd)).
    exact: (IH _ _ _ _ _ _ Henv_tl).
Qed.

Lemma mk_env_xor_newer_gen E g ls1 ls2 E' g' cs lrs :
  mk_env_xor E g ls1 ls2 = (E', g', cs, lrs) -> (g <=? g')%positive.
Proof. exact: mk_env_xor_zip_newer_gen. Qed.

Lemma mk_env_xor_zip_newer_res E g lsp E' g' cs lrs :
  mk_env_xor_zip E g lsp = (E', g', cs, lrs) ->
  newer_than_lits g (unzip1 lsp) -> newer_than_lits g (unzip2 lsp) ->
  newer_than_lits g' lrs.
Proof.
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs.
  - by case=> _ <- _ <- _ _.
  - rewrite /mk_env_xor_zip -/mk_env_xor_zip.
    dcase (mk_env_xor1 E g ls1_hd ls2_hd) => [[[[E_hd g_hd] cs_hd] lsr_hd] Henv_hd].
    dcase (mk_env_xor_zip E_hd g_hd lsp_tl) => [[[[E_tl g_tl] cs_tl] lsr_tl] Henv_tl].
    case=> _ <- _ <- /=. move=> /andP [Hnew1hd Hnew1tl] /andP [Hnew2hd Hnew2tl].
    move: (mk_env_xor1_newer_gen Henv_hd) => Hnewg1.
    move: (mk_env_xor_zip_newer_gen Henv_tl) => Hnewg2.
    move: (mk_env_xor1_newer_res Henv_hd Hnew1hd Hnew2hd)=> Hnew.
    apply/andP; split.
    - exact: (newer_than_lit_le_newer Hnew Hnewg2).
    - rewrite (IH _ _ _ _ _ _ Henv_tl); clear Henv_hd Henv_tl; t_auto_newer.
Qed.

Lemma mk_env_xor_newer_res E g ls1 ls2 E' g' cs lrs :
  mk_env_xor E g ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_lits g' lrs.
Proof.
  rewrite /mk_env_xor => Henv Hnewtt Hnew1 Hnew2.
  apply: (mk_env_xor_zip_newer_res Henv); by t_auto_newer.
Qed.

Lemma mk_env_xor_zip_newer_cnf E g lsp E' g' cs lrs :
  mk_env_xor_zip E g lsp = (E', g', cs, lrs) ->
  newer_than_lits g (unzip1 lsp) -> newer_than_lits g (unzip2 lsp) ->
  newer_than_cnf g' cs.
Proof.
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs.
  - by case=> _ <- <- _ _ _.
  - rewrite /mk_env_xor_zip -/mk_env_xor_zip.
    dcase (mk_env_xor1 E g ls1_hd ls2_hd) => [[[[E_hd g_hd] cs_hd] lsr_hd] Henv_hd].
    dcase (mk_env_xor_zip E_hd g_hd lsp_tl) => [[[[E_tl g_tl] cs_tl] lsr_tl] Henv_tl].
    case=> _ <- <- _ /=. move=> /andP [Hnew1hd Hnew1tl] /andP [Hnew2hd Hnew2tl].
    move: (mk_env_xor1_newer_gen Henv_hd) => Hnewg1.
    move: (mk_env_xor_zip_newer_gen Henv_tl) => Hnewg2.
    move: (mk_env_xor1_newer_cnf Henv_hd Hnew1hd Hnew2hd) => Hnew1.
    rewrite newer_than_cnf_catrev.
    rewrite (IH _ _ _ _ _ _ Henv_tl); clear Henv_hd Henv_tl; by t_auto_newer.
Qed.

Lemma mk_env_xor_newer_cnf E g ls1 ls2 E' g' cs lrs :
  mk_env_xor E g ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_xor => Henv Hnewtt Hnew1 Hnew2.
  apply: (mk_env_xor_zip_newer_cnf Henv); by t_auto_newer.
Qed.

Lemma mk_env_xor_zip_preserve E g lsp E' g' cs lrs :
  mk_env_xor_zip E g lsp = (E', g', cs, lrs) -> env_preserve E E' g.
Proof.
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs.
  - by case=> <- _ _ _.
  - rewrite /mk_env_xor_zip -/mk_env_xor_zip.
    dcase (mk_env_xor1 E g ls1_hd ls2_hd) => [[[[E_hd g_hd] cs_hd] lsr_hd] Henv_hd].
    dcase (mk_env_xor_zip E_hd g_hd lsp_tl) => [[[[E_tl g_tl] cs_tl] lsr_tl] Henv_tl].
    case=> <- _ _ _ /=. move: (mk_env_xor1_preserve Henv_hd) => Hpre_hd.
    move: (IH _ _ _ _ _ _ Henv_tl) => Hpre_tl.
    move: (mk_env_xor1_newer_gen Henv_hd) => Hnewg1.
    clear Henv_hd Henv_tl.
      by t_auto_preserve.
Qed.

Lemma mk_env_xor_preserve E g ls1 ls2 E' g' cs lrs :
  mk_env_xor E g ls1 ls2 = (E', g', cs, lrs) -> env_preserve E E' g.
Proof. exact: mk_env_xor_zip_preserve. Qed.

Lemma mk_env_xor_zip_sat E g lsp E' g' cs lrs :
  mk_env_xor_zip E g lsp = (E', g', cs, lrs) ->
  newer_than_lits g (unzip1 lsp) -> newer_than_lits g (unzip2 lsp) ->
  interp_cnf E' cs.
Proof.
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs.
  - by case=> <- _ <- _ _ _.
  - rewrite /mk_env_xor_zip -/mk_env_xor_zip.
    dcase (mk_env_xor1 E g ls1_hd ls2_hd) => [[[[E_hd g_hd] cs_hd] lsr_hd] Henv_hd].
    dcase (mk_env_xor_zip E_hd g_hd lsp_tl) => [[[[E_tl g_tl] cs_tl] lsr_tl] Henv_tl].
    case=> <- _ <- _ /=. move=> /andP [Hnew1hd Hnew1tl] /andP [Hnew2hd Hnew2tl].
    rewrite interp_cnf_catrev.
    move: (mk_env_xor1_newer_cnf Henv_hd Hnew1hd Hnew2hd) => Hnew1.
    move: (mk_env_xor1_newer_gen Henv_hd) => Hnewg1.
    move: (mk_env_xor1_sat Henv_hd Hnew1hd Hnew2hd) => Hcs_hd.
    move: (mk_env_xor1_preserve Henv_hd) => Hpre_hd.
    move: (mk_env_xor_zip_preserve Henv_tl) => Hpre_tl. apply/andP; split.
    (* interp_cnf E_tl cs_hd *)
    - rewrite (env_preserve_cnf Hpre_tl); clear Henv_hd; last by t_auto_newer. assumption.
    - apply: (IH _ _ _ _ _ _ Henv_tl); clear Henv_hd; by t_auto_newer.
Qed.

Lemma mk_env_xor_sat E g ls1 ls2 E' g' cs lrs :
  mk_env_xor E g ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  interp_cnf E' cs.
Proof.
  rewrite /mk_env_xor => Henv Hnewtt Hnew1 Hnew2.
  apply: (mk_env_xor_zip_sat Henv); by t_auto_newer.
Qed.

Lemma mk_env_xor_zip_size E g lsp E' g' cs lrs :
  mk_env_xor_zip E g lsp = (E', g', cs, lrs) ->
  size lrs == size lsp.
Proof.
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs.
  - by case=> _ _ _ <-.
  - rewrite /mk_env_xor_zip -/mk_env_xor_zip.
    dcase (mk_env_xor1 E g ls1_hd ls2_hd) => [[[[E_hd g_hd] cs_hd] lsr_hd] Henv_hd].
    dcase (mk_env_xor_zip E_hd g_hd lsp_tl) => [[[[E_tl g_tl] cs_tl] lsr_tl] Henv_tl].
    case=> _ _ _ <-.
    rewrite /=.
    move: (IH _ _ _ _ _ _ Henv_tl) => IHH.
      by rewrite (eqP IHH).
Qed.

Lemma mk_env_xor_size E g ls1 ls2 E' g' cs lrs :
  mk_env_xor E g ls1 ls2 = (E', g', cs, lrs) ->
  size ls1 == size ls2 ->
  size lrs == size ls1.
Proof.
  rewrite /mk_env_xor.
  move=> Henv Hsz.
  move: (mk_env_xor_zip_size Henv) => Hsz2.
  rewrite (eqP Hsz2).
  rewrite size_extzip.
  rewrite -(eqP Hsz).
    by rewrite maxnn.
Qed.
