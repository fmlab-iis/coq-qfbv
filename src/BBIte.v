
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon.
From ssrlib Require Import ZAriths Seqs Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_ite ===== *)

Definition bit_blast_ite1 g c l1 l2 : generator * cnf * literal :=
  let (g', r) := gen g in
  let cs := [::
               [:: neg_lit r; neg_lit c; l1];
               [:: neg_lit r; c; l2];
               [:: r; c; neg_lit l2];
               [:: r; neg_lit c; neg_lit l1];
               [:: r; neg_lit l1; neg_lit l2]
            ] in
  (g', cs, r) .

Definition mk_env_ite1 E g c l1 l2 : env * generator * cnf * literal :=
  let (g', r) := gen g in
  let E' := env_upd E (var_of_lit r)
                    (if interp_lit E c then interp_lit E l1 else interp_lit E l2)
  in
  let cs := [::
               [:: neg_lit r; neg_lit c; l1];
               [:: neg_lit r; c; l2];
               [:: r; c; neg_lit l2];
               [:: r; neg_lit c; neg_lit l1];
               [:: r; neg_lit l1; neg_lit l2]
            ] in
  (E', g', cs, r) .

Fixpoint bit_blast_ite_zip g c lsp : generator * cnf * word :=
  match lsp with
  | [::] => (g, [::], [::])
  | (l1, l2)::tl =>
    let '(g_hd, cs_hd, lrs_hd) := bit_blast_ite1 g c l1 l2 in
    let '(g_tl, cs_tl, lrs_tl) := bit_blast_ite_zip g_hd c tl in
    (g_tl, catrev cs_hd cs_tl, lrs_hd::lrs_tl)
  end .

Fixpoint mk_env_ite_zip E g c lsp : env * generator * cnf * word :=
  match lsp with
  | [::] => (E, g, [::], [::])
  | (l1, l2)::tl =>
    let '(E_hd, g_hd, cs_hd, lrs_hd) := mk_env_ite1 E g c l1 l2 in
    let '(E_tl, g_tl, cs_tl, lrs_tl) := mk_env_ite_zip E_hd g_hd c tl in
    (E_tl, g_tl, catrev cs_hd cs_tl, lrs_hd::lrs_tl)
  end .

Definition bit_blast_ite g c ls1 ls2 := bit_blast_ite_zip g c (extzip_ff ls1 ls2) .

Definition mk_env_ite E g c ls1 ls2 := mk_env_ite_zip E g c (extzip_ff ls1 ls2) .

Lemma bit_blast_ite_zip_size_ss g l lsp g' cs rlrs :
  bit_blast_ite_zip g l lsp = (g', cs, rlrs) ->
  size rlrs = size lsp.
Proof.
  elim: lsp g l g' cs rlrs => [| [l1 l2] lsp IH] l g g' cs rlrs //=.
  - case=> ? ? ?; subst. reflexivity.
  - dcase (bit_blast_ite_zip (l + 1)%positive g lsp) => [[[g_tl cs_tl] lrs_tl] Hbb_tl].
    case=> ? ? ?; subst. rewrite /=. rewrite (IH _ _ _ _ _ Hbb_tl). reflexivity.
Qed.

Lemma bit_blast_ite_size_ss g l ls1 ls2 g' cs rlrs :
  bit_blast_ite g l ls1 ls2 = (g', cs, rlrs) -> size ls1 = size ls2->
  size rlrs = size ls1.
Proof.
  rewrite /bit_blast_ite. move=> Hbb Hs12. move: (bit_blast_ite_zip_size_ss Hbb).
  rewrite /extzip_ff. rewrite size_extzip. rewrite Hs12 maxnn. by apply.
Qed.

Lemma bit_blast_ite1_correct E g bc b1 b2 lc l1 l2 g' cs lr :
  bit_blast_ite1 g lc l1 l2 = (g', cs, lr) ->
  enc_bit E lc bc -> enc_bit E l1 b1 -> enc_bit E l2 b2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bit E lr (if bc then b1 else b2) .
Proof .
  rewrite /bit_blast_ite1 /enc_bit.
  case=> _ <- <- /eqP <- /eqP <- /eqP <- /= .
  move => /andP /= [_ Hcs] .
  rewrite !interp_lit_neg_lit in Hcs .
  move : Hcs.
  by case : (E g); case : (interp_lit E lc); case : (interp_lit E l1); case : (interp_lit E l2) .
Qed .

Lemma bit_blast_ite_zip_correct E g bc bsp lc lsp g' cs lrs :
  bit_blast_ite_zip g lc lsp = (g', cs, lrs) ->
  enc_bit E lc bc ->
  enc_bits E (unzip1 lsp) (unzip1 bsp) ->
  enc_bits E (unzip2 lsp) (unzip2 bsp) ->
  interp_cnf E (add_prelude cs) -> enc_bits E lrs (if bc then unzip1 bsp else unzip2 bsp) .
Proof .
  elim: lsp E g bsp g' cs lrs => [| [l1_hd l2_hd] lsp_tl IH] E g bsp g' cs lrs .
  - rewrite !enc_bits_nil_l !unzip1_l_nil !unzip2_l_nil .
    case=> _ <- <- _ /eqP -> _ _ /= .
    by case : bc .
  - rewrite /bit_blast_ite_zip (lock bit_blast_ite1) /= -lock -/bit_blast_ite_zip .
    dcase (bit_blast_ite1 g lc l1_hd l2_hd) => [[[g_hd cs_hd] lrs_hd] Hbb_hd].
    dcase (bit_blast_ite_zip g_hd lc lsp_tl) => [[[g_tl cs_tl] lrs_tl] Hbb_tl].
    case => _ <- <- .
    case: bsp => [| [b_hd1 b_hd2] bsp_tl] //= .
    rewrite !enc_bits_cons .
    move=> Henclcbc /andP [Henc1hd Henc1tl] /andP [Henc2hd Henc2tl] .
    rewrite add_prelude_catrev => /andP [Hpre_hd Hpre_tl] .
    move : (IH E g_hd bsp_tl g_tl cs_tl lrs_tl Hbb_tl Henclcbc Henc1tl Henc2tl Hpre_tl) .
    move : (bit_blast_ite1_correct Hbb_hd Henclcbc Henc1hd Henc2hd Hpre_hd) .
    case bc => Henclrs_hd Henclrs_tl;
    by rewrite enc_bits_cons Henclrs_hd Henclrs_tl .
Qed .

Lemma bit_blast_ite_correct g bc bs1 bs2 E lc ls1 ls2 g' cs lrs :
  size ls1 == size ls2 ->
  bit_blast_ite g lc ls1 ls2 = (g', cs, lrs) ->
  enc_bit E lc bc -> enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 -> interp_cnf E (add_prelude cs) ->
  enc_bits E lrs (if bc then bs1 else bs2) .
Proof .
  rewrite /bit_blast_ite => Hsize Hbb Henclc Henc1 Henc2 Hcs.
  move: (enc_bits_size Henc1) (enc_bits_size Henc2) => Hs1 Hs2.
  rewrite Hs1 Hs2 in Hsize .
  move: (add_prelude_enc_bit_tt Hcs) => Henctt.
  move: (bit_blast_ite_zip_correct Hbb Henclc
          (enc_bits_unzip1_extzip Henctt Henc1 Henc2)
          (enc_bits_unzip2_extzip Henctt Henc1 Henc2) Hcs).
  rewrite /extzip0 (extzip_zip_ss _ _ (eqP Hsize))
          (unzip1_zip (eq_leq (eqP Hsize))) .
  rewrite eq_sym in Hsize .
  rewrite (unzip2_zip (eq_leq (eqP Hsize))) // .
Qed.

Lemma mk_env_ite1_is_bit_blast_ite1 E g lc l1 l2 E' g' cs lr :
  mk_env_ite1 E g lc l1 l2 = (E', g', cs, lr) -> bit_blast_ite1 g lc l1 l2 = (g', cs, lr).
Proof .
  rewrite /mk_env_ite1 /bit_blast_ite1; intros;
    dite_hyps; dcase_hyps; subst; reflexivity.
Qed.

Lemma mk_env_ite_zip_is_bit_blast_ite_zip E g lc lsp E' g' cs lrs :
  mk_env_ite_zip E g lc lsp = (E', g', cs, lrs) ->
  bit_blast_ite_zip g lc lsp = (g', cs, lrs).
Proof .
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs .
  - by case=> _ <- <- <-.
  - rewrite /mk_env_ite_zip -/mk_env_ite_zip .
    dcase (mk_env_ite1 E g lc ls1_hd ls2_hd) => [[[[E_hd g_hd] cs_hd] lrs_hd] Henv_hd] .
    dcase (mk_env_ite_zip E_hd g_hd lc lsp_tl) => [[[[E_tl g_tl] cs_tl] lrs_tl] Henv_tl] .
    case=> _ <- <- <-.
    rewrite /bit_blast_ite_zip -/bit_blast_ite_zip .
    rewrite (mk_env_ite1_is_bit_blast_ite1 Henv_hd) .
    by rewrite (IH _ _ _ _ _ _ Henv_tl).
Qed.

Lemma mk_env_ite_is_bit_blast_ite E g lc ls1 ls2 E' g' cs lrs :
  mk_env_ite E g lc ls1 ls2 = (E', g', cs, lrs) ->
  bit_blast_ite g lc ls1 ls2 = (g', cs, lrs).
Proof .
  exact: mk_env_ite_zip_is_bit_blast_ite_zip.
Qed.

Lemma mk_env_ite1_newer_gen E g lc l1 l2 E' g' cs lr :
  mk_env_ite1 E g lc l1 l2 = (E', g', cs, lr) -> (g <=? g')%positive.
Proof .
  rewrite /mk_env_ite1.
  case => _ <- _ _ .
  exact : pos_leb_add_diag_r .
Qed .

Lemma mk_env_ite_zip_newer_gen E g lc lsp E' g' cs lrs :
  mk_env_ite_zip E g lc lsp = (E', g', cs, lrs) -> (g <=? g')%positive .
Proof .
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs .
  - case => _ <- _ _; exact : Pos.leb_refl .
  - rewrite /mk_env_ite_zip -/mk_env_ite_zip .
    dcase (mk_env_ite1 E g lc ls1_hd ls2_hd) => [[[[E_hd g_hd] cs_hd] lsr_hd] Henv_hd] .
    dcase (mk_env_ite_zip E_hd g_hd lc lsp_tl) => [[[[E_tl g_tl] cs_tl] lsr_tl] Henv_tl] .
    case => _ <- _ _ .
    apply : (pos_leb_trans (mk_env_ite1_newer_gen Henv_hd)) .
    exact : (IH _ _ _ _ _ _ Henv_tl) .
Qed .

Lemma mk_env_ite_newer_gen E g lc ls1 ls2 E' g' cs lrs :
  mk_env_ite E g lc ls1 ls2 = (E', g', cs, lrs) -> (g <=? g')%positive .
Proof .
  exact: mk_env_ite_zip_newer_gen .
Qed .

Lemma mk_env_ite1_newer_res E g lc l1 l2 E' g' cs lr :
  mk_env_ite1 E g lc l1 l2 = (E', g', cs, lr) ->
  newer_than_lit g' lr .
Proof .
  rewrite /mk_env_ite1 .
  case => _ <- _ <- .
  exact : newer_than_lit_add_diag_r .
Qed .

Lemma mk_env_ite_zip_newer_res E g lc lsp E' g' cs lrs :
  mk_env_ite_zip E g lc lsp = (E', g', cs, lrs) ->
  newer_than_lits g' lrs.
Proof .
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs .
  - by case=> _ <- _ <- .
  - rewrite /mk_env_ite_zip -/mk_env_ite_zip .
    dcase (mk_env_ite1 E g lc ls1_hd ls2_hd) => [[[[E_hd g_hd] cs_hd] lsr_hd] Henv_hd] .
    dcase (mk_env_ite_zip E_hd g_hd lc lsp_tl) => [[[[E_tl g_tl] cs_tl] lsr_tl] Henv_tl] .
    case=> _ <- _ <- .
    rewrite newer_than_lits_cons (IH _ _ _ _ _ _ Henv_tl) .
    apply/andP; split; last done .
    move : (mk_env_ite1_newer_res Henv_hd)
             (mk_env_ite_zip_newer_gen Henv_tl) .
    exact : newer_than_lit_le_newer .
Qed .

Lemma mk_env_ite_newer_res E g lc ls1 ls2 E' g' cs lrs :
  mk_env_ite E g lc ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_lits g' lrs .
Proof .
  rewrite /mk_env_ite => Henv .
  apply: (mk_env_ite_zip_newer_res Henv) .
Qed .

Lemma mk_env_ite1_newer_cnf E g lc l1 l2 E' g' cs lr :
  mk_env_ite1 E g lc l1 l2 = (E', g', cs, lr) ->
  newer_than_lit g lc ->
  newer_than_lit g l1 -> newer_than_lit g l2 ->
  newer_than_cnf g' cs .
Proof .
  rewrite /mk_env_ite1 .
  case => _ <- <- _ => Hlc Hl1 Hl2 .
  by repeat t_auto_newer .
Qed .

Lemma mk_env_ite_zip_newer_cnf E g lc lsp E' g' cs lrs :
  mk_env_ite_zip E g lc lsp = (E', g', cs, lrs) ->
  newer_than_lit g lc ->
  newer_than_lits g (unzip1 lsp) ->
  newer_than_lits g (unzip2 lsp) ->
  newer_than_cnf g' cs .
Proof .
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs .
  - by case=> _ <- <- _ .
  - rewrite /mk_env_ite_zip -/mk_env_ite_zip .
    dcase (mk_env_ite1 E g lc ls1_hd ls2_hd) =>
    [[[[E_hd g_hd] cs_hd] lsr_hd] Henv_hd] .
    dcase (mk_env_ite_zip E_hd g_hd lc lsp_tl) =>
    [[[[E_tl g_tl] cs_tl] lsr_tl] Henv_tl] .
    case=> _ <- <- _ .
    move=> Hnewlc /= /andP [Hnew1hd Hnew1tl]
                  /andP [Hnew2hd Hnew2tl] .
    move: (mk_env_ite_zip_newer_gen Henv_tl) => Hnewg2 .
    move: (mk_env_ite1_newer_cnf Henv_hd Hnewlc Hnew1hd Hnew2hd) => Hnew1 .
    rewrite newer_than_cnf_catrev .
    apply/andP; split; first by rewrite (newer_than_cnf_le_newer Hnew1 Hnewg2) .
    move : (mk_env_ite1_newer_gen Henv_hd) => Hnewghd .
    apply: (IH _ _ _ _ _ _ Henv_tl) .
    + by rewrite (newer_than_lit_le_newer Hnewlc Hnewghd) .
    + by rewrite (newer_than_lits_le_newer Hnew1tl Hnewghd) .
    + by rewrite (newer_than_lits_le_newer Hnew2tl Hnewghd) .
Qed .

Lemma mk_env_ite_newer_cnf E g lc ls1 ls2 E' g' cs lrs :
  mk_env_ite E g lc ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_lit g lit_ff ->
  newer_than_lit g lc -> newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs .
Proof .
  rewrite /mk_env_ite => Henv Hnewff Hnewlc Hnew1 Hnew2 .
  apply: (mk_env_ite_zip_newer_cnf Henv) .
  - done .
  - rewrite unzip1_extzip newer_than_lits_cat
            newer_than_lits_copy; last done .
    apply /andP; split; done .
  - rewrite unzip2_extzip newer_than_lits_cat
            newer_than_lits_copy; last done .
    apply /andP; split; done .
Qed .

Lemma mk_env_ite1_preserve E g lc l1 l2 E' g' cs lr :
  mk_env_ite1 E g lc l1 l2 = (E', g', cs, lr) -> env_preserve E E' g .
Proof .
  rewrite /mk_env_ite1 .
  case => <- _ _ _ /= .
  case : (interp_lit E lc); exact : env_upd_eq_preserve .
Qed .

Lemma mk_env_ite_zip_preserve E g lc lsp E' g' cs lrs :
  mk_env_ite_zip E g lc lsp = (E', g', cs, lrs) -> env_preserve E E' g .
Proof .
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs .
  - by case=> <- _ _ _.
  - rewrite /mk_env_ite_zip -/mk_env_ite_zip .
    dcase (mk_env_ite1 E g lc ls1_hd ls2_hd) => [[[[E_hd g_hd] cs_hd] lsr_hd] Henv_hd] .
    dcase (mk_env_ite_zip E_hd g_hd lc lsp_tl) => [[[[E_tl g_tl] cs_tl] lsr_tl] Henv_tl] .
    case=> <- _ _ _ .
    move: (mk_env_ite1_preserve Henv_hd) => Hpre_hd .
    move: (IH _ _ _ _ _ _ Henv_tl) => Hpre_tl.
    move: (mk_env_ite1_newer_gen Henv_hd) => Hnewg1 .
    move : (env_preserve_le Hpre_tl Hnewg1) => Hpre_tlg .
    exact : (env_preserve_trans Hpre_hd Hpre_tlg) .
Qed .

Lemma mk_env_ite_preserve E g lc ls1 ls2 E' g' cs lrs :
  mk_env_ite E g lc ls1 ls2 = (E', g', cs, lrs) -> env_preserve E E' g .
Proof .
  exact : mk_env_ite_zip_preserve .
Qed .

Lemma mk_env_ite1_sat E g lc l1 l2 E' g' cs lr :
  mk_env_ite1 E g lc l1 l2 = (E', g', cs, lr) ->
  newer_than_lit g lc ->
  newer_than_lit g l1 -> newer_than_lit g l2 -> interp_cnf E' cs .
Proof .
  rewrite /mk_env_ite1 .
  case => <- _ <- _ Hnewlc Hnewl1 Hnewl2 .
  move : (newer_than_lit_neq Hnewlc) (newer_than_lit_neq Hnewl1) (newer_than_lit_neq Hnewl2) => Hnlc Hnl1 Hnl2 .
  rewrite /= !env_upd_eq !interp_lit_neg_lit
          !(interp_lit_env_upd_neq _ _ Hnlc)
          !(interp_lit_env_upd_neq _ _ Hnl1)
          !(interp_lit_env_upd_neq _ _ Hnl2) .
  by case (interp_lit E lc); case (interp_lit E l1); case (interp_lit E l2) .
Qed .

Lemma mk_env_ite_zip_sat E g lc lsp E' g' cs lrs :
  mk_env_ite_zip E g lc lsp = (E', g', cs, lrs) ->
  newer_than_lit g lc ->
  newer_than_lits g (unzip1 lsp) -> newer_than_lits g (unzip2 lsp) ->
  interp_cnf E' cs .
Proof .
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs .
  - by case=> <- _ <- _ _ _.
  - rewrite /mk_env_ite_zip -/mk_env_ite_zip .
    dcase (mk_env_ite1 E g lc ls1_hd ls2_hd) => [[[[E_hd g_hd] cs_hd] lsr_hd] Henv_hd] .
    dcase (mk_env_ite_zip E_hd g_hd lc lsp_tl) => [[[[E_tl g_tl] cs_tl] lsr_tl] Henv_tl] .
    case=> <- _ <- _ .
    move=> /= Hnewglc /andP [Hnew1hd Hnew1tl] /andP [Hnew2hd Hnew2tl] .
    rewrite interp_cnf_catrev .
    move: (mk_env_ite1_newer_cnf Henv_hd Hnewglc Hnew1hd Hnew2hd) => Hnew1 .
    move: (mk_env_ite1_newer_gen Henv_hd) => Hnewg1 .
    move: (mk_env_ite1_sat Henv_hd Hnewglc Hnew1hd Hnew2hd) => Hcs_hd .
    move: (mk_env_ite1_preserve Henv_hd) => Hpre_hd .
    move: (mk_env_ite_zip_preserve Henv_tl) => Hpre_tl.
    apply/andP; split .
  - rewrite (env_preserve_cnf Hpre_tl); by assumption .
  - apply: (IH _ _ _ _ _ _ Henv_tl) .
    + by exact : (newer_than_lit_le_newer Hnewglc Hnewg1) .
    + exact : (newer_than_lits_le_newer Hnew1tl Hnewg1) .
    + exact : (newer_than_lits_le_newer Hnew2tl Hnewg1) .
Qed .

Lemma mk_env_ite_sat E g lc ls1 ls2 E' g' cs lrs :
  mk_env_ite E g lc ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lit g lc ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  interp_cnf E' cs .
Proof .
  move => Henv hgt Hglc Hgls1 Hgls2 .
  apply : (mk_env_ite_zip_sat Henv); first by done .
  - rewrite unzip1_extzip newer_than_lits_cat
            newer_than_lits_copy; last done .
    apply /andP; split; done .
  - rewrite unzip2_extzip newer_than_lits_cat
            newer_than_lits_copy; last done .
    apply /andP; split; done .
Qed .

Lemma mk_env_ite1_env_equal E1 E2 g c l1 l2 E1' E2' g1' g2' cs1 cs2 lr1 lr2 :
  env_equal E1 E2 ->
  mk_env_ite1 E1 g c l1 l2 = (E1', g1', cs1, lr1) ->
  mk_env_ite1 E2 g c l1 l2 = (E2', g2', cs2, lr2) ->
  env_equal E1' E2' /\ g1' = g2' /\ cs1 = cs2 /\ lr1 = lr2.
Proof.
  rewrite /mk_env_ite1 => Heq. dcase (gen g) => [[g' r] Hg].
  case=> ? ? ? ?; case=> ? ? ? ?; subst. repeat split.
  rewrite (env_equal_interp_lit l1 Heq) (env_equal_interp_lit l2 Heq)
          (env_equal_interp_lit c Heq).
  apply: env_equal_upd. assumption.
Qed.

Lemma mk_env_ite_zip_env_equal E1 E2 g c lsp E1' E2' g1' g2' cs1 cs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_ite_zip E1 g c lsp = (E1', g1', cs1, lrs1) ->
  mk_env_ite_zip E2 g c lsp = (E2', g2', cs2, lrs2) ->
  env_equal E1' E2' /\ g1' = g2' /\ cs1 = cs2 /\ lrs1 = lrs2.
Proof.
  elim: lsp E1 E2 g c E1' E2' g1' g2' cs1 cs2 lrs1 lrs2
  => [| [l1 l2] lsp IH] //= E1 E2 g c E1' E2' g1' g2' cs1 cs2 lrs1 lrs2 Heq.
  - case=> ? ? ? ?; case=> ? ? ? ?; subst. done.
  - rewrite !(env_equal_interp_lit _ Heq).
    dcase (mk_env_ite_zip
             (env_upd E1 g (if interp_lit E2 c then interp_lit E2 l1 else interp_lit E2 l2))
             (g + 1)%positive c lsp) => [[[[E_tl1 g_tl1] cs_tl1] lrs_tl1] Hv_tl1].
    dcase (mk_env_ite_zip
             (env_upd E2 g (if interp_lit E2 c then interp_lit E2 l1 else interp_lit E2 l2))
             (g + 1)%positive c lsp) => [[[[E_tl2 g_tl2] cs_tl2] lrs_tl2] Hv_tl2].
    case=> ? ? ? ?; case=> ? ? ? ?; subst.
    move: (env_equal_upd g (if interp_lit E2 c then interp_lit E2 l1 else interp_lit E2 l2) Heq)
    => Heq1.
    move: (IH _ _ _ _ _ _ _ _ _ _ _ _ Heq1 Hv_tl1 Hv_tl2) => [Heq3 [? [? ?]]]; subst.
    done.
Qed.

Lemma mk_env_ite_env_equal E1 E2 g c ls1 ls2 E1' E2' g1' g2' cs1 cs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_ite E1 g c ls1 ls2 = (E1', g1', cs1, lrs1) ->
  mk_env_ite E2 g c ls1 ls2 = (E2', g2', cs2, lrs2) ->
  env_equal E1' E2' /\ g1' = g2' /\ cs1 = cs2 /\ lrs1 = lrs2.
Proof. exact: mk_env_ite_zip_env_equal. Qed.
