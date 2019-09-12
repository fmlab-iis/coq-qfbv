From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From BitBlasting Require Import Var QFBV CNF BBCommon.
From ssrlib Require Import ZAriths Tactics Bools Seqs.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== bit_blast_eq ===== *)

Fixpoint bit_blast_eq_eq_zip r lsp : cnf :=
  match lsp with
  | [::] => [::]
  | (l1, l2)::tl =>
    let cs_hd := List.map (fun cs => neg_lit r::cs) (cnf_lit_eq l1 l2) in
    let cs_tl := bit_blast_eq_eq_zip r tl in
    catrev cs_hd cs_tl
  end.

Definition bit_blast_eq_choice r (auxs: word) : cnf :=
  [:: r::auxs].

Fixpoint bit_blast_eq_neq_zip g lsp : generator * cnf * word :=
  match lsp with
  | [::] => (g, [::], [::])
  | (l1, l2)::tl =>
    let (g_hd, auxs_hd) := gen g in
    let cs_hd := [:: [:: neg_lit auxs_hd; l1; l2];
                    [:: neg_lit auxs_hd; neg_lit l1; neg_lit l2];
                    [:: auxs_hd; neg_lit l1; l2];
                    [:: auxs_hd; l1; neg_lit l2] ] in
    let '(g_tl, cs_tl, auxs_tl) := bit_blast_eq_neq_zip g_hd tl in
    (g_tl, catrev cs_hd cs_tl, auxs_hd :: auxs_tl)
  end.

Fixpoint mk_env_eq_neq_zip E g lsp : env * generator * cnf * word :=
  match lsp with
  | [::] => (E, g, [::], [::])
  | (l1, l2)::tl =>
    let (g_hd, auxs_hd) := gen g in
    let E' := env_upd E (var_of_lit auxs_hd)
                      (xorb (interp_lit E l1) (interp_lit E l2)) in
    let cs_hd := [:: [:: neg_lit auxs_hd; l1; l2];
                    [:: neg_lit auxs_hd; neg_lit l1; neg_lit l2];
                    [:: auxs_hd; neg_lit l1; l2];
                    [:: auxs_hd; l1; neg_lit l2] ] in
    let '(E_tl, g_tl, cs_tl, auxs_tl) := mk_env_eq_neq_zip E' g_hd tl in
    (E_tl, g_tl, catrev cs_hd cs_tl, auxs_hd :: auxs_tl)
  end.

Definition bit_blast_eq_zip (g : generator) lsp : generator * cnf * literal :=
  let (g_r, r) := gen g in
  let '(g_aux, cs_neq, auxs) := bit_blast_eq_neq_zip g_r lsp in
  let cs_aux := bit_blast_eq_choice r auxs in
  let cs_eq := bit_blast_eq_eq_zip r lsp in
  (g_aux, catrev cs_neq (catrev cs_aux cs_eq), r).

Definition mk_env_eq_zip E g lsp : env * generator * cnf * literal :=
  let (g_r, r) := gen g in
  let E' := env_upd E (var_of_lit r) (interp_word E (unzip1 lsp) == interp_word E (unzip2 lsp)) in
  let '(E_aux, g_aux, cs_neq, auxs) := mk_env_eq_neq_zip E' g_r lsp in
  let cs_aux := bit_blast_eq_choice r auxs in
  let cs_eq := bit_blast_eq_eq_zip r lsp in
  (E_aux, g_aux, catrev cs_neq (catrev cs_aux cs_eq), r).

Definition bit_blast_eq g ls1 ls2 := bit_blast_eq_zip g (extzip_ff ls1 ls2).

Definition mk_env_eq E g ls1 ls2 := mk_env_eq_zip E g (extzip_ff ls1 ls2).

Lemma bit_blast_eq_eq_zip_correct E bsp lsp lr:
  enc_bits E (unzip1 lsp) (unzip1 bsp) ->
  enc_bits E (unzip2 lsp) (unzip2 bsp) ->
  interp_cnf E (add_prelude (bit_blast_eq_eq_zip lr lsp)) ->
  interp_lit E lr ->
  (unzip1 bsp) = (unzip2 bsp).
Proof.
  elim: lsp E bsp lr => [| [ls1_hd ls2_hd] lsp_tl IH] E bsp lr.
  - rewrite !enc_bits_nil_l unzip1_l_nil.
      by case/eqP => ->.
  - rewrite /=.
    case: bsp => [| [bsp_hd1 bsp_hd2] bsp_tl] //=.
    rewrite !enc_bits_cons. move=> /andP [Henc1hd Henc1tl] /andP [Henc2hd Henc2tl].
    move=> Hcnf Hlr.
    rewrite add_prelude_cons in Hcnf. move/andP: Hcnf => [Hcnf_hd1 Hcnf_tl].
    rewrite add_prelude_cons in Hcnf_tl. move/andP: Hcnf_tl => [Hcnf_hd2 Hcnf_tl].
    have Heqhd: bsp_hd1 = bsp_hd2.
    {
      rewrite 2!add_prelude_singleton in Hcnf_hd1 Hcnf_hd2.
      rewrite /= in Hcnf_hd1 Hcnf_hd2. split_andb_hyps.
      rewrite !interp_lit_neg_lit in H0 H2. rewrite Hlr /= !orbF in H0 H2.
      move: (expand_eq (interp_lit E ls1_hd) (interp_lit E ls2_hd)).
      rewrite H0 H2 /= => /eqP Heq. exact: (enc_bit_eq_bit Heq Henc1hd Henc2hd).
    }
    move: (IH _ _ _ Henc1tl Henc2tl Hcnf_tl Hlr) => Heqtl.
    rewrite Heqhd Heqtl. reflexivity.
Qed.

Lemma bit_blast_eq_neq_zip_correct E g bsp lsp g' cs lauxs:
  bit_blast_eq_neq_zip g lsp = (g', cs, lauxs) ->
  enc_bits E (unzip1 lsp) (unzip1 bsp) ->
  enc_bits E (unzip2 lsp) (unzip2 bsp) ->
  interp_cnf E (add_prelude cs) ->
  (exists laux : literal, laux \in lauxs /\ interp_lit E laux) ->
  (unzip1 bsp) <> (unzip2 bsp).
Proof.
  elim: lsp E g bsp g' cs lauxs  => [| [ls1_hd ls2_hd] lsp_tl IH] E g bsp g' cs lauxs /=.
  - case=> _ _ <- _ _ _ Hcontra.
    destruct Hcontra.
    rewrite in_nil in H. by destruct H.
  - dcase (bit_blast_eq_neq_zip (g + 1)%positive lsp_tl) => [[[g_tl cs_tl] auxs_tl] Hblast].
    case=> Hg Hcs Hlauxs.
    case: bsp => [| [bsp_hd1 bsp_hd2] bsp_tl] //=.
    rewrite !enc_bits_cons. move=> /andP [Henc1hd Henc1tl] /andP [Henc2hd Henc2tl].
    move=> Hcnf Hlr.
    move: Hlr => [laux [Hin Haux]].
    rewrite -Hlauxs in_cons in Hin.
    case/orP: Hin.
    + move=> /eqP Hin. rewrite -Hcs in Hcnf. rewrite -/(neg_lit (Pos g)) in Hcnf.
      rewrite  -Hin in Hcnf.
      rewrite add_prelude_expand /= in Hcnf.
      rewrite !interp_lit_neg_lit in Hcnf. rewrite Haux /= !orbF in Hcnf. split_andb_hyps.
      move=> Heq. injection Heq => Heqtl Heqhd. move: H0 H1.
      move: (enc_bit_eq_lit Heqhd Henc1hd Henc2hd) => ->.
        by case: (interp_lit E ls2_hd).
    + move=> Hin.
      have Hexists: (exists laux : literal,
                        laux \in auxs_tl /\ interp_lit E laux).
      {
        exists laux. split; last by exact: Haux.
        exact: Hin.
      }
      have Hcnftl: interp_cnf E (add_prelude cs_tl).
      {
        rewrite -Hcs in Hcnf.
        rewrite add_prelude_cons in Hcnf.
        move/andP: Hcnf => [Hcnf1 Hcnf]. rewrite add_prelude_cons in Hcnf.
        move/andP: Hcnf => [Hcnf2 Hcnf]. rewrite add_prelude_cons in Hcnf.
        move/andP: Hcnf => [Hcnf3 Hcnf]. rewrite add_prelude_cons in Hcnf.
        move/andP: Hcnf => [Hcnf4 Hcnf]. exact: Hcnf.
      }
      move: (IH _ _ _ _ _ _ Hblast Henc1tl Henc2tl Hcnftl Hexists) => Hne Heq.
      apply: Hne. injection Heq => Heqtl Heqhd. exact: Heqtl.
Qed.

Lemma bit_blast_eq_choice_correct E r auxs:
  interp_cnf E (add_prelude (bit_blast_eq_choice r auxs)) ->
  interp_lit E r \/ (exists aux : literal,
                       aux \in auxs /\ interp_lit E aux).
Proof.
  rewrite /bit_blast_eq_choice.
  rewrite add_prelude_expand.
  rewrite interp_cnf_cons /= -/(interp_clause E (r::auxs)).
  rewrite !andbT.
  move/andP=> [_ H].
  case/orP: H => H.
  - by left.
  - right.
    move: (interp_clause_mem H).
    destruct 1.
    exists x; done.
Qed.

Lemma bit_blast_eq_zip_correct E g bsp lsp g' cs lr:
  bit_blast_eq_zip g lsp = (g', cs, lr) ->
  enc_bits E (unzip1 lsp) (unzip1 bsp) ->
  enc_bits E (unzip2 lsp) (unzip2 bsp) ->
  interp_cnf E (add_prelude cs) ->
  enc_bit E lr (unzip1 bsp == unzip2 bsp).
Proof.
  rewrite /bit_blast_eq_zip.
  rewrite /gen. case Hneq: (bit_blast_eq_neq_zip (g+1)%positive lsp) =>
                [[g_aux cs_neq] auxs]. set r := Pos g.
  case=> _ <- <- Henc1 Henc2 Hcnf.
  rewrite add_prelude_catrev add_prelude_cons in Hcnf.
  move/andP: Hcnf=> [Hcnf_neq Hcnf]. move/andP: Hcnf=> [Hcnf_auxs Hcnf_eq].
  rewrite /enc_bit. case Hr: (interp_lit E r).
  - apply/eqP; symmetry. apply/eqP.
    exact: (bit_blast_eq_eq_zip_correct Henc1 Henc2 Hcnf_eq Hr).
  - move: (bit_blast_eq_choice_correct Hcnf_auxs). rewrite Hr.
    case => H; first by elim H. apply/eqP; symmetry. apply/eqP.
    exact: (bit_blast_eq_neq_zip_correct Hneq Henc1 Henc2 Hcnf_neq H).
Qed.

Lemma bit_blast_eq_correct g bs1 bs2 E ls1 ls2 g' cs lr :
  bit_blast_eq g ls1 ls2 = (g', cs, lr) ->
  size ls1 = size ls2 ->
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 -> interp_cnf E (add_prelude cs) ->
  enc_bit E lr (bs1 == bs2).
Proof.
  rewrite /bit_blast_eq => Hbb Hsz Henc1 Henc2 Hcs.
  move: (enc_bits_size Henc1) (enc_bits_size Henc2) => Hs1 Hs2.
  move: (add_prelude_enc_bit_tt Hcs) => Henctt.
  move: (bit_blast_eq_zip_correct Hbb
                                  (enc_bits_unzip1_extzip Henctt Henc1 Henc2)
                                  (enc_bits_unzip2_extzip Henctt Henc1 Henc2) Hcs).

  have H1: (size bs2 <= size bs1) by rewrite -Hs1 -Hs2 Hsz.
  have H2: (size bs1 <= size bs2) by rewrite -Hs1 -Hs2 Hsz.
  rewrite /extzip0.
  rewrite (unzip1_extzip_ll b0 b0 H1).
  rewrite (unzip2_extzip_rl b0 b0 H2).
  done.
Qed.

Lemma mk_env_eq_neq_zip_is_bit_blast_eq_neq_zip E g lsp E' g' cs lr:
  mk_env_eq_neq_zip E g lsp = (E', g', cs, lr) ->
  bit_blast_eq_neq_zip g lsp = (g', cs, lr).
Proof.
  elim: lsp E g E' g' cs lr => [| [ls1_hd ls2_hd] lsp_tl IH ]E g E' g' cs lr //=.
  - intros; dcase_hyps; subst; reflexivity.
  - dcase (mk_env_eq_neq_zip
             (env_upd E g (xorb (interp_lit E ls1_hd) (interp_lit E ls2_hd)))
             (g + 1)%positive lsp_tl) => [[[[E_tl g_tl] cs_tl] auxs_tl] Henv_tl].
    rewrite (IH _ _ _ _ _ _ Henv_tl).
      by case=> _ <- <- <-.
Qed.

Lemma mk_env_eq_zip_is_bit_blast_eq_zip E g lsp E' g' cs lrs:
  mk_env_eq_zip E g lsp = (E', g', cs, lrs) ->
  bit_blast_eq_zip g lsp = (g', cs, lrs).
Proof.
  rewrite /mk_env_eq_zip /bit_blast_eq_zip /=; intros; dcase_hyps; subst.
  move: H.
  dcase (mk_env_eq_neq_zip
           (env_upd E g
                    (interp_word E (unzip1 lsp) == interp_word E (unzip2 lsp)))
           (g + 1)%positive lsp) => [[[[? ?] ?] ?] H].
  rewrite (mk_env_eq_neq_zip_is_bit_blast_eq_neq_zip H).
    by case=> _ <- <- <-.
Qed.

Lemma mk_env_eq_is_bit_blast_eq E g ls1 ls2 E' g' cs lr:
  mk_env_eq E g ls1 ls2 = (E', g', cs, lr) ->
  bit_blast_eq g ls1 ls2 = (g', cs, lr).
Proof.
  exact: mk_env_eq_zip_is_bit_blast_eq_zip.
Qed.

Lemma mk_env_eq_neq_zip_newer_gen E g lsp E' g' cs lr:
  mk_env_eq_neq_zip E g lsp = (E', g', cs, lr) ->
  (g <=? g')%positive.
Proof.
  elim: lsp E g E' g' cs lr => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lr /=.
  - case; t_auto_newer.
  - dcase (mk_env_eq_neq_zip
             (env_upd E g (xorb (interp_lit E ls1_hd) (interp_lit E ls2_hd)))
             (g + 1)%positive lsp_tl) => [[[[E_tl g_tl] cs_tl] auxs_tl] Henv_tl].
    case=> _ <- _ _.
    move: (IH _ _ _ _ _ _ Henv_tl) => H.
    t_auto_newer.
Qed.

Lemma mk_env_eq_zip_newer_gen E g lsp E' g' cs lrs:
  mk_env_eq_zip E g lsp = (E', g', cs, lrs) ->
  (g <=? g')%positive.
Proof.
  rewrite /mk_env_eq_zip /gen /=.
  dcase (mk_env_eq_neq_zip
           (env_upd E g
                    (interp_word E (unzip1 lsp) == interp_word E (unzip2 lsp)))
           (g + 1)%positive lsp) => [[[[? ?] ?] ?] H].
  case=> _ <- _ _.
  move: (mk_env_eq_neq_zip_newer_gen H).
  by t_auto_newer.
Qed.

Lemma mk_env_eq_newer_gen E g ls1 ls2 E' g' cs lr:
  mk_env_eq E g ls1 ls2 = (E', g', cs, lr) ->
  (g <=? g')%positive.
Proof.
  exact: mk_env_eq_zip_newer_gen.
Qed.

Lemma mk_env_eq_neq_zip_newer_res E g lsp E' g' cs lr:
  mk_env_eq_neq_zip E g lsp = (E', g', cs, lr) ->
  newer_than_lits g' lr.
Proof.
  elim: lsp E g E' g' cs lr => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lr /=.
  - by case=> _ <- _ <-.
  - dcase (mk_env_eq_neq_zip
             (env_upd E g (xorb (interp_lit E ls1_hd) (interp_lit E ls2_hd)))
             (g + 1)%positive lsp_tl) => [[[[E_tl g_tl] cs_tl] auxs_tl] Henv_tl].
    case=> _ <- _ <-.
    move: (IH _ _ _ _ _ _ Henv_tl) => H.
    move: (mk_env_eq_neq_zip_newer_gen Henv_tl) => H2.
    t_auto_newer.
    rewrite /newer_than_lit /newer_than_var /=.
    by t_auto_newer.
Qed.

Lemma mk_env_eq_zip_newer_res E g lsp E' g' cs lr:
  mk_env_eq_zip E g lsp = (E', g', cs, lr) ->
  newer_than_lit g' lr.
Proof.
  rewrite /mk_env_eq_zip /gen /=.
  dcase (mk_env_eq_neq_zip
           (env_upd E g
                    (interp_word E (unzip1 lsp) == interp_word E (unzip2 lsp)))
           (g + 1)%positive lsp) => [[[[E_aux g_aux] cs_neq] auxs] H].
  case=> _ <- _ <-.
  move: (mk_env_eq_neq_zip_newer_gen H).
  t_auto_newer.
    rewrite /newer_than_lit /newer_than_var /=.
  by t_auto_newer.
Qed.

Lemma mk_env_eq_newer_res E g ls1 ls2 E' g' cs lr:
  mk_env_eq E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g' lr.
Proof.
  exact: mk_env_eq_zip_newer_res.
Qed.

Lemma bit_blast_eq_eq_zip_newer_cnf g lsp g':
  (g <? g')%positive ->
  newer_than_lits g (unzip1 lsp) -> newer_than_lits g (unzip2 lsp) ->
  newer_than_cnf g' (bit_blast_eq_eq_zip (Pos g) lsp).
Proof.
  elim: lsp g g' => [| [ls1_hd ls2_hd] lsp_tl IH] g g' //=.
  move=> Hgg' /andP [Hnew_gls1hd Hnew_gls1tl] /andP [Hnew_gls2hd Hnew_gls2tl].
  rewrite !newer_than_lit_neg.
  split_andb_goal; t_auto_newer.
  by apply: IH.
Qed.

Lemma mk_env_eq_neq_zip_newer_cnf E g lsp E' g' cs lr:
  mk_env_eq_neq_zip E g lsp = (E', g', cs, lr) ->
  newer_than_lits g (unzip1 lsp) -> newer_than_lits g (unzip2 lsp) ->
  newer_than_cnf g' cs.
Proof.
  elim: lsp E g E' g' cs lr => [| [ls1_hd ls2_hd] lsp_tl IH] E g  E' g' cs lr //=.
  - by case=> _ <- <- _.
  - dcase (mk_env_eq_neq_zip
             (env_upd E g (xorb (interp_lit E ls1_hd) (interp_lit E ls2_hd)))
             (g + 1)%positive lsp_tl) => [[[[E_tl g_tl] cs_tl] auxs_tl] Henv_tl].
    case=> _ <- <- _.
    move: (IH _ _ _ _ _ _ Henv_tl) => H.
    move: (mk_env_eq_neq_zip_newer_gen Henv_tl) => H2.
    move=> /andP [Hnew_gls1hd Hnew_gls1tl] /andP [Hnew_gls2hd Hnew_gls2tl].
    rewrite /= !newer_than_lit_neg.
    split_andb_goal; t_auto_newer.
    all:  rewrite /newer_than_lit /newer_than_var /=; t_auto_newer.
      by apply: H; t_auto_newer.
Qed.

Lemma mk_env_eq_zip_newer_cnf E g lsp E' g' cs lr:
  mk_env_eq_zip E g lsp = (E', g', cs, lr) ->
  newer_than_lits g (unzip1 lsp) -> newer_than_lits g (unzip2 lsp) ->
  newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_eq_zip /gen /=.
  dcase (mk_env_eq_neq_zip
           (env_upd E g
                    (interp_word E (unzip1 lsp) == interp_word E (unzip2 lsp)))
           (g + 1)%positive lsp) => [[[[E_aux g_aux] cs_neq] auxs] H].
  case=> _ <- <- _.
  move: (mk_env_eq_neq_zip_newer_gen H) => Hg1gg Hnew_gls1 Hnew_gls2.
  move: (mk_env_eq_neq_zip_newer_res H) => Hnres_eq_neq.
  move: (mk_env_eq_neq_zip_newer_cnf H) => Hncnf_eq_neq.
  have Hggaux: (g <? g_aux)%positive by t_auto_newer.
  move: (bit_blast_eq_eq_zip_newer_cnf Hggaux Hnew_gls1 Hnew_gls2) => Hncnf_eq_eq.
  t_auto_newer.
  by apply: Hncnf_eq_neq; t_auto_newer.
Qed.

Lemma mk_env_eq_newer_cnf E g ls1 ls2 E' g' cs lr:
  mk_env_eq E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_eq.
  move=> Hzip.
  move: (mk_env_eq_zip_newer_cnf Hzip) => Hncnf_zip.
  move=> Hgtt Hgls1 Hgls2.
    by apply: Hncnf_zip; t_auto_newer.
Qed.

Lemma mk_env_eq_neq_zip_preserve E g lsp E' g' cs lr:
  mk_env_eq_neq_zip E g lsp = (E', g', cs, lr) ->
  env_preserve E E' g.
Proof.
  elim: lsp E g E' g' cs lr => [| [ls1_hd ls2_hd] lsp_tl IH] E g  E' g' cs lr //=.
  - by case=> <- _ _ _.
  - dcase (mk_env_eq_neq_zip
             (env_upd E g (xorb (interp_lit E ls1_hd) (interp_lit E ls2_hd)))
             (g + 1)%positive lsp_tl) => [[[[E_tl g_tl] cs_tl] auxs_tl] Henv_tl].
    case=> <- _ _ _.
    move: (IH _ _ _ _ _ _ Henv_tl) => H.
    have H2: (env_preserve
        (env_upd E g (xorb (interp_lit E ls1_hd) (interp_lit E ls2_hd)))
        E_tl (g)
) by t_auto_preserve.
    by t_auto_preserve.
Qed.

Lemma mk_env_eq_zip_preserve E g lsp E' g' cs lr:
  mk_env_eq_zip E g lsp = (E', g', cs, lr) ->
  env_preserve E E' g.
Proof.
  rewrite /mk_env_eq_zip /gen /=.
  dcase (mk_env_eq_neq_zip
           (env_upd E g
                    (interp_word E (unzip1 lsp) == interp_word E (unzip2 lsp)))
           (g + 1)%positive lsp) => [[[[E_aux g_aux] cs_neq] auxs] H].
  case=> <- _ _ _.
  move: (mk_env_eq_neq_zip_preserve H) => Hpre_eq_neq.
  eapply env_preserve_env_upd_succ.
  exact: Hpre_eq_neq.
Qed.

Lemma mk_env_eq_preserve E g ls1 ls2 E' g' cs lr:
  mk_env_eq E g ls1 ls2 = (E', g', cs, lr) ->
  env_preserve E E' g.
Proof.
  exact: mk_env_eq_zip_preserve.
Qed.

Lemma mk_env_eq_neq_zip_sat E g lsp E' g' cs lr:
  mk_env_eq_neq_zip E g lsp = (E', g', cs, lr) ->
  newer_than_lits g (unzip1 lsp) -> newer_than_lits g (unzip2 lsp) ->
  interp_cnf E' cs.
Proof.
  elim: lsp E g E' g' cs lr => [| [ls1_hd ls2_hd] lsp_tl IH] E g  E' g' cs lr //=.
  - by case=> <- _ <- _.
  - dcase (mk_env_eq_neq_zip
             (env_upd E g (xorb (interp_lit E ls1_hd) (interp_lit E ls2_hd)))
             (g + 1)%positive lsp_tl) => [[[[E_tl g_tl] cs_tl] auxs_tl] Henv_tl].
    case=> <- _ <- _.
    move: (IH _ _ _ _ _ _ Henv_tl) => IHH.
    move: (mk_env_eq_neq_zip_newer_gen Henv_tl) => H2.
    move=> /andP [Hnew_gls1hd Hnew_gls1tl] /andP [Hnew_gls2hd Hnew_gls2tl].
    rewrite /=.
    have -> : (interp_cnf E_tl cs_tl) by apply: IHH; t_auto_newer.
    rewrite /= !interp_lit_neg_lit.
    move: (mk_env_eq_neq_zip_preserve Henv_tl) => Hpre.
    move: (env_preserve_lit Hpre (newer_than_lit_add_diag_r (Pos g) 1))=> /= H_etlg.
    rewrite env_upd_eq in H_etlg.
    rewrite H_etlg.
    have Hnew_g1ls1hd: (newer_than_lit (g+1) ls1_hd) by t_auto_newer.
    have Hnew_g1ls2hd: (newer_than_lit (g+1) ls2_hd) by t_auto_newer.
    move: (env_preserve_lit Hpre Hnew_g1ls1hd) (env_preserve_lit Hpre Hnew_g1ls2hd).
    rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hnew_gls1hd)).
    rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hnew_gls2hd)).
    move=> -> ->.
    by case: (interp_lit E ls1_hd); case: (interp_lit E ls2_hd).
Qed.

Lemma bit_blast_eq_eq_zip_sat_eq (E:env) g lsp:
  E g ->
  interp_word E (unzip1 lsp) == interp_word E (unzip2 lsp) ->
  interp_cnf E (bit_blast_eq_eq_zip (Pos g) lsp).
Proof.
  elim: lsp E g => [| [ls1_hd ls2_hd] lsp_tl IH] E g //=.
  move=> Heg.
  move/eqP => Heq_tl.
  inversion Heq_tl.
  move/eqP: H1 => H1.
  rewrite (IH E _  Heg H1).
  rewrite !interp_lit_neg_lit.
  by rewrite Heg -H0; case: (interp_lit E ls1_hd).
Qed.

Lemma bit_blast_eq_eq_zip_sat_neq (E:env) g lsp:
  ~~ E g ->
  interp_cnf E (bit_blast_eq_eq_zip (Pos g) lsp).
Proof.
  elim: lsp E g => [| [ls1_hd ls2_hd] lsp_tl IH] E g //=.
  move=> Heg.
  rewrite (IH E _  Heg).
  rewrite !interp_lit_neg_lit.
  by rewrite Heg.
Qed.

Lemma mk_env_eq_neq_zip_sat_neq E g lsp E' g' cs lrs:
  mk_env_eq_neq_zip E g lsp = (E', g', cs, lrs) ->
  newer_than_lits g (unzip1 lsp) -> newer_than_lits g (unzip2 lsp) ->
  interp_word E' (unzip1 lsp) != interp_word E' (unzip2 lsp) ->
  interp_clause E' lrs.
Proof.
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g  E' g' cs lrs //=.
  dcase (mk_env_eq_neq_zip
           (env_upd E g (xorb (interp_lit E ls1_hd) (interp_lit E ls2_hd)))
           (g + 1)%positive lsp_tl) => [[[[E_tl g_tl] cs_tl] auxs_tl] Henv_tl].
  case=> <- _ _ <-.
  move: (IH _ _ _ _ _ _ Henv_tl) => IHH.
  move: (mk_env_eq_neq_zip_newer_gen Henv_tl) => H2.
  move=> /andP [Hnew_gls1hd Hnew_gls1tl] /andP [Hnew_gls2hd Hnew_gls2tl].
  rewrite /=.
  move=> Hneq.
  rewrite seq_neq_split in Hneq.
  case/orP: Hneq => Hneq.
  - move: (mk_env_eq_neq_zip_preserve Henv_tl) => Hpre.
    move: (env_preserve_lit Hpre (newer_than_lit_add_diag_r (Pos g) 1))=> /= H_etlg.
    rewrite env_upd_eq in H_etlg.
    rewrite H_etlg.
    have Hpre2: (env_preserve (env_upd E g (xorb (interp_lit E ls1_hd) (interp_lit E ls2_hd))) E_tl g) by t_auto_preserve.
    have Hpre3: (env_preserve E E_tl g) by t_auto_preserve.
    move: (env_preserve_lit Hpre3 Hnew_gls1hd) (env_preserve_lit Hpre3 Hnew_gls2hd).
    move=> <- <-.
      by move: Hneq; case: (interp_lit E_tl ls1_hd); case: (interp_lit E_tl ls2_hd).
  - apply /orP; right.
    by apply IHH; t_auto_newer.
Qed.

Lemma mk_env_eq_zip_sat E g lsp E' g' cs lr:
  mk_env_eq_zip E g lsp = (E', g', cs, lr) ->
  newer_than_lits g (unzip1 lsp) -> newer_than_lits g (unzip2 lsp) ->
  interp_cnf E' cs.
Proof.
  rewrite /mk_env_eq_zip /gen /=.
  dcase (mk_env_eq_neq_zip
           (env_upd E g
                    (interp_word E (unzip1 lsp) == interp_word E (unzip2 lsp)))
           (g + 1)%positive lsp) => [[[[E_aux g_aux] cs_neq] auxs] H].
  case=> <- _ <- _ Hnew_gls1 Hnew_gls2.
  move: (mk_env_eq_neq_zip_newer_gen H) => Hg1gg.
  move: (mk_env_eq_neq_zip_newer_res H) => Hnres_eq_neq.
  move: (mk_env_eq_neq_zip_newer_cnf H) => Hncnf_eq_neq.
  move: (mk_env_eq_neq_zip_sat H) => Hsat_eq_neq.
  have Hggaux: (g <? g_aux)%positive by t_auto_newer.
  rewrite interp_cnf_catrev interp_cnf_cons.
  have -> : interp_cnf E_aux cs_neq by apply Hsat_eq_neq; t_auto_newer.
  rewrite andTb.
  rewrite interp_clause_cons.
  move: (mk_env_eq_neq_zip_preserve H) => Hpre.
  move: (env_preserve_lit Hpre (newer_than_lit_add_diag_r (Pos g) 1))=> /= H_etlg.
  rewrite env_upd_eq in H_etlg.
  move: H_etlg.
  move: (env_preserve_env_upd_succ Hpre) => Hpre2.
  rewrite -(env_preserve_word Hpre2 Hnew_gls1) -(env_preserve_word Hpre2 Hnew_gls2).
  case Heg: (E_aux g).
  - rewrite /=. move=> Heq. move: (Logic.eq_sym Heq) => {Heq} Heq.
    exact: (bit_blast_eq_eq_zip_sat_eq Heg Heq).
  - rewrite /=. move=> Hne. move: (Logic.eq_sym Hne) => {Hne} Hne.
    move/idP/negP: Hne => Hne. move/idP/negP: Heg => Heg.
    rewrite (bit_blast_eq_eq_zip_sat_neq lsp Heg) andbT.
    by apply: (mk_env_eq_neq_zip_sat_neq H _ _ Hne); t_auto_newer.
Qed.

Lemma mk_env_eq_sat E g ls1 ls2 E' g' cs lr:
  mk_env_eq E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  interp_cnf E' cs.
Proof.
  rewrite /mk_env_eq.
  move=> Hzip.
  move: (mk_env_eq_zip_sat Hzip) => Hsat_zip.
  move=> Hgtt Hgls1 Hgls2.
    by apply: Hsat_zip; t_auto_newer.
Qed.
