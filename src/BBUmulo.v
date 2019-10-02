From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From BitBlasting Require Import Var QFBV CNF BBCommon BBConst BBZeroExtend BBMul.
From ssrlib Require Import ZAriths Tactics Bools Seqs.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section BBUmulo.

  Infix "++r" := catrev (right associativity, at level 60): seq_scope.

  Fixpoint bit_blast_umulo_rec_zip g lsp: generator * cnf * literal * literal:=
    match lsp with
    | [::] => (g, [::], lit_ff, lit_ff)
    | (ls1_low, ls2_high)::tl =>
      let '(g1, cs_tl, r_or_tl, r_and_or_tl) := bit_blast_umulo_rec_zip g tl in
      let (g2, r_or) := gen g1 in
      let (g3, r_and_or) := gen g2 in
      (* or sum  r_or <-> r_or_tl || ls1_low *)
      let cs_prefix_or := [::
                             [:: neg_lit r_or_tl; r_or];
                             [:: r_or_tl; ls1_low; neg_lit r_or];
                             [:: neg_lit ls1_low; r_or]
                          ] in
      (* and r_and_or <-> r_and_or_tl || (r_or && ls2_high) *)
      let cs_and_or := [::
                          [:: neg_lit r_or; neg_lit ls2_high; r_and_or];
                          [:: r_or; r_and_or_tl; neg_lit r_and_or];
                          [:: ls2_high; r_and_or_tl; neg_lit r_and_or];
                          [:: neg_lit r_and_or_tl; r_and_or]
                       ] in
      (g3, cs_tl ++r cs_prefix_or ++r cs_and_or, r_or, r_and_or)
    end.


  Definition bit_blast_umulo_rec g ls1 ls2 :=
    bit_blast_umulo_rec_zip g (extzip_ff ls1 (rev ls2)).

  Example test_orb:
    orb_all [:: false ; true ;true] = true.
  Proof. reflexivity. Qed.

  Example test_orb2:
    orb_all [:: false ; false ; false] = false.
  Proof. reflexivity. Qed.

  Lemma bit_blast_umulo_rec_zip_correct1 E g bsp lsp g' cs lr_or lr_and_or :
    bit_blast_umulo_rec_zip g lsp = (g', cs, lr_or, lr_and_or) ->
    enc_bits E (unzip1 lsp) (unzip1 bsp) ->
    enc_bits E (unzip2 lsp) (unzip2 bsp) ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr_or (orb_all (unzip1 bsp)).
  Proof.
    elim: lsp E g bsp g' cs lr_or lr_and_or
    => [| [ls1_hd ls2_hd] lsp_tl IH] E g bsp g' cs lr_or lr_and_or //=.
    - case=> _ _ <- _.
      rewrite !enc_bits_nil_l unzip1_l_nil unzip2_l_nil.
      move/eqP => H _; rewrite H /=.
      exact: add_prelude_enc_bit_ff.
    - case: bsp => [| [bsp_hd1 bsp_hd2] bsp_tl] //=.
      dcase (bit_blast_umulo_rec_zip g lsp_tl) => [[[[g3 cs_tl] r_or_tl] r_and_or_tl] Hblast].
      case=> Hog <- Holr _ .
      rewrite !enc_bits_cons.
      move=> /andP [Henc1hd Henc1tl] /andP [Henc2hd Henc2tl].
      rewrite add_prelude_catrev.
      move/andP => [Hcnf_tl Hcnf].
      repeat rewrite add_prelude_cons add_prelude_singleton in Hcnf.
      rewrite /= !interp_lit_neg_lit /= in Hcnf.
      t_clear. split_andb_hyps.
      repeat match goal with H: is_true (E var_tt) |- _ => clear H end.
      move: (IH _ _ _ _ _ _ _ Hblast Henc1tl Henc2tl Hcnf_tl) => IHH.
      move: H7 H8 H9 H10 H11 H12 H13.
      rewrite -Holr.
      move: Henc1hd Henc2hd IHH.
      rewrite /enc_bit /=.
      move=> /eqP -> /eqP -> /eqP ->.
        by case (interp_lit E r_or_tl);
          case (interp_lit E r_and_or_tl);
          case (E g3);
          case (E (g3+1)%positive);
          case (bsp_hd1);
          case (bsp_hd2);
          case (orb_all (unzip1 bsp_tl)).
  Qed.

  Lemma bit_blast_umulo_rec_zip_correct2 E g bsp lsp g' cs lr_or lr_and_or :
    bit_blast_umulo_rec_zip g lsp = (g', cs, lr_or, lr_and_or) ->
    enc_bits E (unzip1 lsp) (unzip1 bsp) ->
    enc_bits E (unzip2 lsp) (unzip2 bsp) ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr_and_or (andb_orb_all_zip bsp).
  Proof.
    elim: lsp E g bsp g' cs lr_or lr_and_or
    => [| [ls1_hd ls2_hd] lsp_tl IH] E g bsp g' cs lr_or lr_and_or //=.
    - case=> _ <- _ <-.
      rewrite !enc_bits_nil_l unzip1_l_nil unzip2_l_nil.
      move/eqP => H _; rewrite H /=.
      exact: add_prelude_enc_bit_ff.
    - case: bsp => [| [bsp_hd1 bsp_hd2] bsp_tl] //=.
      dcase (bit_blast_umulo_rec_zip g lsp_tl) => [[[[g1 cs_tl] r_or_tl] r_and_or_tl] Hblast].
      case=> _ <- _ <-.
      rewrite !enc_bits_cons.
      move=> /andP [Henc1hd Henc1tl] /andP [Henc2hd Henc2tl].
      rewrite add_prelude_catrev.
      move/andP => [Hcnf_tl Hcnf].
      repeat rewrite add_prelude_cons add_prelude_singleton in Hcnf.
      rewrite /= !interp_lit_neg_lit /= in Hcnf.
      t_clear. split_andb_hyps.
      repeat match goal with H: is_true (E var_tt) |- _ => clear H end.
      move: (IH _ _ _ _ _ _ _ Hblast Henc1tl Henc2tl Hcnf_tl) => IHH.
      move: (bit_blast_umulo_rec_zip_correct1 Hblast Henc1tl Henc2tl Hcnf_tl) => Henc_or.
      move: H7 H8 H9 H10 H11 H12 H13.
      move: Henc1hd Henc2hd IHH Henc_or.
      rewrite /enc_bit /=.
      move=> /eqP -> /eqP -> /eqP -> /eqP ->.
        by case: (andb_orb_all_zip bsp_tl);
          case: (E (g1+1)%positive);
          case: (E g1);
          case: (bsp_hd1);
          case: (bsp_hd2);
          case: (orb_all(unzip1 bsp_tl));
          case: (interp_lit E r_or_tl).
  Qed.

  Lemma bit_blast_umulo_rec_correct g bs1 bs2 E ls1 ls2 g' cs lr_or lr_and_or :
    bit_blast_umulo_rec g ls1 ls2 = (g', cs, lr_or, lr_and_or) ->
    size ls1 == size ls2 ->
    enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr_or (orb_all bs1) && enc_bit E lr_and_or (andb_orb_all bs1 bs2).
  Proof.
    rewrite /bit_blast_umulo_rec.
    move=> Hblast Hsz Henc1 Henc2 Hcnf.
    move: (add_prelude_enc_bit_tt Hcnf) => Henctt.
    apply enc_bits_rev in Henc2.
    move: (enc_bits_size Henc1) (enc_bits_size Henc2) => Hs1 Hs2.
    move: (enc_bits_unzip1_extzip Henctt Henc1 Henc2) => Hzip1.
    move: (enc_bits_unzip2_extzip Henctt Henc1 Henc2) => Hzip2.
    move: (bit_blast_umulo_rec_zip_correct1 Hblast Hzip1 Hzip2 Hcnf) => Henc_lr_or.
    move: (bit_blast_umulo_rec_zip_correct2 Hblast Hzip1 Hzip2 Hcnf) => Henc_lr_and_or.
    rewrite /andb_orb_all Henc_lr_and_or andbT.
    rewrite (size_rev ls2) in Hs2.
    have H1: (size (rev bs2) <= size bs1) by rewrite -Hs1 -Hs2 (eqP Hsz).
      by rewrite (unzip1_extzip_ll b0 b0 H1) in Henc_lr_or.
  Qed.

  Fixpoint mk_env_umulo_rec_zip E g lsp: env * generator * cnf * literal * literal:=
    match lsp with
    | [::] => (E, g, [::], lit_ff, lit_ff)
    | (ls1_low, ls2_high)::tl =>
      let '(E_rec, g1, cs_tl, r_or_tl, r_and_or_tl) := mk_env_umulo_rec_zip E g tl in
      let (g2, r_or) := gen g1 in
      let (g3, r_and_or) := gen g2 in
      let E' := env_upd E_rec (var_of_lit r_or) (
                          interp_lit E_rec r_or_tl ||
                          interp_lit E_rec ls1_low
                        ) in
      let E'' := env_upd E' (var_of_lit r_and_or) (
                           interp_lit E' r_and_or_tl ||
                           (interp_lit E' r_or && interp_lit E' ls2_high)
                         ) in
      (* or sum  r_or <-> r_or_tl || ls1_low *)
      let cs_prefix_or := [::
                             [:: neg_lit r_or_tl; r_or];
                             [:: r_or_tl; ls1_low; neg_lit r_or];
                             [:: neg_lit ls1_low; r_or]
                          ] in
      (* and r_and_or <-> r_and_or_tl || (r_or && ls2_high) *)
      let cs_and_or := [::
                          [:: neg_lit r_or; neg_lit ls2_high; r_and_or];
                          [:: r_or; r_and_or_tl; neg_lit r_and_or];
                          [:: ls2_high; r_and_or_tl; neg_lit r_and_or];
                          [:: neg_lit r_and_or_tl; r_and_or]
                       ] in
      (E'', g3, cs_tl ++r cs_prefix_or ++r cs_and_or, r_or, r_and_or)
    end.

  Definition mk_env_umulo_rec E g ls1 ls2 :=
    mk_env_umulo_rec_zip E g (extzip_ff ls1 (rev ls2)).

  Lemma mk_env_umulo_rec_zip_is_bit_blast_umulo_rec_zip E g lsp E' g' cs lr_or lr_and_or:
    mk_env_umulo_rec_zip E g lsp = (E', g', cs, lr_or, lr_and_or) ->
    bit_blast_umulo_rec_zip g lsp = (g', cs, lr_or, lr_and_or).
  Proof.
    elim: lsp E g E' g' cs lr_or lr_and_or => [| [ls1_hd ls2_hd] lsp_tl IH ]E g E' g' cs lr_or lr_and_or //=.
    - intros; dcase_hyps; subst; reflexivity.
    -
      dcase (mk_env_umulo_rec_zip E g lsp_tl) => [[[[[E_rec g1] cs_tl] r_or_tl] r_and_or_tl] Henv].
      rewrite (IH _ _ _ _ _ _ _ Henv).
        by case=> _ <- <- <- <-.
  Qed.

  Lemma mk_env_umulo_rec_is_bit_blast_umulo_rec E g ls1 ls2 E' g' cs lr_or lr_and_or:
    mk_env_umulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    bit_blast_umulo_rec g ls1 ls2 = (g', cs, lr_or, lr_and_or).
  Proof.
    exact: mk_env_umulo_rec_zip_is_bit_blast_umulo_rec_zip.
  Qed.

  Lemma mk_env_umulo_rec_zip_newer_gen E g lsp E' g' cs lr_or lr_and_or:
    mk_env_umulo_rec_zip E g lsp = (E', g', cs, lr_or, lr_and_or) ->
    (g <=? g')%positive.
  Proof.
    elim: lsp E g E' g' cs lr_or lr_and_or => [| [ls1_hd ls2_hd] lsp_tl IH ]E g E' g' cs lr_or lr_and_or //=.
    - case=> _ <- _ _ _; t_auto_newer.
    -
      dcase (mk_env_umulo_rec_zip E g lsp_tl) => [[[[[E_rec g1] cs_tl] r_or_tl] r_and_or_tl] Henv].
      case=> _ <- _ _ _ .
      move: (IH _ _ _ _ _ _ _ Henv) => Hgg1.
      apply pos_leb_trans with g1. exact: Hgg1.
      eapply pos_leb_trans.
      exact: (pos_leb_add_diag_r _ 1).
      exact: (pos_leb_add_diag_r _ 1).
  Qed.

  Lemma mk_env_umulo_rec_newer_gen E g ls1 ls2 E' g' cs lr_or lr_and_or:
    mk_env_umulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    (g <=? g')%positive.
  Proof.
    exact: mk_env_umulo_rec_zip_newer_gen.
  Qed.

  Lemma mk_env_umulo_rec_zip_newer_res E g lsp E' g' cs lr_or lr_and_or:
    mk_env_umulo_rec_zip E g lsp = (E', g', cs, lr_or, lr_and_or) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g' lr_or && newer_than_lit g' lr_and_or.
  Proof.
    elim: lsp E g E' g' cs lr_or lr_and_or => [| [ls1_hd ls2_hd] lsp_tl IH ]E g E' g' cs lr_or lr_and_or //=.
    - case=> _ <- _ <- <- Htt.
      rewrite -[lit_ff]/(neg_lit lit_tt).
        by rewrite newer_than_lit_neg Htt.
    -
      dcase (mk_env_umulo_rec_zip E g lsp_tl) => [[[[[E_rec g1] cs_tl] r_or_tl] r_and_or_tl] Henv].
      case=> _ <- _ <- <- => Hgtt.
      rewrite /newer_than_lit /newer_than_var /=.
      move: (mk_env_umulo_rec_zip_newer_gen Henv) => Hg2g3.
      have Hgtg2 : (g1 <? (g1+1+1))%positive.
      apply pos_ltb_trans with (g1+1)%positive.
      exact: (pos_ltb_add_diag_r _ 1).
      exact: (pos_ltb_add_diag_r _ 1).
      rewrite (Hgtg2).
      rewrite (pos_ltb_add_diag_r _ 1).
      done.
  Qed.

  Lemma mk_env_umulo_rec_newer_res E g ls1 ls2 E' g' cs lr_or lr_and_or:
    mk_env_umulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g' lr_or && newer_than_lit g' lr_and_or.
  Proof.
    exact: mk_env_umulo_rec_zip_newer_res.
  Qed.

  Lemma mk_env_umulo_rec_zip_newer_cnf E g lsp E' g' cs lr_or lr_and_or:
    mk_env_umulo_rec_zip E g lsp = (E', g', cs, lr_or, lr_and_or) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g (unzip1 lsp) ->
    newer_than_lits g (unzip2 lsp) ->
    newer_than_cnf g' cs.
  Proof.
    elim: lsp E g E' g' cs lr_or lr_and_or => [| [ls1_hd ls2_hd] lsp_tl IH ]E g E' g' cs lr_or lr_and_or //=.
    - by case=> _ <- <- _ _.
    -
      dcase (mk_env_umulo_rec_zip E g lsp_tl) => [[[[[E_rec g1] cs_tl] r_or_tl] r_and_or_tl] Henv].
      case=> _ <- <- _ _ => Hgtt.
      move=> /andP [Hnew_gls1hd Hnew_gls1tl] /andP [Hnew_gls2hd Hnew_gls2tl].
      have Hgtg2 : (g1 <=? (g1+1+1))%positive.
      apply pos_leb_trans with (g1+1)%positive.
      exact: (pos_leb_add_diag_r _ 1).
      exact: (pos_leb_add_diag_r _ 1).
      rewrite !newer_than_cnf_catrev.
      move: (IH _ _ _ _ _ _ _ Henv Hgtt Hnew_gls1tl Hnew_gls2tl) => tmp.
      rewrite (newer_than_cnf_le_newer tmp Hgtg2).
      rewrite !newer_than_cnf_cons /=.
      move: (mk_env_umulo_rec_zip_newer_res Henv Hgtt) => /andP [Hnew1 Hnew2].
      move: (newer_than_lit_le_newer Hnew1 Hgtg2) => {Hnew1} Hnew1.
      move: (newer_than_lit_le_newer Hnew2 Hgtg2) => {Hnew2} Hnew2.
      rewrite !newer_than_lit_neg !Hnew1 !Hnew2.
      move: (mk_env_umulo_rec_zip_newer_gen Henv) => Hgg3.
      move: (pos_leb_trans Hgg3 Hgtg2) => Hgg32.
      rewrite !(newer_than_lit_le_newer Hnew_gls1hd Hgg32).
      rewrite !(newer_than_lit_le_newer Hnew_gls2hd Hgg32).
      rewrite /newer_than_lit /newer_than_var /=.
      have Hgttg2 : (g1 <? (g1+1+1))%positive.
      apply pos_ltb_trans with (g1+1)%positive.
      exact: (pos_ltb_add_diag_r _ 1).
      exact: (pos_ltb_add_diag_r _ 1).
      rewrite !Hgttg2 /var_of_lit /=.
        by rewrite (pos_ltb_add_diag_r _ 1).
  Qed.

  Lemma mk_env_umulo_rec_newer_cnf E g ls1 ls2 E' g' cs lr_or lr_and_or:
    mk_env_umulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    size ls1 == size ls2 ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
  Proof.
    move=> Hzip Hsz.
    move: (mk_env_umulo_rec_zip_newer_cnf Hzip) => Hncnf_zip.
    move=> Hgtt Hgls1 Hgls2.
    apply: Hncnf_zip.
    - done.
    - rewrite (unzip1_extzip_ll). done.
        by rewrite (size_rev ls2) (eqP Hsz).
    - rewrite (unzip2_extzip_rl).
      exact: (newer_than_lits_rev Hgls2).
        by rewrite (size_rev ls2) (eqP Hsz).
  Qed.

  Lemma mk_env_umulo_rec_zip_preserve E g lsp E' g' cs lr_or lr_and_or:
    mk_env_umulo_rec_zip E g lsp = (E', g', cs, lr_or, lr_and_or) ->
    env_preserve E E' g.
  Proof.
    elim: lsp E g E' g' cs lr_or lr_and_or => [| [ls1_hd ls2_hd] lsp_tl IH ]E g E' g' cs lr_or lr_and_or //=.
    - by case=> <- _ _ _ _.
    -
      dcase (mk_env_umulo_rec_zip E g lsp_tl) => [[[[[E_rec g1] cs_tl] r_or_tl] r_and_or_tl] Henv].
      case => <- _ _ _ _.
      specialize (IH _ _ _ _ _ _ _ Henv).
      move: (mk_env_umulo_rec_zip_newer_gen Henv) => Hgg3.
      remember (interp_lit E_rec r_or_tl || interp_lit E_rec ls1_hd) as val.
      remember (interp_lit (env_upd E_rec g1 val) r_and_or_tl
                || env_upd E_rec g1 val g1 && interp_lit (env_upd E_rec g1 val) ls2_hd) as val2.
      eapply env_preserve_trans. exact: IH.
      have Hpre2 : (env_preserve E_rec (env_upd E_rec g1 val) g).
      {
        apply: env_preserve_le.
        exact: env_upd_eq_preserve.
        exact Hgg3.
      }
      eapply env_preserve_trans. exact: Hpre2.
      apply: env_upd_newer_preserve.
      rewrite /newer_than_var /=.
      eapply pos_leb_ltb_trans. exact: Hgg3.
      exact: (pos_ltb_add_diag_r g1 1).
  Qed.

  Lemma mk_env_umulo_rec_preserve E g ls1 ls2 E' g' cs lr_or lr_and_or:
    mk_env_umulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    env_preserve E E' g.
  Proof.
    exact: mk_env_umulo_rec_zip_preserve.
  Qed.

  Lemma mk_env_umulo_rec_zip_sat E g lsp E' g' cs lr_or lr_and_or:
    mk_env_umulo_rec_zip E g lsp = (E', g', cs, lr_or, lr_and_or) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g (unzip1 lsp) ->
    newer_than_lits g (unzip2 lsp) ->
    interp_cnf E' cs.
  Proof.
    elim: lsp E g E' g' cs lr_or lr_and_or => [| [ls1_hd ls2_hd] lsp_tl IH ]E g E' g' cs lr_or lr_and_or //=.
    - by case=> <- _ <- _ _.
    -
      dcase (mk_env_umulo_rec_zip E g lsp_tl) => [[[[[E_rec g1] cs_tl] r_or_tl] r_and_or_tl] Henv].
      remember (interp_lit E_rec r_or_tl || interp_lit E_rec ls1_hd) as val.
      remember (interp_lit (env_upd E_rec g1 val) r_and_or_tl
                || env_upd E_rec g1 val g1 && interp_lit (env_upd E_rec g1 val) ls2_hd) as val2.
      case => Hoe _ <- _ _ => Hgtt.
      move=> /andP [Hnew_gls1hd Hnew_gls1tl] /andP [Hnew_gls2hd Hnew_gls2tl].
      move: (IH _ _ _ _ _ _ _ Henv Hgtt Hnew_gls1tl Hnew_gls2tl) => tmp.
      move: (mk_env_umulo_rec_zip_newer_cnf Henv Hgtt Hnew_gls1tl Hnew_gls2tl) => tmp2.
      move: (mk_env_umulo_rec_zip_preserve Henv) => Hpre_rec.
      have Hpre3: env_preserve E_rec (env_upd E_rec g1 val) g1.
      exact: env_upd_eq_preserve.
      have Hpre2: env_preserve E_rec E' g1.
      {
        rewrite -Hoe.
        eapply env_preserve_trans. exact: Hpre3.
        eapply env_upd_newer_preserve.
        exact: (pos_ltb_add_diag_r _ 1).
      }
      have Hpre4: env_preserve (env_upd E_rec g1 val) E' g1.
      {
        rewrite -Hoe.
        eapply env_preserve_le.
        exact: env_upd_eq_preserve.
        exact: (pos_leb_add_diag_r _ 1).
      }
      rewrite -(env_preserve_cnf Hpre2 tmp2) in tmp.
      rewrite !interp_cnf_catrev.
      rewrite tmp andTb => {tmp tmp2}.
      rewrite !Heqval !Heqval2 in Hoe.
      rewrite !interp_cnf_cons !interp_clause_cons !interp_lit_neg_lit /=.
      rewrite !env_upd_eq in Hoe.
      move: (mk_env_umulo_rec_zip_newer_res Henv Hgtt) => /andP[Hnew1 Hnew2].
      have He1: E' g1 = val.
      {
        rewrite -Hoe Heqval.
        rewrite env_upd_neq.  rewrite env_upd_eq. reflexivity.
        apply newer_than_var_neq.
        exact: (pos_ltb_add_diag_r _ 1).
      }
      have He2: E' (g1+1)%positive = val2.
      {
        rewrite -Hoe Heqval2.
        rewrite !env_upd_eq. reflexivity.
      }
      rewrite Heqval in He1.
      rewrite Heqval2 in He2.
      (* rewrite env_upd_eq in He2. *)
      move: (mk_env_umulo_rec_zip_newer_gen Henv) => Hgg3.
      move: (newer_than_lit_le_newer Hnew_gls2hd Hgg3) => Hg3_ls2last.
      move: (newer_than_lit_le_newer Hnew_gls1hd Hgg3) => Hg3_ls1low.
      rewrite (env_preserve_lit Hpre4 Hg3_ls2last).
      rewrite (env_preserve_lit Hpre4 Hg3_ls1low).
      rewrite (env_preserve_lit Hpre4 Hnew1).
      rewrite (env_preserve_lit Hpre4 Hnew2).
      rewrite -(env_preserve_lit Hpre3 Hnew1) in He1.
      rewrite -(env_preserve_lit Hpre3 Hg3_ls1low) in He1.
      rewrite !He1 !He2.
      rewrite !env_upd_eq.
      case H1 :(interp_lit (env_upd E_rec g1 val) ls2_hd);
        case H2 :(interp_lit (env_upd E_rec g1 val) ls1_hd);
        case H3 :(interp_lit (env_upd E_rec g1 val) r_and_or_tl);
        case H4 :(interp_lit (env_upd E_rec g1 val) r_or_tl).
      all:try done.
      all: rewrite !Heqval.
      all: rewrite -(env_preserve_lit Hpre3 Hnew1);
        rewrite -(env_preserve_lit Hpre3 Hg3_ls1low).
      all: rewrite H2 H4.
      all: done.
  Qed.

  Lemma mk_env_umulo_rec_sat E g ls1 ls2 E' g' cs lr_or lr_and_or:
    mk_env_umulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    size ls1 == size ls2 ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
  Proof.
    move=> Hzip Hsz.
    move: (mk_env_umulo_rec_zip_sat Hzip) => Hsat_zip.
    move=> Hgtt Hgls1 Hgls2.
    apply: Hsat_zip.
    - done.
    - rewrite (unzip1_extzip_ll). done.
        by rewrite (size_rev ls2) (eqP Hsz).
    - rewrite (unzip2_extzip_rl).
      exact: (newer_than_lits_rev Hgls2).
        by rewrite (size_rev ls2) (eqP Hsz).
  Qed.

  (* r <-> ls1 * ls2  >= 2^w *)
  (* TODO: check edge case right? *)
  Definition bit_blast_umulo (g: generator) ls1 ls2 : generator * cnf * literal:=
    let (ls1_low, ls1_hightl) := eta_expand (splitlsl ls1) in
    let (ls2_low, ls2_hightl) := eta_expand (splitlsl ls2) in
    let '(g_wls1, cs_wls1, lrs_wls1) := bit_blast_zeroextend 1 g ls1 in
    let '(g_wls2, cs_wls2, lrs_wls2) := bit_blast_zeroextend 1 g_wls1 ls2 in
    let '(g_rec1, cs_rec1, r_or_rec1, r_or_and_rec1) := bit_blast_umulo_rec g_wls2 ls1_hightl ls2_hightl in
    let '(g_mul, cs_mul, lrs_mul) := bit_blast_mul g_rec1 lrs_wls1 lrs_wls2 in
    let lrs_msb := msl lrs_mul in
    let (g_r, r) := gen g_mul in
    let cs := [::
                 [:: neg_lit r_or_and_rec1; r];
                 [:: r_or_and_rec1; lrs_msb; neg_lit r];
                 [:: neg_lit lrs_msb; r]
              ] in
    (g_r, cs_rec1 ++r cs_wls1 ++r cs_wls2 ++r cs_mul ++r cs, r).

  Definition mk_env_umulo E (g: generator) ls1 ls2 : env * generator * cnf * literal :=
    let (ls1_low, ls1_hightl) := eta_expand (splitlsl ls1) in
    let (ls2_low, ls2_hightl) := eta_expand (splitlsl ls2) in
    let '(E_wls1, g_wls1, cs_wls1, lrs_wls1) := mk_env_zeroextend 1 E g ls1 in
    let '(E_wls2, g_wls2, cs_wls2, lrs_wls2) := mk_env_zeroextend 1 E_wls1 g_wls1 ls2 in
    let '(E_rec, g_rec, cs_rec, r_or_rec, r_or_and_rec) := mk_env_umulo_rec E_wls2 g_wls2 ls1_hightl ls2_hightl in
    let '(E_mul, g_mul, cs_mul, lrs_mul) := mk_env_mul E_rec g_rec lrs_wls1 lrs_wls2 in
    let lrs_msb := msl lrs_mul in
    let (g_r, r) := gen g_mul in
    let E' := env_upd E_mul (var_of_lit r) (
                        (interp_lit E_mul r_or_and_rec) ||
                        (interp_lit E_mul lrs_msb)
                      ) in
    let cs := [::
                 [:: neg_lit r_or_and_rec; r];
                 [:: r_or_and_rec; lrs_msb; neg_lit r];
                 [:: neg_lit lrs_msb; r]
              ] in
    (E', g_r, cs_rec ++r cs_wls1 ++r cs_wls2 ++r cs_mul ++r cs, r).

  Lemma bit_blast_umulo_correct g bs1 bs2 E ls1 ls2 g' cs lr :
    bit_blast_umulo g ls1 ls2 = (g', cs, lr) ->
    size ls1 == size ls2 ->
    enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (Umulo bs1 bs2).
  Proof.
    rewrite /bit_blast_umulo /gen.
    dcase (bit_blast_zeroextend 1 g ls1) => [[[g_wls1 cs_wls1] lrs_wls1] Hblast_wls1].
    dcase (bit_blast_zeroextend 1 g_wls1 ls2) => [[[g_wls2 cs_wls2] lrs_wls2] Hblast_wls2].
    rewrite /Umulo /=.
    dcase (bit_blast_umulo_rec g_wls2 (behead ls1) (behead ls2))=> [[[[g_rec cs_rec] r_or_rec] r_or_and_rec] Hblast_rec].
    dcase (bit_blast_mul g_rec lrs_wls1 lrs_wls2) => [[[g_mul cs_mul] lrs_mul] Hblast_mul].
    case=> _ <- <- Hsz Henc1 Henc2.
    repeat rewrite add_prelude_catrev.
    move/andP => [Hcnf_rec /andP [Hcnf_wls1 /andP [Hcnf_wls2 /andP [Hcnf_mul Hcnf]]]].
    move: (add_prelude_enc_bit_tt Hcnf) => Htt.
    rewrite /enc_bit in Htt.
    move/eqP in Htt.
    move: (enc_bits_splitlsb Htt Henc1) => /= /andP [_ Henc_ls1tl].
    move: (enc_bits_splitlsb Htt Henc2) => /= /andP [_ Henc_ls2tl].
    have Hsz_tl: (size (behead ls1) == size (behead ls2)) by rewrite !size_behead (eqP Hsz).
    move: (bit_blast_umulo_rec_correct Hblast_rec Hsz_tl Henc_ls1tl Henc_ls2tl Hcnf_rec)
    => /andP [_ Henc_andb].
    move: (bit_blast_zeroextend_correct Hblast_wls1 Henc1 Hcnf_wls1) => Henc_wls1.
    move: (bit_blast_zeroextend_correct Hblast_wls2 Henc2 Hcnf_wls2) => Henc_wls2.
    have Hsz_wls12 : size lrs_wls1 == size lrs_wls2.
    {
      case: Hblast_wls1 => _ _ <-.
      case: Hblast_wls2 => _ _ <-.
      rewrite !seq.size_cat /=.
        by rewrite (eqP Hsz).
    }
    move: (bit_blast_mul_correct Hblast_mul Henc_wls1 Henc_wls2 Hcnf_mul (eqP Hsz_wls12)) => Henc_mul.
    move: (add_prelude_enc_bit_ff Hcnf) => Hff.
    move: (enc_bit_lastd Hff Henc_mul) => Hlastd.
    rewrite /msb /=.
    repeat rewrite add_prelude_cons add_prelude_singleton in Hcnf.
    rewrite /msl /= !interp_lit_neg_lit in Hcnf.
    split_andb_hyps.
    repeat match goal with H: is_true (E var_tt) |- _ => clear H end.
    move: H3 H4 H5.
    move: Henc_andb Hlastd.
    rewrite /enc_bit.
    move=> /eqP <- /eqP <- /=.
      by case: (interp_lit E (lastd lit_ff lrs_mul));
        case: (E g_mul);
        case: (interp_lit E r_or_and_rec).
  Qed.

  Lemma mk_env_umulo_is_bit_blast_umulo E g ls1 ls2 E' g' cs lr:
    mk_env_umulo E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_umulo g ls1 ls2 = (g', cs, lr).
  Proof.
    rewrite /bit_blast_umulo /mk_env_umulo /gen.
    dcase (mk_env_zeroextend 1 E g ls1) => [[[[E_wls1 g_wls1] cs_wls1] lrs_wls1] Henv_wls1].
    dcase (mk_env_zeroextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] lrs_wls2] Henv_wls2].
    simpl snd.
    dcase (mk_env_umulo_rec E_wls2 g_wls2 (behead ls1) (behead ls2))=> [[[[[E_rec g_rec] cs_rec] r_or_rec] r_or_and_rec] Henv_rec].
    dcase (mk_env_mul E_rec g_rec lrs_wls1 lrs_wls2) => [[[[E_mul g_mul] cs_mul] lrs_mul] Henv_mul].
    rewrite (mk_env_zeroextend_is_bit_blast_zeroextend Henv_wls1).
    rewrite (mk_env_zeroextend_is_bit_blast_zeroextend Henv_wls2).
    rewrite (mk_env_umulo_rec_is_bit_blast_umulo_rec Henv_rec).
    rewrite (mk_env_mul_is_bit_blast_mul Henv_mul).
      by case=> _ <- <- <-.
  Qed.

  Lemma mk_env_umulo_newer_gen E g ls1 ls2 E' g' cs lr:
    mk_env_umulo E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
  Proof.
    rewrite /bit_blast_umulo /mk_env_umulo /gen.
    dcase (mk_env_zeroextend 1 E g ls1) => [[[[E_wls1 g_wls1] cs_wls1] lrs_wls1] Henv_wls1].
    dcase (mk_env_zeroextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] lrs_wls2] Henv_wls2].
    simpl snd.
    dcase (mk_env_umulo_rec E_wls2 g_wls2 (behead ls1) (behead ls2))=> [[[[[E_rec g_rec] cs_rec] r_or_rec] r_or_and_rec] Henv_rec].
    dcase (mk_env_mul E_rec g_rec lrs_wls1 lrs_wls2) => [[[[E_mul g_mul] cs_mul] lrs_mul] Henv_mul].
    case=> _ <- _ _.
    move: (mk_env_zeroextend_newer_gen Henv_wls1) => tmp.
    apply (pos_leb_trans (mk_env_zeroextend_newer_gen Henv_wls1)).
    apply (pos_leb_trans (mk_env_zeroextend_newer_gen Henv_wls2)).
    apply (pos_leb_trans (mk_env_umulo_rec_newer_gen Henv_rec)).
    apply (pos_leb_trans (mk_env_mul_newer_gen Henv_mul)).
    exact: (pos_leb_add_diag_r _ 1).
  Qed.

  Lemma mk_env_umulo_newer_res E g ls1 ls2 E' g' cs lr:
    mk_env_umulo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g' lr.
  Proof.
    rewrite /bit_blast_umulo /mk_env_umulo /gen.
    dcase (mk_env_zeroextend 1 E g ls1) => [[[[E_wls1 g_wls1] cs_wls1] lrs_wls1] Henv_wls1].
    dcase (mk_env_zeroextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] lrs_wls2] Henv_wls2].
    simpl snd.
    dcase (mk_env_umulo_rec E_wls2 g_wls2 (behead ls1) (behead ls2))=> [[[[[E_rec g_rec] cs_rec] r_or_rec] r_or_and_rec] Henv_rec].
    dcase (mk_env_mul E_rec g_rec lrs_wls1 lrs_wls2) => [[[[E_mul g_mul] cs_mul] lrs_mul] Henv_mul].
    case=> _ <- _ <- => Hgtt.
    exact: (pos_ltb_add_diag_r _ 1).
  Qed.

  Lemma mk_env_umulo_newer_cnf E g ls1 ls2 E' g' cs lr:
    mk_env_umulo E g ls1 ls2 = (E', g', cs, lr) ->
    size ls1 == size ls2 ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
  Proof.
    rewrite /bit_blast_umulo /mk_env_umulo /gen.
    dcase (mk_env_zeroextend 1 E g ls1) => [[[[E_wls1 g_wls1] cs_wls1] lrs_wls1] Henv_wls1].
    dcase (mk_env_zeroextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] lrs_wls2] Henv_wls2].
    simpl snd.
    dcase (mk_env_umulo_rec E_wls2 g_wls2 (behead ls1) (behead ls2))=> [[[[[E_rec g_rec] cs_rec] r_or_rec] r_or_and_rec] Henv_rec].
    dcase (mk_env_mul E_rec g_rec lrs_wls1 lrs_wls2) => [[[[E_mul g_mul] cs_mul] lrs_mul] Henv_mul].
    case=> _ <- <- _ => Hsz Hnew_gtt Hnew_gls1 Hnew_gls2.
    rewrite !newer_than_cnf_catrev.
    move: (mk_env_zeroextend_newer_gen Henv_wls1) => H_gls1.
    move: (mk_env_zeroextend_newer_gen Henv_wls2) => H_gls12.
    move: (mk_env_umulo_rec_newer_gen Henv_rec) => H_gls2rec.
    move: (mk_env_mul_newer_gen Henv_mul) => H_grecmul.
    move: (pos_leb_add_diag_r g_mul 1) => H_gmul1.
    move: (pos_leb_trans H_grecmul H_gmul1) => H_grecgmul1.
    move: (pos_leb_trans H_gls2rec H_grecgmul1) => H_gls2mul1.
    move: (pos_leb_trans H_gls12 H_gls2mul1) => H_gls1mul1.
    move: (mk_env_zeroextend_newer_cnf Henv_wls1 Hnew_gtt Hnew_gls1) => Hnew_gwls1_wls1.
    rewrite (newer_than_cnf_le_newer Hnew_gwls1_wls1 H_gls1mul1).
    move: (newer_than_lit_le_newer Hnew_gtt H_gls1) => Hnew_ggls1_gtt.
    move: (newer_than_lits_le_newer Hnew_gls1 H_gls1) => Hnew_ggls1_gls1.
    move: (newer_than_lits_le_newer Hnew_gls2 H_gls1) => Hnew_ggls1_gls2.
    move: (mk_env_zeroextend_newer_cnf Henv_wls2 Hnew_ggls1_gtt Hnew_ggls1_gls2) => Hnew_gwls2_wls2.
    rewrite (newer_than_cnf_le_newer Hnew_gwls2_wls2 H_gls2mul1).
    move: (newer_than_lit_le_newer Hnew_ggls1_gtt H_gls12) => Hnew_ggls2_gtt.
    move: (newer_than_lits_le_newer Hnew_ggls1_gls1 H_gls12) => Hnew_ggls2_gls1.
    move: (newer_than_lits_le_newer Hnew_ggls1_gls2 H_gls12) => Hnew_ggls2_gls2.
    move: (mk_env_zeroextend_newer_res Henv_wls1 Hnew_gtt Hnew_gls1) => H_gls1_lrs1.
    move: (newer_than_lits_le_newer H_gls1_lrs1 H_gls12) => H_gls2_lrs1.
    move: (mk_env_zeroextend_newer_res Henv_wls2 Hnew_ggls1_gtt Hnew_ggls1_gls2) => H_gls2_lrs2.
    move: (newer_than_lits_splitlsl Hnew_ggls2_gtt Hnew_ggls2_gls1) => /= /andP [Hnew_ggls2_ls1low Hnew_ggls2_ls1high].
    move: (newer_than_lits_splitlsl Hnew_ggls2_gtt Hnew_ggls2_gls2) => /= /andP [Hnew_ggls2_ls12ow Hnew_ggls2_ls2high].
    have Hsz_tl: (size (behead ls1) == size (behead ls2)) by rewrite !size_behead (eqP Hsz).
    move: (mk_env_umulo_rec_newer_cnf Henv_rec Hsz_tl Hnew_ggls2_gtt Hnew_ggls2_ls1high Hnew_ggls2_ls2high) => Hnew_rec.
    rewrite (newer_than_cnf_le_newer Hnew_rec H_grecgmul1).
    move: (newer_than_lits_le_newer H_gls2_lrs1 H_gls2rec) => tmp.
    move: (newer_than_lits_le_newer H_gls2_lrs2 H_gls2rec) => tmp2.
    move: (newer_than_lit_le_newer Hnew_ggls2_gtt H_gls2rec) => tmp3.
    move: (mk_env_mul_newer_cnf Henv_mul tmp3 tmp tmp2) => Hnew_mul.
    rewrite (newer_than_cnf_le_newer Hnew_mul H_gmul1).
    rewrite /=.
    rewrite !newer_than_lit_neg.
    move: (mk_env_umulo_rec_newer_res Henv_rec Hnew_ggls2_gtt) => /andP [_ Hand].
    rewrite (newer_than_lit_le_newer Hand H_grecgmul1).
    move: (mk_env_mul_newer_res Henv_mul tmp3) => tmp4.
    have tmptt: (newer_than_lit g_mul lit_tt) by t_newer_hook.
    move: (newer_than_lits_msl tmptt tmp4) => tmp5.
    rewrite (newer_than_lit_le_newer tmp5 H_gmul1).
    rewrite /newer_than_lit /newer_than_var /=.
    rewrite (pos_ltb_add_diag_r g_mul 1).
    done.
  Qed.

  Lemma mk_env_umulo_preserve E g ls1 ls2 E' g' cs lr:
    mk_env_umulo E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
  Proof.
    rewrite /bit_blast_umulo /mk_env_umulo /gen.
    dcase (mk_env_zeroextend 1 E g ls1) => [[[[E_wls1 g_wls1] cs_wls1] lrs_wls1] Henv_wls1].
    dcase (mk_env_zeroextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] lrs_wls2] Henv_wls2].
    simpl snd.
    dcase (mk_env_umulo_rec E_wls2 g_wls2 (behead ls1) (behead ls2))=> [[[[[E_rec g_rec] cs_rec] r_or_rec] r_or_and_rec] Henv_rec].
    dcase (mk_env_mul E_rec g_rec lrs_wls1 lrs_wls2) => [[[[E_mul g_mul] cs_mul] lrs_mul] Henv_mul].
    case=> <- _ _ _.
    move: (mk_env_zeroextend_newer_gen Henv_wls1) => H_ggls1.
    move: (mk_env_zeroextend_newer_gen Henv_wls2) => H_ggls12.
    move: (mk_env_umulo_rec_newer_gen Henv_rec) => H_ggls2rec.
    move: (mk_env_mul_newer_gen Henv_mul) => H_ggrecmul.
    move: (pos_leb_trans H_ggls1 H_ggls12) => H_gls2.
    move: (pos_leb_trans H_gls2 H_ggls2rec) => H_grec.
    move: (pos_leb_trans H_grec H_ggrecmul) => H_gmul.
    move: (mk_env_zeroextend_preserve Henv_wls1) => Hpre1.
    move: (mk_env_zeroextend_preserve Henv_wls2) => Hpre2.
    move: (mk_env_umulo_rec_preserve Henv_rec) => Hpre3.
    move: (mk_env_mul_preserve Henv_mul) => Hpre4.
    move: (env_preserve_le Hpre2 H_ggls1) => {Hpre2} Hpre2.
    move: (env_preserve_le Hpre3 H_gls2) => {Hpre3} Hpre3.
    move: (env_preserve_le Hpre4 H_grec) => {Hpre4} Hpre4.
    apply env_preserve_trans with E_mul.
    apply env_preserve_trans with E_rec.
    apply env_preserve_trans with E_wls2.
    apply env_preserve_trans with E_wls1.
    all: try done.
    eapply env_preserve_le.
    exact: env_upd_eq_preserve.
    exact: H_gmul.
  Qed.

  Lemma mk_env_umulo_sat E g ls1 ls2 E' g' cs lr:
    mk_env_umulo E g ls1 ls2 = (E', g', cs, lr) ->
    size ls1 == size ls2 ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->  newer_than_lits g ls2 ->
    interp_cnf E' cs.
  Proof.
    rewrite /bit_blast_umulo /mk_env_umulo /gen.
    dcase (mk_env_zeroextend 1 E g ls1) => [[[[E_wls1 g_wls1] cs_wls1] lrs_wls1] Henv_wls1].
    dcase (mk_env_zeroextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] lrs_wls2] Henv_wls2].
    simpl snd.
    dcase (mk_env_umulo_rec E_wls2 g_wls2 (behead ls1) (behead ls2))=> [[[[[E_rec g_rec] cs_rec] r_or_rec] r_or_and_rec] Henv_rec].
    dcase (mk_env_mul E_rec g_rec lrs_wls1 lrs_wls2) => [[[[E_mul g_mul] cs_mul] lrs_mul] Henv_mul].
    case=> <- _ <- _ => Hsz Hnew_gtt Hnew_gls1 Hnew_gls2.
    rewrite !interp_cnf_catrev.
    move: (mk_env_zeroextend_newer_gen Henv_wls1) => H_ggls1.
    move: (mk_env_zeroextend_newer_gen Henv_wls2) => H_ggls12.
    move: (mk_env_umulo_rec_newer_gen Henv_rec) => H_ggls2rec.
    move: (mk_env_mul_newer_gen Henv_mul) => H_grecmul.
    move: (pos_leb_add_diag_r g_mul 1) => H_gmul1.
    move: (mk_env_zeroextend_preserve Henv_wls1) => Hpre_wls1.
    move: (mk_env_zeroextend_preserve Henv_wls2) => Hpre_wls2.
    move: (mk_env_umulo_rec_preserve Henv_rec) => Hpre_rec.
    move: (mk_env_mul_preserve Henv_mul) => Hpre_mul.
    remember (env_upd E_mul g_mul
                      (interp_lit E_mul r_or_and_rec || interp_lit E_mul (msl lrs_mul))) as Ef.
    have Hpre_Ef : (env_preserve E_mul Ef g_mul).
    {
      rewrite HeqEf.
      exact: env_upd_eq_preserve.
    }
    (* wls1 *)
    move: (mk_env_zeroextend_sat Henv_wls1 Hnew_gtt Hnew_gls1) => Hicnf_ls1_ls1.
    move: (mk_env_zeroextend_newer_cnf Henv_wls1 Hnew_gtt Hnew_gls1) => Hncnf_ls1_ls1.
    move: (newer_than_cnf_le_newer Hncnf_ls1_ls1 H_ggls12) => Hncnf_ls2_ls1.
    move: (newer_than_cnf_le_newer Hncnf_ls2_ls1 H_ggls2rec) => Hncnf_rec_ls1.
    move: (newer_than_cnf_le_newer Hncnf_rec_ls1 H_grecmul) => Hncnf_mul_ls1.
    rewrite (env_preserve_cnf Hpre_Ef Hncnf_mul_ls1).
    rewrite (env_preserve_cnf Hpre_mul Hncnf_rec_ls1).
    rewrite (env_preserve_cnf Hpre_rec Hncnf_ls2_ls1).
    rewrite (env_preserve_cnf Hpre_wls2 Hncnf_ls1_ls1).
    rewrite Hicnf_ls1_ls1 andTb.
    move=> {Hncnf_ls2_ls1 Hncnf_mul_ls1 Hncnf_ls1_ls1}.
    (* wls2 *)
    move: (newer_than_lit_le_newer Hnew_gtt H_ggls1) => Hnew_gls1tt.
    move: (newer_than_lits_le_newer Hnew_gls1 H_ggls1) => Hnew_gls1ls1.
    move: (newer_than_lits_le_newer Hnew_gls2 H_ggls1) => Hnew_gls1ls2.
    move: (mk_env_zeroextend_sat Henv_wls2 Hnew_gls1tt Hnew_gls1ls2) => Hicnf_ls2_ls2.
    move: (mk_env_zeroextend_newer_cnf Henv_wls2 Hnew_gls1tt Hnew_gls1ls2) => Hncnf_ls2_ls2.
    move: (newer_than_cnf_le_newer Hncnf_ls2_ls2 H_ggls2rec) => Hncnf_rec_ls2.
    move: (newer_than_cnf_le_newer Hncnf_rec_ls2 H_grecmul) => Hncnf_mul_ls2.
    rewrite (env_preserve_cnf Hpre_Ef Hncnf_mul_ls2).
    rewrite (env_preserve_cnf Hpre_mul Hncnf_rec_ls2).
    rewrite (env_preserve_cnf Hpre_rec Hncnf_ls2_ls2).
    rewrite Hicnf_ls2_ls2 andTb.
    move=> {Hncnf_ls2_ls2 Hncnf_mul_ls2 Hicnf_ls1_ls1 Hicnf_ls2_ls2}.
    (* rec *)
    move: (newer_than_lit_le_newer Hnew_gls1tt H_ggls12) => Hnew_gls2tt.
    move: (newer_than_lits_le_newer Hnew_gls1ls1 H_ggls12) => Hnew_gls2ls1.
    move: (newer_than_lits_le_newer Hnew_gls1ls2 H_ggls12) => Hnew_gls2ls2.
    move: (mk_env_zeroextend_newer_res Henv_wls1 Hnew_gtt Hnew_gls1) => Hnew_gls1_lrs1.
    move: (newer_than_lits_le_newer Hnew_gls1_lrs1 H_ggls12) => Hnew_gls2_lrs1.
    move: (mk_env_zeroextend_newer_res Henv_wls2 Hnew_gls1tt Hnew_gls1ls2) => Hnew_gls2_lrs2.
    move: (newer_than_lits_splitlsl Hnew_gls2tt Hnew_gls2ls1) => /= /andP [Hnew_gls2ls1_low Hnew_gls2ls1_high].
    move: (newer_than_lits_splitlsl Hnew_gls2tt Hnew_gls2ls2) => /= /andP [Hnew_gls2ls2_low Hnew_gls2ls2_high].
    have Hsz_tl: (size (behead ls1) == size (behead ls2)) by rewrite !size_behead (eqP Hsz).
    move: (mk_env_umulo_rec_sat Henv_rec Hsz_tl Hnew_gls2tt Hnew_gls2ls1_high Hnew_gls2ls2_high) => Hicnf_rec_rec.
    move: (mk_env_umulo_rec_newer_cnf Henv_rec Hsz_tl Hnew_gls2tt Hnew_gls2ls1_high Hnew_gls2ls2_high) => Hncnf_rec_rec.
    move: (newer_than_cnf_le_newer Hncnf_rec_rec H_grecmul) => Hncnf_mul_rec.
    rewrite (env_preserve_cnf Hpre_Ef Hncnf_mul_rec).
    rewrite (env_preserve_cnf Hpre_mul Hncnf_rec_rec).
    rewrite Hicnf_rec_rec andTb.
    move=> {Hncnf_rec_rec Hncnf_mul_rec Hicnf_rec_rec}.
    (* mul *)
    move: (newer_than_lit_le_newer Hnew_gls2tt H_ggls2rec) => Hnew_grectt.
    move: (newer_than_lits_le_newer Hnew_gls2_lrs1 H_ggls2rec) => Hnew_grec_lrs1.
    move: (newer_than_lits_le_newer Hnew_gls2_lrs2 H_ggls2rec) => Hnew_grec_lrs2.
    move: (mk_env_mul_sat Henv_mul Hnew_grectt Hnew_grec_lrs1 Hnew_grec_lrs2) => Hicnf_mul_mul.
    move: (mk_env_mul_newer_cnf Henv_mul Hnew_grectt Hnew_grec_lrs1 Hnew_grec_lrs2) => Hncnf_mul_mul.
    rewrite (env_preserve_cnf Hpre_Ef Hncnf_mul_mul).
    rewrite Hicnf_mul_mul andTb.
    move => {Hicnf_mul_mul Hncnf_mul_mul}.
    rewrite !interp_lit_neg_lit /=.
    move: (mk_env_umulo_rec_newer_res Henv_rec Hnew_gls2tt) => /andP [_ Hand].
    move: (newer_than_lit_le_newer Hand H_grecmul) => {Hand} Hand.
    rewrite (env_preserve_lit Hpre_Ef Hand).
    move: (mk_env_mul_newer_res Henv_mul Hnew_grectt) => H.
    have tmptt: (newer_than_lit g_mul lit_tt) by t_newer_hook.
    move: (newer_than_lits_msl tmptt H) => H2.
    rewrite (env_preserve_lit Hpre_Ef H2).
    rewrite HeqEf. rewrite !env_upd_eq.
      by case :(interp_lit E_mul r_or_and_rec);
        case :(interp_lit E_mul (msl lrs_mul)).
  Qed.
End BBUmulo.
