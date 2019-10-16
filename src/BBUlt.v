From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From BitBlasting Require Import QFBV CNF BBCommon BBEq.
From ssrlib Require Import ZAriths Tactics Bools Seqs.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== bit_blast_ult ===== *)

Fixpoint bit_blast_ult_rev'_zip (g : generator) lsp : generator * cnf * literal :=
  match lsp with
  | [::] => (g, [::], lit_ff)
  | (ls1_hd, ls2_hd)::lsp_tl =>
    let '(gult_tl, csult_tl, lrult_tl) := bit_blast_ult_rev'_zip g lsp_tl in
    let (g_r, r) := gen gult_tl in
    let cs := [ ::
                  [:: neg_lit ls1_hd; ls2_hd; neg_lit r];
                  [:: neg_lit ls1_hd; lrult_tl; neg_lit r];
                  [:: ls1_hd; neg_lit ls2_hd; r];
                  [:: ls1_hd; neg_lit lrult_tl; r];
                  [:: neg_lit ls2_hd; neg_lit lrult_tl; r];
                  [:: ls2_hd; lrult_tl; neg_lit r]
              ] in
    (g_r, catrev csult_tl cs, r)
  end.

Fixpoint mk_env_ult_rev'_zip E (g : generator) lsp : env * generator * cnf * literal :=
  match lsp with
  | [::] => (E, g, [::], lit_ff)
  | (ls1_hd, ls2_hd)::lsp_tl =>
    let '(Eult_tl, gult_tl, csult_tl, lrult_tl) := mk_env_ult_rev'_zip E g lsp_tl in
    let (g_r, r) := gen gult_tl in
    let E' := env_upd Eult_tl (var_of_lit r) ((~~interp_lit Eult_tl ls1_hd && interp_lit Eult_tl ls2_hd) || ((interp_lit Eult_tl ls1_hd == interp_lit Eult_tl ls2_hd) && interp_lit Eult_tl lrult_tl)) in
    let cs := [ ::
                  [:: neg_lit ls1_hd; ls2_hd; neg_lit r];
                  [:: neg_lit ls1_hd; lrult_tl; neg_lit r];
                  [:: ls1_hd; neg_lit ls2_hd; r];
                  [:: ls1_hd; neg_lit lrult_tl; r];
                  [:: neg_lit ls2_hd; neg_lit lrult_tl; r];
                  [:: ls2_hd; lrult_tl; neg_lit r]
              ] in
     (E', g_r, catrev csult_tl cs, r)
  end.


Definition bit_blast_ult g ls1 ls2: generator * cnf * literal :=
  bit_blast_ult_rev'_zip g (extzip_ff (rev ls1) (rev ls2)).

Definition mk_env_ult E g ls1 ls2: env * generator * cnf * literal :=
  mk_env_ult_rev'_zip E g (extzip_ff (rev ls1) (rev ls2)).

Lemma bit_blast_ult_rev'_zip_correct E g bsp lsp g' cs lr:
  bit_blast_ult_rev'_zip g lsp = (g', cs, lr) ->
  enc_bits E (unzip1 lsp) (unzip1 bsp) ->
  enc_bits E (unzip2 lsp) (unzip2 bsp) ->
  interp_cnf E (add_prelude cs) ->
  enc_bit E lr (ltB_rev_zip bsp).
Proof.
  rewrite /bit_blast_ult_rev'_zip -/bit_blast_ult_rev'_zip.
  elim: lsp E g bsp g' cs lr => [| [ls1_hd ls2_hd] lsp_tl IH] E g bsp g' cs lr //=.
  - case=> _ _ <-.
    rewrite !enc_bits_nil_l unzip1_l_nil unzip2_l_nil.
    move/eqP => H _; rewrite H /=.
    exact: add_prelude_enc_bit_ff.
  - case: bsp => [| [bsp_hd1 bsp_hd2] bsp_tl] //=.
    dcase (bit_blast_ult_rev'_zip g lsp_tl) => [[[gult_tl csult_tl] lrsult_tl] Hblast_ult].
    case=> _ <- <-.
    rewrite !enc_bits_cons.
    move=> /andP [Henc1hd Henc1tl] /andP [Henc2hd Henc2tl].
    rewrite add_prelude_catrev.
    move/andP => [Hcnf_tl Hcnf].
    repeat rewrite add_prelude_cons add_prelude_singleton in Hcnf.
    rewrite /= !interp_lit_neg_lit /= in Hcnf.
    t_clear. split_andb_hyps.
    move: (IH _ _ _ _ _ _ Hblast_ult Henc1tl Henc2tl Hcnf_tl) => IHH.
    move: H6 H7 H8 H9 H10 H11.
    move: Henc1hd Henc2hd IHH.
    rewrite /enc_bit /=.
    move=> /eqP -> /eqP -> /eqP ->.
    by case: (E gult_tl); case (bsp_hd1); case (bsp_hd2); case (ltB_rev_zip bsp_tl).
Qed.

Lemma bit_blast_ult_correct g bs1 bs2 E ls1 ls2 g' cs lr :
  bit_blast_ult g ls1 ls2 = (g', cs, lr) ->
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bit E lr (ltB bs1 bs2).
Proof.
  rewrite -ltB_rev_ltB.
  rewrite /bit_blast_ult.
  move=> H Henc1 Henc2 Hcnf.
  move: (add_prelude_enc_bit_tt Hcnf) => Henctt.
  apply enc_bits_rev in Henc1.
  apply enc_bits_rev in Henc2.
  move: (enc_bits_unzip1_extzip Henctt Henc1 Henc2) => Hzip1.
  move: (enc_bits_unzip2_extzip Henctt Henc1 Henc2) => Hzip2.
  exact: (bit_blast_ult_rev'_zip_correct H).
Qed.


Lemma mk_env_ult_rev'_zip_is_bit_blast_ult_rev'_zip E g lsp E' g' cs lr:
    mk_env_ult_rev'_zip E g lsp = (E', g', cs, lr) ->
    bit_blast_ult_rev'_zip g lsp = (g', cs, lr).
Proof.
  rewrite /bit_blast_ult_rev'_zip -/bit_blast_ult_rev'_zip.
  rewrite /mk_env_ult_rev'_zip -/mk_env_ult_rev'_zip.
  elim: lsp E g E' g' cs lr => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lr //=.
  - rewrite /=; intros; dcase_hyps; subst; reflexivity.
  -
    dcase (mk_env_ult_rev'_zip E g lsp_tl) => [[[[Eult_tl gult_tl] csult_tl] lrult_tl] H].
    rewrite (IH _ _ _ _ _ _ H).
    by case=> _ <- <- <-.
Qed.

Lemma mk_env_ult_is_bit_blast_ult E g ls1 ls2 E' g' cs lr:
    mk_env_ult E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_ult g ls1 ls2 = (g', cs, lr).
Proof.
  exact: mk_env_ult_rev'_zip_is_bit_blast_ult_rev'_zip.
Qed.

Lemma mk_env_ult_rev'_zip_newer_gen E g lsp E' g' cs lr:
  mk_env_ult_rev'_zip E g lsp = (E', g', cs, lr) ->
  (g <=? g')%positive.
Proof.
  elim: lsp E g E' g' cs lr => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lr //=.
  - by case=> _ <- _ _; t_auto_newer.
  - dcase (mk_env_ult_rev'_zip E g lsp_tl) => [[[[Eult_tl gult_tl] csult_tl] lrult_tl] Henv_tl].
    move: (IH _ _ _ _ _ _ Henv_tl) => IHH.
      by case=> _ <- _ _; t_auto_newer.
Qed.

Lemma mk_env_ult_rev'_zip_newer_res E g lsp E' g' cs lr:
  mk_env_ult_rev'_zip E g lsp = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lit g' lr.
Proof.
  elim: lsp E g E' g' cs lr => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lr //=.
  - by case=> _ <- _ <-; t_auto_newer.
  - dcase (mk_env_ult_rev'_zip E g lsp_tl) => [[[[Eult_tl gult_tl] csult_tl] lrult_tl] Henv_tl].
    move: (IH _ _ _ _ _ _ Henv_tl) => IHH.
      by case=> _ <- _ <-; t_auto_newer.
Qed.

Lemma mk_env_ult_rev'_zip_newer_cnf E g lsp E' g' cs lr:
  mk_env_ult_rev'_zip E g lsp = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g (unzip1 lsp) -> newer_than_lits g (unzip2 lsp) ->
  newer_than_cnf g' cs.
Proof.
  elim: lsp E g E' g' cs lr => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lr //=.
  - by case=> _ <- <- _; t_auto_newer.
  - dcase (mk_env_ult_rev'_zip E g lsp_tl) => [[[[Eult_tl gult_tl] csult_tl] lrult_tl] Henv_tl].
    case=> _ <- <- _.
    move=> Hgtt /andP [Hnew_gls1hd Hnew_gls1tl] /andP [Hnew_gls2hd Hnew_gls2tl].
    move: (IH _ _ _ _ _ _ Henv_tl Hgtt Hnew_gls1tl Hnew_gls2tl) => IHH.
    move: (mk_env_ult_rev'_zip_newer_res Henv_tl Hgtt) => Hres.
    move: (mk_env_ult_rev'_zip_newer_gen Henv_tl) => Hg.
    rewrite newer_than_cnf_catrev.
    rewrite /= !newer_than_lit_neg.
    split_andb_goal; t_auto_newer.
Qed.

Lemma mk_env_ult_rev'_zip_preserve E g lsp E' g' cs lr:
  mk_env_ult_rev'_zip E g lsp = (E', g', cs, lr) ->
  env_preserve E E' g.
Proof.
  elim: lsp E g E' g' cs lr => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lr //=.
  - by case=> <- _ _ _; t_auto_preserve.
  - dcase (mk_env_ult_rev'_zip E g lsp_tl) => [[[[Eult_tl gult_tl] csult_tl] lrult_tl] Henv_tl].
    case=> <- _ _ _.
    move: (IH _ _ _ _ _ _ Henv_tl) => IHH.
    move: (mk_env_ult_rev'_zip_newer_gen Henv_tl) => Hg.
    t_auto_preserve.
    apply env_preserve_le with gult_tl; t_auto_preserve.
Qed.

Lemma mk_env_ult_rev'_zip_sat E g lsp E' g' cs lr:
  mk_env_ult_rev'_zip E g lsp = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g (unzip1 lsp) -> newer_than_lits g (unzip2 lsp) ->
  interp_cnf E' cs.
Proof.
  elim: lsp E g E' g' cs lr => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lr //=.
  - by case=> <- _ <- _.
  - dcase (mk_env_ult_rev'_zip E g lsp_tl) => [[[[Eult_tl gult_tl] csult_tl] lrult_tl] Henv_tl].
    case=> <- _ <- _.
    move=> Hgtt /andP [Hnew_gls1hd Hnew_gls1tl] /andP [Hnew_gls2hd Hnew_gls2tl].
    move: (IH _ _ _ _ _ _ Henv_tl Hgtt Hnew_gls1tl Hnew_gls2tl) => IHH.
    move: (mk_env_ult_rev'_zip_newer_res Henv_tl Hgtt) => Hres.
    move: (mk_env_ult_rev'_zip_newer_gen Henv_tl) => Hg.
    move: (mk_env_ult_rev'_zip_preserve Henv_tl) => Hpre.
    move: (mk_env_ult_rev'_zip_newer_cnf Henv_tl Hgtt Hnew_gls1tl Hnew_gls2tl) => Hcnf.
    rewrite interp_cnf_catrev.
    remember (env_upd Eult_tl gult_tl
       (~~ interp_lit Eult_tl ls1_hd && interp_lit Eult_tl ls2_hd
        || (interp_lit Eult_tl ls1_hd == interp_lit Eult_tl ls2_hd) &&
           interp_lit Eult_tl lrult_tl)) as Ef.
    rewrite /=.
    have HEf: (Ef gult_tl = (~~ interp_lit Eult_tl ls1_hd && interp_lit Eult_tl ls2_hd
             || (interp_lit Eult_tl ls1_hd == interp_lit Eult_tl ls2_hd) &&
                                                                        interp_lit Eult_tl lrult_tl)) by rewrite HeqEf env_upd_eq.
    have Hpre2: (env_preserve Eult_tl Ef g).
    {
      rewrite HeqEf.
      apply env_preserve_le with gult_tl; t_auto_preserve.
    }
    have Hpre3: (env_preserve Eult_tl Ef gult_tl) by rewrite HeqEf; t_auto_preserve.
    rewrite -(env_preserve_lit Hpre2 Hnew_gls1hd) in HEf.
    rewrite -(env_preserve_lit Hpre2 Hnew_gls2hd) in HEf.
    rewrite -(env_preserve_lit Hpre3 Hres) in HEf.
    rewrite -(env_preserve_cnf Hpre3 Hcnf) in IHH.
    rewrite IHH.
    rewrite HEf !interp_lit_neg_lit.
      by case: (interp_lit Ef ls1_hd);
        case: (interp_lit Ef ls2_hd);
        case: (interp_lit Ef lrult_tl).
Qed.

Lemma mk_env_ult_newer_gen E g ls1 ls2 E' g' cs lr:
    mk_env_ult E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  exact: mk_env_ult_rev'_zip_newer_gen.
Qed.

Lemma mk_env_ult_newer_res E g ls1 ls2 E' g' cs lr:
    mk_env_ult E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g' lr.
Proof.
  exact: mk_env_ult_rev'_zip_newer_res.
Qed.

Lemma mk_env_ult_newer_cnf E g ls1 ls2 E' g' cs lr:
  mk_env_ult E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_ult.
  move=> Hzip.
  move: (mk_env_ult_rev'_zip_newer_cnf Hzip) => Hncnf_zip.
  move=> Hgtt Hgls1 Hgls2.
  move: (newer_than_lits_rev Hgls1) => Hgls1rev.
  move: (newer_than_lits_rev Hgls2) => Hgls2rev.
  by apply Hncnf_zip; t_auto_newer.
Qed.

Lemma mk_env_ult_preserve E g ls1 ls2 E' g' cs lr:
    mk_env_ult E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  exact: mk_env_ult_rev'_zip_preserve.
Qed.

Lemma mk_env_ult_sat E g ls1 ls2 E' g' cs lr:
  mk_env_ult E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  interp_cnf E' cs.
Proof.
  rewrite /mk_env_ult.
  move=> Hzip.
  move: (mk_env_ult_rev'_zip_sat Hzip) => Hncnf_zip.
  move=> Hgtt Hgls1 Hgls2.
  move: (newer_than_lits_rev Hgls1) => Hgls1rev.
  move: (newer_than_lits_rev Hgls2) => Hgls2rev.
  by apply Hncnf_zip; t_auto_newer.
Qed.
