
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon.
From ssrlib Require Import ZAriths Seqs Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_and ===== *)

Definition bit_blast_and1 g l1 l2 : generator * cnf * literal :=
  if (l1 == lit_ff) || (l2 == lit_ff) then (g, [::], lit_ff)
  else if l1 == lit_tt then (g, [::], l2)
       else if l2 == lit_tt then (g, [::], l1)
            else let (g', r) := gen g in
                 let cs := [:: [:: neg_lit r; l1]; [:: neg_lit r; l2];
                              [:: r; neg_lit l1; neg_lit l2]] in
                 (g', cs, r).

Definition mk_env_and1 E g l1 l2 : env * generator * cnf * literal :=
  if (l1 == lit_ff) || (l2 == lit_ff) then (E, g, [::], lit_ff)
  else if l1 == lit_tt then (E, g, [::], l2)
       else if l2 == lit_tt then (E, g, [::], l1)
            else let (g', r) := gen g in
                 let E' := env_upd E (var_of_lit r)
                                   (interp_lit E l1 && interp_lit E l2) in
                 let cs := [:: [:: neg_lit r; l1]; [:: neg_lit r; l2];
                              [:: r; neg_lit l1; neg_lit l2]] in
                 (E', g', cs, r).

Fixpoint bit_blast_and_zip g lsp : generator * cnf * word :=
  match lsp with
  | [::] => (g, [::], [::])
  | (l1, l2)::tl =>
      let '(g_hd, cs_hd, lrs_hd) := bit_blast_and1 g l1 l2 in
      let '(g_tl, cs_tl, lrs_tl) := bit_blast_and_zip g_hd tl in
      (g_tl, catrev cs_hd cs_tl, lrs_hd::lrs_tl)
  end.

Fixpoint mk_env_and_zip E g lsp : env * generator * cnf * word :=
  match lsp with
  | [::] => (E, g, [::], [::])
  | (l1, l2)::tl =>
    let '(E_hd, g_hd, cs_hd, lrs_hd) := mk_env_and1 E g l1 l2 in
    let '(E_tl, g_tl, cs_tl, lrs_tl) := mk_env_and_zip E_hd g_hd tl in
    (E_tl, g_tl, catrev cs_hd cs_tl, lrs_hd::lrs_tl)
  end.

Definition bit_blast_and g ls1 ls2 := bit_blast_and_zip g (extzip_ff ls1 ls2).

Definition mk_env_and E g ls1 ls2 := mk_env_and_zip E g (extzip_ff ls1 ls2).

Lemma bit_blast_and_size_ss :
      forall ls1 ls2 g g' cs lrs,
  bit_blast_and g ls1 ls2 = (g', cs, lrs) -> size ls1 = size ls2 -> size ls1 = size lrs.
Proof.
  elim => [|ls1_hd ls1_tl IH] ls2 g g' cs lrs.
  - move => /=Hbband Hsz0. move : Hbband. symmetry in Hsz0; rewrite (size0nil Hsz0). by case => _ _ <-.
  - rewrite/bit_blast_and /=. case ls2 => [|ls2_hd ls2_tl]; try discriminate.
    rewrite /bit_blast_and_zip (lock bit_blast_and1) /= -!lock -/bit_blast_and_zip.
    dcase (bit_blast_and1 g ls1_hd ls2_hd) => [[[g_hd cs_hd] lrs_hd] Hbband1].
    dcase (bit_blast_and_zip g_hd (extzip_ff ls1_tl ls2_tl)) => [[[g_tl cs_tl] lrs_tl] Hbbandzip].
    move => Hres Hsz. rewrite -addn1 in Hsz; symmetry in Hsz; rewrite -addn1 in Hsz. move : (addIn Hsz) => Hszeq; symmetry in Hszeq.
    rewrite /bit_blast_and in IH; rewrite (IH _ _ _ _ _ Hbbandzip Hszeq).
    by case : Hres =>  _ _ <-.
Qed.

Lemma bit_blast_and1_correct E g b1 b2 l1 l2 g' cs lr :
  bit_blast_and1 g l1 l2 = (g', cs, lr) ->
  enc_bit E l1 b1 -> enc_bit E l2 b2 ->
  interp_cnf E (add_prelude cs) -> enc_bit E lr (andb b1 b2).
Proof.
  rewrite /bit_blast_and1 /enc_bit. case Hff: ((l1 == lit_ff) || (l2 == lit_ff)).
  - case => _ <- <- /eqP <- /eqP <- /= Hpre. move: (add_prelude_tt Hpre) => /= Htt.
    case/orP: Hff => /eqP -> /=; rewrite Htt //=. by rewrite andbF.
  - case Htt1: (l1 == lit_tt); last case Htt2: (l2 == lit_tt).
    + case=> _ <- <- /eqP <- /eqP <- /= Hpre. move: (add_prelude_tt Hpre) => /= Htt.
      rewrite (eqP Htt1) /= Htt andTb. exact: eqxx.
    + case=> _ <- <- /eqP <- /eqP <- /= Hpre. move: (add_prelude_tt Hpre) => /= Htt.
      rewrite (eqP Htt2) /= Htt andbT. exact: eqxx.
    + case => _ <- <-. move=> /eqP <- /eqP <- /= /andP [/= Htt Hcs]; t_clear.
      rewrite !interp_lit_neg_lit in Hcs. move: Hcs.
      by case: (E g); case: (interp_lit E l1); case: (interp_lit E l2).
Qed.

Lemma bit_blast_and_zip_correct E g bsp lsp g' cs lrs :
  bit_blast_and_zip g lsp = (g', cs, lrs) ->
  enc_bits E (unzip1 lsp) (unzip1 bsp) -> enc_bits E (unzip2 lsp) (unzip2 bsp) ->
  interp_cnf E (add_prelude cs) -> enc_bits E lrs (map (fun e => andb e.1 e.2) bsp).
Proof.
  elim: lsp E g bsp g' cs lrs => [| [l1_hd l2_hd] lsp_tl IH] E g bsp g' cs lrs /=.
  - rewrite !enc_bits_nil_l unzip1_l_nil. case=> _ <- <- /eqP -> _ _ /=.
    exact: enc_bits_nil.
  - dcase (bit_blast_and1 g l1_hd l2_hd) => [[[g_hd cs_hd] lrs_hd] Hbb_hd].
    dcase (bit_blast_and_zip g_hd lsp_tl) => [[[g_tl cs_tl] lrs_tl] Hbb_tl].
    case=> _ <- <- /=. case: bsp => [| [bsp_hd1 bsp_hd2] bsp_tl] //=.
    rewrite !enc_bits_cons. move=> /andP [Henc1hd Henc1tl] /andP [Henc2hd Henc2tl].
    rewrite add_prelude_catrev => /andP [Hpre_hd Hpre_tl].
    rewrite (bit_blast_and1_correct Hbb_hd Henc1hd Henc2hd Hpre_hd) andTb.
    by rewrite (IH _ _ _ _ _ _ Hbb_tl Henc1tl Henc2tl Hpre_tl).
Qed.

Lemma bit_blast_and_correct g bs1 bs2 E ls1 ls2 g' cs lrs :
  bit_blast_and g ls1 ls2 = (g', cs, lrs) ->
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 -> interp_cnf E (add_prelude cs) ->
  enc_bits E lrs (andB bs1 bs2).
Proof.
  rewrite /bit_blast_and => Hbb Henc1 Henc2 Hcs.
  move: (enc_bits_size Henc1) (enc_bits_size Henc2) => Hs1 Hs2.
  move: (add_prelude_enc_bit_tt Hcs) => Henctt.
  exact: (bit_blast_and_zip_correct Hbb
                                    (enc_bits_unzip1_extzip Henctt Henc1 Henc2)
                                    (enc_bits_unzip2_extzip Henctt Henc1 Henc2) Hcs).
Qed.

Lemma mk_env_and1_is_bit_blast_and1 E g l1 l2 E' g' cs lr :
  mk_env_and1 E g l1 l2 = (E', g', cs, lr) -> bit_blast_and1 g l1 l2 = (g', cs, lr).
Proof.
  rewrite /mk_env_and1 /bit_blast_and1; intros;
    dite_hyps; dcase_hyps; subst; reflexivity.
Qed.

Lemma mk_env_and_zip_is_bit_blast_and_zip E g lsp E' g' cs lrs :
  mk_env_and_zip E g lsp = (E', g', cs, lrs) ->
  bit_blast_and_zip g lsp = (g', cs, lrs).
Proof.
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs /=.
  - by case=> _ <- <- <-.
  - dcase (mk_env_and1 E g ls1_hd ls2_hd) => [[[[E_hd g_hd] cs_hd] lrs_hd] Henv_hd].
    dcase (mk_env_and_zip E_hd g_hd lsp_tl) => [[[[E_tl g_tl] cs_tl] lrs_tl] Henv_tl].
    case=> _ <- <- <-. rewrite (mk_env_and1_is_bit_blast_and1 Henv_hd).
    by rewrite (IH _ _ _ _ _ _ Henv_tl).
Qed.

Lemma mk_env_and_is_bit_blast_and E g ls1 ls2 E' g' cs lrs :
  mk_env_and E g ls1 ls2 = (E', g', cs, lrs) ->
  bit_blast_and g ls1 ls2 = (g', cs, lrs).
Proof. exact: mk_env_and_zip_is_bit_blast_and_zip. Qed.

Lemma mk_env_and1_newer_gen E g l1 l2 E' g' cs lr :
  mk_env_and1 E g l1 l2 = (E', g', cs, lr) -> (g <=? g')%positive.
Proof.
  rewrite /mk_env_and1. case Hff : ((l1 == lit_ff) || (l2 == lit_ff)).
  - case=> _ <- _ _; exact: Pos.leb_refl.
  - case Hl1t : (l1 == lit_tt); last case Hl2t : (l2 == lit_tt); case=> _ <- _ _.
    + exact: Pos.leb_refl.
    + exact: Pos.leb_refl.
    + exact: pos_leb_add_diag_r.
Qed.

Lemma mk_env_and_zip_newer_gen E g lsp E' g' cs lrs :
  mk_env_and_zip E g lsp = (E', g', cs, lrs) -> (g <=? g')%positive.
Proof.
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs /=.
  - case=> _ <- _ _. exact: Pos.leb_refl.
  - dcase (mk_env_and1 E g ls1_hd ls2_hd) => [[[[E_hd g_hd] cs_hd] lsr_hd] Henv_hd].
    dcase (mk_env_and_zip E_hd g_hd lsp_tl) => [[[[E_tl g_tl] cs_tl] lsr_tl] Henv_tl].
    case=> _ <- _ _. apply: (pos_leb_trans (mk_env_and1_newer_gen Henv_hd)).
    exact: (IH _ _ _ _ _ _ Henv_tl).
Qed.

Lemma mk_env_and_newer_gen E g ls1 ls2 E' g' cs lrs :
  mk_env_and E g ls1 ls2 = (E', g', cs, lrs) -> (g <=? g')%positive.
Proof. exact: mk_env_and_zip_newer_gen. Qed.

Lemma mk_env_and1_newer_res E g l1 l2 E' g' cs lr :
  mk_env_and1 E g l1 l2 = (E', g', cs, lr) ->
  newer_than_lit g l1 -> newer_than_lit g l2 -> newer_than_lit g' lr.
Proof.
  rewrite /mk_env_and1. case Hff : ((l1 == lit_ff) || (l2 == lit_ff)).
  - case=> _ <- _ <-. by case/orP: Hff; move/eqP => ->.
  - case Hl1t : (l1 == lit_tt); last case Hl2t : (l2 == lit_tt); case=> _ <- _ <- //=.
    move=> _ _; exact: newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_and_zip_newer_res E g lsp E' g' cs lrs :
  mk_env_and_zip E g lsp = (E', g', cs, lrs) ->
  newer_than_lits g (unzip1 lsp) -> newer_than_lits g (unzip2 lsp) ->
  newer_than_lits g' lrs.
Proof.
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs /=.
  - by case=> _ <- _ <- _ _.
  - dcase (mk_env_and1 E g ls1_hd ls2_hd) => [[[[E_hd g_hd] cs_hd] lsr_hd] Henv_hd].
    dcase (mk_env_and_zip E_hd g_hd lsp_tl) => [[[[E_tl g_tl] cs_tl] lsr_tl] Henv_tl].
    case=> _ <- _ <-. move=> /andP [Hnew1hd Hnew1tl] /andP [Hnew2hd Hnew2tl].
    move: (mk_env_and1_newer_gen Henv_hd) => Hnewg1.
    move: (mk_env_and_zip_newer_gen Henv_tl) => Hnewg2.
    move: (mk_env_and1_newer_res Henv_hd Hnew1hd Hnew2hd)=> Hnew.
    rewrite newer_than_lits_cons.
    apply/andP; split; first by t_auto_newer.
    by rewrite (IH _ _ _ _ _ _ Henv_tl); t_auto_newer.
Qed.

Lemma mk_env_and_newer_res E g ls1 ls2 E' g' cs lrs :
  mk_env_and E g ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_lits g' lrs.
Proof.
  rewrite /mk_env_and => Henv Hnewtt Hnew1 Hnew2.
  apply: (mk_env_and_zip_newer_res Henv); by t_auto_newer.
Qed.

Lemma mk_env_and1_newer_cnf E g l1 l2 E' g' cs lr :
  mk_env_and1 E g l1 l2 = (E', g', cs, lr) ->
  newer_than_lit g l1 -> newer_than_lit g l2 -> newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_and1. case Hff : ((l1 == lit_ff) || (l2 == lit_ff)).
  - case=> _ <- <- _; done.
  - case Hl1t : (l1 == lit_tt); last case Hl2t : (l2 == lit_tt); case=> _ <- <- _ //=.
    move=> Hnew1 Hnew2. by repeat (apply/andP; split); t_auto_newer.
Qed.

Lemma mk_env_and_zip_newer_cnf E g lsp E' g' cs lrs :
  mk_env_and_zip E g lsp = (E', g', cs, lrs) ->
  newer_than_lits g (unzip1 lsp) -> newer_than_lits g (unzip2 lsp) ->
  newer_than_cnf g' cs.
Proof.
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs /=.
  - by case=> _ <- <- _ _ _.
  - dcase (mk_env_and1 E g ls1_hd ls2_hd) => [[[[E_hd g_hd] cs_hd] lsr_hd] Henv_hd].
    dcase (mk_env_and_zip E_hd g_hd lsp_tl) => [[[[E_tl g_tl] cs_tl] lsr_tl] Henv_tl].
    case=> _ <- <- _. move=> /andP [Hnew1hd Hnew1tl] /andP [Hnew2hd Hnew2tl].
    move: (mk_env_and1_newer_gen Henv_hd) => Hnewg1.
    move: (mk_env_and_zip_newer_gen Henv_tl) => Hnewg2.
    move: (mk_env_and1_newer_cnf Henv_hd Hnew1hd Hnew2hd) => Hnew1.
    rewrite newer_than_cnf_catrev. apply/andP; split; first by t_auto_newer.
    apply: (IH _ _ _ _ _ _ Henv_tl); by t_auto_newer.
Qed.

Lemma mk_env_and_newer_cnf E g ls1 ls2 E' g' cs lrs :
  mk_env_and E g ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_and => Henv Hnewtt Hnew1 Hnew2.
  apply: (mk_env_and_zip_newer_cnf Henv); by t_auto_newer.
Qed.

Lemma mk_env_and1_preserve E g l1 l2 E' g' cs lr :
  mk_env_and1 E g l1 l2 = (E', g', cs, lr) -> env_preserve E E' g.
Proof.
  rewrite /mk_env_and1. case Hff : ((l1 == lit_ff) || (l2 == lit_ff)).
  - by case=> <- _ _ _.
  - case Hl1t : (l1 == lit_tt); last case Hl2t : (l2 == lit_tt); case=> <- _ _ _ //=.
    exact: env_upd_eq_preserve.
Qed.

Lemma mk_env_and_zip_preserve E g lsp E' g' cs lrs :
  mk_env_and_zip E g lsp = (E', g', cs, lrs) -> env_preserve E E' g.
Proof.
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs /=.
  - by case=> <- _ _ _.
  - dcase (mk_env_and1 E g ls1_hd ls2_hd) => [[[[E_hd g_hd] cs_hd] lsr_hd] Henv_hd].
    dcase (mk_env_and_zip E_hd g_hd lsp_tl) => [[[[E_tl g_tl] cs_tl] lsr_tl] Henv_tl].
    case=> <- _ _ _. move: (mk_env_and1_preserve Henv_hd) => Hpre_hd.
    move: (IH _ _ _ _ _ _ Henv_tl) => Hpre_tl.
    move: (mk_env_and1_newer_gen Henv_hd) => Hnewg1. by t_auto_preserve.
Qed.

Lemma mk_env_and_preserve E g ls1 ls2 E' g' cs lrs :
  mk_env_and E g ls1 ls2 = (E', g', cs, lrs) -> env_preserve E E' g.
Proof. exact: mk_env_and_zip_preserve. Qed.

Lemma mk_env_and1_sat E g l1 l2 E' g' cs lr :
  mk_env_and1 E g l1 l2 = (E', g', cs, lr) ->
  newer_than_lit g l1 -> newer_than_lit g l2 -> interp_cnf E' cs.
Proof.
  rewrite /mk_env_and1. case Hff : ((l1 == lit_ff) || (l2 == lit_ff)).
  - by case=> <- _ <- _.
  - case Hl1t : (l1 == lit_tt); last case Hl2t : (l2 == lit_tt); case=> <- _ <- _ //=.
    move=> Hgl1 Hgl2.
    move: (newer_than_lit_neq Hgl1) (newer_than_lit_neq Hgl2) => Hngl1 Hngl2.
    rewrite /= !env_upd_eq !interp_lit_neg_lit.
    rewrite (interp_lit_env_upd_neq _ _ Hngl1).
    rewrite (interp_lit_env_upd_neq _ _ Hngl2).
    by case (interp_lit E l1); case (interp_lit E l2).
Qed.

Lemma mk_env_and_zip_sat E g lsp E' g' cs lrs :
  mk_env_and_zip E g lsp = (E', g', cs, lrs) ->
  newer_than_lits g (unzip1 lsp) -> newer_than_lits g (unzip2 lsp) ->
  interp_cnf E' cs.
Proof.
  elim: lsp E g E' g' cs lrs => [| [ls1_hd ls2_hd] lsp_tl IH] E g E' g' cs lrs /=.
  - by case=> <- _ <- _ _ _.
  - dcase (mk_env_and1 E g ls1_hd ls2_hd) => [[[[E_hd g_hd] cs_hd] lsr_hd] Henv_hd].
    dcase (mk_env_and_zip E_hd g_hd lsp_tl) => [[[[E_tl g_tl] cs_tl] lsr_tl] Henv_tl].
    case=> <- _ <- _. move=> /andP [Hnew1hd Hnew1tl] /andP [Hnew2hd Hnew2tl].
    rewrite interp_cnf_catrev.
    move: (mk_env_and1_newer_cnf Henv_hd Hnew1hd Hnew2hd) => Hnew1.
    move: (mk_env_and1_newer_gen Henv_hd) => Hnewg1.
    move: (mk_env_and1_sat Henv_hd Hnew1hd Hnew2hd) => Hcs_hd.
    move: (mk_env_and1_preserve Henv_hd) => Hpre_hd.
    move: (mk_env_and_zip_preserve Henv_tl) => Hpre_tl. apply/andP; split.
    (* interp_cnf E_tl cs_hd *)
    - rewrite (env_preserve_cnf Hpre_tl); last by t_auto_newer. assumption.
    - apply: (IH _ _ _ _ _ _ Henv_tl); by t_auto_newer.
Qed.

Lemma mk_env_and_sat E g ls1 ls2 E' g' cs lrs :
  mk_env_and E g ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  interp_cnf E' cs.
Proof.
  rewrite /mk_env_and => Henv Hnewtt Hnew1 Hnew2.
  apply: (mk_env_and_zip_sat Henv); by t_auto_newer.
Qed.

Lemma mk_env_and1_env_equal E1 E2 g l1 l2 E1' E2' g1' g2' cs1 cs2 lr1 lr2 :
  env_equal E1 E2 ->
  mk_env_and1 E1 g l1 l2 = (E1', g1', cs1, lr1) ->
  mk_env_and1 E2 g l1 l2 = (E2', g2', cs2, lr2) ->
  env_equal E1' E2' /\ g1' = g2' /\ cs1 = cs2 /\ lr1 = lr2.
Proof.
  rewrite /mk_env_and1 => Heq. case ((l1 == lit_ff) || (l2 == lit_ff)).
  - case=> ? ? ? ?; case=> ? ? ? ?; subst. done.
  - case (l1 == lit_tt).
    + case=> ? ? ? ?; case=> ? ? ? ?; subst. done.
    + case (l2 == lit_tt).
      * case=> ? ? ? ?; case=> ? ? ? ?; subst. done.
      * dcase (gen g) => [[g' r] Hg]. case=> ? ? ? ?; case=> ? ? ? ?; subst.
        repeat split. rewrite (env_equal_interp_lit l1 Heq) (env_equal_interp_lit l2 Heq).
        apply: env_equal_upd. assumption.
Qed.

Lemma mk_env_and_zip_env_equal E1 E2 g lsp E1' E2' g1' g2' cs1 cs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_and_zip E1 g lsp = (E1', g1', cs1, lrs1) ->
  mk_env_and_zip E2 g lsp = (E2', g2', cs2, lrs2) ->
  env_equal E1' E2' /\ g1' = g2' /\ cs1 = cs2 /\ lrs1 = lrs2.
Proof.
  elim: lsp E1 E2 g E1' E2' g1' g2' cs1 cs2 lrs1 lrs2
  => [| [l1 l2] lsp IH] //= E1 E2 g E1' E2' g1' g2' cs1 cs2 lrs1 lrs2 Heq.
  - case=> ? ? ? ?; case=> ? ? ? ?; subst. done.
  - dcase (mk_env_and1 E1 g l1 l2) => [[[[E_hd1 g_hd1] cs_hd1] lrs_hd1] Hvhd1].
    dcase (mk_env_and1 E2 g l1 l2) => [[[[E_hd2 g_hd2] cs_hd2] lrs_hd2] Hvhd2].
    move: (mk_env_and1_env_equal Heq Hvhd1 Hvhd2) => [Heq' [? [? ?]]]; subst.
    dcase (mk_env_and_zip E_hd1 g_hd2 lsp) => [[[[E_tl1 g_tl1] cs_tl1] lrs_tl1] Hvtl1].
    dcase (mk_env_and_zip E_hd2 g_hd2 lsp) => [[[[E_tl2 g_tl2] cs_tl2] lrs_tl2] Hvtl2].
    move: (IH _ _ _ _ _ _ _ _ _ _ _ Heq' Hvtl1 Hvtl2) => [Heq'' [? [? ?]]]; subst.
    case=> ? ? ? ?; case=> ? ? ? ?; subst. done.
Qed.

Lemma mk_env_and_env_equal E1 E2 g ls1 ls2 E1' E2' g1' g2' cs1 cs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_and E1 g ls1 ls2 = (E1', g1', cs1, lrs1) ->
  mk_env_and E2 g ls1 ls2 = (E2', g2', cs2, lrs2) ->
  env_equal E1' E2' /\ g1' = g2' /\ cs1 = cs2 /\ lrs1 = lrs2.
Proof. exact: mk_env_and_zip_env_equal. Qed.
