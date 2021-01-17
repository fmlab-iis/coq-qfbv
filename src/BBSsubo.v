From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBSub.
From ssrlib Require Import ZAriths Tactics Bools Seqs.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ===== bit_blast_ssubo ===== *)
(* TODO: check *)

(* (~s1 && s2 && s3) || (s1 && ~s2 && ~s3) *)

(* (¬r ∨ ¬s1 ∨ ¬s3) ∧ (¬r ∨ s1 ∨ s2) ∧ (¬r ∨ ¬s2 ∨ s3) ∧ (r ∨ ¬s1 ∨ s2 ∨ s3) ∧ (r ∨ s1 ∨ ¬s2 ∨ ¬s3) *)

Definition bit_blast_ssubo g ls1 ls2: generator * cnf * literal :=
  let (tls1, sign1) := eta_expand (splitmsl ls1) in
  let (tls2, sign2) := eta_expand (splitmsl ls2) in
  let '(g_sub, cs_sub, lrs_sub) := bit_blast_sub g ls1 ls2 in
  let (usub, sign_sub) := eta_expand (splitmsl lrs_sub) in
  let (gr, r) := gen g_sub in
  let csr := [::
                [:: neg_lit r; neg_lit sign1; neg_lit sign_sub];
                [:: neg_lit r; sign1; sign2];
                [:: neg_lit r; neg_lit sign2; sign_sub];
                [:: r; neg_lit sign1; sign2; sign_sub];
                [:: r; sign1; neg_lit sign2; neg_lit sign_sub]
      ] in
  (gr, catrev cs_sub csr, r).

Lemma bit_blast_ssubo_correct g bs1 bs2 E ls1 ls2 g' cs lr :
  bit_blast_ssubo g ls1 ls2 = (g', cs, lr) ->
  size ls1 == size ls2 ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bit E lr (Ssubo bs1 bs2).
Proof.
  rewrite /bit_blast_ssubo /gen.
  dcase (bit_blast_sub g ls1 ls2) => [[[g_sub cs_sub] lrs_sub] Hblast_sub].
  case=> _ <- <-.
  move => Hsz Henc1 Henc2.
  rewrite !add_prelude_catrev.
  move /andP => [Hicnf_sub Hicnf].
  move: (add_prelude_enc_bit_ff Hicnf_sub) => Hencff.
  move: (add_prelude_enc_bit_tt Hicnf_sub) => Henctt.
  dcase (subB bs1 bs2) => [brs HsubB].
  move: (bit_blast_sub_correct Hblast_sub Henc1 Henc2 Hicnf_sub (eqP Hsz)) => Henc_brs.
  have Hitt: interp_lit E lit_tt by exact: (eqP Henctt).
  move: (enc_bits_splitmsb Hitt Henc1) => /andP [Henc_s1 Henc_t1].
  move: (enc_bits_splitmsb Hitt Henc2) => /andP [Henc_s2 Henc_t2].
  move: (enc_bits_splitmsb Hitt Henc_brs) => /andP [Henc_sbrs Henc_tbrs].
  move: Hicnf.
  repeat rewrite add_prelude_cons add_prelude_singleton.
  rewrite /Ssubo.
  rewrite /=.
  rewrite !interp_lit_neg_lit.
  move => H. split_andb_hyps.
  repeat match goal with H: is_true (E var_tt) |- _ => clear H end.
  rewrite /enc_bit.
  rewrite /= in Henc_tbrs.
  move: Henc_t1 Henc_t2 Henc_tbrs.
  rewrite HsubB /=.
  move=> /eqP <- /eqP <- /eqP <-.
  move: H5 H6 H7 H8 H9.
    by case H_gfa: (E g_sub); case H_s1 :(interp_lit E (lastd lit_ff ls1)); case H_s2: (interp_lit E (lastd lit_ff ls2)); case H_sbrs: (interp_lit E (lastd lit_ff lrs_sub)).
Qed.

Definition mk_env_ssubo E g ls1 ls2: env * generator * cnf * literal :=
  let (tls1, sign1) := eta_expand (splitmsl ls1) in
  let (tls2, sign2) := eta_expand (splitmsl ls2) in
  let '(E_sub, g_sub, cs_sub, lrs_sub) := mk_env_sub E g ls1 ls2 in
  let (usub, sign_sub) := eta_expand (splitmsl lrs_sub) in
  let (gr, r) := gen g_sub in
  let E' := env_upd E_sub (var_of_lit r) (
                      (~~(interp_lit E_sub sign1) && (interp_lit E_sub sign2) && (interp_lit E_sub sign_sub)
                      ) ||
                      ((interp_lit E_sub sign1) && ~~(interp_lit E_sub sign2) && ~~(interp_lit E_sub sign_sub))) in
  let csr := [::
                [:: neg_lit r; neg_lit sign1; neg_lit sign_sub];
                [:: neg_lit r; sign1; sign2];
                [:: neg_lit r; neg_lit sign2; sign_sub];
                [:: r; neg_lit sign1; sign2; sign_sub];
                [:: r; sign1; neg_lit sign2; neg_lit sign_sub]
      ] in
  (E', gr, catrev cs_sub csr, r).

Lemma mk_env_ssubo_is_bit_blast_ssubo E g ls1 ls2 E' g' cs lr :
  mk_env_ssubo E g ls1 ls2 = (E', g', cs, lr) ->
  bit_blast_ssubo g ls1 ls2 = (g', cs, lr).
Proof.
  rewrite /mk_env_ssubo /bit_blast_ssubo /gen.
  case Hmkfsub : (mk_env_sub E g ls1 ls2)
  => [[[E_sub g_sub] cs_sub] r_sub].
  rewrite (mk_env_sub_is_bit_blast_sub Hmkfsub).
    by case=> _ <- <- <-.
Qed.

Lemma mk_env_ssubo_newer_gen E g ls1 ls2 E' g' cs lr :
  mk_env_ssubo E g ls1 ls2 = (E', g', cs, lr) ->
  (g <=? g')%positive.
Proof.
  rewrite /mk_env_ssubo /gen.
  dcase (mk_env_sub E g ls1 ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Henv_sub].
  case=> _ <- _ _.
  move: (mk_env_sub_newer_gen Henv_sub) =>  Hgngf.
  move : (pos_leb_add_diag_r g_sub 1) => Hgfg1.
  by apply (pos_leb_trans Hgngf Hgfg1).
Qed.

Lemma mk_env_ssubo_newer_res E g ls1 ls2 E' g' cs lr :
  mk_env_ssubo E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g' lr.
Proof.
  rewrite /mk_env_ssubo /gen.
  dcase (mk_env_sub E g ls1 ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Henv_sub].
  case=> _ <- _ <-.
  by apply newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_ssubo_newer_cnf E g ls1 ls2 E' g' cs lr :
  mk_env_ssubo E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_ssubo /gen.
  dcase (mk_env_sub E g ls1 ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Henv_sub].
  case=> _ <- <- _ Hgt Hgl1 Hgl2. rewrite /= !newer_than_cnf_catrev.
  (* newer_than_cnf (g_subdd+1) cs_subdd *)
  move : (mk_env_sub_newer_cnf Henv_sub Hgt Hgl1 Hgl2) => Hgfcf.
  move : (pos_leb_add_diag_r g_sub 1) => Hgfg1.
  rewrite (newer_than_cnf_le_newer Hgfcf Hgfg1) /=.
  (* others *)
  rewrite !newer_than_lit_neg.
  rewrite /=.
  move: (mk_env_sub_newer_gen Henv_sub) => Hgf.
  move: (pos_leb_trans Hgf Hgfg1) => Hggf1.
  move : (newer_than_lits_splitmsl Hgt Hgl1) => /andP [_ Hgs1].
  move : (newer_than_lits_splitmsl Hgt Hgl2) => /andP [_ Hgs2].
  rewrite (newer_than_lit_le_newer Hgs1 Hggf1) (newer_than_lit_le_newer Hgs2 Hggf1).
  move: (mk_env_sub_newer_res Henv_sub) => H.
  have Hgt2: newer_than_lit g_sub lit_tt by t_newer_hook.
  move: (newer_than_lits_splitmsl Hgt2 H) => /andP /= [_ Hgssub].
  rewrite (newer_than_lit_le_newer Hgssub Hgfg1).
  rewrite /newer_than_lit /newer_than_var /=.
  by rewrite (pos_ltb_add_diag_r g_sub 1).
Qed.

Lemma mk_env_ssubo_preserve E g ls1 ls2 E' g' cs lr :
    mk_env_ssubo E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  rewrite /mk_env_ssubo /gen.
  dcase (mk_env_sub E g ls1 ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Henv_sub].
  case=> <- _ _ _.
  move : (mk_env_sub_preserve Henv_sub) => HpEnEfgn.
  move : (mk_env_sub_newer_gen Henv_sub) => {Henv_sub} Hgngf.
  eapply env_preserve_trans.
  exact: HpEnEfgn.
  eapply env_preserve_le.
  exact: env_upd_eq_preserve.
  exact: Hgngf.
Qed.

Lemma mk_env_ssubo_sat E g ls1 ls2 E' g' cs lr :
  mk_env_ssubo E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  interp_cnf E' cs.
Proof.
  rewrite /mk_env_ssubo /gen.
  dcase (mk_env_sub E g ls1 ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Henv_sub].
  case=> <- _ <- _ Hngg Hngls1 Hngls2.
  rewrite !interp_cnf_catrev.
  rewrite !interp_cnf_cons.
  remember (env_upd E_sub g_sub
           (~~ interp_lit E_sub (lastd lit_ff ls1) && interp_lit E_sub (lastd lit_ff ls2) &&
            interp_lit E_sub (lastd lit_ff lrs_sub)
            || interp_lit E_sub (lastd lit_ff ls1) && ~~ interp_lit E_sub (lastd lit_ff ls2) &&
               ~~ interp_lit E_sub (lastd lit_ff lrs_sub))) as Ef.
  move: (mk_env_sub_sat Henv_sub Hngg Hngls1 Hngls2) => Hicnf_sub.
  move: (mk_env_sub_newer_gen Henv_sub) => Hggsub.
  move: (mk_env_sub_newer_cnf Henv_sub Hngg Hngls1 Hngls2) => H.
  move: (mk_env_sub_preserve Henv_sub) => Hpre_sub.
  have: (env_preserve E_sub Ef g_sub) => Hpre_ef.
  {
    rewrite HeqEf.
    exact: env_upd_eq_preserve.
  }
  have -> : (interp_cnf Ef cs_sub).
  {
    by rewrite (env_preserve_cnf Hpre_ef H).
  }
  rewrite /=.
  rewrite !interp_lit_neg_lit.
  move: (newer_than_lits_le_newer Hngls1 Hggsub) => Hngsubls1.
  move: (newer_than_lits_le_newer Hngls2 Hggsub) => Hngsubls2.
  move: (mk_env_sub_newer_res Henv_sub) => Hngsubrsub.
  have Hgsubtt: (newer_than_lit g_sub lit_tt) by t_newer_hook.
  move: (newer_than_lits_splitmsl Hgsubtt Hngsubls1) => /andP [ _ Hnsub_s1].
  move: (newer_than_lits_splitmsl Hgsubtt Hngsubls2) => /andP [ _ Hnsub_s2].
  move: (newer_than_lits_splitmsl Hgsubtt Hngsubrsub) => /andP [_ Hnsub_ssub].
  rewrite !(env_preserve_lit Hpre_ef Hnsub_s1).
  rewrite !(env_preserve_lit Hpre_ef Hnsub_s2).
  rewrite !(env_preserve_lit Hpre_ef Hnsub_ssub).
  rewrite HeqEf. rewrite !env_upd_eq.
  rewrite /=.
    by case (interp_lit E_sub (lastd lit_ff ls1));
    case (interp_lit E_sub (lastd lit_ff ls2));
    case (interp_lit E_sub (lastd lit_ff lrs_sub)).
Qed.

Lemma mk_env_ssubo_env_equal E1 E2 g ls1 ls2 E1' E2' g1' g2' cs1 cs2 lr1 lr2 :
  env_equal E1 E2 ->
  mk_env_ssubo E1 g ls1 ls2 = (E1', g1', cs1, lr1) ->
  mk_env_ssubo E2 g ls1 ls2 = (E2', g2', cs2, lr2) ->
  env_equal E1' E2' /\ g1' = g2' /\ cs1 = cs2 /\ lr1 = lr2.
Proof.
  rewrite /mk_env_ssubo => Heq.
  dcase (mk_env_sub E1 g ls1 ls2) => [[[[E_sub1 g_sub1] cs_sub1] lrs_sub1] Hsub1].
  dcase (mk_env_sub E2 g ls1 ls2) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hsub2].
  move: (mk_env_sub_env_equal Heq Hsub1 Hsub2) => {Heq Hsub1 Hsub2} [Heq [? [? ?]]]; subst.
  dcase (gen g_sub2) => [[g' r'] Hg']. case=> ? ? ? ?; case=> ? ? ? ?; subst.
  repeat split. rewrite !(env_equal_interp_lit _ Heq). apply: env_equal_upd.
  assumption.
Qed.
