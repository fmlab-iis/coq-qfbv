From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From BitBlasting Require Import QFBVSimple CNFSimple BBCommon BBSub.
From ssrlib Require Import Var ZAriths Tuples Tactics.
From Bits Require Import bits extra.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_ssubo ===== *)


(* (~s1 && s2 && s3) || (s1 && ~s2 && ~s3) *)

(* (¬r ∨ ¬s1 ∨ ¬s3) ∧ (¬r ∨ s1 ∨ s2) ∧ (¬r ∨ ¬s2 ∨ s3) ∧ (r ∨ ¬s1 ∨ s2 ∨ s3) ∧ (r ∨ s1 ∨ ¬s2 ∨ ¬s3) *)

Definition bit_blast_ssubo w g (ls1 ls2 : w.+1.-tuple literal) : generator * cnf * literal :=
  let (sign1, tls1) := eta_expand (splitmsb ls1) in
  let (sign2, tls2) := eta_expand (splitmsb ls2) in
  let '(g_sub, cs_sub, lrs_sub) := bit_blast_sub g ls1 ls2 in
  let (sign_sub, usub) := eta_expand (splitmsb lrs_sub) in
  let (gr, r) := gen g_sub in
  let csr := [::
                [:: neg_lit r; neg_lit sign1; neg_lit sign_sub];
                [:: neg_lit r; sign1; sign2];
                [:: neg_lit r; neg_lit sign2; sign_sub];
                [:: r; neg_lit sign1; sign2; sign_sub];
                [:: r; sign1; neg_lit sign2; neg_lit sign_sub]
      ] in
  (gr, cs_sub ++ csr, r).

Definition mk_env_ssubo w E g (ls1 ls2 : w.+1.-tuple literal) : env * generator * cnf * literal :=
  let (sign1, tls1) := eta_expand (splitmsb ls1) in
  let (sign2, tls2) := eta_expand (splitmsb ls2) in
  let '(E_sub, g_sub, cs_sub, lrs_sub) := mk_env_sub E g ls1 ls2 in
  let (sign_sub, usub) := eta_expand (splitmsb lrs_sub) in
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
  (E', gr, cs_sub ++ csr, r).


Definition Ssubo w (bs1 bs2 :BITS (w.+1)) :=
  let (sign1, tbs1) := eta_expand (splitmsb bs1) in
  let (sign2, tbs2) := eta_expand (splitmsb bs2) in
  let b_sub := subB bs1 bs2 in
  let (sign_sub, t_sub) := eta_expand (splitmsb b_sub) in
  (~~sign1 && sign2 && sign_sub) || (sign1 && ~~sign2 && ~~sign_sub).


Lemma bit_blast_ssubo_correct :
  forall w g (bs1 bs2 : BITS (w.+1)) E g' ls1 ls2 cs lr,
    bit_blast_ssubo g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (Ssubo bs1 bs2).
Proof.
  move=> w g bs1 bs2 E g' ls1 ls2 cs lr.
  dcase (splitmsb ls1) => [[sign_ls1 tls1] Hls1].
  dcase (splitmsb ls2) => [[sign_ls2 tls2] Hls2].
  dcase (splitmsb bs1) => [[sign_bs1 tbs1] Hbs1].
  dcase (splitmsb bs2) => [[sign_bs2 tbs2] Hbs2].
  rewrite /bit_blast_ssubo /gen.
  dcase (bit_blast_sub g ls1 ls2) => [[[g_sub cs_sub] lrs_sub] Hblast_sub].
  case=> _ <- <-.
  move => Henc1 Henc2.
  rewrite !add_prelude_append.
  move /andP => [Hicnf_sub Hicnf].
  move: (bit_blast_sub_correct Hblast_sub Henc1 Henc2 Hicnf_sub) => Henc_brs.
  move: Henc1 Henc2 Henc_brs.
  rewrite !enc_bits_splitmsb => /andP [Henc_s1 Henc_t1] /andP [Henc_s2 Henc_t2] /andP [Henc_sbrs Henc_tbrs].
  move: Hicnf.
  rewrite /add_prelude.
  rewrite !interp_cnf_cons.
  dcase (splitmsb lrs_sub) => [[sign_lrs tlrs] Hlrs].
  dcase (splitmsb (bs1-bs2)%bits) => [[sign_brs tbrs] Hbrs].
  rewrite /Ssubo.
  rewrite Hls1 Hls2 Hlrs Hbs1 Hbs2 Hbrs /= in Henc_s1 Henc_s2 Henc_sbrs |- * .
  rewrite !interp_lit_neg_lit.
  move => H. split_andb.
  rewrite /enc_bit.
  rewrite Hlrs Hbrs /= in Henc_tbrs.
  rewrite /=.
  move/eqP: Henc_s1 => <-.
  move/eqP: Henc_s2 => <-.
  move/eqP: Henc_sbrs => <-.
  by case H_gsub: (E g_sub); case H_s1 :(interp_lit E sign_ls1); case H_s2: (interp_lit E sign_ls2); case H_sbrs: (interp_lit E sign_lrs);
    rewrite H_gsub H_s1 H_s2 H_sbrs in H0 H1 H2 H3 H4 H5.
Qed.

Lemma mk_env_ssubo_is_bit_blast_ssubo :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_ssubo E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_ssubo g ls1 ls2 = (g', cs, lr).
Proof.
  move=> w E g ls1 ls2 E' g' cs lr.
  rewrite /mk_env_ssubo /bit_blast_ssubo /gen.
  dcase (mk_env_sub E g ls1 ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Henv_sub].
  rewrite (mk_env_sub_is_bit_blast_sub Henv_sub).
  by case=> _ <- <- <-.
Qed.

Lemma mk_env_ssubo_newer_gen :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_ssubo E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_ssubo /gen.
  dcase (mk_env_sub E g ls1 ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Henv_sub].
  case=> _ <- _ _.
  move: (mk_env_sub_newer_gen Henv_sub) =>  Hgngf.
  move : (pos_leb_add_diag_r g_sub 1) => Hgfg1.
  by apply (pos_leb_trans Hgngf Hgfg1).
Qed.

Lemma mk_env_ssubo_newer_res :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_ssubo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g' lr.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_ssubo /gen.
  dcase (mk_env_sub E g ls1 ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Henv_sub].
  case=> _ <- _ <-.
  by apply newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_ssubo_newer_cnf :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_ssubo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_ssubo /gen.
  dcase (mk_env_sub E g ls1 ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Henv_sub].
  case=> _ <- <- _ Hgt Hgl1 Hgl2. rewrite /= !newer_than_cnf_append.
  (* newer_than_cnf (g_subdd+1) cs_subdd *)
  move : (mk_env_sub_newer_cnf Henv_sub) => H.
  move : (H Hgt Hgl1 Hgl2) => {H} Hgfcf.
  move : (pos_leb_add_diag_r g_sub 1) => Hgfg1.
  rewrite (newer_than_cnf_le_newer Hgfcf Hgfg1) /=.
  (* others *)
  rewrite !newer_than_lit_neg.
  case Hls1 : (splitmsb ls1) => [sign1 others1].
  case Hls2 : (splitmsb ls2) => [sign2 others2].
  case Hsub : (splitmsb lrs_sub) => [sign_sub others_sub].
  rewrite /=.
  move: (mk_env_sub_newer_gen Henv_sub) => Hgf.
  move: (pos_leb_trans Hgf Hgfg1) => Hggf1.
  move : (newer_than_lits_splitmsb Hgl1 Hls1) => /andP [Hgs1 _].
  move : (newer_than_lits_splitmsb Hgl2 Hls2) => /andP [Hgs2 _].
  rewrite (newer_than_lit_le_newer Hgs1 Hggf1) (newer_than_lit_le_newer Hgs2 Hggf1).
  move: (mk_env_sub_newer_res Henv_sub) => H.
  move: (newer_than_lits_splitmsb H Hsub) => /andP [Hgssub _].
  rewrite (newer_than_lit_le_newer Hgssub Hgfg1).
  rewrite /newer_than_lit /newer_than_var /=.
  by rewrite (pos_ltb_add_diag_r g_sub 1).
Qed.

Lemma mk_env_ssubo_preserve :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_ssubo E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_ssubo /gen.
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

Lemma mk_env_ssubo_sat :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_ssubo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_ssubo /gen.
  dcase (mk_env_sub E g ls1 ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Henv_sub].
  case=> <- _ <- _. move=> Hngg Hngls1 Hngls2.
  rewrite !interp_cnf_append !interp_cnf_cons.
  remember (env_upd E_sub g_sub
           (~~ interp_lit E_sub (splitmsb ls1).1 && interp_lit E_sub (splitmsb ls2).1 &&
            interp_lit E_sub (splitmsb lrs_sub).1
            || interp_lit E_sub (splitmsb ls1).1 && ~~ interp_lit E_sub (splitmsb ls2).1 &&
               ~~ interp_lit E_sub (splitmsb lrs_sub).1)) as Ef.
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
  dcase (splitmsb ls1) => [[sign_ls1 tls1] Hls1].
  dcase (splitmsb ls2) => [[sign_ls2 tls2] Hls2].
  dcase (splitmsb lrs_sub) => [[sign_lrs tlrs] Hlrs].
  rewrite /=.
  rewrite !interp_lit_neg_lit.
  move: (newer_than_lits_le_newer Hngls1 Hggsub) => Hngsubls1.
  move: (newer_than_lits_le_newer Hngls2 Hggsub) => Hngsubls2.
  move: (mk_env_sub_newer_res Henv_sub) => Hngsubrsub.
  move: (newer_than_lits_splitmsb Hngsubls1 Hls1) => /andP [ Hnsub_s1 _].
  move: (newer_than_lits_splitmsb Hngsubls2 Hls2) => /andP [ Hnsub_s2 _].
  move: (newer_than_lits_splitmsb Hngsubrsub Hlrs) => /andP [Hnsub_ssub _].
  rewrite !(env_preserve_lit Hpre_ef Hnsub_s1).
  rewrite !(env_preserve_lit Hpre_ef Hnsub_s2).
  rewrite !(env_preserve_lit Hpre_ef Hnsub_ssub).
  rewrite HeqEf. rewrite !env_upd_eq.
  rewrite Hls1 Hls2 Hlrs /=.
    by case (interp_lit E_sub sign_ls1);
    case (interp_lit E_sub sign_ls2);
    case (interp_lit E_sub sign_lrs).
Qed.
