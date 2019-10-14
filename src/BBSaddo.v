From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBAdd.
From ssrlib Require Import ZAriths Tactics Bools Seqs.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_saddo ===== *)
(* TODO: check *)

Definition bit_blast_saddo g ls1 ls2: generator * cnf * literal :=
  let (tls1, sign1) := eta_expand (splitmsl ls1) in
  let (tls2, sign2) := eta_expand (splitmsl ls2) in
  let '(g_fa, cs_fa, cout, lrs_fa) := bit_blast_full_adder g lit_ff ls1 ls2 in
  let (ufa, sign_fa) := eta_expand (splitmsl lrs_fa) in
  let (gr, r) := gen g_fa in
  let csr := [::
                [:: neg_lit r; neg_lit sign1; sign2];
                [:: neg_lit r; sign1; neg_lit sign2];
                [:: neg_lit r; neg_lit sign2; neg_lit sign_fa];
                [:: neg_lit r; sign2; sign_fa];
                [:: r; neg_lit sign1; neg_lit sign2; sign_fa];
                [:: r; sign1; sign2; neg_lit sign_fa]
             ] in
  (gr, catrev cs_fa csr, r).

Lemma bit_blast_saddo_correct g bs1 bs2 E ls1 ls2 g' cs lr :
  bit_blast_saddo g ls1 ls2 = (g', cs, lr) ->
  size ls1 == size ls2 ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bit E lr (Saddo bs1 bs2).
Proof.
  rewrite /bit_blast_saddo /gen.
  dcase (bit_blast_full_adder g lit_ff ls1 ls2) => [[[[g_fa cs_fa] cout_fa ] lrs_fa] Hblast_fa].
  case=> _ <- <-.
  move => Hsz Henc1 Henc2.
  rewrite !add_prelude_catrev.
  move /andP => [Hicnf_fa Hicnf].
  move: (add_prelude_enc_bit_ff Hicnf_fa) => Hencff.
  move: (add_prelude_enc_bit_tt Hicnf_fa) => Henctt.
  dcase (adcB false bs1 bs2) => [[bcout brs] HadcB].
  move: (bit_blast_full_adder_correct Hblast_fa Henc1 Henc2 Hencff Hicnf_fa HadcB (eqP Hsz)).
  move=> [Henc_bcout Henc_brs].
  have Hitt: interp_lit E lit_tt by exact: (eqP Henctt).
  move: (enc_bits_splitmsb Hitt Henc1) => /andP [Henc_s1 Henc_t1].
  move: (enc_bits_splitmsb Hitt Henc2) => /andP [Henc_s2 Henc_t2].
  move: (enc_bits_splitmsb Hitt Henc_brs) => /andP [Henc_sbrs Henc_tbrs].
  move: Hicnf.
  repeat rewrite add_prelude_cons add_prelude_singleton.
  rewrite /Saddo.
  rewrite /=.
  rewrite !interp_lit_neg_lit.
  move => H. split_andb_hyps.
  repeat match goal with H: is_true (E var_tt) |- _ => clear H end.
  rewrite /enc_bit.
  rewrite /= in Henc_tbrs.
  move: Henc_t1 Henc_t2 Henc_tbrs.
  rewrite /addB HadcB /=.
  move=> /eqP <- /eqP <- /eqP <-.
  move: H6 H7 H8 H9 H10 H11.
    by case H_gfa: (E g_fa); case H_s1 :(interp_lit E (lastd lit_ff ls1)); case H_s2: (interp_lit E (lastd lit_ff ls2)); case H_sbrs: (interp_lit E (lastd lit_ff lrs_fa)).
Qed.

Definition mk_env_saddo E g ls1 ls2: env * generator * cnf * literal :=
  let (tls1, sign1) := eta_expand (splitmsl ls1) in
  let (tls2, sign2) := eta_expand (splitmsl ls2) in
  let '(E_fa, g_fa, cs_fa, cout, lrs_fa) := mk_env_full_adder E g lit_ff ls1 ls2 in
  let (ufa, sign_fa) := eta_expand (splitmsl lrs_fa) in
  let (gr, r) := gen g_fa in
  let E' := env_upd E_fa (var_of_lit r) (
                      ((interp_lit E_fa sign1) && (interp_lit E_fa sign2) && ~~ (interp_lit E_fa sign_fa)
                      ) ||
                      (~~(interp_lit E_fa sign1) && ~~(interp_lit E_fa sign2) && (interp_lit E_fa sign_fa))) in
  let csr := [::
                [:: neg_lit r; neg_lit sign1; sign2];
                [:: neg_lit r; sign1; neg_lit sign2];
                [:: neg_lit r; neg_lit sign2; neg_lit sign_fa];
                [:: neg_lit r; sign2; sign_fa];
                [:: r; neg_lit sign1; neg_lit sign2; sign_fa];
                [:: r; sign1; sign2; neg_lit sign_fa]
             ] in
  (E', gr, catrev cs_fa csr, r).

Lemma mk_env_saddo_is_bit_blast_saddo E g ls1 ls2 E' g' cs lr :
  mk_env_saddo E g ls1 ls2 = (E', g', cs, lr) ->
  bit_blast_saddo g ls1 ls2 = (g', cs, lr).
Proof.
  rewrite /mk_env_saddo /bit_blast_saddo /gen.
  case Hmkfadd : (mk_env_full_adder E g lit_ff ls1 ls2)
  => [[[[E_fadd g_fadd] cs_fadd] cout] r_fadd].
  rewrite (mk_env_full_adder_is_bit_blast_full_adder Hmkfadd) {Hmkfadd}.
    by case=> _ <- <- <-.
Qed.

Lemma mk_env_saddo_newer_gen E g ls1 ls2 E' g' cs lr :
  mk_env_saddo E g ls1 ls2 = (E', g', cs, lr) ->
  (g <=? g')%positive.
Proof.
  rewrite /mk_env_saddo /gen.
  case Hmkfadd : (mk_env_full_adder E g lit_ff ls1 ls2)
  => [[[[E_fadd g_fadd] cs_fadd] cout] r_fadd].
  case=> _ <- _ _.
  move: (mk_env_full_adder_newer_gen Hmkfadd) => {Hmkfadd} Hgngf.
  move : (pos_leb_add_diag_r g_fadd 1) => Hgfg1.
    by apply (pos_leb_trans Hgngf Hgfg1).
Qed.

Lemma mk_env_saddo_newer_res E g ls1 ls2 E' g' cs lr :
  mk_env_saddo E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g' lr.
Proof.
  rewrite /mk_env_saddo /gen.
  case Hmkfadd : (mk_env_full_adder E g lit_ff ls1 ls2)
  => [[[[E_fadd g_fadd] cs_fadd] cout] r_fadd].
  case=> _ <- _ <-.
    by apply newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_saddo_newer_cnf E g ls1 ls2 E' g' cs lr :
  mk_env_saddo E g ls1 ls2 = (E', g', cs, lr) ->
  size ls1 == size ls2 ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_saddo /gen.
  case Hmkfadd : (mk_env_full_adder E g lit_ff ls1 ls2)
  => [[[[E_fadd g_fadd] cs_fadd] cout] r_fadd].
  case=> _ <- <- _ Hsz Hgt Hgl1 Hgl2. rewrite /= !newer_than_cnf_catrev.
  (* newer_than_cnf (g_fadd+1) cs_fadd *)
  move : (mk_env_full_adder_newer_cnf Hmkfadd Hgl1 Hgl2 Hgt (eqP Hsz)) => Hgfcf.
  move : (pos_leb_add_diag_r g_fadd 1) => Hgfg1.
  rewrite (newer_than_cnf_le_newer Hgfcf Hgfg1) /=.
  (* others *)
  rewrite !newer_than_lit_neg.
  rewrite /=.
  move: (mk_env_full_adder_newer_gen Hmkfadd) => Hgf.
  move: (pos_leb_trans Hgf Hgfg1) => Hggf1.
  move : (newer_than_lits_splitmsl Hgt Hgl1) => /andP [_ Hgs1].
  move : (newer_than_lits_splitmsl Hgt Hgl2) => /andP [_ Hgs2].
  rewrite (newer_than_lit_le_newer Hgs1 Hggf1) (newer_than_lit_le_newer Hgs2 Hggf1).
  move: (mk_env_full_adder_newer_res Hmkfadd) => H.
  have Hgt2: newer_than_lit g_fadd lit_tt by t_newer_hook.
  move: (newer_than_lits_splitmsl Hgt2 H) => /andP /= [_ Hgsfa].
  rewrite (newer_than_lit_le_newer Hgsfa Hgfg1).
  rewrite /newer_than_lit /newer_than_var /=.
    by rewrite (pos_ltb_add_diag_r g_fadd 1).
Qed.

Lemma mk_env_saddo_preserve E g ls1 ls2 E' g' cs lr :
    mk_env_saddo E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  rewrite /mk_env_saddo /gen.
  case Hmkfadd : (mk_env_full_adder E g lit_ff ls1 ls2)
  => [[[[E_fadd g_fadd] cs_fadd] cout] r_fadd].
  case=> <- _ _ _.
  move : (mk_env_full_adder_preserve Hmkfadd) => HpEnEfgn.
  move : (mk_env_full_adder_newer_gen Hmkfadd) => {Hmkfadd} Hgngf.
  eapply env_preserve_trans.
  exact: HpEnEfgn.
  eapply env_preserve_le.
  exact: env_upd_eq_preserve.
  exact: Hgngf.
Qed.

Lemma mk_env_saddo_sat E g ls1 ls2 E' g' cs lr :
  mk_env_saddo E g ls1 ls2 = (E', g', cs, lr) ->
  size ls1 == size ls2 ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  interp_cnf E' cs.
Proof.
  rewrite /mk_env_saddo /gen.
  case Henv_fa : (mk_env_full_adder E g lit_ff ls1 ls2)
  => [[[[E_fa g_fa] cs_fa] cout] r_fa].
  case=> <- _ <- _ Hsz Hngg Hngls1 Hngls2.
  rewrite !interp_cnf_catrev.
  rewrite !interp_cnf_cons.
  remember (env_upd E_fa g_fa
           (interp_lit E_fa (lastd lit_ff ls1) && interp_lit E_fa (lastd lit_ff ls2) &&
            ~~ interp_lit E_fa (lastd lit_ff r_fa)
            || ~~ interp_lit E_fa (lastd lit_ff ls1) && ~~ interp_lit E_fa (lastd lit_ff ls2) &&
               interp_lit E_fa (lastd lit_ff r_fa))) as Ef.
  move: (mk_env_full_adder_sat Henv_fa Hngls1 Hngls2 Hngg (eqP Hsz)) => Hicnf_fa.
  move: (mk_env_full_adder_newer_gen Henv_fa) => Hggfa.
  move: (mk_env_full_adder_newer_cnf Henv_fa Hngls1 Hngls2 Hngg (eqP Hsz)) => H.
  move: (mk_env_full_adder_preserve Henv_fa) => Hpre_fa.
  have: (env_preserve E_fa Ef g_fa) => Hpre_ef.
  {
    rewrite HeqEf.
    exact: env_upd_eq_preserve.
  }
  have -> : (interp_cnf Ef cs_fa).
  {
      by rewrite (env_preserve_cnf Hpre_ef H).
  }
  rewrite /=.
  rewrite !interp_lit_neg_lit.
  move: (newer_than_lits_le_newer Hngls1 Hggfa) => Hngfals1.
  move: (newer_than_lits_le_newer Hngls2 Hggfa) => Hngfals2.
  move: (mk_env_full_adder_newer_res Henv_fa) => Hngfarfa.
  have Hgfatt: (newer_than_lit g_fa lit_tt) by t_newer_hook.
  move: (newer_than_lits_splitmsl Hgfatt Hngfals1) => /andP [ _ Hnfa_s1 ].
  move: (newer_than_lits_splitmsl Hgfatt Hngfals2) => /andP [ _ Hnfa_s2 ].
  move: (newer_than_lits_splitmsl Hgfatt Hngfarfa) => /andP [ _ Hnfa_sfa ].
  rewrite !(env_preserve_lit Hpre_ef Hnfa_s1).
  rewrite !(env_preserve_lit Hpre_ef Hnfa_s2).
  rewrite !(env_preserve_lit Hpre_ef Hnfa_sfa).
  rewrite HeqEf. rewrite !env_upd_eq.
  rewrite /=.
    by case (interp_lit E_fa (lastd lit_ff ls1));
      case (interp_lit E_fa (lastd lit_ff ls2));
      case (interp_lit E_fa (lastd lit_ff r_fa)).
Qed.
