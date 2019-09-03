From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From BitBlasting Require Import QFBVSimple CNFSimple BBCommon BBAdd.
From ssrlib Require Import Var ZAriths Tuples Tactics.
From Bits Require Import bits extra.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_saddo ===== *)


(* https://www.wolframalpha.com/input/?i=r+%3C-%3E+(+(s1+%26%26+s2+%26%26+~s3)+%7C%7C+(~s1+%26%26+~s2+%26%26+s3)+)+CNF *)
(* (¬r ∨ ¬s1 ∨ s2) ∧ (¬r ∨ s1 ∨ ¬s2) ∧ (¬r ∨ ¬s2 ∨ ¬s3) ∧ (¬r ∨ s2 ∨ s3) ∧ (r ∨ ¬s1 ∨ ¬s2 ∨ s3) ∧ (r ∨ s1 ∨ s2 ∨ ¬s3) *)

Definition bit_blast_saddo w g (ls1 ls2 : w.+1.-tuple literal) : generator * cnf * literal :=
  let (sign1, tls1) := eta_expand (splitmsb ls1) in
  let (sign2, tls2) := eta_expand (splitmsb ls2) in
  let '(g_fa, cs_fa, cout, lrs_fa) := bit_blast_full_adder g lit_ff ls1 ls2 in
  let (sign_fa, ufa) := eta_expand (splitmsb lrs_fa) in
  let (gr, r) := gen g_fa in
  let csr := [::
                [:: neg_lit r; neg_lit sign1; sign2];
                [:: neg_lit r; sign1; neg_lit sign2];
                [:: neg_lit r; neg_lit sign2; neg_lit sign_fa];
                [:: neg_lit r; sign2; sign_fa];
                [:: r; neg_lit sign1; neg_lit sign2; sign_fa];
                [:: r; sign1; sign2; neg_lit sign_fa]
      ] in
  (gr, cs_fa ++ csr, r).

Definition mk_env_saddo w E g (ls1 ls2 : w.+1.-tuple literal) : env * generator * cnf * literal :=
  let (sign1, tls1) := eta_expand (splitmsb ls1) in
  let (sign2, tls2) := eta_expand (splitmsb ls2) in
  let '(E_fa, g_fa, cs_fa, cout, lrs_fa) := mk_env_full_adder E g lit_ff ls1 ls2 in
  let (sign_fa, ufa) := eta_expand (splitmsb lrs_fa) in
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
  (E', gr, cs_fa ++ csr, r).


Definition Saddo w (bs1 bs2 :BITS (w.+1)) :=
  let (sign1, tbs1) := eta_expand (splitmsb bs1) in
  let (sign2, tbs2) := eta_expand (splitmsb bs2) in
  let b_add := addB bs1 bs2 in
  let (sign_fa, u_fa) := eta_expand (splitmsb b_add) in
  (sign1 && sign2 && ~~sign_fa) || (~~sign1 && ~~sign2 && sign_fa).


Lemma bit_blast_saddo_correct :
  forall w g (bs1 bs2 : BITS (w.+1)) E g' ls1 ls2 cs lr,
    bit_blast_saddo g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (Saddo bs1 bs2).
Proof.
  move=> w g bs1 bs2 E g' ls1 ls2 cs lr.
  dcase (splitmsb ls1) => [[sign_ls1 tls1] Hls1].
  dcase (splitmsb ls2) => [[sign_ls2 tls2] Hls2].
  dcase (splitmsb bs1) => [[sign_bs1 tbs1] Hbs1].
  dcase (splitmsb bs2) => [[sign_bs2 tbs2] Hbs2].
  rewrite /bit_blast_saddo /gen.
  dcase (bit_blast_full_adder g lit_ff ls1 ls2) => [[[[g_fa cs_fa] cout_fa ] lrs_fa] Hblast_fa].
  case=> _ <- <-.
  move => Henc1 Henc2.
  rewrite !add_prelude_append.
  move /andP => [Hicnf_fa Hicnf].
  move: (add_prelude_enc_bit_ff Hicnf_fa) => Hencff.
  dcase (adcB false bs1 bs2) => [[bcout brs] HadcB].
  move: (bit_blast_full_adder_correct Hblast_fa Henc1 Henc2 Hencff Hicnf_fa HadcB).
  move=> [Henc_brs _].
  move: Henc1 Henc2 Henc_brs.
  rewrite !enc_bits_splitmsb => /andP [Henc_s1 Henc_t1] /andP [Henc_s2 Henc_t2] /andP [Henc_sbrs Henc_tbrs].
  move: Hicnf.
  rewrite /add_prelude.
  rewrite !interp_cnf_cons.
  dcase (splitmsb lrs_fa) => [[sign_lrs tlrs] Hlrs].
  dcase (splitmsb brs) => [[sign_brs tbrs] Hbrs].
  rewrite /Saddo.
  rewrite Hls1 Hls2 Hlrs Hbs1 Hbs2 Hbrs /= in Henc_s1 Henc_s2 Henc_sbrs |- * .
  rewrite !interp_lit_neg_lit.
  move => H. split_andb.
  rewrite /enc_bit.
  rewrite Hlrs Hbrs /= in Henc_tbrs.
  have -> : ((splitmsb (addB bs1 bs2)).1 = sign_brs).
  {
    replace sign_brs with (splitmsb brs).1.
    replace brs with (adcB false bs1 bs2).2.
    reflexivity.
    rewrite HadcB. reflexivity.
    rewrite Hbrs. reflexivity.
  }
  rewrite /=.
  move/eqP: Henc_s1 => <-.
  move/eqP: Henc_s2 => <-.
  move/eqP: Henc_sbrs => <-.
  by case H_gfa: (E g_fa); case H_s1 :(interp_lit E sign_ls1); case H_s2: (interp_lit E sign_ls2); case H_sbrs: (interp_lit E sign_lrs);
    rewrite H_gfa H_s1 H_s2 H_sbrs in H0 H1 H2 H3 H4 H5.
Qed.

Lemma mk_env_saddo_is_bit_blast_saddo :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_saddo E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_saddo g ls1 ls2 = (g', cs, lr).
Proof.
  move=> w E g ls1 ls2 E' g' cs lr.
  rewrite /mk_env_saddo /bit_blast_saddo /gen.
  case Hmkfadd : (mk_env_full_adder E g lit_ff ls1 ls2)
  => [[[[E_fadd g_fadd] cs_fadd] cout] r_fadd].
  rewrite (mk_env_full_adder_is_bit_blast_full_adder Hmkfadd) {Hmkfadd}.
  by case=> _ <- <- <-.
Qed.

Lemma mk_env_saddo_newer_gen :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_saddo E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_saddo /gen.
  case Hmkfadd : (mk_env_full_adder E g lit_ff ls1 ls2)
  => [[[[E_fadd g_fadd] cs_fadd] cout] r_fadd].
  case=> _ <- _ _.
  move: (mk_env_full_adder_newer_gen Hmkfadd) => {Hmkfadd} Hgngf.
  move : (pos_leb_add_diag_r g_fadd 1) => Hgfg1.
  by apply (pos_leb_trans Hgngf Hgfg1).
Qed.

Lemma mk_env_saddo_newer_res :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_saddo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g' lr.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_saddo /gen.
  case Hmkfadd : (mk_env_full_adder E g lit_ff ls1 ls2)
  => [[[[E_fadd g_fadd] cs_fadd] cout] r_fadd].
  case=> _ <- _ <-.
  by apply newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_saddo_newer_cnf :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_saddo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_saddo /gen.
  case Hmkfadd : (mk_env_full_adder E g lit_ff ls1 ls2)
  => [[[[E_fadd g_fadd] cs_fadd] cout] r_fadd].
  case=> _ <- <- _ Hgt Hgl1 Hgl2. rewrite /= !newer_than_cnf_append.
  (* newer_than_cnf (g_fadd+1) cs_fadd *)
  move : (mk_env_full_adder_newer_cnf Hmkfadd) => H.
  move : (H Hgt Hgl1 Hgl2) => {H} Hgfcf.
  move : (pos_leb_add_diag_r g_fadd 1) => Hgfg1.
  rewrite (newer_than_cnf_le_newer Hgfcf Hgfg1) /=.
  (* others *)
  rewrite !newer_than_lit_neg.
  case Hls1 : (splitmsb ls1) => [sign1 others1].
  case Hls2 : (splitmsb ls2) => [sign2 others2].
  case Hfa : (splitmsb r_fadd) => [sign_fa others_fa].
  rewrite /=.
  move: (mk_env_full_adder_newer_gen Hmkfadd) => Hgf.
  move: (pos_leb_trans Hgf Hgfg1) => Hggf1.
  move : (newer_than_lits_splitmsb Hgl1 Hls1) => /andP [Hgs1 _].
  move : (newer_than_lits_splitmsb Hgl2 Hls2) => /andP [Hgs2 _].
  rewrite (newer_than_lit_le_newer Hgs1 Hggf1) (newer_than_lit_le_newer Hgs2 Hggf1).
  move: (mk_env_full_adder_newer_res Hmkfadd) => H.
  move: (newer_than_lits_splitmsb H Hfa) => /andP [Hgsfa _].
  rewrite (newer_than_lit_le_newer Hgsfa Hgfg1).
  rewrite /newer_than_lit /newer_than_var /=.
  by rewrite (pos_ltb_add_diag_r g_fadd 1).
Qed.

Lemma mk_env_saddo_preserve :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_saddo E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_saddo /gen.
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

Lemma mk_env_saddo_sat :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_saddo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_saddo /gen.
  case Henv_fa : (mk_env_full_adder E g lit_ff ls1 ls2)
  => [[[[E_fa g_fa] cs_fa] cout] r_fa].
  case=> <- _ <- _. move=> Hngg Hngls1 Hngls2.
  rewrite !interp_cnf_append !interp_cnf_cons.
  remember (env_upd E_fa g_fa
           (interp_lit E_fa (splitmsb ls1).1 && interp_lit E_fa (splitmsb ls2).1 &&
            ~~ interp_lit E_fa (splitmsb r_fa).1
            || ~~ interp_lit E_fa (splitmsb ls1).1 && ~~ interp_lit E_fa (splitmsb ls2).1 &&
                 interp_lit E_fa (splitmsb r_fa).1)) as Ef.
  move: (mk_env_full_adder_sat Henv_fa Hngg Hngls1 Hngls2) => Hicnf_fa.
  move: (mk_env_full_adder_newer_gen Henv_fa) => Hggfa.
  move: (mk_env_full_adder_newer_cnf Henv_fa Hngg Hngls1 Hngls2) => H.
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
  dcase (splitmsb ls1) => [[sign_ls1 tls1] Hls1].
  dcase (splitmsb ls2) => [[sign_ls2 tls2] Hls2].
  dcase (splitmsb r_fa) => [[sign_lrs tlrs] Hlrs].
  rewrite /=.
  rewrite !interp_lit_neg_lit.
  move: (newer_than_lits_le_newer Hngls1 Hggfa) => Hngfals1.
  move: (newer_than_lits_le_newer Hngls2 Hggfa) => Hngfals2.
  move: (mk_env_full_adder_newer_res Henv_fa) => Hngfarfa.
  move: (newer_than_lits_splitmsb Hngfals1 Hls1) => /andP [ Hnfa_s1 _].
  move: (newer_than_lits_splitmsb Hngfals2 Hls2) => /andP [ Hnfa_s2 _].
  move: (newer_than_lits_splitmsb Hngfarfa Hlrs) => /andP [Hnfa_sfa _].
  rewrite !(env_preserve_lit Hpre_ef Hnfa_s1).
  rewrite !(env_preserve_lit Hpre_ef Hnfa_s2).
  rewrite !(env_preserve_lit Hpre_ef Hnfa_sfa).
  rewrite HeqEf. rewrite !env_upd_eq.
  rewrite Hls1 Hls2 Hlrs /=.
    by case (interp_lit E_fa sign_ls1);
    case (interp_lit E_fa sign_ls2);
    case (interp_lit E_fa sign_lrs).
Qed.
