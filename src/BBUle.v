From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From BitBlasting Require Import QFBV CNF BBCommon BBEq BBUlt BBDisj.
From ssrlib Require Import ZAriths Tactics Bools Seqs.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Definition bit_blast_ule g ls1 ls2 : generator * cnf * literal :=
  let '(g_eq, cs_eq, r_eq) := bit_blast_eq g ls1 ls2 in
  let '(g_ult, cs_ult, r_ult) := bit_blast_ult g_eq ls1 ls2 in
  let '(g_disj, cs_disj, r_disj) := bit_blast_disj g_ult r_eq r_ult in
  (g_disj, catrev cs_eq (catrev cs_ult cs_disj), r_disj).

Definition mk_env_ule E g ls1 ls2 : env * generator * cnf * literal :=
  let '(E_eq, g_eq, cs_eq, r_eq) := mk_env_eq E g ls1 ls2 in
  let '(E_ult, g_ult, cs_ult, r_ult) := mk_env_ult E_eq g_eq ls1 ls2 in
  let '(E_disj, g_disj, cs_disj, r_disj) := mk_env_disj E_ult g_ult r_eq r_ult in
  (E_disj, g_disj, catrev cs_eq (catrev cs_ult cs_disj), r_disj).

Lemma bit_blast_ule_correct g bs1 bs2 E ls1 ls2 g' cs lr:
  bit_blast_ule g ls1 ls2 = (g', cs, lr) ->
  size ls1 = size ls2 ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bit E lr (leB bs1 bs2).
Proof.
  rewrite /bit_blast_ule.
  case Heq : (bit_blast_eq g ls1 ls2) => [[g_eq cs_eq] r_eq].
  case Hult : (bit_blast_ult g_eq ls1 ls2) => [[g_ult cs_ult] r_ult].
  case Hdisj : (bit_blast_disj g_ult r_eq r_ult) => [[g_disj cs_disj] r_disj].
  case => _ <- <- Hsz Henc1 Henc2.
  rewrite 2!add_prelude_catrev.
  move => Hcnf.
  move/andP : Hcnf => [Hcnf_eq Hcnf].
  move/andP : Hcnf => [Hcnf_ult Hcnf_disj].
  move : (bit_blast_eq_correct Heq Hsz Henc1 Henc2 Hcnf_eq) => Hreq.
  move : (bit_blast_ult_correct Hult Henc1 Henc2 Hcnf_ult) => Hrult.
  move : (bit_blast_disj_correct Hdisj Hreq Hrult Hcnf_disj) => Hrdisj.
  rewrite /enc_bit in Hrdisj. move/eqP: Hrdisj => Hrdisj.
  apply/eqP. by rewrite /leB/enc_bit.
Qed.

Lemma mk_env_ule_is_bit_blast_ule E g ls1 ls2 E' g' cs lr:
  mk_env_ule E g ls1 ls2 = (E', g', cs, lr) ->
  bit_blast_ule g ls1 ls2 = (g', cs, lr).
Proof.
  rewrite /bit_blast_ule /mk_env_ule /=.
  move => H. dcase_hyps. subst.
  rewrite (mk_env_eq_is_bit_blast_eq H).
  rewrite (mk_env_ult_is_bit_blast_ult H1).
  done.
Qed.

Lemma mk_env_ule_newer_gen E g ls1 ls2 E' g' cs lr:
  mk_env_ule E g ls1 ls2 = (E', g', cs, lr) ->
  (g <=? g')%positive.
Proof.
  rewrite /mk_env_ule. rewrite /gen.
  case Heq: (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] lr_eq].
  case Hult: (mk_env_ult E_eq g_eq ls1 ls2) => [[[E_ult g_ult] cs_ult] lr_ult].
  case Hdisj: (mk_env_disj E_ult g_ult lr_eq lr_ult) => [[[E_disj g_disj] cs_disj] lr_disj].
  case. move=> _ <- _ _ .
  move: (mk_env_disj_newer_gen Hdisj) => g_ult_le_g_disj.
  move: (mk_env_ult_newer_gen Hult) => g_eq_le_g_ult.
  move: (mk_env_eq_newer_gen Heq) => g_le_g_eq.
  apply: (pos_leb_trans (pos_leb_trans g_le_g_eq g_eq_le_g_ult) g_ult_le_g_disj).
Qed.

Lemma mk_env_ule_newer_res E g ls1 ls2 E' g' cs lr :
  mk_env_ule E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g' lr.
Proof.
  rewrite /mk_env_ule. rewrite /gen.
  case Heq: (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] lr_eq].
  case Hult: (mk_env_ult E_eq g_eq ls1 ls2) => [[[E_ult g_ult] cs_ult] lr_ult].
  case Hdisj: (mk_env_disj E_ult g_ult lr_eq lr_ult) => [[[E_disj g_disj] cs_disj] lr_disj].
  case. move=> _ <- _ <-.
  exact: (mk_env_disj_newer_res Hdisj).
Qed.

Lemma mk_env_ule_newer_cnf E g ls1 ls2 E' g' cs lr :
  mk_env_ule E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_ule. rewrite /gen.
  case Heq: (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] lr_eq].
  case Hult: (mk_env_ult E_eq g_eq ls1 ls2) => [[[E_ult g_ult] cs_ult] lr_ult].
  case Hdisj: (mk_env_disj E_ult g_ult lr_eq lr_ult) => [[[E_disj g_disj] cs_disj] lr_disj].
  case. move=> _ <- <- _. move=> Hnew_gtt Hnew_gls1 Hnew_gls2.
  rewrite 2!newer_than_cnf_catrev.
  move: (mk_env_eq_newer_cnf Heq Hnew_gtt Hnew_gls1 Hnew_gls2) => H_new_cnf_geq_cseq.
  move: (mk_env_eq_newer_gen Heq) => g_le_geq.
  move: (mk_env_ult_newer_gen Hult) => geq_le_gult.
  move: (newer_than_lit_le_newer Hnew_gtt g_le_geq) => Hnew_geqtt.
  move: (newer_than_lits_le_newer Hnew_gls1 g_le_geq) => Hnew_geqls1.
  move: (newer_than_lits_le_newer Hnew_gls2 g_le_geq) => Hnew_geqls2.
  move: (mk_env_ult_newer_cnf Hult Hnew_geqtt Hnew_geqls1 Hnew_geqls2) => H_new_cnf_gult_csult.
  move: (mk_env_disj_newer_res Hdisj) => tmp.
  move: (mk_env_ult_newer_res Hult Hnew_geqtt) => tmp2.
  move: (mk_env_eq_newer_res Heq) => tmp3.
  move: (newer_than_lit_le_newer tmp3 geq_le_gult) => tmp4.
  move: (mk_env_disj_newer_cnf Hdisj tmp4 tmp2) => -> /=.
  move: (mk_env_disj_newer_gen Hdisj) => g_ult_le_g_disj.
  move: (newer_than_cnf_le_newer H_new_cnf_gult_csult g_ult_le_g_disj) => -> /=.
  move: (pos_leb_trans geq_le_gult g_ult_le_g_disj) => geq_le_gdisj.
  move: (newer_than_cnf_le_newer H_new_cnf_geq_cseq geq_le_gdisj) => -> /=.
  done.
Qed.


Lemma mk_env_ule_preserve E g ls1 ls2 E' g' cs lr :
  mk_env_ule E g ls1 ls2 = (E', g', cs, lr) ->
  env_preserve E E' g.
Proof.
  rewrite /mk_env_ule. rewrite /gen.
  case Heq: (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] lr_eq].
  case Hult: (mk_env_ult E_eq g_eq ls1 ls2) => [[[E_ult g_ult] cs_ult] lr_ult].
  case Hdisj: (mk_env_disj E_ult g_ult lr_eq lr_ult) => [[[E_disj g_disj] cs_disj] lr_disj].
  case=> <- _ _ _.
  move: (mk_env_eq_preserve Heq) => Hpre_eq.
  move: (mk_env_ult_preserve Hult) => Hpre_ult.
  move: (mk_env_disj_preserve Hdisj) => Hpre_disj.
  move: (mk_env_eq_newer_gen Heq) => Hng_eq.
  move: (mk_env_ult_newer_gen Hult) => Hng_ult.
  move: (mk_env_disj_newer_gen Hdisj) => Hng_disj.
  move: (env_preserve_le Hpre_ult Hng_eq) => Hpre2.
  move: (pos_leb_trans Hng_eq Hng_ult) => g_le_gult.
  move: (env_preserve_le Hpre_disj g_le_gult) => Hpre3.
  exact: (env_preserve_trans (env_preserve_trans Hpre_eq Hpre2) Hpre3).
Qed.


Lemma mk_env_ule_sat E g ls1 ls2 E' g' cs lr :
    mk_env_ule E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  rewrite /mk_env_ule. rewrite /gen.
  case Heq: (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] lr_eq].
  case Hult: (mk_env_ult E_eq g_eq ls1 ls2) => [[[E_ult g_ult] cs_ult] lr_ult].
  case Hdisj: (mk_env_disj E_ult g_ult lr_eq lr_ult) => [[[E_disj g_disj] cs_disj] lr_disj].
  case=> <- _ <- _. move=> Hnew_gtt Hnew_gls1 Hnew_gls2.
  rewrite 2!interp_cnf_catrev.
  move: (mk_env_eq_newer_cnf Heq Hnew_gtt Hnew_gls1 Hnew_gls2) => H_new_cnf_geq_cseq.
  move: (mk_env_eq_newer_gen Heq) => g_le_geq.
  move: (mk_env_ult_newer_gen Hult) => geq_le_gult.
  move: (newer_than_lit_le_newer Hnew_gtt g_le_geq) => Hnew_geqtt.
  move: (newer_than_lits_le_newer Hnew_gls1 g_le_geq) => Hnew_geqls1.
  move: (newer_than_lits_le_newer Hnew_gls2 g_le_geq) => Hnew_geqls2.
  move: (mk_env_ult_sat Hult Hnew_geqtt Hnew_geqls1 Hnew_geqls2) => Hsat_ult.
  move: (mk_env_disj_newer_gen Hdisj) => g_ult_le_g_disj.
  move: (mk_env_disj_preserve Hdisj) => Hpre_disj.
  move: (newer_than_lit_le_newer Hnew_geqtt geq_le_gult) => Hnew_gulttt.
  move: (newer_than_lits_le_newer Hnew_geqls1 geq_le_gult) => Hnew_gultls1.
  move: (newer_than_lits_le_newer Hnew_geqls2 geq_le_gult) => Hnew_gultls2.
  move: (mk_env_ult_newer_cnf Hult Hnew_geqtt Hnew_geqls1 Hnew_geqls2) => Hnew_cnf_gult_csult.
  move: (env_preserve_cnf Hpre_disj Hnew_cnf_gult_csult) => -> /=.
  rewrite Hsat_ult /=.
  move: (mk_env_disj_newer_res Hdisj) => tmp.
  move: (mk_env_ult_newer_res Hult Hnew_geqtt) => tmp2.
  move: (mk_env_eq_newer_res Heq) => tmp3.
  move: (newer_than_lit_le_newer tmp3 geq_le_gult) => tmp4.
  move: (mk_env_disj_sat Hdisj tmp4 tmp2) => -> /=.
  move: (mk_env_eq_sat Heq Hnew_gtt Hnew_gls1 Hnew_gls2) => H.
  move: (mk_env_eq_preserve Heq) => Hpre_eq.
  move: (mk_env_ult_preserve Hult) => Hpre_ult.
  move: (mk_env_eq_newer_cnf Heq Hnew_gtt Hnew_gls1 Hnew_gls2) => Hnew_cnf_geq_cseq.
  move: (env_preserve_cnf Hpre_ult Hnew_cnf_geq_cseq) => eq1.
  rewrite H in eq1.
  move: (mk_env_disj_newer_cnf Hdisj tmp4 tmp2) => Hnew_cnf_gdisj_csdisj.
  move: (newer_than_cnf_le_newer Hnew_cnf_geq_cseq geq_le_gult) => Hnewcnf_gult_cseq.
  move: (env_preserve_cnf Hpre_disj Hnewcnf_gult_cseq) => -> /=.
    by rewrite eq1 /=.
Qed.
