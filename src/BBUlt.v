
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon BBEq.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_ult ===== *)

(*Parameter bit_blast_ult : forall w : nat, generator -> w.-tuple literal -> w.-tuple literal -> generator * cnf * literal.*)
(* https://www.wolframalpha.com/input/?i=r+%3C-%3E+(l+%7C%7C+(e+%26%26+~b1+%26%26+b2))+CNF *)
Fixpoint bit_blast_ult w (g : generator) : w.-tuple literal -> w.-tuple literal -> generator * cnf * literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(geq_tl, cseq_tl, lrseq_tl) := bit_blast_eq g ls1_tl ls2_tl in
      let '(gult_tl, csult_tl, lrsult_tl) := bit_blast_ult geq_tl ls1_tl ls2_tl in
      let (g_r, r) := gen gult_tl in
      let cs := [::
            [:: neg_lit ls1_hd; lrsult_tl; neg_lit r];
            [:: ls1_hd; neg_lit ls2_hd; neg_lit lrseq_tl; r];
            [:: ls2_hd; lrsult_tl; neg_lit r];
            [:: lrseq_tl; lrsult_tl; neg_lit r];
            [:: neg_lit lrsult_tl; r]
          ] in
      (g_r, cseq_tl ++ csult_tl ++ cs, r)
  else
    fun _ _ =>
      (g, [::], lit_ff).


Fixpoint mk_env_ult w E (g : generator) : w.-tuple literal -> w.-tuple literal -> env * generator * cnf * literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(Eeq_tl, geq_tl, cseq_tl, lrseq_tl) := mk_env_eq E g ls1_tl ls2_tl in
      let '(Eult_tl, gult_tl, csult_tl, lrsult_tl) := mk_env_ult Eeq_tl geq_tl ls1_tl ls2_tl in
      let (g_r, r) := gen gult_tl in
      let E' := env_upd Eult_tl (var_of_lit r)
                        (
                          interp_lit Eult_tl lrsult_tl ||
                          interp_lit Eult_tl lrseq_tl &&
                          ~~interp_lit Eult_tl ls1_hd &&
                           interp_lit Eult_tl ls2_hd
                        ) in
      let cs := [::
            [:: neg_lit ls1_hd; lrsult_tl; neg_lit r];
            [:: ls1_hd; neg_lit ls2_hd; neg_lit lrseq_tl; r];
            [:: ls2_hd; lrsult_tl; neg_lit r];
            [:: lrseq_tl; lrsult_tl; neg_lit r];
            [:: neg_lit lrsult_tl; r]
          ] in
      (E', g_r, cseq_tl ++ csult_tl ++ cs, r)
  else
    fun _ _ =>
      (E, g, [::], lit_ff).


Lemma bit_blast_ult_correct :
  forall w g (bs1 bs2 : BITS w) E g' ls1 ls2 cs lr,
    bit_blast_ult g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (ltB bs1 bs2).
Proof.
  elim.
  - move=> g bs1 bs2 E g' ls1 ls2 cs lr. rewrite tuple0 (lock interp_cnf) /=.
    case=> _ _ <- _ _ . rewrite -lock. exact: add_prelude_enc_bit_ff.
  - move=> w IH g.
    move=> /tupleP [bs1_hd bs1_tl] /tupleP [bs2_hd bs2_tl] E g'.
    move=> /tupleP [ls1_hd ls1_tl] /tupleP [ls2_hd ls2_tl] cs lr.
    rewrite /bit_blast_ult -/bit_blast_ult. rewrite (lock interp_cnf).
    rewrite /splitlsb /=. repeat rewrite beheadCons theadCons. rewrite /=.
    rewrite -lock.
    case Heq: (bit_blast_eq g ls1_tl ls2_tl) =>
    [[geq_tl cseq_tl] lrseq_tl].
    case Hult: (bit_blast_ult geq_tl ls1_tl ls2_tl) =>
    [[gult_tl csult_tl] lrsult_tl].
    case=> Hog Hocs Holr. move=> /andP [Hels1_hd Hels1_tl] /andP [Hels2_hd Hels2_tl].     move=> Hcnf.
    move: (IH geq_tl bs1_tl bs2_tl E gult_tl ls1_tl ls2_tl csult_tl lrsult_tl Hult) => HIH.
    rewrite -Hocs in Hcnf.
    rewrite add_prelude_append in Hcnf. move/andP :Hcnf => [Hprelude_eq Hcnf].
    rewrite add_prelude_append in Hcnf. move/andP :Hcnf => [Hprelude_ult Hcnf].
    rewrite /add_prelude in Hcnf. repeat rewrite interp_cnf_cons interp_cnf_append in Hcnf. repeat rewrite interp_cnf_cons in Hcnf. repeat rewrite interp_clause_cons in Hcnf.
    repeat rewrite interp_lit_neg_lit in Hcnf. rewrite /= in Hcnf.
    split_andb.
    move: (HIH Hels1_tl Hels2_tl Hprelude_ult) => Heult.
    move: (@bit_blast_eq_correct w g bs1_tl bs2_tl E geq_tl ls1_tl ls2_tl cseq_tl lrseq_tl Heq Hels1_tl Hels2_tl Hprelude_eq) => Heeq.
    rewrite -Holr => {Holr}.
    move=> {H H5 Hocs Hult Heq IH HIH Hprelude_eq Hprelude_ult}.
    rewrite /enc_bit in Hels1_hd Hels2_hd Heult Heeq.
    case Hbs1_hd :(bs1_hd); case Hbs2_hd: (bs2_hd); case Hceq: (bs1_tl == bs2_tl);
      case Hclt: (ltB bs1_tl bs2_tl); rewrite //=.
    all: rewrite Hbs1_hd in Hels1_hd; rewrite Hbs2_hd in Hels2_hd; case Heg: (E gult_tl).
    all:rewrite /enc_bit /=; try by apply /eqP.
    all: move/eqP: Hels1_hd => -> in H0 H1 H2 H3 H4.
    all: move/eqP: Hels2_hd => -> in H0 H1 H2 H3 H4.
    all: move/eqP: Heult => -> in H0 H1 H2 H3 H4.
    all: move/eqP: Heeq => -> in H0 H1 H2 H3 H4.
    all: rewrite Heg Hceq Hclt /= in H0 H1 H2 H3 H4.
    all: done.
Qed.

Lemma mk_env_ult_is_bit_blast_ult :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_ult E g ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_ult g ls1 ls2 = (g', cs, lrs).
Proof.
  elim.
  - rewrite /=; intros; dcase_hyps; subst; reflexivity.
  - intros_tuple; dcase_hyps; intros; subst.
    move: (mk_env_eq_is_bit_blast_eq H0) => ->.
    by rewrite (H _ _ _ _ _ _ _ _ H2).
Qed.

Lemma mk_env_ult_newer_gen :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_ult E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr. case=> _ <- _ _. exact: Pos.leb_refl.
  - move=> w IH E g. case/tupleP=> [ls1_hd ls1_tl]. case/tupleP=> [ls2_hd ls2_tl].
    move=> E' g' cs lr.  rewrite /= !theadE !beheadCons.
    case Henv_eq: (mk_env_eq E g ls1_tl ls2_tl) => [[[Eeq_tl geq_tl] cseq_tl] lrseq_tl].
    case Henv_ult: (mk_env_ult Eeq_tl geq_tl ls1_tl ls2_tl) => [[[Eult_tl gult_tl] csult_tl] lrsult_tl].
    case => _ <- _ _.
    move: (mk_env_eq_newer_gen Henv_eq) => Hng_eq.
    move: (IH _ _ _ _ _ _ _ _ Henv_ult) => Hng_ult.
    apply: (pos_leb_trans Hng_eq _ ).
    apply: (pos_leb_trans Hng_ult _ ).
    exact: (pos_leb_add_diag_r gult_tl 1).
Qed.

Lemma mk_env_ult_newer_res :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_ult E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g' lr.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr. case=> _ <- _ <-. done.
  - move=> w IH E g /tupleP [ls1_hd ls1_tl] /tupleP [ls2_hd ls2_tl] E' g' cs lr.
    rewrite /= !theadE !beheadCons.
    case Henv_eq: (mk_env_eq E g ls1_tl ls2_tl) => [[[Eeq_tl geq_tl] cseq_tl] lrseq_tl].
    case Henv_ult: (mk_env_ult Eeq_tl geq_tl ls1_tl ls2_tl) => [[[Eult_tl gult_tl] csult_tl] lrsult_tl].
    case. move=> _ <- _ <-. move=> Hnew_g_lit_tt.
    move: (IH _ _ _ _ _ _ _ _ Henv_ult).
    move: (mk_env_eq_newer_gen Henv_eq) => Hle_ggeq.
    (* move: (@newer_than_lit_add_r g lit_tt 1 Hnew_g_lit_tt)=> Hnew_g1_lit_tt. *)
    move: (newer_than_lit_le_newer Hnew_g_lit_tt Hle_ggeq) => tmp.
    move=> H. move: (H tmp) => {H tmp}. move=> Hnew_gult_lrsult.
    move: (mk_env_eq_newer_res Henv_eq) => Hnew_geq_lrseq.
    rewrite /newer_than_lit /newer_than_var /=.
    move: (mk_env_ult_newer_gen Henv_ult) => tmp.
    exact: (pos_ltb_add_diag_r gult_tl 1).
Qed.

Lemma mk_env_ult_newer_cnf :
forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
  mk_env_ult E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr /=. case=> _ _ <- _. done.
  - move=> w IH E g /tupleP [ls1_hd ls1_tl] /tupleP [ls2_hd ls2_tl] E' g' cs lr.
    rewrite /= !theadE !beheadCons.
    case Henv_eq: (mk_env_eq E g ls1_tl ls2_tl) => [[[Eeq_tl geq_tl] cseq_tl] lrseq_tl].
    case Henv_ult: (mk_env_ult Eeq_tl geq_tl ls1_tl ls2_tl) => [[[Eult_tl gult_tl] csult_tl] lrsult_tl].
    case=> _ <- <- _. move=> Hnew_gtt /andP [Hnew_g_ls1hd Hnew_g_ls1_tl] /andP [Hnew_g_ls2hd Hnew_g_ls2_tl].
    rewrite 2!newer_than_cnf_append.
    move: (pos_leb_add_diag_r g 1) => H_ggp1.
    move: (mk_env_eq_newer_cnf Henv_eq Hnew_g_ls1_tl Hnew_g_ls2_tl) => Hncnf_geq_cseq.
    move: (mk_env_ult_newer_gen Henv_ult) => tmp.
    move: (pos_leb_trans tmp (pos_leb_add_diag_r gult_tl 1)) => {tmp} tmp.
    rewrite (newer_than_cnf_le_newer Hncnf_geq_cseq tmp) andTb => {tmp}.
    move: (IH _ _ _ _ _ _ _ _ Henv_ult).
    move: (mk_env_eq_newer_gen Henv_eq) => tmp.
    move: (newer_than_lit_le_newer Hnew_gtt tmp) => H1 .
    move: (newer_than_lits_le_newer Hnew_g_ls1_tl tmp) => H2 .
    move: (newer_than_lits_le_newer Hnew_g_ls2_tl tmp) => H3 .
    move => H4. move : (H4 H1 H2 H3) => {H1 H2 H3 H4} H.
    rewrite (newer_than_cnf_le_newer H (pos_leb_add_diag_r gult_tl 1)) => {H}.
    rewrite andTb. rewrite /=.
    rewrite !newer_than_lit_neg.
    move: (mk_env_ult_newer_gen Henv_ult)=> tmp3.
    move: (pos_leb_trans tmp tmp3) => tmp4.
    move: (pos_leb_trans tmp4 (pos_leb_add_diag_r gult_tl 1)) => tmp5.
    rewrite (newer_than_lit_le_newer Hnew_g_ls1hd tmp5) /=.
    rewrite (newer_than_lit_le_newer Hnew_g_ls2hd tmp5) /= andbT.
    move: (mk_env_ult_newer_res Henv_ult).
    move: (newer_than_lit_le_newer Hnew_gtt tmp) => -> H.
    assert true as I by done.
    rewrite (newer_than_lit_le_newer (H I) (pos_leb_add_diag_r gult_tl 1)) /= => {H}.
    move: (mk_env_eq_newer_res Henv_eq) => H.
    move: (pos_leb_trans tmp3 (pos_leb_add_diag_r gult_tl 1)) => tmp6.
    move: (newer_than_lit_le_newer H tmp6) => -> /=.
    rewrite /newer_than_lit /newer_than_var /=.
    by rewrite (pos_ltb_add_diag_r gult_tl 1).
Qed.


Lemma mk_env_ult_preserve :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_ult E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr /=. case=> <- _ _ _. done.
  - move=> w IH E g /tupleP [ls1_hd ls1_tl] /tupleP [ls2_hd ls2_tl] E' g' cs lr.
    rewrite /= !theadE !beheadCons.
    case Henv_eq: (mk_env_eq E g ls1_tl ls2_tl) => [[[Eeq_tl geq_tl] cseq_tl] lrseq_tl].
    case Henv_ult: (mk_env_ult Eeq_tl geq_tl ls1_tl ls2_tl) => [[[Eult_tl gult_tl] csult_tl] lrsult_tl].
    case=> <- _ _ _.
    move: (IH _ _ _ _ _ _ _ _ Henv_ult) => Hpre_ult.
    move: (mk_env_eq_preserve Henv_eq) => Hpre_eq.
    move: (mk_env_eq_newer_gen Henv_eq) => tmp.
    move: (mk_env_ult_newer_gen Henv_ult) => tmp2.
    apply env_preserve_trans with Eeq_tl.
    exact: Hpre_eq.
    move: (env_preserve_le Hpre_ult tmp) => Hpre3.
    apply env_preserve_trans with Eult_tl. exact: Hpre3.
    apply env_preserve_le with gult_tl. exact: env_upd_eq_preserve.
    exact: (pos_leb_trans tmp tmp2).
Qed.


Lemma mk_env_ult_sat :
forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
  mk_env_ult E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  interp_cnf E' cs.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr /=. case=> <- _ <- _. done.
  - move=> w IH E g /tupleP [ls1_hd ls1_tl] /tupleP [ls2_hd ls2_tl] E' g' cs lr.
    rewrite /= !theadE !beheadCons.
    case Henv_eq: (mk_env_eq E g ls1_tl ls2_tl)  => [[[Eeq_tl geq_tl] cseq_tl] lrseq_tl].
    case Henv_ult: (mk_env_ult Eeq_tl geq_tl ls1_tl ls2_tl) => [[[Eult_tl gult_tl] csult_tl] lrsult_tl].
    case. move=> <- _ <- Holr.
    move=> Hnew_g_tt /andP [Hnew_g_ls1hd Hnew_g_ls1tl] /andP [Hnew_g_ls2hd Hnew_g_ls2tl].
    rewrite !interp_cnf_append.
    move: (mk_env_eq_newer_gen Henv_eq) => Hng_eq.
    move: (mk_env_ult_newer_gen Henv_ult) => Hng_ult.
    move: (mk_env_eq_sat Henv_eq Hnew_g_ls1tl Hnew_g_ls2tl) => Hicnf_eq_eq.
    move: (mk_env_eq_newer_cnf Henv_eq Hnew_g_ls1tl Hnew_g_ls2tl) => Hncnf_eq_eq.
    move: (newer_than_cnf_le_newer Hncnf_eq_eq Hng_ult) => Hncnf_ult_eq.
    remember (interp_lit Eult_tl lrsult_tl
            || interp_lit Eult_tl lrseq_tl && ~~ interp_lit Eult_tl ls1_hd &&
               interp_lit Eult_tl ls2_hd) as val.
    move: (interp_cnf_env_upd_newer Eult_tl val Hncnf_ult_eq) => -> .
    move: (mk_env_eq_preserve Henv_eq) => Hpre_eq.
    move: (mk_env_ult_preserve Henv_ult) => Hpre_ult.
    move: (env_preserve_cnf Hpre_ult Hncnf_eq_eq) => -> . rewrite Hicnf_eq_eq andTb.
    move: (newer_than_lit_le_newer Hnew_g_tt Hng_eq) => Hnew_geq_tt.
    move: (newer_than_lits_le_newer Hnew_g_ls1tl Hng_eq) => Hnew_geq_ls1tl.
    move: (newer_than_lits_le_newer Hnew_g_ls2tl Hng_eq) => Hnew_geq_ls2tl.
    move: (IH _ _ _ _ _ _ _ _ Henv_ult Hnew_geq_tt Hnew_geq_ls1tl Hnew_geq_ls2tl) => Hicnf_ult_ult.
    move: (mk_env_ult_newer_cnf Henv_ult Hnew_geq_tt Hnew_geq_ls1tl Hnew_geq_ls2tl) => Hncnf_ult_ult.
    move: (interp_cnf_env_upd_newer Eult_tl val Hncnf_ult_ult) => ->.
    rewrite Hicnf_ult_ult andTb.
    rewrite /= !interp_lit_neg_lit. rewrite !env_upd_eq.
    symmetry in Heqval.
    move: (mk_env_eq_newer_res Henv_eq) => Hnres_eq.
    move: (mk_env_ult_newer_res Henv_ult Hnew_geq_tt) => Hnres_ult.
    move: (interp_lit_env_upd_newer Eult_tl val Hnres_ult) => ->.
    move: (newer_than_lit_le_newer Hnres_eq Hng_ult) => Hnres_eq2.
    move: (interp_lit_env_upd_newer Eult_tl val Hnres_eq2) => ->.
    move: (pos_leb_trans Hng_eq Hng_ult) => Hng_gult.
    move: (newer_than_lit_le_newer Hnew_g_ls1hd Hng_gult) => Hnew_ult_ls1hd.
    move: (interp_lit_env_upd_newer Eult_tl val Hnew_ult_ls1hd) => ->.
    move: (newer_than_lit_le_newer Hnew_g_ls2hd Hng_gult) => Hnew_ult_ls2hd.
    move: (interp_lit_env_upd_newer Eult_tl val Hnew_ult_ls2hd) => ->.
    by case Hval: val;
      case Hls1hd: (interp_lit Eult_tl ls1_hd);
      case Hls2hd: (interp_lit Eult_tl ls2_hd);
      case Heq: (interp_lit Eult_tl lrseq_tl);
      case Hult: (interp_lit Eult_tl lrsult_tl);
    rewrite Hval Hls1hd Hls2hd Heq Hult in Heqval.
Qed.
