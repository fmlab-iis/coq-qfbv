
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNFSimple BBCommon BBEq.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ===== bit_blast_ult ===== *)

(*Parameter bit_blast_ult : forall w : nat, generator -> w.-tuple literal -> w.-tuple literal -> generator * cnf * literal.*)
(* https://www.wolframalpha.com/input/?i=r+%3C-%3E+((~a+%26%26+b)+%7C%7C+(+((a+%26%26+b)+%7C%7C+(~a+%26%26+~b))+%26%26+l))+CNF *)

Fixpoint bit_blast_ult_rev' w (g : generator) : w.-tuple literal -> w.-tuple literal -> generator * cnf * literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(gult_tl, csult_tl, lrsult_tl) := bit_blast_ult_rev' g ls1_tl ls2_tl in
      let (g_r, r) := gen gult_tl in
      let cs := [ ::
            [:: neg_lit ls1_hd; ls2_hd; neg_lit r];
            [:: neg_lit ls1_hd; lrsult_tl; neg_lit r];
            [:: ls1_hd; neg_lit ls2_hd; r];
            [:: ls1_hd; neg_lit lrsult_tl; r];
            [:: neg_lit ls2_hd; neg_lit lrsult_tl; r];
            [:: ls2_hd; lrsult_tl; neg_lit r]
          ] in
      (g_r, csult_tl ++ cs, r)
  else
    fun _ _ =>
      (g, [::], lit_ff).



Definition bit_blast_ult w (g : generator) (ls1 ls2: w.-tuple literal): generator * cnf * literal :=
  let ls1_rev := rev_tuple ls1 in
  let ls2_rev := rev_tuple ls2 in
  @bit_blast_ult_rev' w g ls1_rev ls2_rev.


Fixpoint mk_env_ult_rev' w E (g : generator) : w.-tuple literal -> w.-tuple literal -> env * generator * cnf * literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(Eult_tl, gult_tl, csult_tl, lrsult_tl) := mk_env_ult_rev' E g ls1_tl ls2_tl in
      let (g_r, r) := gen gult_tl in
      let E' := env_upd Eult_tl (var_of_lit r) (
                           (~~interp_lit Eult_tl ls1_hd && interp_lit Eult_tl ls2_hd) ||
                           (
                             (interp_lit Eult_tl ls1_hd == interp_lit Eult_tl ls2_hd) &&
                             interp_lit Eult_tl lrsult_tl
                           )
                         ) in
      let cs := [ ::
            [:: neg_lit ls1_hd; ls2_hd; neg_lit r];
            [:: neg_lit ls1_hd; lrsult_tl; neg_lit r];
            [:: ls1_hd; neg_lit ls2_hd; r];
            [:: ls1_hd; neg_lit lrsult_tl; r];
            [:: neg_lit ls2_hd; neg_lit lrsult_tl; r];
            [:: ls2_hd; lrsult_tl; neg_lit r]
          ] in
      (E', g_r, csult_tl ++ cs, r)
  else
    fun _ _ =>
      (E, g, [::], lit_ff).

Definition mk_env_ult w E (g : generator) (ls1 ls2: w.-tuple literal): env * generator * cnf * literal :=
  let ls1_rev := rev_tuple ls1 in
  let ls2_rev := rev_tuple ls2 in
  @mk_env_ult_rev' w E g ls1_rev ls2_rev.

Lemma bit_blast_ult_rev'_correct :
  forall w g (bs1 bs2 : BITS w) E g' ls1 ls2 cs lr,
    bit_blast_ult_rev' g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (ltB_rev' bs1 bs2).
Proof.
  elim.
  - move=> g bs1 bs2 E g' ls1 ls2 cs lr. rewrite tuple0 (lock interp_cnf) /=.
    case=> _ _ <- _ _ . rewrite -lock. exact: add_prelude_enc_bit_ff.
  - move=> w IH g.
    move=> /tupleP [bs1_hd bs1_tl] /tupleP [bs2_hd bs2_tl] E g'.
    move=> /tupleP [ls1_hd ls1_tl] /tupleP [ls2_hd ls2_tl] cs lr.
    rewrite /bit_blast_ult_rev' -/bit_blast_ult_rev'. rewrite (lock interp_cnf).
    rewrite /splitlsb /=. repeat rewrite beheadCons theadCons. rewrite /=.
    rewrite -lock.
    case Hult: (bit_blast_ult_rev' g ls1_tl ls2_tl) =>
    [[gult_tl csult_tl] lrsult_tl].
    case=> Hog Hocs Holr. move=> /andP [Hels1_hd Hels1_tl] /andP [Hels2_hd Hels2_tl].     move=> Hcnf.
    move: (IH g bs1_tl bs2_tl E gult_tl ls1_tl ls2_tl csult_tl lrsult_tl Hult) => HIH.
    rewrite -Hocs in Hcnf.
    rewrite add_prelude_append in Hcnf. move/andP :Hcnf => [Hprelude_ult Hcnf].
    rewrite /add_prelude in Hcnf. repeat rewrite interp_cnf_cons interp_cnf_append in Hcnf. repeat rewrite interp_cnf_cons in Hcnf. repeat rewrite interp_clause_cons in Hcnf.
    repeat rewrite interp_lit_neg_lit in Hcnf. rewrite /= in Hcnf.
    split_andb.
    move: (HIH Hels1_tl Hels2_tl Hprelude_ult) => Heult.
    rewrite -Holr => {Holr}.
    move=> {H H6 Hocs Hult IH HIH Hprelude_ult}.
    rewrite /enc_bit in Hels1_hd Hels2_hd Heult.
    case Hbs1_hd :(bs1_hd); case Hbs2_hd: (bs2_hd); case Hceq: (bs1_hd == bs2_hd);
      case Hclt: (ltB_rev' bs1_tl bs2_tl); rewrite //=.
    all: rewrite Hbs1_hd in Hels1_hd; rewrite Hbs2_hd in Hels2_hd; case Heg: (E gult_tl).
    all:rewrite /enc_bit /=; try by apply /eqP.
    all: try by inversion Heg.
    all: move/eqP: Hels1_hd => -> in H0 H1 H2 H3 H4 H5.
    all: move/eqP: Hels2_hd => -> in H0 H1 H2 H3 H4 H5.
    all: move/eqP: Heult => -> in H0 H1 H2 H3 H4 H5.
    all: rewrite Heg Hclt /= in H0 H1 H2 H3 H4 H5.
    all: try done.
Qed.


Lemma bit_blast_ult_correct :
  forall w g (bs1 bs2 : BITS w) E g' ls1 ls2 cs lr,
    bit_blast_ult g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (ltB bs1 bs2).
Proof.
  move=> w g bs1 bs2 E g' ls1 ls2 cs lr.
  rewrite /bit_blast_ult.
  case Hult_rev': (bit_blast_ult_rev' g (rev_tuple ls1)  (rev_tuple ls2)) => [[gult_rev' csult_rev'] lrult_rev'].
  case=> _ <- <- Henc1 Henc2 Hicnf.
  apply enc_bits_rev in Henc1.
  apply enc_bits_rev in Henc2.
  move: (bit_blast_ult_rev'_correct Hult_rev' Henc1 Henc2 Hicnf) => Hlt_rev'.
  rewrite -ltB_rev_ltB.
  exact: Hlt_rev'.
Qed.

Lemma mk_env_ult_rev'_is_bit_blast_ult_rev' :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_ult_rev' E g ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_ult_rev' g ls1 ls2 = (g', cs, lrs).
Proof.
  elim.
  - rewrite /=; intros; dcase_hyps; subst; reflexivity.
  - intros_tuple; dcase_hyps; intros; subst.
      by rewrite (H _ _ _ _ _ _ _ _ H0).
Qed.


Lemma mk_env_ult_is_bit_blast_ult :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_ult E g ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_ult g ls1 ls2 = (g', cs, lrs).
Proof.
  move=> w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_ult /bit_blast_ult.
  move => Henv_ultrev'.
  exact: (mk_env_ult_rev'_is_bit_blast_ult_rev' Henv_ultrev').
Qed.

Lemma mk_env_ult_rev'_newer_gen :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_ult_rev' E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr. case=> _ <- _ _. exact: Pos.leb_refl.
  - move=> w IH E g. case/tupleP=> [ls1_hd ls1_tl]. case/tupleP=> [ls2_hd ls2_tl].
    move=> E' g' cs lr.  rewrite /= !theadE !beheadCons.
    case Henv_ult_rev': (mk_env_ult_rev' E g ls1_tl ls2_tl) => [[[Eult_tl gult_tl] csult_tl] lrsult_tl].
    case => _ <- _ _.
    move: (IH _ _ _ _ _ _ _ _ Henv_ult_rev') => Hng_ult_rev'.
    apply: (pos_leb_trans Hng_ult_rev' _ ).
    exact: (pos_leb_add_diag_r gult_tl 1).
Qed.

Lemma mk_env_ult_newer_gen :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_ult E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  move=> W E g ls1 ls2 E' g' cs lr.
  rewrite /mk_env_ult => Henv_ult_rev'.
  exact: (mk_env_ult_rev'_newer_gen Henv_ult_rev').
Qed.

Lemma mk_env_ult_rev'_newer_res :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_ult_rev' E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g' lr.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr. case=> _ <- _ <-. done.
  - move=> w IH E g /tupleP [ls1_hd ls1_tl] /tupleP [ls2_hd ls2_tl] E' g' cs lr.
    rewrite /= !theadE !beheadCons.
    case Henv_ult_rev': (mk_env_ult_rev' E g ls1_tl ls2_tl) => [[[Eult_tl gult_tl] csult_tl] lrsult_tl].
    case. move=> _ <- _ <-. move=> Hnew_g_lit_tt.
    move: (IH _ _ _ _ _ _ _ _ Henv_ult_rev').
    move=> H. move: (H Hnew_g_lit_tt) => {H}. move=> Hnew_gult_lrsult.
    rewrite /newer_than_lit /newer_than_var /=.
    exact: (pos_ltb_add_diag_r gult_tl 1).
Qed.

Lemma mk_env_ult_newer_res :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_ult E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g' lr.
Proof.
  move=> W E g ls1 ls2 E' g' cs lr.
  rewrite /mk_env_ult => Henv_ult_rev' Hngtt.
  exact: (mk_env_ult_rev'_newer_res Henv_ult_rev' Hngtt).
Qed.

Lemma mk_env_ult_rev'_newer_cnf :
forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
  mk_env_ult_rev' E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr /=. case=> _ _ <- _. done.
  - move=> w IH E g /tupleP [ls1_hd ls1_tl] /tupleP [ls2_hd ls2_tl] E' g' cs lr.
    rewrite /= !theadE !beheadCons.
    case Henv_ult_rev': (mk_env_ult_rev' E g ls1_tl ls2_tl) => [[[Eult_tl gult_tl] csult_tl] lrsult_tl].
    case=> _ <- <- _. move=> Hnew_gtt /andP [Hnew_g_ls1hd Hnew_g_ls1_tl] /andP [Hnew_g_ls2hd Hnew_g_ls2_tl].
    rewrite !newer_than_cnf_append.
    move: (pos_leb_add_diag_r g 1) => H_ggp1.
    move: (mk_env_ult_rev'_newer_gen Henv_ult_rev') => tmp.
    move: (pos_leb_trans tmp (pos_leb_add_diag_r gult_tl 1)) => {tmp} tmp.
    move: (IH _ _ _ _ _ _ _ _ Henv_ult_rev').
    move: (newer_than_lits_le_newer Hnew_g_ls1_tl tmp) => H2 .
    move: (newer_than_lits_le_newer Hnew_g_ls2_tl tmp) => H3 .
    move => H4. move : (H4 Hnew_gtt Hnew_g_ls1_tl Hnew_g_ls2_tl) => {H2 H3} H.
    rewrite (newer_than_cnf_le_newer H (pos_leb_add_diag_r gult_tl 1)) => {H}.
    rewrite andTb. rewrite /=.
    rewrite !newer_than_lit_neg.
    rewrite (newer_than_lit_le_newer Hnew_g_ls1hd tmp) /=.
    rewrite (newer_than_lit_le_newer Hnew_g_ls2hd tmp) /= andbT.
    move: (mk_env_ult_rev'_newer_res Henv_ult_rev' Hnew_gtt) => H.
    move: (newer_than_lit_le_newer H (pos_leb_add_diag_r gult_tl 1)) => ->.
    rewrite /newer_than_lit /newer_than_var /=.
    by rewrite (pos_ltb_add_diag_r gult_tl 1).
Qed.

Lemma mk_env_ult_newer_cnf :
forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
  mk_env_ult E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  move=> W E g ls1 ls2 E' g' cs lr.
  rewrite /mk_env_ult => Henv_ult_rev' Hngtt Hngls1 Hngls2.
  apply newer_than_lits_rev in Hngls1.
  apply newer_than_lits_rev in Hngls2.
  exact: (mk_env_ult_rev'_newer_cnf Henv_ult_rev' Hngtt Hngls1 Hngls2).
Qed.

Lemma mk_env_ult_rev'_preserve :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_ult_rev' E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr /=. case=> <- _ _ _. done.
  - move=> w IH E g /tupleP [ls1_hd ls1_tl] /tupleP [ls2_hd ls2_tl] E' g' cs lr.
    rewrite /= !theadE !beheadCons.
    case Henv_ult_rev': (mk_env_ult_rev' E g  ls1_tl ls2_tl) => [[[Eult_tl gult_tl] csult_tl] lrsult_tl].
    case=> <- _ _ _.
    move: (IH _ _ _ _ _ _ _ _ Henv_ult_rev') => Hpre_ult_rev'.
    move: (mk_env_ult_rev'_newer_gen Henv_ult_rev') => tmp.
    apply env_preserve_trans with Eult_tl. exact: Hpre_ult_rev'.
    apply env_preserve_le with gult_tl. exact: env_upd_eq_preserve.
    exact: tmp.
Qed.

Lemma mk_env_ult_preserve :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_ult E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  move => w E g ls1 ls2 E' g' cs lr.
  rewrite /mk_env_ult  => Henv_ult_rev'.
  exact: (mk_env_ult_rev'_preserve Henv_ult_rev').
Qed.

Lemma mk_env_ult_rev'_sat :
forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
  mk_env_ult_rev' E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  interp_cnf E' cs.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr /=. case=> <- _ <- _. done.
  - move=> w IH E g /tupleP [ls1_hd ls1_tl] /tupleP [ls2_hd ls2_tl] E' g' cs lr.
    rewrite /= !theadE !beheadCons.
    case Henv_ult_rev': (mk_env_ult_rev' E g ls1_tl ls2_tl) => [[[Eult_tl gult_tl] csult_tl] lrsult_tl].
    case. move=> <- _ <- Holr.
    move=> Hnew_g_tt /andP [Hnew_g_ls1hd Hnew_g_ls1tl] /andP [Hnew_g_ls2hd Hnew_g_ls2tl].
    rewrite !interp_cnf_append.
    move: (mk_env_ult_rev'_newer_gen Henv_ult_rev') => Hng_ult_rev'.
    remember (~~ interp_lit Eult_tl ls1_hd && interp_lit Eult_tl ls2_hd
        || (interp_lit Eult_tl ls1_hd == interp_lit Eult_tl ls2_hd) &&
           interp_lit Eult_tl lrsult_tl)  as val.
    move: (IH _ _ _ _ _ _ _ _ Henv_ult_rev' Hnew_g_tt Hnew_g_ls1tl Hnew_g_ls2tl) => Hicnf_ult_rev'.
    move: (mk_env_ult_rev'_newer_cnf Henv_ult_rev' Hnew_g_tt Hnew_g_ls1tl Hnew_g_ls2tl) => Hncnf_ult_rev'.
    move: (interp_cnf_env_upd_newer Eult_tl val Hncnf_ult_rev') => ->.
    rewrite Hicnf_ult_rev' andTb.
    rewrite /= !interp_lit_neg_lit. rewrite !env_upd_eq.
    symmetry in Heqval.
    move: (mk_env_ult_rev'_newer_res Henv_ult_rev' Hnew_g_tt) => Hnres_ult_rev'.
    move: (interp_lit_env_upd_newer Eult_tl val Hnres_ult_rev') => ->.
    move: (newer_than_lit_le_newer Hnew_g_ls1hd Hng_ult_rev') => Hnew_ult_ls1hd.
    move: (interp_lit_env_upd_newer Eult_tl val Hnew_ult_ls1hd) => ->.
    move: (newer_than_lit_le_newer Hnew_g_ls2hd Hng_ult_rev') => Hnew_ult_ls2hd.
    move: (interp_lit_env_upd_newer Eult_tl val Hnew_ult_ls2hd) => ->.
    by case Hval: val;
      case Hls1hd: (interp_lit Eult_tl ls1_hd);
      case Hls2hd: (interp_lit Eult_tl ls2_hd);
      case Hult: (interp_lit Eult_tl lrsult_tl);
    rewrite Hval Hls1hd Hls2hd Hult in Heqval.
Qed.

Lemma mk_env_ult_sat :
forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
  mk_env_ult E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  interp_cnf E' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr.
  rewrite /mk_env_ult => Henv_ult_rev' Hngtt Hngls1 Hngls2.
  apply newer_than_lits_rev in Hngls1.
  apply newer_than_lits_rev in Hngls2.
  exact: (mk_env_ult_rev'_sat Henv_ult_rev' Hngtt Hngls1 Hngls2).
Qed.
