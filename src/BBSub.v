
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon BBNot BBAdd BBNeg.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_sbb ===== *)

Definition bit_blast_sbb w g l_bin ls1 ls2 : generator * cnf * literal * w.-tuple literal :=
  let '(g_not, cs_not, lrs_not) := bit_blast_not g ls2 in
  let '(g_add, cs_add, l_bout, lrs_add) := bit_blast_full_adder g_not (neg_lit l_bin) ls1 lrs_not in
  (g_add, cs_not ++ cs_add, neg_lit l_bout, lrs_add).

Definition mk_env_sbb w E g l_bin ls1 ls2 : env * generator * cnf * literal * w.-tuple literal :=
  let '(E_not, g_not, cs_not, lrs_not) := mk_env_not E g ls2 in
  let '(E_add, g_add, cs_add, l_bout, lrs_add) := mk_env_full_adder E_not g_not (neg_lit l_bin) ls1 lrs_not in
  (E_add, g_add, cs_not ++ cs_add, neg_lit l_bout, lrs_add).

Lemma bit_blast_sbb_correct :
  forall w g bin (bs1 bs2 : BITS w) E l_bin ls1 ls2 bout brs g' cs l_bout lrs,
    bit_blast_sbb g l_bin ls1 ls2 = (g', cs, l_bout, lrs) ->
    enc_bit E l_bin bin ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    sbbB bin bs1 bs2 = (bout, brs) ->
    enc_bit E l_bout bout /\ enc_bits E lrs brs.
Proof.
  move=> w g bin bs1 bs2 E l_bin ls1 ls2 bout brs g' cs l_bout lrs.
  rewrite /bit_blast_sbb.
  dcase (bit_blast_not g ls2) => [[[g_not cs_not] lrs_not] Hbb_not].
  dcase (bit_blast_full_adder g_not (neg_lit l_bin) ls1 lrs_not) =>
  [[[[g_add cs_add] l_bout_add] lrs_add] Hbb_add]. case=> _ <- <- <-.
  move=> Hencb Henc1 Henc2 Hcs. Local Transparent sbbB. rewrite /sbbB.
  Local Opaque sbbB. case => Hbout Hbrs.
  rewrite add_prelude_append in Hcs. move/andP: Hcs => [Hcs_not Hcs_add].
  move: (bit_blast_not_correct Hbb_not Henc2 Hcs_not) => Henc_inv2.
  rewrite enc_bit_not in Hencb.
  have HadcB: adcB (~~ bin) bs1 (invB bs2) = (~~ bout, brs)
    by rewrite -(negbRL Hbout) -Hbrs; apply: injective_projections.
  move: (bit_blast_full_adder_correct Hbb_add Henc1 Henc_inv2 Hencb Hcs_add HadcB).
  move=> {Hbrs Hbout} [Hbrs Hbout]. rewrite Hbrs.
  rewrite -(Bool.negb_involutive bout) -enc_bit_not Hbout. done.
Qed.

Lemma mk_env_sbb_is_bit_blast_sbb :
  forall w E g l_bin (ls1 ls2 : w.-tuple literal) E' g' cs l_bout lrs,
    mk_env_sbb E g l_bin ls1 ls2 = (E', g', cs, l_bout, lrs) ->
    bit_blast_sbb g l_bin ls1 ls2 = (g', cs, l_bout, lrs).
Proof.
  move=> w E g l_bin ls1 ls2 E' g' cs l_bout lrs. rewrite /mk_env_sbb /bit_blast_sbb.
  dcase (mk_env_not E g ls2) => [[[[E_not g_not] cs_not] lrs_not] Henv_not].
  dcase (mk_env_full_adder E_not g_not (neg_lit l_bin) ls1 lrs_not) =>
  [[[[[E_add g_add] cs_add] l_bout_add] lrs_add] Henv_add].
  rewrite (mk_env_not_is_bit_blast_not Henv_not).
  rewrite (mk_env_full_adder_is_bit_blast_full_adder Henv_add).
  case=> _ <- <- <- <-. reflexivity.
Qed.

Lemma mk_env_sbb_newer_gen :
  forall w E g l_bin (ls1 ls2 : w.-tuple literal) E' g' cs l_bout lrs,
    mk_env_sbb E g l_bin ls1 ls2 = (E', g', cs, l_bout, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> w E g l_bin ls1 ls2 E' g' cs l_bout lrs. rewrite /mk_env_sbb.
  dcase (mk_env_not E g ls2) => [[[[E_not g_not] cs_not] lrs_not] Henv_not].
  dcase (mk_env_full_adder E_not g_not (neg_lit l_bin) ls1 lrs_not) =>
  [[[[[E_add g_add] cs_add] l_bout_add] lrs_add] Henv_add].
  case=> _ <- _ _ _. apply: (pos_leb_trans (mk_env_not_newer_gen Henv_not)).
  exact: (mk_env_full_adder_newer_gen Henv_add).
Qed.

Lemma mk_env_sbb_newer_res :
  forall w E g l_bin (ls1 ls2 : w.-tuple literal) E' g' cs l_bout lrs,
    mk_env_sbb E g l_bin ls1 ls2 = (E', g', cs, l_bout, lrs) ->
    newer_than_lits g' lrs.
Proof.
  move=> w E g l_bin ls1 ls2 E' g' cs l_bout lrs. rewrite /mk_env_sbb.
  dcase (mk_env_not E g ls2) => [[[[E_not g_not] cs_not] lrs_not] Henv_not].
  dcase (mk_env_full_adder E_not g_not (neg_lit l_bin) ls1 lrs_not) =>
  [[[[[E_add g_add] cs_add] l_bout_add] lrs_add] Henv_add].
  case=> _ <- _ _ <-. exact: (mk_env_full_adder_newer_res Henv_add).
Qed.

Lemma mk_env_sbb_newer_cnf :
  forall w E g l_bin (ls1 ls2 : w.-tuple literal) E' g' cs l_bout lrs,
    mk_env_sbb E g l_bin ls1 ls2 = (E', g', cs, l_bout, lrs) ->
    newer_than_lit g l_bin ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  move=> w E g l_bin ls1 ls2 E' g' cs l_bout lrs. rewrite /mk_env_sbb.
  dcase (mk_env_not E g ls2) => [[[[E_not g_not] cs_not] lrs_not] Henv_not].
  dcase (mk_env_full_adder E_not g_not (neg_lit l_bin) ls1 lrs_not) =>
  [[[[[E_add g_add] cs_add] l_bout_add] lrs_add] Henv_add].
  case=> _ <- <- _ _. move=> Hnew_gbin Hnew_gls1 Hnew_gls2.
  rewrite newer_than_cnf_append.
  move: (mk_env_not_newer_cnf Henv_not Hnew_gls2) => Hnew_g_notcs_not.
  rewrite (newer_than_cnf_le_newer Hnew_g_notcs_not
                                   (mk_env_full_adder_newer_gen Henv_add)) andTb.
  move: (mk_env_not_newer_gen Henv_not) => Hgg_not.
  move: (mk_env_full_adder_newer_gen Henv_add) => Hg_notg_add.
  move: (newer_than_lits_le_newer Hnew_gls1 Hgg_not) => Hnew_g_notls1.
  move: (newer_than_lits_le_newer Hnew_gls2 Hgg_not) => Hnew_g_notls2.
  move: (newer_than_lit_le_newer Hnew_gbin Hgg_not) => Hnew_g_notbin.
  rewrite -newer_than_lit_neg in Hnew_g_notbin.
  exact: (mk_env_full_adder_newer_cnf Henv_add Hnew_g_notbin Hnew_g_notls1
                                      (mk_env_not_newer_res Henv_not Hnew_gls2)).
Qed.

Lemma mk_env_sbb_preserve :
  forall w E g l_bin (ls1 ls2 : w.-tuple literal) E' g' cs l_bout lrs,
    mk_env_sbb E g l_bin ls1 ls2 = (E', g', cs, l_bout, lrs) ->
    env_preserve E E' g.
Proof.
  move=> w E g l_bin ls1 ls2 E' g' cs l_bout lrs. rewrite /mk_env_sbb.
  dcase (mk_env_not E g ls2) => [[[[E_not g_not] cs_not] lrs_not] Henv_not].
  dcase (mk_env_full_adder E_not g_not (neg_lit l_bin) ls1 lrs_not) =>
  [[[[[E_add g_add] cs_add] l_bout_add] lrs_add] Henv_add].
  case=> <- _ _ _ _.
  move: (mk_env_not_preserve Henv_not) => HEEadd.
  move: (mk_env_full_adder_preserve Henv_add) => HEnotEaddgnot.
  move: (env_preserve_le HEnotEaddgnot (mk_env_not_newer_gen Henv_not)) => HEnotEaddg.
  exact: (env_preserve_trans HEEadd HEnotEaddg).
Qed.

Lemma mk_env_sbb_sat :
  forall w E g l_bin (ls1 ls2 : w.-tuple literal) E' g' cs l_bout lrs,
    mk_env_sbb E g l_bin ls1 ls2 = (E', g', cs, l_bout, lrs) ->
    newer_than_lit g l_bin ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move=> w E g l_bin ls1 ls2 E' g' cs l_bout lrs. rewrite /mk_env_sbb.
  dcase (mk_env_not E g ls2) => [[[[E_not g_not] cs_not] lrs_not] Henv_not].
  dcase (mk_env_full_adder E_not g_not (neg_lit l_bin) ls1 lrs_not) =>
  [[[[[E_add g_add] cs_add] l_bout_add] lrs_add] Henv_add].
  case=> <- _ <- _ _. move=> Hnew_gbin Hnew_gls1 Hnew_gls2.
  rewrite interp_cnf_append.
  move: (mk_env_not_sat Henv_not Hnew_gls2) => Hcs_Enotcsnot.
  move: (mk_env_full_adder_preserve Henv_add) => Hpre.
  rewrite (env_preserve_cnf Hpre (mk_env_not_newer_cnf Henv_not Hnew_gls2)).
  rewrite Hcs_Enotcsnot andTb.
  move: (mk_env_not_newer_gen Henv_not) => Hggnot.
  move: (newer_than_lits_le_newer Hnew_gls1 Hggnot) => Hnew_gnotls1.
  move: (mk_env_not_newer_res Henv_not Hnew_gls2) => Hnew_gnotlrsnot.
  move: (newer_than_lit_le_newer Hnew_gbin Hggnot) => Hnew_gnotbin.
  rewrite -newer_than_lit_neg in Hnew_gnotbin.
  exact: (mk_env_full_adder_sat Henv_add Hnew_gnotbin Hnew_gnotls1 Hnew_gnotlrsnot).
Qed.



(* ===== bit_blast_sub ===== *)

Definition bit_blast_sub w g ls1 ls2 : generator * cnf * w.-tuple literal :=
  let '(g_neg, cs_neg, lrs_neg) := bit_blast_neg g ls2 in
  let '(g_add, cs_add, lrs_add) := bit_blast_add g_neg ls1 lrs_neg in
  (g_add, cs_neg++cs_add, lrs_add).

Lemma bit_blast_sub_correct :
  forall w g (bs1 bs2 : BITS w) E ls1 ls2 g' cs lrs,
    bit_blast_sub g ls1 ls2 = (g', cs, lrs) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (subB bs1 bs2).
Proof.
  move=> n g bs1 bs2 E ls1 ls2 g' cs lrs.
  rewrite /bit_blast_sub.
  case Hneg : (bit_blast_neg g ls2) => [[g_neg cs_neg] lrs_neg].
  case Hadd : (bit_blast_add g_neg ls1 lrs_neg) => [[g_add cs_add] lrs_add].
  move => [] _ <- <- Henc1 Henc2.
  rewrite add_prelude_append. move/andP => [Hcnfneg Hcnfadd].
  move : (bit_blast_neg_correct Hneg Henc2 Hcnfneg) => Hencneg.
  move : (subB_equiv_addB_negB bs1 bs2) => Hencbr. symmetry in Hencbr.
  exact : (bit_blast_add_correct Hadd Henc1 Hencneg Hencbr Hcnfadd).
Qed.

Definition mk_env_sub w E (g: generator) ls1 ls2 : env * generator * cnf * w.-tuple literal :=
  let '(E_neg, g_neg, cs_neg, lrs_neg) := mk_env_neg E g ls2 in
  let '(E_add, g_add, cs_add, lrs_add) := mk_env_add E_neg g_neg ls1 lrs_neg in
  (E_add, g_add, cs_neg++cs_add, lrs_add).

Lemma mk_env_sub_is_bit_blast_sub :
  forall w E g  (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_sub E g ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_sub g ls1 ls2 = (g', cs, lrs).
Proof.
  move =>  w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_sub/bit_blast_sub.
  case Hmkneg : (mk_env_neg E g ls2) => [[[E_neg g_neg] cs_neg] lrs_neg].
  case Hmkadd : (mk_env_add E_neg g_neg ls1 lrs_neg) => [[[E_add g_add] cs_add] lrs_add].
  rewrite (mk_env_neg_is_bit_blast_neg Hmkneg).
  rewrite (mk_env_add_is_bit_blast_add Hmkadd).
  by case => _ <- <- <-.
Qed.

Lemma mk_env_sub_newer_gen :
  forall w E g  (ls1 ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_sub E g ls1 ls2 = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move =>  w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_sub.
  case Hmkneg : (mk_env_neg E g ls2) => [[[E_neg g_neg] cs_neg] lrs_neg].
  case Hmkadd : (mk_env_add E_neg g_neg ls1 lrs_neg) => [[[E_add g_add] cs_add] lrs_add].
  case => _ <- _ _.
  move : (mk_env_neg_newer_gen Hmkneg) => Hggneg.
  move : (mk_env_add_newer_gen Hmkadd) => Hgneggadd.
  exact : (pos_leb_trans Hggneg Hgneggadd).
Qed.

Lemma mk_env_sub_newer_res :
  forall  w E g  (ls1 ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_sub E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lits g' lrs.
Proof.
  move =>  w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_sub.
  case Hmkneg : (mk_env_neg E g ls2) => [[[E_neg g_neg] cs_neg] lrs_neg].
  case Hmkadd : (mk_env_add E_neg g_neg ls1 lrs_neg) => [[[E_add g_add] cs_add] lrs_add].
  case => _ <- _ <-.
  exact : (mk_env_add_newer_res Hmkadd).
Qed.

Lemma mk_env_sub_newer_cnf:
  forall  w E g  (ls1 ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_sub E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lit_ff ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  move =>  w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_sub.
  case Hmkneg : (mk_env_neg E g ls2) => [[[E_neg g_neg] cs_neg] lrs_neg].
  case Hmkadd : (mk_env_add E_neg g_neg ls1 lrs_neg) => [[[E_add g_add] cs_add] lrs_add].
  case => _ <- <- _ Htt Hgls1 Hgls2.
  rewrite newer_than_cnf_append.
  move : (mk_env_add_newer_gen Hmkadd) => Hgneggadd.
  move : (mk_env_neg_newer_gen Hmkneg) => Hggneg.
  move : (mk_env_neg_newer_res Hmkneg Htt Hgls2) => Hnegres.
  rewrite (mk_env_add_newer_cnf Hmkadd (newer_than_lit_le_newer Htt Hggneg) (newer_than_lits_le_newer Hgls1 Hggneg) Hnegres)/=.
  move : (mk_env_neg_newer_cnf Hmkneg Htt Hgls2) => Hnegcnf.
  rewrite (newer_than_cnf_le_newer Hnegcnf Hgneggadd).
  done.
Qed.

Lemma mk_env_sub_preserve :
  forall  w E g  (ls1 ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_sub E g ls1 ls2 = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move =>  w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_sub.
  case Hmkneg : (mk_env_neg E g ls2) => [[[E_neg g_neg] cs_neg] lrs_neg].
  case Hmkadd : (mk_env_add E_neg g_neg ls1 lrs_neg) => [[[E_add g_add] cs_add] lrs_add].
  case => <- _ _ _.
  move : (mk_env_neg_preserve Hmkneg) => HEEneg.
  move : (mk_env_add_preserve Hmkadd) => HEnegEadd.
  move : (mk_env_neg_newer_gen Hmkneg) => Hggneg.
  move : (mk_env_add_newer_gen Hmkadd) => Hgneggadd.
  exact : (env_preserve_trans HEEneg (env_preserve_le HEnegEadd Hggneg)).
Qed.

Lemma mk_env_sub_sat :
  forall  w E g  (ls1 ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_sub E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lit_ff -> newer_than_lits g ls1 ->  newer_than_lits g ls2 -> interp_cnf E' cs.
Proof.
  move =>  w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_sub.
  case Hmkneg : (mk_env_neg E g ls2) => [[[E_neg g_neg] cs_neg] lrs_neg].
  case Hmkadd : (mk_env_add E_neg g_neg ls1 lrs_neg) => [[[E_add g_add] cs_add] lrs_add].
  case => <- _ <- _ Htt Hgls1 Hgls2.
  rewrite interp_cnf_append.
  move : (mk_env_neg_newer_gen Hmkneg) => Hggneg.
  move : (mk_env_neg_newer_res Hmkneg Htt Hgls2) => Hnegres.
  rewrite (mk_env_add_sat Hmkadd (newer_than_lit_le_newer Htt Hggneg) (newer_than_lits_le_newer Hgls1 Hggneg) Hnegres).
  move : (mk_env_neg_sat Hmkneg Htt Hgls2)=> Hcnfneg.
  move : (mk_env_add_preserve Hmkadd) => HEnegEadd.
  move : (mk_env_neg_preserve Hmkneg) => HEEneg.
  move : (mk_env_neg_newer_cnf Hmkneg Htt Hgls2) => Hcsneg.
  rewrite (env_preserve_cnf HEnegEadd Hcsneg) Hcnfneg.
  done.
Qed.
