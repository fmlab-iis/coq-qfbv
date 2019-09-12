
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNFSimple BBCommonSimple BBNotSimple BBConstSimple BBAddSimple.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_neg ===== *)

Definition bit_blast_neg w g ls : generator * cnf * w.-tuple literal :=
  let '(g_not, cs_not, lrs_not) := bit_blast_not g ls in
  let '(g_con, cs_con, lrs_con) := bit_blast_const g_not (#1) in
  let '(g_add, cs_add, lrs_add) := bit_blast_add g_con lrs_not lrs_con in
  (g_add, cs_not++cs_con++cs_add, lrs_add).

Definition mk_env_neg  w E g ls : env * generator * cnf * w.-tuple literal :=
  let '(E_not, g_not, cs_not, lrs_not) := mk_env_not E g ls in
  let '(E_con, g_con, cs_con, lrs_con) := mk_env_const E_not g_not (# 1) in
  let '(E_add, g_add, cs_add, lrs_add) := mk_env_add E_con g_con lrs_not lrs_con in
  (E_add, g_add, cs_not++cs_con++cs_add, lrs_add).

Lemma bit_blast_neg_correct :
  forall w g (bs : BITS w) E ls g' cs lrs,
    bit_blast_neg g ls = (g', cs, lrs) ->
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (negB bs).
Proof.
  move => w g bs E ls g' cs lrs.
  rewrite /bit_blast_neg (lock bit_blast_const) (lock interp_cnf)/= -!lock.
  case Hnot : (bit_blast_not g ls) => [[g_not cs_not] lrs_not].
  case Hcons : (bit_blast_const g_not # (1)) => [[g_con cs_con] lrs_con].
  case Hadd : (bit_blast_add g_con lrs_not lrs_con) => [[g_add cs_add] lrs_add].
  move => [] _ <- <-.
  rewrite !add_prelude_append.
  move => Hencbs Hcnf.
  move/andP : Hcnf => [Hcnfnot /andP [Hcnfcon Hcnfadd]].
  move : (bit_blast_not_correct  Hnot Hencbs Hcnfnot) => Henclrs_not.
  move : (bit_blast_const_correct Hcons Hcnfcon) => Henclrs_con.
  move : (addB1 (invB bs))=> Hencbr. rewrite /negB.
  exact : (bit_blast_add_correct Hadd Henclrs_not Henclrs_con Hencbr Hcnfadd ).
Qed.

Lemma mk_env_neg_is_bit_blast_neg :
  forall w E g (ls : w.-tuple literal) E' g' cs lrs,
    mk_env_neg E g ls = (E', g', cs, lrs) ->
    bit_blast_neg g ls = (g', cs, lrs).
Proof.
  move => w E g ls E' g' cs lrs.
  rewrite /mk_env_neg /bit_blast_neg.
  case Hmknot : (mk_env_not E g ls) => [[[E_not g_not] cs_not] lrs_not].
  rewrite (mk_env_not_is_bit_blast_not Hmknot).
  case Hmkcon : (mk_env_const E_not g_not # (1)) => [[[E_con g_con] cs_con] lrs_con].
  rewrite (mk_env_const_is_bit_blast_const Hmkcon).
  case Hmkadd : (mk_env_add E_con g_con lrs_not lrs_con) => [[[E_add g_add] cs_add] lrs_add].
  rewrite (mk_env_add_is_bit_blast_add Hmkadd).
  by move => [] _ <- <- <-.
Qed.

Lemma mk_env_neg_sat :
  forall w E g (ls : w.-tuple literal) E' g' cs lrs,
    mk_env_neg E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_ff ->
    newer_than_lits g ls ->
    interp_cnf E' cs.
Proof.
  rewrite /mk_env_neg => w E g ls E' g' cs lrs.
  case Hmknot : (mk_env_not E g ls) => [[[E_not g_not] cs_not] lrs_not].
  case Hmkcon : (mk_env_const E_not g_not # (1)) => [[[E_con g_con] cs_con] lrs_con].
  case Hmkadd : (mk_env_add E_con g_con lrs_not lrs_con) => [[[E_add g_add] cs_add] lrs_add].
  move => [] <-  _ <- _ Hnewtt Hnewls.
  rewrite !interp_cnf_append.
  move : (mk_env_not_sat Hmknot Hnewls) .
  move : (mk_env_const_sat Hmkcon) => Hcnfcon.
  move : (mk_env_not_newer_gen Hmknot)=> Hggnot.
  move : (mk_env_const_newer_gen Hmkcon) => Hgnotgcon.
  move : (mk_env_not_newer_res Hmknot Hnewls) => Hnotres.
  move : (mk_env_const_newer_res Hmkcon (newer_than_lit_le_newer Hnewtt Hggnot)) => Hconres.
  move : (mk_env_add_sat Hmkadd (newer_than_lit_le_newer Hnewtt (pos_leb_trans Hggnot Hgnotgcon)) (newer_than_lits_le_newer Hnotres Hgnotgcon) Hconres) => Hcnfadd.
  move : (mk_env_not_newer_cnf Hmknot Hnewls).
  rewrite /mk_env_const in Hmkcon.
  move : (mk_env_not_preserve Hmknot).
  move : Hmkcon => [] -> -> <- _.
  move => HEEcon Hnewcnfnot Hcnfnot.
  move : (mk_env_add_newer_gen Hmkadd) => Hgcongadd.
  move : (mk_env_add_preserve Hmkadd) => HEconEadd.
  rewrite (env_preserve_cnf HEconEadd Hnewcnfnot).
  by rewrite /= Hcnfnot Hcnfadd /=.
Qed.

Lemma mk_env_neg_preserve :
  forall w E g (ls: w.-tuple literal) E' g' cs lrs,
    mk_env_neg E g ls = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move => w E g ls E' g' cs lrs.
  rewrite /mk_env_neg.
  case Hmknot : (mk_env_not E g ls) => [[[E_not g_not] cs_not] lrs_not].
  case Hmkcon : (mk_env_const E_not g_not # (1)) => [[[E_con g_con] cs_con] lrs_con].
  case Hmkadd : (mk_env_add E_con g_con lrs_not lrs_con) => [[[E_add g_add] cs_add] lrs_add].
  move => [] <- _ _ _.
  move : (mk_env_not_preserve Hmknot) => HEEnot.
  move : (mk_env_const_preserve Hmkcon) => HEnotEcon.
  move : (mk_env_not_newer_gen Hmknot) => Hggnot.
  move : (mk_env_const_newer_gen Hmkcon) => Hgnotgcon.
  move : (mk_env_add_newer_gen Hmkadd) => Hgcongadd.
  move : (mk_env_add_preserve Hmkadd) => HEconEadd.
  move : (env_preserve_le HEnotEcon Hggnot) => HEnotEcong.
  move : (env_preserve_le HEconEadd (pos_leb_trans Hggnot Hgnotgcon)) => HEconEaddg.
  exact : (env_preserve_trans HEEnot (env_preserve_trans HEnotEcong HEconEaddg)).
Qed.

Lemma mk_env_neg_newer_gen :
  forall w E g (ls: w.-tuple literal) E' g' cs lrs,
    mk_env_neg E g ls = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move =>  w E g ls E' g' cs lrs.
  rewrite /mk_env_neg.
  case Hmknot : (mk_env_not E g ls) => [[[E_not g_not] cs_not] lrs_not].
  case Hmkcon : (mk_env_const E_not g_not # (1)) => [[[E_con g_con] cs_con] lrs_con].
  case Hmkadd : (mk_env_add E_con g_con lrs_not lrs_con) => [[[E_add g_add] cs_add] lrs_add].
  move => [] _ <- _ _.
  move : (mk_env_not_newer_gen Hmknot) => Hggnot.
  move : (mk_env_const_newer_gen Hmkcon) => Hgnotgcon.
  move : (mk_env_add_newer_gen Hmkadd) => Hgcongadd.
  exact : (pos_leb_trans Hggnot (pos_leb_trans Hgnotgcon Hgcongadd)).
Qed.

Lemma mk_env_neg_newer_res :
  forall w E g (ls: w.-tuple literal) E' g' cs lrs,
    mk_env_neg E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    newer_than_lits g' lrs.
Proof.
    move =>  w E g ls E' g' cs lrs.
  rewrite /mk_env_neg.
  case Hmknot : (mk_env_not E g ls) => [[[E_not g_not] cs_not] lrs_not].
  case Hmkcon : (mk_env_const E_not g_not # (1)) => [[[E_con g_con] cs_con] lrs_con].
  case Hmkadd : (mk_env_add E_con g_con lrs_not lrs_con) => [[[E_add g_add] cs_add] lrs_add].
  move => [] _ <- _ <- Htt Hgls.
  exact : (mk_env_add_newer_res Hmkadd) => Hgaddlrsadd.
Qed.

Lemma mk_env_neg_newer_cnf :
  forall w E g (ls: w.-tuple literal) E' g' cs lrs,
    mk_env_neg E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    newer_than_cnf g' cs.
Proof.
  move =>  w E g ls E' g' cs lrs.
  rewrite /mk_env_neg.
  case Hmknot : (mk_env_not E g ls) => [[[E_not g_not] cs_not] lrs_not].
  case Hmkcon : (mk_env_const E_not g_not # (1)) => [[[E_con g_con] cs_con] lrs_con].
  case Hmkadd : (mk_env_add E_con g_con lrs_not lrs_con) => [[[E_add g_add] cs_add] lrs_add].
  move => [] _ <- <- _ Htt Hgls.
  rewrite !newer_than_cnf_append.
  move : (mk_env_not_newer_gen Hmknot) => Hggnot.
  move : (mk_env_const_newer_gen Hmkcon) => Hgnotgcon.
  move : (mk_env_add_newer_gen Hmkadd) => Hgcongadd.
  move : (mk_env_not_newer_res Hmknot Hgls) => Hgnotresnot.
  move : (mk_env_const_newer_res Hmkcon (newer_than_lit_le_newer Htt Hggnot)) => Hgconlrscon.
  rewrite (mk_env_add_newer_cnf Hmkadd (newer_than_lit_le_newer Htt (pos_leb_trans Hggnot Hgnotgcon)) (newer_than_lits_le_newer Hgnotresnot Hgnotgcon) Hgconlrscon) /=.
  move : (mk_env_not_newer_cnf Hmknot Hgls) => Hcnfnot.
  rewrite (newer_than_cnf_le_newer Hcnfnot (pos_leb_trans Hgnotgcon Hgcongadd)) /=.
  rewrite /mk_env_const in Hmkcon.
  by case :Hmkcon => _ _ <- _ /=.
Qed.
