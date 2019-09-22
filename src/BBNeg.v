From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import Var QFBV CNF BBCommon BBNot BBConst BBAdd.
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ===== bit_blast_neg ===== *)

Definition bit_blast_neg g ls : generator * cnf * word :=
  let '(g_not, cs_not, lrs_not) := bit_blast_not g ls in
  let '(g_con, cs_con, lrs_con) := bit_blast_const g_not (from_nat (size ls) 1) in
  let '(g_add, cs_add, lrs_add) := bit_blast_add g_con lrs_not lrs_con in
  (g_add, cs_not++cs_con++cs_add, lrs_add).

Definition mk_env_neg E g ls : env * generator * cnf * word :=
  let '(E_not, g_not, cs_not, lrs_not) := mk_env_not E g ls in
  let '(E_con, g_con, cs_con, lrs_con) := mk_env_const E_not g_not (from_nat (size ls) 1) in
  let '(E_add, g_add, cs_add, lrs_add) := mk_env_add E_con g_con lrs_not lrs_con in
  (E_add, g_add, cs_not++cs_con++cs_add, lrs_add).

Lemma addB1 bs:
  addB bs (from_nat (size bs) 1) = succB bs.
Proof.
Admitted.

Lemma invB_ss bs :
  size bs = size (invB bs).
Proof.
  elim : bs => [|b_hd b_tl IH].
  - by done.
  - by rewrite /= IH.
Qed.

Lemma bit_blast_neg_correct :
  forall g bs E ls g' cs lrs,
    bit_blast_neg g ls = (g', cs, lrs) ->
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (negB bs).
Proof.
  move => g bs E ls g' cs lrs.
  rewrite /bit_blast_neg (lock bit_blast_const) (lock interp_cnf)/= -!lock.
  case Hnot : (bit_blast_not g ls) => [[g_not cs_not] lrs_not].
  case Hcons : (bit_blast_const g_not (from_nat (size ls) 1)) => [[g_con cs_con] lrs_con].
  case Hadd : (bit_blast_add g_con lrs_not lrs_con) => [[g_add cs_add] lrs_add].
  move => [] _ <- <-.
  rewrite !add_prelude_cat.
  move => Hencbs Hcnf.
  move/andP : Hcnf => [Hcnfnot /andP [Hcnfcon Hcnfadd]].
  move : (bit_blast_not_correct  Hnot Hencbs Hcnfnot) => Henclrs_not.
  move : (bit_blast_const_correct Hcons Hcnfcon) => Henclrs_con. 
  move : (addB1 (invB bs))=> Hencbr. rewrite /negB.
  move : (enc_bits_size Hencbs) => Hszeqls.
  move : (enc_bits_size Henclrs_not) => Hszeqlrsnot.
  move : (enc_bits_size Henclrs_con) => Hszeqlrscon. rewrite size_from_nat in Hszeqlrscon.
  rewrite invB_ss in Hszeqls. rewrite -Hszeqls in Hencbr. rewrite -Hszeqls -Hszeqlrscon in Hszeqlrsnot. 
  exact : (bit_blast_add_correct Hadd Henclrs_not Henclrs_con Hencbr Hcnfadd Hszeqlrsnot).
Qed.

Lemma mk_env_neg_is_bit_blast_neg :
  forall E g ls E' g' cs lrs,
    mk_env_neg E g ls = (E', g', cs, lrs) ->
    bit_blast_neg g ls = (g', cs, lrs).
Proof.
  move => E g ls E' g' cs lrs.
  rewrite /mk_env_neg /bit_blast_neg.
  case Hmknot : (mk_env_not E g ls) => [[[E_not g_not] cs_not] lrs_not].
  rewrite (mk_env_not_is_bit_blast_not Hmknot).
  case Hmkcon : (mk_env_const E_not g_not (from_nat (size ls) 1)) => [[[E_con g_con] cs_con] lrs_con].
  rewrite (mk_env_const_is_bit_blast_const Hmkcon).
  case Hmkadd : (mk_env_add E_con g_con lrs_not lrs_con) => [[[E_add g_add] cs_add] lrs_add].
  rewrite (mk_env_add_is_bit_blast_add Hmkadd).
  by move => [] _ <- <- <-.
Qed.

Lemma bit_blast_not_ss :
  forall ls g g' (cs: cnf) (lrs: seq literal),
    bit_blast_not g ls = (g', cs, lrs) ->
    size ls = size lrs.
Proof.
  move => ls.
  elim : ls=> [| ls_hd ls_tl IH] g g' cs lrs.
  - by case => _ _ <-. 
  - rewrite /=. case Hbbnot : (bit_blast_not (g + 1)%positive ls_tl) => [[gnot csnot] lrsnot].
    case => _ _ <-. move : (IH _ _ _ _ Hbbnot) => Hszeq.
    by rewrite Hszeq /=.
Qed.

Lemma bit_blast_const_ss ls g g' (cs: cnf) (lrs: seq literal):
    bit_blast_const g ls = (g', cs, lrs) ->
    size ls = size lrs.
Proof.
  rewrite /bit_blast_const/=. case => _ _ <-. by rewrite size_map.
Qed.

Lemma mk_env_neg_sat :
  forall E g ls E' g' cs lrs,
    mk_env_neg E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_ff ->
    newer_than_lits g ls ->
    interp_cnf E' cs.
Proof.
  rewrite /mk_env_neg => E g ls E' g' cs lrs.
  case Hmknot : (mk_env_not E g ls) => [[[E_not g_not] cs_not] lrs_not].
  case Hmkcon : (mk_env_const E_not g_not (from_nat (size ls) 1)) => [[[E_con g_con] cs_con] lrs_con].
  case Hmkadd : (mk_env_add E_con g_con lrs_not lrs_con) => [[[E_add g_add] cs_add] lrs_add].
  move => [] <-  _ <- _ Hnewtt Hnewls.
  rewrite !interp_cnf_cat.
  move : (mk_env_not_sat Hmknot Hnewls) .
  move : (mk_env_const_sat Hmkcon) => Hcnfcon.
  move : (mk_env_not_newer_gen Hmknot)=> Hggnot.
  move : (mk_env_const_newer_gen Hmkcon) => Hgnotgcon.
  move : (mk_env_not_newer_res Hmknot Hnewls) => Hnotres.
  move : (mk_env_const_newer_res Hmkcon (newer_than_lit_le_newer Hnewtt Hggnot)) => Hconres.
  move : (bit_blast_not_ss (mk_env_not_is_bit_blast_not Hmknot)) => Hbbnotss. 
  move : (bit_blast_const_ss (mk_env_const_is_bit_blast_const Hmkcon)) => Hbbconss.
  rewrite size_from_nat Hbbnotss in Hbbconss.
  move : (mk_env_add_sat Hmkadd  (newer_than_lits_le_newer Hnotres Hgnotgcon) Hconres (newer_than_lit_le_newer Hnewtt (pos_leb_trans Hggnot Hgnotgcon)) Hbbconss ) => Hcnfadd.
  move : (mk_env_not_newer_cnf Hmknot Hnewls).
  rewrite /mk_env_const in Hmkcon.
  move : (mk_env_not_preserve Hmknot).
  move : Hmkcon => [] -> -> <- _.
  move => HEEcon Hnewcnfnot Hcnfnot.
  move : (mk_env_add_newer_gen Hmkadd) => Hgcongadd.
  move : (mk_env_add_preserve Hmkadd) => HEconEadd.
  rewrite (env_preserve_cnf HEconEadd Hnewcnfnot).
  by rewrite /= Hcnfnot Hcnfadd. 
Qed.

Lemma mk_env_neg_preserve :
  forall E g ls E' g' cs lrs,
    mk_env_neg E g ls = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move => E g ls E' g' cs lrs.
  rewrite /mk_env_neg.
  case Hmknot : (mk_env_not E g ls) => [[[E_not g_not] cs_not] lrs_not].
  case Hmkcon : (mk_env_const E_not g_not (from_nat (size ls) 1)) => [[[E_con g_con] cs_con] lrs_con].
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
  forall E g ls E' g' cs lrs,
    mk_env_neg E g ls = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move => E g ls E' g' cs lrs.
  rewrite /mk_env_neg.
  case Hmknot : (mk_env_not E g ls) => [[[E_not g_not] cs_not] lrs_not].
  case Hmkcon : (mk_env_const E_not g_not (from_nat (size ls) 1)) => [[[E_con g_con] cs_con] lrs_con].
  case Hmkadd : (mk_env_add E_con g_con lrs_not lrs_con) => [[[E_add g_add] cs_add] lrs_add].
  move => [] _ <- _ _.
  move : (mk_env_not_newer_gen Hmknot) => Hggnot.
  move : (mk_env_const_newer_gen Hmkcon) => Hgnotgcon.
  move : (mk_env_add_newer_gen Hmkadd) => Hgcongadd.
  exact : (pos_leb_trans Hggnot (pos_leb_trans Hgnotgcon Hgcongadd)).
Qed.

Lemma mk_env_neg_newer_res :
  forall E g ls E' g' cs lrs,
    mk_env_neg E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    newer_than_lits g' lrs.
Proof.
  move => E g ls E' g' cs lrs.
  rewrite /mk_env_neg.
  case Hmknot : (mk_env_not E g ls) => [[[E_not g_not] cs_not] lrs_not].
  case Hmkcon : (mk_env_const E_not g_not (from_nat (size ls) 1)) => [[[E_con g_con] cs_con] lrs_con].
  case Hmkadd : (mk_env_add E_con g_con lrs_not lrs_con) => [[[E_add g_add] cs_add] lrs_add].
  move => [] _ <- _ <- Htt Hgls.
  exact : (mk_env_add_newer_res Hmkadd) => Hgaddlrsadd.
Qed.

Lemma mk_env_neg_newer_cnf :
  forall E g ls E' g' cs lrs,
    mk_env_neg E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    newer_than_cnf g' cs.
Proof.
  move => E g ls E' g' cs lrs.
  rewrite /mk_env_neg.
  case Hmknot : (mk_env_not E g ls) => [[[E_not g_not] cs_not] lrs_not].
  case Hmkcon : (mk_env_const E_not g_not (from_nat (size ls) 1)) => [[[E_con g_con] cs_con] lrs_con].
  case Hmkadd : (mk_env_add E_con g_con lrs_not lrs_con) => [[[E_add g_add] cs_add] lrs_add].
  move => [] _ <- <- _ Htt Hgls.
  rewrite !newer_than_cnf_cat.
  move : (mk_env_not_newer_gen Hmknot) => Hggnot.
  move : (mk_env_const_newer_gen Hmkcon) => Hgnotgcon.
  move : (mk_env_add_newer_gen Hmkadd) => Hgcongadd.
  move : (mk_env_not_newer_res Hmknot Hgls) => Hgnotresnot.
  move : (mk_env_const_newer_res Hmkcon (newer_than_lit_le_newer Htt Hggnot)) => Hgconlrscon.
  move : (bit_blast_not_ss (mk_env_not_is_bit_blast_not Hmknot)) => Hnotss.
  move : (bit_blast_const_ss (mk_env_const_is_bit_blast_const Hmkcon)) => Hconss.
  rewrite size_from_nat Hnotss in Hconss.
  rewrite (mk_env_add_newer_cnf Hmkadd (newer_than_lits_le_newer Hgnotresnot Hgnotgcon) Hgconlrscon (newer_than_lit_le_newer Htt (pos_leb_trans Hggnot Hgnotgcon)) Hconss) /=.
  move : (mk_env_not_newer_cnf Hmknot Hgls) => Hcnfnot.
  rewrite (newer_than_cnf_le_newer Hcnfnot (pos_leb_trans Hgnotgcon Hgcongadd)) /=.
  rewrite /mk_env_const in Hmkcon.
  by case :Hmkcon => _ _ <- _ /=.
Qed.
