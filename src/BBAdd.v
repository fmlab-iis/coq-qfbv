From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import Var QFBV CNF BBCommon.
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_full_adder ===== *)

Definition bit_blast_full_adder1 g a1 a2 cin :=
  let (g', r) := gen g in
  let (g'', cout) := gen g' in
  let sum_cs := [::
        [:: neg_lit r; a1; a2; cin];
          [:: neg_lit r; neg_lit a1; neg_lit a2; cin];
          [:: neg_lit r; neg_lit a1; a2; neg_lit cin];
          [:: neg_lit r; a1; neg_lit a2; neg_lit cin];
        [:: r; neg_lit a1; a2; cin];
          [:: r; a1; neg_lit a2; cin];
          [:: r; a1; a2; neg_lit cin];
          [:: r; neg_lit a1; neg_lit a2; neg_lit cin]
      ] in
  let cout_cs := [::
        [:: neg_lit cout; a1; a2];
          [:: neg_lit cout; a1; cin];
          [:: neg_lit cout; a2; cin];
        [:: cout; neg_lit a1; neg_lit a2];
          [:: cout; neg_lit a1; a2; neg_lit cin];
          [:: cout; a1; neg_lit a2; neg_lit cin]
      ] in
  (g'', sum_cs++cout_cs, cout, r).

Definition mk_env_full_adder1 E g a1 a2 cin :=
  let (g', r) := gen g in
  let (g'', cout) := gen g' in
  let sum_cs := [::
        [:: neg_lit r; a1; a2; cin];
          [:: neg_lit r; neg_lit a1; neg_lit a2; cin];
          [:: neg_lit r; neg_lit a1; a2; neg_lit cin];
          [:: neg_lit r; a1; neg_lit a2; neg_lit cin];
        [:: r; neg_lit a1; a2; cin];
          [:: r; a1; neg_lit a2; cin];
          [:: r; a1; a2; neg_lit cin];
          [:: r; neg_lit a1; neg_lit a2; neg_lit cin]
      ] in
  let cout_cs := [::
        [:: neg_lit cout; a1; a2];
          [:: neg_lit cout; a1; cin];
          [:: neg_lit cout; a2; cin];
        [:: cout; neg_lit a1; neg_lit a2];
          [:: cout; neg_lit a1; a2; neg_lit cin];
          [:: cout; a1; neg_lit a2; neg_lit cin]
      ] in
  let E' := env_upd E (var_of_lit r)
                    (xorb (xorb (interp_lit E a1) (interp_lit E a2))
                          (interp_lit E cin)) in
  let E'' := env_upd E' (var_of_lit cout)
                     (((interp_lit E a1) && (interp_lit E a2))
                      || ((xorb (interp_lit E a1) (interp_lit E a2))
                            && (interp_lit E cin))) in
  (E'', g'', sum_cs++cout_cs, cout, r).

Lemma bit_blast_full_adder1_correct1 :
  forall g b1 b2 bcin E l1 l2 lcin g' cs lcout lr ,
    bit_blast_full_adder1 g l1 l2 lcin = (g', cs, lcout, lr) ->
    enc_bit E l1 b1 -> enc_bit E l2 b2 -> enc_bit E lcin bcin ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (xorb (xorb b1 b2) bcin) /\
    enc_bit E lcout ((b1 && b2) || ((xorb b1 b2) && bcin)).
Proof.
  rewrite /bit_blast_full_adder1 /=.
  move=> g b1 b2 bcin E l1 l2 lcin g' cs lcout lr.
  case => _ <- <- <-. move=> {g' cs lcout lr}.
  rewrite /enc_bit /=.
  repeat (rewrite add_prelude_cons !add_prelude_singleton !interp_clause_cons).
  rewrite !interp_lit_neg_lit /=.
  move=> /eqP -> /eqP -> /eqP -> H. split_andb_hyps. split.
  - move: {H13 H14 H15 H16 H17 H18} H19 H20 H21 H22 H23 H24 H25 H26.
      by case: (E g); case: b1; case: b2; case: bcin.
  - move: H13 H14 H15 H16 H17 H18 {H19 H20 H21 H22 H23 H24 H25 H26}.
      by case: (E (g + 1)%positive); case: b1; case: b2; case: bcin.
Qed.


Lemma bit_blast_full_adder1_correct2 :
  forall g b1 b2 bcin bcout br E l1 l2 lcin g' cs lcout lr,
    bit_blast_full_adder1 g l1 l2 lcin = (g', cs, lcout, lr) ->
    enc_bit E l1 b1 -> enc_bit E l2 b2 -> enc_bit E lcin bcin ->
    interp_cnf E (add_prelude cs) ->
    bool_adder bcin b1 b2 = (bcout, br) ->
    enc_bit E lr br /\
    enc_bit E lcout bcout.
Proof.
  rewrite /bit_blast_full_adder1 /=.
  move=> g b1 b2 bcin bcout br E l1 l2 lcin g' cs lcout lr.
  case => _ <- <- <-. move=> {g' cs lcout lr}.
  rewrite /enc_bit /=.
  repeat (rewrite add_prelude_cons !add_prelude_singleton !interp_clause_cons).
  rewrite !interp_lit_neg_lit /=.
  move=> /eqP -> /eqP -> /eqP -> H. split_andb_hyps. move=> Hadd. split.
  - move: Hadd {H13 H14 H15 H16 H17 H18} H19 H20 H21 H22 H23 H24 H25 H26.
    rewrite /bool_adder.
      by case: (E g); case: b1; case: b2; case: bcin; case; move=> _ <- /=.
  - move: Hadd H13 H14 H15 H16 H17 H18 {H19 H20 H21 H22 H23 H24 H25 H26}.
      by case: (E (g + 1)%positive); case: b1; case: b2; case: bcin;
        case; move=> <- _.
Qed.

Fixpoint bit_blast_full_adder_zip g lcin lp : generator * cnf * literal * word :=
  match lp with
  | [::] => (g, [::], lcin, [::])
  | (l1, l2) :: tl =>
    let '(g_hd, cs_hd, lcout_hd, lrs_hd) := bit_blast_full_adder1 g l1 l2 lcin in
    let '(g_tl, cs_tl, lcout_tl, lrs_tl) := bit_blast_full_adder_zip g_hd lcout_hd tl in
    (g_tl, catrev cs_hd cs_tl, lcout_tl, lrs_hd :: lrs_tl)
  end.

Definition bit_blast_full_adder g lcin ls1 ls2 :=
  bit_blast_full_adder_zip g lcin (extzip_ff ls1 ls2).

Fixpoint mk_env_full_adder_zip E g lcin lp : env * generator * cnf * literal * word :=
  match lp with
  | [::] => (E, g, [::], lcin, [::])
  | (l1, l2) :: tl =>
    let '(E_hd, g_hd, cs_hd, lcout_hd, lrs_hd) := mk_env_full_adder1 E g l1 l2 lcin in
    let '(E_tl, g_tl, cs_tl, lcout_tl, lrs_tl) := mk_env_full_adder_zip E_hd g_hd lcout_hd tl in
    (E_tl, g_tl, catrev cs_hd cs_tl, lcout_tl, lrs_hd::lrs_tl)
  end.

Definition mk_env_full_adder E g lcin ls1 ls2 :=
  mk_env_full_adder_zip E g lcin (extzip_ff ls1 ls2).

Lemma bit_blast_full_adder_zip_correct E g bp bcin bcout lp lcin lcout g' cs lrs brs :
  bit_blast_full_adder_zip g lcin lp = (g', cs, lcout, lrs) ->
  enc_bits E (unzip1 lp) (unzip1 bp) -> enc_bits E (unzip2 lp) (unzip2 bp) ->
  enc_bit E lcin bcin -> interp_cnf E (add_prelude cs) ->
  adcB bcin (unzip1 bp) (unzip2 bp) = (bcout, brs) ->
  enc_bit E lcout bcout /\ enc_bits E lrs brs.
Proof.
  elim: lp E g bp bcin bcout lcin lcout g' cs lrs brs =>
  [|[l1_hd l2_hd] lp_tl IH] E g bp bcin bcout lcin lcout g' cs lrs brs.
  - rewrite !enc_bits_nil_l. case => _ <- <- <- /eqP -> /eqP -> Henclcin _ /=.
    rewrite /adcB /full_adder/=. case => <- <-.
    split; [exact Henclcin| rewrite !enc_bits_nil_l/=; auto].
  - rewrite /bit_blast_full_adder_zip (lock bit_blast_full_adder1) /= -!lock -/bit_blast_full_adder_zip.
    dcase (bit_blast_full_adder1 g l1_hd l2_hd lcin) => [[[[g_hd] cs_hd] lcout_hd] lrs_hd] Hfadd1.
    dcase (bit_blast_full_adder_zip g_hd lcout_hd lp_tl) => [[[[g_tl] cs_tl] lcout_tl] lrs_tl] Hfaddz.
    case => _ <- <- <- /=.
    case : bp => [| [bp_hd1 bp_hd2] bp_tl] //=.
    rewrite !enc_bits_cons. move => /andP [Henchd1 Henctl1] /andP [Henchd2 Henctl2] Henclcin.
    rewrite add_prelude_catrev => /andP [Haphd Haptl].
    rewrite /adcB /=.
    case Hfaddhd : (full_adder bcin (bp_hd1 :: unzip1 bp_tl) (bp_hd2 :: unzip2 bp_tl)) => [bcout_hd brs_hd].
    move : Hfaddhd.
    rewrite /full_adder /=.
    case Hbaddhd : (bool_adder bcin bp_hd1 bp_hd2) => [bbcout_hd bbrs_hd].
    case Hfaddzhd : (full_adder_zip bbcout_hd (zip (unzip1 bp_tl) (unzip2 bp_tl)))
                      => [bbcout_tl bbrs_tl].
    case => <- <-. case => <- <-.
    move : (bit_blast_full_adder1_correct2 Hfadd1 Henchd1 Henchd2 Henclcin Haphd Hbaddhd) => [Henclrshd Henclcouthd]. 
    rewrite enc_bits_cons Henclrshd andTb.
    move : Hfaddzhd.
    replace (full_adder_zip bbcout_hd (zip (unzip1 bp_tl) (unzip2 bp_tl))) with
        (full_adder bbcout_hd (unzip1 bp_tl) (unzip2 bp_tl)) by auto.
    replace (full_adder bbcout_hd (unzip1 bp_tl) (unzip2 bp_tl)) with
        (adcB bbcout_hd (unzip1 bp_tl) (unzip2 bp_tl)) by auto.
    move => Hfaddzhd.
    exact : (IH _ _ _ _ _ _ _ _ _ _ _ Hfaddz Henctl1 Henctl2 Henclcouthd Haptl Hfaddzhd).
Qed.

Lemma bit_blast_full_adder_correct E g ls1 ls2 bcin bs1 bs2 lcin g' cs lrs brs lcout bcout:
  bit_blast_full_adder g lcin ls1 ls2 = (g', cs, lcout, lrs) ->
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 -> enc_bit E lcin bcin ->
  interp_cnf E (add_prelude cs) -> adcB bcin bs1 bs2 = (bcout, brs) ->
  size ls1 = size ls2 ->
  enc_bit E lcout bcout /\ enc_bits E lrs brs.
Proof.
  rewrite /bit_blast_full_adder => Hbbfadd Henc1 Henc2 Hencin Hcs HadcB Hszeq.
  move : (enc_bits_size Henc1) (enc_bits_size Henc2) => Hsz1 Hsz2.
  move : (add_prelude_enc_bit_tt Hcs) => Henctt.
  move : HadcB.
  assert (bs1 = (unzip1 (extzip0 bs1 bs2))) as Hbs1; [rewrite unzip1_extzip_ss; [auto|rewrite -Hsz1-Hsz2; exact Hszeq]|].
  assert (bs2 = (unzip2 (extzip0 bs1 bs2))) as Hbs2; [rewrite unzip2_extzip_ss; [auto|rewrite -Hsz1-Hsz2; exact Hszeq]|].
  rewrite Hbs2.
  replace (adcB bcin bs1 (unzip2 (extzip0 bs1 bs2))) with (adcB bcin (unzip1 (extzip0 bs1 bs2)) (unzip2 (extzip0 bs1 bs2))); [|rewrite <- Hbs1; auto].
  move => HadcB.
  exact : (bit_blast_full_adder_zip_correct Hbbfadd
                                            (enc_bits_unzip1_extzip Henctt Henc1 Henc2)
                                            (enc_bits_unzip2_extzip Henctt Henc1 Henc2)
                                            Hencin Hcs HadcB).
Qed.
  
Corollary bit_blast_full_adder_correct1 E g ls1 ls2 bcin bs1 bs2 lcin g' cs lrs brs lcout bcout :
  bit_blast_full_adder g lcin ls1 ls2 = (g', cs, lcout, lrs) ->
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 -> enc_bit E lcin bcin ->
  interp_cnf E (add_prelude cs) ->
  adcB bcin bs1 bs2 = (bcout, brs) ->
  size ls1 = size ls2 ->
  enc_bits E lrs brs.
Proof.
  move=> Hblast Henc1 Henc2 Hencin Hcs Hbrs Hszeq.
  move: (bit_blast_full_adder_correct Hblast Henc1 Henc2 Hencin Hcs Hbrs Hszeq).
  move=> [H1 H2]; exact: H2.
Qed.

Corollary bit_blast_full_adder_correct2 E g ls1 ls2 bcin bs1 bs2 lcin g' cs lrs brs lcout bcout :
  bit_blast_full_adder g lcin ls1 ls2 = (g', cs, lcout, lrs) ->
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 -> enc_bit E lcin bcin ->
  interp_cnf E (add_prelude cs) ->
  adcB bcin bs1 bs2 = (bcout, brs) ->
  size ls1 = size ls2 ->
  enc_bit E lcout bcout.
Proof.
  move=> Hblast Henc1 Henc2 Hencin Hcs Hbrs Hszeq.
  move: (bit_blast_full_adder_correct Hblast Henc1 Henc2 Hencin Hcs Hbrs Hszeq).
  move=> [H1 H2]; exact: H1.
Qed.

Lemma mk_env_full_adder1_is_bit_blast_full_adder1 E g l1 l2 lcin E' g' cs lcout lrs :
  mk_env_full_adder1 E g l1 l2 lcin = (E', g', cs, lcout, lrs) ->
  bit_blast_full_adder1 g l1 l2 lcin = (g', cs, lcout, lrs).
Proof.
  rewrite /mk_env_full_adder1 /bit_blast_full_adder1; intros.
  dite_hyps; dcase_hyps; subst; reflexivity.
Qed.

Lemma mk_env_full_adder_zip_is_bit_blast_full_adder_zip E g lp lcin E' g' cs lcout lrs :
  mk_env_full_adder_zip E g lcin lp = (E', g', cs, lcout, lrs) ->
  bit_blast_full_adder_zip g lcin lp = (g', cs, lcout, lrs).
Proof.
  elim : lp E g lcin lcout E' g' cs lrs =>
  [|[l1_hd l2_hd] lp_tl IH] E g lcin lcout E' g' cs lrs.
  - by case => _ <- <- <- <-.
  - rewrite /bit_blast_full_adder_zip (lock bit_blast_full_adder1) /mk_env_full_adder_zip (lock mk_env_full_adder1)/= -!lock -/bit_blast_full_adder_zip -/mk_env_full_adder_zip.
    dcase (mk_env_full_adder1 E g l1_hd l2_hd lcin) => [[[[[E_hd] g_hd] cs_hd] lcout_hd] lrs_hd] Henv1.
    dcase (mk_env_full_adder_zip E_hd g_hd lcout_hd lp_tl) => [[[[[E_tl] g_tl] lcout_tl] cs_tl] lrs_tl] Henvzip.
    case => _ <- <- <- <-. rewrite (mk_env_full_adder1_is_bit_blast_full_adder1 Henv1).
    by rewrite (IH _ _ _ _ _ _ _ _ Henvzip).
Qed.

Lemma mk_env_full_adder_is_bit_blast_full_adder E g l1 l2 lcin E' g' cs lcout lrs :
  mk_env_full_adder E g lcin l1 l2 = (E', g', cs, lcout, lrs) ->
  bit_blast_full_adder g lcin l1 l2 = (g', cs, lcout, lrs).
Proof.
  exact : mk_env_full_adder_zip_is_bit_blast_full_adder_zip.
Qed.
  
Lemma mk_env_full_adder1_newer_gen E g l1 l2 lcin E' g' cs lrs lcout:
  mk_env_full_adder1 E g l1 l2 lcin = (E', g', cs, lcout, lrs) -> (g <=? g')%positive.
Proof.
  rewrite /mk_env_full_adder1.
  case => _ <- _ _ _. rewrite -Pos.add_assoc; exact : pos_leb_add_diag_r.
Qed.

Lemma mk_env_full_adder_zip_newer_gen E g lp lcin E' g' cs lrs lcout :
  mk_env_full_adder_zip E g lcin lp = (E', g', cs, lcout, lrs) -> (g <=? g')%positive.
Proof.
  elim: lp E g lcin E' g' cs lrs lcout => [| [l1_hd l2_hd] lp_tl IH] E g lcin E' g' cs lrs lcout.
  - case => _ <- _ _ _. exact: Pos.leb_refl.
  - rewrite /mk_env_full_adder_zip (lock mk_env_full_adder1)/= -!lock -/mk_env_full_adder_zip.
    dcase (mk_env_full_adder1 E g l1_hd l2_hd lcin) => [[[[[E_hd] g_hd] cs_hd] lcout_hd] lrs_hd] Henv1.
    dcase (mk_env_full_adder_zip E_hd g_hd lcout_hd lp_tl) => [[[[[E_tl] g_tl] cs_tl] lcout_tl] lrs_tl] Henvzip.
    case => _ <- _ _ _. apply : (pos_leb_trans (mk_env_full_adder1_newer_gen Henv1)).
    exact : (IH _ _ _ _ _ _ _ _ Henvzip).
Qed.

Lemma mk_env_full_adder_newer_gen E g l1 l2 lcin E' g' cs lrs lcout:
  mk_env_full_adder E g lcin l1 l2 = (E', g', cs, lcout, lrs) -> (g <=? g')%positive.
Proof.
  rewrite /mk_env_full_adder => Henv.
  by apply mk_env_full_adder_zip_newer_gen with E (extzip_ff l1 l2) lcin E' cs lrs lcout.
Qed.

Lemma mk_env_full_adder1_newer_res E g l1 l2 lcin E' g' cs lrs lcout:
  mk_env_full_adder1 E g l1 l2 lcin = (E', g', cs, lcout, lrs) -> newer_than_lit g' lrs.
Proof.
  rewrite /mk_env_full_adder1.
  case => _ <- _ _ <-. rewrite /newer_than_lit/newer_than_var -Pos.add_assoc; exact : pos_ltb_add_diag_r.
Qed.

Lemma mk_env_full_adder_zip_newer_res  E g lp lcin E' g' cs lrs lcout:
  mk_env_full_adder_zip E g lcin lp = (E', g', cs, lcout, lrs) ->
  newer_than_lits g' lrs.
Proof.
  elim : lp E g lcin E' g' cs lrs lcout => [| [l1_hd l2_hd] lp_tl IH] E g lcin E' g' cs lrs lcout.
  - by case => _ <- _ _ <-.
  - rewrite /mk_env_full_adder_zip (lock mk_env_full_adder1)/= -!lock -/mk_env_full_adder_zip.
    dcase (mk_env_full_adder1 E g l1_hd l2_hd lcin) => [[[[[E_hd] g_hd] cs_hd] lcout_hd] lrs_hd] Henv1.
    dcase (mk_env_full_adder_zip E_hd g_hd lcout_hd lp_tl) => [[[[[E_tl] g_tl] cs_tl] lcout_tl] lrs_tl] Henvzip.
    case => _ <- _ _ <-.
    move : (mk_env_full_adder_zip_newer_gen Henvzip) => Hgle.
    move : (mk_env_full_adder1_newer_res Henv1) => Hntlghdlrshd.
    rewrite newer_than_lits_cons. apply/andP; split.
    exact : (newer_than_lit_le_newer Hntlghdlrshd Hgle).
    exact : (IH _ _ _ _ _ _ _ _ Henvzip).
Qed.

Lemma mk_env_full_adder_newer_res  E g l1 l2 lcin E' g' cs lrs lcout:
  mk_env_full_adder E g lcin l1 l2 = (E', g', cs, lcout, lrs) -> newer_than_lits g' lrs.
Proof.
  rewrite /mk_env_full_adder => Henv.
  by apply mk_env_full_adder_zip_newer_res with E g (extzip_ff l1 l2) lcin E' cs lcout.
Qed.
  
Lemma mk_env_full_adder1_newer_cout E g l1 l2 lcin E' g' cs lrs lcout:
  mk_env_full_adder1 E g lcin l1 l2 = (E', g', cs, lcout, lrs) ->
  (*newer_than_lit g lcin ->*) newer_than_lit g' lcout.
Proof.
  rewrite /mk_env_full_adder1. case => _ <- _ <- _.
  rewrite /newer_than_lit/newer_than_var /=. exact : pos_ltb_add_diag_r.
Qed.

Lemma mk_env_full_adder_zip_newer_cout  E g lp lcin E' g' cs lrs lcout:
  mk_env_full_adder_zip E g lcin lp = (E', g', cs, lcout, lrs) ->
  newer_than_lit g lcin -> newer_than_lit g' lcout.
Proof.
  elim : lp E g lcin E' g' cs lrs lcout => [| [l1_hd l2_hd] lp_tl IH] E g lcin E' g' cs lrs lcout.
  - by case => _ <- _ <- _.
  - rewrite /mk_env_full_adder_zip (lock mk_env_full_adder1)/= -!lock -/mk_env_full_adder_zip.
    dcase (mk_env_full_adder1 E g l1_hd l2_hd lcin) => [[[[[E_hd] g_hd] cs_hd] lcout_hd] lrs_hd] Henv1.
    dcase (mk_env_full_adder_zip E_hd g_hd lcout_hd lp_tl) => [[[[[E_tl] g_tl] cs_tl] lcout_tl] lrs_tl] Henvzip.
    case => _ <- _ <- _ Hglcin.
    move : (mk_env_full_adder1_newer_cout Henv1) => Hghdlcout.
    exact : (IH _ _ _ _ _ _ _ _ Henvzip Hghdlcout).
Qed.

Lemma mk_env_full_adder_newer_cout  E g l1 l2 lcin E' g' cs lrs lcout:
  mk_env_full_adder E g lcin l1 l2 = (E', g', cs, lcout, lrs) ->
  newer_than_lit g lcin -> newer_than_lit g' lcout.
Proof.
  rewrite /mk_env_full_adder => Henv Hntlcin.
  by apply mk_env_full_adder_zip_newer_cout with E g (extzip_ff l1 l2) lcin E' cs lrs.
Qed.

Lemma mk_env_full_adder1_newer_cnf E g l1 l2 lcin E' g' cs lrs lcout:
  mk_env_full_adder1 E g l1 l2  lcin = (E', g', cs, lcout, lrs) ->
  newer_than_lit g l1 -> newer_than_lit g l2 -> newer_than_lit g lcin ->
  newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_full_adder1.
  - case => _ <- <- _ _ Hl1 Hl2 Hlcin.  
    move : (pos_ltb_add_diag_r g (1+1)) => Hgg2; rewrite Pos.add_assoc in Hgg2.
    move : (newer_than_lit_lt_newer Hl1 Hgg2) => Hg2l1.
    move : (newer_than_lit_lt_newer Hl2 Hgg2) => Hg2l2.
    move : (newer_than_lit_lt_newer Hlcin Hgg2) => Hg2lcin.
    by rewrite /= !newer_than_lit_neg Hg2l1 Hg2l2 Hg2lcin /= /newer_than_lit/newer_than_var/= pos_ltb_add_diag_r Hgg2 .
Qed.

Lemma mk_env_full_adder_zip_newer_cnf  E g lp lcin E' g' cs lrs lcout:
  mk_env_full_adder_zip E g lcin lp = (E', g', cs, lcout, lrs) ->
  newer_than_lits g (unzip1 lp) -> newer_than_lits g (unzip2 lp) ->
  newer_than_lit g lcin -> newer_than_cnf g' cs.
Proof.
  elim : lp E g lcin E' g' cs lrs lcout => [| [l1_hd l2_hd] lp_tl IH] E g lcin E' g' cs lrs lcout.
  - by case => _ <- <- _ _.
  - rewrite /mk_env_full_adder_zip (lock mk_env_full_adder1)/= -!lock -/mk_env_full_adder_zip.
    dcase (mk_env_full_adder1 E g l1_hd l2_hd lcin) => [[[[[E_hd] g_hd] cs_hd] lcout_hd] lrs_hd] Henv1.
    dcase (mk_env_full_adder_zip E_hd g_hd lcout_hd lp_tl) => [[[[[E_tl] g_tl] cs_tl] lcout_tl] lrs_tl] Henvzip.
    case => _ <- <- _ _ . move => /andP [Hntl1hd Hntl1tl] /andP [Hntl2hd Hntl2tl] Hntlcin.
    rewrite newer_than_cnf_catrev.
    move : (mk_env_full_adder1_newer_cnf Henv1 Hntl1hd Hntl2hd Hntlcin) => Hntcgtl.
    move : (mk_env_full_adder1_newer_gen Henv1) => Hgghd.
    move : (mk_env_full_adder_zip_newer_gen Henvzip) => Hghdgtl.
    apply /andP; split.
    exact : (newer_than_cnf_le_newer Hntcgtl Hghdgtl).
    move : (newer_than_lits_le_newer Hntl1tl Hgghd) => Hntlghd1.
    move : (newer_than_lits_le_newer Hntl2tl Hgghd) => Hntlghd2.
    move : (newer_than_lit_le_newer Hntlcin Hgghd) => Hntlghdcin.
    move : (mk_env_full_adder1_newer_cout Henv1) => Hntlcout.
    exact : (IH _ _ _ _ _ _ _ _ Henvzip Hntlghd1 Hntlghd2 Hntlcout).
Qed.

Lemma mk_env_full_adder_newer_cnf  E g l1 l2 lcin E' g' cs lrs lcout:
  mk_env_full_adder E g lcin l1 l2 = (E', g', cs, lcout, lrs) ->
  newer_than_lits g l1 -> newer_than_lits g l2 ->
  newer_than_lit g lcin -> size l1 = size l2 -> newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_full_adder => Henv Hntl1 Hntl2 Hntlcin Hszeq.
  apply mk_env_full_adder_zip_newer_cnf with E g (extzip_ff l1 l2) lcin E' lrs lcout;
    [done|by rewrite unzip1_extzip_ss|by rewrite unzip2_extzip_ss|done].
Qed.

Lemma mk_env_full_adder1_preserve E g l1 l2 lcin E' g' cs lrs lcout:
  mk_env_full_adder1 E g l1 l2 lcin = (E', g', cs, lcout, lrs) ->
  env_preserve E E' g.
Proof.
  rewrite /mk_env_full_adder1/=. case => <- _ _ _ _.
  apply (@env_preserve_trans _ (env_upd E g
          (xorb (xorb (interp_lit E l1) (interp_lit E l2))
                (interp_lit E lcin)))).
  - exact: env_upd_eq_preserve.
  - apply env_upd_newer_preserve; by apply newer_than_var_add_diag_r.
Qed.

Lemma mk_env_full_adder_zip_preserve E g lp lcin E' g' cs lrs lcout:
  mk_env_full_adder_zip E g lcin lp = (E', g', cs, lcout, lrs) ->
  env_preserve E E' g.
Proof.
  elim : lp E g lcin E' g' cs lrs lcout => [| [l1_hd l2_hd] lp_tl IH] E g lcin E' g' cs lrs lcout.
  - by case => <- _ _ _ _.
  - rewrite /mk_env_full_adder_zip (lock mk_env_full_adder1)/= -!lock -/mk_env_full_adder_zip.
    dcase (mk_env_full_adder1 E g l1_hd l2_hd lcin) => [[[[[E_hd] g_hd] cs_hd] lcout_hd] lrs_hd] Henv1.
    dcase (mk_env_full_adder_zip E_hd g_hd lcout_hd lp_tl) => [[[[[E_tl] g_tl] cs_tl] lcout_tl] lrs_tl] Henvzip.
    case => <- _ _ _ _.
    move : (mk_env_full_adder1_preserve Henv1) => HEEhd.
    move : (IH _ _ _ _ _ _ _ _ Henvzip) => HEhdEtl.
    move : (mk_env_full_adder1_newer_gen Henv1) => Hgghd.
    exact : (env_preserve_trans HEEhd (env_preserve_le HEhdEtl Hgghd)).
Qed.

Lemma mk_env_full_adder_preserve E g l1 l2 lcin E' g' cs lrs lcout:
  mk_env_full_adder E g l1 l2 lcin = (E', g', cs, lcout, lrs) ->
  env_preserve E E' g.
Proof.
  exact : mk_env_full_adder_zip_preserve.
Qed.

Lemma mk_env_full_adder1_sat E g l1 l2 lcin E' g' cs lrs lcout:
  mk_env_full_adder1 E g l1 l2 lcin = (E', g', cs, lcout, lrs) ->
  newer_than_lit g l1 -> newer_than_lit g l2 -> newer_than_lit g lcin ->
  interp_cnf E' cs.
Proof.
  move => Hadd1 Hntl1 Hntl2 Hntlcin. 
  move : (pos_ltb_add_diag_r g 1) => Hgg1.
  move : (newer_than_lit_lt_newer Hntl1 Hgg1) => Hntl1g1.
  move : (newer_than_lit_lt_newer Hntl2 Hgg1) => Hntl2g1.
  move : (newer_than_lit_lt_newer Hntlcin Hgg1) => Hntlcing1. 
  move : (Pos.succ_discr g) => Hneqsucc.
  move : Hadd1.
  rewrite /mk_env_full_adder1. case => <- _ <- _ _ .
  case Hintl1 : (interp_lit E l1); case Hintl2: (interp_lit E l2);case Hintlcin :(interp_lit E lcin); rewrite/= !orbF andbT;
    rewrite !interp_lit_env_upd_neq;
    try (apply newer_than_lit_neq; rewrite newer_than_lit_neg; done);
    try (apply newer_than_lit_neq; done);
    try (rewrite !interp_lit_neg_lit Hintl1 Hintl2 Hintlcin/= !orbF !orbT !andTb andbT /env_upd/= !eq_refl Pos.add_1_r;
       case Heqsucc: (Pos.succ g == g); try done; rewrite (eqP Heqsucc) in Hneqsucc; done).
  rewrite !interp_lit_neg_lit Hintl1 Hintl2 Hintlcin/= !orbF !orbT !andTb /env_upd/=!eq_refl Pos.add_1_r; case Heqsucc: (Pos.succ g == g); try done; rewrite (eqP Heqsucc) in Hneqsucc; done.
Qed.

Lemma mk_env_full_adder_zip_sat E g lp lcin E' g' cs lrs lcout:
  mk_env_full_adder_zip E g lcin lp = (E', g', cs, lcout, lrs) ->
  newer_than_lits g (unzip1 lp) -> newer_than_lits g (unzip2 lp) -> newer_than_lit g lcin ->
  interp_cnf E' cs.
Proof. 
  elim : lp E g lcin E' g' cs lrs lcout => [| [l1_hd l2_hd] lp_tl IH] E g lcin E' g' cs lrs lcout.
  - by case => <- _ <- _ _.
  - rewrite /mk_env_full_adder_zip (lock mk_env_full_adder1)/= -!lock -/mk_env_full_adder_zip.
    dcase (mk_env_full_adder1 E g l1_hd l2_hd lcin) => [[[[[E_hd] g_hd] cs_hd] lcout_hd] lrs_hd] Henv1.
    dcase (mk_env_full_adder_zip E_hd g_hd lcout_hd lp_tl) => [[[[[E_tl] g_tl] cs_tl] lcout_tl] lrs_tl] Henvzip.
    case => <- _ <- _ _ /andP [Hntl1hd Hntl1tl] /andP [Hntl2hd Hntl2tl] Hntlcin.
    move : (mk_env_full_adder1_sat Henv1 Hntl1hd Hntl2hd Hntlcin) => Hsat1.
    move : (mk_env_full_adder_zip_preserve Henvzip) => HEhdEtl.
    move : (mk_env_full_adder1_newer_gen Henv1)=> Hgghd.
    move : (mk_env_full_adder1_newer_cout Henv1) => Hntlcoutghd.
    move : (newer_than_lits_le_newer Hntl1tl Hgghd) => Hntl1tlghd.
    move : (newer_than_lits_le_newer Hntl2tl Hgghd) => Hntl2tlghd.
    move : (mk_env_full_adder1_newer_cnf Henv1 Hntl1hd Hntl2hd Hntlcin) => Hncnf1.
    rewrite interp_cnf_catrev.
    apply /andP; split.
  - by rewrite (env_preserve_cnf HEhdEtl Hncnf1).
  - exact : (IH _ _ _ _ _ _ _ _ Henvzip Hntl1tlghd Hntl2tlghd Hntlcoutghd).
Qed.

Lemma mk_env_full_adder_sat  E g l1 l2 lcin E' g' cs lrs lcout:
  mk_env_full_adder E g lcin l1 l2 = (E', g', cs, lcout, lrs) ->
  newer_than_lits g l1 -> newer_than_lits g l2 -> newer_than_lit g lcin -> size l1 = size l2 ->
  interp_cnf E' cs.
Proof.
  rewrite /mk_env_full_adder => Henv Hntl1 Hntl2 Hntlcin Hszeq.
  apply mk_env_full_adder_zip_sat with E g (extzip_ff l1 l2) lcin g' lrs lcout;
    [done|by rewrite unzip1_extzip_ss|by rewrite unzip2_extzip_ss|done].
Qed.
  