From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNFSimple BBCommonSimple BBConstSimple BBZeroExtendSimple BBMulSimple BBHighSimple BBEqSimple.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Fixpoint bit_blast_umulo_rec w (g: generator) : w.-tuple literal -> w.-tuple literal -> generator * cnf * literal * literal:=
  if w is w'.+1 then
    fun ls1 ls2 =>
      let (ls1_hightl, ls1_low) := eta_expand (splitlsb ls1) in
      let (ls2_high, ls2_lowtl) := eta_expand (splitmsb ls2) in
      let '(g1, cs_tl, r_or_tl, r_and_or_tl) := bit_blast_umulo_rec g ls1_hightl ls2_lowtl in
      let (g2, r_or) := gen g1 in
      let (g3, r_and_or) := gen g2 in
      (* or sum  r_or <-> r_or_tl || ls1_low *)
      let cs_prefix_or := [::
                             [:: neg_lit r_or_tl; r_or];
                             [:: r_or_tl; ls1_low; neg_lit r_or];
                             [:: neg_lit ls1_low; r_or]
                          ] in
      (* and r_and_or <-> r_and_or_tl || (r_or && ls2_high) *)
      let cs_and_or := [::
                          [:: neg_lit r_or; neg_lit ls2_high; r_and_or];
                          [:: r_or; r_and_or_tl; neg_lit r_and_or];
                          [:: ls2_high; r_and_or_tl; neg_lit r_and_or];
                          [:: neg_lit r_and_or_tl; r_and_or]
                       ] in
      (g3, cs_tl ++ cs_prefix_or ++ cs_and_or, r_or, r_and_or)
  else
    fun _ _ =>
      (g, [::], lit_ff, lit_ff).

Fixpoint mk_env_umulo_rec w E (g: generator) : w.-tuple literal -> w.-tuple literal -> env * generator * cnf * literal * literal:=
  if w is w'.+1 then
    fun ls1 ls2 =>
      let (ls1_hightl, ls1_low) := eta_expand (splitlsb ls1) in
      let (ls2_high, ls2_lowtl) := eta_expand (splitmsb ls2) in
      let '(E_rec, g1, cs_tl, r_or_tl, r_and_or_tl) := mk_env_umulo_rec E g ls1_hightl ls2_lowtl in
      let (g2, r_or) := gen g1 in
      let (g3, r_and_or) := gen g2 in
      (* or sum  r_or <-> r_or_tl || ls1_low *)
      let E' := env_upd E_rec (var_of_lit r_or) (
                          interp_lit E_rec r_or_tl ||
                          interp_lit E_rec ls1_low
                        ) in
      let cs_prefix_or := [::
                             [:: neg_lit r_or_tl; r_or];
                             [:: r_or_tl; ls1_low; neg_lit r_or];
                             [:: neg_lit ls1_low; r_or]
                          ] in
      let E'' := env_upd E' (var_of_lit r_and_or) (
                           interp_lit E' r_and_or_tl ||
                           (interp_lit E' r_or && interp_lit E' ls2_high)
                         ) in
      (* and r_and_or <-> r_and_or_tl || (r_or && ls2_high) *)
      let cs_and_or := [::
                          [:: neg_lit r_or; neg_lit ls2_high; r_and_or];
                          [:: r_or; r_and_or_tl; neg_lit r_and_or];
                          [:: ls2_high; r_and_or_tl; neg_lit r_and_or];
                          [:: neg_lit r_and_or_tl; r_and_or]
                       ] in
      (E'', g3, cs_tl ++ cs_prefix_or ++ cs_and_or, r_or, r_and_or)
  else
    fun _ _ =>
      (E, g, [::], lit_ff, lit_ff).

Fixpoint orb_all w : BITS w -> bool :=
  if w is w'.+1 then
    fun ls =>
      let (ls_hightl, ls_low) := eta_expand (splitlsb ls) in
      let result_tl := orb_all ls_hightl in
      orb result_tl ls_low
  else
    fun _ =>
      false.

Example test_orb:
  orb_all [tuple false ; true ;true] = true.
Proof. reflexivity. Qed.

Example test_orb2:
  orb_all [tuple false ; false ; false] = false.
Proof. reflexivity. Qed.

Lemma bit_blast_umulo_rec_correct1 :
  forall w g (bs1 bs2 : BITS w) E ls1 ls2 g' cs lr_or lr_and_or,
    bit_blast_umulo_rec g ls1 ls2 = (g', cs, lr_or, lr_and_or) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr_or (orb_all bs1).
Proof.
  elim.
  - move=> g bs1 bs2 E ls1 ls2 g' cs lr_or lr_and_or.
    rewrite (lock interp_cnf) /=. case=> _ _ <- _.
    rewrite -lock. move=> _ _. exact: add_prelude_enc_bit_ff.
  - move=> w IH g.
    move=> /tupleP [bs1_hd bs1_tl] bs2 E.
    move=> /tupleP [ls1_hd ls1_tl] ls2 g' cs lr_or lr_and_or.
    rewrite /bit_blast_umulo_rec -/bit_blast_umulo_rec. rewrite (lock interp_cnf).
    case Hmsb_ls2 : (splitmsb ls2) => [last_ls2 prefix_ls2].
    case Hmsb_bs2 : (splitmsb bs2) => [last_bs2 prefix_bs2].
    rewrite (lock enc_bits) /=.
    rewrite !beheadCons !theadCons.
    dcase (bit_blast_umulo_rec g ls1_tl prefix_ls2) => [[[[g3 cs_tl] r_or_tl] r_and_or_tl] Hblast].
    case=> Hog <- Holr _ . rewrite -lock. move=> Henc1 Henc2.
    rewrite /= !beheadCons !theadCons in Henc1.
    move: Henc1 => /andP [Hels1_hd Hels1_tl].
    rewrite enc_bits_splitmsb in Henc2.
    rewrite !Hmsb_ls2 !Hmsb_bs2 /= in Henc2.
    move: Henc2 => /andP [Hels2_hd Hels2_tl].
    rewrite -lock.
    rewrite !add_prelude_append. move/andP => [Hicnf_tl Hicnf].
    rewrite /add_prelude !interp_cnf_cons !interp_clause_cons in Hicnf.
    move: (add_prelude_tt Hicnf_tl) => Htt.
    rewrite !Htt /= !orbF interp_lit_neg_lit in Hicnf.
    move: (IH _ _ _ _ _ _ _ _ _ _ Hblast Hels1_tl Hels2_tl Hicnf_tl).
    move=> Henc_tl. rewrite -Holr.
    move: Hicnf Henc_tl Hels1_hd Hels1_tl Hels2_hd Hels2_tl.
    rewrite /enc_bit !interp_lit_neg_lit.
    rewrite /=.
      by case (interp_lit E r_or_tl);
        case (orb_all bs1_tl);
        case (E g3);
        case (interp_lit E ls1_hd);
        case (interp_lit E last_ls2);
        case (interp_lit E r_and_or_tl);
        case (E (g3+1)%positive).
Qed.


Fixpoint andb_orb_all w : BITS w -> BITS w -> bool :=
  if w is w'.+1 then
    fun ls1 ls2 =>
      let (ls1_hightl, ls1_low) := eta_expand (splitlsb ls1) in
      let (ls2_high, ls2_low_tl) := eta_expand (splitmsb ls2) in
      let result_tl := andb_orb_all ls1_hightl ls2_low_tl in
      let result_or := orb_all ls1 in
      orb result_tl (andb result_or ls2_high)
  else
    fun _ _ =>
      false.

Lemma bit_blast_umulo_rec_correct2 :
  forall w g (bs1 bs2 : BITS w) E ls1 ls2 g' cs lr_or lr_and_or,
    bit_blast_umulo_rec g ls1 ls2 = (g', cs, lr_or, lr_and_or) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr_and_or (andb_orb_all bs1 bs2).
Proof.
  elim.
  - move=> g bs1 bs2 E ls1 ls2 g' cs lr_or lr_and_or.
    rewrite (lock interp_cnf) /=. case=> _ _ _ <- .
    rewrite -lock. move=> _ _. exact: add_prelude_enc_bit_ff.
  - move=> w IH g.
    move=> /tupleP [bs1_hd bs1_tl] bs2 E.
    move=> /tupleP [ls1_hd ls1_tl] ls2 g' cs lr_or lr_and_or.
    rewrite /bit_blast_umulo_rec -/bit_blast_umulo_rec. rewrite (lock interp_cnf).
    case Hmsb_ls2 : (splitmsb ls2) => [last_ls2 prefix_ls2].
    case Hmsb_bs2 : (splitmsb bs2) => [last_bs2 prefix_bs2].
    rewrite (lock enc_bits) /=.
    rewrite !beheadCons !theadCons.
    dcase (bit_blast_umulo_rec g ls1_tl prefix_ls2) => [[[[g3 cs_tl] r_or_tl] r_and_or_tl] Hblast].
    case=> Hog <- _ Holr_and_or . rewrite -lock. move=> Henc1 Henc2.
    rewrite /= !beheadCons !theadCons in Henc1.
    move: Henc1 => /andP [Hels1_hd Hels1_tl].
    rewrite enc_bits_splitmsb in Henc2.
    rewrite !Hmsb_ls2 !Hmsb_bs2 /= in Henc2.
    move: Henc2 => /andP [Hels2_hd Hels2_tl].
    rewrite  !Hmsb_bs2 /=.
    rewrite -lock.
    rewrite !add_prelude_append. move/andP => [Hicnf_tl Hicnf].
    rewrite /add_prelude !interp_cnf_cons !interp_clause_cons in Hicnf.
    move: (add_prelude_tt Hicnf_tl) => Htt.
    rewrite !Htt /= !orbF interp_lit_neg_lit in Hicnf.
    move: (IH _ _ _ _ _ _ _ _ _ _ Hblast Hels1_tl Hels2_tl Hicnf_tl).
    move=> Henc_tl. rewrite -Holr_and_or.
    move: (bit_blast_umulo_rec_correct1 Hblast Hels1_tl Hels2_tl Hicnf_tl).
    move: Hicnf Henc_tl Hels1_hd Hels1_tl Hels2_hd Hels2_tl.
    rewrite /enc_bit !interp_lit_neg_lit.
    rewrite /=.
    case H1: (interp_lit E r_or_tl);
      case H2: (interp_lit E r_and_or_tl);
      case H3: (andb_orb_all bs1_tl prefix_bs2);
      case H4: (E g3);
      case H5: (interp_lit E ls1_hd);
      case H6: (interp_lit E last_ls2);
      case H7: (orb_all bs1_tl);
      case H8: (E (g3+1)%positive).
    all: try done; rewrite /=.
    all: by move=> _ _ /eqP <- _ /eqP <- _ _ .
Qed.


Lemma bit_blast_umulo_rec_correct :
  forall w g (bs1 bs2 : BITS w) E ls1 ls2 g' cs lr_or lr_and_or,
    bit_blast_umulo_rec g ls1 ls2 = (g', cs, lr_or, lr_and_or) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr_or (orb_all bs1) /\
    enc_bit E lr_and_or (andb_orb_all bs1 bs2).
Proof.
  move=> w g bs1 bs2 E ls1 ls2 g' cs lr_or lr_and_or.
  move=> Hblast Henc1 Henc2 Hicnf.
  split.
  - exact: (bit_blast_umulo_rec_correct1 Hblast Henc1 Henc2 Hicnf).
  - exact: (bit_blast_umulo_rec_correct2 Hblast Henc1 Henc2 Hicnf).
Qed.


Lemma mk_env_umulo_rec_is_bit_blast_umulo_rec :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr_or lr_and_or,
    mk_env_umulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    bit_blast_umulo_rec g ls1 ls2 = (g', cs, lr_or, lr_and_or).
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr_or lr_and_or /=; intro; dcase_hyps; subst; done.
  -
    move=> w IH E g ls1 ls2 E' g' cs lr_or lr_and_or.
    rewrite /mk_env_umulo_rec /bit_blast_umulo_rec.
    rewrite -/mk_env_umulo_rec. rewrite -/bit_blast_umulo_rec.
    case Hlsb_ls1 : (splitlsb ls1) => [ls1_high ls1_low].
    case Hmsb_ls2 : (splitmsb ls2) => [last_ls2 prefix_ls2].
    rewrite /=.
    dcase (mk_env_umulo_rec E g ls1_high prefix_ls2) => [[[[[E_rec g3] cs_tl] r_or_tl] r_and_or_tl] Henv].
    rewrite (IH _ _ _ _ _ _ _ _ _ Henv).
      by case=> _ <- <- <- <-.
Qed.

Lemma mk_env_umulo_rec_newer_gen :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr_or lr_and_or,
    mk_env_umulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    (g <=? g')%positive.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr_or lr_and_or /=. case=> _ <- _ _ _. exact: Pos.leb_refl.
  - move=> w IH E g ls1 ls2 E' g' cs lr_or lr_and_or.
    rewrite /mk_env_umulo_rec -/mk_env_umulo_rec /gen.
    case Hlsb_ls1 : (splitlsb ls1) => [ls1_high ls1_low].
    case Hmsb_ls2 : (splitmsb ls2) => [last_ls2 prefix_ls2].
    rewrite /=.
    dcase (mk_env_umulo_rec E g ls1_high prefix_ls2) => [[[[[E_rec g3] cs_tl] r_or_tl] r_and_or_tl] Henv].
    case=> _ <- _ _ _ .
    specialize (IH _ _ _ _ _ _ _ _ _ Henv).
    apply pos_leb_trans with g3. exact: IH.
    eapply pos_leb_trans.
    exact: (pos_leb_add_diag_r _ 1).
    exact: (pos_leb_add_diag_r _ 1).
Qed.


Lemma mk_env_umulo_rec_newer_res :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr_or lr_and_or,
    mk_env_umulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g' lr_or /\ newer_than_lit g' lr_and_or.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lor_or lr_and_or /=. by case=> _ <- _ <- <-.
  - move=> w IH E g ls1 ls2 E' g' cs lr_or lr_and_or.
    rewrite /mk_env_umulo_rec -/mk_env_umulo_rec /gen.
    case Hlsb_ls1 : (splitlsb ls1) => [ls1_high ls1_low].
    case Hmsb_ls2 : (splitmsb ls2) => [last_ls2 prefix_ls2].
    rewrite /=.
    dcase (mk_env_umulo_rec E g ls1_high prefix_ls2) => [[[[[E_rec g3] cs_tl] r_or_tl] r_and_or_tl] Henv].
    case=> _ <- _ <- <- => Hgtt.
    rewrite /newer_than_lit /newer_than_var /=.
    move: (mk_env_umulo_rec_newer_gen Henv) => Hg2g3.
    have Hgtg2 : (g3 <? (g3+1+1))%positive.
    apply pos_ltb_trans with (g3+1)%positive.
    exact: (pos_ltb_add_diag_r _ 1).
    exact: (pos_ltb_add_diag_r _ 1).
    rewrite (Hgtg2).
    rewrite (pos_ltb_add_diag_r _ 1).
    done.
Qed.


Lemma mk_env_umulo_rec_newer_cnf :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr_or lr_and_or,
    mk_env_umulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lor_or lr_and_or /=. by case=> _ <- <- _ _.
  - move=> w IH E g ls1 ls2 E' g' cs lr_or lr_and_or.
    rewrite /mk_env_umulo_rec -/mk_env_umulo_rec /gen.
    case Hlsb_ls1 : (splitlsb ls1) => [ls1_high ls1_low].
    case Hmsb_ls2 : (splitmsb ls2) => [last_ls2 prefix_ls2].
    rewrite /=.
    dcase (mk_env_umulo_rec E g ls1_high prefix_ls2) => [[[[[E_rec g3] cs_tl] r_or_tl] r_and_or_tl] Henv].
    case=> _ <- <- _ _ => Hgtt Hgls1 Hgls2.
    have Hgtg2 : (g3 <=? (g3+1+1))%positive.
    apply pos_leb_trans with (g3+1)%positive.
    exact: (pos_leb_add_diag_r _ 1).
    exact: (pos_leb_add_diag_r _ 1).
    rewrite !newer_than_cnf_append.
    move: (newer_than_lits_splitlsb Hgls1 Hlsb_ls1) => /andP [H1 H2].
    move: (newer_than_lits_splitmsb Hgls2 Hmsb_ls2) => /andP [Hg_ls2last Hg_ls2prefix].
    move: (IH _ _ _ _ _ _ _ _ _ Henv Hgtt H1 Hg_ls2prefix) => tmp.
    rewrite (newer_than_cnf_le_newer tmp Hgtg2).
    rewrite !newer_than_cnf_cons /=.
    move: (mk_env_umulo_rec_newer_res Henv Hgtt) => [Hnew1 Hnew2].
    move: (newer_than_lit_le_newer Hnew1 Hgtg2) => {Hnew1} Hnew1.
    move: (newer_than_lit_le_newer Hnew2 Hgtg2) => {Hnew2} Hnew2.
    rewrite !newer_than_lit_neg !Hnew1 !Hnew2.
    move: (mk_env_umulo_rec_newer_gen Henv) => Hgg3.
    move: (pos_leb_trans Hgg3 Hgtg2) => Hgg32.
    rewrite !(newer_than_lit_le_newer H2 Hgg32).
    rewrite !(newer_than_lit_le_newer Hg_ls2last Hgg32).
    rewrite /newer_than_lit /newer_than_var /=.
    have Hgttg2 : (g3 <? (g3+1+1))%positive.
    apply pos_ltb_trans with (g3+1)%positive.
    exact: (pos_ltb_add_diag_r _ 1).
    exact: (pos_ltb_add_diag_r _ 1).
    rewrite !Hgttg2 /var_of_lit /=.
      by rewrite (pos_ltb_add_diag_r _ 1).
Qed.

Lemma mk_env_umulo_rec_preserve :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr_or lr_and_or,
    mk_env_umulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    env_preserve E E' g.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lor_or lr_and_or /=. by case=> <- _ _ _ _.
  - move=> w IH E g ls1 ls2 E' g' cs lr_or lr_and_or.
    rewrite /mk_env_umulo_rec -/mk_env_umulo_rec /gen.
    case Hlsb_ls1 : (splitlsb ls1) => [ls1_high ls1_low].
    case Hmsb_ls2 : (splitmsb ls2) => [last_ls2 prefix_ls2].
    rewrite /=.
    dcase (mk_env_umulo_rec E g ls1_high prefix_ls2) => [[[[[E_rec g3] cs_tl] r_or_tl] r_and_or_tl] Henv].
    case => <- _ _ _ _.
    specialize (IH _ _ _ _ _ _ _ _ _ Henv).
    move: (mk_env_umulo_rec_newer_gen Henv) => Hgg3.
    remember (interp_lit E_rec r_or_tl || interp_lit E_rec ls1_low) as val.
    remember (interp_lit (env_upd E_rec g3 val) r_and_or_tl
              || env_upd E_rec g3 val g3 && interp_lit (env_upd E_rec g3 val) last_ls2) as val2.
    eapply env_preserve_trans. exact: IH.
    have Hpre2 : (env_preserve E_rec (env_upd E_rec g3 val) g).
    {
      apply: env_preserve_le.
      exact: env_upd_eq_preserve.
      exact Hgg3.
    }
    eapply env_preserve_trans. exact: Hpre2.
    apply: env_upd_newer_preserve.
    rewrite /newer_than_var /=.
    eapply pos_leb_ltb_trans. exact: Hgg3.
    exact: (pos_ltb_add_diag_r g3 1).
Qed.

Lemma mk_env_umulo_rec_sat :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr_or lr_and_or,
    mk_env_umulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->  newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lor_or lr_and_or /=. by case=> <- _ <- _ _.
  - move=> w IH E g ls1 ls2 E' g' cs lr_or lr_and_or.
    rewrite /mk_env_umulo_rec -/mk_env_umulo_rec /gen.
    case Hlsb_ls1 : (splitlsb ls1) => [ls1_high ls1_low].
    case Hmsb_ls2 : (splitmsb ls2) => [last_ls2 prefix_ls2].
    rewrite /=.
    dcase (mk_env_umulo_rec E g ls1_high prefix_ls2) => [[[[[E_rec g3] cs_tl] r_or_tl] r_and_or_tl] Henv].
    remember (interp_lit E_rec r_or_tl || interp_lit E_rec ls1_low) as val.
    remember (interp_lit (env_upd E_rec g3 val) r_and_or_tl
              || env_upd E_rec g3 val g3 && interp_lit (env_upd E_rec g3 val) last_ls2) as val2.
    case => Hoe _ <- _ _ => Hgtt Hgls1 Hgls2.
    move: (newer_than_lits_splitlsb Hgls1 Hlsb_ls1) => /andP [Hg_ls1high Hg_ls1low].
    move: (newer_than_lits_splitmsb Hgls2 Hmsb_ls2) => /andP [Hg_ls2last Hg_ls2prefix].
    move: (IH _ _ _ _ _ _ _ _ _ Henv Hgtt Hg_ls1high Hg_ls2prefix) => tmp.
    move: (mk_env_umulo_rec_newer_cnf Henv Hgtt Hg_ls1high Hg_ls2prefix) => tmp2.
    move: (mk_env_umulo_rec_preserve Henv) => Hpre_rec.
    have Hpre3: env_preserve E_rec (env_upd E_rec g3 val) g3.
    exact: env_upd_eq_preserve.
    have Hpre2: env_preserve E_rec E' g3.
    {
      rewrite -Hoe.
      eapply env_preserve_trans. exact: Hpre3.
      eapply env_upd_newer_preserve.
      exact: (pos_ltb_add_diag_r _ 1).
    }
    have Hpre4: env_preserve (env_upd E_rec g3 val) E' g3.
    {
      rewrite -Hoe.
      eapply env_preserve_le.
      exact: env_upd_eq_preserve.
      exact: (pos_leb_add_diag_r _ 1).
    }
    rewrite -(env_preserve_cnf Hpre2 tmp2) in tmp.
    rewrite !interp_cnf_append.
    rewrite tmp andTb => {tmp tmp2}.
    rewrite !Heqval !Heqval2 in Hoe.
    rewrite !interp_cnf_cons !interp_clause_cons !interp_lit_neg_lit /=.
    rewrite !env_upd_eq in Hoe.
    move: (mk_env_umulo_rec_newer_res Henv Hgtt) => [Hnew1 Hnew2].
    have He1: E' g3 = val.
    {
      rewrite -Hoe Heqval.
      rewrite env_upd_neq.  rewrite env_upd_eq. reflexivity.
      apply newer_than_var_neq.
      exact: (pos_ltb_add_diag_r _ 1).
    }
    have He2: E' (g3+1)%positive = val2.
    {
      rewrite -Hoe Heqval2.
      rewrite !env_upd_eq. reflexivity.
    }
    rewrite Heqval in He1.
    rewrite Heqval2 in He2.
    (* rewrite env_upd_eq in He2. *)
    move: (mk_env_umulo_rec_newer_gen Henv) => Hgg3.
    move: (newer_than_lit_le_newer Hg_ls2last Hgg3) => Hg3_ls2last.
    move: (newer_than_lit_le_newer Hg_ls1low Hgg3) => Hg3_ls1low.
    rewrite (env_preserve_lit Hpre4 Hg3_ls2last).
    rewrite (env_preserve_lit Hpre4 Hg3_ls1low).
    rewrite (env_preserve_lit Hpre4 Hnew1).
    rewrite (env_preserve_lit Hpre4 Hnew2).
    rewrite -(env_preserve_lit Hpre3 Hnew1) in He1.
    rewrite -(env_preserve_lit Hpre3 Hg3_ls1low) in He1.
    rewrite !He1 !He2.
    rewrite !env_upd_eq.
    case H1 :(interp_lit (env_upd E_rec g3 val) last_ls2);
      case H2 :(interp_lit (env_upd E_rec g3 val) ls1_low);
      case H3 :(interp_lit (env_upd E_rec g3 val) r_and_or_tl);
      case H4 :(interp_lit (env_upd E_rec g3 val) r_or_tl).
    all:try done.
    all: rewrite !Heqval.
    all: rewrite -(env_preserve_lit Hpre3 Hnew1);
      rewrite -(env_preserve_lit Hpre3 Hg3_ls1low).
    all: rewrite H2 H4.
    all: done.
Qed.

(* r <-> ls1 * ls2  >= 2^w *)
Definition bit_blast_umulo w (g: generator) : w.-tuple literal -> w.-tuple literal -> generator * cnf * literal:=
  if w is w'.+1 then
    fun ls1 ls2 =>
      let (ls1_hightl, ls1_low) := eta_expand (splitlsb ls1) in
      let (ls2_hightl, ls2_low) := eta_expand (splitlsb ls2) in
      let '(g_wls1, cs_wls1, lrs_wls1) := bit_blast_zeroextend 1 g ls1 in
      let '(g_wls2, cs_wls2, lrs_wls2) := bit_blast_zeroextend 1 g_wls1 ls2 in
      let '(g_rec1, cs_rec1, r_or_rec1, r_or_and_rec1) := bit_blast_umulo_rec g_wls2 ls1_hightl ls2_hightl in
      let '(g_mul, cs_mul, lrs_mul) := bit_blast_mul g_rec1 lrs_wls1 lrs_wls2 in
      let lrs_msb := last lit_ff lrs_mul in
      let (g_r, r) := gen g_mul in
      let cs := [::
                   [:: neg_lit r_or_and_rec1; r];
                   [:: r_or_and_rec1; lrs_msb; neg_lit r];
                   [:: neg_lit lrs_msb; r]
                ] in
      (g_r, cs_rec1 ++ cs_wls1 ++ cs_wls2 ++ cs_mul ++ cs, r)
  else
    fun _ _ =>
      (g, [::], lit_ff).

Definition mk_env_umulo w E (g: generator) : w.-tuple literal -> w.-tuple literal -> env * generator * cnf * literal:=
  if w is w'.+1 then
    fun ls1 ls2 =>
      let (ls1_hightl, ls1_low) := eta_expand (splitlsb ls1) in
      let (ls2_hightl, ls2_low) := eta_expand (splitlsb ls2) in
      let '(E_wls1, g_wls1, cs_wls1, lrs_wls1) := mk_env_zeroextend 1 E g ls1 in
      let '(E_wls2, g_wls2, cs_wls2, lrs_wls2) := mk_env_zeroextend 1 E_wls1 g_wls1 ls2 in
      let '(E_rec, g_rec, cs_rec, r_or_rec, r_or_and_rec) := mk_env_umulo_rec E_wls2 g_wls2 ls1_hightl ls2_hightl in
      let '(E_mul, g_mul, cs_mul, lrs_mul) := mk_env_mul E_rec g_rec lrs_wls1 lrs_wls2 in
      let lrs_msb := last lit_ff lrs_mul in
      let (g_r, r) := gen g_mul in
      let E' := env_upd E_mul (var_of_lit r) (
                          (interp_lit E_mul r_or_and_rec) ||
                          (interp_lit E_mul lrs_msb)
                        ) in
      let cs := [::
                   [:: neg_lit r_or_and_rec; r];
                   [:: r_or_and_rec; lrs_msb; neg_lit r];
                   [:: neg_lit lrs_msb; r]
                ] in
      (E', g_r, cs_rec ++ cs_wls1 ++ cs_wls2 ++ cs_mul ++ cs, r)
  else
    fun _ _ =>
      (E, g, [::], lit_ff).

Definition Umulo w : BITS w -> BITS w -> bool :=
  if w is w'.+1 then
    fun bs1 bs2 =>
      let (bs1_hightl, bs1_low) := eta_expand (splitlsb bs1) in
      let (bs2_hightl, bs2_low) := eta_expand (splitlsb bs2) in
      let wbs1 := zeroExtend 1 bs1 in
      let wbs2 := zeroExtend 1 bs2 in
      let mul := mulB wbs1 wbs2 in
      let mul_high := msb mul in
      orb (andb_orb_all bs1_hightl bs2_hightl) mul_high
  else
    fun _ _ =>
      false.

Definition mul_overflow w (bs1 bs2: BITS w): bool :=
  high w (mulB (zeroExtend w bs1) (zeroExtend w bs2)) != #0 .

Lemma Umulo_equiv_mul_overflow:
  forall w (bs1 bs2: BITS w),
    Umulo bs1 bs2 = mul_overflow bs1 bs2.
Admitted.


Lemma bit_blast_umulo_correct :
  forall w g (bs1 bs2 : BITS w) E ls1 ls2 g' cs lr,
    bit_blast_umulo g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (mul_overflow bs1 bs2).
Proof.
  elim.
  - move=> g bs1 bs2 E ls1 ls2 g' cs lr.
    rewrite - (Umulo_equiv_mul_overflow bs1 bs2).
    rewrite /Umulo. rewrite /bit_blast_umulo.
    case=> _ <- <-.
    rewrite (tuple0 bs1) (tuple0 bs2).
    move => _ _ Hicnf.
    exact: add_prelude_enc_bit_ff Hicnf.
  - move=> w IH g.
    move=> bs1 bs2 E ls1 ls2 g' cs lr.
    rewrite - (Umulo_equiv_mul_overflow bs1 bs2).
    rewrite /bit_blast_umulo /gen.
    dcase (bit_blast_zeroextend 1 g ls1) => [[[g_wls1 cs_wls1] lrs_wls1] Hblast_wls1].
    dcase (bit_blast_zeroextend 1 g_wls1 ls2) => [[[g_wls2 cs_wls2] lrs_wls2] Hblast_wls2].
    move=> H Henc1 Henc2.
    move: H.
    rewrite (lock interp_cnf).
    rewrite /Umulo.
    case Hls1 : (splitlsb ls1) => [ls1_hightl ls1_low].
    case Hls2 : (splitlsb ls2) => [ls2_hightl ls2_low].
    case Hbs1 : (splitlsb bs1) => [bs1_hightl bs1_low].
    case Hbs2 : (splitlsb bs2) => [bs2_hightl bs2_low].
    rewrite /=.
    dcase (bit_blast_umulo_rec g_wls2 ls1_hightl ls2_hightl) => [[[[g_rec cs_rec] r_or_rec] r_or_and_rec] Hblast_rec].
    dcase (bit_blast_mul g_rec lrs_wls1 lrs_wls2) => [[[g_mul cs_mul] lrs_mul] Hblast_mul].
    case=> _ <- <-.
    rewrite -lock.
    move: (Henc1) => Henc1'.
    move: (Henc2) => Henc2'.
    rewrite !enc_bits_splitlsb in Henc1' Henc2'.
    rewrite !Hls1 !Hbs1 /= in Henc1'.
    rewrite !Hls2 !Hbs2 /= in Henc2'.
    move/andP: Henc1' => [Hels1_low Hels1_hightl].
    move/andP: Henc2' => [Hels2_low Hels2_hightl].
    rewrite !add_prelude_append.
    move /andP => [Hicnf_rec /andP [Hicnf_wls1 /andP [Hicnf_wls2 /andP [Hicnf_mul Hicnf]]]].
    rewrite /add_prelude in Hicnf. rewrite !interp_cnf_cons !interp_clause_cons in Hicnf.
    rewrite /Umulo.
    move: (bit_blast_umulo_rec_correct Hblast_rec Hels1_hightl Hels2_hightl Hicnf_rec) => [_ Handb_correct].
    rewrite /enc_bit.
    move: (@bit_blast_zeroextend_correct (w.+1) 1 bs1 E ls1 cs_wls1 Henc1 Hicnf_wls1).
    move: (@bit_blast_zeroextend_correct (w.+1) 1 bs2 E ls2 cs_wls2 Henc2 Hicnf_wls2).
    move=> Henc_ze2 Henc_ze1.
    move: Hblast_wls1 Hblast_wls2.
    rewrite /bit_blast_zeroextend.
    case=> _ Hcs_wls1 Hlrs_wls1.
    case=> _ Hcs_wls2 Hlrs_wls2.
    rewrite -Hlrs_wls1 -Hlrs_wls2 in Hblast_mul.
    move: (bit_blast_mul_correct Hblast_mul Henc_ze1 Henc_ze2 Hicnf_mul).
    move=> Hmul_correct.
    rewrite /msb.
    move: (add_prelude_tt Hicnf_rec) => Htt.
    rewrite Htt in Hicnf.
    rewrite !interp_lit_neg_lit /= in Hicnf.
    replace (interp_lit E (Pos g)) with (E g) by done.
    move: (enc_bits_last false lit_ff Hmul_correct).
    move: Handb_correct Hmul_correct Hicnf.
    rewrite /enc_bit.
    case H1 :(interp_lit E r_or_and_rec);
      case H2: (E g_mul);
      case H3: (interp_lit E (last lit_ff lrs_mul));
      case H4: (andb_orb_all bs1_hightl bs2_hightl);
      case H5: (interp_lit E (Pos g_mul)); try done.
    all: rewrite /= H2 in H5; discriminate.
Qed.

Lemma mk_env_umulo_is_bit_blast_umulo :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_umulo E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_umulo g ls1 ls2 = (g', cs, lr).
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr /=. by case=> _ <- <- <-.
  - move=> w IH E g ls1 ls2 E' g' cs lr.
    rewrite /mk_env_umulo /bit_blast_umulo.
    case Hls1 : (splitlsb ls1) => [ls1_hightl ls1_low].
    case Hls2 : (splitlsb ls2) => [ls2_hightl ls2_low].
    rewrite (lock bit_blast_zeroextend) (lock mk_env_zeroextend )/=.
    rewrite -lock -lock.
    dcase (mk_env_zeroextend 1 E g ls1) => [[[[E_wls1 g_wls1] cs_wls1] lrs_wls1] Henv_z1].
    dcase (mk_env_zeroextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] lrs_wls2] Henv_z2].
    rewrite (mk_env_zeroextend_is_bit_blast_zeroextend Henv_z1).
    rewrite (mk_env_zeroextend_is_bit_blast_zeroextend Henv_z2).
    dcase (mk_env_umulo_rec E_wls2 g_wls2 ls1_hightl ls2_hightl) => [[[[[E_rec g_rec] cs_rec] r_or_rec] r_or_and_rec] Henv_rec].
    dcase (mk_env_mul E_rec g_rec lrs_wls1 lrs_wls2) => [[[[E_mul g_mul] cs_mul] lrs_mul] Henv_mul].
    rewrite (mk_env_umulo_rec_is_bit_blast_umulo_rec Henv_rec).
    rewrite (mk_env_mul_is_bit_blast_mul Henv_mul).
    case=> _ <- <- <-.
    done.
Qed.

Lemma mk_env_umulo_newer_gen :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_umulo E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr /=. case=> _ <- _ _. exact: Pos.leb_refl.
  - move=> w IH E g ls1 ls2 E' g' cs lr.
    rewrite /mk_env_umulo.
    case Hls1 : (splitlsb ls1) => [ls1_hightl ls1_low].
    case Hls2 : (splitlsb ls2) => [ls2_hightl ls2_low].
    rewrite (lock mk_env_zeroextend) /=.
    rewrite -lock.
    dcase (mk_env_zeroextend 1 E g ls1) => [[[[E_wls1 g_wls1] cs_wls1] lrs_wls1] Henv_z1].
    dcase (mk_env_zeroextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] lrs_wls2] Henv_z2].
    dcase (mk_env_umulo_rec E_wls2 g_wls2 ls1_hightl ls2_hightl) => [[[[[E_rec g_rec] cs_rec] r_or_rec] r_or_and_rec] Henv_rec].
    dcase (mk_env_mul E_rec g_rec lrs_wls1 lrs_wls2) => [[[[E_mul g_mul] cs_mul] lrs_mul] Henv_mul].
    case=> _ <- _ _.
    move: (mk_env_zeroextend_newer_gen Henv_z1) => tmp.
    apply (pos_leb_trans (mk_env_zeroextend_newer_gen Henv_z1)).
    apply (pos_leb_trans (mk_env_zeroextend_newer_gen Henv_z2)).
    apply (pos_leb_trans (mk_env_umulo_rec_newer_gen Henv_rec)).
    apply (pos_leb_trans (mk_env_mul_newer_gen Henv_mul)).
    exact: (pos_leb_add_diag_r _ 1).
Qed.

Lemma mk_env_umulo_newer_res :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_umulo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g' lr.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr /=. case=> _ <- _ <-. done.
  - move=> w IH E g ls1 ls2 E' g' cs lr.
    rewrite /mk_env_umulo.
    case Hls1 : (splitlsb ls1) => [ls1_hightl ls1_low].
    case Hls2 : (splitlsb ls2) => [ls2_hightl ls2_low].
    rewrite (lock mk_env_zeroextend) /=.
    rewrite -lock.
    dcase (mk_env_zeroextend 1 E g ls1) => [[[[E_wls1 g_wls1] cs_wls1] lrs_wls1] Henv_z1].
    dcase (mk_env_zeroextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] lrs_wls2] Henv_z2].
    dcase (mk_env_umulo_rec E_wls2 g_wls2 ls1_hightl ls2_hightl) => [[[[[E_rec g_rec] cs_rec] r_or_rec] r_or_and_rec] Henv_rec].
    dcase (mk_env_mul E_rec g_rec lrs_wls1 lrs_wls2) => [[[[E_mul g_mul] cs_mul] lrs_mul] Henv_mul].
    case=> _ <- _ <- => Hgtt.
    exact: (pos_ltb_add_diag_r _ 1).
Qed.


Lemma mk_env_umulo_newer_cnf :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_umulo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr /=. case=> _ <- <- _. done.
  - move=> w IH E g ls1 ls2 E' g' cs lr.
    rewrite /mk_env_umulo.
    case Hls1 : (splitlsb ls1) => [ls1_hightl ls1_low].
    case Hls2 : (splitlsb ls2) => [ls2_hightl ls2_low].
    rewrite (lock mk_env_zeroextend) /=.
    rewrite -lock.
    dcase (mk_env_zeroextend 1 E g ls1) => [[[[E_wls1 g_wls1] cs_wls1] lrs_wls1] Henv_wls1].
    dcase (mk_env_zeroextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] lrs_wls2] Henv_wls2].
    dcase (mk_env_umulo_rec E_wls2 g_wls2 ls1_hightl ls2_hightl) => [[[[[E_rec g_rec] cs_rec] r_or_rec] r_or_and_rec] Henv_rec].
    dcase (mk_env_mul E_rec g_rec lrs_wls1 lrs_wls2) => [[[[E_mul g_mul] cs_mul] lrs_mul] Henv_mul].
    case=> _ <- <- _ => Hnew_gtt Hnew_gls1 Hnew_gls2.
    rewrite !newer_than_cnf_append.
    move: (mk_env_zeroextend_newer_gen Henv_wls1) => H_gls1.
    move: (mk_env_zeroextend_newer_gen Henv_wls2) => H_gls12.
    move: (mk_env_umulo_rec_newer_gen Henv_rec) => H_gls2rec.
    move: (mk_env_mul_newer_gen Henv_mul) => H_grecmul.
    move: (pos_leb_add_diag_r g_mul 1) => H_gmul1.
    move: (pos_leb_trans H_grecmul H_gmul1) => H_grecgmul1.
    move: (pos_leb_trans H_gls2rec H_grecgmul1) => H_gls2mul1.
    move: (pos_leb_trans H_gls12 H_gls2mul1) => H_gls1mul1.
    move: (mk_env_zeroextend_newer_cnf Henv_wls1 Hnew_gtt Hnew_gls1) => Hnew_gwls1_wls1.
    rewrite (newer_than_cnf_le_newer Hnew_gwls1_wls1 H_gls1mul1).
    move: (newer_than_lit_le_newer Hnew_gtt H_gls1) => Hnew_ggls1_gtt.
    move: (newer_than_lits_le_newer Hnew_gls1 H_gls1) => Hnew_ggls1_gls1.
    move: (newer_than_lits_le_newer Hnew_gls2 H_gls1) => Hnew_ggls1_gls2.
    move: (mk_env_zeroextend_newer_cnf Henv_wls2 Hnew_ggls1_gtt Hnew_ggls1_gls2) => Hnew_gwls2_wls2.
    rewrite (newer_than_cnf_le_newer Hnew_gwls2_wls2 H_gls2mul1).
    move: (newer_than_lit_le_newer Hnew_ggls1_gtt H_gls12) => Hnew_ggls2_gtt.
    move: (newer_than_lits_le_newer Hnew_ggls1_gls1 H_gls12) => Hnew_ggls2_gls1.
    move: (newer_than_lits_le_newer Hnew_ggls1_gls2 H_gls12) => Hnew_ggls2_gls2.
    move: (mk_env_zeroextend_newer_res Henv_wls1 Hnew_gtt Hnew_gls1) => H_gls1_lrs1.
    move: (newer_than_lits_le_newer H_gls1_lrs1 H_gls12) => H_gls2_lrs1.
    move: (mk_env_zeroextend_newer_res Henv_wls2 Hnew_ggls1_gtt Hnew_ggls1_gls2) => H_gls2_lrs2.
    move: (newer_than_lits_splitlsb Hnew_ggls2_gls1 Hls1) => /andP [Hnew_ggls2_ls1high Hnew_ggls2_ls1low].
    move: (newer_than_lits_splitlsb Hnew_ggls2_gls2 Hls2) => /andP [Hnew_ggls2_ls2high Hnew_ggls2_ls2low].
    move: (mk_env_umulo_rec_newer_cnf Henv_rec Hnew_ggls2_gtt Hnew_ggls2_ls1high Hnew_ggls2_ls2high) => Hnew_rec.
    rewrite (newer_than_cnf_le_newer Hnew_rec H_grecgmul1).
    move: (newer_than_lits_le_newer H_gls2_lrs1 H_gls2rec) => tmp.
    move: (newer_than_lits_le_newer H_gls2_lrs2 H_gls2rec) => tmp2.
    move: (newer_than_lit_le_newer Hnew_ggls2_gtt H_gls2rec) => tmp3.
    move: (mk_env_mul_newer_cnf Henv_mul tmp3 tmp tmp2) => Hnew_mul.
    rewrite (newer_than_cnf_le_newer Hnew_mul H_gmul1).
    rewrite /=.
    rewrite !newer_than_lit_neg.
    move: (mk_env_umulo_rec_newer_res Henv_rec Hnew_ggls2_gtt) => [_ Hand].
    rewrite (newer_than_lit_le_newer Hand H_grecgmul1).
    move: (mk_env_mul_newer_res Henv_mul tmp3) => tmp4.
    move: (newer_than_lits_last lit_ff tmp4) => tmp5.
    rewrite (newer_than_lit_le_newer tmp5 H_gmul1).
    rewrite /newer_than_lit /newer_than_var /=.
    rewrite (pos_ltb_add_diag_r g_mul 1).
    done.
Qed.

Lemma mk_env_umulo_preserve :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_umulo E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr /=. case=> <- _ _ _. done.
  - move=> w IH E g ls1 ls2 E' g' cs lr.
    rewrite /mk_env_umulo /gen.
    case Hls1 : (splitlsb ls1) => [ls1_hightl ls1_low].
    case Hls2 : (splitlsb ls2) => [ls2_hightl ls2_low].
    rewrite (lock mk_env_zeroextend) /=.
    rewrite -lock.
    dcase (mk_env_zeroextend 1 E g ls1) => [[[[E_wls1 g_wls1] cs_wls1] lrs_wls1] Henv_wls1].
    dcase (mk_env_zeroextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] lrs_wls2] Henv_wls2].
    dcase (mk_env_umulo_rec E_wls2 g_wls2 ls1_hightl ls2_hightl) => [[[[[E_rec g_rec] cs_rec] r_or_rec] r_or_and_rec] Henv_rec].
    dcase (mk_env_mul E_rec g_rec lrs_wls1 lrs_wls2) => [[[[E_mul g_mul] cs_mul] lrs_mul] Henv_mul].
    case=> <- _ _ _.
    move: (mk_env_zeroextend_newer_gen Henv_wls1) => H_ggls1.
    move: (mk_env_zeroextend_newer_gen Henv_wls2) => H_ggls12.
    move: (mk_env_umulo_rec_newer_gen Henv_rec) => H_ggls2rec.
    move: (mk_env_mul_newer_gen Henv_mul) => H_ggrecmul.
    move: (pos_leb_trans H_ggls1 H_ggls12) => H_gls2.
    move: (pos_leb_trans H_gls2 H_ggls2rec) => H_grec.
    move: (pos_leb_trans H_grec H_ggrecmul) => H_gmul.
    move: (mk_env_zeroextend_preserve Henv_wls1) => Hpre1.
    move: (mk_env_zeroextend_preserve Henv_wls2) => Hpre2.
    move: (mk_env_umulo_rec_preserve Henv_rec) => Hpre3.
    move: (mk_env_mul_preserve Henv_mul) => Hpre4.
    move: (env_preserve_le Hpre2 H_ggls1) => {Hpre2} Hpre2.
    move: (env_preserve_le Hpre3 H_gls2) => {Hpre3} Hpre3.
    move: (env_preserve_le Hpre4 H_grec) => {Hpre4} Hpre4.
    (* move: (env_preserve_le Hpre5 H_ghigh) => {Hpre5} Hpre5. *)
    (* move: (env_preserve_le Hpre6 H_gzero) => {Hpre6} Hpre6. *)
    apply env_preserve_trans with E_mul.
    apply env_preserve_trans with E_rec.
    apply env_preserve_trans with E_wls2.
    apply env_preserve_trans with E_wls1.
    all: try done.
    eapply env_preserve_le.
    exact: env_upd_eq_preserve.
    exact: H_gmul.
Qed.

Lemma mk_env_umulo_sat :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_umulo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->  newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr /=. case=> <- _ <- _. done.
  - move=> w IH E g ls1 ls2 E' g' cs lr.
    rewrite /mk_env_umulo /gen.
    case Hls1 : (splitlsb ls1) => [ls1_hightl ls1_low].
    case Hls2 : (splitlsb ls2) => [ls2_hightl ls2_low].
    rewrite (lock mk_env_zeroextend) /=.
    rewrite -lock.
    dcase (mk_env_zeroextend 1 E g ls1) => [[[[E_wls1 g_wls1] cs_wls1] lrs_wls1] Henv_wls1].
    dcase (mk_env_zeroextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] lrs_wls2] Henv_wls2].
    dcase (mk_env_umulo_rec E_wls2 g_wls2 ls1_hightl ls2_hightl) => [[[[[E_rec g_rec] cs_rec] r_or_rec] r_or_and_rec] Henv_rec].
    dcase (mk_env_mul E_rec g_rec lrs_wls1 lrs_wls2) => [[[[E_mul g_mul] cs_mul] lrs_mul] Henv_mul].
    case=> <- _ <- _ => Hnew_gtt Hnew_gls1 Hnew_gls2.
    rewrite !interp_cnf_append.
    move: (mk_env_zeroextend_newer_gen Henv_wls1) => H_ggls1.
    move: (mk_env_zeroextend_newer_gen Henv_wls2) => H_ggls12.
    move: (mk_env_umulo_rec_newer_gen Henv_rec) => H_ggls2rec.
    move: (mk_env_mul_newer_gen Henv_mul) => H_grecmul.
    move: (pos_leb_add_diag_r g_mul 1) => H_gmul1.
    move: (mk_env_zeroextend_preserve Henv_wls1) => Hpre_wls1.
    move: (mk_env_zeroextend_preserve Henv_wls2) => Hpre_wls2.
    move: (mk_env_umulo_rec_preserve Henv_rec) => Hpre_rec.
    move: (mk_env_mul_preserve Henv_mul) => Hpre_mul.
    remember (env_upd E_mul g_mul
           (interp_lit E_mul r_or_and_rec || interp_lit E_mul (last lit_ff lrs_mul))) as Ef.
    have Hpre_Ef : (env_preserve E_mul Ef g_mul).
    {
      rewrite HeqEf.
      exact: env_upd_eq_preserve.
    }
    (* wls1 *)
    move: (mk_env_zeroextend_sat Henv_wls1 Hnew_gtt Hnew_gls1) => Hicnf_ls1_ls1.
    move: (mk_env_zeroextend_newer_cnf Henv_wls1 Hnew_gtt Hnew_gls1) => Hncnf_ls1_ls1.
    move: (newer_than_cnf_le_newer Hncnf_ls1_ls1 H_ggls12) => Hncnf_ls2_ls1.
    move: (newer_than_cnf_le_newer Hncnf_ls2_ls1 H_ggls2rec) => Hncnf_rec_ls1.
    move: (newer_than_cnf_le_newer Hncnf_rec_ls1 H_grecmul) => Hncnf_mul_ls1.
    rewrite (env_preserve_cnf Hpre_Ef Hncnf_mul_ls1).
    rewrite (env_preserve_cnf Hpre_mul Hncnf_rec_ls1).
    rewrite (env_preserve_cnf Hpre_rec Hncnf_ls2_ls1).
    rewrite (env_preserve_cnf Hpre_wls2 Hncnf_ls1_ls1).
    rewrite Hicnf_ls1_ls1 andTb.
    move=> {Hncnf_ls2_ls1 Hncnf_mul_ls1 Hncnf_ls1_ls1}.
    (* wls2 *)
    move: (newer_than_lit_le_newer Hnew_gtt H_ggls1) => Hnew_gls1tt.
    move: (newer_than_lits_le_newer Hnew_gls1 H_ggls1) => Hnew_gls1ls1.
    move: (newer_than_lits_le_newer Hnew_gls2 H_ggls1) => Hnew_gls1ls2.
    move: (mk_env_zeroextend_sat Henv_wls2 Hnew_gls1tt Hnew_gls1ls2) => Hicnf_ls2_ls2.
    move: (mk_env_zeroextend_newer_cnf Henv_wls2 Hnew_gls1tt Hnew_gls1ls2) => Hncnf_ls2_ls2.
    move: (newer_than_cnf_le_newer Hncnf_ls2_ls2 H_ggls2rec) => Hncnf_rec_ls2.
    move: (newer_than_cnf_le_newer Hncnf_rec_ls2 H_grecmul) => Hncnf_mul_ls2.
    rewrite (env_preserve_cnf Hpre_Ef Hncnf_mul_ls2).
    rewrite (env_preserve_cnf Hpre_mul Hncnf_rec_ls2).
    rewrite (env_preserve_cnf Hpre_rec Hncnf_ls2_ls2).
    rewrite Hicnf_ls2_ls2 andTb.
    move=> {Hncnf_ls2_ls2 Hncnf_mul_ls2 Hicnf_ls1_ls1 Hicnf_ls2_ls2}.
    (* rec *)
    move: (newer_than_lit_le_newer Hnew_gls1tt H_ggls12) => Hnew_gls2tt.
    move: (newer_than_lits_le_newer Hnew_gls1ls1 H_ggls12) => Hnew_gls2ls1.
    move: (newer_than_lits_le_newer Hnew_gls1ls2 H_ggls12) => Hnew_gls2ls2.
    move: (mk_env_zeroextend_newer_res Henv_wls1 Hnew_gtt Hnew_gls1) => Hnew_gls1_lrs1.
    move: (newer_than_lits_le_newer Hnew_gls1_lrs1 H_ggls12) => Hnew_gls2_lrs1.
    move: (mk_env_zeroextend_newer_res Henv_wls2 Hnew_gls1tt Hnew_gls1ls2) => Hnew_gls2_lrs2.
    move: (newer_than_lits_splitlsb Hnew_gls2ls1 Hls1) => /andP [Hnew_gls2ls1_high Hnew_gls2ls1_low].
    move: (newer_than_lits_splitlsb Hnew_gls2ls2 Hls2) => /andP [Hnew_gls2ls2_high Hnew_gls2ls2_low].
    move: (mk_env_umulo_rec_sat Henv_rec Hnew_gls2tt Hnew_gls2ls1_high Hnew_gls2ls2_high) => Hicnf_rec_rec.
    move: (mk_env_umulo_rec_newer_cnf Henv_rec Hnew_gls2tt Hnew_gls2ls1_high Hnew_gls2ls2_high) => Hncnf_rec_rec.
    move: (newer_than_cnf_le_newer Hncnf_rec_rec H_grecmul) => Hncnf_mul_rec.
    rewrite (env_preserve_cnf Hpre_Ef Hncnf_mul_rec).
    rewrite (env_preserve_cnf Hpre_mul Hncnf_rec_rec).
    rewrite Hicnf_rec_rec andTb.
    move=> {Hncnf_rec_rec Hncnf_mul_rec Hicnf_rec_rec}.
    (* mul *)
    move: (newer_than_lit_le_newer Hnew_gls2tt H_ggls2rec) => Hnew_grectt.
    move: (newer_than_lits_le_newer Hnew_gls2_lrs1 H_ggls2rec) => Hnew_grec_lrs1.
    move: (newer_than_lits_le_newer Hnew_gls2_lrs2 H_ggls2rec) => Hnew_grec_lrs2.
    move: (mk_env_mul_sat Henv_mul Hnew_grectt Hnew_grec_lrs1 Hnew_grec_lrs2) => Hicnf_mul_mul.
    move: (mk_env_mul_newer_cnf Henv_mul Hnew_grectt Hnew_grec_lrs1 Hnew_grec_lrs2) => Hncnf_mul_mul.
    rewrite (env_preserve_cnf Hpre_Ef Hncnf_mul_mul).
    rewrite Hicnf_mul_mul andTb.
    move => {Hicnf_mul_mul Hncnf_mul_mul}.
    rewrite !interp_cnf_cons !interp_clause_cons !interp_lit_neg_lit /=.
    move: (mk_env_umulo_rec_newer_res Henv_rec Hnew_gls2tt) => [_ Hand].
    move: (newer_than_lit_le_newer Hand H_grecmul) => {Hand} Hand.
    rewrite (env_preserve_lit Hpre_Ef Hand).
    move: (mk_env_mul_newer_res Henv_mul Hnew_grectt) => H.
    move: (newer_than_lits_last lit_ff H) => H2.
    rewrite (env_preserve_lit Hpre_Ef H2).
    rewrite HeqEf. rewrite !env_upd_eq.
    by case :(interp_lit E_mul r_or_and_rec);
      case :(interp_lit E_mul (last lit_ff lrs_mul)).
Qed.

(*
Definition bit_blast_umulo w (g: generator) (ls1 ls2:  w.-tuple literal) :generator * cnf * literal:=
  let '(g_wls1, cs_wls1, lrs_wls1) := @bit_blast_zeroextend w w g ls1 in
  let '(g_wls2, cs_wls2, lrs_wls2) := @bit_blast_zeroextend w w g_wls1 ls2 in
  let '(g_mul, cs_mul, lrs_mul) := bit_blast_mul g_wls2 lrs_wls1 lrs_wls2 in
  let '(g_high, cs_high, lrs_high) := @bit_blast_high w w g_mul lrs_mul in
  let '(g_zero, cs_zero, lrs_zero) := @bit_blast_const w g_high (# 0) in
  let '(g_safe, cs_safe, lr_safe) := bit_blast_eq g_zero lrs_high lrs_zero in
  (g_safe, cs_wls1 ++ cs_wls2 ++ cs_mul ++ cs_high ++ cs_zero ++ cs_safe, neg_lit lr_safe).

Definition mk_env_umulo w E (g: generator) (ls1 ls2:  w.-tuple literal) : env * generator * cnf * literal:=
  let '(E_wls1, g_wls1, cs_wls1, lrs_wls1) := @mk_env_zeroextend w w E g ls1 in
  let '(E_wls2, g_wls2, cs_wls2, lrs_wls2) := @mk_env_zeroextend w w E_wls1 g_wls1 ls2 in
  let '(E_mul, g_mul, cs_mul, lrs_mul) := mk_env_mul E_wls2 g_wls2 lrs_wls1 lrs_wls2 in
  let '(E_high, g_high, cs_high, lrs_high) := @mk_env_high w w E_mul g_mul lrs_mul in
  let '(E_zero, g_zero, cs_zero, lrs_zero) := @mk_env_const w E_high g_high (# 0) in
  let '(E_safe, g_safe, cs_safe, lr_safe) := mk_env_eq E_zero g_zero lrs_high lrs_zero in
  (E_safe, g_safe, cs_wls1 ++ cs_wls2 ++ cs_mul ++ cs_high ++ cs_zero ++ cs_safe, neg_lit lr_safe).

Definition mul_overflow w (bs1 bs2: BITS w): bool :=
  high w (mulB (zeroExtend w bs1) (zeroExtend w bs2)) != #0 .

Lemma bit_blast_umulo_correct :
  forall w g (bs1 bs2 : BITS w) E ls1 ls2 br g' cs lr,
    bit_blast_umulo g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    br = mul_overflow bs1 bs2 ->
    enc_bit E lr br.
Proof.
  move=> w g bs1 bs2 E ls1 ls2 br g' cs lr.
  rewrite /bit_blast_umulo.
  dcase (bit_blast_zeroextend w g ls1) => [[[g_wls1 cs_wls1] lrs_wls1] Hblast_wls1].
  dcase (bit_blast_zeroextend w g_wls1 ls2) => [[[g_wls2 cs_wls2] lrs_wls2] Hblast_wls2].
  dcase (bit_blast_mul g_wls2 lrs_wls1 lrs_wls2) => [[[g_mul cs_mul] lrs_mul] Hblast_mul].
  dcase (bit_blast_high g_mul lrs_mul) => [[[g_high cs_high] lrs_high] Hblast_high].
  dcase (@bit_blast_const w g_high #0) => [[[g_zero cs_zero] lrs_zero] Hblast_zero].
  dcase (bit_blast_eq g_zero lrs_high lrs_zero) => [[[g_safe cs_safe] lr_safe] Hblast_safe].
  case => _ <- <- => Henc1 Henc2 Hicnf ->.
  rewrite enc_bit_not.
  rewrite /mul_overflow.
  move: Hblast_wls1 Hblast_wls2 Hblast_high. rewrite /bit_blast_zeroextend /bit_blast_high.
  case => _ Hcs_wls1 Heq_wls1. case => _ Hcs_wls2 Heq_wls2. case=> _ Hcs_high Heq_high.
  rewrite !add_prelude_append in Hicnf.
  split_andb.
  move: (@bit_blast_zeroextend_correct w w bs1 E ls1 cs_safe Henc1 H4).
  move: (@bit_blast_zeroextend_correct w w bs2 E ls2 cs_safe Henc2 H4).
  rewrite Heq_wls1 Heq_wls2 =>  Henc_wls2 Henc_wls1.
  move: (bit_blast_mul_correct Hblast_mul Henc_wls1 Henc_wls2 H1) => Henc_mul.
  move: (bit_blast_const_correct Hblast_zero H3) => Henc_zero.
  move: (@bit_blast_high_correct w w _ E _ _ Henc_mul H2).
  rewrite Heq_high => Henc_high.
  move: (bit_blast_eq_correct Hblast_safe Henc_high Henc_zero H4) => Henc_safe.
  rewrite /enc_bit in Henc_safe.
  rewrite /enc_bit.
  rewrite interp_lit_neg_involutive.
  case Hsafe: (interp_lit E lr_safe);
    case Hsafe2: (high w (mulB (zeroExtend w bs1) (zeroExtend w bs2)) == # (0));
    try done; try by rewrite Hsafe Hsafe2 in Henc_safe.
Qed.

Lemma mk_env_umulo_is_bit_blast_umulo :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_umulo E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_umulo g ls1 ls2 = (g', cs, lr).
Proof.
  rewrite /mk_env_umulo /bit_blast_umulo.
  move=> w E g ls1 ls2 E' g' cs lr.
  move=>H. dcase_hyps. subst.
  rewrite (mk_env_zeroextend_is_bit_blast_zeroextend H).
  rewrite (mk_env_zeroextend_is_bit_blast_zeroextend H1).
  rewrite (mk_env_mul_is_bit_blast_mul H0).
  rewrite (mk_env_high_is_bit_blast_high H2).
  rewrite (mk_env_const_is_bit_blast_const H3).
  rewrite (mk_env_eq_is_bit_blast_eq H4).
  done.
Qed.

Lemma mk_env_umulo_newer_gen :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_umulo E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  rewrite /mk_env_umulo.
  move=> w E g ls1 ls2 E' g' cs lr.
  dcase_goal.
  case=> _ <- _ _.
  move: (mk_env_zeroextend_newer_gen H) => tmp.
  apply (pos_leb_trans (mk_env_zeroextend_newer_gen H)).
  apply (pos_leb_trans (mk_env_zeroextend_newer_gen H0)).
  apply (pos_leb_trans (mk_env_mul_newer_gen H1)).
  apply (pos_leb_trans (mk_env_high_newer_gen H2)).
  apply (pos_leb_trans (mk_env_const_newer_gen H3)).
  exact: (mk_env_eq_newer_gen H4).
Qed.

Lemma mk_env_umulo_newer_res :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_umulo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g' lr.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr.
  rewrite /mk_env_umulo.
  dcase (mk_env_zeroextend w E g ls1) => [[[[E_wls1 g_wls1] cs_wls1] lrs_wls1] Henv_wls1].
  dcase (mk_env_zeroextend w E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] lrs_wls2] Henv_wls2].
  dcase (mk_env_mul E_wls2 g_wls2 lrs_wls1 lrs_wls2) => [[[[E_mul g_mul] cs_mul] lrs_mul] Henv_mul].
  dcase (mk_env_high E_mul g_mul lrs_mul) => [[[[E_high g_high] cs_high] lrs_high] Henv_high].
  dcase (@mk_env_const w E_high g_high #0) => [[[[E_zero g_zero] cs_zero] lrs_zero] Henv_zero].
  dcase (mk_env_eq E_zero g_zero lrs_high lrs_zero) => [[[[E_safe g_safe] cs_safe] lr_safe] Henv_safe].
  case => _ <- _ <-.
  move: (mk_env_eq_newer_res Henv_safe).
    by rewrite newer_than_lit_neg.
Qed.

Lemma mk_env_umulo_newer_cnf :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_umulo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr.
  rewrite /mk_env_umulo.
  dcase (mk_env_zeroextend w E g ls1) => [[[[E_wls1 g_wls1] cs_wls1] lrs_wls1] Henv_wls1].
  dcase (mk_env_zeroextend w E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] lrs_wls2] Henv_wls2].
  dcase (mk_env_mul E_wls2 g_wls2 lrs_wls1 lrs_wls2) => [[[[E_mul g_mul] cs_mul] lrs_mul] Henv_mul].
  dcase (mk_env_high E_mul g_mul lrs_mul) => [[[[E_high g_high] cs_high] lrs_high] Henv_high].
  dcase (@mk_env_const w E_high g_high #0) => [[[[E_zero g_zero] cs_zero] lrs_zero] Henv_zero].
  dcase (mk_env_eq E_zero g_zero lrs_high lrs_zero) => [[[[E_safe g_safe] cs_safe] lr_safe] Henv_safe].
  case => _ <- <- _. move=> Hnew_gtt Hnew_gls1 Hnew_gls2.
  rewrite !newer_than_cnf_append.
  move: (mk_env_zeroextend_newer_gen Henv_wls1) => H_ggls1.
  move: (mk_env_zeroextend_newer_gen Henv_wls2) => H_ggls12.
  move: (mk_env_mul_newer_gen Henv_mul) => H_ggls2mul.
  move: (mk_env_high_newer_gen Henv_high) => H_mulhigh.
  move: (mk_env_const_newer_gen Henv_zero) => H_highzero.
  move: (mk_env_eq_newer_gen Henv_safe) => H_zerosafe.
  move: (pos_leb_trans H_highzero H_zerosafe) => H_highsafe.
  move: (pos_leb_trans H_mulhigh H_highsafe) => H_mulsafe.
  move: (pos_leb_trans H_ggls2mul H_mulsafe) => H_ggls2safe.
  move: (pos_leb_trans H_ggls12 H_ggls2safe) => H_ggls1safe.
  move: (mk_env_zeroextend_newer_cnf Henv_wls1 Hnew_gtt Hnew_gls1) => Hnew_gwls1_wls1.
  rewrite (newer_than_cnf_le_newer Hnew_gwls1_wls1 H_ggls1safe).
  move: (newer_than_lit_le_newer Hnew_gtt H_ggls1) => Hnew_ggls1_gtt.
  move: (newer_than_lits_le_newer Hnew_gls1 H_ggls1) => Hnew_ggls1_gls1.
  move: (newer_than_lits_le_newer Hnew_gls2 H_ggls1) => Hnew_ggls1_gls2.
  move: (mk_env_zeroextend_newer_cnf Henv_wls2 Hnew_ggls1_gtt Hnew_ggls1_gls2) => Hnew_gwls2_wls2.
  rewrite (newer_than_cnf_le_newer Hnew_gwls2_wls2 H_ggls2safe).
  move: (newer_than_lit_le_newer Hnew_ggls1_gtt H_ggls12) => Hnew_ggls2_gtt.
  move: (newer_than_lits_le_newer Hnew_ggls1_gls1 H_ggls12) => Hnew_ggls2_gls1.
  move: (newer_than_lits_le_newer Hnew_ggls1_gls2 H_ggls12) => Hnew_ggls2_gls2.
  move: (mk_env_zeroextend_newer_res Henv_wls1 Hnew_gtt Hnew_gls1) => H_gls1_lrs1.
  move: (newer_than_lits_le_newer H_gls1_lrs1 H_ggls12) => H_gls2_lrs1.
  move: (mk_env_zeroextend_newer_res Henv_wls2 Hnew_ggls1_gtt Hnew_ggls1_gls2) => H_gls2_lrs2.
  move: (mk_env_mul_newer_cnf Henv_mul Hnew_ggls2_gtt H_gls2_lrs1 H_gls2_lrs2) => Hnew_mul.
  rewrite (newer_than_cnf_le_newer Hnew_mul H_mulsafe).
  move: (mk_env_mul_newer_res Henv_mul Hnew_ggls2_gtt) => H.
  move: (newer_than_lit_le_newer Hnew_ggls2_gtt H_ggls2mul) => H2.
  move: (mk_env_high_newer_cnf Henv_high H2 H)  => Hnew_high.
  rewrite (newer_than_cnf_le_newer Hnew_high H_highsafe).
  move: (newer_than_lit_le_newer H2 H_mulhigh) => H3.
  move: (mk_env_const_newer_cnf Henv_zero H3) => Hnew_zero.
  rewrite (newer_than_cnf_le_newer Hnew_zero H_zerosafe).
  move: (mk_env_eq_newer_cnf Henv_safe).
  move: (mk_env_const_newer_res Henv_zero H3) => H4.
  move: (mk_env_high_newer_res Henv_high H2 H) => H5.
  move: (newer_than_lits_le_newer H5 H_highzero) => H6.
  move=> tmp.
    by rewrite (tmp H6 H4).
Qed.

Lemma mk_env_umulo_preserve :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_umulo E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr.
  rewrite /mk_env_umulo.
  dcase (mk_env_zeroextend w E g ls1) => [[[[E_wls1 g_wls1] cs_wls1] lrs_wls1] Henv_wls1].
  dcase (mk_env_zeroextend w E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] lrs_wls2] Henv_wls2].
  dcase (mk_env_mul E_wls2 g_wls2 lrs_wls1 lrs_wls2) => [[[[E_mul g_mul] cs_mul] lrs_mul] Henv_mul].
  dcase (mk_env_high E_mul g_mul lrs_mul) => [[[[E_high g_high] cs_high] lrs_high] Henv_high].
  dcase (@mk_env_const w E_high g_high #0) => [[[[E_zero g_zero] cs_zero] lrs_zero] Henv_zero].
  dcase (mk_env_eq E_zero g_zero lrs_high lrs_zero) => [[[[E_safe g_safe] cs_safe] lr_safe] Henv_safe].
  case=> <- _ _ _ .
  move: (mk_env_zeroextend_newer_gen Henv_wls1) => H_ggls1.
  move: (mk_env_zeroextend_newer_gen Henv_wls2) => H_ggls12.
  move: (mk_env_mul_newer_gen Henv_mul) => H_ggls2mul.
  move: (mk_env_high_newer_gen Henv_high) => H_mulhigh.
  move: (mk_env_const_newer_gen Henv_zero) => H_highzero.
  move: (mk_env_eq_newer_gen Henv_safe) => H_zerosafe.
  move: (pos_leb_trans H_ggls1 H_ggls12) => H_gls2.
  move: (pos_leb_trans H_gls2 H_ggls2mul) => H_gmul.
  move: (pos_leb_trans H_gmul H_mulhigh) => H_ghigh.
  move: (pos_leb_trans H_ghigh H_highzero) => H_gzero.
  move: (pos_leb_trans H_gzero H_zerosafe) => H_gsafe.
  move: (mk_env_zeroextend_preserve Henv_wls1) => Hpre1.
  move: (mk_env_zeroextend_preserve Henv_wls2) => Hpre2.
  move: (mk_env_mul_preserve Henv_mul) => Hpre3.
  move: (mk_env_high_preserve Henv_high) => Hpre4.
  move: (mk_env_const_preserve Henv_zero) => Hpre5.
  move: (mk_env_eq_preserve Henv_safe) => Hpre6.
  move: (env_preserve_le Hpre2 H_ggls1) => {Hpre2} Hpre2.
  move: (env_preserve_le Hpre3 H_gls2) => {Hpre3} Hpre3.
  move: (env_preserve_le Hpre4 H_gmul) => {Hpre4} Hpre4.
  move: (env_preserve_le Hpre5 H_ghigh) => {Hpre5} Hpre5.
  move: (env_preserve_le Hpre6 H_gzero) => {Hpre6} Hpre6.
  apply env_preserve_trans with E_zero.
  apply env_preserve_trans with E_high.
  apply env_preserve_trans with E_mul.
  apply env_preserve_trans with E_wls2.
  apply env_preserve_trans with E_wls1.
  all: done.
Qed.

Lemma mk_env_umulo_sat :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_umulo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->  newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr.
  rewrite /mk_env_umulo.
  dcase (mk_env_zeroextend w E g ls1) => [[[[E_wls1 g_wls1] cs_wls1] lrs_wls1] Henv_wls1].
  dcase (mk_env_zeroextend w E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] lrs_wls2] Henv_wls2].
  dcase (mk_env_mul E_wls2 g_wls2 lrs_wls1 lrs_wls2) => [[[[E_mul g_mul] cs_mul] lrs_mul] Henv_mul].
  dcase (mk_env_high E_mul g_mul lrs_mul) => [[[[E_high g_high] cs_high] lrs_high] Henv_high].
  dcase (@mk_env_const w E_high g_high #0) => [[[[E_zero g_zero] cs_zero] lrs_zero] Henv_zero].
  dcase (mk_env_eq E_zero g_zero lrs_high lrs_zero) => [[[[E_safe g_safe] cs_safe] lr_safe] Henv_safe].
  case=> <- _ <- _.
  move=> Hnew_gtt Hnew_gls1 Hnew_gls2.
  rewrite !interp_cnf_append.
  move: (mk_env_zeroextend_newer_gen Henv_wls1) => H_ggls1.
  move: (mk_env_zeroextend_newer_gen Henv_wls2) => H_ggls12.
  move: (mk_env_mul_newer_gen Henv_mul) => H_ggls2mul.
  move: (mk_env_high_newer_gen Henv_high) => H_mulhigh.
  move: (mk_env_const_newer_gen Henv_zero) => H_highzero.
  move: (mk_env_eq_newer_gen Henv_safe) => H_zerosafe.
  move: (mk_env_zeroextend_preserve Henv_wls1) => Hpre_wls1.
  move: (mk_env_zeroextend_preserve Henv_wls2) => Hpre_wls2.
  move: (mk_env_mul_preserve Henv_mul) => Hpre_mul.
  move: (mk_env_high_preserve Henv_high) => Hpre_high.
  move: (mk_env_const_preserve Henv_zero) => Hpre_zero.
  move: (mk_env_eq_preserve Henv_safe) => Hpre_safe.
  (* wls1 *)
  move: (mk_env_zeroextend_sat Henv_wls1 Hnew_gtt Hnew_gls1) => Hicnf_ls1_ls1.
  move: (mk_env_zeroextend_newer_cnf Henv_wls1 Hnew_gtt Hnew_gls1) => Hncnf_ls1_ls1.
  move: (newer_than_cnf_le_newer Hncnf_ls1_ls1 H_ggls12) => Hncnf_ls2_ls1.
  move: (newer_than_cnf_le_newer Hncnf_ls2_ls1 H_ggls2mul) => Hncnf_mul_ls1.
  move: (newer_than_cnf_le_newer Hncnf_mul_ls1 H_mulhigh) => Hncnf_high_ls1.
  move: (newer_than_cnf_le_newer Hncnf_high_ls1 H_highzero) => Hncnf_zero_ls1.
  rewrite (env_preserve_cnf Hpre_safe Hncnf_zero_ls1).
  rewrite (env_preserve_cnf Hpre_zero Hncnf_high_ls1).
  rewrite (env_preserve_cnf Hpre_high Hncnf_mul_ls1).
  rewrite (env_preserve_cnf Hpre_mul Hncnf_ls2_ls1).
  rewrite (env_preserve_cnf Hpre_wls2 Hncnf_ls1_ls1).
  rewrite Hicnf_ls1_ls1 andTb.
  move=> {Hncnf_high_ls1 Hncnf_ls2_ls1 Hncnf_mul_ls1 Hncnf_zero_ls1 Hncnf_ls1_ls1}.
  (* wls2 *)
  move: (newer_than_lit_le_newer Hnew_gtt H_ggls1) => Hnew_gls1tt.
  move: (newer_than_lits_le_newer Hnew_gls2 H_ggls1) => Hnew_gls1ls2.
  move: (mk_env_zeroextend_sat Henv_wls2 Hnew_gls1tt Hnew_gls1ls2) => Hicnf_ls2_ls2.
  move: (mk_env_zeroextend_newer_cnf Henv_wls2 Hnew_gls1tt Hnew_gls1ls2) => Hncnf_ls2_ls2.
  move: (newer_than_cnf_le_newer Hncnf_ls2_ls2 H_ggls2mul) => Hncnf_mul_ls2.
  move: (newer_than_cnf_le_newer Hncnf_mul_ls2 H_mulhigh) => Hncnf_high_ls2.
  move: (newer_than_cnf_le_newer Hncnf_high_ls2 H_highzero) => Hncnf_zero_ls2.
  rewrite (env_preserve_cnf Hpre_safe Hncnf_zero_ls2).
  rewrite (env_preserve_cnf Hpre_zero Hncnf_high_ls2).
  rewrite (env_preserve_cnf Hpre_high Hncnf_mul_ls2).
  rewrite (env_preserve_cnf Hpre_mul Hncnf_ls2_ls2).
  rewrite Hicnf_ls2_ls2 andTb.
  move=> {Hncnf_high_ls2 Hncnf_ls2_ls2 Hncnf_mul_ls2 Hncnf_zero_ls2 Hicnf_ls1_ls1 Hicnf_ls2_ls2}.
  (* mul *)
  move: (newer_than_lit_le_newer Hnew_gls1tt H_ggls12) => Hnew_gls2tt.
  move: (mk_env_zeroextend_newer_res Henv_wls1 Hnew_gtt Hnew_gls1) => Hnew_gls1_lrs1.
  move: (mk_env_zeroextend_newer_res Henv_wls2 Hnew_gls1tt Hnew_gls1ls2) => Hnew_gls2_lrs2.
  move: (newer_than_lits_le_newer Hnew_gls1_lrs1 H_ggls12) => Hnew_gls2_lrs1.
  move: (mk_env_mul_sat Henv_mul Hnew_gls2tt Hnew_gls2_lrs1 Hnew_gls2_lrs2) => Hicnf_mul_mul.
  move: (mk_env_mul_newer_cnf Henv_mul Hnew_gls2tt Hnew_gls2_lrs1 Hnew_gls2_lrs2) => Hncnf_mul_mul.
  move: (newer_than_cnf_le_newer Hncnf_mul_mul H_mulhigh) => Hncnf_high_mul.
  move: (newer_than_cnf_le_newer Hncnf_high_mul H_highzero) => Hncnf_zero_mul.
  rewrite (env_preserve_cnf Hpre_safe Hncnf_zero_mul).
  rewrite (env_preserve_cnf Hpre_zero Hncnf_high_mul).
  rewrite (env_preserve_cnf Hpre_high Hncnf_mul_mul).
  rewrite Hicnf_mul_mul andTb.
  move => {Hicnf_mul_mul Hncnf_mul_mul Hncnf_high_mul Hncnf_zero_mul}.
  (* high *)
  move: (newer_than_lit_le_newer Hnew_gls2tt H_ggls2mul) => Hnew_gmultt.
  move: (mk_env_mul_newer_res Henv_mul Hnew_gls2tt) => Hnew_gmul_lsrmul.
  move: (mk_env_high_sat Henv_high Hnew_gmultt Hnew_gmul_lsrmul) => Hinf_high_high.
  move: (mk_env_high_newer_cnf Henv_high Hnew_gmultt Hnew_gmul_lsrmul) => Hncnf_high_high.
  move: (newer_than_cnf_le_newer Hncnf_high_high H_highzero) => Hncnf_zero_high.
  rewrite (env_preserve_cnf Hpre_safe Hncnf_zero_high).
  rewrite (env_preserve_cnf Hpre_zero Hncnf_high_high).
  rewrite Hinf_high_high andTb.
  move => {Hinf_high_high Hncnf_high_high Hncnf_zero_high}.
  (* zero *)
  move: (mk_env_const_sat Henv_zero) => Hicnf_zero_zero.
  move: (newer_than_lit_le_newer Hnew_gmultt H_mulhigh) => Hnew_ghightt.
  move: (mk_env_const_newer_cnf Henv_zero Hnew_ghightt) => Hncnf_zero_zero.
  rewrite (env_preserve_cnf Hpre_safe Hncnf_zero_zero).
  rewrite Hicnf_zero_zero andTb.
  move: (mk_env_const_newer_res Henv_zero Hnew_ghightt) => Hnres_zero_zero.
  move: (mk_env_high_newer_res Henv_high Hnew_gmultt Hnew_gmul_lsrmul) => Hnres_high_high.
  move: (newer_than_lits_le_newer Hnres_high_high H_highzero) => Hnres_zero_high.
  move: (mk_env_eq_sat Henv_safe Hnres_zero_high Hnres_zero_zero).
  done.
Qed.
*)
