From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From BitBlasting Require Import Var QFBV CNF BBCommon BBAnd BBXor BBOr BBSignExtend BBMul BBUmulo.
From ssrlib Require Import ZAriths Tactics Bools Seqs.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section BBSmulo.
  Infix "++r" := catrev (right associativity, at level 60): seq_scope.
  (* ===== bit_blast_smulo ===== *)

  (* ===== smulo_rec is same as umulo_rec *)

  Definition bit_blast_smulo_rec := bit_blast_umulo_rec.

  Definition mk_env_smulo_rec := mk_env_umulo_rec.

  (* orb_all and andb_orb_all defined in Umulo *)

  Lemma bit_blast_smulo_rec_correct g bs1 bs2 E ls1 ls2 g' cs lr_or lr_and_or :
    bit_blast_smulo_rec g ls1 ls2 = (g', cs, lr_or, lr_and_or) ->
    size ls1 == size ls2 ->
    enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr_or (orb_all bs1) && enc_bit E lr_and_or (andb_orb_all bs1 bs2).
  Proof.
    exact: bit_blast_umulo_rec_correct.
  Qed.

  Lemma mk_env_smulo_rec_is_bit_blast_smulo_rec E g ls1 ls2 E' g' cs lr_or lr_and_or:
    mk_env_smulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    bit_blast_smulo_rec g ls1 ls2 = (g', cs, lr_or, lr_and_or).
  Proof.
    exact: mk_env_umulo_rec_is_bit_blast_umulo_rec.
  Qed.

  Lemma mk_env_smulo_rec_newer_gen E g ls1 ls2 E' g' cs lr_or lr_and_or:
    mk_env_smulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    (g <=? g')%positive.
  Proof.
    exact: mk_env_umulo_rec_newer_gen.
  Qed.

  Lemma mk_env_smulo_rec_newer_res E g ls1 ls2 E' g' cs lr_or lr_and_or:
    mk_env_smulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g' lr_or && newer_than_lit g' lr_and_or.
    exact: mk_env_umulo_rec_newer_res.
  Qed.

  Lemma mk_env_smulo_rec_newer_cnf E g ls1 ls2 E' g' cs lr_or lr_and_or:
    mk_env_smulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    size ls1 == size ls2 ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
  Proof.
    exact: mk_env_umulo_rec_newer_cnf.
  Qed.

  Lemma mk_env_smulo_rec_preserve E g ls1 ls2 E' g' cs lr_or lr_and_or:
    mk_env_smulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    env_preserve E E' g.
  Proof.
    exact: mk_env_umulo_rec_preserve.
  Qed.

  Lemma mk_env_smulo_rec_sat E g ls1 ls2 E' g' cs lr_or lr_and_or:
    mk_env_smulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    size ls1 == size ls2 ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
  Proof.
    exact: mk_env_umulo_rec_sat.
  Qed.

  Definition bit_blast_smulo (g: generator) ls1 ls2 : generator * cnf * literal:=
    let (ls1_tl, ls1_sign) := eta_expand (splitmsl ls1) in
    let (ls2_tl, ls2_sign) := eta_expand (splitmsl ls2) in
    let wsign1 := copy (size ls1_tl) ls1_sign in
    let wsign2 := copy (size ls2_tl) ls2_sign in
    let '(g_xls1, cs_xls1, xls1) := bit_blast_xor g ls1_tl wsign1 in
    let '(g_xls2, cs_xls2, xls2) := bit_blast_xor g_xls1 ls2_tl wsign2 in
    let (xls1_low, xls1_hightl) := eta_expand (splitlsl xls1) in
    let (xls2_low, xls2_hightl) := eta_expand (splitlsl xls2) in
    let '(g_rec, cs_rec, r_or_rec, r_or_and_rec) := bit_blast_smulo_rec g_xls2 xls1_hightl xls2_hightl in
    let '(g_wls1, cs_wls1, wls1) := bit_blast_signextend 1 g_rec ls1 in
    let '(g_wls2, cs_wls2, wls2) := bit_blast_signextend 1 g_wls1 ls2 in
    let '(g_mul, cs_mul, mul) := bit_blast_mul g_wls2 wls1 wls2 in
    let (mul_tl, mul_n) := eta_expand (splitmsl mul) in
    let (_, mul_n_minus1) := eta_expand (splitmsl mul_tl) in
    let '(g_xor1, cs_xor1, xor1) := bit_blast_xor1 g_mul mul_n mul_n_minus1 in
    let '(g_or1, cs_or1, or1) := bit_blast_or1 g_xor1 r_or_and_rec xor1 in
    (g_or1, cs_xls1 ++r cs_xls2 ++r cs_rec ++r cs_wls1 ++r cs_wls2  ++r cs_mul ++r cs_xor1 ++r cs_or1, or1).

  Definition mk_env_smulo E (g: generator) ls1 ls2 : env * generator * cnf * literal :=
    let (ls1_tl, ls1_sign) := eta_expand (splitmsl ls1) in
    let (ls2_tl, ls2_sign) := eta_expand (splitmsl ls2) in
    let wsign1 := copy (size ls1_tl) ls1_sign in
    let wsign2 := copy (size ls2_tl) ls2_sign in
    let '(E_xls1, g_xls1, cs_xls1, xls1) := mk_env_xor E g ls1_tl wsign1 in
    let '(E_xls2, g_xls2, cs_xls2, xls2) := mk_env_xor E_xls1 g_xls1 ls2_tl wsign2 in
    let (xls1_low, xls1_hightl) := eta_expand (splitlsl xls1) in
    let (xls2_low, xls2_hightl) := eta_expand (splitlsl xls2) in
    let '(E_rec, g_rec, cs_rec, r_or_rec, r_or_and_rec) := mk_env_smulo_rec E_xls2 g_xls2 xls1_hightl xls2_hightl in
    let '(E_wls1, g_wls1, cs_wls1, wls1) := mk_env_signextend 1 E_rec g_rec ls1 in
    let '(E_wls2, g_wls2, cs_wls2, wls2) := mk_env_signextend 1 E_wls1 g_wls1 ls2 in
    let '(E_mul, g_mul, cs_mul, mul) := mk_env_mul E_wls2 g_wls2 wls1 wls2 in
    let (mul_tl, mul_n) := eta_expand (splitmsl mul) in
    let (_, mul_n_minus1) := eta_expand (splitmsl mul_tl) in
    let '(E_xor1, g_xor1, cs_xor1, xor1) := mk_env_xor1 E_mul g_mul mul_n mul_n_minus1 in
    let '(E_or1, g_or1, cs_or1, or1) := mk_env_or1 E_xor1 g_xor1 r_or_and_rec xor1 in
    (E_or1, g_or1, cs_xls1 ++r cs_xls2 ++r cs_rec ++r cs_wls1 ++r cs_wls2  ++r cs_mul ++r cs_xor1 ++r cs_or1, or1).


  Lemma bit_blast_smulo_correct g bs1 bs2 E ls1 ls2 g' cs lr :
    bit_blast_smulo g ls1 ls2 = (g', cs, lr) ->
    size ls1 == size ls2 ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (Smulo bs1 bs2).
  Proof.
    rewrite /bit_blast_smulo /Smulo.
    rewrite (lock bit_blast_signextend) (lock bit_blast_xor1 )/= -2!lock.
    dcase (bit_blast_xor g (belastd ls1) (copy (size (belastd ls1)) (lastd lit_ff ls1)))
    => [[[g_xls1 cs_xls1] xls1] Hblast_xls1].
    dcase (bit_blast_xor g_xls1 (belastd ls2) (copy (size (belastd ls2)) (lastd lit_ff ls2)))
    => [[[g_xls2 cs_xls2] xls2] Hblast_xls2].
    dcase (bit_blast_smulo_rec g_xls2 (behead xls1) (behead xls2))
    => [[[[g_rec cs_rec] r_or ] r_or_and_rec] Hblast_rec].
    dcase (bit_blast_signextend 1 g_rec ls1) => [[[g_wls1 cs_wls1] wls1] Hblast_wls1].
    dcase (bit_blast_signextend 1 g_wls1 ls2) => [[[g_wls2 cs_wls2] wls2] Hblast_wls2].
    dcase (bit_blast_mul g_wls2 wls1 wls2) => [[[g_mul cs_mul] mul] Hblast_mul].
    dcase (bit_blast_xor1 g_mul (lastd lit_ff mul) (lastd lit_ff (belastd mul)))
    => [[[g_xor1 cs_xor1] xor1] Hblast_xor1].
    dcase (bit_blast_or1 g_xor1 r_or_and_rec xor1) => [[[g_or1 cs_or1] or1] Hblast_or1].
    case => _ <- <- Hsz Henc1 Henc2.
    move: (enc_bits_size Henc1) => Hsz1.
    move: (enc_bits_size Henc2) => Hsz2.
    have HszB : size bs1 == size bs2 by rewrite -Hsz1 -Hsz2 (eqP Hsz).
    rewrite !add_prelude_catrev.
    move=> /andP [Hcnf_xls1 /andP [Hcnf_xls2 /andP [Hcnf_rec /andP [Hcnf_wls1 /andP [Hcnf_wls2 /andP [Hcnf_mul /andP [Hcnf_xor1 Hcnf_or1]]]]]]].
    move: (add_prelude_enc_bit_tt Hcnf_xls1) => Htt.
    rewrite /enc_bit in Htt.
    move/eqP in Htt.
    move: (enc_bits_splitmsb Htt Henc1) => /= /andP [Henc_ls1tl Henc_ls1sign].
    move: (enc_bits_splitmsb Htt Henc2) => /= /andP [Henc_ls2tl Henc_ls2sign].
    move: (enc_bits_copy (size (belastd ls1)) Henc_ls1sign) => Henc_wsign1.
    move: (enc_bits_copy (size (belastd ls2)) Henc_ls2sign) => Henc_wsign2.
    move: (bit_blast_xor_correct Hblast_xls1 Henc_ls1tl Henc_wsign1 Hcnf_xls1) => Henc_xls1.
    move: (bit_blast_xor_correct Hblast_xls2 Henc_ls2tl Henc_wsign2 Hcnf_xls2) => Henc_xls2.
    have Hsz_xls : size (behead xls1) = size (behead xls2).
    {
      rewrite !size_behead /=; f_equal.
      rewrite (enc_bits_size Henc_xls1).
      rewrite (enc_bits_size Henc_xls2).
      move: (size_belastd Hsz) => Hsz_wsign.
      rewrite (eqP Hsz_wsign).
      rewrite /xorB.
      rewrite !size_lift.
      move: (size_belastd HszB) => Hsz_wsignB.
      rewrite (eqP Hsz_wsignB).
      f_equal.
        by rewrite !size_copy.
    }
    move/eqP: Hsz_xls => Hsz_xls.
    move: (enc_bits_splitlsb Htt Henc_xls1) => /= /andP [_ Henc_xls1tl].
    move: (enc_bits_splitlsb Htt Henc_xls2) => /= /andP [_ Henc_xls2tl].
    move: (bit_blast_smulo_rec_correct Hblast_rec Hsz_xls Henc_xls1tl Henc_xls2tl Hcnf_rec)
    => /andP [_ Henc_rec].
    move: (bit_blast_signextend_correct Hblast_wls1 Henc1 Hcnf_wls1) => Henc_wls1.
    move: (bit_blast_signextend_correct Hblast_wls2 Henc2 Hcnf_wls2) => Henc_wls2.
    have Hsz_wls: size wls1 = size wls2.
    {
      rewrite (enc_bits_size Henc_wls1) (enc_bits_size Henc_wls2).
      rewrite /sext !size_cat !size_copy /=.
        by rewrite (eqP HszB).
    }
    move: (bit_blast_mul_correct Hblast_mul Henc_wls1 Henc_wls2 Hcnf_mul Hsz_wls) => Henc_mul.
    move: (enc_bits_splitmsb Htt Henc_mul) => /= /andP [Henc_multl Henc_muln].
    move: (enc_bits_splitmsb Htt Henc_multl) => /= /andP [_ Henc_muln1].
    move: (bit_blast_xor1_correct Hblast_xor1 Henc_muln Henc_muln1 Hcnf_xor1) => Henc_xor1.
    have -> : size (belastd bs1) = size (belastd ls1).
    {
      apply /eqP.
      apply size_belastd.
        by rewrite Hsz1.
    }
    have -> : size (belastd bs2) = size (belastd ls2).
    {
      apply /eqP.
      apply size_belastd.
        by rewrite Hsz2.
    }
    exact: (bit_blast_or1_correct Hblast_or1 Henc_rec Henc_xor1 Hcnf_or1).
  Qed.

  Lemma mk_env_smulo_is_bit_blast_smulo  E g ls1 ls2 E' g' cs lr:
    mk_env_smulo E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_smulo g ls1 ls2 = (g', cs, lr).
  Proof.
    rewrite /mk_env_smulo /bit_blast_smulo.
    rewrite (lock bit_blast_signextend) (lock bit_blast_xor1)
            (lock mk_env_signextend) (lock mk_env_xor1)
            /= -4!lock.
    dcase (mk_env_xor E g (belastd ls1) (copy (size (belastd ls1)) (lastd lit_ff ls1)))
    => [[[ [ E_xls1 g_xls1 ]  cs_xls1] xls1] Henv_xls1].
    dcase (mk_env_xor E_xls1 g_xls1 (belastd ls2) (copy (size (belastd ls2)) (lastd lit_ff ls2)))
    => [[[[ E_xls2 g_xls2] cs_xls2] xls2] Henv_xls2].
    dcase (mk_env_smulo_rec E_xls2 g_xls2 (behead xls1) (behead xls2))
    => [[[[[ E_rec g_rec] cs_rec] r_or ] r_or_and_rec] Henv_rec].
    dcase (mk_env_signextend 1 E_rec g_rec ls1) => [[[[E_wls1 g_wls1] cs_wls1] wls1] Henv_wls1].
    dcase (mk_env_signextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] wls2] Henv_wls2].
    dcase (mk_env_mul E_wls2 g_wls2 wls1 wls2) => [[[[ E_mul g_mul ] cs_mul] mul] Henv_mul].
    dcase (mk_env_xor1 E_mul g_mul (lastd lit_ff mul) (lastd lit_ff (belastd mul)))
    => [[[[ E_xor1 g_xor1 ] cs_xor1] xor1] Henv_xor1].
    dcase (mk_env_or1 E_xor1 g_xor1 r_or_and_rec xor1) => [[[[ E_or1 g_or1 ] cs_or1] or1] Henv_or1].
    rewrite (mk_env_xor_is_bit_blast_xor Henv_xls1).
    rewrite (mk_env_xor_is_bit_blast_xor Henv_xls2).
    rewrite (mk_env_smulo_rec_is_bit_blast_smulo_rec Henv_rec).
    rewrite (mk_env_signextend_is_bit_blast_signextend Henv_wls1).
    rewrite (mk_env_signextend_is_bit_blast_signextend Henv_wls2).
    rewrite (mk_env_mul_is_bit_blast_mul Henv_mul).
    rewrite (mk_env_xor1_is_bit_blast_xor1 Henv_xor1).
    rewrite (mk_env_or1_is_bit_blast_or1 Henv_or1).
      by case=> _ <- <- <-.
  Qed.

  Lemma mk_env_smulo_newer_gen E g ls1 ls2 E' g' cs lr:
    mk_env_smulo E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
  Proof.
    rewrite /mk_env_smulo /bit_blast_smulo.
    rewrite (lock mk_env_signextend) (lock mk_env_xor1) /= -2!lock.
    dcase (mk_env_xor E g (belastd ls1) (copy (size (belastd ls1)) (lastd lit_ff ls1)))
    => [[[ [ E_xls1 g_xls1 ]  cs_xls1] xls1] Henv_xls1].
    dcase (mk_env_xor E_xls1 g_xls1 (belastd ls2) (copy (size (belastd ls2)) (lastd lit_ff ls2)))
    => [[[[ E_xls2 g_xls2] cs_xls2] xls2] Henv_xls2].
    dcase (mk_env_smulo_rec E_xls2 g_xls2 (behead xls1) (behead xls2))
    => [[[[[ E_rec g_rec] cs_rec] r_or ] r_or_and_rec] Henv_rec].
    dcase (mk_env_signextend 1 E_rec g_rec ls1) => [[[[E_wls1 g_wls1] cs_wls1] wls1] Henv_wls1].
    dcase (mk_env_signextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] wls2] Henv_wls2].
    dcase (mk_env_mul E_wls2 g_wls2 wls1 wls2) => [[[[ E_mul g_mul ] cs_mul] mul] Henv_mul].
    dcase (mk_env_xor1 E_mul g_mul (lastd lit_ff mul) (lastd lit_ff (belastd mul)))
    => [[[[ E_xor1 g_xor1 ] cs_xor1] xor1] Henv_xor1].
    dcase (mk_env_or1 E_xor1 g_xor1 r_or_and_rec xor1) => [[[[ E_or1 g_or1 ] cs_or1] or1] Henv_or1].
    case=> _ <- _ _.
    apply: (pos_leb_trans (mk_env_xor_newer_gen Henv_xls1)).
    apply: (pos_leb_trans (mk_env_xor_newer_gen Henv_xls2)).
    apply: (pos_leb_trans (mk_env_smulo_rec_newer_gen Henv_rec)).
    apply: (pos_leb_trans (mk_env_signextend_newer_gen Henv_wls1)).
    apply: (pos_leb_trans (mk_env_signextend_newer_gen Henv_wls2)).
    apply: (pos_leb_trans (mk_env_mul_newer_gen Henv_mul)).
    apply: (pos_leb_trans (mk_env_xor1_newer_gen Henv_xor1)).
    apply: (pos_leb_trans (mk_env_or1_newer_gen Henv_or1)).
    exact: Pos.leb_refl.
  Qed.

  Lemma mk_env_smulo_newer_res  E g ls1 ls2 E' g' cs lr:
    mk_env_smulo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_lit g' lr.
  Proof.
    rewrite /mk_env_smulo .
    rewrite (lock mk_env_signextend) (lock mk_env_xor1) /= -2!lock.
    dcase (mk_env_xor E g (belastd ls1) (copy (size (belastd ls1)) (lastd lit_ff ls1)))
    => [[[ [ E_xls1 g_xls1 ]  cs_xls1] xls1] Henv_xls1].
    dcase (mk_env_xor E_xls1 g_xls1 (belastd ls2) (copy (size (belastd ls2)) (lastd lit_ff ls2)))
    => [[[[ E_xls2 g_xls2] cs_xls2] xls2] Henv_xls2].
    dcase (mk_env_smulo_rec E_xls2 g_xls2 (behead xls1) (behead xls2))
    => [[[[[ E_rec g_rec] cs_rec] r_or ] r_or_and_rec] Henv_rec].
    dcase (mk_env_signextend 1 E_rec g_rec ls1) => [[[[E_wls1 g_wls1] cs_wls1] wls1] Henv_wls1].
    dcase (mk_env_signextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] wls2] Henv_wls2].
    dcase (mk_env_mul E_wls2 g_wls2 wls1 wls2) => [[[[ E_mul g_mul ] cs_mul] mul] Henv_mul].
    dcase (mk_env_xor1 E_mul g_mul (lastd lit_ff mul) (lastd lit_ff (belastd mul)))
    => [[[[ E_xor1 g_xor1 ] cs_xor1] xor1] Henv_xor1].
    dcase (mk_env_or1 E_xor1 g_xor1 r_or_and_rec xor1) => [[[[ E_or1 g_or1 ] cs_or1] or1] Henv_or1].
    case=> _ <- _ <- . move=> Hgtt Hgls1 Hgls2.
    move: (newer_than_lits_splitmsl Hgtt Hgls1) => /andP [Hgls1tl Hgls1sign].
    move: (newer_than_lits_copy (size (belastd ls1)) Hgls1sign) => Hgls1signs.
    move: (mk_env_xor_newer_res Henv_xls1 Hgtt Hgls1tl Hgls1signs) => Hnew_xls1.
    move: (newer_than_lits_splitmsl Hgtt Hgls2) => /andP [Hgls2tl Hgls2sign].
    move: (newer_than_lits_copy (size (belastd ls2)) Hgls2sign) => Hgls2signs.
    move: (mk_env_xor_newer_gen Henv_xls1) => Hgxls1.
    move: (newer_than_lits_le_newer Hgls2signs Hgxls1) => Hgx1ls2signs.
    move: (newer_than_lits_le_newer Hgls2tl Hgxls1) => Hgx1ls2tl.
    have Hgxls1tt: newer_than_lit g_xls1 lit_tt by t_newer_hook.
    move: (mk_env_xor_newer_res Henv_xls2 Hgxls1tt Hgx1ls2tl Hgx1ls2signs) => Hnew_xls2.
    move: (mk_env_xor_newer_gen Henv_xls2) => Hgxls2.
    move: (newer_than_lits_le_newer Hnew_xls1 Hgxls2) => {Hnew_xls1} Hnew_xls1.
    have Hgxls2tt: newer_than_lit g_xls2 lit_tt by t_newer_hook.
    move: (newer_than_lit_le_newer Hgtt Hgxls1) => Hgx1tt.
    move: (newer_than_lit_le_newer Hgx1tt Hgxls2) => Hgx2tt.
    move: (newer_than_lits_le_newer Hgls1 Hgxls1) => Hgx1ls1.
    move: (newer_than_lits_le_newer Hgx1ls1 Hgxls2) => Hgx2ls1.
    move: (newer_than_lits_le_newer Hgls2 Hgxls1) => Hgx1ls2.
    move: (newer_than_lits_le_newer Hgx1ls2 Hgxls2) => Hgx2ls2.
    move: (mk_env_smulo_rec_newer_res Henv_rec Hgx2tt) => /andP [_ Hnew_rec_rec].
    move: (mk_env_smulo_rec_newer_gen Henv_rec) => Hgx2grec.
    move: (newer_than_lit_le_newer Hgx2tt Hgx2grec) => Hgrectt.
    move: (newer_than_lits_le_newer Hgx2ls1 Hgx2grec) => Hgrecls1.
    move: (newer_than_lits_le_newer Hgx2ls2 Hgx2grec) => Hgrecls2.
    move: (mk_env_signextend_newer_res Henv_wls1 Hgrectt Hgrecls1) => Hnew_wls1.
    move: (mk_env_signextend_newer_gen Henv_wls1) => Hgrecwls1.
    move: (newer_than_lit_le_newer Hgrectt Hgrecwls1) => Hgwls1tt.
    move: (newer_than_lits_le_newer Hgrecls2 Hgrecwls1) => Hgwls1ls2.
    move: (mk_env_signextend_newer_res Henv_wls2 Hgwls1tt Hgwls1ls2) => Hnew_wls2.
    move: (mk_env_signextend_newer_gen Henv_wls2) => Hgwls1wls2.
    move: (newer_than_lit_le_newer Hgwls1tt Hgwls1wls2) => Hgwls2tt.
    move: (mk_env_mul_newer_res Henv_mul Hgwls2tt) => Hnew_gmulmul.
    move: (mk_env_mul_newer_gen Henv_mul) => Hgwls2mul.
    have Hgmultt: newer_than_lit g_mul lit_tt by t_newer_hook.
    move: (newer_than_lits_splitmsl Hgmultt Hnew_gmulmul) => /= /andP [Hnew_mul_tl Hnew_mul_n].
    move: (newer_than_lits_splitmsl Hgmultt Hnew_mul_tl) => /= /andP [_ Hnew_mul_n_minus1].
    move: (mk_env_xor1_newer_res Henv_xor1) => tmp.
    have Hnew_xor1xor1: newer_than_lit g_xor1 xor1 by apply tmp; t_newer_hook.
    move: (mk_env_xor1_newer_gen Henv_xor1) => Hgmulxor1.
    move: (pos_leb_trans Hgrecwls1 Hgwls1wls2) => Hgrecwls2.
    move: (pos_leb_trans Hgrecwls2 Hgwls2mul) => Hgrecmul.
    move: (pos_leb_trans Hgrecmul Hgmulxor1) => Hgrecxor1.
    move: (newer_than_lit_le_newer Hnew_rec_rec Hgrecxor1) => {tmp} tmp.
    exact: (mk_env_or1_newer_res Henv_or1 tmp Hnew_xor1xor1).
  Qed.

  Lemma mk_env_smulo_newer_cnf  E g ls1 ls2 E' g' cs lr:
    mk_env_smulo E g ls1 ls2 = (E', g', cs, lr) ->
    size ls1 == size ls2 ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
  Proof.
    rewrite /mk_env_smulo .
    rewrite (lock mk_env_signextend) (lock mk_env_xor1) /= -2!lock.
    dcase (mk_env_xor E g (belastd ls1) (copy (size (belastd ls1)) (lastd lit_ff ls1)))
    => [[[ [ E_xls1 g_xls1 ]  cs_xls1] xls1] Henv_xls1].
    dcase (mk_env_xor E_xls1 g_xls1 (belastd ls2) (copy (size (belastd ls2)) (lastd lit_ff ls2)))
    => [[[[ E_xls2 g_xls2] cs_xls2] xls2] Henv_xls2].
    dcase (mk_env_smulo_rec E_xls2 g_xls2 (behead xls1) (behead xls2))
    => [[[[[ E_rec g_rec] cs_rec] r_or ] r_or_and_rec] Henv_rec].
    dcase (mk_env_signextend 1 E_rec g_rec ls1) => [[[[E_wls1 g_wls1] cs_wls1] wls1] Henv_wls1].
    dcase (mk_env_signextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] wls2] Henv_wls2].
    dcase (mk_env_mul E_wls2 g_wls2 wls1 wls2) => [[[[ E_mul g_mul ] cs_mul] mul] Henv_mul].
    dcase (mk_env_xor1 E_mul g_mul (lastd lit_ff mul) (lastd lit_ff (belastd mul)))
    => [[[[ E_xor1 g_xor1 ] cs_xor1] xor1] Henv_xor1].
    dcase (mk_env_or1 E_xor1 g_xor1 r_or_and_rec xor1) => [[[[ E_or1 g_or1 ] cs_or1] or1] Henv_or1].
    case=> _ <- <- _. move=> Hsz Hgtt Hgls1 Hgls2.
    move: (newer_than_lits_splitmsl Hgtt Hgls1) => /= /andP [Hgls1tl Hgls1sign].
    move: (newer_than_lits_copy (size (belastd ls1)) Hgls1sign) => Hgls1signs.
    move: (mk_env_xor_newer_res Henv_xls1 Hgtt Hgls1tl Hgls1signs) => Hnew_xls1.
    move: (mk_env_xor_newer_cnf Henv_xls1 Hgtt Hgls1tl Hgls1signs) => Hnewcnf_xls1.
    move: (newer_than_lits_splitmsl Hgtt Hgls2) => /= /andP [Hgls2tl Hgls2sign].
    move: (newer_than_lits_copy (size (belastd ls2)) Hgls2sign) => Hgls2signs.
    move: (mk_env_xor_newer_gen Henv_xls1) => Hgxls1.
    move: (newer_than_lits_le_newer Hgls2signs Hgxls1) => Hgx1ls2signs.
    move: (newer_than_lits_le_newer Hgls2tl Hgxls1) => Hgx1ls2tl.
    have Hgxls1tt: newer_than_lit g_xls1 lit_tt by t_newer_hook.
    move: (mk_env_xor_newer_res Henv_xls2 Hgxls1tt Hgx1ls2tl Hgx1ls2signs) => Hnew_xls2.
    move: (mk_env_xor_newer_cnf Henv_xls2 Hgxls1tt Hgx1ls2tl Hgx1ls2signs) => Hnewcnf_xls2.
    move: (mk_env_xor_newer_gen Henv_xls2) => Hgxls2.
    move: (newer_than_lits_le_newer Hnew_xls1 Hgxls2) => {Hnew_xls1} Hnew_xls1.
    have Hgxls2tt: newer_than_lit g_xls2 lit_tt by t_newer_hook.
    move: (newer_than_lits_splitlsl Hgxls2tt Hnew_xls1) => {Hnew_xls1} /= /andP [_ Hnew_xls1].
    move: (newer_than_lits_splitlsl Hgxls2tt Hnew_xls2) => {Hnew_xls2} /= /andP [_ Hnew_xls2].
    move: (newer_than_lit_le_newer Hgtt Hgxls1) => Hgx1tt.
    move: (newer_than_lit_le_newer Hgx1tt Hgxls2) => Hgx2tt.
    move: (newer_than_lits_le_newer Hgls1 Hgxls1) => Hgx1ls1.
    move: (newer_than_lits_le_newer Hgx1ls1 Hgxls2) => Hgx2ls1.
    move: (newer_than_lits_le_newer Hgls2 Hgxls1) => Hgx1ls2.
    move: (newer_than_lits_le_newer Hgx1ls2 Hgxls2) => Hgx2ls2.
    move: (mk_env_smulo_rec_newer_res Henv_rec Hgx2tt) => /andP [_ Hnew_rec_rec].
    have /eqP Hsz_xls: size xls1 = size xls2.
    {
      have Hcopy: (size (belastd ls1) == size (copy (size (belastd ls1)) (lastd lit_ff ls1)))
        by rewrite /copy size_nseq.
      move: (mk_env_xor_size Henv_xls1 Hcopy) => /eqP ->.
      have Hcopy2: (size (belastd ls2) == size (copy (size (belastd ls2)) (lastd lit_ff ls2)))
        by rewrite /copy size_nseq.
      move: (mk_env_xor_size Henv_xls2 Hcopy2) => /eqP -> .
      exact: (eqP (size_belastd Hsz)).
    }
    have /eqP Hsz_xls_behead : size (behead xls1) = size (behead xls2).
    {
      rewrite !size_behead /=; f_equal.
      exact: (eqP Hsz_xls).
    }
    have /eqP Hsz_xls_belastd: size (belastd xls1) = size (belastd xls2).
    {
      exact: (eqP (size_belastd Hsz_xls)).
    }
    move: (mk_env_smulo_rec_newer_cnf Henv_rec Hsz_xls_behead Hgx2tt Hnew_xls1 Hnew_xls2) => Hnewcnf_rec_rec.
    move: (mk_env_smulo_rec_newer_gen Henv_rec) => Hgx2grec.
    move: (newer_than_lit_le_newer Hgx2tt Hgx2grec) => Hgrectt.
    move: (newer_than_lits_le_newer Hgx2ls1 Hgx2grec) => Hgrecls1.
    move: (newer_than_lits_le_newer Hgx2ls2 Hgx2grec) => Hgrecls2.
    move: (mk_env_signextend_newer_res Henv_wls1 Hgrectt Hgrecls1) => Hnew_wls1.
    move: (mk_env_signextend_newer_cnf Henv_wls1 Hgrectt Hgrecls1) => Hnewcnf_wls1.
    move: (mk_env_signextend_newer_gen Henv_wls1) => Hgrecwls1.
    move: (newer_than_lit_le_newer Hgrectt Hgrecwls1) => Hgwls1tt.
    move: (newer_than_lits_le_newer Hgrecls2 Hgrecwls1) => Hgwls1ls2.
    move: (mk_env_signextend_newer_res Henv_wls2 Hgwls1tt Hgwls1ls2) => Hnew_wls2.
    move: (mk_env_signextend_newer_cnf Henv_wls2 Hgwls1tt Hgwls1ls2) => Hnewcnf_wls2.
    move: (mk_env_signextend_newer_gen Henv_wls2) => Hgwls1wls2.
    move: (newer_than_lit_le_newer Hgwls1tt Hgwls1wls2) => Hgwls2tt.
    move: (newer_than_lits_le_newer Hnew_wls1 Hgwls1wls2) => Hnew_wls2wls1.
    move: (mk_env_mul_newer_res Henv_mul Hgwls2tt) => Hnew_gmulmul.
    move: (mk_env_mul_newer_cnf Henv_mul Hgwls2tt Hnew_wls2wls1 Hnew_wls2) => Hnewcnf_gmulmul.
    move: (mk_env_xor1_newer_cnf Henv_xor1).
    move: (mk_env_xor1_newer_res Henv_xor1).
    move: (mk_env_mul_newer_gen Henv_mul) => Hgwls2mul.
    have Hgmultt: newer_than_lit g_mul lit_tt by t_newer_hook.
    move: (newer_than_lits_splitmsl Hgmultt Hnew_gmulmul) => /= /andP [Hnew_mul_tl Hnew_mul_n].
    move: (newer_than_lits_splitmsl Hgmultt Hnew_mul_tl) => /= /andP [_ Hnew_mul_n_minus1].
    move=> tmp tmp2. move: (tmp Hnew_mul_n Hnew_mul_n_minus1) => {tmp} Hnew_xor1xor1.
    move: (tmp2 Hnew_mul_n Hnew_mul_n_minus1) => {tmp2} Hnewcnf_xor1xor1.
    move: (mk_env_xor1_newer_gen Henv_xor1) => Hgmulxor1.
    move: (pos_leb_trans Hgrecwls1 Hgwls1wls2) => Hgrecwls2.
    move: (pos_leb_trans Hgrecwls2 Hgwls2mul) => Hgrecmul.
    move: (pos_leb_trans Hgrecmul Hgmulxor1) => Hgrecxor1.
    move: (newer_than_lit_le_newer Hnew_rec_rec Hgrecxor1) => tmp.
    move: (newer_than_lit_le_newer Hgrectt Hgrecxor1) => tmp2.
    move: (mk_env_or1_newer_res Henv_or1 tmp Hnew_xor1xor1) => Hnew_or1or1.
    move: (mk_env_or1_newer_cnf Henv_or1 tmp Hnew_xor1xor1) => Hnewcnf_or1or1.
    rewrite !newer_than_cnf_catrev.
    rewrite Hnewcnf_or1or1.
    move: (mk_env_or1_newer_gen Henv_or1) => Hgxor1or1.
    rewrite (newer_than_cnf_le_newer Hnewcnf_xor1xor1 Hgxor1or1).
    move: (pos_leb_trans Hgmulxor1 Hgxor1or1) => Hgmulor1.
    move: (pos_leb_trans Hgrecxor1 Hgxor1or1) => Hgrecor1.
    rewrite (newer_than_cnf_le_newer Hnewcnf_gmulmul Hgmulor1).
    rewrite (newer_than_cnf_le_newer Hnewcnf_rec_rec Hgrecor1).
    move: (pos_leb_trans Hgwls2mul Hgmulor1) => Hgwls2or1.
    rewrite (newer_than_cnf_le_newer Hnewcnf_wls2 Hgwls2or1).
    move: (pos_leb_trans Hgwls1wls2 Hgwls2or1) => Hgwls1or1.
    rewrite (newer_than_cnf_le_newer Hnewcnf_wls1 Hgwls1or1).
    move: (pos_leb_trans Hgx2grec Hgrecor1) => Hgx2or1.
    rewrite (newer_than_cnf_le_newer Hnewcnf_xls2 Hgx2or1).
    move: (pos_leb_trans Hgxls2 Hgx2or1) => Hgx1or1.
    rewrite (newer_than_cnf_le_newer Hnewcnf_xls1 Hgx1or1).
    done.
  Qed.

  Lemma mk_env_smulo_preserve E g ls1 ls2 E' g' cs lr:
    mk_env_smulo E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
  Proof.
    rewrite /mk_env_smulo .
    rewrite (lock mk_env_signextend) (lock mk_env_xor1) /= -2!lock.
    dcase (mk_env_xor E g (belastd ls1) (copy (size (belastd ls1)) (lastd lit_ff ls1)))
    => [[[ [ E_xls1 g_xls1 ]  cs_xls1] xls1] Henv_xls1].
    dcase (mk_env_xor E_xls1 g_xls1 (belastd ls2) (copy (size (belastd ls2)) (lastd lit_ff ls2)))
    => [[[[ E_xls2 g_xls2] cs_xls2] xls2] Henv_xls2].
    dcase (mk_env_smulo_rec E_xls2 g_xls2 (behead xls1) (behead xls2))
    => [[[[[ E_rec g_rec] cs_rec] r_or ] r_or_and_rec] Henv_rec].
    dcase (mk_env_signextend 1 E_rec g_rec ls1) => [[[[E_wls1 g_wls1] cs_wls1] wls1] Henv_wls1].
    dcase (mk_env_signextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] wls2] Henv_wls2].
    dcase (mk_env_mul E_wls2 g_wls2 wls1 wls2) => [[[[ E_mul g_mul ] cs_mul] mul] Henv_mul].
    dcase (mk_env_xor1 E_mul g_mul (lastd lit_ff mul) (lastd lit_ff (belastd mul)))
    => [[[[ E_xor1 g_xor1 ] cs_xor1] xor1] Henv_xor1].
    dcase (mk_env_or1 E_xor1 g_xor1 r_or_and_rec xor1) => [[[[ E_or1 g_or1 ] cs_or1] or1] Henv_or1].
    case=> <- _ _ _.
    move: (mk_env_xor_preserve Henv_xls1) => Hpre_xls1.
    apply (env_preserve_trans Hpre_xls1).
    move: (mk_env_xor_newer_gen Henv_xls1) => Hng_xls1.
    move: (mk_env_xor_preserve Henv_xls2) => Hpre_xls2.
    move: (mk_env_xor_newer_gen Henv_xls2) => Hng_xls2.
    move: (pos_leb_trans Hng_xls1 Hng_xls2) => Hgxls2.
    move: (env_preserve_le Hpre_xls2 Hng_xls1) => {Hpre_xls2} Hpre_xls2.
    apply (env_preserve_trans Hpre_xls2).
    move: (mk_env_smulo_rec_preserve Henv_rec) => Hpre_rec.
    move: (mk_env_smulo_rec_newer_gen Henv_rec) => Hng_rec.
    move: (pos_leb_trans Hgxls2 Hng_rec) => Hgrec.
    move: (env_preserve_le Hpre_rec Hgxls2) => {Hpre_rec} Hpre_rec.
    apply (env_preserve_trans Hpre_rec).
    move: (mk_env_signextend_preserve Henv_wls1) => Hpre_wls1.
    move: (mk_env_signextend_newer_gen Henv_wls1) => Hng_wls1.
    move: (pos_leb_trans Hgrec Hng_wls1) => Hgwls1.
    move: (env_preserve_le Hpre_wls1 Hgrec) => {Hpre_wls1} Hpre_wls1.
    apply (env_preserve_trans Hpre_wls1).
    move: (mk_env_signextend_preserve Henv_wls2) => Hpre_wls2.
    move: (mk_env_signextend_newer_gen Henv_wls2) => Hng_wls2.
    move: (pos_leb_trans Hgwls1 Hng_wls2) => Hgwls2.
    move: (env_preserve_le Hpre_wls2 Hgwls1) => {Hpre_wls2} Hpre_wls2.
    apply (env_preserve_trans Hpre_wls2).
    move: (mk_env_mul_preserve Henv_mul) => Hpre_mul.
    move: (mk_env_mul_newer_gen Henv_mul) => Hng_mul.
    move: (pos_leb_trans Hgwls2 Hng_mul) => Hgmul.
    move: (env_preserve_le Hpre_mul Hgwls2) => {Hpre_mul} Hpre_mul.
    apply (env_preserve_trans Hpre_mul).
    move: (mk_env_xor1_preserve Henv_xor1) => Hpre_xor1.
    move: (mk_env_xor1_newer_gen Henv_xor1) => Hng_xor1.
    move: (pos_leb_trans Hgmul Hng_xor1) => Hgxor1.
    move: (env_preserve_le Hpre_xor1 Hgmul) => {Hpre_xor1} Hpre_xor1.
    apply (env_preserve_trans Hpre_xor1).
    move: (mk_env_or1_preserve Henv_or1) => Hpre_or1.
    move: (mk_env_or1_newer_gen Henv_or1) => Hng_or1.
    move: (pos_leb_trans Hgxor1 Hng_or1) => Hgor1.
    move: (env_preserve_le Hpre_or1 Hgxor1) => {Hpre_or1} Hpre_or1.
    apply (env_preserve_trans Hpre_or1).
    exact: env_preserve_refl.
  Qed.

  Lemma mk_env_smulo_sat E g ls1 ls2 E' g' cs lr:
    mk_env_smulo E g ls1 ls2 = (E', g', cs, lr) ->
    size ls1 == size ls2 ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->  newer_than_lits g ls2 ->
    interp_cnf E' cs.
  Proof.
    rewrite /mk_env_smulo .
    rewrite (lock mk_env_signextend) (lock mk_env_xor1) /= -2!lock.
    dcase (mk_env_xor E g (belastd ls1) (copy (size (belastd ls1)) (lastd lit_ff ls1)))
    => [[[ [ E_xls1 g_xls1 ]  cs_xls1] xls1] Henv_xls1].
    dcase (mk_env_xor E_xls1 g_xls1 (belastd ls2) (copy (size (belastd ls2)) (lastd lit_ff ls2)))
    => [[[[ E_xls2 g_xls2] cs_xls2] xls2] Henv_xls2].
    dcase (mk_env_smulo_rec E_xls2 g_xls2 (behead xls1) (behead xls2))
    => [[[[[ E_rec g_rec] cs_rec] r_or ] r_or_and_rec] Henv_rec].
    dcase (mk_env_signextend 1 E_rec g_rec ls1) => [[[[E_wls1 g_wls1] cs_wls1] wls1] Henv_wls1].
    dcase (mk_env_signextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] wls2] Henv_wls2].
    dcase (mk_env_mul E_wls2 g_wls2 wls1 wls2) => [[[[ E_mul g_mul ] cs_mul] mul] Henv_mul].
    dcase (mk_env_xor1 E_mul g_mul (lastd lit_ff mul) (lastd lit_ff (belastd mul)))
    => [[[[ E_xor1 g_xor1 ] cs_xor1] xor1] Henv_xor1].
    dcase (mk_env_or1 E_xor1 g_xor1 r_or_and_rec xor1) => [[[[ E_or1 g_or1 ] cs_or1] or1] Henv_or1].
    case=> <- _ <- _. move=> Hsz Hgtt Hgls1 Hgls2.
    move: (newer_than_lits_splitmsl Hgtt Hgls1) => /= /andP [Hgls1tl Hgls1sign].
    move: (newer_than_lits_copy (size (belastd ls1)) Hgls1sign) => Hgls1signs.
    move: (mk_env_xor_newer_res Henv_xls1 Hgtt Hgls1tl Hgls1signs) => Hnew_xls1.
    move: (mk_env_xor_newer_cnf Henv_xls1 Hgtt Hgls1tl Hgls1signs) => Hnewcnf_xls1.
    move: (mk_env_xor_sat Henv_xls1 Hgtt Hgls1tl Hgls1signs) => Hsat_xls1.
    move: (mk_env_xor_preserve Henv_xls1) => Hpre_xls1.
    move: (newer_than_lits_splitmsl Hgtt Hgls2) => /= /andP [Hgls2tl Hgls2sign].
    move: (newer_than_lits_copy (size (belastd ls2)) Hgls2sign) => Hgls2signs.
    move: (mk_env_xor_newer_gen Henv_xls1) => Hgxls1.
    move: (newer_than_lits_le_newer Hgls2signs Hgxls1) => Hgx1ls2signs.
    move: (newer_than_lits_le_newer Hgls2tl Hgxls1) => Hgx1ls2tl.
    have Hgxls1tt: newer_than_lit g_xls1 lit_tt by t_newer_hook.
    move: (mk_env_xor_newer_res Henv_xls2 Hgxls1tt Hgx1ls2tl Hgx1ls2signs) => Hnew_xls2.
    move: (mk_env_xor_newer_cnf Henv_xls2 Hgxls1tt Hgx1ls2tl Hgx1ls2signs) => Hnewcnf_xls2.
    move: (mk_env_xor_newer_gen Henv_xls2) => Hgxls2.
    move: (mk_env_xor_sat Henv_xls2 Hgxls1tt Hgx1ls2tl Hgx1ls2signs) => Hsat_xls2.
    move: (mk_env_xor_preserve Henv_xls2) => Hpre_xls2.
    move: (newer_than_lits_le_newer Hnew_xls1 Hgxls2) => {Hnew_xls1} Hnew_xls1.
    have Hgxls2tt: newer_than_lit g_xls2 lit_tt by t_newer_hook.
    move: (newer_than_lits_splitlsl Hgxls2tt Hnew_xls1) => {Hnew_xls1} /= /andP [_ Hnew_xls1].
    move: (newer_than_lits_splitlsl Hgxls2tt Hnew_xls2) => {Hnew_xls2} /= /andP [_ Hnew_xls2].
    move: (newer_than_lit_le_newer Hgtt Hgxls1) => Hgx1tt.
    move: (newer_than_lit_le_newer Hgx1tt Hgxls2) => Hgx2tt.
    move: (newer_than_lits_le_newer Hgls1 Hgxls1) => Hgx1ls1.
    move: (newer_than_lits_le_newer Hgx1ls1 Hgxls2) => Hgx2ls1.
    move: (newer_than_lits_le_newer Hgls2 Hgxls1) => Hgx1ls2.
    move: (newer_than_lits_le_newer Hgx1ls2 Hgxls2) => Hgx2ls2.
    move: (mk_env_smulo_rec_newer_res Henv_rec Hgx2tt) => /andP [_ Hnew_rec_rec].
    have /eqP Hsz_xls: size xls1 = size xls2.
    {
      have Hcopy: (size (belastd ls1) == size (copy (size (belastd ls1)) (lastd lit_ff ls1)))
        by rewrite /copy size_nseq.
      move: (mk_env_xor_size Henv_xls1 Hcopy) => /eqP ->.
      have Hcopy2: (size (belastd ls2) == size (copy (size (belastd ls2)) (lastd lit_ff ls2)))
        by rewrite /copy size_nseq.
      move: (mk_env_xor_size Henv_xls2 Hcopy2) => /eqP -> .
      exact: (eqP (size_belastd Hsz)).
    }
    have /eqP Hsz_xls_behead : size (behead xls1) = size (behead xls2).
    {
      rewrite !size_behead /=; f_equal.
      exact: (eqP Hsz_xls).
    }
    have /eqP Hsz_xls_belastd: size (belastd xls1) = size (belastd xls2).
    {
      exact: (eqP (size_belastd Hsz_xls)).
    }
    move: (mk_env_smulo_rec_newer_cnf Henv_rec Hsz_xls_behead Hgx2tt Hnew_xls1 Hnew_xls2) => Hnewcnf_rec_rec.
    move: (mk_env_smulo_rec_sat Henv_rec Hsz_xls_behead Hgx2tt Hnew_xls1 Hnew_xls2) => Hsat_rec_rec.
    move: (mk_env_smulo_rec_preserve Henv_rec) => Hpre_rec.
    move: (mk_env_smulo_rec_newer_gen Henv_rec) => Hgx2grec.
    move: (newer_than_lit_le_newer Hgx2tt Hgx2grec) => Hgrectt.
    move: (newer_than_lits_le_newer Hgx2ls1 Hgx2grec) => Hgrecls1.
    move: (newer_than_lits_le_newer Hgx2ls2 Hgx2grec) => Hgrecls2.
    move: (mk_env_signextend_newer_res Henv_wls1 Hgrectt Hgrecls1) => Hnew_wls1.
    move: (mk_env_signextend_newer_cnf Henv_wls1 Hgrectt Hgrecls1) => Hnewcnf_wls1.
    move: (mk_env_signextend_sat Henv_wls1 Hgrectt Hgrecls1) => Hsat_wls1.
    move: (mk_env_signextend_preserve Henv_wls1) => Hpre_wls1.
    move: (mk_env_signextend_newer_gen Henv_wls1) => Hgrecwls1.
    move: (newer_than_lit_le_newer Hgrectt Hgrecwls1) => Hgwls1tt.
    move: (newer_than_lits_le_newer Hgrecls2 Hgrecwls1) => Hgwls1ls2.
    move: (mk_env_signextend_newer_res Henv_wls2 Hgwls1tt Hgwls1ls2) => Hnew_wls2.
    move: (mk_env_signextend_newer_cnf Henv_wls2 Hgwls1tt Hgwls1ls2) => Hnewcnf_wls2.
    move: (mk_env_signextend_sat Henv_wls2 Hgwls1tt Hgwls1ls2) => Hsat_wls2.
    move: (mk_env_signextend_preserve Henv_wls2) => Hpre_wls2.
    move: (mk_env_signextend_newer_gen Henv_wls2) => Hgwls1wls2.
    move: (newer_than_lit_le_newer Hgwls1tt Hgwls1wls2) => Hgwls2tt.
    move: (newer_than_lits_le_newer Hnew_wls1 Hgwls1wls2) => Hnew_wls2wls1.
    move: (mk_env_mul_newer_res Henv_mul Hgwls2tt) => Hnew_gmulmul.
    move: (mk_env_mul_newer_cnf Henv_mul Hgwls2tt Hnew_wls2wls1 Hnew_wls2) => Hnewcnf_gmulmul.
    move: (mk_env_mul_sat Henv_mul Hgwls2tt Hnew_wls2wls1 Hnew_wls2) => Hsat_gmulmul.
    move: (mk_env_mul_preserve Henv_mul) => Hpre_mul.
    move: (mk_env_xor1_sat Henv_xor1).
    move: (mk_env_xor1_newer_cnf Henv_xor1).
    move: (mk_env_xor1_newer_res Henv_xor1).
    move: (mk_env_xor1_preserve Henv_xor1) => Hpre_xor1.
    move: (mk_env_mul_newer_gen Henv_mul) => Hgwls2mul.
    have Hgmultt: newer_than_lit g_mul lit_tt by t_newer_hook.
    move: (newer_than_lits_splitmsl Hgmultt Hnew_gmulmul) => /= /andP [Hnew_mul_tl Hnew_mul_n].
    move: (newer_than_lits_splitmsl Hgmultt Hnew_mul_tl) => /= /andP [_ Hnew_mul_n_minus1].
    move=> tmp tmp2 tmp3.
    move: (tmp Hnew_mul_n Hnew_mul_n_minus1) => {tmp} Hnew_xor1xor1.
    move: (tmp2 Hnew_mul_n Hnew_mul_n_minus1) => {tmp2} Hnewcnf_xor1xor1.
    move: (tmp3 Hnew_mul_n Hnew_mul_n_minus1) => {tmp3} Hsat_xor1xor1.
    move: (mk_env_xor1_newer_gen Henv_xor1) => Hgmulxor1.
    move: (pos_leb_trans Hgrecwls1 Hgwls1wls2) => Hgrecwls2.
    move: (pos_leb_trans Hgrecwls2 Hgwls2mul) => Hgrecmul.
    move: (pos_leb_trans Hgrecmul Hgmulxor1) => Hgrecxor1.
    move: (newer_than_lit_le_newer Hnew_rec_rec Hgrecxor1) => tmp.
    move: (newer_than_lit_le_newer Hgrectt Hgrecxor1) => tmp2.
    move: (mk_env_or1_newer_res Henv_or1 tmp Hnew_xor1xor1) => Hnew_or1or1.
    move: (mk_env_or1_newer_cnf Henv_or1 tmp Hnew_xor1xor1) => Hnewcnf_or1or1.
    move: (mk_env_or1_sat Henv_or1 tmp Hnew_xor1xor1) => Hsat_or1or1.
    move: (mk_env_or1_preserve Henv_or1) => Hpre_or1.
    rewrite !interp_cnf_catrev.
    rewrite Hsat_or1or1.
    rewrite (env_preserve_cnf Hpre_or1 Hnewcnf_xor1xor1).
    rewrite Hsat_xor1xor1.
    move: (newer_than_cnf_le_newer Hnewcnf_gmulmul Hgmulxor1) => H.
    rewrite (env_preserve_cnf Hpre_or1 H).
    rewrite (env_preserve_cnf Hpre_xor1 Hnewcnf_gmulmul).
    rewrite (Hsat_gmulmul) => {H}.
    move: (newer_than_cnf_le_newer Hnewcnf_wls2 Hgwls2mul) => H.
    move: (newer_than_cnf_le_newer H Hgmulxor1) => H1.
    rewrite (env_preserve_cnf Hpre_or1 H1).
    rewrite (env_preserve_cnf Hpre_xor1 H).
    rewrite (env_preserve_cnf Hpre_mul Hnewcnf_wls2).
    rewrite (Hsat_wls2) => {H H1}.
    move: (newer_than_cnf_le_newer Hnewcnf_wls1 Hgwls1wls2) => H.
    move: (newer_than_cnf_le_newer H Hgwls2mul) => H1.
    move: (newer_than_cnf_le_newer H1 Hgmulxor1) => H2.
    rewrite (env_preserve_cnf Hpre_or1 H2).
    rewrite (env_preserve_cnf Hpre_xor1 H1).
    rewrite (env_preserve_cnf Hpre_mul H).
    rewrite (env_preserve_cnf Hpre_wls2 Hnewcnf_wls1).
    rewrite (Hsat_wls1) => {H H1 H2}.
    move: (newer_than_cnf_le_newer Hnewcnf_rec_rec Hgrecwls1) => H.
    move: (newer_than_cnf_le_newer H Hgwls1wls2) => H1.
    move: (newer_than_cnf_le_newer H1 Hgwls2mul) => H2.
    move: (newer_than_cnf_le_newer H2 Hgmulxor1) => H3.
    rewrite (env_preserve_cnf Hpre_or1 H3).
    rewrite (env_preserve_cnf Hpre_xor1 H2).
    rewrite (env_preserve_cnf Hpre_mul H1).
    rewrite (env_preserve_cnf Hpre_wls2 H).
    rewrite (env_preserve_cnf Hpre_wls1 Hnewcnf_rec_rec).
    rewrite (Hsat_rec_rec) => {H H1 H2 H3}.
    move: (newer_than_cnf_le_newer Hnewcnf_xls2 Hgx2grec) => H.
    move: (newer_than_cnf_le_newer H Hgrecwls1) => H1.
    move: (newer_than_cnf_le_newer H1 Hgwls1wls2) => H2.
    move: (newer_than_cnf_le_newer H2 Hgwls2mul) => H3.
    move: (newer_than_cnf_le_newer H3 Hgmulxor1) => H4.
    rewrite (env_preserve_cnf Hpre_or1 H4).
    rewrite (env_preserve_cnf Hpre_xor1 H3).
    rewrite (env_preserve_cnf Hpre_mul H2).
    rewrite (env_preserve_cnf Hpre_wls2 H1).
    rewrite (env_preserve_cnf Hpre_wls1 H).
    rewrite (env_preserve_cnf Hpre_rec Hnewcnf_xls2).
    rewrite (Hsat_xls2) => {H H1 H2 H3 H4}.
    move: (newer_than_cnf_le_newer Hnewcnf_xls1 Hgxls2) => H.
    move: (newer_than_cnf_le_newer H Hgx2grec) => H1.
    move: (newer_than_cnf_le_newer H1 Hgrecwls1) => H2.
    move: (newer_than_cnf_le_newer H2 Hgwls1wls2) => H3.
    move: (newer_than_cnf_le_newer H3 Hgwls2mul) => H4.
    move: (newer_than_cnf_le_newer H4 Hgmulxor1) => H5.
    rewrite (env_preserve_cnf Hpre_or1 H5).
    rewrite (env_preserve_cnf Hpre_xor1 H4).
    rewrite (env_preserve_cnf Hpre_mul H3).
    rewrite (env_preserve_cnf Hpre_wls2 H2).
    rewrite (env_preserve_cnf Hpre_wls1 H1).
    rewrite (env_preserve_cnf Hpre_rec H).
    rewrite (env_preserve_cnf Hpre_xls2 Hnewcnf_xls1).
    rewrite (Hsat_xls1) => {H H1 H2 H3 H4 H5}.
    done.
  Qed.
End BBSmulo.
