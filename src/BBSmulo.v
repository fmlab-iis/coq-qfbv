From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNFSimple BBCommon BBAnd BBXor BBOr BBSignExtend BBMul BBUmulo.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== bit_blast_smulo ===== *)

(* ===== smulo_rec is same as umulo_rec *)

Definition bit_blast_smulo_rec := bit_blast_umulo_rec.

Definition mk_env_smulo_rec := mk_env_umulo_rec.

(* orb_all and andb_orb_all defined in Umulo *)

Lemma bit_blast_smulo_rec_correct :
  forall w g (bs1 bs2 : BITS w) E ls1 ls2 g' cs lr_or lr_and_or,
    bit_blast_smulo_rec g ls1 ls2 = (g', cs, lr_or, lr_and_or) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr_or (orb_all bs1) /\
    enc_bit E lr_and_or (andb_orb_all bs1 bs2).
Proof.
  exact: bit_blast_umulo_rec_correct.
Qed.


Lemma mk_env_smulo_rec_is_bit_blast_smulo_rec :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr_or lr_and_or,
    mk_env_smulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    bit_blast_smulo_rec g ls1 ls2 = (g', cs, lr_or, lr_and_or).
Proof.
  exact: mk_env_umulo_rec_is_bit_blast_umulo_rec.
Qed.

Lemma mk_env_smulo_rec_newer_gen :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr_or lr_and_or,
    mk_env_smulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    (g <=? g')%positive.
Proof.
  exact: mk_env_umulo_rec_newer_gen.
Qed.

Lemma mk_env_smulo_rec_newer_res :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr_or lr_and_or,
    mk_env_smulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g' lr_or /\ newer_than_lit g' lr_and_or.
Proof.
  exact: mk_env_umulo_rec_newer_res.
Qed.

Lemma mk_env_smulo_rec_newer_cnf :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr_or lr_and_or,
    mk_env_smulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  exact: mk_env_umulo_rec_newer_cnf.
Qed.

Lemma mk_env_smulo_rec_preserve :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr_or lr_and_or,
    mk_env_smulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    env_preserve E E' g.
Proof.
  exact: mk_env_umulo_rec_preserve.
Qed.

Lemma mk_env_smulo_rec_sat :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr_or lr_and_or,
    mk_env_smulo_rec E g ls1 ls2 = (E', g', cs, lr_or, lr_and_or) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->  newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  exact: mk_env_umulo_rec_sat.
Qed.

Definition bit_blast_smulo w (g: generator) : (w.+1).-tuple literal -> (w.+1).-tuple literal -> generator * cnf * literal:=
  if w is w'.+1 then
    fun ls1 ls2 =>
      let (ls1_sign, ls1_tl) := eta_expand (splitmsb ls1) in
      let (ls2_sign, ls2_tl) := eta_expand (splitmsb ls2) in
      let wsign1 := copy w'.+1 ls1_sign in
      let wsign2 := copy w'.+1 ls2_sign in
      let '(g_xls1, cs_xls1, xls1) := bit_blast_xor g ls1_tl wsign1 in
      let '(g_xls2, cs_xls2, xls2) := bit_blast_xor g_xls1 ls2_tl wsign2 in
      let (xls1_hightl, xls1_low) := eta_expand (splitlsb xls1) in
      let (xls2_hightl, xls2_low) := eta_expand (splitlsb xls2) in
      let '(g_rec, cs_rec, r_or_rec, r_or_and_rec) := bit_blast_smulo_rec g_xls2 xls1_hightl xls2_hightl in
      let '(g_wls1, cs_wls1, wls1) := bit_blast_signextend 1 g_rec ls1 in
      let '(g_wls2, cs_wls2, wls2) := bit_blast_signextend 1 g_wls1 ls2 in
      let '(g_mul, cs_mul, mul) := bit_blast_mul g_wls2 wls1 wls2 in
      let (mul_n, mul_tl) := eta_expand (splitmsb mul) in
      let (mul_n_minus1, _) := eta_expand (splitmsb mul_tl) in
      let '(g_xor1, cs_xor1, xor1) := bit_blast_xor1 g_mul mul_n mul_n_minus1 in
      let '(g_or1, cs_or1, or1) := bit_blast_or1 g_xor1 r_or_and_rec xor1 in
      (g_or1, cs_xls1 ++ cs_xls2 ++ cs_rec ++ cs_wls1 ++ cs_wls2  ++ cs_mul ++ cs_xor1 ++ cs_or1, or1)
  else
    fun ls1 ls2 =>
      let (sign1, _) := eta_expand (splitmsb ls1) in
      let (sign2, _) := eta_expand (splitmsb ls2) in
      bit_blast_and1 g sign1 sign2.

Definition mk_env_smulo w E (g: generator) : (w.+1).-tuple literal -> (w.+1).-tuple literal -> env * generator * cnf * literal:=
  if w is w'.+1 then
    fun ls1 ls2 =>
      let (ls1_sign, ls1_tl) := eta_expand (splitmsb ls1) in
      let (ls2_sign, ls2_tl) := eta_expand (splitmsb ls2) in
      let wsign1 := copy w'.+1 ls1_sign in
      let wsign2 := copy w'.+1 ls2_sign in
      let '(E_xls1, g_xls1, cs_xls1, xls1) := mk_env_xor E g ls1_tl wsign1 in
      let '(E_xls2, g_xls2, cs_xls2, xls2) := mk_env_xor E_xls1 g_xls1 ls2_tl wsign2 in
      let (xls1_hightl, xls1_low) := eta_expand (splitlsb xls1) in
      let (xls2_hightl, xls2_low) := eta_expand (splitlsb xls2) in
      let '(E_rec, g_rec, cs_rec, r_or_rec, r_or_and_rec) := mk_env_smulo_rec E_xls2 g_xls2 xls1_hightl xls2_hightl in
      let '(E_wls1, g_wls1, cs_wls1, wls1) := mk_env_signextend 1 E_rec g_rec ls1 in
      let '(E_wls2, g_wls2, cs_wls2, wls2) := mk_env_signextend 1 E_wls1 g_wls1 ls2 in
      let '(E_mul, g_mul, cs_mul, mul) := mk_env_mul E_wls2 g_wls2 wls1 wls2 in
      let (mul_n, mul_tl) := eta_expand (splitmsb mul) in
      let (mul_n_minus1, _) := eta_expand (splitmsb mul_tl) in
      let '(E_xor1, g_xor1, cs_xor1, xor1) := mk_env_xor1 E_mul g_mul mul_n mul_n_minus1 in
      let '(E_or1, g_or1, cs_or1, or1) := mk_env_or1 E_xor1 g_xor1 r_or_and_rec xor1 in
      (E_or1, g_or1, cs_xls1 ++ cs_xls2 ++ cs_rec ++ cs_wls1 ++ cs_wls2  ++ cs_mul ++ cs_xor1 ++ cs_or1, or1)
  else
    fun ls1 ls2 =>
      let (sign1, _) := eta_expand (splitmsb ls1) in
      let (sign2, _) := eta_expand (splitmsb ls2) in
      mk_env_and1 E g sign1 sign2.

Definition Smulo w : BITS (w.+1) -> BITS (w.+1) -> bool :=
  if w is w'.+1 then
    fun bs1 bs2 =>
      let (bs1_sign, bs1_tl) := eta_expand (splitmsb bs1) in
      let (bs2_sign, bs2_tl) := eta_expand (splitmsb bs2) in
      let wsign1 := copy w'.+1 bs1_sign in
      let wsign2 := copy w'.+1 bs2_sign in
      let xbs1 := xorB bs1_tl wsign1 in
      let xbs2 := xorB bs2_tl wsign2 in
      let (xbs1_hightl, xbs1_low) := eta_expand (splitlsb xbs1) in
      let (xbs2_hightl, xbs2_low) := eta_expand (splitlsb xbs2) in
      let and_or := andb_orb_all xbs1_hightl xbs2_hightl in
      let wbs1 := signExtend 1 bs1 in
      let wbs2 := signExtend 1 bs2 in
      let mul := mulB wbs1 wbs2 in
      let (mul_n, mul_tl) := eta_expand (splitmsb mul) in
      let (mul_n_minus1, _) := eta_expand (splitmsb mul_tl) in
      orb and_or (xorb mul_n mul_n_minus1)
  else
    fun bs1 bs2 =>
      let (sign1, _) := eta_expand (splitmsb bs1) in
      let (sign2, _) := eta_expand (splitmsb bs2) in
      andb sign1 sign2.


Definition smul_overflow w (bs1 bs2: BITS (w.+1)) :=
  let mul1 := (mulB (signExtend (w.+1) bs1) (signExtend (w.+1) bs2)) in
  let mul2:= signExtend (w.+1) (mulB bs1 bs2) in
  mul1 != mul2.


Lemma Smulo_equiv_smul_overflow:
  forall w (bs1 bs2: BITS (w.+1)),
    Smulo bs1 bs2 = smul_overflow bs1 bs2.
Admitted.

Lemma bit_blast_smulo_correct :
  forall w g (bs1 bs2 : BITS (w.+1)) E ls1 ls2 g' cs lr,
    bit_blast_smulo g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (smul_overflow bs1 bs2).
Proof.
  elim.
  - move=> g bs1 bs2 E ls1 ls2 g' cs lr.
    rewrite - (Smulo_equiv_smul_overflow bs1 bs2).
    case Hls1 : (splitmsb ls1) => [ls1_sign ls1_tl].
    case Hls2 : (splitmsb ls2) => [ls2_sign ls2_tl].
    case Hbs1 : (splitmsb bs1) => [bs1_sign bs1_tl].
    case Hbs2 : (splitmsb bs2) => [bs2_sign bs2_tl].
    rewrite /bit_blast_smulo /Smulo.
    rewrite !enc_bits_splitmsb.
    rewrite !Hls1 !Hls2 !Hbs1 !Hbs2.
    rewrite (lock interp_cnf) /= -lock.
    move=> H /andP [Henc1 _] /andP [Henc2 _] Hicnf.
    remember (bs1_sign && bs2_sign) as br .
    symmetry in Heqbr.
    exact: (bit_blast_and1_correct H Henc1 Henc2 Hicnf Heqbr).
  - move=> w IH g bs1 bs2 E ls1 ls2 g' cs lr.
    rewrite - (Smulo_equiv_smul_overflow bs1 bs2).
    rewrite /bit_blast_smulo /Smulo.
    case Hls1 : (splitmsb ls1) => [ls1_sign ls1_tl].
    case Hls2 : (splitmsb ls2) => [ls2_sign ls2_tl].
    case Hbs1 : (splitmsb bs1) => [bs1_sign bs1_tl].
    case Hbs2 : (splitmsb bs2) => [bs2_sign bs2_tl].
    dcase (bit_blast_xor g (snd (ls1_sign, ls1_tl)) (copy w.+1 (fst (ls1_sign, ls1_tl))))
          => [[[g_xls1 cs_xls1] xls1] Hblast_xls1].
    dcase (bit_blast_xor g_xls1 (snd (ls2_sign, ls2_tl)) (copy w.+1 (fst (ls2_sign, ls2_tl))))
    => [[[g_xls2 cs_xls2] xls2] Hblast_xls2].
    case Hxls1: (splitlsb xls1) => [xls1_high xls1_low].
    case Hxls2: (splitlsb xls2) => [xls2_high xls2_low].
    dcase (bit_blast_smulo_rec g_xls2 (fst (xls1_high, xls1_low)) (fst (xls2_high, xls2_low)))
    => [[[[g_rec cs_rec] r_or ] r_or_and_rec] Hblast_rec].
    dcase (bit_blast_signextend 1 g_rec ls1) => [[[g_wls1 cs_wls1] wls1] Hblast_wls1].
    dcase (bit_blast_signextend 1 g_wls1 ls2) => [[[g_wls2 cs_wls2] wls2] Hblast_wls2].
    dcase (bit_blast_mul g_wls2 wls1 wls2) => [[[g_mul cs_mul] mul] Hblast_mul].
    case Hmul: (splitmsb mul) => [mul_n mul_tl].
    case Hmul_tl: (splitmsb mul_tl) => [mul_n_minus1 mul_tl_tl].
    dcase (bit_blast_xor1 g_mul (fst (mul_n, mul_tl)) (fst (mul_n_minus1, mul_tl_tl))) => [[[g_xor1 cs_xor1] xor1] Hblast_xor1].
    dcase (bit_blast_or1 g_xor1 r_or_and_rec xor1) => [[[g_or1 cs_or1] or1] Hblast_or1].
    case => _ <- <- Henc1 Henc2.
    rewrite !add_prelude_append.
    move=> /andP [Hicnf_xls1 /andP [Hicnf_xls2 /andP [Hicnf_rec /andP [Hicnf_wls1 /andP [Hicnf_wls2 /andP [Hicnf_mul /andP [Hicnf_xor1 Hicnf_or1]]]]]]].
    simpl fst in Hblast_xls1, Hblast_xls2, Hblast_rec, Hblast_xor1.
    simpl snd in Hblast_xls1, Hblast_xls2, Hblast_rec, Hblast_xor1.
    move: (Henc1) (Henc2).
    rewrite enc_bits_splitmsb => H.
    rewrite !Hls1 !Hbs1 in H.
    simpl fst in H. simpl snd in H.
    move/andP: H => [Henc_ls1_sign Henc_ls1_tl].
    rewrite enc_bits_splitmsb => H.
    rewrite !Hls2 !Hbs2 in H.
    simpl fst in H. simpl snd in H.
    move/andP: H => [Henc_ls2_sign Henc_ls2_tl].
    case Hbmul: (splitmsb (mulB (signExtend 1 bs1) (signExtend 1 bs2))) => [bmul_n bmul_tl].
    have -> : snd (bmul_n, bmul_tl) = bmul_tl by done.
    case Hbmul_tl: (splitmsb bmul_tl) => [bmul_n_minus1 bmul_tl_tl].
    have -> : fst (bs1_sign, bs1_tl) = bs1_sign by done.
    have -> : snd (bs1_sign, bs1_tl) = bs1_tl by done.
    have -> : fst (bs2_sign, bs2_tl) = bs2_sign by done.
    have -> : snd (bs2_sign, bs2_tl) = bs2_tl by done.
    apply enc_bit_copy with (n:= w.+1) in Henc_ls1_sign.
    apply enc_bit_copy with (n:= w.+1) in Henc_ls2_sign.
    move: (bit_blast_xor_correct Hblast_xls1 Henc_ls1_tl Henc_ls1_sign Hicnf_xls1) => Henc_wsign1.
    move: (bit_blast_xor_correct Hblast_xls2 Henc_ls2_tl Henc_ls2_sign Hicnf_xls2) => Henc_wsign2.
    move: (Henc_wsign1).
    rewrite enc_bits_splitlsb => /andP [_ Henc_wls1high].
    rewrite Hxls1 /= in Henc_wls1high.
    move: (Henc_wsign2).
    rewrite enc_bits_splitlsb => /andP [_ Henc_wls2high].
    rewrite Hxls2 /= in Henc_wls2high.
    move: (bit_blast_smulo_rec_correct Hblast_rec Henc_wls1high Henc_wls2high Hicnf_rec) => [_ Henc_rec].
    rewrite /=.
    move: (bit_blast_signextend_correct 1 Henc1 Hicnf_wls1) => H1.
    move: (bit_blast_signextend_correct 1 Henc2 Hicnf_wls2) => H2.
    case: Hblast_wls1 => _ _ Hr1.
    case: Hblast_wls2 => _ _ Hr2.
    rewrite Hr1 in H1. rewrite Hr2 in H2.
    move: (bit_blast_mul_correct Hblast_mul H1 H2 Hicnf_mul) => Henc_mul.
    rewrite enc_bits_splitmsb in Henc_mul.
    rewrite Hmul Hbmul in Henc_mul.
    move/andP: Henc_mul => [Henc_mul_n Henc_mul_tl].
    rewrite /= in Henc_mul_n.
    have tmp : snd (mul_n, mul_tl) = mul_tl by done.
    rewrite tmp in Henc_mul_tl.
    have {tmp} tmp : snd (bmul_n, bmul_tl) = bmul_tl by done.
    rewrite tmp in Henc_mul_tl.
    rewrite enc_bits_splitmsb in Henc_mul_tl.
    rewrite Hbmul_tl in Henc_mul_tl.
    rewrite Hmul_tl in Henc_mul_tl.
    rewrite /= in Henc_mul_tl.
    move: Henc_mul_tl => /andP [Henc_mul_n_minus_1 _].
    remember (xorb bmul_n bmul_n_minus1) as br.
    symmetry in Heqbr.
    move: (bit_blast_xor1_correct Hblast_xor1 Henc_mul_n Henc_mul_n_minus_1 Hicnf_xor1 Heqbr). rewrite -Heqbr => Henc_xor1.
    remember (andb_orb_all (behead_tuple (xorB bs1_tl (copy w.+1 bs1_sign)))
       (behead_tuple (xorB bs2_tl (copy w.+1 bs2_sign))) || xorb bmul_n bmul_n_minus1) as br2.
    symmetry in Heqbr2.
    move: (bit_blast_or1_correct Hblast_or1 Henc_rec Henc_xor1 Hicnf_or1 Heqbr2).
      by rewrite -Heqbr2.
Qed.

Lemma mk_env_smulo_is_bit_blast_smulo :
  forall w E g (ls1 ls2: (w.+1).-tuple literal) E' g' cs lr,
    mk_env_smulo E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_smulo g ls1 ls2 = (g', cs, lr).
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr.
    rewrite /mk_env_smulo /bit_blast_smulo.
    exact: mk_env_and1_is_bit_blast_and1.
  - move=> w IH E g ls1 ls2 E' g' cs lr.
    rewrite /mk_env_smulo /bit_blast_smulo.
    dcase (mk_env_xor E g (snd (splitmsb ls1)) (copy w.+1 (fst (splitmsb ls1))))
    => [[[[E_xls1 g_xls1] cs_xls1] xls1] Henv_xls1].
    dcase (mk_env_xor E_xls1 g_xls1 (snd (splitmsb ls2)) (copy w.+1 (fst (splitmsb ls2))))
    => [[[[E_xls2 g_xls2] cs_xls2] xls2] Henv_xls2].
    dcase (mk_env_smulo_rec E_xls2 g_xls2 (fst (splitlsb xls1)) (fst (splitlsb xls2)) )
    => [[[[[E_rec g_rec] cs_rec] rec_or] rec_and_or] Henv_rec].
    rewrite (mk_env_xor_is_bit_blast_xor Henv_xls1).
    rewrite (mk_env_xor_is_bit_blast_xor Henv_xls2).
    rewrite (mk_env_smulo_rec_is_bit_blast_smulo_rec Henv_rec).
    dcase (mk_env_signextend 1 E_rec g_rec ls1) => [[[[E_wls1 g_wls1] cs_wls1] wls1] Henv_wls1].
    dcase (mk_env_signextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] wls2] Henv_wls2].
    rewrite (mk_env_signextend_is_bit_blast_signextend Henv_wls1).
    rewrite (mk_env_signextend_is_bit_blast_signextend Henv_wls2).
    move=> H. dcase_hyps.
    rewrite (mk_env_mul_is_bit_blast_mul H).
    rewrite (mk_env_xor1_is_bit_blast_xor1 H1).
    rewrite (mk_env_or1_is_bit_blast_or1 H0).
      by rewrite H4 H5 H6.
Qed.

Lemma mk_env_smulo_newer_gen :
  forall w E g (ls1 ls2: (w.+1).-tuple literal) E' g' cs lr,
    mk_env_smulo E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr.
    rewrite /mk_env_smulo.
    exact: mk_env_and1_newer_gen.
  - move=> w IH E g ls1 ls2 E' g' cs lr.
    rewrite /mk_env_smulo.
    dcase (mk_env_xor E g (snd (splitmsb ls1)) (copy w.+1 (fst (splitmsb ls1))))
    => [[[[E_xls1 g_xls1] cs_xls1] xls1] Henv_xls1].
    dcase (mk_env_xor E_xls1 g_xls1 (snd (splitmsb ls2)) (copy w.+1 (fst (splitmsb ls2))))
    => [[[[E_xls2 g_xls2] cs_xls2] xls2] Henv_xls2].
    dcase (mk_env_smulo_rec E_xls2 g_xls2 (fst (splitlsb xls1)) (fst (splitlsb xls2)) )
    => [[[[[E_rec g_rec] cs_rec] rec_or] rec_and_or] Henv_rec].
    dcase (mk_env_signextend 1 E_rec g_rec ls1) => [[[[E_wls1 g_wls1] cs_wls1] wls1] Henv_wls1].
    dcase (mk_env_signextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] wls2] Henv_wls2].
    dcase (mk_env_mul E_wls2 g_wls2 wls1 wls2) => [[[[E_mul g_mul] cs_mul] mul] Henv_mul].
    dcase (mk_env_xor1 E_mul g_mul (fst (splitmsb mul)) (fst (splitmsb (snd (splitmsb mul))))) => [[[[E_xor1 g_xor1] cs_xor1] xor1] Henv_xor1].
    dcase (mk_env_or1 E_xor1 g_xor1 rec_and_or xor1) => [[[[E_or1 g_or1] cs_or1] or1] Henv_or1].
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

Lemma mk_env_smulo_newer_res :
  forall w E g (ls1 ls2: (w.+1).-tuple literal) E' g' cs lr,
    mk_env_smulo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_lit g' lr.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr.
    rewrite /mk_env_smulo.
    case Hls1 : (splitmsb ls1) => [ls1_sign ls1_tl].
    case Hls2 : (splitmsb ls2) => [ls2_sign ls2_tl].
    rewrite /=. move=> Henv Hgtt Hgls1 Hgls2.
    move: (newer_than_lits_splitmsb Hgls1 Hls1) => /andP [H1 _].
    move: (newer_than_lits_splitmsb Hgls2 Hls2) => /andP [H2 _].
    exact: (mk_env_and1_newer_res Henv H1 H2).
  - move=> w IH E g ls1 ls2 E' g' cs lr.
    rewrite /mk_env_smulo.
    dcase (mk_env_xor E g (snd (splitmsb ls1)) (copy w.+1 (fst (splitmsb ls1))))
    => [[[[E_xls1 g_xls1] cs_xls1] xls1] Henv_xls1].
    dcase (mk_env_xor E_xls1 g_xls1 (snd (splitmsb ls2)) (copy w.+1 (fst (splitmsb ls2))))
    => [[[[E_xls2 g_xls2] cs_xls2] xls2] Henv_xls2].
    dcase (mk_env_smulo_rec E_xls2 g_xls2 (fst (splitlsb xls1)) (fst (splitlsb xls2)) )
    => [[[[[E_rec g_rec] cs_rec] rec_or] rec_and_or] Henv_rec].
    dcase (mk_env_signextend 1 E_rec g_rec ls1) => [[[[E_wls1 g_wls1] cs_wls1] wls1] Henv_wls1].
    dcase (mk_env_signextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] wls2] Henv_wls2].
    dcase (mk_env_mul E_wls2 g_wls2 wls1 wls2) => [[[[E_mul g_mul] cs_mul] mul] Henv_mul].
    dcase (mk_env_xor1 E_mul g_mul (fst (splitmsb mul)) (fst (splitmsb (snd (splitmsb mul))))) => [[[[E_xor1 g_xor1] cs_xor1] xor1] Henv_xor1].
    dcase (mk_env_or1 E_xor1 g_xor1 rec_and_or xor1) => [[[[E_or1 g_or1] cs_or1] or1] Henv_or1].
    case=> _ <- _ <- . move=> Hgtt Hgls1 Hgls2.
    case Hls1 : (splitmsb ls1) => [ls1_sign ls1_tl].
    rewrite Hls1 in Henv_xls1.
    simpl fst in Henv_xls1.
    simpl snd in Henv_xls1.
    move: (newer_than_lits_splitmsb Hgls1 Hls1) => /andP [Hgls1sign Hgls1tl].
    move: (newer_than_lits_copy w.+1 Hgls1sign) => Hgls1signs.
    move: (mk_env_xor_newer_res Henv_xls1 Hgls1tl Hgls1signs) => Hnew_xls1.
    case Hls2 : (splitmsb ls2) => [ls2_sign ls2_tl].
    rewrite Hls2 in Henv_xls2.
    simpl fst in Henv_xls2.
    simpl snd in Henv_xls2.
    move: (newer_than_lits_splitmsb Hgls2 Hls2) => /andP [Hgls2sign Hgls2tl].
    move: (newer_than_lits_copy w.+1 Hgls2sign) => Hgls2signs.
    move: (mk_env_xor_newer_gen Henv_xls1) => Hgxls1.
    move: (newer_than_lits_le_newer Hgls2signs Hgxls1) => Hgx1ls2signs.
    move: (newer_than_lits_le_newer Hgls2tl Hgxls1) => Hgx1ls2tl.
    move: (mk_env_xor_newer_res Henv_xls2 Hgx1ls2tl Hgx1ls2signs) => Hnew_xls2.
    simpl in Henv_rec.
    move: (mk_env_xor_newer_gen Henv_xls2) => Hgxls2.
    move: (newer_than_lits_le_newer Hnew_xls1 Hgxls2) => {Hnew_xls1} Hnew_xls1.
    move: (newer_than_lits_behead Hnew_xls1) => {Hnew_xls1} Hnew_xls1.
    move: (newer_than_lits_behead Hnew_xls2) => {Hnew_xls2} Hnew_xls2.
    move: (newer_than_lit_le_newer Hgtt Hgxls1) => Hgx1tt.
    move: (newer_than_lit_le_newer Hgx1tt Hgxls2) => Hgx2tt.
    move: (newer_than_lits_le_newer Hgls1 Hgxls1) => Hgx1ls1.
    move: (newer_than_lits_le_newer Hgx1ls1 Hgxls2) => Hgx2ls1.
    move: (newer_than_lits_le_newer Hgls2 Hgxls1) => Hgx1ls2.
    move: (newer_than_lits_le_newer Hgx1ls2 Hgxls2) => Hgx2ls2.
    move: (mk_env_smulo_rec_newer_res Henv_rec Hgx2tt) => [_ Hnew_rec_rec].
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
    move: (mk_env_xor1_newer_res Henv_xor1).
    case Hmul: (splitmsb mul) => [mul_n mul_tl].
    case Hmul_tl: (splitmsb mul_tl) => [mul_n_minus1 mul_tl_tl].
    simpl fst.
    move: (newer_than_lits_splitmsb Hnew_gmulmul Hmul) => /andP [Hnew_mul_n Hnew_mul_tl].
    move: (newer_than_lits_splitmsb Hnew_mul_tl Hmul_tl) => /andP [Hnew_mul_n_minus1 _].
    move=> tmp. move: (tmp Hnew_mul_n Hnew_mul_n_minus1) => {tmp} Hnew_xor1xor1.
    move: (mk_env_mul_newer_gen Henv_mul) => Hgwls2mul.
    move: (mk_env_xor1_newer_gen Henv_xor1) => Hgmulxor1.
    move: (pos_leb_trans Hgrecwls1 Hgwls1wls2) => Hgrecwls2.
    move: (pos_leb_trans Hgrecwls2 Hgwls2mul) => Hgrecmul.
    move: (pos_leb_trans Hgrecmul Hgmulxor1) => Hgrecxor1.
    move: (newer_than_lit_le_newer Hnew_rec_rec Hgrecxor1) => tmp.
    move: (newer_than_lit_le_newer Hgrectt Hgrecxor1) => tmp2.
    exact: (mk_env_or1_newer_res Henv_or1 tmp2 tmp Hnew_xor1xor1).
Qed.

Lemma mk_env_smulo_newer_cnf :
  forall w E g (ls1 ls2: (w.+1).-tuple literal) E' g' cs lr,
    mk_env_smulo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr.
    rewrite /mk_env_smulo.
    case Hls1 : (splitmsb ls1) => [ls1_sign ls1_tl].
    case Hls2 : (splitmsb ls2) => [ls2_sign ls2_tl].
    rewrite /=. move=> Henv Hgtt Hgls1 Hgls2.
    move: (newer_than_lits_splitmsb Hgls1 Hls1) => /andP [H1 _].
    move: (newer_than_lits_splitmsb Hgls2 Hls2) => /andP [H2 _].
    exact: (mk_env_and1_newer_cnf Henv H1 H2).
  - move=> w IH E g ls1 ls2 E' g' cs lr.
    rewrite /mk_env_smulo.
    dcase (mk_env_xor E g (snd (splitmsb ls1)) (copy w.+1 (fst (splitmsb ls1))))
    => [[[[E_xls1 g_xls1] cs_xls1] xls1] Henv_xls1].
    dcase (mk_env_xor E_xls1 g_xls1 (snd (splitmsb ls2)) (copy w.+1 (fst (splitmsb ls2))))
    => [[[[E_xls2 g_xls2] cs_xls2] xls2] Henv_xls2].
    dcase (mk_env_smulo_rec E_xls2 g_xls2 (fst (splitlsb xls1)) (fst (splitlsb xls2)) )
    => [[[[[E_rec g_rec] cs_rec] rec_or] rec_and_or] Henv_rec].
    dcase (mk_env_signextend 1 E_rec g_rec ls1) => [[[[E_wls1 g_wls1] cs_wls1] wls1] Henv_wls1].
    dcase (mk_env_signextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] wls2] Henv_wls2].
    dcase (mk_env_mul E_wls2 g_wls2 wls1 wls2) => [[[[E_mul g_mul] cs_mul] mul] Henv_mul].
    dcase (mk_env_xor1 E_mul g_mul (fst (splitmsb mul)) (fst (splitmsb (snd (splitmsb mul))))) => [[[[E_xor1 g_xor1] cs_xor1] xor1] Henv_xor1].
    dcase (mk_env_or1 E_xor1 g_xor1 rec_and_or xor1) => [[[[E_or1 g_or1] cs_or1] or1] Henv_or1].
    case=> _ <- <- _. move=> Hgtt Hgls1 Hgls2.
    case Hls1 : (splitmsb ls1) => [ls1_sign ls1_tl].
    rewrite Hls1 in Henv_xls1.
    simpl fst in Henv_xls1.
    simpl snd in Henv_xls1.
    move: (newer_than_lits_splitmsb Hgls1 Hls1) => /andP [Hgls1sign Hgls1tl].
    move: (newer_than_lits_copy w.+1 Hgls1sign) => Hgls1signs.
    move: (mk_env_xor_newer_res Henv_xls1 Hgls1tl Hgls1signs) => Hnew_xls1.
    move: (mk_env_xor_newer_cnf Henv_xls1 Hgls1tl Hgls1signs) => Hnewcnf_xls1.
    case Hls2 : (splitmsb ls2) => [ls2_sign ls2_tl].
    rewrite Hls2 in Henv_xls2.
    simpl fst in Henv_xls2.
    simpl snd in Henv_xls2.
    move: (newer_than_lits_splitmsb Hgls2 Hls2) => /andP [Hgls2sign Hgls2tl].
    move: (newer_than_lits_copy w.+1 Hgls2sign) => Hgls2signs.
    move: (mk_env_xor_newer_gen Henv_xls1) => Hgxls1.
    move: (newer_than_lits_le_newer Hgls2signs Hgxls1) => Hgx1ls2signs.
    move: (newer_than_lits_le_newer Hgls2tl Hgxls1) => Hgx1ls2tl.
    move: (mk_env_xor_newer_res Henv_xls2 Hgx1ls2tl Hgx1ls2signs) => Hnew_xls2.
    move: (mk_env_xor_newer_cnf Henv_xls2 Hgx1ls2tl Hgx1ls2signs) => Hnewcnf_xls2.
    simpl in Henv_rec.
    move: (mk_env_xor_newer_gen Henv_xls2) => Hgxls2.
    move: (newer_than_lits_le_newer Hnew_xls1 Hgxls2) => {Hnew_xls1} Hnew_xls1.
    move: (newer_than_lits_behead Hnew_xls1) => {Hnew_xls1} Hnew_xls1.
    move: (newer_than_lits_behead Hnew_xls2) => {Hnew_xls2} Hnew_xls2.
    move: (newer_than_lit_le_newer Hgtt Hgxls1) => Hgx1tt.
    move: (newer_than_lit_le_newer Hgx1tt Hgxls2) => Hgx2tt.
    move: (newer_than_lits_le_newer Hgls1 Hgxls1) => Hgx1ls1.
    move: (newer_than_lits_le_newer Hgx1ls1 Hgxls2) => Hgx2ls1.
    move: (newer_than_lits_le_newer Hgls2 Hgxls1) => Hgx1ls2.
    move: (newer_than_lits_le_newer Hgx1ls2 Hgxls2) => Hgx2ls2.
    move: (mk_env_smulo_rec_newer_res Henv_rec Hgx2tt) => [_ Hnew_rec_rec].
    move: (mk_env_smulo_rec_newer_cnf Henv_rec Hgx2tt Hnew_xls1 Hnew_xls2) => Hnewcnf_rec_rec.
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
    case Hmul: (splitmsb mul) => [mul_n mul_tl].
    case Hmul_tl: (splitmsb mul_tl) => [mul_n_minus1 mul_tl_tl].
    simpl fst.
    move: (newer_than_lits_splitmsb Hnew_gmulmul Hmul) => /andP [Hnew_mul_n Hnew_mul_tl].
    move: (newer_than_lits_splitmsb Hnew_mul_tl Hmul_tl) => /andP [Hnew_mul_n_minus1 _].
    move=> tmp tmp2. move: (tmp Hnew_mul_n Hnew_mul_n_minus1) => {tmp} Hnew_xor1xor1.
    move: (tmp2 Hnew_mul_n Hnew_mul_n_minus1) => {tmp2} Hnewcnf_xor1xor1.
    move: (mk_env_mul_newer_gen Henv_mul) => Hgwls2mul.
    move: (mk_env_xor1_newer_gen Henv_xor1) => Hgmulxor1.
    move: (pos_leb_trans Hgrecwls1 Hgwls1wls2) => Hgrecwls2.
    move: (pos_leb_trans Hgrecwls2 Hgwls2mul) => Hgrecmul.
    move: (pos_leb_trans Hgrecmul Hgmulxor1) => Hgrecxor1.
    move: (newer_than_lit_le_newer Hnew_rec_rec Hgrecxor1) => tmp.
    move: (newer_than_lit_le_newer Hgrectt Hgrecxor1) => tmp2.
    move: (mk_env_or1_newer_res Henv_or1 tmp2 tmp Hnew_xor1xor1) => Hnew_or1or1.
    move: (mk_env_or1_newer_cnf Henv_or1 tmp Hnew_xor1xor1) => Hnewcnf_or1or1.
    rewrite !newer_than_cnf_append.
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

Lemma mk_env_smulo_preserve :
  forall w E g (ls1 ls2: (w.+1).-tuple literal) E' g' cs lr,
    mk_env_smulo E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr.
    rewrite /mk_env_smulo.
    exact: (mk_env_and1_preserve).
  - move=> w IH E g ls1 ls2 E' g' cs lr.
    rewrite /mk_env_smulo.
    dcase (mk_env_xor E g (snd (splitmsb ls1)) (copy w.+1 (fst (splitmsb ls1))))
    => [[[[E_xls1 g_xls1] cs_xls1] xls1] Henv_xls1].
    dcase (mk_env_xor E_xls1 g_xls1 (snd (splitmsb ls2)) (copy w.+1 (fst (splitmsb ls2))))
    => [[[[E_xls2 g_xls2] cs_xls2] xls2] Henv_xls2].
    dcase (mk_env_smulo_rec E_xls2 g_xls2 (fst (splitlsb xls1)) (fst (splitlsb xls2)) )
    => [[[[[E_rec g_rec] cs_rec] rec_or] rec_and_or] Henv_rec].
    dcase (mk_env_signextend 1 E_rec g_rec ls1) => [[[[E_wls1 g_wls1] cs_wls1] wls1] Henv_wls1].
    dcase (mk_env_signextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] wls2] Henv_wls2].
    dcase (mk_env_mul E_wls2 g_wls2 wls1 wls2) => [[[[E_mul g_mul] cs_mul] mul] Henv_mul].
    dcase (mk_env_xor1 E_mul g_mul (fst (splitmsb mul)) (fst (splitmsb (snd (splitmsb mul))))) => [[[[E_xor1 g_xor1] cs_xor1] xor1] Henv_xor1].
    dcase (mk_env_or1 E_xor1 g_xor1 rec_and_or xor1) => [[[[E_or1 g_or1] cs_or1] or1] Henv_or1].
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

Lemma mk_env_smulo_sat :
  forall w E g (ls1 ls2: (w.+1).-tuple literal) E' g' cs lr,
    mk_env_smulo E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->  newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr.
    rewrite /mk_env_smulo.
    case Hls1 : (splitmsb ls1) => [ls1_sign ls1_tl].
    case Hls2 : (splitmsb ls2) => [ls2_sign ls2_tl].
    rewrite /=. move=> Henv Hgtt Hgls1 Hgls2.
    move: (newer_than_lits_splitmsb Hgls1 Hls1) => /andP [H1 _].
    move: (newer_than_lits_splitmsb Hgls2 Hls2) => /andP [H2 _].
    exact: (mk_env_and1_sat Henv H1 H2).
  - move=> w IH E g ls1 ls2 E' g' cs lr.
    rewrite /mk_env_smulo.
    dcase (mk_env_xor E g (snd (splitmsb ls1)) (copy w.+1 (fst (splitmsb ls1))))
    => [[[[E_xls1 g_xls1] cs_xls1] xls1] Henv_xls1].
    dcase (mk_env_xor E_xls1 g_xls1 (snd (splitmsb ls2)) (copy w.+1 (fst (splitmsb ls2))))
    => [[[[E_xls2 g_xls2] cs_xls2] xls2] Henv_xls2].
    dcase (mk_env_smulo_rec E_xls2 g_xls2 (fst (splitlsb xls1)) (fst (splitlsb xls2)) )
    => [[[[[E_rec g_rec] cs_rec] rec_or] rec_and_or] Henv_rec].
    dcase (mk_env_signextend 1 E_rec g_rec ls1) => [[[[E_wls1 g_wls1] cs_wls1] wls1] Henv_wls1].
    dcase (mk_env_signextend 1 E_wls1 g_wls1 ls2) => [[[[E_wls2 g_wls2] cs_wls2] wls2] Henv_wls2].
    dcase (mk_env_mul E_wls2 g_wls2 wls1 wls2) => [[[[E_mul g_mul] cs_mul] mul] Henv_mul].
    dcase (mk_env_xor1 E_mul g_mul (fst (splitmsb mul)) (fst (splitmsb (snd (splitmsb mul))))) => [[[[E_xor1 g_xor1] cs_xor1] xor1] Henv_xor1].
    dcase (mk_env_or1 E_xor1 g_xor1 rec_and_or xor1) => [[[[E_or1 g_or1] cs_or1] or1] Henv_or1].
    case=> <- _ <- _. move=> Hgtt Hgls1 Hgls2.
    case Hls1 : (splitmsb ls1) => [ls1_sign ls1_tl].
    rewrite Hls1 in Henv_xls1.
    simpl fst in Henv_xls1.
    simpl snd in Henv_xls1.
    move: (newer_than_lits_splitmsb Hgls1 Hls1) => /andP [Hgls1sign Hgls1tl].
    move: (newer_than_lits_copy w.+1 Hgls1sign) => Hgls1signs.
    move: (mk_env_xor_newer_res Henv_xls1 Hgls1tl Hgls1signs) => Hnew_xls1.
    move: (mk_env_xor_newer_cnf Henv_xls1 Hgls1tl Hgls1signs) => Hnewcnf_xls1.
    move: (mk_env_xor_sat Henv_xls1 Hgls1tl Hgls1signs) => Hsat_xls1.
    move: (mk_env_xor_preserve Henv_xls1) => Hpre_xls1.
    case Hls2 : (splitmsb ls2) => [ls2_sign ls2_tl].
    rewrite Hls2 in Henv_xls2.
    simpl fst in Henv_xls2.
    simpl snd in Henv_xls2.
    move: (newer_than_lits_splitmsb Hgls2 Hls2) => /andP [Hgls2sign Hgls2tl].
    move: (newer_than_lits_copy w.+1 Hgls2sign) => Hgls2signs.
    move: (mk_env_xor_newer_gen Henv_xls1) => Hgxls1.
    move: (newer_than_lits_le_newer Hgls2signs Hgxls1) => Hgx1ls2signs.
    move: (newer_than_lits_le_newer Hgls2tl Hgxls1) => Hgx1ls2tl.
    move: (mk_env_xor_newer_res Henv_xls2 Hgx1ls2tl Hgx1ls2signs) => Hnew_xls2.
    move: (mk_env_xor_newer_cnf Henv_xls2 Hgx1ls2tl Hgx1ls2signs) => Hnewcnf_xls2.
    move: (mk_env_xor_sat Henv_xls2 Hgx1ls2tl Hgx1ls2signs) => Hsat_xls2.
    move: (mk_env_xor_preserve Henv_xls2) => Hpre_xls2.
    simpl in Henv_rec.
    move: (mk_env_xor_newer_gen Henv_xls2) => Hgxls2.
    move: (newer_than_lits_le_newer Hnew_xls1 Hgxls2) => {Hnew_xls1} Hnew_xls1.
    move: (newer_than_lits_behead Hnew_xls1) => {Hnew_xls1} Hnew_xls1.
    move: (newer_than_lits_behead Hnew_xls2) => {Hnew_xls2} Hnew_xls2.
    move: (newer_than_lit_le_newer Hgtt Hgxls1) => Hgx1tt.
    move: (newer_than_lit_le_newer Hgx1tt Hgxls2) => Hgx2tt.
    move: (newer_than_lits_le_newer Hgls1 Hgxls1) => Hgx1ls1.
    move: (newer_than_lits_le_newer Hgx1ls1 Hgxls2) => Hgx2ls1.
    move: (newer_than_lits_le_newer Hgls2 Hgxls1) => Hgx1ls2.
    move: (newer_than_lits_le_newer Hgx1ls2 Hgxls2) => Hgx2ls2.
    move: (mk_env_smulo_rec_newer_res Henv_rec Hgx2tt) => [_ Hnew_rec_rec].
    move: (mk_env_smulo_rec_newer_cnf Henv_rec Hgx2tt Hnew_xls1 Hnew_xls2) => Hnewcnf_rec_rec.
    move: (mk_env_smulo_rec_sat Henv_rec Hgx2tt Hnew_xls1 Hnew_xls2) => Hsat_rec_rec.
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
    case Hmul: (splitmsb mul) => [mul_n mul_tl].
    case Hmul_tl: (splitmsb mul_tl) => [mul_n_minus1 mul_tl_tl].
    simpl fst.
    move: (newer_than_lits_splitmsb Hnew_gmulmul Hmul) => /andP [Hnew_mul_n Hnew_mul_tl].
    move: (newer_than_lits_splitmsb Hnew_mul_tl Hmul_tl) => /andP [Hnew_mul_n_minus1 _].
    move=> tmp tmp2 tmp3.
    move: (tmp Hnew_mul_n Hnew_mul_n_minus1) => {tmp} Hnew_xor1xor1.
    move: (tmp2 Hnew_mul_n Hnew_mul_n_minus1) => {tmp2} Hnewcnf_xor1xor1.
    move: (tmp3 Hnew_mul_n Hnew_mul_n_minus1) => {tmp3} Hsat_xor1xor1.
    move: (mk_env_mul_newer_gen Henv_mul) => Hgwls2mul.
    move: (mk_env_xor1_newer_gen Henv_xor1) => Hgmulxor1.
    move: (pos_leb_trans Hgrecwls1 Hgwls1wls2) => Hgrecwls2.
    move: (pos_leb_trans Hgrecwls2 Hgwls2mul) => Hgrecmul.
    move: (pos_leb_trans Hgrecmul Hgmulxor1) => Hgrecxor1.
    move: (newer_than_lit_le_newer Hnew_rec_rec Hgrecxor1) => tmp.
    move: (newer_than_lit_le_newer Hgrectt Hgrecxor1) => tmp2.
    move: (mk_env_or1_newer_res Henv_or1 tmp2 tmp Hnew_xor1xor1) => Hnew_or1or1.
    move: (mk_env_or1_newer_cnf Henv_or1 tmp Hnew_xor1xor1) => Hnewcnf_or1or1.
    move: (mk_env_or1_sat Henv_or1 tmp Hnew_xor1xor1) => Hsat_or1or1.
    move: (mk_env_or1_preserve Henv_or1) => Hpre_or1.
    rewrite !interp_cnf_append.
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
