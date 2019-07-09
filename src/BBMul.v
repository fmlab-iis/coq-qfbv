
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon BBConst BBAnd BBAdd BBShl.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_mul ===== *)

Fixpoint bit_blast_mul_rec w wn (g:generator) : w.-tuple literal -> wn.-tuple literal -> nat -> generator * cnf * w.-tuple literal :=
  if wn is _.+1 then
    fun ls1 ls2 i =>
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(g_tl, cs_tl, lrs_tl) := bit_blast_mul_rec g ls1 ls2_tl (i+1) in
      let '(g_hd, cs_hd, lrs_hd) := bit_blast_shl_int g_tl ls1 i in
      if ls2_hd == lit_tt then
        let '(g_add, cs_add, lrs_add) := bit_blast_add g_hd lrs_tl lrs_hd in
        (g_add, cs_tl++cs_hd++cs_add, lrs_add)
      else if ls2_hd == lit_ff then
             (g_tl, cs_tl, lrs_tl)
           else
             let '(g_and, cs_and, lrs_and) := bit_blast_and g_hd (copy w ls2_hd) lrs_hd in
             let '(g_add, cs_add, lrs_add) := bit_blast_add g_and lrs_tl lrs_and in
             (g_add, cs_tl++cs_hd++cs_and++cs_add, lrs_add)
  else
    fun _ _ _ =>
      bit_blast_const g (@fromNat w 0).

Fixpoint mk_env_mul_rec w wn E (g: generator) : w.-tuple literal -> wn.-tuple literal -> nat -> env * generator * cnf * w.-tuple literal :=
  if wn is _.+1 then
    fun ls1 ls2 i =>
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(E_tl, g_tl, cs_tl, lrs_tl) := mk_env_mul_rec E g ls1 ls2_tl (i+1) in
      let '(E_hd, g_hd, cs_hd, lrs_hd) := mk_env_shl_int E_tl g_tl ls1 i in
      if ls2_hd == lit_tt then
        let '(E_add, g_add, cs_add, lrs_add) := mk_env_add E_hd g_hd lrs_tl lrs_hd in
        (E_add, g_add, cs_tl++cs_hd++cs_add, lrs_add)
      else if ls2_hd == lit_ff then
             (E_tl, g_tl, cs_tl, lrs_tl)
           else
             let '(E_and, g_and, cs_and, lrs_and) := mk_env_and E_hd g_hd (copy w ls2_hd) lrs_hd in
             let '(E_add, g_add, cs_add, lrs_add) := mk_env_add E_and g_and lrs_tl lrs_and in
             (E_add, g_add, cs_tl++cs_hd++cs_and++cs_add, lrs_add)
  else
    fun _ _ _ =>
      mk_env_const E g (@fromNat w 0).

Definition bit_blast_mul w (g: generator) (ls1 ls2:  w.-tuple literal) :generator * cnf * w.-tuple literal:=
  bit_blast_mul_rec g ls1 ls2 0.

Definition mk_env_mul w E (g: generator) (ls1 ls2:  w.-tuple literal) :env * generator * cnf * w.-tuple literal:=
  mk_env_mul_rec E g ls1 ls2 0.

Lemma mk_env_mul_rec_is_bit_blast_mul_rec :
  forall wn w E g (ls1: w.-tuple literal) (ls2: wn.-tuple literal) i E' g' cs lrs,
    mk_env_mul_rec E g ls1 ls2 i = (E', g', cs, lrs) ->
    bit_blast_mul_rec g ls1 ls2 i = (g', cs, lrs).
Proof.
  elim.
  - rewrite /=/bit_blast_const => w E g ls1 ls2 i E' g' cs lrs [] _ <- <- <-. done.
  -
    intros_tuple. dcase_hyps; subst.
    rewrite (H _ _ _ _ _ _ _ _ _ _ H0)/=.
    rewrite (mk_env_shl_int_is_bit_blast_shl_int H2) (mk_env_add_is_bit_blast_add H1) (mk_env_and_is_bit_blast_and H3) (mk_env_add_is_bit_blast_add H4).
    case (ls2 == lit_tt); case (ls2 == lit_ff); by  move => [] _<- <- <-.
Qed.

Lemma mk_env_mul_is_bit_blast_mul :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_mul E g ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_mul g ls1 ls2 = (g', cs, lrs).
Proof.
  intros.
  rewrite /mk_env_mul/bit_blast_mul (mk_env_mul_rec_is_bit_blast_mul_rec H). done.
Qed.

Lemma mk_env_mul_rec_newer_gen :
  forall wn w E g  (ls1: w.-tuple literal) (ls2: wn.-tuple literal) i E' g' cs lrs,
    mk_env_mul_rec E g ls1 ls2 i = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  elim.
  - move => w E g ls1 ls2 i E' g' cs lrs [] _ <- _ _.
    exact: Pos.leb_refl.
  - intros_tuple. dcase_hyps; subst.
    move : (H _ _ _ _ _ _ _ _ _ _ H0) => Hgg0.
    move : (mk_env_shl_int_newer_gen H2) => Hg0g1.
    move : (mk_env_add_newer_gen H1) => Hg1g2.
    move : (mk_env_and_newer_gen H3) => Hg1g3.
    move : (mk_env_add_newer_gen H4) => Hg3g4.
    move : (pos_leb_trans Hgg0 (pos_leb_trans Hg0g1 Hg1g2)) => Hgg2.
    move : (pos_leb_trans (pos_leb_trans Hgg0 Hg0g1) (pos_leb_trans Hg1g3 Hg3g4)) => Hgg4.
    case (ls2 == lit_tt); case (ls2 == lit_ff); (move => [] _ <- _ _; try exact).
Qed.

Lemma mk_env_mul_newer_gen:
  forall w E g  (ls1 ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_mul E g ls1 ls2 = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  rewrite/mk_env_mul. intros. exact: (mk_env_mul_rec_newer_gen H).
Qed.

Lemma mk_env_mul_rec_newer_res :
  forall wn w E g  (ls1: w.-tuple literal) (ls2: wn.-tuple literal) i E' g' cs lrs,
    mk_env_mul_rec E g ls1 ls2 i = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g' lrs.
Proof.
  elim.
  - rewrite /=.  move => w E g ls1 ls2 i E' g' cs lrs IH Htt.
    rewrite (mk_env_const_newer_res IH); done.
  - rewrite /mk_env_mul. intros_tuple. dcase_hyps; subst.
    move : (H _ _ _ _ _ _ _ _ _ _ H0 H1) => Hg0ls.
    move : (mk_env_add_newer_res H2) => Hg2ls4.
    move : (mk_env_add_newer_res H5) => Hg4ls6.
    case (ls2 == lit_tt); case (ls2 == lit_ff); move => [] _ <- _ <-; try exact.
Qed.

Lemma mk_env_mul_newer_res :
  forall w E g  (ls1: w.-tuple literal) (ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_mul E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g' lrs.
Proof.
  move => w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_mul. exact : (mk_env_mul_rec_newer_res).
Qed.

Lemma mk_env_mul_rec_newer_cnf :
  forall wn w E g  (ls1: w.-tuple literal) (ls2: wn.-tuple literal) i E' g' cs lrs,
    mk_env_mul_rec E g ls1 ls2 i = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  elim.
  - move => w E g ls1 ls2 i E' g' cs lrs [] _ <- <- _ _ _. done.
  - intros_tuple. dcase_hyps; subst.
    move/andP : H3 => [Hgls2 Hgls0].
    move : ( H _ _ _ _ _ _ _ _ _ _ H0 H1 H2 Hgls0) => Hg0cs0.
    move : (mk_env_mul_rec_newer_gen H0) => Hgg0.
    move : (mk_env_shl_int_newer_gen H5) => Hg0g1.
    move : (mk_env_add_newer_gen H4) => Hg1g2.
    move : (mk_env_and_newer_gen H6) => Hg1g3.
    move : (mk_env_add_newer_gen H7) => Hg3g4.
    move : (mk_env_mul_rec_newer_res H0 H1) => Hg0ls.
    move : (mk_env_shl_int_newer_res (newer_than_lit_le_newer H1 Hgg0) (newer_than_lits_le_newer H2 Hgg0) H5) => Hg1ls3.
    move : (mk_env_add_newer_cnf H4 (newer_than_lit_le_newer H1 (pos_leb_trans Hgg0 Hg0g1))
           (newer_than_lits_le_newer Hg0ls Hg0g1) Hg1ls3) => Hg2cs2.
    move : (pos_leb_trans Hgg0 Hg0g1) => Hgg1.
    move : (pos_leb_trans Hg0g1 Hg1g2) => Hg0g2.
    move : (pos_leb_trans Hg1g3 Hg3g4) => Hg1g4.
    move : (pos_leb_trans Hgg0 (pos_leb_trans Hg0g1 Hg1g3)) => Hgg3.
    move : (pos_leb_trans Hg0g1 Hg1g3) => Hg0g3.
    move : (mk_env_shl_int_newer_cnf H5 (newer_than_lits_le_newer H2 Hgg0)) => Hg1cs1.
    move : (mk_env_and_newer_res H6) => Hg3ls5.
    move : (Hg3ls5 (newer_than_lits_nseq_lit w (newer_than_lit_le_newer Hgls2 Hgg1)) Hg1ls3) => {Hg3ls5}Hg3ls5.
    move : (mk_env_add_newer_cnf H7 (newer_than_lit_le_newer H1 Hgg3) (newer_than_lits_le_newer Hg0ls Hg0g3) Hg3ls5) => Hg4cs4.
    move : (mk_env_and_newer_cnf H6) => Hg3cs3.
    rewrite /copy in Hg3cs3.
    move: (Hg3cs3 (newer_than_lits_nseq_lit w (newer_than_lit_le_newer Hgls2 Hgg1)) Hg1ls3) => {Hg3cs3}Hg3cs3.
    case (ls2 == lit_tt); case (ls2 == lit_ff); move => [] _ <- <- _; try exact; rewrite !newer_than_cnf_append.
    by rewrite (newer_than_cnf_le_newer Hg0cs0 Hg0g2) (newer_than_cnf_le_newer Hg1cs1 Hg1g2) Hg2cs2.
    by rewrite (newer_than_cnf_le_newer Hg0cs0 Hg0g2) (newer_than_cnf_le_newer Hg1cs1 Hg1g2) Hg2cs2.
    by rewrite (newer_than_cnf_le_newer Hg0cs0 (pos_leb_trans Hg0g3 Hg3g4)) (newer_than_cnf_le_newer Hg1cs1 Hg1g4) (newer_than_cnf_le_newer Hg3cs3 Hg3g4) Hg4cs4.
Qed.

Lemma mk_env_mul_newer_cnf :
  forall w E g  (ls1 ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_mul E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  move => w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_mul. exact : (mk_env_mul_rec_newer_cnf).
Qed.

Lemma andB_copy_case :
  forall w b (bs : BITS w),
    andB (copy w b) bs = if b then bs else (@fromNat w 0).
Proof.
  move=> w [] bs.
  - exact: and1B.
  - rewrite -/(zero w) -fromNat0. exact: and0B.
Qed.

Lemma andB_copy_mul :
  forall w b (bs : BITS w),
    andB (copy w b) bs = bs *# b.
Proof.
  move=> w b bs. rewrite andB_copy_case. case: b.
  - rewrite mulB1; reflexivity.
  - rewrite mulB0; reflexivity.
Qed.

Lemma bit_blast_mul_rec_correct :
  forall wn w g (bs1 : BITS w) (bs2 : BITS wn) i E (ls1:w.-tuple literal) (ls2 : wn.-tuple literal) g' cs lrs,
    bit_blast_mul_rec g ls1 ls2 i = (g', cs, lrs) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (mulB bs1 (# (toNat bs2 * (2^i)))).
Proof.
  elim.
  - move => wn ig ibs1 ibs2 i E ils1 ils2 og cs olrs.
    case=> _ <- <- Henc1 Henc2 Hcnf.
    apply: (bit_blast_const_correct (g:=ig) _ Hcnf).
    apply: injective_projections => /=; first by reflexivity.
    rewrite toNatNil /= mul0n mulB0. reflexivity.
  - move => wn IH w ig ibs1. case/tupleP => [ibs2_hd ibs2_tl] i E ls1.
    case/tupleP => [ils2_hd ils2_tl] og cs olrs.
    rewrite /bit_blast_mul_rec -/bit_blast_mul_rec
            (lock interp_cnf) (lock bit_blast_add) (lock bit_blast_and)
            (lock bit_blast_shl_int) (lock enc_bits) /= !theadE !beheadCons -!lock.
    case Htl: (bit_blast_mul_rec ig ls1 ils2_tl (i+1)) => [[g_tl cs_tl] ls_tl].
    case Hhd: (bit_blast_shl_int g_tl ls1 i) => [[g_hd cs_hd] lrs_hd].
    case Hadd1: (bit_blast_add g_hd ls_tl lrs_hd) => [[g_add cs_add] lrs_add].
    case Hand: (bit_blast_and g_hd (copy w ils2_hd) lrs_hd)=> [[g_and cs_and] lrs_and].
    case Hadd2: (bit_blast_add g_and ls_tl lrs_and) => [[g_add2 cs_add2] lrs_add2].
    case Htt: (ils2_hd == lit_tt); last case Hff: (ils2_hd == lit_ff).
    + rewrite (eqP Htt) => {Hadd2 lrs_add2 cs_add2 g_add2 Hand lrs_and cs_and g_and}.
      case=> Hog Hcs Holrs Henc1 Henc2 Hcnf. rewrite -Holrs => {Holrs olrs Hog og}.
      move: (enc_bits_thead Henc2) (enc_bits_behead Henc2) => {Henc2}.
      rewrite !theadE !beheadCons => Henc2_hd Henc2_tl.
      rewrite -Hcs 2!add_prelude_append in Hcnf.
      move/andP: Hcnf => [Hcnf_tl /andP [Hcnf_hd Hcnf_add]].
      rewrite (add_prelude_enc_bit_true _ Hcnf_tl) in Henc2_hd. rewrite Henc2_hd.
      rewrite toNatCons -muln2 /=.
      have ->: ((1+toNat ibs2_tl*2) * 2^i) = ((2^i) + (toNat ibs2_tl) * (2^(i+1))).
      {
        rewrite mulnDl mul1n -mulnA -expnS addn1. reflexivity.
      }
      move: (IH _ _ _ _  (i+1) _ _ _ _ _ _ Htl Henc1 Henc2_tl Hcnf_tl) => Henc_ls_tl.
      move : (bit_blast_shl_int_correct Hhd Henc1 Hcnf_hd) => Henc_shl.
      apply: (bit_blast_add_correct Hadd1 Henc_ls_tl Henc_shl _ Hcnf_add).
      rewrite /shlBn shlB_mul2exp mulB_addn addBC. reflexivity.
    + rewrite (eqP Hff) => {Hadd2 lrs_add2 cs_add2 g_add2 Hand lrs_and cs_and g_and
                                  Hadd1 lrs_add cs_add g_add Hhd lrs_hd cs_hd g_hd}.
      case => Hog Hcs Holrs Henc_bs1 Henc_bs2 Hcnf.
      rewrite -Holrs => {Holrs olrs Hog og}. rewrite -Hcs in Hcnf => {Hcs cs}.
      move: (enc_bits_thead Henc_bs2) (enc_bits_behead Henc_bs2) => {Henc_bs2}.
      rewrite !theadE !beheadCons => Henc2_hd Henc2_tl.
      rewrite (add_prelude_enc_bit_is_false _ Hcnf) in Henc2_hd.
      rewrite (eqP Henc2_hd).
      rewrite toNatCons /= add0n -muln2 -mulnA -expnS -(addn1 i).
      exact: (IH _ _ _ _ _ _ _ _ _ _ _ Htl Henc_bs1 Henc2_tl Hcnf).
    + case => {Hadd1 lrs_add cs_add g_add} Hog Hcs Horls Henc_bs1 Henc_bs2 Hcnf.
      rewrite -Horls => {Horls olrs Hog og}.
      rewrite -Hcs 3!add_prelude_append in Hcnf => {Hcs}.
      move/andP: Hcnf => [Hcnf_tl /andP [Hcnf_hd /andP [Hcnf_and Hcnf_add2]]].
      move: (enc_bits_thead Henc_bs2) (enc_bits_behead Henc_bs2) => {Henc_bs2}.
      rewrite !theadE !beheadCons => [Henc2_hd Henc2_tl]. rewrite toNatCons.
      rewrite -muln2 mulnDl -mulnA -expnS -(addn1 i).
      move: (IH _ _ _ _ (i+1) _ _ _ _ _ _ Htl Henc_bs1 Henc2_tl Hcnf_tl) =>
      Henc_ls_tl.
      move : (bit_blast_shl_int_correct Hhd Henc_bs1 Hcnf_hd) => Henc_lrs_hd.
      move: (enc_bit_copy w Henc2_hd) => Henc_copy.
      move : (bit_blast_and_correct Hand Henc_copy Henc_lrs_hd Hcnf_and) =>
      Henc_lrs_and.
      apply: (bit_blast_add_correct Hadd2 Henc_ls_tl Henc_lrs_and _ Hcnf_add2).
      rewrite /shlBn shlB_mul2exp. rewrite andB_copy_mul.
      rewrite -mulB_muln -mulB_addn.
      replace (toNat ibs2_tl * 2 ^ (i + 1) + 2 ^ i * ibs2_hd) with
          (ibs2_hd * 2 ^ i + toNat ibs2_tl * 2 ^ (i + 1)) by ring.
      reflexivity.
Qed.

Lemma bit_blast_mul_correct :
  forall w g (bs1 bs2 : BITS w) E ls1 ls2 g' cs lrs,
    bit_blast_mul g ls1 ls2 = (g', cs, lrs) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (mulB bs1 bs2).
Proof.
  move => w g bs1 bs2 E ls1 ls2 g' cs lrs Hmul Henc_bs1 Henc_bs2 Hcnf.
  rewrite -(toNatK bs2). replace (toNat bs2) with (toNat bs2 * (2^ 0)) by ring.
  exact: (bit_blast_mul_rec_correct Hmul Henc_bs1 Henc_bs2 Hcnf).
Qed.

Lemma mk_env_mul_rec_preserve :
  forall wn w E g (ls1 : w.-tuple literal) (ls2 : wn.-tuple literal) i E' g' cs lrs,
    mk_env_mul_rec E g ls1 ls2 i = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  elim.
  - move => w E g ls1 ls2 i E' g' cs lrs [] <- _ _ _. done.
  - intros_tuple. dcase_hyps; subst.
    move : (H _ _ _ _ _ _ _ _ _ _ H0) => HEE0g.
    move : (mk_env_add_preserve H4) => HE3E4g3.
    move : (mk_env_add_preserve H1) => HE1E2g1.
    move : (mk_env_and_preserve H3) => HE1E3g1.
    move : (mk_env_shl_int_preserve H2) => HE0E1g1.
    move : (mk_env_mul_rec_newer_gen H0) => Hgg0.
    move : (mk_env_shl_int_newer_gen H2) => Hg0g1.
    move : (env_preserve_le HE1E2g1 (pos_leb_trans Hgg0 Hg0g1)) => HE1E2g.
    move : (env_preserve_le HE0E1g1 Hgg0) => HE0E1g.
    move : (env_preserve_le HE1E3g1 (pos_leb_trans Hgg0 Hg0g1)) => HE1E3g.
    move : (mk_env_and_newer_gen H3) => Hg1g3.
    move : (env_preserve_le HE3E4g3 (pos_leb_trans Hgg0 (pos_leb_trans Hg0g1 Hg1g3))) => HE3E4g.
    move : (env_preserve_trans HEE0g (env_preserve_trans HE0E1g (env_preserve_trans HE1E3g HE3E4g))) => HEE4g.
    move : (env_preserve_trans HEE0g (env_preserve_trans HE0E1g HE1E2g)) => HEE2g.
    case (ls2 == lit_tt); case (ls2 == lit_ff);
      move => [] <- _ _ _; try exact.
Qed.

Lemma mk_env_mul_preserve :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_mul E g ls1 ls2 = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move => w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_mul. move => Hmk. exact (mk_env_mul_rec_preserve Hmk).
Qed.

Lemma mk_env_mul_rec_sat :
  forall wn w E g (ls1 : w.-tuple literal) (ls2 : wn.-tuple literal) i E' g' cs lrs,
    mk_env_mul_rec E g ls1 ls2 i = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  elim.
  - move => w E g ls1 ls2 i E' g' cs lrs [] _ _ <- _ _ _ _. done.
  - intros_tuple; dcase_hyps; subst.
    move/andP : H3 => [Hgls2 Hgls0].
    move : (H _ _ _ _ _ _ _ _ _ _ H0 H1 H2 Hgls0) => HE0cs0.
    move : (mk_env_shl_int_preserve H5) => HE0E1g0.
    move : (mk_env_mul_rec_newer_gen H0) => Hgg0.
    move : (mk_env_add_preserve H4) => HE1E2g1.
    move : (mk_env_shl_int_newer_gen H5) => Hg0g1.
    move : (env_preserve_le HE1E2g1 Hg0g1) => HE1E2g0.
    move : (env_preserve_trans HE0E1g0 HE1E2g0) => HE0E2g0.
    move : (mk_env_mul_rec_newer_cnf H0 H1 H2 Hgls0) => Hcnfg0cs0.
    move : (newer_than_cnf_le_newer Hcnfg0cs0 Hg0g1) => Hcnfg1cs0.
    move : (mk_env_mul_rec_newer_res H0 H1) => Hg0ls.
    move : (newer_than_lits_le_newer Hg0ls Hg0g1) => Hg1ls.
    move : (mk_env_shl_int_newer_res (newer_than_lit_le_newer H1 Hgg0) (newer_than_lits_le_newer H2 Hgg0) H5) => Hg1ls3.
    move : (mk_env_add_sat H4 (newer_than_lit_le_newer H1 (pos_leb_trans Hgg0 Hg0g1)) Hg1ls Hg1ls3) => HcnfE2cs2.
    move : (mk_env_shl_int_sat H5 (newer_than_lits_le_newer H2 Hgg0)) => HcnfE1cs1.
    move : (mk_env_shl_int_newer_cnf H5 (newer_than_lits_le_newer H2 Hgg0)) => Hg1cs1.
    case (ls2 == lit_tt); case (ls2 == lit_ff);
    move =>[] <- _ <- _; try rewrite !interp_cnf_append;
    try (exact||
         rewrite (env_preserve_cnf HE0E2g0 Hcnfg0cs0) HE0cs0 HcnfE2cs2 (env_preserve_cnf HE1E2g1 Hg1cs1) HcnfE1cs1; done).
    move : (mk_env_and_newer_gen H6) => Hg1g3.
    move : (mk_env_add_newer_gen H7) => Hg3g4.
    move : (pos_leb_trans Hgg0 Hg0g1) => Hgg1.
    move : (pos_leb_trans Hg1g3 Hg3g4) => Hg1g4.
    move : (newer_than_lits_le_newer Hg1ls Hg1g3) => Hg3ls.
    move : (newer_than_lits_nseq_lit w Hgls2) => Hgcopyls2.
    move : (mk_env_and_newer_res H6 (newer_than_lits_le_newer Hgcopyls2 Hgg1) Hg1ls3) => Hg3ls5.
    move : (mk_env_add_sat H7 (newer_than_lit_le_newer H1 (pos_leb_trans Hgg1 Hg1g3)) Hg3ls Hg3ls5) => HE4cs4.
    move : (mk_env_and_preserve H6) => HE1E3g1.
    move : (mk_env_add_preserve H7) => HE3E4g3.
    move : (env_preserve_le HE1E3g1 Hg0g1) => HE1E3g0.
    move : (env_preserve_le HE3E4g3 (pos_leb_trans Hg0g1 Hg1g3)) => HE3E4g0.
    move : (env_preserve_le HE3E4g3 Hg1g3) => HE3E4g1.
    move : (env_preserve_trans HE0E1g0 (env_preserve_trans HE1E3g0 HE3E4g0)) => HE0E4g0.
    rewrite (env_preserve_cnf HE0E4g0 Hcnfg0cs0) HE0cs0 /=.
    move : (env_preserve_trans HE1E3g1 HE3E4g1) => HE1E4g1.
    rewrite (env_preserve_cnf HE1E4g1 Hg1cs1) HcnfE1cs1 /=.
    move : (mk_env_and_newer_cnf H6 (newer_than_lits_le_newer Hgcopyls2 Hgg1) Hg1ls3) => Hg3cs3.
    rewrite (env_preserve_cnf HE3E4g3 Hg3cs3) (mk_env_and_sat H6 (newer_than_lits_le_newer Hgcopyls2 Hgg1) Hg1ls3) HE4cs4.
    done.
Qed.

Lemma mk_env_mul_sat :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_mul E g ls1 ls2  = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move => w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_mul. move => Hmk Hgtt Hgls1 Hgls2.
  exact : (mk_env_mul_rec_sat Hmk Hgtt Hgls1 Hgls2).
Qed.
