From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBUlt.
From ssrlib Require Import ZAriths Seqs Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_slt ===== *)

Definition bit_blast_slt g ls1 ls2: generator * cnf * literal :=
  let (tls1, sign1) := eta_expand (splitmsl ls1) in
  let (tls2, sign2) := eta_expand (splitmsl ls2) in
  let '(g_tl, cs_tl, r_tl) := bit_blast_ult g tls1 tls2 in
  let (gr, r) := gen g_tl in
  (* r <->  (((s1 <-> s2) && u) || (s1 && ~s2)) *)
  let csr := [::
                 [:: neg_lit r; sign1; neg_lit sign2];
                 [:: neg_lit r; sign1; r_tl];
                 [:: neg_lit r; neg_lit sign2; r_tl];
                 [:: r; neg_lit sign1; sign2];
                 [:: r; neg_lit sign1; neg_lit r_tl];
                 [:: r; sign2; neg_lit r_tl]
             ] in
  (gr, catrev cs_tl csr, r).

Lemma bit_blast_slt_correct g bs1 bs2 E ls1 ls2 g' cs lr :
  bit_blast_slt g ls1 ls2 = (g', cs, lr) ->
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 -> interp_cnf E (add_prelude cs) ->  
  enc_bit E lr (sltB bs1 bs2).
Proof.
  rewrite /bit_blast_slt /gen. 
  case Hbb_tl : (bit_blast_ult g (splitmsl ls1).1 (splitmsl ls2).1) => [[g_tl cs_tl] r_tl]. 
  rewrite (lock splitmsl). case=> _ <- <- Henc1 Henc2 Hics.
  rewrite add_prelude_catrev in Hics. move: Hics => /andP [Hics_tl Hics]. 
  rewrite add_prelude_expand in Hics. move: Hics => /andP [Htt Hics].
  move: (enc_bits_splitmsb Htt Henc1) => /andP [Henc_t1 Henc_s1].
  move: (enc_bits_splitmsb Htt Henc2) => /andP [Henc_t2 Henc_s2]. 
  move: (bit_blast_ult_correct Hbb_tl Henc_t1 Henc_t2 Hics_tl). 
  rewrite /enc_bit => /eqP Hr_tl. rewrite /sltB /interp_lit -Hr_tl.
  rewrite /= !interp_lit_neg_lit -lock in Hics; t_clear.
  rewrite /enc_bit in Henc_s1 Henc_s2. 
  move: Henc_s1 Henc_s2 Hics => /eqP -> /eqP ->.
  by case (E g_tl); case ((splitmsb bs1).2); case ((splitmsb bs2).2); case (interp_lit E r_tl). 
Qed.

Definition mk_env_slt E g ls1 ls2: env * generator * cnf * literal :=
  let (tls1, sign1) := eta_expand (splitmsl ls1) in
  let (tls2, sign2) := eta_expand (splitmsl ls2) in
  let '(E_tl, g_tl, cs_tl, r_tl) := mk_env_ult E g tls1 tls2 in
  let (gr, r) := gen g_tl in
  let Er := env_upd E_tl (var_of_lit r) (
                      ((interp_lit E_tl sign1 == interp_lit E_tl sign2)
                         &&
                         interp_lit E_tl r_tl) 
                      || (interp_lit E_tl sign1 && ~~ interp_lit E_tl sign2)
                    ) in
  (* r <->  (((s1 <-> s2) && u) || (s1 && ~s2)) *)
  let csr := [::
                 [:: neg_lit r; sign1; neg_lit sign2];
                 [:: neg_lit r; sign1; r_tl];
                 [:: neg_lit r; neg_lit sign2; r_tl];
                 [:: r; neg_lit sign1; sign2];
                 [:: r; neg_lit sign1; neg_lit r_tl];
                 [:: r; sign2; neg_lit r_tl]
             ] in
  (Er, gr, catrev cs_tl csr, r).

Lemma mk_env_slt_is_bit_blast_slt E g ls1 ls2 E' g' cs lr:
    mk_env_slt E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_slt g ls1 ls2 = (g', cs, lr).
Proof.
  rewrite /mk_env_slt /bit_blast_slt /gen.
  dcase (mk_env_ult E g (splitmsl ls1).1 (splitmsl ls2).1)
        => [[[[E_tl g_tl] cs_tl] r_tl] Henv_tl].
  rewrite (mk_env_ult_is_bit_blast_ult Henv_tl).
  by case=> _ <- <- <-.
Qed.

Lemma mk_env_slt_newer_gen E g ls1 ls2 E' g' cs lr:
    mk_env_slt E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  rewrite /mk_env_slt /bit_blast_slt /gen.
  dcase (mk_env_ult E g (splitmsl ls1).1 (splitmsl ls2).1)
        => [[[[E_tl g_tl] cs_tl] r_tl] Henv_tl].
  case=> _ <- _ _.
  move: (mk_env_ult_newer_gen Henv_tl) => {Henv_tl} Hggt.
  eapply pos_leb_trans.
  exact: Hggt.
  exact: pos_leb_add_diag_r.
Qed.

Lemma mk_env_slt_newer_res E g ls1 ls2 E' g' cs lr:
    mk_env_slt E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g' lr.
Proof.
  rewrite /mk_env_slt /bit_blast_slt /gen.
  dcase (mk_env_ult E g (splitmsl ls1).1 (splitmsl ls2).1)
        => [[[[E_tl g_tl] cs_tl] r_tl] Henv_tl].
  case=> _ <- _ <-.
  by apply newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_slt_newer_cnf E g ls1 ls2 E' g' cs lr:
    mk_env_slt E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_slt /bit_blast_slt /gen.
  case Hls1: (splitmsl ls1) => [tl1 sign1].
  case Hls2: (splitmsl ls2) => [tl2 sign2].
  simpl [fst snd].
  dcase (mk_env_ult E g tl1 tl2) => [[[[E_tl g_tl] cs_tl] r_tl] Henv_tl].
  case=> _ <- <- _ => Hgtt Hgls1 Hgls2.
  rewrite newer_than_cnf_catrev.
  move: (newer_than_lits_splitmsl Hgtt Hgls1). 
  rewrite Hls1 /fst /snd => /andP [Hgtl1 Hgs1].
  move: (newer_than_lits_splitmsl Hgtt Hgls2).
  rewrite Hls2 /fst /snd => /andP [Hgtl2 Hgs2].
  move: (mk_env_ult_newer_cnf Henv_tl Hgtt Hgtl1 Hgtl2) => Hncnf_tl.
  move: (pos_leb_add_diag_r g_tl 1) => Hgtgt1.
  rewrite (newer_than_cnf_le_newer Hncnf_tl Hgtgt1).
  rewrite andTb /newer_than_cnf /newer_than_lit /=.
  rewrite !newer_than_lit_neg.
  move: (mk_env_ult_newer_gen Henv_tl) => Hggt.
  move: (pos_leb_trans Hggt Hgtgt1) => Hggt1.
  rewrite !(newer_than_lit_le_newer Hgs1 Hggt1).
  rewrite !(newer_than_lit_le_newer Hgs2 Hggt1).
  move: (mk_env_ult_newer_res Henv_tl Hgtt) => Hgtrt.
  rewrite !(newer_than_lit_le_newer Hgtrt Hgtgt1).
  rewrite /newer_than_lit /newer_than_var /=.
  by rewrite (pos_ltb_add_diag_r g_tl 1).
Qed.

Lemma mk_env_slt_preserve E g ls1 ls2 E' g' cs lr:
    mk_env_slt E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  rewrite /mk_env_slt /bit_blast_slt /gen.
  case Hls1: (splitmsl ls1) => [tl1 sign1].
  case Hls2: (splitmsl ls2) => [tl2 sign2].
  simpl [fst snd].
  dcase (mk_env_ult E g tl1 tl2) => [[[[E_tl g_tl] cs_tl] r_tl] Henv_tl].
  case=> <- _ _ _.
  move: (mk_env_ult_preserve Henv_tl) => Hpre_tl.
  move: (mk_env_ult_newer_gen Henv_tl) => Hggtl.
  eapply env_preserve_trans.
  exact: Hpre_tl.
  eapply env_preserve_le.
  exact: env_upd_eq_preserve.
  exact: Hggtl.
Qed.

Lemma mk_env_slt_sat E g ls1 ls2 E' g' cs lr:
    mk_env_slt E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  rewrite /mk_env_slt /bit_blast_slt /gen.
  case Hls1: (splitmsl ls1) => [tl1 sign1].
  case Hls2: (splitmsl ls2) => [tl2 sign2].
  simpl [fst snd].
  dcase (mk_env_ult E g tl1 tl2) => [[[[E_tl g_tl] cs_tl] r_tl] Henv_tl].
  case=> <- _ <- _ Hgtt Hgls1 Hgls2.
  rewrite !interp_cnf_catrev.
  move: (newer_than_lits_splitmsl Hgtt Hgls1). 
  rewrite Hls1 /fst /snd => /andP [Hgtl1 Hgs1].
  move: (newer_than_lits_splitmsl Hgtt Hgls2). 
  rewrite Hls2 /fst /snd => /andP [Hgtl2 Hgs2].
  move: (mk_env_ult_newer_cnf Henv_tl Hgtt Hgtl1 Hgtl2) => Hncnf_tl.
  rewrite (interp_cnf_env_upd_newer _ _ Hncnf_tl).
  rewrite (mk_env_ult_sat Henv_tl Hgtt Hgtl1 Hgtl2) andTb.
  (* interp_cnf Er csr *)
  rewrite /= env_upd_eq !interp_lit_neg_lit.
  move: (mk_env_ult_newer_res Henv_tl Hgtt) => Hgtrt.
  rewrite (interp_lit_env_upd_newer _ _ Hgtrt).
  move: (mk_env_ult_newer_gen Henv_tl) => Hggt.
  move: (newer_than_lit_le_newer Hgs1 Hggt) => Hgts1.
  move: (newer_than_lit_le_newer Hgs2 Hggt) => Hgts2.
  rewrite (interp_lit_env_upd_newer _ _ Hgts1) (interp_lit_env_upd_newer _ _ Hgts2).
  by case (interp_lit E_tl sign1);
    case (interp_lit E_tl sign2);
    case (interp_lit E_tl r_tl).
Qed.

(*
Lemma toNegZCons n b  (p:BITS n) : toNegZ (consB b p) = if b then Zdouble (toNegZ p) else Zsucc (Zdouble (toNegZ p)).
Proof. done. Qed.

Lemma toPosZCons n b  (p:BITS n) : toPosZ (consB b p) = if b then Zsucc (Zdouble (toPosZ p)) else Zdouble (toPosZ p).
Proof. done. Qed.

Lemma splitmsb_ones :
  forall n, splitmsb (ones n.+1) = (true, ones n).
Proof.
  move => n.
  apply injective_projections.
  rewrite  splitmsb_msb msb_ones /=; reflexivity.
  simpl.
  induction n.
  rewrite /ones /copy /= nseqCons beheadCons; reflexivity.
  rewrite /ones /copy nseqCons tupleE/= beheadCons.
  replace (splitmsb (nseq_tuple n.+1 true)) with (eta_expand (splitmsb (nseq_tuple n.+1 true))).
  rewrite IHn /= theadE /= /joinlsb /=.
  rewrite /ones /copy /= nseqCons tupleE; reflexivity.
    by (symmetry; apply injective_projections).
Qed.

Lemma joinmsb_ones :
  forall n, joinmsb (true, ones n) =  ones n.+1.
Proof.
  move => n.
  induction n.
  simpl. replace (joinlsb (nilB, true)) with (singleBit true) by done.
  rewrite /ones /copy nseqCons tuple0 tupleE; done.
  rewrite /ones /copy /= nseqCons beheadCons theadE.
  rewrite IHn.
  rewrite /joinlsb /= nseqCons tupleE; done.
Qed.

Lemma dropmsb_ones :
  forall n , dropmsb (ones n.+1) = (ones n).
Proof.
  move => n.
  rewrite /dropmsb.
  rewrite splitmsb_ones /=; done.
Qed.

Lemma toZ_zero: forall n, toZ (zero n.+1) = 0%Z.
Proof.
  move => n.
  induction n.
  - rewrite /toZ /= /toPosZ /=; done.
  - rewrite -fromNat0 in IHn. rewrite -fromNat0.
    rewrite /toZ splitmsb_fromNat /= div.div0n /=.
    rewrite /toZ splitmsb_fromNat /= div.div0n /= in IHn.
    replace (# (0)) with (consB false (@fromNat n 0)) by done.
    rewrite toPosZCons. rewrite IHn /=.
    done.
Qed.

Lemma toZ_ones : forall n, toZ (ones n.+1) = (-1)%Z.
Proof.
  move => n.
  induction n.
  - rewrite /toZ.
    replace (splitmsb (ones 1)) with (true, (splitmsb (ones 1)).2) by
        (apply injective_projections; [rewrite splitmsb_msb; reflexivity|simpl; reflexivity]).
    simpl; reflexivity.
  - rewrite /toZ.
    rewrite splitmsb_ones.
    rewrite Z.opp_succ -Z.sub_1_r.
    symmetry; apply Zplus_minus_eq; simpl.
    rewrite /ones /copy nseqCons toNegZCons.
    rewrite /toZ splitmsb_ones Z.opp_succ -Z.sub_1_r in IHn.
    rewrite -Z.add_opp_r -Z.opp_add_distr in IHn.
    apply Z.opp_inj_wd in IHn. rewrite Z.opp_involutive /= in IHn.
    apply Z.add_move_r in IHn; simpl in IHn.
    rewrite IHn.
    done.
Qed.


Lemma toZ_joinmsb0 n: forall (p: BITS n),
    toZ (joinmsb (false, p)) = toPosZ p.
Proof.
  move => p.
  rewrite /toZ joinmsbK; reflexivity.
Qed.

Lemma toPosZ_joinmsb0 n: forall (p: BITS n),
    toPosZ (joinmsb (false, p)) = toPosZ p.
Proof.
  induction n.
  - move => p.
    rewrite (tuple0 p)/= /joinmsb /joinlsb /toPosZ/=; reflexivity.
  - case/tupleP => [p_hd p_tl].
    move : (IHn p_tl).
    case Hpd : p_hd.
    + replace (toPosZ [tuple of false :: p_tl]) with (toPosZ (consB false p_tl)) by done.
      rewrite /= !theadE !beheadCons/= /joinlsb/= !toPosZCons /=.
      move => IHm.
      rewrite IHm !Z.double_spec; reflexivity.
    + replace (toPosZ [tuple of false :: p_tl]) with (toPosZ (consB false p_tl)) by done.
      rewrite /= !theadE !beheadCons/= /joinlsb/= !toPosZCons /=.
      move => IHm.
      rewrite IHm; reflexivity.
Qed.

Lemma toZ_joinmsb1 n : forall (p: BITS n),
    toZ (joinmsb (true, p)) = (Zopp (Zsucc (toNegZ p)))%Z.
Proof.
  move => p.
  rewrite /toZ joinmsbK; reflexivity.
Qed.

Lemma toPosZ_joinmsb1 n : forall (p: BITS n),
    toPosZ (joinmsb (true, p)) = ((toPosZ p) + 2^(Z.of_nat n))%Z.
Proof.
  induction n.
  - move => p.
    rewrite (tuple0 p)/= /joinmsb /joinlsb /toPosZ/=; reflexivity.
  - case/tupleP => [p_hd p_tl].
    move : (IHn p_tl).
    case Hpd : p_hd.
    + replace (toPosZ [tuple of true :: p_tl]) with (toPosZ (consB true p_tl)) by done.
      rewrite /= !theadE !beheadCons/= /joinlsb/= !toPosZCons /=.
      move => IHm.
      rewrite IHm Z.pow_pos_fold Zpos_P_of_succ_nat !Z.double_spec Z.mul_add_distr_l.
      rewrite Z.pow_succ_r; try omega.
    + replace (toPosZ [tuple of false :: p_tl]) with (toPosZ (consB false p_tl)) by done.
      rewrite /= !theadE !beheadCons/= /joinlsb/= !toPosZCons /=.
      move => IHm.
      rewrite IHm Z.pow_pos_fold Zpos_P_of_succ_nat !Z.double_spec Z.mul_add_distr_l.
      rewrite Z.pow_succ_r; try omega.
Qed.

Lemma toNat_joinmsb1 n (p: BITS n) : toNat (joinmsb (true, p)) = toNat p + 2^n.
Proof. rewrite toNat_joinmsb /=. ring. Qed.

Lemma ltB_joinmsb1 n: forall (p q : BITS n),
    ltB (joinmsb (true,p)) (joinmsb (true, q)) = ltB p q.
Proof.
  move => p q.
  rewrite ltB_nat. rewrite !toNat_joinmsb1.
  replace (toNat p + 2 ^ n < toNat q + 2 ^ n) with (toNat p < toNat q).
  symmetry; apply ltB_nat.
  rewrite ltn_add2r.
  done.
Qed.

Lemma toNegZ_toNat n : forall (p: BITS n),
    toNegZ p = Z.of_nat ((2^n-1) - (toNat p)).
Proof.
  induction n.
  - move => p. rewrite (tuple0 p) /toNegZ /=; reflexivity.
  - case/tupleP => [p_hd p_tl].
    case p_hd.
    + replace [tuple of true :: p_tl] with (consB true p_tl) by done.
      rewrite toNegZCons toNatCons /= (IHn p_tl).
      rewrite Z.double_spec expnS.
      rewrite Nat2Z.inj_sub;
        [| move : (toNatBounded p_tl) => Hnb; apply lt_n_Sm_le; rewrite -addn1 subnK; move/ltP :Hnb => Hnb; [done|apply Nats.expn2_gt0]].
      rewrite Z.mul_sub_distr_l.
      replace (Z.of_nat (2 * 2 ^ n - 1 - (1 + (toNat p_tl).*2))) with
          (Z.of_nat (2 * 2 ^ n - 1) - Z.of_nat (1 + (toNat p_tl).*2))%Z by
          (rewrite -Nat2Z.inj_sub;
           [done|
            rewrite -muln2; apply/leP /Nats.ltn_leq_sub; apply/ltP; rewrite mulnC;
            apply Nat.mul_2_mono_l; apply/ltP /toNatBounded]).
      rewrite !Nat2Z.inj_add Z.sub_add_distr -muln2 !Nat2Z.inj_mul !Nat2Z.inj_sub .
      rewrite Nat2Z.inj_mul.
      assert (Z.of_nat 2 = 2%Z) as H2 by done; assert (Z.of_nat 1= 1%Z) as H1 by done.
      rewrite !H1 !H2 Z.mul_sub_distr_l Z.mul_1_r. ring.
      rewrite -expnS; apply/leP /Nats.expn2_gt0.
      apply/leP /Nats.expn2_gt0.
    + replace [tuple of false :: p_tl] with (consB false p_tl) by done.
      rewrite toNegZCons toNatCons /= (IHn p_tl) /= Z.double_spec add0n.
      rewrite !Nat2Z.inj_sub. rewrite -muln2 expnS !Nat2Z.inj_mul.
      assert (Z.of_nat 2 = 2%Z) as H2 by done;
      assert (Z.of_nat 1= 1%Z) as H1 by done.
      rewrite !H1 !H2 !Z.mul_sub_distr_l Z.mul_1_r -Z.add_1_r. ring.
      apply/leP /Nats.expn2_gt0.
      rewrite expnS -muln2 mulnC. apply/leP /Nats.ltn_leq_sub.
      apply/ltP /mult_lt_compat_l.
      apply/ltP /toNatBounded. omega. apply/leP /Nats.expn2_gt0.
      apply lt_n_Sm_le. rewrite -addn1 subnK. apply/ltP /toNatBounded. apply Nats.expn2_gt0.
Qed.

Lemma fromPosZ_fromNat n:
  forall z,
    (z >= 0)%Z ->
    @fromPosZ n z = @fromNat n (Z.to_nat z).
Proof.
  move=> z H. rewrite -extra.fromPosZ_fromNat (Z2Nat.id _ (Z.ge_le _ _ H)).
  reflexivity.
Qed.

Lemma ltB_toZ_Pos :
  forall n (p1 p2 :BITS n.+1),
    ~~((splitmsb p1).1 || (splitmsb p2).1) -> ltB p1 p2 = Z.ltb (toZ p1) (toZ p2)%Z.
Proof.
  move => n.
  move => p1 p2 Hmsb.
  move : (splitmsbK p1) => <-; move : (splitmsbK p2) => <-.
  case Hmsb1 : ((splitmsb p1).1); rewrite Hmsb1 in Hmsb; try discriminate.
  rewrite orFb in Hmsb.
  move/eqP/eqP: Hmsb=> Hmsb2.
  apply Bool.negb_true_iff in Hmsb2.
  case Hspl1: (splitmsb p1) => [b1 ps1];
  case Hspl2: (splitmsb p2) => [b2 ps2].
  rewrite Hspl1 /= in Hmsb1; rewrite Hspl2 /= in Hmsb2.
  rewrite Hmsb1 Hmsb2.
  rewrite /toZ !joinmsbK ltB_joinmsb0 !toPosZ_toNat ltB_nat.
  case Hlt : (toNat ps1 < toNat ps2).
  - move/ltP : Hlt => Hlt.
    apply inj_lt in Hlt.
    rewrite /Z.ltb Hlt; reflexivity.
  - move/ltP in Hlt. apply not_lt in Hlt.
    apply inj_ge in Hlt.
    rewrite /Z.ge in Hlt. rewrite /Z.ltb.
    case Hge : ((Z.of_nat (toNat ps1) ?= Z.of_nat (toNat ps2))%Z); try reflexivity.
    rewrite Hge in Hlt. destruct Hlt; reflexivity.
Qed.

Lemma ltB_toZ_Neg n :
  forall (p1 p2 : BITS n.+1),
    ((splitmsb p1).1 && (splitmsb p2).1) -> ltB p1 p2 = (Z.ltb (toZ p1) (toZ p2)%Z).
Proof.
  move => p1 p2 Hmsb.
  move : (splitmsbK p1) => <-; move : (splitmsbK p2) => <-.
  case Hmsb1 : ((splitmsb p1).1); rewrite Hmsb1 in Hmsb; try discriminate.
  rewrite andTb in Hmsb. move/eqP/eqP: Hmsb => Hmsb2.
  case Hspl1: (splitmsb p1) => [b1 ps1];
  case Hspl2: (splitmsb p2) => [b2 ps2].
  rewrite Hspl1 /= in Hmsb1; rewrite Hspl2 /= in Hmsb2.
  rewrite Hmsb1 Hmsb2.
  rewrite /toZ !joinmsbK ltB_joinmsb1 !toNegZ_toNat ltB_nat.
  case Hlt : ((toNat ps1 < toNat ps2)).
  - move/ltP : Hlt => Hlt.
    apply inj_lt in Hlt.
    symmetry.
    rewrite !Nat2Z.inj_sub; try (apply/ltP /Nats.expn2_gt0).
    apply Z.opp_lt_mono  in Hlt.
    apply Zplus_lt_compat_l with (p:=(Z.of_nat (2 ^ n) - Z.of_nat 1)%Z) in Hlt.
    apply Zsucc_lt_compat, Z.opp_lt_mono, Z.ltb_lt in Hlt.
    rewrite Hlt; reflexivity.
    apply/leP; rewrite -ltnS; replace ((2 ^ n - 1).+1) with ((2 ^ n - 1)+1) by (rewrite addn1; reflexivity).
    rewrite subnK; [apply toNatBounded|apply Nats.expn2_gt0].
    apply/leP; rewrite -ltnS; replace ((2 ^ n - 1).+1) with ((2 ^ n - 1)+1) by (rewrite addn1; reflexivity).
    rewrite subnK; [apply toNatBounded|apply Nats.expn2_gt0].
  - rewrite ltnNge in Hlt.
    apply Bool.negb_false_iff in Hlt.
    move/leP : Hlt => Hlt.
    apply inj_le in Hlt.
    symmetry; rewrite !Nat2Z.inj_sub; try (apply/ltP /Nats.expn2_gt0).
    apply Z.opp_le_mono in Hlt.
    apply Zplus_le_compat_l with (p:=(Z.of_nat (2 ^ n) - Z.of_nat 1)%Z) in Hlt.
    apply Zsucc_le_compat, Z.opp_le_mono in Hlt.
    rewrite -Z.gtb_ltb /Z.gtb.
    apply Z.leb_le in Hlt.
    rewrite /Z.leb in Hlt.
    case Hcomp: ((- Z.succ (Z.of_nat (2 ^ n) - Z.of_nat 1 + - Z.of_nat (toNat ps2))
                           ?= - Z.succ (Z.of_nat (2 ^ n) - Z.of_nat 1 + - Z.of_nat (toNat ps1)))%Z); try done.
    + rewrite Hcomp in Hlt; discriminate.
    + apply/leP. rewrite -ltnS.
      replace ((2 ^ n - 1).+1) with ((2 ^ n - 1)+1) by (rewrite addn1; reflexivity);
        rewrite subnK; [apply toNatBounded|apply Nats.expn2_gt0].
      apply/leP. rewrite -ltnS. replace ((2 ^ n - 1).+1) with ((2 ^ n - 1)+1) by (rewrite addn1; reflexivity);
    rewrite subnK; [apply toNatBounded|apply Nats.expn2_gt0].
Qed.

Lemma ltB_toZ_SameSign n :
  forall (p1 p2 : BITS n.+1),
    ((splitmsb p1).1 = (splitmsb p2).1) -> ltB p1 p2 = (Z.ltb (toZ p1) (toZ p2)%Z).
Proof.
  move => p1 p2.
  case Hp1 : ((splitmsb p1).1); case Hp2: ((splitmsb p2).1);
    try discriminate.
  - move => _; apply ltB_toZ_Neg; rewrite Hp1 Hp2; done.
  - move => _; apply ltB_toZ_Pos; rewrite Hp1 Hp2; done.
Qed.


Lemma ltB_toZ_SameSign2 n :
  forall (p1 p2 : BITS n.+1) sign1 utl1 sign2 utl2,
    splitmsb p1 = (sign1, utl1) ->
    splitmsb p2 = (sign2, utl2) ->
    sign1 = sign2 ->
    ltB utl1 utl2 = (Z.ltb (toZ p1) (toZ p2)%Z).
Proof.
  move => p1 p2 sign1 utl1 sign2 utl2 Hmsb1 Hmsb2.
  case Hsign1: sign1; case Hsign2: sign2; try discriminate; move=> eq.
  all: rewrite Hsign1 in Hmsb1; rewrite Hsign2 in Hmsb2.
  - have tmp: ((splitmsb p1).1 && (splitmsb p2).1) by rewrite Hmsb1 Hmsb2.
    move: (ltB_toZ_Neg tmp) => <-.
    have tmp1: (p1 = joinmsb (true, utl1)) by rewrite -Hmsb1 splitmsbK.
    have tmp2: (p2 = joinmsb (true, utl2)) by rewrite -Hmsb2 splitmsbK.
    by rewrite tmp1 tmp2 -ltB_joinmsb1.
  - have tmp: (~~ ((splitmsb p1).1 || (splitmsb p2).1)) by rewrite Hmsb1 Hmsb2.
    move: (ltB_toZ_Pos tmp) => <-.
    have tmp1: (p1 = joinmsb (false, utl1)) by rewrite -Hmsb1 splitmsbK.
    have tmp2: (p2 = joinmsb (false, utl2)) by rewrite -Hmsb2 splitmsbK.
    by rewrite tmp1 tmp2 -ltB_joinmsb0.
Qed.


Lemma ltB_toZ_DiffSign n:forall (p1 p2 : BITS n.+1),
    ~((splitmsb p1).1 = (splitmsb p2).1) -> ltB p1 p2 = (Z.ltb (toZ p2) (toZ p1)%Z).
Proof.
  move => p1 p2 Hcmp.
  rewrite ltB_nat.
  move : (splitmsbK p1) => <-; move : (splitmsbK p2) => <-.
  case Hspl1: (splitmsb p1) => [b1 ps1]; case Hspl2: (splitmsb p2) => [b2 ps2].
  case Hp1 : ((splitmsb p1).1); case Hp2: ((splitmsb p2).1);
    rewrite Hp1 Hp2 in Hcmp; move/eqP : Hcmp => Hcmp; try discriminate.
  -
    rewrite Hspl1 Hspl2 /= in Hp1 Hp2. rewrite Hp1 Hp2.
    rewrite toNat_joinmsb0 toNat_joinmsb1 toZ_joinmsb0 toZ_joinmsb1.
    move : (toNatBounded ps2) => Hb2.
    assert ((toNat ps1 + 2 ^ n < toNat ps2) = false) as Hlt.
    move/ltP : Hb2 => Hb2.
    apply plus_lt_le_compat with (toNat ps2) (2^n) 0 (toNat ps1) in Hb2;
      [|apply Peano.le_0_n].
    rewrite -plus_n_O in Hb2.
    apply/ltP /gt_asym. move/ltP : Hb2 => Hb2.
    apply/ltP. rewrite -Nats.addn_add addnC in Hb2. exact.
    rewrite Hlt; symmetry.
    rewrite toNegZ_toNat toPosZ_toNat.
    rewrite /Z.ltb /=.
    case Hlt2: ((Z.of_nat (toNat ps2) ?= - Z.succ (Z.of_nat (2 ^ n - 1 - toNat ps1)))%Z); try reflexivity.
    apply -> Z.compare_lt_iff in Hlt2.
    omega.
  -
    rewrite Hspl1 Hspl2 /= in Hp1 Hp2. rewrite Hp1 Hp2.
    rewrite toNat_joinmsb0 toNat_joinmsb1 toZ_joinmsb0 toZ_joinmsb1.
    rewrite toNegZ_toNat toPosZ_toNat.
    assert ((toNat ps1 < toNat ps2 + 2 ^ n) = true) as Hlt.
    move : (toNatBounded ps1) => Hps1b.
    move/ltP /lt_plus_trans in Hps1b.
    move : (Hps1b (toNat ps2)) => Hps1.
    rewrite -Nats.addn_add addnC in Hps1.
    apply/ltP. exact.
    rewrite Hlt; symmetry.
    rewrite Z.ltb_lt. omega.
Qed.

Lemma toNat_joinmsb_lt n : forall (p1 p2 : BITS n),
    ltB (joinmsb (false, p2)) (joinmsb (true, p1)).
Proof.
  move => p1 p2.
  rewrite ltB_nat.
  rewrite !toNat_joinmsb /= addnC mul0n mul1n.
  apply/ltP /plus_lt_le_compat.
  apply/ltP /toNatBounded.
  apply Nat.le_0_l.
Qed.

Lemma ltB_toZ_DiffSign2 n :
  forall (p1 p2 : BITS n.+1) sign1 utl1 sign2 utl2,
    splitmsb p1 = (sign1, utl1) ->
    splitmsb p2 = (sign2, utl2) ->
    sign1 <> sign2 ->
    (sign1 && ~~sign2) = (Z.ltb (toZ p1) (toZ p2)%Z).
Proof.
  move => p1 p2 sign1 utl1 sign2 utl2 Hmsb1 Hmsb2.
  case Hsign1: sign1; case Hsign2: sign2; try discriminate; move=> eq; try (by destruct eq).
  all: rewrite Hsign1 in Hmsb1; rewrite Hsign2 in Hmsb2.
  - have tmp: ((splitmsb p2).1 <> (splitmsb p1).1) by rewrite Hmsb1 Hmsb2.
    rewrite /=.
    move: (ltB_toZ_DiffSign tmp) => <-.
    have tmp1: (p1 = joinmsb (true, utl1)) by rewrite -Hmsb1 splitmsbK.
    have tmp2: (p2 = joinmsb (false, utl2)) by rewrite -Hmsb2 splitmsbK.
    by rewrite tmp1 tmp2 toNat_joinmsb_lt.
  - have tmp: ((splitmsb p2).1 <> (splitmsb p1).1) by rewrite Hmsb1 Hmsb2.
    rewrite /=.
    move: (ltB_toZ_DiffSign tmp) => <-.
    have tmp1: (p1 = joinmsb (false, utl1)) by rewrite -Hmsb1 splitmsbK.
    have tmp2: (p2 = joinmsb (true, utl2)) by rewrite -Hmsb2 splitmsbK.
    have contra: (p1<p2)%bits.
    {
        by rewrite tmp1 tmp2 toNat_joinmsb_lt.
    }
    apply leB_weaken in contra.
    rewrite leBNlt in contra.
    move/eqP/eqP: contra.
    by rewrite Bool.negb_true_iff.
Qed.
*)


Lemma mk_env_slt_env_equal E1 E2 g ls1 ls2 E1' E2' g1' g2' cs1 cs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_slt E1 g ls1 ls2 = (E1', g1', cs1, lrs1) ->
  mk_env_slt E2 g ls1 ls2 = (E2', g2', cs2, lrs2) ->
  env_equal E1' E2' /\ g1' = g2' /\ cs1 = cs2 /\ lrs1 = lrs2.
Proof.
  rewrite /mk_env_slt => Heq.
  dcase (mk_env_ult E1 g (splitmsl ls1).1 (splitmsl ls2).1)
  => [[[[E_tl1 g_tl1] cs_tl1] lrs_tl1] Htl1].
  dcase (mk_env_ult E2 g (splitmsl ls1).1 (splitmsl ls2).1)
  => [[[[E_tl2 g_tl2] cs_tl2] lrs_tl2] Htl2].
  move: (mk_env_ult_env_equal Heq Htl1 Htl2) => {Heq Htl1 Htl2} [Heq [? [? ?]]]; subst.
  dcase (gen g_tl2) => [[g' r'] Hg']. case=> ? ? ? ?; case=> ? ? ? ?; subst.
  repeat split. rewrite !(env_equal_interp_lit _ Heq). apply: env_equal_upd.
  assumption.
Qed.
