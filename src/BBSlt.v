
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From BitBlasting Require Import QFBVSimple CNF BBCommon BBNot BBAdd.
From ssrlib Require Import Var ZAriths Tuples Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_slt ===== *)

(*Parameter bit_blast_slt : forall w : nat, generator -> w.+1.-tuple literal -> w.+1.-tuple literal -> generator * cnf * literal.
 *)
Definition bit_blast_slt w g (ls1 ls2 : w.+1.-tuple literal) : generator * cnf * literal :=
  let (sign1, uls1) := eta_expand (splitmsb ls1) in
  let (sign2, uls2) := eta_expand (splitmsb ls2) in
  let '(g_not, cs_not, r_not) := bit_blast_not g ls2 in
  let '(g_fadd, cs_fadd, cout, r_fadd) := bit_blast_full_adder g_not lit_tt ls1 r_not in
  let (gr, r) := gen g_fadd in
  let csr := [:: [:: neg_lit r; cout; neg_lit sign1; sign2];
                [:: neg_lit r; cout; sign1; neg_lit sign2];
                [:: neg_lit r; neg_lit cout; sign1; sign2];
                [:: neg_lit r; neg_lit cout; neg_lit sign1; neg_lit sign2];
                [:: r; cout; sign1; sign2];
                [:: r; cout; neg_lit sign1; neg_lit sign2];
                [:: r; neg_lit cout; neg_lit sign1; sign2];
                [:: r; neg_lit cout; sign1; neg_lit sign2]] in
  (gr, cs_not++cs_fadd++csr, r).

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

Lemma toPosZ_toNat n : forall (p: BITS n),
    toPosZ p = Z.of_nat (toNat p).
Proof.
  induction n.
  - move => p. rewrite (tuple0 p) /= /toPosZ /=; reflexivity.
  - case/tupleP => [p_hd p_tl].
    case p_hd.
    + replace [tuple of true :: p_tl] with (consB true p_tl) by done.
      rewrite toPosZCons toNatCons /=.
      rewrite Zpos_P_of_succ_nat.
      rewrite (IHn p_tl).
      apply Z.succ_inj_wd. rewrite Z.double_spec.
      rewrite -muln2 Nat2Z.inj_mul.
      ring.
    + replace [tuple of false :: p_tl] with (consB false p_tl) by done.
      rewrite toPosZCons toNatCons /=.
      rewrite (IHn p_tl).
      rewrite Z.double_spec.
      rewrite -muln2 Nat2Z.inj_add Nat2Z.inj_0 Nat2Z.inj_mul.
      ring.
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
  induction n.
  - done.
  - move => z Hge0.
    rewrite /= (IHn (Z.div2 z)).
    case Heven : (Z.even z).
     apply toNat_inj; rewrite toNat_joinlsb/=.
    + rewrite add0n 2!toNat_fromNat/= expnS -muln2.
      apply Zeven_bool_iff in Heven.
      move : (Zeven_div2 z Heven) => Hed2.
      symmetry; rewrite ->Hed2 at 1.
      rewrite Z2Nat.inj_mul; try omega.
      replace (Z.to_nat 2) with 2%coq_nat by done.
      rewrite -Nats.muln_mul -div.muln_modr; [ring|auto].
    + apply Bool.negb_true_iff in Heven.
      rewrite Z.negb_even in Heven.
      rewrite /fromNat /=.
      assert (odd (Z.to_nat z) = true) as Hoddz.
      rewrite Nats.ssrodd_odd. apply Nat.odd_spec.
      rewrite /Nat.Odd. exists (Z.to_nat (Z.div2 z)).
      apply Zodd_bool_iff in Heven.
      move : (Zodd_div2 z Heven) => Hzodd.
      rewrite ->Hzodd at 1.
      rewrite Z2Nat.inj_add; try omega. rewrite  Z2Nat.inj_mul; try omega.
      assert (Z.to_nat 2 = 2) as H2 by done; assert (Z.to_nat 1= 1) as H1 by done.
      by rewrite H2 H1 Zdiv2_div -!Nats.addn_add -!Nats.muln_mul.
      rewrite Hoddz.
      assert ((Z.to_nat (Z.div2 z)) = Nat.div2 (Z.to_nat z)) as Htonat.
      rewrite -!Z_N_nat -Nnat.N2Nat.inj_div2.
      by rewrite Z2N.inj_div2.
      by rewrite Htonat Nats.ssrdiv2_div2.
      apply Z.le_ge; apply <-Z.div2_nonneg.
      omega.
Qed.

Lemma toPosZ_lt n : forall (p1 p2: BITS n),
    ltB p1 p2 -> ((toPosZ p1)< (toPosZ p2))%Z.
Proof.
  move => p1 p2.
  rewrite !toPosZ_toNat. rewrite ltB_nat.
  move => Hltb.
  apply inj_lt.
  apply/ltP.
  done.
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

Lemma bit_blast_slt_correct_iff :
  forall w g (bs1 bs2 : BITS (w.+1)) E g' ls1 ls2 cs lr,
    bit_blast_slt g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    interp_lit E lr <-> (toZ bs1 < toZ bs2)%Z.
Proof.
  move => w ig ibs1 ibs2 E g' ils1 ils2 cs olr.
  rewrite /bit_blast_slt.
  case Hnot : (bit_blast_not ig ils2) => [[g_not cs_not] r_not].
  case Hfadd : (bit_blast_full_adder g_not lit_tt ils1 r_not) => [[[g_fadd cs_fadd] c_out] r_fadd].
  case Hg1 : (gen g_fadd) => [gr r].
  case => _ <- <-.
  move => Henc1 Henc2.
  rewrite interp_cnf_cons 2!interp_cnf_append.
  rewrite !interp_cnf_cons /=.
  rewrite !interp_lit_neg_lit /=.
  move => Hcnf.
  move/andP : Hcnf => [Htt Hcnf].
  move/andP : Hcnf => [Hcnf_not Hcnf].
  move/andP : Hcnf => [Hcnf_fadd Hcnf].
  move/andP : Hcnf => [Hcnf1 Hcnf]; move/andP : Hcnf => [Hcnf2 Hcnf]; move/andP : Hcnf => [Hcnf3 Hcnf]; move/andP : Hcnf => [Hcnf4 Hcnf]; move/andP : Hcnf => [Hcnf5 Hcnf]; move/andP : Hcnf => [Hcnf6 Hcnf]; move/andP : Hcnf => [Hcnf7 Hcnf]; move/andP : Hcnf => [Hcnf8 _].
  assert (interp_lit E lit_tt) as Hintt by done.
  assert (interp_lit E lit_tt && interp_cnf E cs_not) as Hcnf_addnot by (rewrite Hintt Hcnf_not; done).
  rewrite -add_prelude_expand in Hcnf_addnot.
  move : (bit_blast_not_correct Hnot Henc2 Hcnf_addnot) => Hrnot.
  assert (adcB true ibs1 (invB ibs2) = eta_expand (adcB true ibs1 (invB ibs2))) as Hadcb
    by apply surjective_pairing.
  assert (enc_bit E lit_tt true) as Henc_cin 
                                   by apply (add_prelude_enc_bit_tt Hcnf_addnot).
  assert (interp_lit E lit_tt && interp_cnf E cs_fadd) as Hcnf_addadd by (rewrite Hintt Hcnf_fadd; done).
  rewrite -add_prelude_expand in Hcnf_addadd.
  move : (bit_blast_full_adder_correct Hfadd Henc1 Hrnot Henc_cin Hcnf_addadd Hadcb) => Henc_add.
  move/andP/andP : Henc_add => [Henc_radd Henc_cout].
  assert ((sbbB false ibs1 ibs2).1 = ~~(adcB true ibs1 (invB ibs2)).1) as Hsbbb1 by done.
  rewrite /enc_bit in Henc_cout. move/eqP :Henc_cout=> Henc_cout.
  rewrite !enc_bits_splitmsb in Henc1 Henc2.
  move/andP: Henc1 => [Henc1msb Henc1]; move/andP: Henc2 => [Henc2msb Henc2].
  rewrite /enc_bit in Henc1msb Henc2msb.
  move/eqP : Henc1msb => Henc1msb; move/eqP : Henc2msb => Henc2msb.
  rewrite Henc1msb Henc2msb in Hcnf1 Hcnf2 Hcnf3 Hcnf4 Hcnf5 Hcnf6 Hcnf7 Hcnf8.
  move : (sbbB_ltB_leB ibs1 ibs2) => Hsubltb.
  rewrite -Z.ltb_lt.
  case Hr : (interp_lit E r);
    rewrite Hr /= in Hcnf1 Hcnf2 Hcnf3 Hcnf4 Hcnf5 Hcnf6 Hcnf7 Hcnf8.
  - split; try done.
    move => _.
    case  Hcsub : (carry_subB ibs1 ibs2);
      rewrite !Hcsub in Hsbbb1 Hsubltb; symmetry in Hsbbb1;
        move/eqP/eqP: Hsubltb => Hsubltb.
    + apply Bool.negb_true_iff in Hsbbb1.
      rewrite Hsbbb1 in Henc_cout. rewrite !Henc_cout/= in Hcnf1 Hcnf2.
      case Hs1 :((splitmsb ibs1).1); case Hs2 :((splitmsb ibs2).1);
        try (rewrite -ltB_toZ_SameSign; [exact|rewrite Hs1 Hs2; reflexivity]
                               ||rewrite Hs1 Hs2 in Hcnf1 Hcnf2; discriminate).
    + apply Bool.negb_false_iff in Hsbbb1.
      rewrite Hsbbb1 in Henc_cout. rewrite !Henc_cout/= in Hcnf1 Hcnf2 Hcnf3 Hcnf4.
      case Hs1 :((splitmsb ibs1).1); case Hs2 :((splitmsb ibs2).1);
         (rewrite Hs1 Hs2 /= in Hcnf3 Hcnf4; try discriminate).
      * rewrite -ltB_toZ_DiffSign; [|rewrite Hs1 Hs2; done].
        case Hspl1: (splitmsb ibs1) => [b1 ibss1]; case Hspl2: (splitmsb ibs2) => [b2 ibss2].
        move : (splitmsbK ibs1) => <-; move : (splitmsbK ibs2) => <-.
        rewrite Hspl1/= in Hs1; rewrite Hspl2/= in Hs2.
        rewrite Hspl1 Hspl2 Hs1 Hs2.
        apply toNat_joinmsb_lt.
      * move : (toNat_joinmsb_lt (splitmsb ibs2).2 (splitmsb ibs1).2) => Hlt.
        rewrite -Hs1 -Hs2 -!surjective_pairing !splitmsbK ltBNle in Hlt.
        rewrite Hsubltb in Hlt; discriminate.
  - split; try discriminate.
    move => Hlt.
    case  Hcsub : (carry_subB ibs1 ibs2);
      rewrite !Hcsub in Hsbbb1 Hsubltb; symmetry in Hsbbb1;
        move/eqP/eqP: Hsubltb => Hsubltb.
    + apply Bool.negb_true_iff in Hsbbb1.
      rewrite Hsbbb1 in Henc_cout. rewrite !Henc_cout/= in Hcnf5 Hcnf6 Hcnf7 Hcnf8.
      case Hs1 :((splitmsb ibs1).1); case Hs2 :((splitmsb ibs2).1);
        rewrite Hs1 Hs2 /= in Hcnf5 Hcnf6; try discriminate.
      * move : (toNat_joinmsb_lt (splitmsb ibs1).2 (splitmsb ibs2).2) => Hltneg.
        rewrite -Hs1 -Hs2 -!surjective_pairing !splitmsbK ltBNle /leB in Hltneg.
        rewrite Hsubltb /= in Hltneg; discriminate.
      * rewrite -ltB_toZ_DiffSign in Hlt; [|rewrite Hs1 Hs2; done].
        rewrite ltBNle /leB Hsubltb/= in Hlt; discriminate.
    + apply Bool.negb_false_iff in Hsbbb1.
      rewrite Hsbbb1 in Henc_cout. rewrite !Henc_cout/= in Hcnf5 Hcnf6 Hcnf7 Hcnf8.
      case Hs1 :((splitmsb ibs1).1); case Hs2 :((splitmsb ibs2).1);
        rewrite Hs1 Hs2 /= in Hcnf7 Hcnf8; try discriminate.
      * rewrite -ltB_toZ_SameSign in Hlt; [|rewrite Hs1 Hs2; done].
        rewrite ltBNle Hsubltb in Hlt; discriminate.
      * rewrite -ltB_toZ_SameSign in Hlt; [|rewrite Hs1 Hs2; done].
        rewrite ltBNle Hsubltb in Hlt; discriminate.
Qed.

Lemma bit_blast_slt_correct :
  forall w g (bs1 bs2 : BITS (w.+1)) E g' ls1 ls2 cs lr,
    bit_blast_slt g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (Z.ltb (toZ bs1) (toZ bs2)).
Proof.
  move=> w g bs1 bs2 E g' ls1 ls2 cs lr Hslt Hl1b1 Hl2b2 HiEcs.
  move : (bit_blast_slt_correct_iff Hslt Hl1b1 Hl2b2 HiEcs) => H.
  rewrite /enc_bit. apply iffBool. rewrite H -Z.ltb_lt.
  done.
Qed.

Definition mk_env_slt w (E : env) g (ls1 ls2 : w.+1.-tuple literal) : env * generator * cnf * literal :=
  let (sign1, uls1) := eta_expand (splitmsb ls1) in
  let (sign2, uls2) := eta_expand (splitmsb ls2) in
  let '(E_not, g_not, cs_not, r_not) := mk_env_not E g ls2 in
  let '(E_fadd, g_fadd, cs_fadd, cout, r_fadd) := mk_env_full_adder E_not g_not lit_tt ls1 r_not in
  let (gr, r) := gen g_fadd in
  let Er := env_upd E_fadd (var_of_lit r)
                    (orb ((interp_lit E_fadd sign1) && ~~ (interp_lit E_fadd sign2))
                         ((interp_lit E_fadd sign1 == interp_lit E_fadd sign2)
                            && ~~ interp_lit E_fadd cout)) in
  let csr := [:: [:: neg_lit r; cout; neg_lit sign1; sign2];
                [:: neg_lit r; cout; sign1; neg_lit sign2];
                [:: neg_lit r; neg_lit cout; sign1; sign2];
                [:: neg_lit r; neg_lit cout; neg_lit sign1; neg_lit sign2];
                [:: r; cout; sign1; sign2];
                [:: r; cout; neg_lit sign1; neg_lit sign2];
                [:: r; neg_lit cout; neg_lit sign1; sign2];
                [:: r; neg_lit cout; sign1; neg_lit sign2]] in
  (Er, gr, cs_not++cs_fadd++csr, r).

Lemma mk_env_slt_is_bit_blast_slt :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_slt E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_slt g ls1 ls2 = (g', cs, lr).
Proof.
  move=> w E g ls1 ls2 E' g' cs lr.
  rewrite /mk_env_slt /bit_blast_slt /gen.
  case Hmknot : (mk_env_not E g ls2) => [[[E_not g_not] cs_not] r_not].
  case Hmkfadd : (mk_env_full_adder E_not g_not lit_tt ls1 r_not)
  => [[[[E_fadd g_fadd] cs_fadd] cout] r_fadd].
  rewrite (mk_env_not_is_bit_blast_not Hmknot) {Hmknot}.
  rewrite (mk_env_full_adder_is_bit_blast_full_adder Hmkfadd) {Hmkfadd}.
  by case=> _ <- <- <-.
Qed.

Lemma mk_env_slt_newer_gen :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_slt E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_slt /gen.
  case Hmknot : (mk_env_not E g ls2) => [[[E_not g_not] cs_not] r_not].
  case Hmkfadd : (mk_env_full_adder E_not g_not lit_tt ls1 r_not)
  => [[[[E_fadd g_fadd] cs_fadd] cout] r_fadd].
  case=> _ <- _ _.
  move: (mk_env_not_newer_gen Hmknot) => {Hmknot} Hggn.
  move: (mk_env_full_adder_newer_gen Hmkfadd) => {Hmkfadd} Hgngf.
  move : (pos_leb_trans Hggn Hgngf) => Hggf {Hggn Hgngf}.
  move : (pos_leb_add_diag_r g_fadd 1) => Hgfg1.
  by apply (pos_leb_trans Hggf Hgfg1).
Qed.

Lemma mk_env_slt_newer_res :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_slt E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g' lr.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_slt /gen.
  case Hmknot : (mk_env_not E g ls2) => [[[E_not g_not] cs_not] r_not].
  case Hmkfadd : (mk_env_full_adder E_not g_not lit_tt ls1 r_not)
  => [[[[E_fadd g_fadd] cs_fadd] cout] r_fadd].
  case=> _ <- _ <-.
  by apply newer_than_lit_add_diag_r.
Qed.

Lemma splitmsb_last (T : Type) n (p : n.+1.-tuple T) (x : T) : 
  (splitmsb p).1 = last x p.
Proof. 
  induction n. 
  + case/tupleP: p => b q. by rewrite (tuple0 q)/= theadCons. 
  + case/tupleP: p => b q. rewrite /= beheadCons theadCons. 
    case E: (splitmsb q) => [b' q'].
    specialize (IHn q). rewrite E/= in IHn. simpl. 
    rewrite IHn => {IHn} {E}. by case/tupleP: q => b'' q''.
Qed. 

Lemma mk_env_slt_newer_cnf :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_slt E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_slt /gen.
  case Hmknot : (mk_env_not E g ls2) => [[[E_not g_not] cs_not] r_not].
  case Hmkfadd : (mk_env_full_adder E_not g_not lit_tt ls1 r_not)
  => [[[[E_fadd g_fadd] cs_fadd] cout] r_fadd].
  case=> _ <- <- _ Hgt Hgl1 Hgl2. rewrite /= !newer_than_cnf_append.
  (* newer_than_lit (g_fadd+1) cs_not *)
  move : (mk_env_full_adder_newer_gen Hmkfadd) => Hgngf.
  move : (pos_leb_add_diag_r g_fadd 1) => Hgfg1.  
  move : (pos_leb_trans Hgngf Hgfg1) => Hgng1.
  move : (mk_env_not_newer_cnf Hmknot Hgl2) => Hgncn.
  rewrite (newer_than_cnf_le_newer Hgncn Hgng1) /=.  
  (* newer_than_cnf (g_fadd+1) cs_fadd *)
  move : (mk_env_full_adder_newer_cnf Hmkfadd) => H.
  move : (mk_env_not_newer_gen Hmknot) => Hggn.
  move : (newer_than_lit_le_newer Hgt Hggn) => Hgnt.
  move : (newer_than_lits_le_newer Hgl1 Hggn) => Hgnl1.
  move : (mk_env_not_newer_res Hmknot Hgl2) => {Hmknot} Hgnrn.  
  move : (H Hgnt Hgnl1 Hgnrn) => {H} {Hgnl1} Hgfcf.
  rewrite (newer_than_cnf_le_newer Hgfcf Hgfg1) /=.  
  (* others *)
  rewrite !newer_than_lit_neg. 
  move : (mk_env_full_adder_newer_cout Hmkfadd Hgnt) => {Hmkfadd} Hgfcout.
  rewrite (newer_than_lit_le_newer Hgfcout Hgfg1) /=. 
  case Hls1 : (splitmsb ls1) => [sign1 others1].
  case Hls2 : (splitmsb ls2) => [sign2 others2].
  rewrite /fst.
  move : (newer_than_lits_splitmsb Hgl1 Hls1) => /andP [Hgs1 _].
  move : (newer_than_lits_splitmsb Hgl2 Hls2) => /andP [Hgs2 _].
  move : (pos_leb_trans Hggn Hgng1) => Hgg1.
  rewrite (newer_than_lit_le_newer Hgs1 Hgg1) (newer_than_lit_le_newer Hgs2 Hgg1).
  by rewrite /newer_than_lit /newer_than_var /= (pos_ltb_add_diag_r g_fadd 1).
Qed.

Lemma mk_env_slt_preserve :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_slt E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_slt /gen.
  case Hmknot : (mk_env_not E g ls2) => [[[E_not g_not] cs_not] r_not].
  case Hmkfadd : (mk_env_full_adder E_not g_not lit_tt ls1 r_not)
  => [[[[E_fadd g_fadd] cs_fadd] cout] r_fadd].
  case=> <- _ _ _.
  move : (mk_env_not_preserve Hmknot) => HpEEng.
  move : (mk_env_not_newer_gen Hmknot) => {Hmknot} Hggn.
  move : (mk_env_full_adder_preserve Hmkfadd) => HpEnEfgn.
  move : (mk_env_full_adder_newer_gen Hmkfadd) => {Hmkfadd} Hgngf.
  move : (env_preserve_le HpEnEfgn Hggn) => HpEnEfg.
  move : (env_preserve_trans HpEEng HpEnEfg) => HpEEfg.
  apply (env_preserve_trans HpEEfg).
  move : (pos_leb_trans Hggn Hgngf).
  apply env_preserve_le.
  by apply env_upd_eq_preserve.
Qed.

Lemma mk_env_full_adder_msb_eq :
  forall w E g cin (ls1 ls2 : w.+1.-tuple literal) E' g' cs cout lrs sign1 tls1 sign2 tls2,
    mk_env_full_adder E g cin ls1 ls2 = (E', g', cs, cout, lrs) ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    splitmsb ls1 = (sign1, tls1) -> 
    splitmsb ls2 = (sign2, tls2) ->
    interp_lit E sign1 == interp_lit E sign2 ->
    interp_lit E' cout = interp_lit E sign1.
Proof.
  elim.
  - move=> E g cin /tupleP [l1 t1] /tupleP [l2 t2]. 
    move=> E' g' cs cout lrs sign1 tls1 sign2 tls2.
    rewrite /mk_env_full_adder. case=> [] <- _ _ <- _ /=. 
    rewrite !theadCons. move=> Hnew1 Hnew2 [] -> _ [] -> _.
    rewrite env_upd_eq.
    by case (interp_lit E sign1); case (interp_lit E sign2); 
      case (interp_lit E cin).
  - move=> n IHn E g cin. set n' := n.+1. 
    move=> /tupleP [l1 t1] /tupleP [l2 t2] E' g' cs cout lrs sign1 tls1 sign2 tls2.
    rewrite /mk_env_full_adder -/mk_env_full_adder.
    case Hmkfa_hd :
      (mk_env_full_adder1 E g (splitlsb [tuple of l1 :: t1]).2
                          (splitlsb [tuple of l2 :: t2]).2 cin)
        => [[[[E_hd g_hd] cs_hd] lcout_hd] lrs_hd].
    rewrite /= !theadCons in Hmkfa_hd.
    case Hmkfa_tl : 
      (mk_env_full_adder E_hd g_hd lcout_hd (splitlsb [tuple of l1 :: t1]).1
                         (splitlsb [tuple of l2 :: t2]).1)
        => [[[[E_tl g_tl] cs_tl] lcout_tl] lrs_tl]. 
    rewrite /splitlsb /fst !beheadCons in Hmkfa_tl.
    case=> <- _ _ <- _.
    rewrite /= !theadCons !beheadCons.
    case Ht1: (splitmsb t1) => [t1sign t1tls].
    case Ht2: (splitmsb t2) => [t2sign t2tls].
    move=> /andP [_ Hgt1] /andP [_ Hgt2] [] <- _ [] <- _.
    move : (newer_than_lits_splitmsb Hgt1 Ht1) => /andP [Hgt1s _].
    move : (newer_than_lits_splitmsb Hgt2 Ht2) => /andP [Hgt2s _].
    move : (mk_env_full_adder1_preserve Hmkfa_hd) => HpEEhg.
    rewrite -(env_preserve_lit HpEEhg Hgt1s) -(env_preserve_lit HpEEhg Hgt2s).
    move : (mk_env_full_adder1_newer_gen Hmkfa_hd) => Hggh.
    move : (newer_than_lits_le_newer Hgt1 Hggh) => Hght1.
    move : (newer_than_lits_le_newer Hgt2 Hggh) => Hght2.
    exact: (IHn _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hmkfa_tl Hght1 Hght2 Ht1 Ht2).
Qed.

Lemma mk_env_not_msb_inv :
  forall w E g (ls : w.+1.-tuple literal) E' g' cs lrs sign tls signr tlrs,
    mk_env_not E g ls = (E', g', cs, lrs) ->
    newer_than_lits g ls -> 
    splitmsb ls = (sign, tls) -> 
    splitmsb lrs = (signr, tlrs) ->
    interp_lit E' signr = ~~ interp_lit E sign.
Proof.
  elim.
  - move=> E g /tupleP [l tl] E' g' cs /tupleP [lr tlr] sign tls signr tlrs.
    rewrite /mk_env_not. case=> [] <- _ _ <- /tval_eq <- /=. 
    rewrite !theadCons. move=> _ [] <- _ [] <- _.
    by rewrite /= env_upd_eq.
  - move=> n IHn E g. set n' := n.+1. 
    move=> /tupleP [l tl] E' g' cs /tupleP [lr tlr] sign tls signr tlrs.
    rewrite /mk_env_not -/mk_env_not.
    case Hmknot_hd : (mk_env_not1 E g (splitlsb [tuple of l :: tl]).2)
    => [[[E_hd g_hd] cs_hd] lrs_hd].
    rewrite /= !theadCons in Hmknot_hd.
    case Hmknot_tl : (mk_env_not E_hd g_hd (splitlsb [tuple of l :: tl]).1)
    => [[[E_tl g_tl] cs_tl] lrs_tl]. 
    rewrite /splitlsb /fst !beheadCons in Hmknot_tl.
    case=> <- _ _ <- /tval_eq <-.
    rewrite /= !theadCons !beheadCons.
    case Htl: (splitmsb tl) => [tlsign tlother].
    case Hlrstl: (splitmsb lrs_tl) => [lrstlsign lrstlother].
    move=> /andP [_ Hgtl] [] <- _ [] <- _.
    move : (newer_than_lits_splitmsb Hgtl Htl) => /andP [Hgtls _].
    move : (mk_env_not1_preserve Hmknot_hd) => HpEEhg.
    rewrite -(env_preserve_lit HpEEhg Hgtls).
    move : (mk_env_not1_newer_gen Hmknot_hd) => Hggh.
    move : (newer_than_lits_le_newer Hgtl Hggh) => Hghtl.
    exact: (IHn _ _ _ _ _ _ _ _ _ _ _ Hmknot_tl Hghtl Htl Hlrstl).
Qed.

Lemma mk_env_slt_sat :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_slt E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_slt /gen.
  case Hmknot : (mk_env_not E g ls2) => [[[E_not g_not] cs_not] r_not].
  case Hmkfadd : (mk_env_full_adder E_not g_not lit_tt ls1 r_not) 
  => [[[[E_fadd g_fadd] cs_fadd] cout] r_fadd].
  case=> <- _ <- _ Hgt Hgl1 Hgl2. 
  rewrite !interp_cnf_append.
  (* interp_cnf Er cs_not *)
  move : (mk_env_not_newer_cnf Hmknot Hgl2) => Hgncn.
  move : (mk_env_full_adder_preserve Hmkfadd) => HpEnEfgn.
  move : (mk_env_full_adder_newer_gen Hmkfadd) => Hgngf.
  move : (newer_than_cnf_le_newer Hgncn Hgngf) => Hgfcn.
  rewrite (interp_cnf_env_upd_newer _ _ Hgfcn).
  rewrite (env_preserve_cnf HpEnEfgn Hgncn).
  rewrite (mk_env_not_sat Hmknot Hgl2).
  (* interp_cnf Er cs_fadd *)
  move : (mk_env_not_newer_gen Hmknot) => Hggn.
  move : (newer_than_lit_le_newer Hgt Hggn) => Hgnt.
  move : (newer_than_lits_le_newer Hgl1 Hggn) => Hgnl1.
  move : (mk_env_not_newer_res Hmknot Hgl2) => Hgnrn.
  move : (mk_env_full_adder_newer_cnf Hmkfadd Hgnt Hgnl1 Hgnrn) => Hgfcf.
  rewrite (interp_cnf_env_upd_newer _ _ Hgfcf).
  rewrite (mk_env_full_adder_sat Hmkfadd Hgnt Hgnl1 Hgnrn).
  (* interp_cnf Er csr *)
  rewrite /= env_upd_eq !interp_lit_neg_lit.
  move : (mk_env_full_adder_newer_cout Hmkfadd Hgnt) => Hgfcout.
  rewrite (interp_lit_env_upd_newer _ _ Hgfcout).
  case Hls1 : (splitmsb ls1) => [sign1 tls1] /=.
  case Hls2 : (splitmsb ls2) => [sign2 tls2] /=.
  move : (pos_leb_trans Hggn Hgngf) => Hggf.
  move : (newer_than_lits_le_newer Hgl1 Hggf) => Hgfl1.
  move : (newer_than_lits_le_newer Hgl2 Hggf) => Hgfl2.
  move : (newer_than_lits_splitmsb Hgfl1 Hls1) => /andP [Hgfs1 _].
  move : (newer_than_lits_splitmsb Hgfl2 Hls2) => /andP [Hgfs2 _].
  rewrite (interp_lit_env_upd_newer _ _ Hgfs1) (interp_lit_env_upd_newer _ _ Hgfs2).
  case Hsign_eq : (interp_lit E_fadd sign1 == interp_lit E_fadd sign2).
  - case Hs1 : (interp_lit E_fadd sign1); case Hs2 : (interp_lit E_fadd sign2);
      case Hcout : (interp_lit E_fadd cout); (try by rewrite /=);
        rewrite Hs1 Hs2 in Hsign_eq; by discriminate Hsign_eq.
  - case Hr_not : (splitmsb r_not) => [sign_not tl_not].
    move : (mk_env_not_msb_inv Hmknot Hgl2 Hls2 Hr_not) => Hes_not.
    move : (newer_than_lits_splitmsb Hgnl1 Hls1) => /andP [Hgns1 _].
    rewrite (env_preserve_lit HpEnEfgn Hgns1) in Hsign_eq.
    assert (interp_lit E_not sign1 == interp_lit E_not sign_not) as Hes1sn.
    + rewrite Hes_not.
      move : (mk_env_not_preserve Hmknot) => HpEEng.
      move : (env_preserve_le HpEnEfgn Hggn) => HpEnEfg.
      move : (env_preserve_trans HpEEng HpEnEfg) => HpEEfg.
      move : (newer_than_lits_splitmsb Hgl2 Hls2) => /andP [Hgs2 _].
      rewrite (env_preserve_lit HpEEfg Hgs2) in Hsign_eq.
      move : Hsign_eq.
      by case (interp_lit E_not sign1); case (interp_lit E sign2).
    move : (mk_env_full_adder_msb_eq Hmkfadd Hgnl1 Hgnrn Hls1 Hr_not Hes1sn) => Hecout.
    rewrite Hecout.
    move : (env_preserve_lit HpEnEfgn Hgns1) => Hesign1; rewrite Hesign1.
    move : Hsign_eq.
    by case (interp_lit E_not sign1); case (interp_lit E_fadd sign2).
Qed.
