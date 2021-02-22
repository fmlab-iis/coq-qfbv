
From Coq Require Import ZArith List Recdef.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBConst BBExtract BBRepeat BBEq BBIte BBShl BBLshr .
From ssrlib Require Import ZAriths Seqs Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* sar lemmas *)
(* Lemma sarB_add bs i j : *)
(*   sarB i (sarB j bs) = sarB (i + j) bs . *)
(* Proof . *)
(*   by rewrite /sarB iter_add . *)
(* Qed . *)

(* Lemma sarB1_size bs : *)
(*   size (sarB1 bs) = size bs . *)
(* Proof . *)
(*   elim : bs => [| b bs Hbs] . *)
(*   - done . *)
(*   - by rewrite /sarB1 size_joinmsb /= addn1 . *)
(* Qed . *)

(* Lemma sarB_size n bs : *)
(*   size (sarB n bs) = size bs . *)
(* Proof . *)
(*   rewrite /sarB /iter . *)
(*   elim: n; first done . *)
(*   move => n IH . *)
(*   by rewrite sarB1_size . *)
(* Qed . *)

Lemma enc_bit_msb E ls bs :
  interp_lit E lit_tt -> enc_bits E ls bs ->
  enc_bit E (msl ls) (msb bs) .
Proof .
  destruct ls => Htt Hlsbs .
  - rewrite (enc_bits_nil_l E bs) in Hlsbs .
    rewrite (eqP Hlsbs) /msl /msb -enc_bit_tt_ff /= .
    by apply /eqP .
  - destruct bs .
    + rewrite (enc_bits_nil_r E (l::ls)) in Hlsbs .
      by rewrite (eqP Hlsbs) /msl /msb /= -enc_bit_tt_ff .
    + move : Hlsbs .
      set lls := l::ls .
      set bbs := b::bs .
      assert (size lls > 0); first done .
      assert (size bbs > 0); first done .
      rewrite (enc_bits_splitmsb_nonempty E H H0) /msl /msb /= => /andP [_ Hlast] .
      done .
Qed .

(* ===== bit_blast_ashr ===== *)

Definition bit_blast_ashr_int1 g ls : generator * cnf * word :=
  (g, [::], droplsl (joinmsl ls (msl ls))) .

Function bit_blast_ashr_int g ls (n : N) {wf N.lt n} : generator * cnf * word :=
  match n with
  | N0 => ((g, [::]), ls)
  | _ => let '(g_m, cs_m, ls_m) := bit_blast_ashr_int g ls (n - 1)%num in
         let '(g1, cs1, ls1) := bit_blast_ashr_int1 g_m ls_m in
         ((g1, catrev cs_m cs1), ls1)
  end.
Proof.
  - move=> _ _ n p Hp. rewrite -Hp. move: (N.le_pred_l n) => Hle.
    rewrite N.sub_1_r. move/(N.lt_eq_cases (N.pred n) n): Hle. case=> Hn.
    + assumption.
    + apply: N.lt_pred_l. move=> Hn0. rewrite Hn0 in Hp. discriminate.
  - exact: N.lt_wf_0.
Qed.

Definition mk_env_ashr_int1 E g ls : env * generator * cnf * word :=
  (E, g, [::], droplsl (joinmsl ls (msl ls))) .

Function mk_env_ashr_int E g ls (n : N) {wf N.lt n} : env * generator * cnf * word :=
  match n with
  | N0 => (((E, g), [::]), ls)
  | _ => let: (E_m, g_m, cs_m, ls_m) := mk_env_ashr_int E g ls (n - 1)%num in
         let: (E', g', cs, ls') := mk_env_ashr_int1 E_m g_m ls_m in
         (((E', g'), catrev cs_m cs), ls')
  end.
Proof.
  - move=> _ _ _ n p Hp. rewrite -Hp. move: (N.le_pred_l n) => Hle.
    rewrite N.sub_1_r. move/(N.lt_eq_cases (N.pred n) n): Hle. case=> Hn.
    + assumption.
    + apply: N.lt_pred_l. move=> Hn0. rewrite Hn0 in Hp. discriminate.
  - exact: N.lt_wf_0.
Qed.

Lemma bit_blast_ashr_int_N0 g ls :
  bit_blast_ashr_int g ls N0 = (g, [::], ls).
Proof.
  symmetry. apply: R_bit_blast_ashr_int_complete.
  apply: (R_bit_blast_ashr_int_0 _ _ N0). reflexivity.
Qed.

Lemma bit_blast_ashr_int_Npos g ls p g_m cs_m ls_m g' cs1 lrs :
  bit_blast_ashr_int g ls (N.pos p - 1) = (g_m, cs_m, ls_m) ->
  bit_blast_ashr_int1 g_m ls_m = (g', cs1, lrs) ->
  bit_blast_ashr_int g ls (N.pos p) = (g', catrev cs_m cs1, lrs).
Proof.
  move=> Hbb Hbb1. move: (Logic.eq_sym Hbb) => {Hbb} Hbb.
  move: (R_bit_blast_ashr_int_correct Hbb) => {Hbb} Hbb.
  symmetry. apply: R_bit_blast_ashr_int_complete.
  by apply: (R_bit_blast_ashr_int_1 _ _ _ _ _ _ _ Hbb _ _ _ _ _ _ _ Hbb1).
Qed.

Lemma mk_env_ashr_int_N0 E g ls :
  mk_env_ashr_int E g ls N0 = (E, g, [::], ls).
Proof.
  symmetry. apply: R_mk_env_ashr_int_complete.
  apply: (R_mk_env_ashr_int_0 _ _ _ N0). reflexivity.
Qed.

Lemma mk_env_ashr_int_Npos E g ls p E_m g_m cs_m ls_m E' g' cs1 lrs :
  mk_env_ashr_int E g ls (N.pos p - 1) = (E_m, g_m, cs_m, ls_m) ->
  mk_env_ashr_int1 E_m g_m ls_m = (E', g', cs1, lrs) ->
  mk_env_ashr_int E g ls (N.pos p) = (E', g', catrev cs_m cs1, lrs).
Proof.
  move=> Hbb Hbb1. move: (Logic.eq_sym Hbb) => {Hbb} Hbb.
  move: (R_mk_env_ashr_int_correct Hbb) => {Hbb} Hbb.
  symmetry. apply: R_mk_env_ashr_int_complete.
    by apply: (R_mk_env_ashr_int_1 _ _ _ _ _ _ _ _ Hbb _ _ _ _ _ _ _ _ _ Hbb1).
Qed.

Lemma mk_env_ashr_int_Nsucc E g ls n :
  mk_env_ashr_int E g ls (N.succ n) =
  let '(E_m, g_m, cs_m, ls_m) := mk_env_ashr_int E g ls n in
  let '(E', g', cs, lrs) := mk_env_ashr_int1 E_m g_m ls_m in
  (E', g', catrev cs_m cs, lrs).
Proof.
  dcase (mk_env_ashr_int E g ls (N.succ n)) => [[[[E_s g_s] cs_s] ls_s] Hv_s].
  dcase (mk_env_ashr_int E g ls n) => [[[[E_m g_m] cs_m] lrs_m] Hv_m].
  dcase (mk_env_ashr_int1 E_m g_m lrs_m) => [[[[E' g'] cs'] lrs'] Hv'].
  symmetry in Hv_s. move: (R_mk_env_ashr_int_correct Hv_s) => Hr. inversion Hr.
  - move: (N.neq_0_succ n) => Hne. rewrite -H in Hne. apply: False_ind; apply: Hne; reflexivity.
  - move: (R_mk_env_ashr_int_complete H6). rewrite H3. rewrite -N.pred_sub N.pred_succ.
    move=> Hv_ashr. rewrite H7 Hv_m in Hv_ashr. case: Hv_ashr => ? ? ? ?; subst.
    rewrite Hv' in H8. case: H8 => ? ? ? ?; subst. done.
Qed.



Lemma bit_blast_ashr_int1_correct :
  forall g bs E ls g' cs lrs,
    bit_blast_ashr_int1 g ls = (g', cs, lrs) ->
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (sarB1 bs).
Proof.
  move => g bs E ls g' cs lrs .
  rewrite /bit_blast_ashr_int1 .
  case => _ _ <- Henc_bits Hcs .
  rewrite /sarB1 /= .
  apply : enc_bits_droplsb; first apply : (add_prelude_tt Hcs) .
  rewrite enc_bits_joinmsb Henc_bits /= .
  apply : enc_bit_msb; last done .
  apply : (add_prelude_tt Hcs) .
Qed .

Lemma bit_blast_ashr_int_correct :
  forall g bs n E ls g' cs lrs,
    bit_blast_ashr_int g ls n = (g', cs, lrs) ->
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (sarB n bs).
Proof.
  move => g bs n E ls. eapply bit_blast_ashr_int_ind.
  - clear n. move=> n Hn g' cs lrs. case=> ? ? ?; subst => /=.
    move=> H _; assumption.
  - clear n. move=> n [] => //=. move=> p Hn _ IH.
    move=> g_m cs_m ls_m Hm. move=> g1 cs1 ls1 H1.
    move=> g' cs lrs. case=> ? ? ?; subst => /=.
    move => Hlsbs Hcsm. rewrite add_prelude_catrev in Hcsm.
    move/andP: Hcsm => [Hcsm Hcs1]. move: (IH _ _ _ Hm Hlsbs Hcsm) => Hls_mbs.
    move: (bit_blast_ashr_int1_correct H1 Hls_mbs Hcs1).
    rewrite sarB1_sarB_succ. rewrite -addn1.
    have ->: ((N.pos p - 1)%num + 1) = nat_of_pos p.
    { replace 1 with (nat_of_bin 1) by reflexivity.
      rewrite -nat_of_add_bin. rewrite N.sub_add.
      - exact: nat_of_bin_pos.
      - exact: Npos_ge1. }
    by apply.
Qed.

Lemma size_bit_blast_ashr_int1 g ls g' cs lrs :
  bit_blast_ashr_int1 g ls = (g', cs, lrs) ->
  size ls = size lrs .
Proof .
  rewrite /bit_blast_ashr_int1 .
  case => _ _ <- .
  rewrite size_droplsl size_joinmsl .
  rewrite subn1 addn1.
  reflexivity .
Qed .

Lemma size_bit_blast_ashr_int g n ls g' cs lrs :
  bit_blast_ashr_int g ls n = (g', cs, lrs) ->
  size ls = size lrs.
Proof.
  move: g' cs lrs. eapply bit_blast_ashr_int_ind.
  - clear n. move=> n Hn g' cs lrs [] ? ? ?; subst => /=. reflexivity.
  - clear n. move=> n [] p Hn //=. move=> _ IH g_m cs_m ls_m Hbb g1 cs1 ls1 Hbb1.
    move=> g' cs lrs [] ? ? ?; subst => /=. rewrite (IH _ _ _ Hbb).
    exact: (size_bit_blast_ashr_int1 Hbb1).
Qed.



Fixpoint bit_blast_ashr_rec g ls ns (i : N) : generator * cnf * word :=
  match ns with
  | [::] => (g, [::], ls)
  | ns_hd::ns_tl =>
    let '(g_tl, cs_tl, ls_tl) := bit_blast_ashr_rec g ls ns_tl (i * 2) in
    if ns_hd == lit_tt then
      let '(g_hd, cs_hd, ls_hd) := bit_blast_ashr_int g_tl ls_tl i in
      (g_hd, catrev cs_tl cs_hd, ls_hd)
    else if ns_hd == lit_ff then
           (g_tl, cs_tl, ls_tl)
         else
           let '(g_hd, cs_hd, ls_hd) := bit_blast_ashr_int g_tl ls_tl i in
           let '(g_ite, cs_ite, ls_ite) := bit_blast_ite g_hd ns_hd ls_hd ls_tl in
           (g_ite, catrev cs_tl (catrev cs_hd cs_ite), ls_ite)
  end.

Definition bit_blast_ashr g ls ns : generator * cnf * word :=
  if size ls > 1 then
    let 'log2szls := Z.to_nat (Z.log2_up (Z.of_nat (size ls))) in
    let '(g_zero_hi, cs_zero_hi, zero_hi) :=
        bit_blast_const g (from_nat (size ns - log2szls) 0) in
    let '(g_msb, cs_msb, msb) :=
        bit_blast_extract g_zero_hi (size ls).-1 (size ls).-1 ls in
    let '(g_msbs, cs_msbs, msbs) :=
        bit_blast_repeat g_msb (size ls) msb in
    let '(g_hi, cs_hi, ns_hi) :=
        bit_blast_extract g_msbs (size ns).-1 log2szls ns in
    let '(g_lo, cs_lo, ns_lo) := bit_blast_extract g_hi log2szls.-1 0 ns in
    let '(g_eq, cs_eq, l_eq) := bit_blast_eq g_lo ns_hi zero_hi in
    let '(g_shr, cs_shr, ls_shr) := bit_blast_ashr_rec g_eq ls ns_lo 1%num in
    let '(g_ite, cs_ite, ls_ite) := bit_blast_ite g_shr l_eq ls_shr msbs in
    (g_ite,
     catrev cs_zero_hi
            (catrev cs_msb
                    (catrev cs_msbs
                            (catrev cs_hi
                                    (catrev cs_lo
                                            (catrev cs_eq
                                                    (catrev cs_shr cs_ite)))))),
     ls_ite)
  else
    bit_blast_ashr_rec g ls ns 1%num .

Lemma bit_blast_ashr_rec_correct g bs ns i E ls lns g' cs lrs :
  bit_blast_ashr_rec g ls lns i = (g', cs, lrs) ->
  enc_bits E ls bs ->
  enc_bits E lns ns ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E lrs (sarB (to_nat ns * i) bs) .
Proof .
  move => Hashrrec Hlsbs Hlnsns .
  move : (enc_bits_size Hlnsns) => Hsizelnsns .
  move : lns ns Hsizelnsns i g' cs lrs Hashrrec Hlsbs Hlnsns.
  apply : seq_ind2 => [|lns_hd ns_hd lns_tl ns_tl Hsizelnns IH] i g' cs lrs .
  - by case => _ <- <- .
  - rewrite /= .
    dcase (bit_blast_ashr_rec g ls lns_tl (i*2)) => [[[g_tl cs_tl] ls_tl] Hashrrec] .
    dcase (bit_blast_ashr_int g_tl ls_tl i) => [[[g_hd cs_hd] ls_hd] Hashrint] /= .
    case Hlnshdtt : (lns_hd == lit_tt) .
    + case => _ <- <- Hlsbs Hlnsns Hcnf .
      move : Hlnsns; rewrite enc_bits_cons => /andP [Hlnsns_hd Hlnsns_tl] .
      move : Hcnf; rewrite add_prelude_catrev => /andP [Hcnfcs_tl Hcnfcs_hd] .
      move : (IH _ _ _ _ Hashrrec Hlsbs Hlnsns_tl Hcnfcs_tl) => Hlstlnstl .
      move : (bit_blast_ashr_int_correct Hashrint Hlstlnstl Hcnfcs_hd) .
      rewrite sarB_add .
      move/eqP : Hlnshdtt => Hlnshdtt .
      rewrite Hlnshdtt in Hlnsns_hd .
      rewrite (add_prelude_enc_bit_true ns_hd Hcnfcs_tl) in Hlnsns_hd .
      rewrite Hlnsns_hd.
      rewrite nat_of_mul_bin (mulnC i 2%num). rewrite mulnA muln2 /=.
      by rewrite -[(1+ (to_nat ns_tl).*2)*i]/(i + ((to_nat ns_tl).*2)*i) .
    + case Hlnshdff : (lns_hd == lit_ff) .
      * case => _ <- <- Hlsbs Hlnsns Hcnfcs_tl .
        move : Hlnsns; rewrite enc_bits_cons => /andP [Hlnsns_hd Hlnsns_tl] .
        move : (IH _ _ _ _ Hashrrec Hlsbs Hlnsns_tl Hcnfcs_tl) .
        move/eqP : Hlnshdff => Hlnshdff .
        rewrite Hlnshdff in Hlnsns_hd .
        rewrite (add_prelude_enc_bit_is_not_true ns_hd Hcnfcs_tl) in Hlnsns_hd .
        rewrite (negbTE Hlnsns_hd) .
        by rewrite nat_of_mul_bin (mulnC i 2%num) mulnA muln2 /= .
      * dcase (bit_blast_ite g_hd lns_hd ls_hd ls_tl) => [[[g_ite cs_ite] ls_ite] Hite] .
        case => _ <- <- Hlsbs Hlnsns Hcnf .
        move : Hcnf; rewrite add_prelude_catrev => /andP [Hcnfcs_tl Hcnfcs_others] .
        move : Hcnfcs_others; rewrite add_prelude_catrev => /andP [Hcnfcs_hd Hcnfcs_ite] .
        move : Hlnsns; rewrite enc_bits_cons => /andP [Hlnsns_hd Hlnsns_tl] .
        move : (IH _ _ _ _ Hashrrec Hlsbs Hlnsns_tl Hcnfcs_tl) => Hlstlbs .
        move : (bit_blast_ashr_int_correct Hashrint Hlstlbs Hcnfcs_hd) => Hlshdbs .
        rewrite sarB_add in Hlshdbs .
        move : (size_bit_blast_ashr_int Hashrint) => /eqP Hlshdtl .
        rewrite eq_sym in Hlshdtl .
        move : (bit_blast_ite_correct Hlshdtl Hite Hlnsns_hd Hlshdbs Hlstlbs Hcnfcs_ite) .
        destruct ns_hd .
        + rewrite nat_of_mul_bin (mulnC i 2%num) mulnA muln2 .
          by rewrite -[(i+(to_nat ns_tl).*2 * i)]/((true + (to_nat ns_tl).*2)*i) .
        + rewrite nat_of_mul_bin (mulnC i 2%num) mulnA muln2 .
          by rewrite -[(false + (to_nat ns_tl).*2) * i]/((to_nat ns_tl).*2 *i) .
Qed .

Lemma ashrB_log2 bs ns :
  size bs > 1 ->
  size ns = size bs ->
  sarB (to_nat ns) bs =
  let log2szbs := Z.to_nat (Z.log2_up (Z.of_nat (size bs))) in
  if extract (size ns).-1 log2szbs ns == from_nat (size ns - log2szbs) 0
  then sarB (to_nat (extract log2szbs.-1 0 ns) * 1%num) bs
  else repeat (size bs) (extract (size bs).-1 (size bs).-1 bs) .
Proof .
  rewrite /= => Hszbsgt1 Hszeq .
  remember (Z.to_nat (Z.log2_up (Z.of_nat (size bs)))) as log2szbs .
  rewrite muln1 .
  have : (1 < Z.of_nat (size bs))%Z .
  {
    rewrite -[1%Z]/(Z.of_nat 1) .
    apply inj_lt .
    apply Nats.ltn_lt => // .
  }
  move => Hszbsgt1Z .
  move : (Z.lt_trans _ _ _ Z.lt_0_1 Hszbsgt1Z) => Hszbsgt0Z .
  have : log2szbs < size bs .
  {
    rewrite Heqlog2szbs .
    rewrite -{2}(Nat2Z.id (size bs)) .
    apply Nats.lt_ltn .
    apply Z2Nat.inj_lt; trivial .
    - apply Z.log2_up_nonneg .
    - apply Nat2Z.is_nonneg .
    - by apply Z.log2_up_lt_lin .
  }
  rewrite -{1}Hszeq => Hszlt .
  have : 0 < log2szbs .
  {
    rewrite Heqlog2szbs .
    apply Nats.lt_ltn .
    rewrite -[0]/(Z.to_nat 0) .
    apply Z2Nat.inj_lt .
    + done .
    + apply Z.log2_up_nonneg .
    + apply (Z.log2_up_pos _ Hszbsgt1Z) .
  }
  move => Hlog2szbsgt0 .
  have : log2szbs.-1.+1 = log2szbs .
  {
    rewrite Nat.succ_pred_pos; trivial .
      by apply Nats.ltn_lt .
  }
  move => Hlog2szbsprednaddn1 .
  dcase (extract (size ns).-1 log2szbs ns == (size ns - log2szbs) -bits of (0)%bits); case => /eqP Hcon .
  - rewrite -to_nat_bounded_high_zeros; trivial .
    + by rewrite Hlog2szbsprednaddn1 . 
    + by rewrite Hlog2szbsprednaddn1 Hcon .
  - rewrite extract_high;
      last by rewrite -{2}(ltn_predK Hszbsgt1); apply ltnSn .
    rewrite -{2}(ltn_predK Hszbsgt1) subSnn high1_msb .
    have : repeat (size bs) [:: msb bs] = copy (size bs) (msb bs) .
    {
      elim : (size bs); first done .
      by move => n IH /=; rewrite IH .
    }       
    case => -> .
    apply sarB_oversize .
    move : (@to_nat_bounded_high_nonzeros log2szbs.-1 ns) .
    rewrite Hlog2szbsprednaddn1 => Hhinonzero .
    move : Hcon => /eqP Hcon .
    move : (Hhinonzero Hszlt Hcon) => {Hhinonzero} .
    apply leq_trans .
    rewrite Heqlog2szbs .
    elim : (Z.log2_up_spec _ Hszbsgt1Z) => _ Hexplog2 .
    move: (Z2Nat.inj_le _ _ (Z.lt_le_incl _ _ Hszbsgt0Z)
           (Z.pow_nonneg _ (Z.log2_up (Z.of_nat (size bs))) Z.le_0_2)) .
    elim => Honlyif _ .
    move : (Honlyif Hexplog2) .
    rewrite Nat2Z.id => {Honlyif Hexplog2} Hexplog2 .
    rewrite -(Nat2Z.id 2) .
    rewrite -Z2Nat_expn .
  - by apply Nats.le_leq .
  - done .
  - by apply Z.log2_up_nonneg .
Qed .        

Corollary bit_blast_ashr_correct g bs ns E ls lns g' cs lrs :
  size ls > 0 ->
  size ls = size lns ->
  bit_blast_ashr g ls lns = (g', cs, lrs) ->
  enc_bits E ls bs ->
  enc_bits E lns ns ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E lrs (sarBB bs ns) .
Proof .
  move => Hszgt0 Hszeq Hlshr Hlsbs Hlnsns Hcnf. rewrite sarBB_sarB.
  rewrite -(muln1 (to_nat ns)).
  move : Hlshr; rewrite /bit_blast_ashr .
  remember (Z.to_nat (Z.log2_up (Z.of_nat (size ls)))) as log2szls .
  dcase (1 < size ls); case => /ltP Hcon .
  - dcase (bit_blast_const g (from_nat (size lns - log2szls) 0)) =>
    [[[g_zero_hi] cs_zero_hi] zero_hi] Hzero_hi .
    dcase (bit_blast_extract g_zero_hi (size ls).-1 (size ls).-1 ls) =>
    [[[g_msb cs_msb] ls_msb]] Hmsb .
    dcase (bit_blast_repeat g_msb (size ls) ls_msb) =>
    [[[g_msbs cs_msbs] ls_msbs]] Hmsbs .
    dcase (bit_blast_extract g_msbs (size lns).-1 log2szls lns) =>
    [[[g_hi cs_hi] ns_hi]] Hhi .
    dcase (bit_blast_extract g_hi log2szls.-1 0 lns) =>
    [[[g_lo cs_lo] ns_lo]] Hlo .
    dcase (bit_blast_eq g_lo ns_hi zero_hi) =>
    [[[g_eq cs_eq] l_eq]] Heq .
    dcase (bit_blast_ashr_rec g_eq ls ns_lo 1) =>
    [[[g_shr cs_shr] ls_shr]] Hshr .
    dcase (bit_blast_ite g_shr l_eq ls_shr ls_msbs) =>
    [[[g_ite cs_ite] ls_ite]] Hite .
    move => Hret .
    move : Hret Hcnf .
    case => _ <- <- .
    rewrite !add_prelude_catrev .
    move => /andP [Hcnf_zero_hi /andP  [Hcnf_msb /andP  [Hcnf_msbs
            /andP [Hcnf_hi /andP [Hcnf_lo /andP  [Hcnf_eq /andP
            [Hcnf_shr Hcnf_ite]]]]]]] .
    move : (bit_blast_const_correct Hzero_hi Hcnf_zero_hi)
    => {Hzero_hi Hcnf_zero_hi cs_zero_hi} Henc_zero_hi .
    move : (bit_blast_extract_correct Hmsb Hlsbs Hcnf_msb)
    => {Hmsb Hcnf_msb cs_msb} Henc_msb .
    move : (bit_blast_repeat_correct Hmsbs Henc_msb Hcnf_msbs)
    => {Hmsbs Hcnf_msbs cs_msbs} Henc_msbs .
    move : (bit_blast_extract_correct Hhi Hlnsns Hcnf_hi)
    => {Hhi Hcnf_hi cs_hi} Henc_hi .
    move : (bit_blast_extract_correct Hlo Hlnsns Hcnf_lo)
    => {g_hi Hlo Hcnf_lo cs_lo} Henc_lo .
    have : size ns_hi = size zero_hi .
    {
      rewrite (enc_bits_size Henc_zero_hi) (enc_bits_size Henc_hi)
              size_extract size_from_nat .
      rewrite -mypredn_sub addn1 -S_pred_pos // .
      rewrite Heqlog2szls -Hszeq .
      apply Nats.ltn_lt .
      rewrite subn_gt0 .
      by  apply log2_lt_lin_nat .
    }
    move => Hszhi .
    move : (bit_blast_eq_correct Heq Hszhi Henc_hi Henc_zero_hi Hcnf_eq)
    => {g_lo Hszhi Henc_hi Henc_zero_hi Heq Hcnf_eq cs_eq} Henc_eq .
    move : (bit_blast_ashr_rec_correct Hshr Hlsbs Henc_lo Hcnf_shr)
    => {g_eq Hshr Henc_lo Hcnf_shr cs_shr} Henc_shr .
    have : size ls_shr == size ls_msbs .
    {
      by rewrite (enc_bits_size Henc_shr) (enc_bits_size Henc_msbs)
                 size_sarB size_repeat size_extract subnn addn1 muln1
                 (enc_bits_size Hlsbs) .
    }
    move => Hszshrlsmsbs .
    move : (bit_blast_ite_correct Hszshrlsmsbs Hite Henc_eq
                                  Henc_shr Henc_msbs Hcnf_ite)
    => {g_shr g_ite l_eq Hszshrlsmsbs Hite Henc_eq
              Henc_shr Henc_msbs Hcnf_ite cs_ite} .
    rewrite muln1 ashrB_log2 .
    + by rewrite Heqlog2szls
                 !(enc_bits_size Hlnsns) !(enc_bits_size Hlsbs) /= .
    + rewrite -(enc_bits_size Hlsbs) . by apply Nats.lt_ltn .
    + by rewrite -(enc_bits_size Hlnsns) -Hszeq (enc_bits_size Hlsbs) .
  - move => Hbitblast .
    by apply (bit_blast_ashr_rec_correct Hbitblast Hlsbs Hlnsns Hcnf) .
Qed.

Lemma mk_env_ashr_int1_is_bit_blast_ashr_int1 E g ls E' g' cs lrs :
    mk_env_ashr_int1 E g ls = (E', g', cs, lrs) ->
    bit_blast_ashr_int1 g ls = (g', cs, lrs) .
Proof .
  rewrite /mk_env_ashr_int1 /bit_blast_ashr_int1 .
  by case => _ <- <- <- .
Qed .

Lemma mk_env_ashr_int_is_bit_blast_ashr_int E g ls i E' g' cs lrs :
    mk_env_ashr_int E g ls i = (E', g', cs, lrs) ->
    bit_blast_ashr_int g ls i = (g', cs, lrs).
Proof.
  move: E' g' cs lrs. eapply mk_env_ashr_int_ind.
  - clear i. move=> i Hi E' g' cs lrs [] ? ? ? ?; subst => /=.
    symmetry. apply: R_bit_blast_ashr_int_complete.
    apply: (R_bit_blast_ashr_int_0 _ _ 0). reflexivity.
  - clear i. move=> i [] p Hn //=. move=> _ IH E_m g_m cs_m ls_m Henv.
    move=> E1 g1 cs1 ls1 Henv1. move=> E' g' cs lrs [] ? ? ? ?; subst => /=.
    move: (mk_env_ashr_int1_is_bit_blast_ashr_int1 Henv1) => Hbb1.
    move: (IH _ _ _ _ Henv) => Hbb. exact: (bit_blast_ashr_int_Npos Hbb Hbb1).
Qed.

Lemma size_mk_env_ashr_int1 E g ls E' g' cs lrs :
  mk_env_ashr_int1 E g ls = (E', g', cs, lrs) ->
  size ls = size lrs .
Proof .
  rewrite /mk_env_ashr_int1 .
  case => _ _ _ <- .
  rewrite size_droplsl size_joinmsl .
  rewrite subn1 addn1.
  reflexivity .
Qed .

Lemma size_mk_env_ashr_int E g n ls E' g' cs lrs :
  mk_env_ashr_int E g ls n = (E', g', cs, lrs) ->
  size ls = size lrs.
Proof.
  move: E' g' cs lrs. eapply mk_env_ashr_int_ind.
  - clear n. move=> n Hn E' g' cs lrs [] ? ? ? ?; subst => /=. reflexivity.
  - clear n. move=> n [] p Hn //=. move=> _ IH E_m g_m cs_m ls_m Hbb.
    move=> E1 g1 cs1 ls1 Hbb1. move=> E' g' cs lrs [] ? ? ? ?; subst => /=.
    rewrite (IH _ _ _ _ Hbb). exact: (size_mk_env_ashr_int1 Hbb1).
Qed.



Fixpoint mk_env_ashr_rec E g ls ns (i : N) : env * generator * cnf * word :=
  match ns with
  | [::] => (E, g, [::], ls)
  | ns_hd::ns_tl =>
    let '(E_tl, g_tl, cs_tl, ls_tl) := mk_env_ashr_rec E g ls ns_tl (i * 2) in
    if ns_hd == lit_tt then
      let '(E_hd, g_hd, cs_hd, ls_hd) := mk_env_ashr_int E_tl g_tl ls_tl i in
      (E_hd, g_hd, catrev cs_tl cs_hd, ls_hd)
    else if ns_hd == lit_ff then
           (E_tl, g_tl, cs_tl, ls_tl)
         else
           let '(E_hd, g_hd, cs_hd, ls_hd) := mk_env_ashr_int E_tl g_tl ls_tl i in
           let '(E_ite, g_ite, cs_ite, ls_ite) := mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl in
           (E_ite, g_ite, catrev cs_tl (catrev cs_hd cs_ite), ls_ite)
  end .

Definition mk_env_ashr E g ls ns : env * generator * cnf * word :=
  if size ls > 1 then
    let 'log2szls := Z.to_nat (Z.log2_up (Z.of_nat (size ls))) in
    let '(E_zero_hi, g_zero_hi, cs_zero_hi, zero_hi) :=
        mk_env_const E g (from_nat (size ns - log2szls) 0) in
    let '(E_msb, g_msb, cs_msb, ls_msb) :=
        mk_env_extract E_zero_hi g_zero_hi (size ls).-1 (size ls).-1 ls in
    let '(E_msbs, g_msbs, cs_msbs, ls_msbs) :=
        mk_env_repeat E_msb g_msb (size ls) ls_msb in
    let '(E_hi, g_hi, cs_hi, ns_hi) :=
        mk_env_extract E_msbs g_msbs (size ns).-1 log2szls ns in
    let '(E_lo, g_lo, cs_lo, ns_lo) :=
        mk_env_extract E_hi g_hi log2szls.-1 0 ns in
    let '(E_eq, g_eq, cs_eq, l_eq) := mk_env_eq E_lo g_lo ns_hi zero_hi in
    let '(E_shr, g_shr, cs_shr, ls_shr) :=
        mk_env_ashr_rec E_eq g_eq ls ns_lo 1%num in
    let '(E_ite, g_ite, cs_ite, ls_ite) :=
        mk_env_ite E_shr g_shr l_eq ls_shr ls_msbs in
    (E_ite, g_ite,
     catrev cs_zero_hi
            (catrev cs_msb
                    (catrev cs_msbs
                            (catrev cs_hi
                                    (catrev cs_lo
                                            (catrev cs_eq
                                                    (catrev cs_shr cs_ite)))))),
     ls_ite)
  else
  mk_env_ashr_rec E g ls ns 1%num .

Lemma mk_env_ashr_rec_is_bit_blast_ashr_rec E g ls ns i E' g' cs lrs :
    mk_env_ashr_rec E g ls ns i = (E', g', cs, lrs) ->
    bit_blast_ashr_rec g ls ns i = (g', cs, lrs) .
Proof .
  elim : ns i E' g' cs lrs => [|ns_hd ns_tl IH] i E' g' cs lrs .
  - rewrite /mk_env_ashr_rec /= -/mk_env_ashr_rec .
    by case => _ <- <- <- .
  - rewrite /mk_env_ashr_rec /= -/mk_env_ashr_rec .
    dcase (mk_env_ashr_rec E g ls ns_tl (i*2)) => [[[[E_tl g_tl] cs_tl] ls_tl] Hrec] .
    rewrite (IH _ _ _ _ _ Hrec) .
    dcase (mk_env_ashr_int E_tl g_tl ls_tl i) => [[[[E_hd g_hd] cs_hd] ls_hd] Hint] .
    rewrite (mk_env_ashr_int_is_bit_blast_ashr_int Hint) .
    dcase (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl) => [[[[E_ite g_ite] cs_ite] ls_ite] Hite] .
    rewrite (mk_env_ite_is_bit_blast_ite Hite) /= .
    case Hnshdtt : (ns_hd == lit_tt) .
    + by case => _ <- <- <- .
    + case Hnshdff : (ns_hd == lit_ff); by case => _ <- <- <- .
Qed .

Lemma mk_env_ashr_is_bit_blast_ashr E g ls ns E' g' cs lrs :
    mk_env_ashr E g ls ns = (E', g', cs, lrs) ->
    bit_blast_ashr g ls ns = (g', cs, lrs) .
Proof .
  rewrite /mk_env_ashr /bit_blast_ashr .
  remember (Z.to_nat (Z.log2_up (Z.of_nat (size ls)))) as log2szls .
  dcase (1 < size ls); case => /ltP Hcon .
  - dcase (mk_env_const E g (from_nat (size ns - log2szls) 0)) =>
    [[[[E_zero_hi] g_zero_hi] cs_zero_hi] zero_hi] Hzero_hi .
    rewrite (mk_env_const_is_bit_blast_const Hzero_hi) {Hzero_hi} .
    dcase (mk_env_extract E_zero_hi g_zero_hi (size ls).-1 (size ls).-1 ls) =>
    [[[[E_msb] g_msb cs_msb] ls_msb]] Hmsb .
    rewrite (mk_env_extract_is_bit_blast_extract Hmsb)
            {Hmsb} .
    dcase (mk_env_repeat E_msb g_msb (size ls) ls_msb) =>
    [[[[E_msbs] g_msbs cs_msbs] ls_msbs]] Hmsbs .
    rewrite (mk_env_repeat_is_bit_blast_repeat Hmsbs)
            {Hmsbs E_msb g_msb} .
    dcase (mk_env_extract E_msbs g_msbs (size ns).-1 log2szls ns) =>
    [[[[E_hi] g_hi cs_hi] ns_hi]] Hhi .
    rewrite (mk_env_extract_is_bit_blast_extract Hhi)
            {E_msbs g_msbs Hhi} .
    dcase (mk_env_extract E_hi g_hi log2szls.-1 0 ns) =>
    [[[[E_lo] g_lo cs_lo] ns_lo]] Hlo .
    rewrite (mk_env_extract_is_bit_blast_extract Hlo)
            {E_hi g_hi Hlo} .
    dcase (mk_env_eq E_lo g_lo ns_hi zero_hi) =>
    [[[[E_eq] g_eq cs_eq] l_eq]] Heq .
    rewrite (mk_env_eq_is_bit_blast_eq Heq)
            {E_lo g_lo Heq} .
    dcase (mk_env_ashr_rec E_eq g_eq ls ns_lo 1) =>
    [[[[E_shr] g_shr cs_shr] ls_shr]] Hshr .
    rewrite (mk_env_ashr_rec_is_bit_blast_ashr_rec Hshr)
            {E_eq g_eq Hshr} .
    dcase (mk_env_ite E_shr g_shr l_eq ls_shr ls_msbs) =>
    [[[[E_ite] g_ite cs_ite] ls_ite]] Hite .
    rewrite (mk_env_ite_is_bit_blast_ite Hite)
            {E_shr g_shr Hite} .
    by case => _ <- <- <- .
  - apply mk_env_ashr_rec_is_bit_blast_ashr_rec .
Qed .

Lemma mk_env_ashr_int_newer_gen E g ls n E' g' cs lrs :
    mk_env_ashr_int E g ls n = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move: E' g' cs lrs. eapply mk_env_ashr_int_ind.
  - clear n. move=> n Hn E' g' cs lrs [] ? ? ? ?; subst => /=.
    exact: Pos.leb_refl.
  - clear n. move=> n [] p Hn //=. move=> _ IH E_m g_m cs_m ls_m Henv.
    move=> E1 g1 cs1 ls1 Henv1. move=> E' g' cs lrs [] ? ? ? ?; subst => /=.
    move : (IH _ _ _ _ Henv) => {IH Henv} Hind.
    rewrite /mk_env_ashr_int1 in Henv1. case: Henv1 => ? ? ? ?; subst.
    assumption.
Qed.

Lemma mk_env_ashr_rec_newer_gen E g ls ns i E' g' cs lrs :
    mk_env_ashr_rec E g ls ns i = (E', g', cs, lrs) ->
    (g <=? g')%positive .
Proof .
  elim : ns E' g' cs lrs i => [|ns_hd ns_tl IH] E' g' cs lrs i .
  - rewrite /mk_env_ashr_rec /=; by t_auto_newer .
  - rewrite /mk_env_ashr_rec /= -/mk_env_ashr_rec .
    dcase (mk_env_ashr_rec E g ls ns_tl (i*2)) => [[[[E_tl g_tl] cs_tl] ls_tl] Hrec] .
    move : (IH _ _ _ _ _ Hrec) => Hggtl .
    dcase (mk_env_ashr_int E_tl g_tl ls_tl i) => [[[[E_hd g_hd] cs_hd] ls_hd] Hint] .
    move : (mk_env_ashr_int_newer_gen Hint) => Hgtlghd .
    dcase (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl) => [[[[E_ite g_ite] cs_ite] ls_ite] Hite] .
    move : (mk_env_ite_newer_gen Hite) => Hghdgite .
    move : (pos_leb_trans Hggtl Hgtlghd) => Hgghd .
    move : (pos_leb_trans Hgghd Hghdgite) => Hggite .
    case : (ns_hd == lit_tt) .
    + by case => _ <- _ _ .
    + case : (ns_hd == lit_ff); by case => _ <- _ _ .
Qed .

Lemma mk_env_ashr_newer_gen E g ls ns E' g' cs lrs :
  mk_env_ashr E g ls ns = (E', g', cs, lrs) ->
  (g <=? g')%positive .
Proof .
  rewrite /mk_env_ashr .
  remember (Z.to_nat (Z.log2_up (Z.of_nat (size ls)))) as log2szls .
  dcase (1 < size ls); case => /ltP Hcon .
  - dcase (mk_env_const E g (from_nat (size ns - log2szls) 0)) =>
    [[[[E_zero_hi] g_zero_hi] cs_zero_hi] zero_hi] Hzero_hi .
    move : (mk_env_const_newer_gen Hzero_hi)
    => {Hzero_hi} Hg_gzerohi .
    dcase (mk_env_extract E_zero_hi g_zero_hi (size ls).-1 (size ls).-1 ls) =>
    [[[[E_msb] g_msb cs_msb] ls_msb]] Hmsb .
    move : (mk_env_extract_newer_gen Hmsb)
    => {Hmsb} Hgzerohi_gmsb .
    dcase (mk_env_repeat E_msb g_msb (size ls) ls_msb) =>
    [[[[E_msbs] g_msbs cs_msbs] ls_msbs]] Hmsbs .
    move : (mk_env_repeat_newer_gen Hmsbs)
    => {Hmsbs E_msb} Hgmsb_gmsbs .
    dcase (mk_env_extract E_msbs g_msbs (size ns).-1 log2szls ns) =>
    [[[[E_hi] g_hi cs_hi] ns_hi]] Hhi .
    move : (mk_env_extract_newer_gen Hhi)
    => {E_msbs Hhi} Hgmsbs_ghi .
    dcase (mk_env_extract E_hi g_hi log2szls.-1 0 ns) =>
    [[[[E_lo] g_lo cs_lo] ns_lo]] Hlo .
    move : (mk_env_extract_newer_gen Hlo)
    => {E_hi Hlo} Hghi_glo .
    dcase (mk_env_eq E_lo g_lo ns_hi zero_hi) =>
    [[[[E_eq] g_eq cs_eq] l_eq]] Heq .
    move : (mk_env_eq_newer_gen Heq)
    => {E_lo Heq} Hglo_geq .
    dcase (mk_env_ashr_rec E_eq g_eq ls ns_lo 1) =>
    [[[[E_shr] g_shr cs_shr] ls_shr]] Hshr .
    move : (mk_env_ashr_rec_newer_gen Hshr)
    => {E_eq Hshr} Hgeq_gshr .
    dcase (mk_env_ite E_shr g_shr l_eq ls_shr ls_msbs) =>
    [[[[E_ite] g_ite cs_ite] ls_ite]] Hite .
    move : (mk_env_ite_newer_gen Hite)
    => {E_shr Hite} Hgshr_gite .
    case => _ <- _ _ { cs_zero_hi cs_msb cs_msbs cs_lo cs_hi cs_shr ns_hi ns_lo } .
    move : (pos_leb_trans Hg_gzerohi Hgzerohi_gmsb)
    => {Hg_gzerohi Hgzerohi_gmsb g_zero_hi} => Hg_gmsb .
    move : (pos_leb_trans Hgmsb_gmsbs Hgmsbs_ghi)
    => {Hgmsb_gmsbs Hgmsbs_ghi} => Hgmsb_ghi .
    move : (pos_leb_trans Hgmsb_ghi Hghi_glo)
    => {Hgmsb_ghi Hghi_glo g_hi} => Hgmsb_glo .
    move : (pos_leb_trans Hglo_geq Hgeq_gshr)
    => {Hglo_geq Hgeq_gshr g_eq} => Hglo_gshr .
    move : (pos_leb_trans Hglo_gshr Hgshr_gite)
    => {Hglo_gshr Hgshr_gite g_shr} => Hglo_gite .
    move : (pos_leb_trans Hgmsb_glo Hglo_gite)
    => {Hgmsb_glo Hglo_gite g_lo} => Hgmsb_gite .
    by apply (pos_leb_trans Hg_gmsb Hgmsb_gite) .
  - exact : mk_env_ashr_rec_newer_gen .
Qed .

Lemma mk_env_ashr_int_newer_res E g n E' g' ls cs lrs :
  newer_than_lit g lit_tt ->
  newer_than_lits g ls ->
  mk_env_ashr_int E g ls n = (E', g', cs, lrs) ->
  newer_than_lits g' lrs.
Proof.
  move => Htt Hls .
  move: E' g' cs lrs. eapply mk_env_ashr_int_ind.
  - clear n. move=> n Hn E' g' cs lrs [] ? ? ? ?; subst => /=.
    assumption.
  - clear n. move=> n [] p Hn //=. move=> _ IH E_m g_m cs_m ls_m Henv.
    move=> E1 g1 cs1 ls1 [] ? ? ? ?; subst. move=> E' g' cs lrs [] ? ? ? ?; subst.
    move: (IH _ _ _ _ Henv) => Hlsm.
    move : (mk_env_ashr_int_newer_gen Henv) => {Henv} Hggm.
    move : (newer_than_lit_le_newer Htt Hggm) => Hgmtt.
    move : (newer_than_lits_msl Hgmtt Hlsm) => Hgmmsl .
    move: (newer_than_lits_joinmsl Hlsm Hgmmsl) => Hgmjoinmsl.
    exact: (newer_than_lits_droplsl Hgmjoinmsl).
Qed.

Lemma mk_env_ashr_rec_newer_res E g i E' g' ls ns cs lrs :
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g ns ->
  mk_env_ashr_rec E g ls ns i = (E', g', cs, lrs) ->
  newer_than_lits g' lrs .
Proof .
  move => Hgtt Hgls .
  elim : ns E' g' cs lrs i => [|ns_hd ns_tl IH] E' g' cs lrs i Hgns .
  - rewrite /mk_env_ashr_rec /=; by t_auto_newer .
  - rewrite /mk_env_ashr_rec /= -/mk_env_ashr_rec .
    move : Hgns; rewrite newer_than_lits_cons => /andP [Hgnshd Hgnstl] .
    dcase (mk_env_ashr_rec E g ls ns_tl (i*2)) => [[[[E_tl g_tl] cs_tl] ls_tl] Hrec] .
    move : (IH _ _ _ _ _ Hgnstl Hrec) => Hgtllstl .
    move : (mk_env_ashr_rec_newer_gen Hrec) => Hggtl .
    dcase (mk_env_ashr_int E_tl g_tl ls_tl i) => [[[[E_hd g_hd] cs_hd] ls_hd] Hint] .
    move : (mk_env_ashr_int_newer_res (newer_than_lit_le_newer Hgtt Hggtl) Hgtllstl Hint) => Hghdlshd .
    dcase (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl) => [[[[E_ite g_ite] cs_ite] ls_ite] Hite] .
    move : (mk_env_ite_newer_res Hite) => Hgitelsite .
    case : (ns_hd == lit_tt) .
    + by case => _ <- _ <- .
    + case : (ns_hd == lit_ff); by case => _ <- _ <- .
Qed .

Lemma mk_env_ashr_newer_res E g ls ns E' g' cs lrs :
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g ns ->
  mk_env_ashr E g ls ns = (E', g', cs, lrs) ->
  newer_than_lits g' lrs .
Proof .
  move => Hgtt Hgls Hgns .
  rewrite /mk_env_ashr .
  remember (Z.to_nat (Z.log2_up (Z.of_nat (size ls)))) as log2szls .
  dcase (1 < size ls); case => /ltP Hcon .
  - dcase (mk_env_const E g (from_nat (size ns - log2szls) 0)) =>
    [[[[E_zero_hi] g_zero_hi] cs_zero_hi] zero_hi] Hzero_hi .
    move : (mk_env_const_newer_res Hzero_hi Hgtt) => Hgzerohi .
    move : (newer_than_lit_le_newer Hgtt (mk_env_const_newer_gen Hzero_hi))
           (newer_than_lits_le_newer Hgls (mk_env_const_newer_gen Hzero_hi))
           (newer_than_lits_le_newer Hgns (mk_env_const_newer_gen Hzero_hi))
    => {Hzero_hi} Hgzerohitt Hgzerohils Hgzerohins .
    dcase (mk_env_extract E_zero_hi g_zero_hi (size ls).-1 (size ls).-1 ls) =>
    [[[[E_msb] g_msb cs_msb] ls_msb]] Hmsb .
    move : (mk_env_extract_newer_res Hmsb Hgzerohitt Hgzerohils) => Hgmsb .
    move : (newer_than_lit_le_newer Hgzerohitt (mk_env_extract_newer_gen Hmsb))
           (newer_than_lits_le_newer Hgzerohils (mk_env_extract_newer_gen Hmsb))
           (newer_than_lits_le_newer Hgzerohins (mk_env_extract_newer_gen Hmsb))
    => {E_zero_hi Hgzerohitt Hgzerohils Hgzerohins Hmsb}
         Hgmsbtt Hgmsbls Hgmsbns .
    dcase (mk_env_repeat E_msb g_msb (size ls) ls_msb) =>
    [[[[E_msbs] g_msbs cs_msbs] ls_msbs]] Hmsbs .
    move : (mk_env_repeat_newer_res Hmsbs Hgmsb) => Hgmsbs .
    move : (newer_than_lit_le_newer Hgmsbtt (mk_env_repeat_newer_gen Hmsbs))
           (newer_than_lits_le_newer Hgmsbls (mk_env_repeat_newer_gen Hmsbs))
           (newer_than_lits_le_newer Hgmsbns (mk_env_repeat_newer_gen Hmsbs))
    => {E_msb Hgmsbtt Hgmsbls Hgmsbns Hmsbs}
         Hgmsbstt Hgmsbsls Hgmsbsns .
    dcase (mk_env_extract E_msbs g_msbs (size ns).-1 log2szls ns) =>
    [[[[E_hi] g_hi cs_hi] ns_hi]] Hhi .
    move : (mk_env_extract_newer_res Hhi Hgmsbstt Hgmsbsns) => Hghi .
    move : (newer_than_lit_le_newer Hgmsbstt (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgmsbsls (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgmsbsns (mk_env_extract_newer_gen Hhi))
    => {E_msbs Hgmsbstt Hgmsbsls Hgmsbsns Hhi} Hghitt Hghils Hghins .
    dcase (mk_env_extract E_hi g_hi log2szls.-1 0 ns) =>
    [[[[E_lo] g_lo cs_lo] ns_lo]] Hlo .
    move : (mk_env_extract_newer_res Hlo Hghitt Hghins) => Hglo .
    move : (newer_than_lit_le_newer Hghitt (mk_env_extract_newer_gen Hlo))
           (newer_than_lits_le_newer Hghils (mk_env_extract_newer_gen Hlo))
           (newer_than_lits_le_newer Hghins (mk_env_extract_newer_gen Hlo))
    => {E_hi Hghitt Hghils Hghins Hlo} Hglott Hglols Hglons .
    dcase (mk_env_eq E_lo g_lo ns_hi zero_hi) =>
    [[[[E_eq] g_eq cs_eq] l_eq]] Heq .
    move : (mk_env_eq_newer_res Heq) => Hgeq .
    move : (newer_than_lit_le_newer Hglott (mk_env_eq_newer_gen Heq))
           (newer_than_lits_le_newer Hglols (mk_env_eq_newer_gen Heq))
           (newer_than_lits_le_newer Hglons (mk_env_eq_newer_gen Heq))
           (newer_than_lits_le_newer Hglo (mk_env_eq_newer_gen Heq))
    => {E_lo Hglott Hglols Hglons Heq} Hgeqtt Hgeqls Hgeqns Hgeqnslo .
    dcase (mk_env_ashr_rec E_eq g_eq ls ns_lo 1) =>
    [[[[E_shr] g_shr cs_shr] ls_shr]] Hshr .
    move : (mk_env_ashr_rec_newer_res Hgeqtt Hgeqls Hgeqnslo Hshr) => Hgshr .
    move : (newer_than_lit_le_newer Hgeqtt (mk_env_ashr_rec_newer_gen Hshr))
           (newer_than_lits_le_newer Hgeqls (mk_env_ashr_rec_newer_gen Hshr))
           (newer_than_lits_le_newer Hgeqns (mk_env_ashr_rec_newer_gen Hshr))
    => {E_eq Hgeqtt Hgeqls Hgeqns Hshr} Hgshrtt Hgshrls Hgshrns .
    dcase (mk_env_ite E_shr g_shr l_eq ls_shr ls_msbs) =>
    [[[[E_ite] g_ite cs_ite] ls_ite]] Hite .
    move : (mk_env_ite_newer_res Hite)
    => {E_shr Hgshrtt Hgshrls Hgshrns Hite} Hgshr_gite .
    by case => _ <- _ <- { cs_zero_hi cs_msb cs_msbs cs_lo cs_hi cs_shr } .
  - by apply mk_env_ashr_rec_newer_res .
Qed .

Lemma mk_env_ashr_int_newer_cnf E g ls n E' g' cs lr :
    mk_env_ashr_int E g ls n = (E', g', cs, lr) ->
    newer_than_lits g ls ->
    newer_than_cnf g' cs.
Proof.
  move: E' g' cs lr. eapply mk_env_ashr_int_ind.
  - clear n. move=> n Hn E' g' cs lrs [] ? ? ? ?; subst => /=. done.
  - clear n. move=> n [] p Hn //=. move=> _ IH E_m g_m cs_m ls_m Henv.
    move=> E1 g1 cs1 ls1 [] ? ? ? ?; subst. move=> E' g' cs lrs [] ? ? ? ?; subst.
    move=> Hgls. move : (IH _ _ _ _ Henv Hgls) => Hgmcsm.
    by rewrite newer_than_cnf_catrev Hgmcsm /=.
Qed.

Lemma mk_env_ashr_rec_newer_cnf E g ls ns i E' g' cs lr :
  mk_env_ashr_rec E g ls ns i = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g ns ->
  newer_than_cnf g' cs .
Proof .
  elim : ns E' g' cs lr i => [|ns_hd ns_tl IH] E' g' cs lr i .
  - rewrite /mk_env_ashr_rec /=; by case => _ <- <- _ .
  - rewrite /mk_env_ashr_rec /= -/mk_env_ashr_rec .
    dcase (mk_env_ashr_rec E g ls ns_tl (i*2)) => [[[[E_tl g_tl] cs_tl] ls_tl] Hrec] .
    dcase (mk_env_ashr_int E_tl g_tl ls_tl i) => [[[[E_hd g_hd] cs_hd] ls_hd] Hint] .
    dcase (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl) => [[[[E_ite g_ite] cs_ite] ls_ite] Hite] .
    move => Htemp Hgtt Hgls /andP [Hgnshd Hgnstl] .
    move : Htemp .
    move : (IH _ _ _ _ _ Hrec Hgtt Hgls Hgnstl) => Hgtlcstl .
    move : (mk_env_ashr_rec_newer_res Hgtt Hgls Hgnstl Hrec) => Hgtllstl .
    move : (mk_env_ashr_int_newer_cnf Hint Hgtllstl) => Hghdcshd .
    move : (mk_env_ashr_int_newer_gen Hint) => Hgtlghd .
     case : (ns_hd == lit_tt) .
    + case => _ <- <- _ .
      by rewrite newer_than_cnf_catrev Hghdcshd (newer_than_cnf_le_newer Hgtlcstl Hgtlghd) .
    + case : (ns_hd == lit_ff) .
      * by case => _ <- <- _ .
      * case => _ <- <- _ .
        rewrite !newer_than_cnf_catrev .
        move : (mk_env_ite_newer_gen Hite) => Hghdgite .
        move : (mk_env_ashr_rec_newer_gen Hrec) => Hggtl .
        move : (newer_than_lit_le_newer Hgnshd (pos_leb_trans Hggtl Hgtlghd)) => Hghdnshd .
        move : (mk_env_ashr_int_newer_res (newer_than_lit_le_newer Hgtt Hggtl) Hgtllstl Hint) => Hghdlshd .
        (*
        move : (size_mk_env_ashr_int Hint) => -/eqP Hlstllshd .
        rewrite eq_sym in Hlstllshd .
         *)
        move : (mk_env_ite_newer_cnf Hite (newer_than_lit_le_newer Hgtt (pos_leb_trans Hggtl Hgtlghd)) Hghdnshd Hghdlshd (newer_than_lits_le_newer Hgtllstl Hgtlghd)) => Hgitecsite .
        by rewrite (newer_than_cnf_le_newer Hgtlcstl (pos_leb_trans Hgtlghd Hghdgite)) (newer_than_cnf_le_newer Hghdcshd Hghdgite) Hgitecsite .
Qed .

Lemma mk_env_ashr_newer_cnf E g ls ns E' g' cs lrs :
  mk_env_ashr E g ls ns = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g ns ->
  newer_than_cnf g' cs .
Proof .
  move => Henv Hgtt Hgls Hgns .
  move : Henv; rewrite /mk_env_ashr .
  remember (Z.to_nat (Z.log2_up (Z.of_nat (size ls)))) as log2szls .
  dcase (1 < size ls); case => /ltP _ .
  - dcase (mk_env_const E g (from_nat (size ns - log2szls) 0)) =>
    [[[[E_zero_hi] g_zero_hi] cs_zero_hi] zero_hi] Hzero_hi .
    move : (mk_env_const_newer_cnf Hzero_hi Hgtt)
           (mk_env_const_newer_res Hzero_hi Hgtt)
    => Hgzerohi Hgzerohizerohi .
    move : (newer_than_lit_le_newer Hgtt (mk_env_const_newer_gen Hzero_hi))
           (newer_than_lits_le_newer Hgls (mk_env_const_newer_gen Hzero_hi))
           (newer_than_lits_le_newer Hgns (mk_env_const_newer_gen Hzero_hi))
    => {Hzero_hi} Hgzerohitt Hgzerohils Hgzerohins .
    dcase (mk_env_extract E_zero_hi g_zero_hi (size ls).-1 (size ls).-1 ls) =>
    [[[[E_msb] g_msb cs_msb] ls_msb]] Hmsb .
    move : (mk_env_extract_newer_cnf Hmsb Hgzerohitt Hgzerohils)
           (mk_env_extract_newer_res Hmsb Hgzerohitt Hgzerohils)
    => Hgmsb Hgmsblsmsb .
    move : (newer_than_lit_le_newer Hgzerohitt (mk_env_extract_newer_gen Hmsb))
           (newer_than_lits_le_newer Hgzerohils (mk_env_extract_newer_gen Hmsb))
           (newer_than_lits_le_newer Hgzerohins (mk_env_extract_newer_gen Hmsb))
           (newer_than_lits_le_newer Hgzerohizerohi (mk_env_extract_newer_gen Hmsb))
           (newer_than_cnf_le_newer Hgzerohi (mk_env_extract_newer_gen Hmsb))
    => {Hgzerohi Hgzerohizerohi E_zero_hi Hgzerohitt Hgzerohils Hgzerohins Hmsb}
         Hgmsbtt Hgmsbls Hgmsbns Hgmsbzerohi Hgzerohi .
    dcase (mk_env_repeat E_msb g_msb (size ls) ls_msb) =>
    [[[[E_msbs] g_msbs cs_msbs] ls_msbs]] Hmsbs .
    move : (mk_env_repeat_newer_cnf Hmsbs)
           (mk_env_repeat_newer_res Hmsbs Hgmsblsmsb)
    => Hgmsbs Hgmsbslsmsbs .
    move : (newer_than_lit_le_newer Hgmsbtt (mk_env_repeat_newer_gen Hmsbs))
           (newer_than_lits_le_newer Hgmsbls (mk_env_repeat_newer_gen Hmsbs))
           (newer_than_lits_le_newer Hgmsbns (mk_env_repeat_newer_gen Hmsbs))
           (newer_than_lits_le_newer Hgmsbzerohi (mk_env_repeat_newer_gen Hmsbs))
           (newer_than_cnf_le_newer Hgzerohi (mk_env_repeat_newer_gen Hmsbs))
           (newer_than_cnf_le_newer Hgmsb (mk_env_repeat_newer_gen Hmsbs))
    => {Hgmsb Hgmsblsmsb E_msb Hgmsbtt Hgmsbls Hgmsbns Hmsbs Hgmsbzerohi Hgzerohi}
         Hgmsbstt Hgmsbsls Hgmsbsns Hgmsbszerohi Hgzerohi Hgmsb.
    dcase (mk_env_extract E_msbs g_msbs (size ns).-1 log2szls ns) =>
    [[[[E_hi] g_hi cs_hi] ns_hi]] Hhi .
    move : (mk_env_extract_newer_cnf Hhi Hgmsbstt Hgmsbsns)
           (mk_env_extract_newer_res Hhi Hgmsbstt Hgmsbsns)
    => Hghi Hghinshi .
    move : (newer_than_lit_le_newer Hgmsbstt (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgmsbsls (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgmsbsns (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgmsbszerohi (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgmsbslsmsbs (mk_env_extract_newer_gen Hhi))
           (newer_than_cnf_le_newer Hgzerohi (mk_env_extract_newer_gen Hhi))
           (newer_than_cnf_le_newer Hgmsb (mk_env_extract_newer_gen Hhi))
           (newer_than_cnf_le_newer Hgmsbs (mk_env_extract_newer_gen Hhi))
    => {E_msbs Hgmsbstt Hgmsbsls Hgmsbsns Hgmsbslsmsbs Hhi Hgmsbs Hgmsbszerohi Hgzerohi Hgmsb}
         Hghitt Hghils Hghins Hghizerohi Hghilsmsbs Hgzerohi Hgmsb Hgmsbs .
    dcase (mk_env_extract E_hi g_hi log2szls.-1 0 ns) =>
    [[[[E_lo] g_lo cs_lo] ns_lo]] Hlo .
    move : (mk_env_extract_newer_cnf Hlo Hghitt Hghins)
           (mk_env_extract_newer_res Hlo Hghitt Hghins)
    => Hglo Hglonslo .
    move : (newer_than_lit_le_newer Hghitt (mk_env_extract_newer_gen Hlo))
           (newer_than_lits_le_newer Hghils (mk_env_extract_newer_gen Hlo))
           (newer_than_lits_le_newer Hghins (mk_env_extract_newer_gen Hlo))
           (newer_than_lits_le_newer Hghizerohi (mk_env_extract_newer_gen Hlo))
           (newer_than_lits_le_newer Hghilsmsbs (mk_env_extract_newer_gen Hlo))
           (newer_than_lits_le_newer Hghinshi (mk_env_extract_newer_gen Hlo))
           (newer_than_cnf_le_newer Hgzerohi (mk_env_extract_newer_gen Hlo))
           (newer_than_cnf_le_newer Hgmsb (mk_env_extract_newer_gen Hlo))
           (newer_than_cnf_le_newer Hgmsbs (mk_env_extract_newer_gen Hlo))
           (newer_than_cnf_le_newer Hghi (mk_env_extract_newer_gen Hlo))
    => {Hghi Hghinshi E_hi Hghitt Hghils Hghins Hgzerohi Hghizerohi Hghilsmsbs
             Hgmsb Hgmsbs Hlo}
         Hglott Hglols Hglons Hglozerohi Hglolsmsbs Hglonshi Hgzerohi
         Hgmsb Hgmsbs Hghi.
    dcase (mk_env_eq E_lo g_lo ns_hi zero_hi) =>
    [[[[E_eq] g_eq cs_eq] l_eq]] Heq .
    move : (mk_env_eq_newer_cnf Heq Hglott Hglonshi Hglozerohi)
           (mk_env_eq_newer_res Heq)
    => {Hglonshi} Hgeq Hgeqleq .
    move : (newer_than_lit_le_newer Hglott (mk_env_eq_newer_gen Heq))
           (newer_than_lits_le_newer Hglols (mk_env_eq_newer_gen Heq))
           (newer_than_lits_le_newer Hglons (mk_env_eq_newer_gen Heq))
           (newer_than_lits_le_newer Hglolsmsbs (mk_env_eq_newer_gen Heq))
           (newer_than_lits_le_newer Hglonslo (mk_env_eq_newer_gen Heq))
           (newer_than_cnf_le_newer Hgzerohi (mk_env_eq_newer_gen Heq))
           (newer_than_cnf_le_newer Hgmsb (mk_env_eq_newer_gen Heq))
           (newer_than_cnf_le_newer Hgmsbs (mk_env_eq_newer_gen Heq))
           (newer_than_cnf_le_newer Hghi (mk_env_eq_newer_gen Heq))
           (newer_than_cnf_le_newer Hglo (mk_env_eq_newer_gen Heq))
    => {Hglo Hghi Hgzerohi E_lo Hglott Hglols Hglons Heq Hglonslo
        Hglozerohi Hglolsmsbs Hgmsb Hgmsbs}
         Hgeqtt Hgeqls Hgeqns Hgeqlsmsbs Hgeqnslo Hgzerohi Hgmsb Hgmsbs
         Hghi Hglo .
    dcase (mk_env_ashr_rec E_eq g_eq ls ns_lo 1) =>
    [[[[E_shr] g_shr cs_shr] ls_shr]] Hshr .
    move : (mk_env_ashr_rec_newer_cnf Hshr Hgeqtt Hgeqls Hgeqnslo)
           (mk_env_ashr_rec_newer_res Hgeqtt Hgeqls Hgeqnslo Hshr)
    => Hgshr Hgshrlsshr .
    move : (newer_than_lit_le_newer Hgeqtt (mk_env_ashr_rec_newer_gen Hshr))
           (newer_than_lits_le_newer Hgeqls (mk_env_ashr_rec_newer_gen Hshr))
           (newer_than_lits_le_newer Hgeqns (mk_env_ashr_rec_newer_gen Hshr))
           (newer_than_lits_le_newer Hgeqlsmsbs (mk_env_ashr_rec_newer_gen Hshr))
           (newer_than_lit_le_newer Hgeqleq (mk_env_ashr_rec_newer_gen Hshr))
           (newer_than_cnf_le_newer Hgzerohi (mk_env_ashr_rec_newer_gen Hshr))
           (newer_than_cnf_le_newer Hgmsb (mk_env_ashr_rec_newer_gen Hshr))
           (newer_than_cnf_le_newer Hgmsbs (mk_env_ashr_rec_newer_gen Hshr))
           (newer_than_cnf_le_newer Hghi (mk_env_ashr_rec_newer_gen Hshr))
           (newer_than_cnf_le_newer Hglo (mk_env_ashr_rec_newer_gen Hshr))
           (newer_than_cnf_le_newer Hgeq (mk_env_ashr_rec_newer_gen Hshr))
    => {Hgeq Hglo Hghi Hgmsbs Hgzerohi Hgmsb
             Hgeqtt Hgeqls Hgeqns Hgeqlsmsbs Hshr Hgeqnslo Hgeqleq}
         Hgshrtt Hgshrls Hgshrns Hgshrlsmsbs Hgshrleq Hgzerohi
         Hgmsb Hgmsbs Hghi Hglo Hgeq .
    dcase (mk_env_ite E_shr g_shr l_eq ls_shr ls_msbs) =>
    [[[[E_ite] g_ite cs_ite] ls_ite]] Hite .
   move : (mk_env_ite_newer_res Hite)
   => Hgshr_gite .
   move : (mk_env_ite_newer_cnf Hite Hgshrtt Hgshrleq Hgshrlsshr Hgshrlsmsbs)
          (newer_than_cnf_le_newer Hgzerohi (mk_env_ite_newer_gen Hite))
          (newer_than_cnf_le_newer Hgmsb (mk_env_ite_newer_gen Hite))
          (newer_than_cnf_le_newer Hgmsbs (mk_env_ite_newer_gen Hite))
          (newer_than_cnf_le_newer Hghi (mk_env_ite_newer_gen Hite))
          (newer_than_cnf_le_newer Hglo (mk_env_ite_newer_gen Hite))
          (newer_than_cnf_le_newer Hgeq (mk_env_ite_newer_gen Hite))
          (newer_than_cnf_le_newer Hgshr (mk_env_ite_newer_gen Hite))
   => {Hgshr Hgeq Hglo Hghi Hgzerohi Hgmsb Hgmsbs
       Hite Hgshrlsshr Hgshrtt Hgshrls Hgshrns Hgshrlsmsbs Hgshrleq}
       Hgite Hgzerohi Hgmsb Hgmsbs Hghi Hglo Hgeq Hgshr .
   case => _ <- <- _ .
   by rewrite !newer_than_cnf_catrev Hgzerohi Hgmsb Hgmsbs
              Hghi Hglo Hgeq Hgite Hgshr .
  - move => Henv .
    by apply (mk_env_ashr_rec_newer_cnf Henv Hgtt Hgls Hgns) .
Qed .

Lemma mk_env_ashr_int_preserve E g ls n E' g' cs lrs :
    mk_env_ashr_int E g ls n = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move: E' g' cs lrs. eapply mk_env_ashr_int_ind.
  - clear n. move=> n Hn E' g' cs lrs [] ? ? ? ?; subst => /=. done.
  - clear n. move=> n [] p Hn //=. move=> _ IH E_m g_m cs_m ls_m Henv.
    move=> E1 g1 cs1 ls1 [] ? ? ? ?; subst. move=> E' g' cs lrs [] ? ? ? ?; subst.
    exact: (IH _ _ _ _ Henv).
Qed.

Lemma mk_env_ashr_rec_preserve E g ls ns i E' g' cs lrs :
  mk_env_ashr_rec E g ls ns i = (E', g', cs, lrs) ->
  env_preserve E E' g .
Proof .
  elim : ns E' g' cs lrs i => [| ns_hd ns_tl IH] E' g' cs lrs i .
  - rewrite /mk_env_ashr_rec /=; by case => <- _ _ _ .
  - rewrite /mk_env_ashr_rec /= -/mk_env_ashr_rec .
    dcase (mk_env_ashr_rec E g ls ns_tl (i*2)) => [[[[E_tl g_tl] cs_tl] ls_tl] Hrec] .
    dcase (mk_env_ashr_int E_tl g_tl ls_tl i) => [[[[E_hd g_hd] cs_hd] ls_hd] Hint] .
    dcase (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl) => [[[[E_ite g_ite] cs_ite] ls_ite] Hite] .
    move : (IH _ _ _ _ _ Hrec) => HEEtl .
    move : (mk_env_ashr_int_preserve Hint) => HEtlEhd .
    move : (mk_env_ite_preserve Hite) => HEhdEite .
    move : (mk_env_ashr_rec_newer_gen Hrec) => Hggtl .
    move : (mk_env_ashr_int_newer_gen Hint) => Hgtlghd .
    move : (mk_env_ite_newer_gen Hite) => Hghdgite .
    move : (env_preserve_le HEtlEhd Hggtl) => HEtlEhdg .
    move : (env_preserve_le HEhdEite (pos_leb_trans Hggtl Hgtlghd)) => HEhdEiteg .
    case : (ns_hd == lit_tt) .
    + case => <- _ _ _; by t_auto_preserve .
    + case : (ns_hd == lit_ff); case => <- _ _ _; by t_auto_preserve .
Qed .

Lemma mk_env_ashr_preserve E g ls ns E' g' cs lrs :
  mk_env_ashr E g ls ns = (E', g', cs, lrs) ->
  env_preserve E E' g .
Proof .
  rewrite /mk_env_ashr .
  remember (Z.to_nat (Z.log2_up (Z.of_nat (size ls)))) as log2szls .
  dcase (1 < size ls); case => /ltP _ .
  - dcase (mk_env_const E g (from_nat (size ns - log2szls) 0)) =>
    [[[[E_zero_hi] g_zero_hi] cs_zero_hi] zero_hi] Hzero_hi .
    move : (mk_env_const_newer_gen Hzero_hi)
           (mk_env_const_preserve Hzero_hi)
    => {Hzero_hi} Hggzerohi HEEzerohi .
    dcase (mk_env_extract E_zero_hi g_zero_hi (size ls).-1 (size ls).-1 ls) =>
    [[[[E_msb] g_msb cs_msb] lsmsb]] Hmsb .
    move : (mk_env_extract_newer_gen Hmsb)
           (mk_env_extract_preserve Hmsb)
    => {Hmsb} Hgzerohigmsb HEzerohiEmsb .
    move : (env_preserve_le HEzerohiEmsb Hggzerohi)
    => {HEzerohiEmsb} HEzerohiEmsb .
    dcase (mk_env_repeat E_msb g_msb (size ls) lsmsb) =>
    [[[[E_msbs] g_msbs cs_msbs] lsmsbs]] Hmsbs .
    move : (mk_env_repeat_newer_gen Hmsbs)
           (mk_env_repeat_preserve Hmsbs)
    => {Hmsbs} Hgmsbgmsbs HEmsbEmsbs .
    move : (env_preserve_le
              (env_preserve_le HEmsbEmsbs Hgzerohigmsb) Hggzerohi) 
    => {HEmsbEmsbs} HEmsbEmsbs .
    dcase (mk_env_extract E_msbs g_msbs (size ns).-1 log2szls ns) =>
    [[[[E_hi] g_hi cs_hi] ns_hi]] Hhi .
    move : (mk_env_extract_newer_gen Hhi)
           (mk_env_extract_preserve Hhi)
    => {Hhi} Hgmsbsghi HEmsbsEhi .
    move : (env_preserve_le
              (env_preserve_le
                 (env_preserve_le HEmsbsEhi Hgmsbgmsbs) Hgzerohigmsb)
                 Hggzerohi)
    => {HEmsbsEhi} HEmsbsEhi .
    dcase (mk_env_extract E_hi g_hi log2szls.-1 0 ns) =>
    [[[[E_lo] g_lo cs_lo] ns_lo]] Hlo .
    move : (mk_env_extract_newer_gen Hlo)
           (mk_env_extract_preserve Hlo)
    => {Hlo} Hghiglo HEhiElo .
    move : (env_preserve_le
              (env_preserve_le
                 (env_preserve_le
                    (env_preserve_le HEhiElo Hgmsbsghi) Hgmsbgmsbs)
                 Hgzerohigmsb)
              Hggzerohi)
    => {HEhiElo} HEhiElo .
    dcase (mk_env_eq E_lo g_lo ns_hi zero_hi) =>
    [[[[E_eq] g_eq cs_eq] l_eq]] Heq .
    move : (mk_env_eq_newer_gen Heq)
           (mk_env_eq_preserve Heq)
    => {Heq} Hglogeq HEloEeq .
    move : (env_preserve_le
              (env_preserve_le
                 (env_preserve_le
                    (env_preserve_le
                       (env_preserve_le HEloEeq Hghiglo) Hgmsbsghi)
                    Hgmsbgmsbs)
                 Hgzerohigmsb)
              Hggzerohi)
    => {HEloEeq} HEloEeq .
    dcase (mk_env_ashr_rec E_eq g_eq ls ns_lo 1) =>
    [[[[E_shr] g_shr cs_shr] ls_shr]] Hshr .
    move : (mk_env_ashr_rec_newer_gen Hshr)
           (mk_env_ashr_rec_preserve Hshr)
    => {Hshr} Hgeqgshr HEeqEshr .
    move : (env_preserve_le
              (env_preserve_le
                 (env_preserve_le
                    (env_preserve_le
                       (env_preserve_le
                          (env_preserve_le HEeqEshr Hglogeq)
                          Hghiglo)
                       Hgmsbsghi)
                    Hgmsbgmsbs)
                 Hgzerohigmsb)
              Hggzerohi)
    => {HEeqEshr} HEeqEshr .
    dcase (mk_env_ite E_shr g_shr l_eq ls_shr lsmsbs) =>
    [[[[E_ite] g_ite cs_ite] ls_ite]] Hite .
    move : (mk_env_ite_newer_gen Hite)
           (mk_env_ite_preserve Hite)
    => {Hite} Hgshrgite HEshrEite .
    move : (env_preserve_le
              (env_preserve_le
                 (env_preserve_le
                    (env_preserve_le
                       (env_preserve_le
                          (env_preserve_le
                             (env_preserve_le HEshrEite Hgeqgshr)
                             Hglogeq)
                          Hghiglo)
                       Hgmsbsghi)
                    Hgmsbgmsbs)
                 Hgzerohigmsb)
              Hggzerohi)
    => {Hggzerohi Hgzerohigmsb Hgmsbgmsbs Hgmsbsghi Hghiglo Hglogeq Hgeqgshr
                  Hgshrgite HEshrEite}
         HEshrEite .
    case => <- _ _ _ { g_zero_hi cs_zero_hi g_msb cs_msb g_msbs cs_msbs
                       g_lo cs_lo ns_lo g_hi cs_hi ns_hi
                       g_eq cs_eq g_shr cs_shr
                       g_ite cs_ite } .
    apply env_preserve_trans with E_shr; trivial => {HEshrEite} .
    apply env_preserve_trans with E_eq; trivial => {HEeqEshr} .
    apply env_preserve_trans with E_lo; trivial => {HEloEeq} .
    apply env_preserve_trans with E_hi; trivial => {HEhiElo} .
    apply env_preserve_trans with E_msbs; trivial => {HEmsbsEhi} .
    apply env_preserve_trans with E_msb; trivial => {HEmsbEmsbs} .
    by apply env_preserve_trans with E_zero_hi; trivial => {HEzerohiElo} .
  - exact : mk_env_ashr_rec_preserve .
Qed .

Lemma mk_env_ashr_int_sat E g ls n E' g' cs lrs :
  mk_env_ashr_int E g ls n = (E', g', cs, lrs) ->
  newer_than_lits g ls ->
  interp_cnf E' cs.
Proof.
  move: E' g' cs lrs. eapply mk_env_ashr_int_ind.
  - clear n. move=> n Hn E' g' cs lrs [] ? ? ? ?; subst => /=. done.
  - clear n. move=> n [] p Hn //=. move=> _ IH E_m g_m cs_m ls_m Henv.
    move=> E1 g1 cs1 ls1 [] ? ? ? ?; subst. move=> E' g' cs lrs [] ? ? ? ?; subst.
    move=> Hgls. rewrite interp_cnf_catrev.
    by rewrite (IH _ _ _ _ Henv Hgls) /=.
Qed.

Lemma mk_env_ashr_rec_sat E g ls ns i E' g' cs lrs :
    mk_env_ashr_rec E g ls ns i = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls -> newer_than_lits g ns ->
    interp_cnf E' cs .
Proof .
  elim : ns E' g' cs lrs i => [|ns_hd ns_tl IH] E' g' cs lrs i .
  - rewrite /mk_env_ashr_rec /= .
    by case => <- _ <- _ .
  - rewrite /mk_env_ashr_rec /= -/mk_env_ashr_rec .
    dcase (mk_env_ashr_rec E g ls ns_tl (i*2)) => [[[[E_tl g_tl] cs_tl] ls_tl] Hrec] .
    dcase (mk_env_ashr_int E_tl g_tl ls_tl i) => [[[[E_hd g_hd] cs_hd] ls_hd] Hint] .
    dcase (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl) => [[[[E_ite g_ite] cs_ite] ls_ite] Hite] .
    move => Htmp Hgtt Hgls /andP [Hgnshd Hgnstl] .
    move : Htmp .
    move : (mk_env_ashr_rec_newer_gen Hrec) => Hggtl .
    move : (mk_env_ashr_int_newer_gen Hint) => Hgtlghd .
    move : (IH _ _ _ _ _ Hrec Hgtt Hgls Hgnstl) => HEtlcstl .
    move : (mk_env_ashr_rec_newer_res Hgtt Hgls Hgnstl Hrec) => Hgtllstl .
    move : (mk_env_ashr_int_newer_res (newer_than_lit_le_newer Hgtt Hggtl) Hgtllstl Hint) => Hghdlshd .
    move : (mk_env_ashr_int_sat Hint Hgtllstl) => HEhdcshd .
    move : (mk_env_ashr_int_preserve Hint) => HEtlEhd .
    move : (mk_env_ite_preserve Hite) => HEhdEite .
    move : (mk_env_ashr_rec_newer_cnf Hrec Hgtt Hgls Hgnstl) => Hgtlcstl .
    move : (mk_env_ashr_int_newer_cnf Hint Hgtllstl) => Hghdcshd .
    case : (ns_hd == lit_tt) .
    + case => <- _ <- _ .
      rewrite interp_cnf_catrev (env_preserve_cnf HEtlEhd Hgtlcstl) .
        by t_auto_newer .
    + case : (ns_hd == lit_ff) .
      * by case => <- _ <- _ .
      * case => <- _ <- _ .
        rewrite !interp_cnf_catrev .
        move : (mk_env_ite_sat Hite (newer_than_lit_le_newer Hgtt (pos_leb_trans Hggtl Hgtlghd)) (newer_than_lit_le_newer Hgnshd (pos_leb_trans Hggtl Hgtlghd)) Hghdlshd (newer_than_lits_le_newer Hgtllstl Hgtlghd)) => HEitecsite .
        rewrite (env_preserve_cnf HEhdEite Hghdcshd) .
        rewrite (env_preserve_cnf HEhdEite (newer_than_cnf_le_newer Hgtlcstl Hgtlghd)) .
        rewrite (env_preserve_cnf HEtlEhd Hgtlcstl) .
        by t_auto_newer .
Qed .

Lemma mk_env_ashr_sat E g ls ns E' g' cs lrs :
  mk_env_ashr E g ls ns = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g ns ->
  interp_cnf E' cs.
Proof .
  move => Henv Hgtt Hgls Hgns .
  move : Henv; rewrite /mk_env_ashr .
  remember (Z.to_nat (Z.log2_up (Z.of_nat (size ls)))) as log2szls .
  dcase (1 < size ls); case => /ltP Hcon .
  - dcase (mk_env_const E g (from_nat (size ns - log2szls) 0)) =>
    [[[[E_zero_hi] g_zero_hi] cs_zero_hi] zero_hi] Hzero_hi .
    move : (mk_env_const_sat Hzero_hi)
           (mk_env_const_newer_res Hzero_hi Hgtt)
           (mk_env_const_newer_cnf Hzero_hi Hgtt)
    => Hzerohisat Hgzerohizerohi Hgzerohicszerohi .
    move : (newer_than_lit_le_newer Hgtt (mk_env_const_newer_gen Hzero_hi))
           (newer_than_lits_le_newer Hgls (mk_env_const_newer_gen Hzero_hi))
           (newer_than_lits_le_newer Hgns (mk_env_const_newer_gen Hzero_hi))
    => {Hzero_hi} Hgzerohitt Hgzerohils Hgzerohins .
    dcase (mk_env_extract E_zero_hi g_zero_hi (size ls).-1 (size ls).-1 ls) =>
    [[[[E_msb] g_msb cs_msb] ls_msb]] Hmsb .
    move : (mk_env_extract_sat Hmsb Hgzerohitt Hgzerohils)
           (mk_env_extract_newer_res Hmsb Hgzerohitt Hgzerohils)
           (mk_env_extract_newer_cnf Hmsb Hgzerohitt Hgzerohils)
           (mk_env_extract_preserve Hmsb)
           (mk_env_extract_newer_gen Hmsb)
    => Hmsbsat Hgmsblsmsb Hgmsbcsmsb HEzerohiEmsb Hgzerohigmsb .
    move : (newer_than_lit_le_newer Hgzerohitt (mk_env_extract_newer_gen Hmsb))
           (newer_than_lits_le_newer Hgzerohils (mk_env_extract_newer_gen Hmsb))
           (newer_than_lits_le_newer Hgzerohins (mk_env_extract_newer_gen Hmsb))
           (newer_than_lits_le_newer Hgzerohizerohi (mk_env_extract_newer_gen Hmsb))
    => {Hgzerohitt Hgzerohils Hgzerohins Hmsb Hgzerohizerohi}
         Hgmsbtt Hgmsbls Hgmsbns Hgmsbzerohi .
    dcase (mk_env_repeat E_msb g_msb (size ls) ls_msb) =>
    [[[[E_msbs] g_msbs cs_msbs] ls_msbs]] Hmsbs .
    move : (mk_env_repeat_sat Hmsbs)
           (mk_env_repeat_newer_res Hmsbs Hgmsblsmsb)
           (mk_env_repeat_newer_cnf Hmsbs)
           (mk_env_repeat_preserve Hmsbs)
           (mk_env_repeat_newer_gen Hmsbs)
    => Hmsbssat Hgmsbslsmsbs Hgmsbscsmsbs HEmsbsEmsb Hgmsbgmsbs .
    move : (newer_than_lit_le_newer Hgmsbtt (mk_env_repeat_newer_gen Hmsbs))
           (newer_than_lits_le_newer Hgmsbls (mk_env_repeat_newer_gen Hmsbs))
           (newer_than_lits_le_newer Hgmsbns (mk_env_repeat_newer_gen Hmsbs))
           (newer_than_lits_le_newer Hgmsbzerohi (mk_env_repeat_newer_gen Hmsbs))
           (newer_than_lits_le_newer Hgmsblsmsb (mk_env_repeat_newer_gen Hmsbs))
    => {Hgmsbtt Hgmsbls Hgmsbns Hmsbs Hgmsbzerohi Hgmsblsmsb}
         Hgmsbstt Hgmsbsls Hgmsbsns Hgmsbszerohi Hgmsbslsmsb .
    dcase (mk_env_extract E_msbs g_msbs (size ns).-1 log2szls ns) =>
    [[[[E_hi] g_hi cs_hi] ns_hi]] Hhi .
    move : (mk_env_extract_sat Hhi Hgmsbstt Hgmsbsns)
           (mk_env_extract_newer_res Hhi Hgmsbstt Hgmsbsns)
           (mk_env_extract_newer_cnf Hhi Hgmsbstt Hgmsbsns)
           (mk_env_extract_preserve Hhi)
           (mk_env_extract_newer_gen Hhi)
    => Hhisat Hghinshi Hghicshi HEmsbsEhi Hgmsbsghi .
    move : (newer_than_lit_le_newer Hgmsbstt (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgmsbsls (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgmsbsns (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgmsbszerohi (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgmsbslsmsb (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgmsbslsmsbs (mk_env_extract_newer_gen Hhi))
    => {Hgmsbstt Hgmsbsls Hgmsbsns Hgmsbszerohi Hgmsbslsmsb Hgmsbslsmsbs Hhi}
         Hghitt Hghils Hghins Hghizerohi Hghilsmsb Hghilsmsbs .
    dcase (mk_env_extract E_hi g_hi log2szls.-1 0 ns) =>
    [[[[E_lo] g_lo cs_lo] ns_lo]] Hlo .
    move : (mk_env_extract_sat Hlo Hghitt Hghins)
           (mk_env_extract_newer_res Hlo Hghitt Hghins)
           (mk_env_extract_newer_cnf Hlo Hghitt Hghins)
           (mk_env_extract_preserve Hlo)
           (mk_env_extract_newer_gen Hlo)
    => Hlosat Hglonslo Hglocslo HEhiElo Hghiglo .
    move : (newer_than_lit_le_newer Hghitt (mk_env_extract_newer_gen Hlo))
           (newer_than_lits_le_newer Hghils (mk_env_extract_newer_gen Hlo))
           (newer_than_lits_le_newer Hghins (mk_env_extract_newer_gen Hlo))
           (newer_than_lits_le_newer Hghinshi (mk_env_extract_newer_gen Hlo))
           (newer_than_lits_le_newer Hghizerohi (mk_env_extract_newer_gen Hlo))
           (newer_than_lits_le_newer Hghilsmsb (mk_env_extract_newer_gen Hlo))
           (newer_than_lits_le_newer Hghilsmsbs (mk_env_extract_newer_gen Hlo))
    => {Hghitt Hghils Hghins Hghinshi Hlo Hghizerohi Hghilsmsb Hghilsmsbs}
         Hglott Hglols Hglons Hglonshi Hglozerohi Hglolsmsb Hglolsmsbs .
    dcase (mk_env_eq E_lo g_lo ns_hi zero_hi) =>
    [[[[E_eq] g_eq cs_eq] l_eq]] Heq .
    move : (mk_env_eq_sat Heq Hglott Hglonshi Hglozerohi)
           (mk_env_eq_newer_res Heq)
           (mk_env_eq_newer_cnf Heq Hglott Hglonshi Hglozerohi)
           (mk_env_eq_preserve Heq)
           (mk_env_eq_newer_gen Heq)
    => {Hglonshi Hglozerohi} Heqsat Hgeqleq Hgeqcseq HEloEeq Hglogeq .
    move : (newer_than_lit_le_newer Hglott (mk_env_eq_newer_gen Heq))
           (newer_than_lits_le_newer Hglols (mk_env_eq_newer_gen Heq))
           (newer_than_lits_le_newer Hglons (mk_env_eq_newer_gen Heq))
           (newer_than_lits_le_newer Hglonslo (mk_env_eq_newer_gen Heq))
           (newer_than_lits_le_newer Hglolsmsbs (mk_env_eq_newer_gen Heq))
    => {Hglott Hglols Hglons Hglonslo Heq Hglolsmsbs}
         Hgeqtt Hgeqls Hgeqns Hgeqnslo Hgeqlsmsbs .
    dcase (mk_env_ashr_rec E_eq g_eq ls ns_lo 1) =>
    [[[[E_shr] g_shr cs_shr] ls_shr]] Hshr .
    move : (mk_env_ashr_rec_sat Hshr Hgeqtt Hgeqls Hgeqnslo)
           (mk_env_ashr_rec_newer_res Hgeqtt Hgeqls Hgeqnslo Hshr)
           (mk_env_ashr_rec_newer_cnf Hshr Hgeqtt Hgeqls Hgeqnslo)
           (mk_env_ashr_rec_preserve Hshr)
           (mk_env_ashr_rec_newer_gen Hshr) 
    => {Hgeqnslo} Hshrsat Hgshrlsshr Hgshrcsshr HEeqEshr Hgeqgshr .
    move : (newer_than_lit_le_newer Hgeqtt (mk_env_ashr_rec_newer_gen Hshr))
           (newer_than_lit_le_newer Hgeqleq (mk_env_ashr_rec_newer_gen Hshr))
           (newer_than_lits_le_newer Hgeqls (mk_env_ashr_rec_newer_gen Hshr))
           (newer_than_lits_le_newer Hgeqns (mk_env_ashr_rec_newer_gen Hshr))
           (newer_than_lits_le_newer Hgeqlsmsbs (mk_env_ashr_rec_newer_gen Hshr))
    => {Hgeqtt Hgeqleq Hgeqls Hgeqns Hshr Hgeqlsmsbs}
         Hgshrtt Hgshrleq Hgshrls Hgshrns Hgshrlsmsbs .
    dcase (mk_env_ite E_shr g_shr l_eq ls_shr ls_msbs) =>
    [[[[E_ite] g_ite cs_ite] ls_ite]] Hite .
    move : (mk_env_ite_sat Hite Hgshrtt Hgshrleq Hgshrlsshr Hgshrlsmsbs)
           (mk_env_ite_preserve Hite)
    => {Hite Hgshrls Hgshrns Hgshrtt Hgshrleq Hgshrlsshr Hgshrlsmsbs}
         Hitesat HEshrEite .
    case => <- _ <- _ {ls_shr ls_ite l_eq Hgtt Hgls Hgns} .
    rewrite !interp_cnf_catrev .
    rewrite Hitesat {Hitesat cs_ite g_ite} .
    rewrite (env_preserve_cnf HEshrEite Hgshrcsshr) Hshrsat {Hshrsat} .
    move : (env_preserve_trans HEeqEshr
                               (env_preserve_le HEshrEite Hgeqgshr))
    => {HEeqEshr HEshrEite Hgeqgshr Hgshrcsshr cs_shr g_shr} HEeqEite .
    rewrite (env_preserve_cnf HEeqEite Hgeqcseq) Heqsat
            {Heqsat Hgeqcseq cs_eq} .
    move : (env_preserve_trans HEloEeq (env_preserve_le HEeqEite Hglogeq))
    => {HEloEeq HEeqEite Hglogeq E_eq E_shr g_eq} HEloEite .
    rewrite (env_preserve_cnf HEloEite Hglocslo) Hlosat
            {Hlosat Hglocslo cs_lo ns_lo} .
    move : (env_preserve_trans HEhiElo (env_preserve_le HEloEite Hghiglo))
    => {HEhiElo HEloEite Hghiglo E_lo} HEhiEite .
    rewrite (env_preserve_cnf HEhiEite Hghicshi) Hhisat
            {Hhisat Hghicshi cs_hi ns_hi} .
    move : (env_preserve_trans HEmsbsEhi (env_preserve_le HEhiEite Hgmsbsghi))
    => {HEmsbsEhi HEhiEite Hgmsbsghi E_hi g_hi} HEmsbsEite .
    rewrite (env_preserve_cnf HEmsbsEite Hgmsbscsmsbs) Hmsbssat
            {Hmsbssat Hgmsbscsmsbs cs_msbs} .
    move : (env_preserve_trans HEmsbsEmsb (env_preserve_le HEmsbsEite Hgmsbgmsbs))
    => {HEmsbsEmsb HEmsbsEite Hgmsbgmsbs E_msbs g_msbs} HEmsbEite .
    rewrite (env_preserve_cnf HEmsbEite Hgmsbcsmsb) Hmsbsat
            {Hmsbsat Hgmsbcsmsb cs_msb} .
    move : (env_preserve_trans HEzerohiEmsb
                               (env_preserve_le HEmsbEite Hgzerohigmsb))
    => {HEzerohiEmsb HEmsbEite Hgzerohigmsb E_msb g_msb} HEzerohiEite .
    by rewrite (env_preserve_cnf HEzerohiEite Hgzerohicszerohi) Hzerohisat .
  - move => Henv .
    exact : (mk_env_ashr_rec_sat Henv Hgtt Hgls Hgns) .
Qed .

Lemma mk_env_ashr_int1_env_equal E1 E2 g ls E1' E2' g1 g2 cs1 cs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_ashr_int1 E1 g ls = (E1', g1, cs1, lrs1) ->
  mk_env_ashr_int1 E2 g ls = (E2', g2, cs2, lrs2) ->
  env_equal E1' E2' /\ g1 = g2 /\ cs1 = cs2 /\ lrs1 = lrs2.
Proof.
  rewrite /mk_env_ashr_int1 => Heq. case=> ? ? ? ?; case=> ? ? ? ?; subst. done.
Qed.

Lemma mk_env_ashr_int_env_equal E1 E2 g n ls E1' E2' g1 g2 cs1 cs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_ashr_int E1 g ls n = (E1', g1, cs1, lrs1) ->
  mk_env_ashr_int E2 g ls n = (E2', g2, cs2, lrs2) ->
  env_equal E1' E2' /\ g1 = g2 /\ cs1 = cs2 /\ lrs1 = lrs2.
Proof.
  move: n E1 E2 g ls E1' E2' g1 g2 cs1 cs2 lrs1 lrs2.
  apply: N.peano_ind => [| n IH] E1 E2 g ls E1' E2' g1 g2 cs1 cs2 lrs1 lrs2 Heq.
  - rewrite !mk_env_ashr_int_N0. case=> ? ? ? ?; case=> ? ? ? ?; subst. done.
  - rewrite !mk_env_ashr_int_Nsucc.
    dcase (mk_env_ashr_int E1 g ls n) => [[[[E_m1 g_m1] cs_m1] lrs_m1] Hv_m1].
    dcase (mk_env_ashr_int E2 g ls n) => [[[[E_m2 g_m2] cs_m2] lrs_m2] Hv_m2].
    move: (IH _ _ _ _ _ _ _ _ _ _ _ _ Heq Hv_m1 Hv_m2) => [Heq1 [? [? ?]]]; subst.
    dcase (mk_env_ashr_int1 E_m1 g_m2 lrs_m2) => [[[[E'1 g'1] cs'1] lrs'1] Hv'1].
    dcase (mk_env_ashr_int1 E_m2 g_m2 lrs_m2) => [[[[E'2 g'2] cs'2] lrs'2] Hv'2].
    case=> ? ? ? ?; case=> ? ? ? ?; subst.
    move: (mk_env_ashr_int1_env_equal Heq1 Hv'1 Hv'2) => [Heq2 [? [? ?]]]; subst.
    done.
Qed.

Lemma mk_env_ashr_rec_env_equal E1 E2 g n ls ns E1' E2' g1 g2 cs1 cs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_ashr_rec E1 g ls ns n = (E1', g1, cs1, lrs1) ->
  mk_env_ashr_rec E2 g ls ns n = (E2', g2, cs2, lrs2) ->
  env_equal E1' E2' /\ g1 = g2 /\ cs1 = cs2 /\ lrs1 = lrs2.
Proof.
  elim: ns E1 E2 g n ls E1' E2' g1 g2 cs1 cs2 lrs1 lrs2 =>
  [| nhd ns IH] //= E1 E2 g n ls E1' E2' g1 g2 cs1 cs2 lrs1 lrs2 Heq.
  - case=> ? ? ? ?; case=> ? ? ? ?; subst. done.
  - dcase (mk_env_ashr_rec E1 g ls ns (n * 2)) => [[[[E_tl1 g_tl1] cs_tl1] lrs_tl1] Hv_tl1].
    dcase (mk_env_ashr_rec E2 g ls ns (n * 2)) => [[[[E_tl2 g_tl2] cs_tl2] lrs_tl2] Hv_tl2].
    move: (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Heq Hv_tl1 Hv_tl2) => [Heq1 [? [? ?]]]; subst.
    case: (nhd == lit_tt).
    + dcase (mk_env_ashr_int E_tl1 g_tl2 lrs_tl2 n) => [[[[E_hd1 g_hd1] cs_hd1] lrs_hd1] Hv_hd1].
      dcase (mk_env_ashr_int E_tl2 g_tl2 lrs_tl2 n) => [[[[E_hd2 g_hd2] cs_hd2] lrs_hd2] Hv_hd2].
      case=> ? ? ? ?; case=> ? ? ? ?; subst.
      move: (mk_env_ashr_int_env_equal Heq1 Hv_hd1 Hv_hd2) => [Heq2 [? [? ?]]]; subst.
      done.
    + case: (nhd == lit_ff).
      * case=> ? ? ? ?; case=> ? ? ? ?; subst. done.
      * dcase (mk_env_ashr_int E_tl1 g_tl2 lrs_tl2 n) => [[[[E_hd1 g_hd1] cs_hd1] lrs_hd1] Hv_hd1].
        dcase (mk_env_ashr_int E_tl2 g_tl2 lrs_tl2 n) => [[[[E_hd2 g_hd2] cs_hd2] lrs_hd2] Hv_hd2].
        move: (mk_env_ashr_int_env_equal Heq1 Hv_hd1 Hv_hd2) => [Heq2 [? [? ?]]]; subst.
        dcase (mk_env_ite E_hd1 g_hd2 nhd lrs_hd2 lrs_tl2) =>
        [[[[E_ite1 g_ite1] cs_ite1] lrs_ite1] Hv_ite1].
        dcase (mk_env_ite E_hd2 g_hd2 nhd lrs_hd2 lrs_tl2) =>
        [[[[E_ite2 g_ite2] cs_ite2] lrs_ite2] Hv_ite2].
        case=> ? ? ? ?; case=> ? ? ? ?; subst.
        move: (mk_env_ite_env_equal Heq2 Hv_ite1 Hv_ite2) => [Heq3 [? [? ?]]]; subst.
        done.
Qed.

Lemma mk_env_ashr_env_equal E1 E2 g ls ns E1' E2' g1 g2 cs1 cs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_ashr E1 g ls ns = (E1', g1, cs1, lrs1) ->
  mk_env_ashr E2 g ls ns = (E2', g2, cs2, lrs2) ->
  env_equal E1' E2' /\ g1 = g2 /\ cs1 = cs2 /\ lrs1 = lrs2.
Proof.
  rewrite /mk_env_ashr => Heq.
  case: (1 < size ls).
  - dcase (mk_env_const
             E1 g (size ns - Z.to_nat (Z.log2_up (Z.of_nat (size ls)))) -bits of (0)%bits)
    => [[[[E_zh1 g_zh1] cs_zh1] lrs_zh1] Hzh1]. case: Hzh1=> ? ? ? ?; subst.
    dcase (mk_env_const
             E2 g_zh1 (size ns - Z.to_nat (Z.log2_up (Z.of_nat (size ls)))) -bits of (0)%bits)
    => [[[[E_zh2 g_zh2] cs_zh2] lrs_zh2] Hzh2]. case: Hzh2=> ? ? ? ?; subst.
    dcase (mk_env_extract E_zh1 g_zh2 (size ls).-1 (size ls).-1 ls)
    => [[[[E_msb1 g_msb1] cs_msb1] lrs_msb1] Hmsb1].
    dcase (mk_env_extract E_zh2 g_zh2 (size ls).-1 (size ls).-1 ls)
    => [[[[E_msb2 g_msb2] cs_msb2] lrs_msb2] Hmsb2].
    move: (mk_env_extract_env_equal Heq Hmsb1 Hmsb2)
    => {Heq Hmsb1 Hmsb2} [Heq [? [? ?]]]; subst.
    dcase (mk_env_repeat E_msb1 g_msb2 (size ls) lrs_msb2)
    => [[[[E_msbs1 g_msbs1] cs_msbs1] lrs_msbs1] Hmsbs1].
    dcase (mk_env_repeat E_msb2 g_msb2 (size ls) lrs_msb2)
    => [[[[E_msbs2 g_msbs2] cs_msbs2] lrs_msbs2] Hmsbs2].
    move: (mk_env_repeat_env_equal Heq Hmsbs1 Hmsbs2)
    => {Heq Hmsbs1 Hmsbs2} [Heq [? [? ?]]]; subst.
    dcase (mk_env_extract
             E_msbs1 g_msbs2 (size ns).-1 (Z.to_nat (Z.log2_up (Z.of_nat (size ls)))) ns)
    => [[[[E_hi1 g_hi1] cs_hi1] lrs_hi1] Hhi1].
    dcase (mk_env_extract
             E_msbs2 g_msbs2 (size ns).-1 (Z.to_nat (Z.log2_up (Z.of_nat (size ls)))) ns)
    => [[[[E_hi2 g_hi2] cs_hi2] lrs_hi2] Hhi2].
    move: (mk_env_extract_env_equal Heq Hhi1 Hhi2)
    => {Heq Hhi1 Hhi2} [Heq [? [? ?]]]; subst.
    dcase (mk_env_extract E_hi1 g_hi2 (Z.to_nat (Z.log2_up (Z.of_nat (size ls)))).-1 0 ns)
    => [[[[E_lo1 g_lo1] cs_lo1] lrs_lo1] Hlo1].
    dcase (mk_env_extract E_hi2 g_hi2 (Z.to_nat (Z.log2_up (Z.of_nat (size ls)))).-1 0 ns)
    => [[[[E_lo2 g_lo2] cs_lo2] lrs_lo2] Hlo2].
    move: (mk_env_extract_env_equal Heq Hlo1 Hlo2)
    => {Heq Hlo1 Hlo2} [Heq [? [? ?]]]; subst.
    set ls1 := [seq lit_of_bool i
               | i <- (size ns - Z.to_nat (Z.log2_up (Z.of_nat (size ls)))) -bits of (0)%bits].
    dcase (mk_env_eq E_lo1 g_lo2 lrs_hi2 ls1) => [[[[E_eq1 g_eq1] cs_eq1] lrs_eq1] Hv_eq1].
    dcase (mk_env_eq E_lo2 g_lo2 lrs_hi2 ls1) => [[[[E_eq2 g_eq2] cs_eq2] lrs_eq2] Hv_eq2].
    move: (mk_env_eq_env_equal Heq Hv_eq1 Hv_eq2)
    => {Heq Hv_eq1 Hv_eq2} [Heq [? [? ?]]]; subst.
    dcase (mk_env_ashr_rec E_eq1 g_eq2 ls lrs_lo2 1) =>
    [[[[E_ashr1 g_ashr1] cs_ashr1] lrs_ashr1] Hashr1].
    dcase (mk_env_ashr_rec E_eq2 g_eq2 ls lrs_lo2 1) =>
    [[[[E_ashr2 g_ashr2] cs_ashr2] lrs_ashr2] Hashr2].
    move: (mk_env_ashr_rec_env_equal Heq Hashr1 Hashr2)
    => {Heq Hashr1 Hashr2} [Heq [? [? ?]]]; subst.
    dcase (mk_env_ite E_ashr1 g_ashr2 lrs_eq2 lrs_ashr2 lrs_msbs2)
    => [[[[E_ite1 g_ite1] cs_ite1] lrs_ite1] Hite1].
    dcase (mk_env_ite E_ashr2 g_ashr2 lrs_eq2 lrs_ashr2 lrs_msbs2)
    => [[[[E_ite2 g_ite2] cs_ite2] lrs_ite2] Hite2].
    move: (mk_env_ite_env_equal Heq Hite1 Hite2)
    => {Heq Hite1 Hite2} [Heq [? [? ?]]]; subst.
    case=> ? ? ? ?; case=> ? ? ? ?; subst. done.
  - exact: (mk_env_ashr_rec_env_equal Heq).
Qed.
