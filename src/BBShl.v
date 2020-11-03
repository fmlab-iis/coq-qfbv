
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBIte BBConst BBExtract BBEq .
From ssrlib Require Import ZAriths Seqs Tactics.
From nbits Require Import NBits.
From Coq Require Import Recdef.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* shl lemmas *)
(* Lemma shlB_add bs i j : *)
(*   shlB i (shlB j bs) = shlB (i + j) bs . *)
(* Proof . *)
(*   by rewrite /shlB iter_add . *)
(* Qed . *)

(* Lemma shlB1_size bs : *)
(*   size (shlB1 bs) = size bs . *)
(* Proof . *)
(*   rewrite /shlB1 size_dropmsb size_joinlsb . *)
(*   rewrite subn1 addn1 . *)
(*   reflexivity . *)
(* Qed . *)

(* Lemma shlB_size n bs : *)
(*   size (shlB n bs) = size bs . *)
(* Proof . *)
(*   rewrite /shlB /iter . *)
(*   elim: n; first done . *)
(*   move => n IH . *)
(*   by rewrite shlB1_size . *)
(* Qed . *)

(* ===== bit_blast_shl ===== *)

Definition bit_blast_shl_int1 g ls : generator * cnf * word :=
  (g, [::], dropmsl (joinlsl lit_ff ls)) .

Function bit_blast_shl_int g ls (n : N) {wf N.lt n} : generator * cnf * word :=
  match n with
  | N0 => ((g, [::]), ls)
  | _ =>
    let '(g_m, cs_m, ls_m) := bit_blast_shl_int g ls (n - 1)%num in
    let '(g1, cs1, ls1) := bit_blast_shl_int1 g_m ls_m in
    ((g1, catrev cs_m cs1), ls1)
  end.
Proof.
  - move=> _ _ n p Hp. rewrite -Hp. move: (N.le_pred_l n) => Hle.
    rewrite N.sub_1_r. move/(N.lt_eq_cases (N.pred n) n): Hle. case=> Hn.
    + assumption.
    + apply: N.lt_pred_l. move=> Hn0. rewrite Hn0 in Hp. discriminate.
  - exact: N.lt_wf_0.
Qed.

Definition mk_env_shl_int1 E g ls : env * generator * cnf * word :=
  (E, g, [::], dropmsl (joinlsl lit_ff ls)) .

Function mk_env_shl_int E g ls (n : N) {wf N.lt n} : env * generator * cnf * word :=
  match n with
  | N0 => (((E, g), [::]), ls)
  | _ => let: (E_m, g_m, cs_m, ls_m) := mk_env_shl_int E g ls (n - 1)%num in
         let: (E', g', cs, ls') := mk_env_shl_int1 E_m g_m ls_m in
         (((E', g'), catrev cs_m cs), ls')
  end .
Proof.
  - move=> _ _ _ n p Hp. rewrite -Hp. move: (N.le_pred_l n) => Hle.
    rewrite N.sub_1_r. move/(N.lt_eq_cases (N.pred n) n): Hle. case=> Hn.
    + assumption.
    + apply: N.lt_pred_l. move=> Hn0. rewrite Hn0 in Hp. discriminate.
  - exact: N.lt_wf_0.
Qed.

Lemma bit_blast_shl_int_N0 g ls :
  bit_blast_shl_int g ls N0 = (g, [::], ls).
Proof.
  symmetry. apply: R_bit_blast_shl_int_complete.
  apply: (R_bit_blast_shl_int_0 _ _ N0). reflexivity.
Qed.

Lemma bit_blast_shl_int_Npos g ls p g_m cs_m ls_m g' cs1 lrs :
  bit_blast_shl_int g ls (N.pos p - 1) = (g_m, cs_m, ls_m) ->
  bit_blast_shl_int1 g_m ls_m = (g', cs1, lrs) ->
  bit_blast_shl_int g ls (N.pos p) = (g', catrev cs_m cs1, lrs).
Proof.
  move=> Hbb Hbb1. move: (Logic.eq_sym Hbb) => {Hbb} Hbb.
  move: (R_bit_blast_shl_int_correct Hbb) => {Hbb} Hbb.
  symmetry. apply: R_bit_blast_shl_int_complete.
  by apply: (R_bit_blast_shl_int_1 _ _ _ _ _ _ _ Hbb _ _ _ _ _ _ _ Hbb1).
Qed.

Lemma mk_env_shl_int_N0 E g ls :
  mk_env_shl_int E g ls N0 = (E, g, [::], ls).
Proof.
  symmetry. apply: R_mk_env_shl_int_complete.
  apply: (R_mk_env_shl_int_0 _ _ _ N0). reflexivity.
Qed.

Lemma mk_env_shl_int_Npos E g ls p E_m g_m cs_m ls_m E' g' cs1 lrs :
  mk_env_shl_int E g ls (N.pos p - 1) = (E_m, g_m, cs_m, ls_m) ->
  mk_env_shl_int1 E_m g_m ls_m = (E', g', cs1, lrs) ->
  mk_env_shl_int E g ls (N.pos p) = (E', g', catrev cs_m cs1, lrs).
Proof.
  move=> Hbb Hbb1. move: (Logic.eq_sym Hbb) => {Hbb} Hbb.
  move: (R_mk_env_shl_int_correct Hbb) => {Hbb} Hbb.
  symmetry. apply: R_mk_env_shl_int_complete.
    by apply: (R_mk_env_shl_int_1 _ _ _ _ _ _ _ _ Hbb _ _ _ _ _ _ _ _ _ Hbb1).
Qed.



Lemma bit_blast_shl_int1_correct :
  forall g bs E ls g' cs lrs,
    bit_blast_shl_int1 g ls = (g', cs, lrs) ->
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (shlB1 bs).
Proof.
  move => g bs E ls g' cs lrs .
  rewrite /bit_blast_shl_int1 .
  case => _ _ <- Henc_bits Hcs .
  rewrite /shlB1 /= .
  apply: enc_bits_dropmsb; first apply: (add_prelude_tt Hcs) .
  rewrite enc_bits_joinlsb Henc_bits (add_prelude_enc_bit_ff Hcs) // .
Qed .

Lemma bit_blast_shl_int_correct :
  forall g bs n E ls g' cs lrs,
    bit_blast_shl_int g ls n = (g', cs, lrs) ->
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (shlB n bs).
Proof.
  move => g bs n E ls. eapply bit_blast_shl_int_ind.
  - clear n. move=> n Hn g' cs lrs. case=> ? ? ?; subst => /=.
    move=> H _. assumption.
  - clear n. move=> n [] => //=. move=> p Hn _ IH.
    move=> g_m cs_m ls_m Hm. move=> g1 cs1 ls1 H1.
    move=> g' cs lrs. case=> ? ? ?; subst => /=.
    move=> Henc Hcsm. rewrite add_prelude_catrev in Hcsm.
    move/andP: Hcsm=> [Hcsm Hcs1]. move: (IH _ _ _ Hm Henc Hcsm) => Hls_mbs.
    move: (bit_blast_shl_int1_correct H1 Hls_mbs Hcs1).
    rewrite shlB1_shlB_succ. rewrite -addn1.
    have ->: ((N.pos p - 1)%num + 1) = nat_of_pos p.
    { replace 1 with (nat_of_bin 1) by reflexivity.
      rewrite -nat_of_add_bin. rewrite N.sub_add.
      - exact: nat_of_bin_pos.
      - exact: Npos_ge1. }
    by apply.
Qed.

Lemma size_bit_blast_shl_int1 g ls g' cs lrs :
  bit_blast_shl_int1 g ls = (g', cs, lrs) ->
  size ls = size lrs .
Proof .
  rewrite /bit_blast_shl_int1 .
  case => _ _ <- .
  rewrite size_dropmsl size_joinlsl .
  rewrite subn1 addn1.
  reflexivity .
Qed .

Lemma size_bit_blast_shl_int g n ls g' cs lrs :
  bit_blast_shl_int g ls n = (g', cs, lrs) ->
  size ls = size lrs.
Proof.
  move: g' cs lrs. eapply bit_blast_shl_int_ind.
  - clear n. move=> n Hn g' cs lrs [] ? ? ?; subst => /=. reflexivity.
  - clear n. move=> n [] p Hn //=. move=> _ IH g_m cs_m ls_m Hbb g1 cs1 ls1 Hbb1.
    move=> g' cs lrs [] ? ? ?; subst => /=. rewrite (IH _ _ _ Hbb).
    exact: (size_bit_blast_shl_int1 Hbb1).
Qed.



Fixpoint bit_blast_shl_rec g ls ns (i : N) : generator * cnf * word :=
  match ns with
  | [::] => (g, [::], ls)
  | ns_hd::ns_tl =>
    let '(g_tl, cs_tl, ls_tl) := bit_blast_shl_rec g ls ns_tl (i * 2)%num in
    if ns_hd == lit_tt then
      let '(g_hd, cs_hd, ls_hd) := bit_blast_shl_int g_tl ls_tl i in
      (g_hd, catrev cs_tl cs_hd, ls_hd)
    else if ns_hd == lit_ff then
           (g_tl, cs_tl, ls_tl)
         else
           let '(g_hd, cs_hd, ls_hd) := bit_blast_shl_int g_tl ls_tl i in
           let '(g_ite, cs_ite, ls_ite) := bit_blast_ite g_hd ns_hd ls_hd ls_tl in
           (g_ite, catrev cs_tl (catrev cs_hd cs_ite), ls_ite)
  end .

Definition bit_blast_shl g ls ns : generator * cnf * word :=
  if size ls > 1 then
    let 'log2szls := Z.to_nat (Z.log2_up (Z.of_nat (size ls))) in
    let '(g_zero_hi, cs_zero_hi, zero_hi) :=
        bit_blast_const g (from_nat (size ns - log2szls) 0) in
    let '(g_zero, cs_zero, zero) :=
        bit_blast_const g_zero_hi (from_nat (size ls) 0) in
    let '(g_hi, cs_hi, ns_hi) :=
        bit_blast_extract g_zero (size ns).-1 log2szls ns in
    let '(g_lo, cs_lo, ns_lo) := bit_blast_extract g_hi log2szls.-1 0 ns in
    let '(g_eq, cs_eq, l_eq) := bit_blast_eq g_lo ns_hi zero_hi in
    let '(g_shl, cs_shl, ls_shl) := bit_blast_shl_rec g_eq ls ns_lo 1%num in
    let '(g_ite, cs_ite, ls_ite) := bit_blast_ite g_shl l_eq ls_shl zero in
    (g_ite,
     catrev cs_zero_hi
            (catrev cs_zero
                    (catrev cs_hi
                            (catrev cs_lo
                                    (catrev cs_eq
                                            (catrev cs_shl cs_ite))))),
     ls_ite)
  else
    bit_blast_shl_rec g ls ns 1%num .

Lemma bit_blast_shl_rec_correct g bs ns i E ls lns g' cs lrs :
  bit_blast_shl_rec g ls lns i = (g', cs, lrs) ->
  enc_bits E ls bs ->
  enc_bits E lns ns ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E lrs (shlB (to_nat ns * i) bs).
Proof.
  move => Hshlrec Hlsbs Hlnsns .
  move : (enc_bits_size Hlnsns) => Hsizelnsns .
  move : lns ns Hsizelnsns i g' cs lrs Hshlrec Hlsbs Hlnsns.
  apply : seq_ind2 => [|lns_hd ns_hd lns_tl ns_tl Hsizelnns IH] i g' cs lrs .
  - by case => _ <- <- .
  - rewrite /= .
    dcase (bit_blast_shl_rec g ls lns_tl (i * 2)) => [[[g_tl cs_tl] ls_tl] Hshlrec] .
    dcase (bit_blast_shl_int g_tl ls_tl i) => [[[g_hd cs_hd] ls_hd] Hshlint] /= .
    case Hlnshdtt : (lns_hd == lit_tt) .
    + case => _ <- <- Hlsbs Hlnsns Hcnf .
      move : Hlnsns; rewrite enc_bits_cons => /andP [Hlnsns_hd Hlnsns_tl] .
      move : Hcnf; rewrite add_prelude_catrev => /andP [Hcnfcs_tl Hcnfcs_hd] .
      move : (IH _ _ _ _ Hshlrec Hlsbs Hlnsns_tl Hcnfcs_tl) => Hlstlnstl .
      move : (bit_blast_shl_int_correct Hshlint Hlstlnstl Hcnfcs_hd) .
      rewrite shlB_add .
      move/eqP : Hlnshdtt => Hlnshdtt .
      rewrite Hlnshdtt in Hlnsns_hd .
      rewrite (add_prelude_enc_bit_true ns_hd Hcnfcs_tl) in Hlnsns_hd .
      rewrite Hlnsns_hd.
      rewrite nat_of_mul_bin (mulnC i 2%num). rewrite mulnA muln2 /=.
      by rewrite -[(1+ (to_nat ns_tl).*2)*i]/(i + ((to_nat ns_tl).*2)*i) .
    + case Hlnshdff : (lns_hd == lit_ff) .
      * case => _ <- <- Hlsbs Hlnsns Hcnfcs_tl .
        move : Hlnsns; rewrite enc_bits_cons => /andP [Hlnsns_hd Hlnsns_tl] .
        move : (IH _ _ _ _ Hshlrec Hlsbs Hlnsns_tl Hcnfcs_tl) .
        move/eqP : Hlnshdff => Hlnshdff .
        rewrite Hlnshdff in Hlnsns_hd .
        rewrite (add_prelude_enc_bit_is_not_true ns_hd Hcnfcs_tl) in Hlnsns_hd .
        rewrite (negbTE Hlnsns_hd) .
          by rewrite nat_of_mul_bin (mulnC i 2%num) mulnA muln2 /=.
      * dcase (bit_blast_ite g_hd lns_hd ls_hd ls_tl) => [[[g_ite cs_ite] ls_ite] Hite] .
        case => _ <- <- Hlsbs Hlnsns Hcnf .
        move : Hcnf; rewrite add_prelude_catrev => /andP [Hcnfcs_tl Hcnfcs_others] .
        move : Hcnfcs_others; rewrite add_prelude_catrev => /andP [Hcnfcs_hd Hcnfcs_ite] .
        move : Hlnsns; rewrite enc_bits_cons => /andP [Hlnsns_hd Hlnsns_tl] .
        move : (IH _ _ _ _ Hshlrec Hlsbs Hlnsns_tl Hcnfcs_tl) => Hlstlbs .
        move : (bit_blast_shl_int_correct Hshlint Hlstlbs Hcnfcs_hd) => Hlshdbs .
        rewrite shlB_add in Hlshdbs .
        move : (size_bit_blast_shl_int Hshlint) => /eqP Hlshdtl .
        rewrite eq_sym in Hlshdtl .
        move : (bit_blast_ite_correct Hlshdtl Hite Hlnsns_hd Hlshdbs Hlstlbs Hcnfcs_ite) .
        destruct ns_hd .
        + rewrite nat_of_mul_bin (mulnC i 2%num) mulnA muln2 .
          by rewrite -[(i+(to_nat ns_tl).*2 * i)]/((true + (to_nat ns_tl).*2)*i) .
        + rewrite nat_of_mul_bin (mulnC i 2%num) mulnA muln2 .
          by rewrite -[(false + (to_nat ns_tl).*2) * i]/((to_nat ns_tl).*2 *i) .
Qed.

Lemma mypredn_sub : forall m n, (m - n).-1 = (m.-1 - n) .
Proof .
  move => m n /= .
  elim : m .
  - done .
  - move => m IH /= .
    rewrite -subnS subSS // .
Qed .

Lemma log2_lt_lin_nat : forall n, 0 < n -> Z.to_nat (Z.log2_up (Z.of_nat n)) < n .
Proof .
  move => n /ltP Hlt .
  move : (Z.log2_up_lt_lin (Z.of_nat n)) => Hlog2_lt .
  move : (Hlog2_lt (inj_lt _ _ Hlt)) => {Hlt Hlog2_lt} Hlog2_lt .
  rewrite  -{2}(Nat2Z.id n) .
  apply Nats.lt_ltn; rewrite -Z2Nat.inj_lt;
    [ trivial
    | apply Z.log2_up_nonneg
    | apply Zle_0_nat]  .
  Qed .

Lemma extract_high i ns :
  i < size ns ->
  extract (size ns).-1 i ns = high (size ns - i) ns .
Proof .
  case i => [Hsz | j Hsz] /= .
  - rewrite /extract !subn0 !addn1 (Nat.lt_succ_pred 0);
      [ rewrite low_size //
      | apply Nats.ltn_lt; trivial ] .
  - rewrite /extract !addn1 .
    rewrite -mypredn_sub .
    rewrite !(Nat.lt_succ_pred 0) .
    * rewrite low_size // .
    * move : (ltn0Sn j) => H0j .
      move : (ltn_trans H0j Hsz) .
      apply Nats.ltn_lt => // .
    * apply Nats.ltn_lt .
      move : (ltn_sub2r Hsz Hsz) .
      rewrite subnn // .
Qed .

Lemma extract_low i ns :
  i < size ns ->
  extract i 0 ns = low i.+1 ns .
Proof .
  case i => [Hsz | j Hsz] /= .
  - rewrite /extract subnn addn1 . 
    rewrite low1_lsb {1}lastI high1_rcons /last // .
  - rewrite /extract subn0 !addn1; trivial .
    rewrite -{1}(size_low j.+2 ns) high_size // .
Qed .
    
Lemma extract_cat i ns :
  i.+1 < size ns ->
  ns = (extract i 0 ns) ++ (extract (size ns).-1 i.+1 ns) .
Proof .
  move => Hsz /= .
  move : (ltn_trans (ltnSn i) Hsz) => Hszlt .
  rewrite extract_low; trivial .
  rewrite extract_high; trivial .
  rewrite cat_low_high; trivial => /= .
- rewrite subnKC // .
Qed .

Lemma to_nat_bounded_high_zeros i ns :
  i.+1 < size ns ->
  extract (size ns).-1 i.+1 ns == from_nat (size ns - i.+1) 0 ->
  to_nat ns = to_nat (extract i 0 ns) .
Proof .
  move => Hsz /eqP Hhi /= .
  rewrite {1}(extract_cat Hsz) Hhi .
  rewrite -zeros_from_nat to_nat_cat to_nat_zeros mul0n addn0 // .
Qed .

(*
Lemma to_nat_zeros_iff bs : (exists n, bs = zeros n) <-> to_nat bs = 0 .
Proof .
  split .
  - elim => n ->; apply to_nat_zeros .
  - move => Hbs .  
    exists (size bs) .
    move : Hbs .
    elim : bs => [ Hbs | b bs IH ] .
    + done .
    + rewrite to_nat_cons size_joinlsb addn1 -zeros_cons .
      case : b .
      * done .
      * rewrite add0n .
        move => /eqP .
        rewrite double_eq0 => /eqP Heq0 .
        rewrite {1}(IH Heq0) // .
Qed .
 *)

Lemma to_nat_bounded_high_nonzeros i ns :
  i.+1 < size ns ->
  extract (size ns).-1 i.+1 ns != from_nat (size ns - i.+1) 0 ->
  2 ^ i.+1 <= to_nat ns .
Proof .
  move => Hsz .
  rewrite -zeros_from_nat .
  move : (size_extract (size ns).-1 i.+1 ns) .
  rewrite -mypredn_sub addn1 .
  rewrite (Nat.lt_succ_pred 0 (size ns - i.+1))  .
  - case => <- Hnzero .
    move : (neq_zeros_to_nat_gt0 Hnzero)
    => {Hnzero} Hgt0 .
    rewrite (extract_cat Hsz) to_nat_cat size_extract subn0 addn1 .
    rewrite -{1}(add0n (2 ^ i.+1)) .
    apply : leq_add; trivial .
    rewrite -{1}(mul1n (2 ^ i.+1)) .
    apply : leq_mul; trivial .
  - apply Nats.ltn_lt .
    move : (ltn_sub2r Hsz Hsz) .
    rewrite subnn // .
Qed .

Lemma Z2Nat_expn m n :
  (0 < m)%Z -> (0 <= n)%Z ->
  Z.to_nat (m ^ n) = (Z.to_nat m) ^ (Z.to_nat n) .
Admitted .

Lemma shlB_log2 bs ns :
  size bs > 1 ->
  size ns = size bs ->
  shlB (to_nat ns) bs =
  let log2szbs := Z.to_nat (Z.log2_up (Z.of_nat (size bs))) in
  if extract (size ns).-1 log2szbs ns == from_nat (size ns - log2szbs) 0
  then (bs <<# (to_nat (extract log2szbs.-1 0 ns) * 1%num))%bits
  else (size bs) -bits of (0)%bits .
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
  - rewrite -zeros_from_nat .
    apply shlB_oversize .
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

Corollary bit_blast_shl_correct g bs ns E ls lns g' cs lrs :
  size ls > 0 ->
  size ls = size lns ->
  bit_blast_shl g ls lns = (g', cs, lrs) ->
  enc_bits E ls bs ->
  enc_bits E lns ns ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E lrs (shlB (to_nat ns) bs).
Proof.
  move => Hszgt0 Hszeq Hshl Hlsbs Hlnsns Hcnf.
  rewrite -(muln1 (to_nat ns)).
  move : Hshl; rewrite /bit_blast_shl .
  remember (Z.to_nat (Z.log2_up (Z.of_nat (size ls)))) as log2szls .
  dcase (1 < size ls); case => /ltP Hcon .
  - dcase (bit_blast_const g (from_nat (size lns - log2szls) 0)) =>
    [[[g_zero_hi] cs_zero_hi] zero_hi] Hzero_hi .
    dcase (bit_blast_const g_zero_hi (from_nat (size ls) 0)) =>
    [[[g_zero cs_zero] zero]] Hzero .
    dcase (bit_blast_extract g_zero (size lns).-1 log2szls lns) =>
    [[[g_hi cs_hi] ns_hi]] Hhi .
    dcase (bit_blast_extract g_hi log2szls.-1 0 lns) =>
    [[[g_lo cs_lo] ns_lo]] Hlo .
    dcase (bit_blast_eq g_lo ns_hi zero_hi) =>
    [[[g_eq cs_eq] l_eq]] Heq .
    dcase (bit_blast_shl_rec g_eq ls ns_lo 1) =>
    [[[g_shl cs_shl] ls_shl]] Hshl .
    dcase (bit_blast_ite g_shl l_eq ls_shl zero) =>
    [[[g_ite cs_ite] ls_ite]] Hite .
    move => Hret .
    move : Hret Hcnf .
    case => _ <- <- .
    rewrite !add_prelude_catrev .
    move => /andP [[Hcnf_zero_hi /andP  [Hcnf_zero /andP  [Hcnf_hi
            /andP  [Hcnf_lo /andP  [Hcnf_eq /andP  [Hcnf_shl Hcnf_ite]]]]]]] .
    move : (bit_blast_const_correct Hzero_hi Hcnf_zero_hi)
    => {Hzero_hi Hcnf_zero_hi cs_zero_hi} Henc_zero_hi .
    move : (bit_blast_const_correct Hzero Hcnf_zero)
    => {g_zero_hi Hzero Hcnf_zero cs_zero} Henc_zero .
    move : (bit_blast_extract_correct Hhi Hlnsns Hcnf_hi)
    => {g_zero Hhi Hcnf_hi cs_hi} Henc_hi .
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
      apply log2_lt_lin_nat => // .
    }
    move => Hszhi .
    move : (bit_blast_eq_correct Heq Hszhi Henc_hi Henc_zero_hi Hcnf_eq)
    => {g_lo Hszhi Henc_hi Henc_zero_hi Heq Hcnf_eq cs_eq} Henc_eq .
    move : (bit_blast_shl_rec_correct Hshl Hlsbs Henc_lo Hcnf_shl)
    => {g_eq Hshl Henc_lo Hcnf_shl cs_shl} Henc_shl .
    have : size ls_shl == size zero .
    {
      rewrite (enc_bits_size Henc_shl) (enc_bits_size Henc_zero)
              size_shlB size_from_nat (enc_bits_size Hlsbs) // .
    }
    move => Hszshlzero .
    move : (bit_blast_ite_correct Hszshlzero Hite Henc_eq
                                  Henc_shl Henc_zero Hcnf_ite)
    => {g_shl g_ite l_eq Hszshlzero Hite Henc_eq
              Henc_shl Henc_zero Hcnf_ite cs_ite} .
    rewrite muln1 shlB_log2 .
    + by rewrite Heqlog2szls
                 !(enc_bits_size Hlnsns) !(enc_bits_size Hlsbs) /= .
    + rewrite -(enc_bits_size Hlsbs) . by apply Nats.lt_ltn .
    + by rewrite -(enc_bits_size Hlnsns) -Hszeq (enc_bits_size Hlsbs) .
  - move => Hbitblast .
    by apply (bit_blast_shl_rec_correct Hbitblast Hlsbs Hlnsns Hcnf) .
Qed.

Lemma mk_env_shl_int1_is_bit_blast_shl_int1 E g ls E' g' cs lrs :
    mk_env_shl_int1 E g ls = (E', g', cs, lrs) ->
    bit_blast_shl_int1 g ls = (g', cs, lrs) .
Proof .
  rewrite /mk_env_shl_int1 /bit_blast_shl_int1 .
  by case => _ <- <- <- .
Qed .

Lemma mk_env_shl_int_is_bit_blast_shl_int E g ls i E' g' cs lrs :
    mk_env_shl_int E g ls i = (E', g', cs, lrs) ->
    bit_blast_shl_int g ls i = (g', cs, lrs).
Proof.
  move: E' g' cs lrs. eapply mk_env_shl_int_ind.
  - clear i. move=> i Hi E' g' cs lrs [] ? ? ? ?; subst => /=.
    symmetry. apply: R_bit_blast_shl_int_complete.
    apply: (R_bit_blast_shl_int_0 _ _ 0). reflexivity.
  - clear i. move=> i [] p Hn //=. move=> _ IH E_m g_m cs_m ls_m Henv.
    move=> E1 g1 cs1 ls1 Henv1. move=> E' g' cs lrs [] ? ? ? ?; subst => /=.
    move: (mk_env_shl_int1_is_bit_blast_shl_int1 Henv1) => Hbb1.
    move: (IH _ _ _ _ Henv) => Hbb. exact: (bit_blast_shl_int_Npos Hbb Hbb1).
Qed.

Lemma size_mk_env_shl_int1 E g ls E' g' cs lrs :
  mk_env_shl_int1 E g ls = (E', g', cs, lrs) ->
  size ls = size lrs .
Proof .
  rewrite /mk_env_shl_int1 .
  case => _ _ _ <- .
  rewrite size_dropmsl size_joinlsl .
  rewrite subn1 addn1.
  reflexivity .
Qed .

Lemma size_mk_env_shl_int E g n ls E' g' cs lrs :
  mk_env_shl_int E g ls n = (E', g', cs, lrs) ->
  size ls = size lrs.
Proof.
  move: E' g' cs lrs. eapply mk_env_shl_int_ind.
  - clear n. move=> n Hn E' g' cs lrs [] ? ? ? ?; subst => /=. reflexivity.
  - clear n. move=> n [] p Hn //=. move=> _ IH E_m g_m cs_m ls_m Hbb.
    move=> E1 g1 cs1 ls1 Hbb1. move=> E' g' cs lrs [] ? ? ? ?; subst => /=.
    rewrite (IH _ _ _ _ Hbb). exact: (size_mk_env_shl_int1 Hbb1).
Qed.



Fixpoint mk_env_shl_rec E g ls ns (i : N) : env * generator * cnf * word :=
  match ns with
  | [::] => (E, g, [::], ls)
  | ns_hd::ns_tl =>
    let '(E_tl, g_tl, cs_tl, ls_tl) := mk_env_shl_rec E g ls ns_tl (i * 2) in
    if ns_hd == lit_tt then
      let '(E_hd, g_hd, cs_hd, ls_hd) := mk_env_shl_int E_tl g_tl ls_tl i in
      (E_hd, g_hd, catrev cs_tl cs_hd, ls_hd)
    else if ns_hd == lit_ff then
           (E_tl, g_tl, cs_tl, ls_tl)
         else
           let '(E_hd, g_hd, cs_hd, ls_hd) := mk_env_shl_int E_tl g_tl ls_tl i in
           let '(E_ite, g_ite, cs_ite, ls_ite) := mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl in
           (E_ite, g_ite, catrev cs_tl (catrev cs_hd cs_ite), ls_ite)
  end .

Definition mk_env_shl E g ls ns : env * generator * cnf * word :=
  if size ls > 1 then
    let 'log2szls := Z.to_nat (Z.log2_up (Z.of_nat (size ls))) in
    let '(E_zero_hi, g_zero_hi, cs_zero_hi, zero_hi) :=
        mk_env_const E g (from_nat (size ns - log2szls) 0) in
    let '(E_zero, g_zero, cs_zero, zero) :=
        mk_env_const E_zero_hi g_zero_hi (from_nat (size ls) 0) in
    let '(E_hi, g_hi, cs_hi, ns_hi) :=
        mk_env_extract E_zero g_zero (size ns).-1 log2szls ns in
    let '(E_lo, g_lo, cs_lo, ns_lo) :=
        mk_env_extract E_hi g_hi log2szls.-1 0 ns in
    let '(E_eq, g_eq, cs_eq, l_eq) := mk_env_eq E_lo g_lo ns_hi zero_hi in
    let '(E_shl, g_shl, cs_shl, ls_shl) :=
        mk_env_shl_rec E_eq g_eq ls ns_lo 1%num in
    let '(E_ite, g_ite, cs_ite, ls_ite) :=
        mk_env_ite E_shl g_shl l_eq ls_shl zero in
    (E_ite, g_ite,
     catrev cs_zero_hi
            (catrev cs_zero
                    (catrev cs_hi
                            (catrev cs_lo
                                    (catrev cs_eq
                                            (catrev cs_shl cs_ite))))),
     ls_ite)
  else
    mk_env_shl_rec E g ls ns 1%num .

Lemma mk_env_shl_rec_is_bit_blast_shl_rec E g ls ns i E' g' cs lrs :
    mk_env_shl_rec E g ls ns i = (E', g', cs, lrs) ->
    bit_blast_shl_rec g ls ns i = (g', cs, lrs) .
Proof .
  elim : ns i E' g' cs lrs => [|ns_hd ns_tl IH] i E' g' cs lrs .
  - rewrite /mk_env_shl_rec /= -/mk_env_shl_rec .
    by case => _ <- <- <- .
  - rewrite /mk_env_shl_rec /= -/mk_env_shl_rec .
    dcase (mk_env_shl_rec E g ls ns_tl (i*2)) => [[[[E_tl g_tl] cs_tl] ls_tl] Hrec] .
    rewrite (IH _ _ _ _ _ Hrec) .
    dcase (mk_env_shl_int E_tl g_tl ls_tl i) => [[[[E_hd g_hd] cs_hd] ls_hd] Hint] .
    rewrite (mk_env_shl_int_is_bit_blast_shl_int Hint) .
    dcase (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl) => [[[[E_ite g_ite] cs_ite] ls_ite] Hite] .
    rewrite (mk_env_ite_is_bit_blast_ite Hite) /= .
    case Hnshdtt : (ns_hd == lit_tt) .
    + by case => _ <- <- <- .
    + case Hnshdff : (ns_hd == lit_ff); by case => _ <- <- <- .
Qed .

Lemma mk_env_shl_is_bit_blast_shl E g ls ns E' g' cs lrs :
    mk_env_shl E g ls ns = (E', g', cs, lrs) ->
    bit_blast_shl g ls ns = (g', cs, lrs) .
Proof .
  rewrite /mk_env_shl /bit_blast_shl .
  remember (Z.to_nat (Z.log2_up (Z.of_nat (size ls)))) as log2szls .
  dcase (1 < size ls); case => /ltP Hcon .
  - dcase (mk_env_const E g (from_nat (size ns - log2szls) 0)) =>
    [[[[E_zero_hi] g_zero_hi] cs_zero_hi] zero_hi] Hzero_hi .
    rewrite (mk_env_const_is_bit_blast_const Hzero_hi) {Hzero_hi} .
    dcase (mk_env_const E_zero_hi g_zero_hi (from_nat (size ls) 0)) =>
    [[[[E_zero] g_zero cs_zero] zero]] Hzero .
    rewrite (mk_env_const_is_bit_blast_const Hzero)
            {E_zero_hi g_zero_hi Hzero} .
    dcase (mk_env_extract E_zero g_zero (size ns).-1 log2szls ns) =>
    [[[[E_hi] g_hi cs_hi] ns_hi]] Hhi .
    rewrite (mk_env_extract_is_bit_blast_extract Hhi)
            {E_zero g_zero Hhi} .
    dcase (mk_env_extract E_hi g_hi log2szls.-1 0 ns) =>
    [[[[E_lo] g_lo cs_lo] ns_lo]] Hlo .
    rewrite (mk_env_extract_is_bit_blast_extract Hlo)
            {E_hi g_hi Hlo} .
    dcase (mk_env_eq E_lo g_lo ns_hi zero_hi) =>
    [[[[E_eq] g_eq cs_eq] l_eq]] Heq .
    rewrite (mk_env_eq_is_bit_blast_eq Heq)
            {E_lo g_lo Heq} .
    dcase (mk_env_shl_rec E_eq g_eq ls ns_lo 1) =>
    [[[[E_shl] g_shl cs_shl] ls_shl]] Hshl .
    rewrite (mk_env_shl_rec_is_bit_blast_shl_rec Hshl)
            {E_eq g_eq Hshl} .
    dcase (mk_env_ite E_shl g_shl l_eq ls_shl zero) =>
    [[[[E_ite] g_ite cs_ite] ls_ite]] Hite .
    rewrite (mk_env_ite_is_bit_blast_ite Hite)
            {E_shl g_shl Hite} .
    by case => _ <- <- <- .
  - apply mk_env_shl_rec_is_bit_blast_shl_rec .
Qed .

Lemma mk_env_shl_int_newer_gen E g ls n E' g' cs lrs :
    mk_env_shl_int E g ls n = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move: E' g' cs lrs. eapply mk_env_shl_int_ind.
  - clear n. move=> n Hn E' g' cs lrs [] ? ? ? ?; subst => /=.
    exact: Pos.leb_refl.
  - clear n. move=> n [] p Hn //=. move=> _ IH E_m g_m cs_m ls_m Henv.
    move=> E1 g1 cs1 ls1 Henv1. move=> E' g' cs lrs [] ? ? ? ?; subst => /=.
    move : (IH _ _ _ _ Henv) => {IH Henv} Hind.
    rewrite /mk_env_shl_int1 in Henv1. case: Henv1 => ? ? ? ?; subst.
    assumption.
Qed.

Lemma mk_env_shl_rec_newer_gen E g ls ns i E' g' cs lrs :
    mk_env_shl_rec E g ls ns i = (E', g', cs, lrs) ->
    (g <=? g')%positive .
Proof .
  elim : ns E' g' cs lrs i => [|ns_hd ns_tl IH] E' g' cs lrs i .
  - rewrite /mk_env_shl_rec /=; by t_auto_newer .
  - rewrite /mk_env_shl_rec /= -/mk_env_shl_rec .
    dcase (mk_env_shl_rec E g ls ns_tl (i*2)) => [[[[E_tl g_tl] cs_tl] ls_tl] Hrec] .
    move : (IH _ _ _ _ _ Hrec) => Hggtl .
    dcase (mk_env_shl_int E_tl g_tl ls_tl i) => [[[[E_hd g_hd] cs_hd] ls_hd] Hint] .
    move : (mk_env_shl_int_newer_gen Hint) => Hgtlghd .
    dcase (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl) => [[[[E_ite g_ite] cs_ite] ls_ite] Hite] .
    move : (mk_env_ite_newer_gen Hite) => Hghdgite .
    move : (pos_leb_trans Hggtl Hgtlghd) => Hgghd .
    move : (pos_leb_trans Hgghd Hghdgite) => Hggite .
    case : (ns_hd == lit_tt) .
    + by case => _ <- _ _ .
    + case : (ns_hd == lit_ff); by case => _ <- _ _ .
Qed .

Lemma mk_env_shl_newer_gen E g ls ns E' g' cs lrs :
  mk_env_shl E g ls ns = (E', g', cs, lrs) ->
  (g <=? g')%positive .
Proof .
  rewrite /mk_env_shl .
  remember (Z.to_nat (Z.log2_up (Z.of_nat (size ls)))) as log2szls .
  dcase (1 < size ls); case => /ltP Hcon .
  - dcase (mk_env_const E g (from_nat (size ns - log2szls) 0)) =>
    [[[[E_zero_hi] g_zero_hi] cs_zero_hi] zero_hi] Hzero_hi .
    move : (mk_env_const_newer_gen Hzero_hi)
    => {Hzero_hi} Hg_gzerohi .
    dcase (mk_env_const E_zero_hi g_zero_hi (from_nat (size ls) 0)) =>
    [[[[E_zero] g_zero cs_zero] zero]] Hzero .
    move : (mk_env_const_newer_gen Hzero)
    => {E_zero_hi Hzero} Hgzerohi_gzero .
    dcase (mk_env_extract E_zero g_zero (size ns).-1 log2szls ns) =>
    [[[[E_hi] g_hi cs_hi] ns_hi]] Hhi .
    move : (mk_env_extract_newer_gen Hhi)
    => {E_zero Hhi } Hgzero_ghi .
    dcase (mk_env_extract E_hi g_hi log2szls.-1 0 ns) =>
    [[[[E_lo] g_lo cs_lo] ns_lo]] Hlo .
    move : (mk_env_extract_newer_gen Hlo)
    => {E_hi Hlo} Hghi_glo .
    dcase (mk_env_eq E_lo g_lo ns_hi zero_hi) =>
    [[[[E_eq] g_eq cs_eq] l_eq]] Heq .
    move : (mk_env_eq_newer_gen Heq)
    => {E_lo Heq} Hglo_geq .
    dcase (mk_env_shl_rec E_eq g_eq ls ns_lo 1) =>
    [[[[E_shl] g_shl cs_shl] ls_shl]] Hshl .
    move : (mk_env_shl_rec_newer_gen Hshl)
    => {E_eq Hshl} Hgeq_gshl .
    dcase (mk_env_ite E_shl g_shl l_eq ls_shl zero) =>
    [[[[E_ite] g_ite cs_ite] ls_ite]] Hite .
    move : (mk_env_ite_newer_gen Hite)
    => {E_shl Hite} Hgshl_gite .
    case => _ <- _ _ { cs_zero_hi cs_zero cs_lo cs_hi cs_shl ns_hi ns_lo } .
    move : (pos_leb_trans Hg_gzerohi Hgzerohi_gzero)
    => {Hg_gzerohi Hgzerohi_gzero g_zero_hi} => Hg_gzero .
    move : (pos_leb_trans Hgzero_ghi Hghi_glo)
    => {Hgzero_ghi Hghi_glo g_hi} => Hgzero_glo .
    move : (pos_leb_trans Hglo_geq Hgeq_gshl)
    => {Hglo_geq Hgeq_gshl g_eq} => Hglo_gshl .
    move : (pos_leb_trans Hglo_gshl Hgshl_gite)
    => {Hglo_gshl Hgshl_gite g_shl} => Hglo_gite .
    move : (pos_leb_trans Hgzero_glo Hglo_gite)
    => {Hgzero_glo Hglo_gite g_lo} => Hgzero_gite .
    by apply (pos_leb_trans Hg_gzero Hgzero_gite) .
  - exact : mk_env_shl_rec_newer_gen .
Qed .

Lemma mk_env_shl_int_newer_res E g n E' g' ls cs lrs :
  newer_than_lit g lit_tt ->
  newer_than_lits g ls ->
  mk_env_shl_int E g ls n = (E', g', cs, lrs) ->
  newer_than_lits g' lrs .
Proof .
  move => Htt Hls .
  move: E' g' cs lrs. eapply mk_env_shl_int_ind.
  - clear n. move=> n Hn E' g' cs lrs [] ? ? ? ?; subst => /=.
    assumption.
  - clear n. move=> n [] p Hn //=. move=> _ IH E_m g_m cs_m ls_m Henv.
    move=> E1 g1 cs1 ls1 [] ? ? ? ?; subst. move=> E' g' cs lrs [] ? ? ? ?; subst.
    move: (IH _ _ _ _ Henv) => Hlsm.
    move : (mk_env_shl_int_newer_gen Henv) => {Henv} Hggm.
    move : (newer_than_lit_le_newer Htt Hggm) => Hgmtt.
    generalize Hgmtt.
    rewrite newer_than_lit_tt_ff => Hgmff.
    move : (newer_than_lits_joinlsl Hgmff Hlsm) => Hgmjoinlsl.
    move : (newer_than_lits_splitmsl Hgmtt Hgmjoinlsl) => /andP [Hsplit1 _].
    by rewrite /dropmsl.
Qed.

Lemma mk_env_shl_rec_newer_res E g i E' g' ls ns cs lrs :
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g ns ->
  mk_env_shl_rec E g ls ns i = (E', g', cs, lrs) ->
  newer_than_lits g' lrs .
Proof .
  move => Hgtt Hgls .
  elim : ns E' g' cs lrs i => [|ns_hd ns_tl IH] E' g' cs lrs i Hgns .
  - rewrite /mk_env_shl_rec /=; by t_auto_newer .
  - rewrite /mk_env_shl_rec /= -/mk_env_shl_rec .
    move : Hgns; rewrite newer_than_lits_cons => /andP [Hgnshd Hgnstl] .
    dcase (mk_env_shl_rec E g ls ns_tl (i*2)) => [[[[E_tl g_tl] cs_tl] ls_tl] Hrec] .
    move : (IH _ _ _ _ _ Hgnstl Hrec) => Hgtllstl .
    move : (mk_env_shl_rec_newer_gen Hrec) => Hggtl .
    dcase (mk_env_shl_int E_tl g_tl ls_tl i) => [[[[E_hd g_hd] cs_hd] ls_hd] Hint] .
    move : (mk_env_shl_int_newer_res (newer_than_lit_le_newer Hgtt Hggtl) Hgtllstl Hint) => Hghdlshd .
    dcase (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl) => [[[[E_ite g_ite] cs_ite] ls_ite] Hite] .
    move : (mk_env_ite_newer_res Hite) => Hgitelsite .
    case : (ns_hd == lit_tt) .
    + by case => _ <- _ <- .
    + case : (ns_hd == lit_ff); by case => _ <- _ <- .
Qed .

Lemma mk_env_shl_newer_res E g ls ns E' g' cs lrs :
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g ns ->
  mk_env_shl E g ls ns = (E', g', cs, lrs) ->
  newer_than_lits g' lrs .
Proof .
  move => Hgtt Hgls Hgns .
  rewrite /mk_env_shl .
  remember (Z.to_nat (Z.log2_up (Z.of_nat (size ls)))) as log2szls .
  dcase (1 < size ls); case => /ltP Hcon .
  - dcase (mk_env_const E g (from_nat (size ns - log2szls) 0)) =>
    [[[[E_zero_hi] g_zero_hi] cs_zero_hi] zero_hi] Hzero_hi .
    move : (mk_env_const_newer_res Hzero_hi Hgtt) => Hgzerohi .
    move : (newer_than_lit_le_newer Hgtt (mk_env_const_newer_gen Hzero_hi))
           (newer_than_lits_le_newer Hgls (mk_env_const_newer_gen Hzero_hi))
           (newer_than_lits_le_newer Hgns (mk_env_const_newer_gen Hzero_hi))
    => {Hzero_hi} Hgzerohitt Hgzerohils Hgzerohins .
    dcase (mk_env_const E_zero_hi g_zero_hi (from_nat (size ls) 0)) =>
    [[[[E_zero] g_zero cs_zero] zero]] Hzero .
    move : (mk_env_const_newer_res Hzero Hgzerohitt) => Hgzero .
    move : (newer_than_lit_le_newer Hgzerohitt (mk_env_const_newer_gen Hzero))
           (newer_than_lits_le_newer Hgzerohils (mk_env_const_newer_gen Hzero))
           (newer_than_lits_le_newer Hgzerohins (mk_env_const_newer_gen Hzero))
    => {E_zero_hi Hgzerohitt Hgzerohils Hgzerohins Hzero}
         Hgzerott Hgzerols Hgzerons .
    dcase (mk_env_extract E_zero g_zero (size ns).-1 log2szls ns) =>
    [[[[E_hi] g_hi cs_hi] ns_hi]] Hhi .
    move : (mk_env_extract_newer_res Hhi Hgzerott Hgzerons) => Hghi .
    move : (newer_than_lit_le_newer Hgzerott (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgzerols (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgzerons (mk_env_extract_newer_gen Hhi))
    => {E_zero Hgzerott Hgzerols Hgzerons Hhi} Hghitt Hghils Hghins .
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
    dcase (mk_env_shl_rec E_eq g_eq ls ns_lo 1) =>
    [[[[E_shl] g_shl cs_shl] ls_shl]] Hshl .
    move : (mk_env_shl_rec_newer_res Hgeqtt Hgeqls Hgeqnslo Hshl) => Hgshl .
    move : (newer_than_lit_le_newer Hgeqtt (mk_env_shl_rec_newer_gen Hshl))
           (newer_than_lits_le_newer Hgeqls (mk_env_shl_rec_newer_gen Hshl))
           (newer_than_lits_le_newer Hgeqns (mk_env_shl_rec_newer_gen Hshl))
    => {E_eq Hgeqtt Hgeqls Hgeqns Hshl} Hgshltt Hgshlls Hgshlns .
    dcase (mk_env_ite E_shl g_shl l_eq ls_shl zero) =>
    [[[[E_ite] g_ite cs_ite] ls_ite]] Hite .
    move : (mk_env_ite_newer_res Hite)
    => {E_shl Hgshltt Hgshlls Hgshlns Hite} Hgshl_gite .
    by case => _ <- _ <- { cs_zero_hi cs_zero cs_lo cs_hi cs_shl } .
  - by apply mk_env_shl_rec_newer_res .
Qed .

Lemma mk_env_shl_int_newer_cnf E g ls n E' g' cs lr :
    mk_env_shl_int E g ls n = (E', g', cs, lr) ->
    newer_than_lits g ls ->
    newer_than_cnf g' cs .
Proof .
  move: E' g' cs lr. eapply mk_env_shl_int_ind.
  - clear n. move=> n Hn E' g' cs lrs [] ? ? ? ?; subst => /=. done.
  - clear n. move=> n [] p Hn //=. move=> _ IH E_m g_m cs_m ls_m Henv.
    move=> E1 g1 cs1 ls1 [] ? ? ? ?; subst. move=> E' g' cs lrs [] ? ? ? ?; subst.
    move=> Hgls. move : (IH _ _ _ _ Henv Hgls) => Hgmcsm.
    by rewrite newer_than_cnf_catrev Hgmcsm /=.
Qed .

Lemma mk_env_shl_rec_newer_cnf E g ls ns i E' g' cs lr :
  mk_env_shl_rec E g ls ns i = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g ns ->
  newer_than_cnf g' cs .
Proof .
  elim : ns E' g' cs lr i => [|ns_hd ns_tl IH] E' g' cs lr i .
  - rewrite /mk_env_shl_rec /=; by case => _ <- <- _ .
  - rewrite /mk_env_shl_rec /= -/mk_env_shl_rec .
    dcase (mk_env_shl_rec E g ls ns_tl (i*2)) => [[[[E_tl g_tl] cs_tl] ls_tl] Hrec] .
    dcase (mk_env_shl_int E_tl g_tl ls_tl i) => [[[[E_hd g_hd] cs_hd] ls_hd] Hint] .
    dcase (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl) => [[[[E_ite g_ite] cs_ite] ls_ite] Hite] .
    move => Htemp Hgtt Hgls /andP [Hgnshd Hgnstl] .
    move : Htemp .
    move : (IH _ _ _ _ _ Hrec Hgtt Hgls Hgnstl) => Hgtlcstl .
    move : (mk_env_shl_rec_newer_res Hgtt Hgls Hgnstl Hrec) => Hgtllstl .
    move : (mk_env_shl_int_newer_cnf Hint Hgtllstl) => Hghdcshd .
    move : (mk_env_shl_int_newer_gen Hint) => Hgtlghd .
     case : (ns_hd == lit_tt) .
    + case => _ <- <- _ .
      by rewrite newer_than_cnf_catrev Hghdcshd (newer_than_cnf_le_newer Hgtlcstl Hgtlghd) .
    + case : (ns_hd == lit_ff) .
      * by case => _ <- <- _ .
      * case => _ <- <- _ .
        rewrite !newer_than_cnf_catrev .
        move : (mk_env_ite_newer_gen Hite) => Hghdgite .
        move : (mk_env_shl_rec_newer_gen Hrec) => Hggtl .
        move : (newer_than_lit_le_newer Hgnshd (pos_leb_trans Hggtl Hgtlghd)) => Hghdnshd .
        move : (mk_env_shl_int_newer_res (newer_than_lit_le_newer Hgtt Hggtl) Hgtllstl Hint) => Hghdlshd .
        move : (mk_env_ite_newer_cnf Hite (newer_than_lit_le_newer Hgtt (pos_leb_trans Hggtl Hgtlghd)) Hghdnshd Hghdlshd (newer_than_lits_le_newer Hgtllstl Hgtlghd)) => Hgitecsite .
        by rewrite (newer_than_cnf_le_newer Hgtlcstl (pos_leb_trans Hgtlghd Hghdgite)) (newer_than_cnf_le_newer Hghdcshd Hghdgite) Hgitecsite .
Qed .

Lemma mk_env_shl_newer_cnf E g ls ns E' g' cs lrs :
  mk_env_shl E g ls ns = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g ns ->
  newer_than_cnf g' cs .
Proof .
  move => Henv Hgtt Hgls Hgns .
  move : Henv; rewrite /mk_env_shl .
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
    dcase (mk_env_const E_zero_hi g_zero_hi (from_nat (size ls) 0)) =>
    [[[[E_zero] g_zero cs_zero] zero]] Hzero .
    move : (mk_env_const_newer_cnf Hzero Hgzerohitt)
           (mk_env_const_newer_res Hzero Hgzerohitt)
    => Hgzero Hgzerozero .
    move : (newer_than_lit_le_newer Hgzerohitt (mk_env_const_newer_gen Hzero))
           (newer_than_lits_le_newer Hgzerohils (mk_env_const_newer_gen Hzero))
           (newer_than_lits_le_newer Hgzerohins (mk_env_const_newer_gen Hzero))
           (newer_than_lits_le_newer Hgzerohizerohi (mk_env_const_newer_gen Hzero))
           (newer_than_cnf_le_newer Hgzerohi (mk_env_const_newer_gen Hzero))
    => {Hgzerohi Hgzerohizerohi E_zero_hi Hgzerohitt Hgzerohils Hgzerohins Hzero}
         Hgzerott Hgzerols Hgzerons Hgzerozerohi Hgzerohi .
    dcase (mk_env_extract E_zero g_zero (size ns).-1 log2szls ns) =>
    [[[[E_hi] g_hi cs_hi] ns_hi]] Hhi .
    move : (mk_env_extract_newer_cnf Hhi Hgzerott Hgzerons)
           (mk_env_extract_newer_res Hhi Hgzerott Hgzerons)
    => Hghi Hghinshi .
    move : (newer_than_lit_le_newer Hgzerott (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgzerols (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgzerons (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgzerozerohi (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgzerozero (mk_env_extract_newer_gen Hhi))
           (newer_than_cnf_le_newer Hgzerohi (mk_env_extract_newer_gen Hhi))
           (newer_than_cnf_le_newer Hgzero (mk_env_extract_newer_gen Hhi))
    => {Hgzero Hgzerohi E_zero Hgzerott Hgzerols Hgzerons Hgzerozerohi Hgzerozero Hhi}
         Hghitt Hghils Hghins Hghizerohi Hghizero Hgzerohi Hgzero .
    dcase (mk_env_extract E_hi g_hi log2szls.-1 0 ns) =>
    [[[[E_lo] g_lo cs_lo] ns_lo]] Hlo .
    move : (mk_env_extract_newer_cnf Hlo Hghitt Hghins)
           (mk_env_extract_newer_res Hlo Hghitt Hghins)
    => Hglo Hglonslo .
    move : (newer_than_lit_le_newer Hghitt (mk_env_extract_newer_gen Hlo))
           (newer_than_lits_le_newer Hghils (mk_env_extract_newer_gen Hlo))
           (newer_than_lits_le_newer Hghins (mk_env_extract_newer_gen Hlo))
           (newer_than_lits_le_newer Hghizerohi (mk_env_extract_newer_gen Hlo))
           (newer_than_lits_le_newer Hghizero (mk_env_extract_newer_gen Hlo))
           (newer_than_lits_le_newer Hghinshi (mk_env_extract_newer_gen Hlo))
           (newer_than_cnf_le_newer Hgzerohi (mk_env_extract_newer_gen Hlo))
           (newer_than_cnf_le_newer Hgzero (mk_env_extract_newer_gen Hlo))
           (newer_than_cnf_le_newer Hghi (mk_env_extract_newer_gen Hlo))
    => {Hghi Hgzero Hgzerohi Hghinshi E_hi Hghitt Hghils Hghizerohi Hghizero Hghins Hlo}
         Hglott Hglols Hglons Hglozerohi Hglozero Hglonshi Hgzerohi Hgzero Hghi.
    dcase (mk_env_eq E_lo g_lo ns_hi zero_hi) =>
    [[[[E_eq] g_eq cs_eq] l_eq]] Heq .
    move : (mk_env_eq_newer_cnf Heq Hglott Hglonshi Hglozerohi)
           (mk_env_eq_newer_res Heq)
    => {Hglonshi Hglozerohi} Hgeq Hgeqleq .
    move : (newer_than_lit_le_newer Hglott (mk_env_eq_newer_gen Heq))
           (newer_than_lits_le_newer Hglols (mk_env_eq_newer_gen Heq))
           (newer_than_lits_le_newer Hglons (mk_env_eq_newer_gen Heq))
           (newer_than_lits_le_newer Hglozero (mk_env_eq_newer_gen Heq))
           (newer_than_lits_le_newer Hglonslo (mk_env_eq_newer_gen Heq))
           (newer_than_cnf_le_newer Hgzerohi (mk_env_eq_newer_gen Heq))
           (newer_than_cnf_le_newer Hgzero (mk_env_eq_newer_gen Heq))
           (newer_than_cnf_le_newer Hghi (mk_env_eq_newer_gen Heq))
           (newer_than_cnf_le_newer Hglo (mk_env_eq_newer_gen Heq))
    => {Hglo Hghi Hgzero Hgzerohi E_lo Hglott Hglols Hglons Hglozero Heq Hglonslo}
         Hgeqtt Hgeqls Hgeqns Hgeqzero Hgeqnslo Hgzerohi Hgzero Hghi Hglo .
    dcase (mk_env_shl_rec E_eq g_eq ls ns_lo 1) =>
    [[[[E_shl] g_shl cs_shl] ls_shl]] Hshl .
    move : (mk_env_shl_rec_newer_cnf Hshl Hgeqtt Hgeqls Hgeqnslo)
           (mk_env_shl_rec_newer_res Hgeqtt Hgeqls Hgeqnslo Hshl)
    => Hgshl Hgshllsshl .
    move : (newer_than_lit_le_newer Hgeqtt (mk_env_shl_rec_newer_gen Hshl))
           (newer_than_lits_le_newer Hgeqls (mk_env_shl_rec_newer_gen Hshl))
           (newer_than_lits_le_newer Hgeqns (mk_env_shl_rec_newer_gen Hshl))
           (newer_than_lits_le_newer Hgeqzero (mk_env_shl_rec_newer_gen Hshl))
           (newer_than_lit_le_newer Hgeqleq (mk_env_shl_rec_newer_gen Hshl))
           (newer_than_cnf_le_newer Hgzerohi (mk_env_shl_rec_newer_gen Hshl))
           (newer_than_cnf_le_newer Hgzero (mk_env_shl_rec_newer_gen Hshl))
           (newer_than_cnf_le_newer Hghi (mk_env_shl_rec_newer_gen Hshl))
           (newer_than_cnf_le_newer Hglo (mk_env_shl_rec_newer_gen Hshl))
           (newer_than_cnf_le_newer Hgeq (mk_env_shl_rec_newer_gen Hshl))
    => {Hgeq Hglo Hghi Hgzero Hgzerohi
             E_eq Hgeqtt Hgeqls Hgeqns Hgeqzero Hshl Hgeqnslo Hgeqleq}
         Hgshltt Hgshlls Hgshlns Hgshlzero Hgshlleq Hgzerohi Hgzero Hghi Hglo Hgeq .
    dcase (mk_env_ite E_shl g_shl l_eq ls_shl zero) =>
    [[[[E_ite] g_ite cs_ite] ls_ite]] Hite .
   move : (mk_env_ite_newer_res Hite)
   => Hgshl_gite .
   move : (mk_env_ite_newer_cnf Hite Hgshltt Hgshlleq Hgshllsshl Hgshlzero)
          (newer_than_cnf_le_newer Hgzerohi (mk_env_ite_newer_gen Hite))
          (newer_than_cnf_le_newer Hgzero (mk_env_ite_newer_gen Hite))
          (newer_than_cnf_le_newer Hghi (mk_env_ite_newer_gen Hite))
          (newer_than_cnf_le_newer Hglo (mk_env_ite_newer_gen Hite))
          (newer_than_cnf_le_newer Hgeq (mk_env_ite_newer_gen Hite))
          (newer_than_cnf_le_newer Hgshl (mk_env_ite_newer_gen Hite))
   => {Hgshl Hgeq Hglo Hghi Hgzero Hgzerohi
       Hite Hgshllsshl Hgshltt Hgshlls Hgshlns Hgshlzero Hgshlleq}
       Hgite Hgzerohi Hgzero Hghi Hglo Hgeq Hgshl .
   case => _ <- <- _ .
   by rewrite !newer_than_cnf_catrev Hgzerohi Hgzero Hghi Hglo Hgeq Hgite Hgshl .
  - move => Henv .
    by apply (mk_env_shl_rec_newer_cnf Henv Hgtt Hgls Hgns) .
Qed .

Lemma mk_env_shl_int_preserve E g ls n E' g' cs lrs :
    mk_env_shl_int E g ls n = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move: E' g' cs lrs. eapply mk_env_shl_int_ind.
  - clear n. move=> n Hn E' g' cs lrs [] ? ? ? ?; subst => /=. done.
  - clear n. move=> n [] p Hn //=. move=> _ IH E_m g_m cs_m ls_m Henv.
    move=> E1 g1 cs1 ls1 [] ? ? ? ?; subst. move=> E' g' cs lrs [] ? ? ? ?; subst.
    exact: (IH _ _ _ _ Henv).
Qed.

Lemma mk_env_shl_rec_preserve E g ls ns i E' g' cs lrs :
  mk_env_shl_rec E g ls ns i = (E', g', cs, lrs) ->
  env_preserve E E' g .
Proof .
  elim : ns E' g' cs lrs i => [| ns_hd ns_tl IH] E' g' cs lrs i .
  - rewrite /mk_env_shl_rec /=; by case => <- _ _ _ .
  - rewrite /mk_env_shl_rec /= -/mk_env_shl_rec .
    dcase (mk_env_shl_rec E g ls ns_tl (i*2)) => [[[[E_tl g_tl] cs_tl] ls_tl] Hrec] .
    dcase (mk_env_shl_int E_tl g_tl ls_tl i) => [[[[E_hd g_hd] cs_hd] ls_hd] Hint] .
    dcase (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl) => [[[[E_ite g_ite] cs_ite] ls_ite] Hite] .
    move : (IH _ _ _ _ _ Hrec) => HEEtl .
    move : (mk_env_shl_int_preserve Hint) => HEtlEhd .
    move : (mk_env_ite_preserve Hite) => HEhdEite .
    move : (mk_env_shl_rec_newer_gen Hrec) => Hggtl .
    move : (mk_env_shl_int_newer_gen Hint) => Hgtlghd .
    move : (mk_env_ite_newer_gen Hite) => Hghdgite .
    move : (env_preserve_le HEtlEhd Hggtl) => HEtlEhdg .
    move : (env_preserve_le HEhdEite (pos_leb_trans Hggtl Hgtlghd)) => HEhdEiteg .
    case : (ns_hd == lit_tt) .
    + case => <- _ _ _; by t_auto_preserve .
    + case : (ns_hd == lit_ff); case => <- _ _ _; by t_auto_preserve .
Qed .

Lemma mk_env_shl_preserve E g ls ns E' g' cs lrs :
  mk_env_shl E g ls ns = (E', g', cs, lrs) ->
  env_preserve E E' g .
Proof .
  rewrite /mk_env_shl.
  remember (Z.to_nat (Z.log2_up (Z.of_nat (size ls)))) as log2szls .
  dcase (1 < size ls); case => /ltP _ .
  - dcase (mk_env_const E g (from_nat (size ns - log2szls) 0)) =>
    [[[[E_zero_hi] g_zero_hi] cs_zero_hi] zero_hi] Hzero_hi .
    move : (mk_env_const_newer_gen Hzero_hi)
           (mk_env_const_preserve Hzero_hi)
    => {Hzero_hi} Hggzerohi HEEzerohi .
    dcase (mk_env_const E_zero_hi g_zero_hi (from_nat (size ls) 0)) =>
    [[[[E_zero] g_zero cs_zero] zero]] Hzero .
    move : (mk_env_const_newer_gen Hzero)
           (mk_env_const_preserve Hzero)
    => {Hzero} Hgzerohigzero HEzerohiEzero .
    move : (env_preserve_le HEzerohiEzero Hggzerohi)
    => {HEzerohiEzero} HEzerohiEzero .
    dcase (mk_env_extract E_zero g_zero (size ns).-1 log2szls ns) =>
    [[[[E_hi] g_hi cs_hi] ns_hi]] Hhi .
    move : (mk_env_extract_newer_gen Hhi)
           (mk_env_extract_preserve Hhi)
    => {Hhi} Hgzeroghi HEzeroEhi .
    move : (env_preserve_le
              (env_preserve_le HEzeroEhi Hgzerohigzero) Hggzerohi)
    => {HEzeroEhi} HEzeroEhi .
    dcase (mk_env_extract E_hi g_hi log2szls.-1 0 ns) =>
    [[[[E_lo] g_lo cs_lo] ns_lo]] Hlo .
    move : (mk_env_extract_newer_gen Hlo)
           (mk_env_extract_preserve Hlo)
    => {Hlo} Hghiglo HEhiElo .
    move : (env_preserve_le
              (env_preserve_le
                 (env_preserve_le HEhiElo Hgzeroghi) Hgzerohigzero)
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
                    (env_preserve_le HEloEeq Hghiglo)
                    Hgzeroghi)
                 Hgzerohigzero)
              Hggzerohi)
    => {HEloEeq} HEloEeq .
    dcase (mk_env_shl_rec E_eq g_eq ls ns_lo 1) =>
    [[[[E_shl] g_shl cs_shl] ls_shl]] Hshl .
    move : (mk_env_shl_rec_newer_gen Hshl)
           (mk_env_shl_rec_preserve Hshl)
    => {Hshl} Hgeqgshl HEeqEshl .
    move : (env_preserve_le
              (env_preserve_le
                 (env_preserve_le
                    (env_preserve_le
                       (env_preserve_le HEeqEshl Hglogeq)
                       Hghiglo)
                    Hgzeroghi)
                 Hgzerohigzero)
              Hggzerohi)
    => {HEeqEshl} HEeqEshl .
    dcase (mk_env_ite E_shl g_shl l_eq ls_shl zero) =>
    [[[[E_ite] g_ite cs_ite] ls_ite]] Hite .
    move : (mk_env_ite_newer_gen Hite)
           (mk_env_ite_preserve Hite)
    => {Hite} Hgshlgite HEshlEite .
    move : (env_preserve_le
              (env_preserve_le
                 (env_preserve_le
                    (env_preserve_le
                       (env_preserve_le
                          (env_preserve_le HEshlEite Hgeqgshl)
                          Hglogeq)
                       Hghiglo)
                    Hgzeroghi)
                 Hgzerohigzero)
              Hggzerohi)
    => {Hggzerohi Hgzerohigzero Hgzeroghi Hghiglo Hglogeq Hgeqgshl
                  Hgshlgite HEshlEite}
         HEshlEite .
    case => <- _ _ _ { g_zero_hi cs_zero_hi g_zero cs_zero
                       g_lo cs_lo ns_lo g_hi cs_hi ns_hi
                       g_eq cs_eq g_shl cs_shl
                       g_ite cs_ite } .
    apply env_preserve_trans with E_shl; trivial => {HEshlEite} .
    apply env_preserve_trans with E_eq; trivial => {HEeqEshl} .
    apply env_preserve_trans with E_lo; trivial => {HEloEeq} .
    apply env_preserve_trans with E_hi; trivial => {HEhiElo} .
    apply env_preserve_trans with E_zero; trivial => {HEzeroEhi} .
    by apply env_preserve_trans with E_zero_hi; trivial => {HEzerohiElo} .
  - exact : mk_env_shl_rec_preserve .
Qed .

Lemma mk_env_shl_int_sat E g ls n E' g' cs lrs :
  mk_env_shl_int E g ls n = (E', g', cs, lrs) ->
  newer_than_lits g ls ->
  interp_cnf E' cs .
Proof .
  move: E' g' cs lrs. eapply mk_env_shl_int_ind.
  - clear n. move=> n Hn E' g' cs lrs [] ? ? ? ?; subst => /=. done.
  - clear n. move=> n [] p Hn //=. move=> _ IH E_m g_m cs_m ls_m Henv.
    move=> E1 g1 cs1 ls1 [] ? ? ? ?; subst. move=> E' g' cs lrs [] ? ? ? ?; subst.
    move=> Hgls. rewrite interp_cnf_catrev.
    by rewrite (IH _ _ _ _ Henv Hgls) /=.
Qed .

Lemma mk_env_shl_rec_sat E g ls ns i E' g' cs lrs :
    mk_env_shl_rec E g ls ns i = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls -> newer_than_lits g ns ->
    interp_cnf E' cs .
Proof .
  elim : ns E' g' cs lrs i => [|ns_hd ns_tl IH] E' g' cs lrs i .
  - rewrite /mk_env_shl_rec /= .
    by case => <- _ <- _ .
  - rewrite /mk_env_shl_rec /= -/mk_env_shl_rec .
    dcase (mk_env_shl_rec E g ls ns_tl (i*2)) => [[[[E_tl g_tl] cs_tl] ls_tl] Hrec] .
    dcase (mk_env_shl_int E_tl g_tl ls_tl i) => [[[[E_hd g_hd] cs_hd] ls_hd] Hint] .
    dcase (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl) => [[[[E_ite g_ite] cs_ite] ls_ite] Hite] .
    move => Htmp Hgtt Hgls /andP [Hgnshd Hgnstl] .
    move : Htmp .
    move : (mk_env_shl_rec_newer_gen Hrec) => Hggtl .
    move : (mk_env_shl_int_newer_gen Hint) => Hgtlghd .
    move : (IH _ _ _ _ _ Hrec Hgtt Hgls Hgnstl) => HEtlcstl .
    move : (mk_env_shl_rec_newer_res Hgtt Hgls Hgnstl Hrec) => Hgtllstl .
    move : (mk_env_shl_int_newer_res (newer_than_lit_le_newer Hgtt Hggtl) Hgtllstl Hint) => Hghdlshd .
    move : (mk_env_shl_int_sat Hint Hgtllstl) => HEhdcshd .
    move : (mk_env_shl_int_preserve Hint) => HEtlEhd .
    move : (mk_env_ite_preserve Hite) => HEhdEite .
    move : (mk_env_shl_rec_newer_cnf Hrec Hgtt Hgls Hgnstl) => Hgtlcstl .
    move : (mk_env_shl_int_newer_cnf Hint Hgtllstl) => Hghdcshd .
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

Lemma mk_env_shl_sat E g ls ns E' g' cs lrs :
  mk_env_shl E g ls ns = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g ns ->
  interp_cnf E' cs.
Proof .
  move => Henv Hgtt Hgls Hgns .
  move : Henv; rewrite /mk_env_shl .
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
    dcase (mk_env_const E_zero_hi g_zero_hi (from_nat (size ls) 0)) =>
    [[[[E_zero] g_zero cs_zero] zero]] Hzero .
    move : (mk_env_const_sat Hzero)
           (mk_env_const_newer_res Hzero Hgzerohitt)
           (mk_env_const_newer_cnf Hzero Hgzerohitt)
           (mk_env_const_preserve Hzero)
           (mk_env_const_newer_gen Hzero)
    => Hzerosat Hgzerozero Hgzerocszero HEzerohiEzero Hgzerohigzero .
    move : (newer_than_lit_le_newer Hgzerohitt (mk_env_const_newer_gen Hzero))
           (newer_than_lits_le_newer Hgzerohils (mk_env_const_newer_gen Hzero))
           (newer_than_lits_le_newer Hgzerohins (mk_env_const_newer_gen Hzero))
           (newer_than_lits_le_newer Hgzerohizerohi (mk_env_const_newer_gen Hzero))
    => {Hgzerohitt Hgzerohils Hgzerohins Hzero Hgzerohizerohi}
         Hgzerott Hgzerols Hgzerons Hgzerozerohi .
    dcase (mk_env_extract E_zero g_zero (size ns).-1 log2szls ns) =>
    [[[[E_hi] g_hi cs_hi] ns_hi]] Hhi .
    move : (mk_env_extract_sat Hhi Hgzerott Hgzerons)
           (mk_env_extract_newer_res Hhi Hgzerott Hgzerons)
           (mk_env_extract_newer_cnf Hhi Hgzerott Hgzerons)
           (mk_env_extract_preserve Hhi)
           (mk_env_extract_newer_gen Hhi)
    => Hhisat Hghinshi Hghicshi HEzeroEhi Hgzeroghi .
    move : (newer_than_lit_le_newer Hgzerott (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgzerols (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgzerons (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgzerozerohi (mk_env_extract_newer_gen Hhi))
           (newer_than_lits_le_newer Hgzerozero (mk_env_extract_newer_gen Hhi))
    => {Hgzerott Hgzerols Hgzerons Hgzerozerohi Hgzerozero Hhi}
         Hghitt Hghils Hghins Hghizerohi Hghizero .
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
           (newer_than_lits_le_newer Hghizero (mk_env_extract_newer_gen Hlo))
    => {Hghitt Hghils Hghins Hghinshi Hlo Hghizerohi Hghizero}
         Hglott Hglols Hglons Hglonshi Hglozerohi Hglozero .
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
           (newer_than_lits_le_newer Hglozero (mk_env_eq_newer_gen Heq))
    => {Hglott Hglols Hglons Hglonslo Heq Hglozero}
         Hgeqtt Hgeqls Hgeqns Hgeqnslo Hgeqzero .
    dcase (mk_env_shl_rec E_eq g_eq ls ns_lo 1) =>
    [[[[E_shl] g_shl cs_shl] ls_shl]] Hshl .
    move : (mk_env_shl_rec_sat Hshl Hgeqtt Hgeqls Hgeqnslo)
           (mk_env_shl_rec_newer_res Hgeqtt Hgeqls Hgeqnslo Hshl)
           (mk_env_shl_rec_newer_cnf Hshl Hgeqtt Hgeqls Hgeqnslo)
           (mk_env_shl_rec_preserve Hshl)
           (mk_env_shl_rec_newer_gen Hshl) 
    => {Hgeqnslo} Hshlsat Hgshllsshl Hgshlcsshl HEeqEshl Hgeqgshl .
    move : (newer_than_lit_le_newer Hgeqtt (mk_env_shl_rec_newer_gen Hshl))
           (newer_than_lit_le_newer Hgeqleq (mk_env_shl_rec_newer_gen Hshl))
           (newer_than_lits_le_newer Hgeqls (mk_env_shl_rec_newer_gen Hshl))
           (newer_than_lits_le_newer Hgeqns (mk_env_shl_rec_newer_gen Hshl))
           (newer_than_lits_le_newer Hgeqzero (mk_env_shl_rec_newer_gen Hshl))
    => {Hgeqtt Hgeqleq Hgeqls Hgeqns Hshl Hgeqzero}
         Hgshltt Hgshlleq Hgshlls Hgshlns Hgshlzero .
    dcase (mk_env_ite E_shl g_shl l_eq ls_shl zero) =>
    [[[[E_ite] g_ite cs_ite] ls_ite]] Hite .
    move : (mk_env_ite_sat Hite Hgshltt Hgshlleq Hgshllsshl Hgshlzero)
           (mk_env_ite_preserve Hite)
    => {Hite Hgshlls Hgshlns Hgshltt Hgshlleq Hgshllsshl Hgshlzero}
         Hitesat HEshlEite .
    case => <- _ <- _ {ls_shl ls_ite l_eq Hgtt Hgls Hgns} .
    rewrite !interp_cnf_catrev .
    rewrite Hitesat {Hitesat cs_ite g_ite} .
    rewrite (env_preserve_cnf HEshlEite Hgshlcsshl) Hshlsat {Hshlsat} .
    move : (env_preserve_trans HEeqEshl
                               (env_preserve_le HEshlEite Hgeqgshl))
    => {HEeqEshl HEshlEite Hgeqgshl Hgshlcsshl cs_shl g_shl} HEeqEite .
    rewrite (env_preserve_cnf HEeqEite Hgeqcseq) Heqsat
            {Heqsat Hgeqcseq cs_eq} .
    move : (env_preserve_trans HEloEeq (env_preserve_le HEeqEite Hglogeq))
    => {HEloEeq HEeqEite Hglogeq E_eq E_shl g_eq} HEloEite .
    rewrite (env_preserve_cnf HEloEite Hglocslo) Hlosat
            {Hlosat Hglocslo cs_lo ns_lo} .
    move : (env_preserve_trans HEhiElo (env_preserve_le HEloEite Hghiglo))
    => {HEhiElo HEloEite Hghiglo E_lo g_lo} HEhiEite .
    rewrite (env_preserve_cnf HEhiEite Hghicshi) Hhisat
            {Hhisat Hghicshi cs_hi ns_hi} .
    move : (env_preserve_trans HEzeroEhi (env_preserve_le HEhiEite Hgzeroghi))
    => {HEzeroEhi HEhiEite Hgzeroghi E_hi g_hi} HEzeroEite .
    rewrite (env_preserve_cnf HEzeroEite Hgzerocszero) Hzerosat
            {Hzerosat Hgzerocszero cs_zero} .
    move : (env_preserve_trans HEzerohiEzero
                               (env_preserve_le HEzeroEite Hgzerohigzero))
    => {HEzerohiEzero HEzeroEite Hgzerohigzero E_zero g_zero} HEzerohiEite .
    by rewrite (env_preserve_cnf HEzerohiEite Hgzerohicszerohi) Hzerohisat .
  - move => Henv .
    exact : (mk_env_shl_rec_sat Henv Hgtt Hgls Hgns) .
Qed .
