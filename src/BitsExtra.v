
(* DO NOT MODIFY THIS FILE *)
(* This file is copied from certified_qhasm_vcg. *)

From Coq Require Import OrderedType ZArith String.
From mathcomp Require Import ssreflect ssrbool ssrnat ssralg ssrfun.
From mathcomp Require Import eqtype div zmodp.
From mathcomp Require Export tuple seq.
From Bits Require Import bits.
From ssrlib Require Import Nats ZAriths Seqs Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Close Scope bits_scope.

Notation "x + y" := (addB x y) : bits_scope.
Notation "x - y" := (subB x y) : bits_scope.
Notation "x * y" := (mulB x y) : bits_scope.
Notation "x < y" := (ltB x y) : bits_scope.
Notation "x <= y" := (leB x y) : bits_scope.



Ltac eq_add_posz H :=
  match type of H with
  | ?x = ?y => have: (toPosZ x = toPosZ y); [by rewrite H | move=> {H} H]
  end.

(** Constants *)

Inductive nstring (n : nat) : Set :=
| NString : forall s : string, String.length s = n -> nstring n.

Notation "n .-string" := (nstring n) (at level 4, format "n .-string") : type_scope.

Definition fromNString (n : nat) (s : n.-string) : BITS (n * 4).
Proof.
  destruct s as [s Hlen].
  rewrite -Hlen.
  exact: (fromHex s).
Defined.



(** Lemmas *)

Section BitsLemmas.

  Set Implicit Arguments.

  Lemma ltBnn : forall (n : nat) (x : BITS n), ltB x x = false.
  Proof.
    move=> n x.
    rewrite ltB_nat.
    apply: ltnn.
  Qed.

  Ltac have_incB_m n :=
    let m := fresh n "_dec" in
    let H := fresh in
    set m := decB n;
    have H : n = incB m; [by rewrite (decBK n) | ].

  Ltac have_incB_b n :=
    let m := fresh n "_dec" in
    let H := fresh in
    set m := decB n;
    have H : n == incB m; [by rewrite (decBK n) | ].

  Ltac have_decB_m n :=
    let m := fresh n "_inc" in
    let H := fresh in
    set m := incB n;
    have H : n = decB m; [by rewrite (incBK n) | ].

  Ltac have_decB_b n :=
    let m := fresh n "_inc" in
    let H := fresh in
    set m := incB n;
    have H : n == decB m; [by rewrite (incBK n) | ].

  Inductive bounded_nat (n : nat) : nat -> Set :=
  | BoundedNat : forall m : nat, (m < n) -> bounded_nat n m.

  Lemma bits_bounded : forall (n : nat) (x : BITS n), bounded_nat (2^n) (toNat x).
  Proof.
    move=> n x.
    apply: BoundedNat.
    exact: (toNatBounded x).
  Qed.

  Lemma bits_rect :
    forall (n : nat) (P : BITS n -> Type),
      P (zero n) ->
      (forall x : BITS n, P x -> P (incB x)) ->
      forall x : BITS n, P x.
  Proof.
    move=> n P Hbase Hind x.
    move: (bits_bounded x) => Hbounded.
    rewrite -(toNatK x).
    induction Hbounded.
    elim: m i.
    - move=> Hlt.
      rewrite fromNat0.
      exact: Hbase.
    - move=> m IHm Hlt.
      rewrite -incB_fromNat.
      apply: Hind.
      apply: IHm.
      exact: (ltnW Hlt).
  Qed.

  Lemma bits_ind :
    forall (n : nat) (P : BITS n -> Prop),
      P (zero n) ->
      (forall x : BITS n, P x -> P (incB x)) ->
      forall x : BITS n, P x.
  Proof.
    exact: bits_rect.
  Qed.

  Lemma bits_rec :
    forall (n : nat) (P : BITS n -> Set),
      P (zero n) ->
      (forall x : BITS n, P x -> P (incB x)) ->
      forall x : BITS n, P x.
  Proof.
    exact: bits_rect.
  Qed.

  Lemma behead_tuple_zero : forall n : nat, behead_tuple (zero n.+1) == zero n.
  Proof.
    move=> n.
    exact: eqxx.
  Qed.

  Lemma behead_tuple_fromNat0 : forall n : nat, behead_tuple (n:=n.+1) #0 == #0.
  Proof.
    move=> n.
    exact: eqxx.
  Qed.

  Lemma thead_zero : forall n : nat, thead (zero n.+1) == false.
  Proof.
    move=> n.
    exact: eqxx.
  Qed.

  Lemma thead_fromNat0 : forall n : nat, thead (n:=n.+1) #0 == false.
  Proof.
    move=> n.
    exact: eqxx.
  Qed.

  Lemma behead_tuple_ones : forall n : nat, behead_tuple (ones n.+1) == ones n.
  Proof.
    move=>n.
    apply: eqxx.
  Qed.

  Lemma thead_ones : forall n : nat, thead (ones n.+1) == true.
  Proof.
    move=> n.
    exact: eqxx.
  Qed.

  Lemma bits_ne0_toNat_gt0 :
    forall (n : nat) (x : BITS n), (x != #0) == (0 < toNat x).
  Proof.
    move=> n x.
    rewrite -{1}(toNatK x).
    set m := toNat x.
    have nat_eq0_gt0: forall n : nat, (n == 0) || (n > 0) by move=> i; elim: i.
    case: (orP (nat_eq0_gt0 m)) => {nat_eq0_gt0} Hm.
    - rewrite (eqP Hm) => {x m Hm}.
      rewrite ltnn.
      apply/eqP/negPf/negPf.
      exact: eqxx.
    - rewrite Hm.
      apply/eqP/negP.
      rewrite -fromNatBounded_eq.
      + move=> Heq.
        rewrite (eqP Heq) in Hm.
        done.
      + exact: toNatBounded.
      + rewrite expn_gt0.
        apply/orP; by left.
  Qed.

  Lemma toNatBounded_leq n (p : BITS n) :
    toNat p <= 2^n - 1.
  Proof.
    move: (toNatBounded p). exact: ltn_leq_sub.
  Qed.

  Lemma Zof_nat_toNat_bounded (n : nat) (p : BITS n) :
    (0 <= Z.of_nat (toNat p) < 2 ^ Z.of_nat n)%Z.
  Proof.
    split.
    - exact: Nat2Z.is_nonneg.
    - replace 2%Z with (Z.of_nat 2%N) by reflexivity.
      rewrite -Nat2Z_inj_pow.
      apply: (proj1 (Nat2Z.inj_lt (toNat p) (Nat.pow 2 n))).
      rewrite -expn_pow. apply/ltP. exact: toNatBounded.
  Qed.

  Lemma fromNatK w n : n < 2^w -> toNat (@fromNat w n) = n.
  Proof.
    move=> Hn; rewrite toNat_fromNat (modn_small Hn). reflexivity.
  Qed.

  Lemma eta_expand_eq (A B : Type) (x : A * B) : eta_expand x = x.
  Proof.
    destruct x as [a b]; reflexivity.
  Qed.

  Lemma msb_nil : msb nilB = false.
  Proof.
    reflexivity.
  Qed.

  Lemma msb_fromNat_nonnil n m :
    msb (@fromNat (n.+1) m) = odd (m %/ 2^n).
  Proof.
    rewrite -splitmsb_msb splitmsb_fromNat. reflexivity.
  Qed.

  Lemma msb_fromNat n m :
    m < 2^n ->
    msb (@fromNat n m) = odd (m %/ 2^(n.-1)).
  Proof.
    case: n => /=.
    - rewrite /fromNat expn0 divn1 /=. move/ltP=> H.
      rewrite (proj1 (Nat.lt_1_r m) H) /=. reflexivity.
    - move=> n _; exact: msb_fromNat_nonnil.
  Qed.

  Lemma msb_toNat_nonnil n (p : BITS (n.+1)) :
    msb p = odd (toNat p %/ 2^n).
  Proof.
    rewrite -{1}(toNatK p) msb_fromNat_nonnil. reflexivity.
  Qed.

  Lemma msb_toNat n (p : BITS n) :
    msb p = odd (toNat p %/ 2^(n.-1)).
  Proof.
    rewrite -{1}(toNatK p) (msb_fromNat (toNatBounded p)). reflexivity.
  Qed.

  Lemma catB_consB n1 n2 (p1 : BITS n1) b (p2 : BITS n2) :
    catB p1 (consB b p2) = consB b (catB p1 p2).
  Proof.
    rewrite /catB /consB. apply: val_inj => /=. reflexivity.
  Qed.

  Lemma catB_nilBr n (p : BITS n) :
    catB p nilB = p.
  Proof.
    by apply: val_inj.
  Qed.

  Lemma catB_high_low n1 n2 (p : BITS (n2 + n1)) :
    p = catB (high n1 p) (low n2 p).
  Proof.
    exact: (split2eta p).
  Qed.

  Lemma singleBit_fromNat (b : bool) :
    singleBit b = fromNat b.
  Proof.
    rewrite /fromNat /singleBit. rewrite oddb. reflexivity.
  Qed.

  Lemma catB_eucl n1 n2 (p1 : BITS n1) (p2 : BITS n2) q r :
    (q, r) = Z.div_eucl (Z.of_nat (toNat (p1 ## p2))) (2 ^ Z.of_nat n2) ->
    q = Z.of_nat (toNat p1) /\ r = Z.of_nat (toNat p2).
  Proof.
    rewrite toNatCat Nat2Z.inj_add Nat2Z.inj_mul expn_pow Nat2Z_inj_pow /=.
    move=> H. split.
    - rewrite (Zdiv_eucl_q H).
      rewrite (Z_div_plus_full_l _ _ _ (@two_power_of_nat_ne0 n2)).
      rewrite (Z.div_small _ _ (Zof_nat_toNat_bounded p2)).
      rewrite Z.add_0_r. reflexivity.
    - rewrite (Zdiv_eucl_r H).
      rewrite Z.add_comm Z_mod_plus_full
              (Z.mod_small _ _ (Zof_nat_toNat_bounded p2)).
      reflexivity.
  Qed.

  Lemma catB_eucl_high n1 n2 (p1 : BITS n1) (p2 : BITS n2) q r :
    (q, r) = Z.div_eucl (Z.of_nat (toNat (p1 ## p2))) (2 ^ Z.of_nat n2) ->
    q = Z.of_nat (toNat p1).
  Proof.
    move=> H. exact: (proj1 (catB_eucl H)).
  Qed.

  Lemma catB_eucl_low n1 n2 (p1 : BITS n1) (p2 : BITS n2) q r :
    (q, r) = Z.div_eucl (Z.of_nat (toNat (p1 ## p2))) (2 ^ Z.of_nat n2) ->
    r = Z.of_nat (toNat p2).
  Proof.
    move=> H. exact: (proj2 (catB_eucl H)).
  Qed.

  Lemma toNat_eucl n1 n2 (p : BITS (n2 + n1)) q r :
    (q, r) = Z.div_eucl (Z.of_nat (toNat p)) (2 ^ Z.of_nat n2) ->
    q = Z.of_nat (toNat (high n1 p)) /\ r = Z.of_nat (toNat (low n2 p)).
  Proof.
    rewrite {1}(catB_high_low p). exact: catB_eucl.
  Qed.

  Lemma toNat_eucl_high n1 n2 (p : BITS (n2 + n1)) q r :
    (q, r) = Z.div_eucl (Z.of_nat (toNat p)) (2 ^ Z.of_nat n2) ->
    q = Z.of_nat (toNat (high n1 p)).
  Proof.
    rewrite {1}(catB_high_low p). exact: catB_eucl_high.
  Qed.

  Lemma toNat_eucl_low n1 n2 (p : BITS (n2 + n1)) q r :
    (q, r) = Z.div_eucl (Z.of_nat (toNat p)) (2 ^ Z.of_nat n2) ->
    r = Z.of_nat (toNat (low n2 p)).
  Proof.
    rewrite {1}(catB_high_low p). exact: catB_eucl_low.
  Qed.

  Lemma high1_msb n (p : BITS (n + 1)%N) : high 1 p = singleBit (msb p).
  Proof.
    rewrite /msb. elim: n p => /=.
    - move=> p. destruct p; apply: val_inj => /=.
      rewrite add0n in i. move/eqP: i => i.
      move: (singleton_seq i) => [b Hb]. rewrite Hb; reflexivity.
    - move=> n IH; case/tupleP => /=. rewrite -/addn.
      move=> b p. rewrite tuple.beheadCons IH. destruct p => /=.
      rewrite (@last_default_irrelevant _ tval _ false b (eqP i)).
      reflexivity.
  Qed.

  Lemma toNat_splitmsb1 n (p : BITS (n.+1)) :
    (splitmsb p).1 = odd (toNat p %/ 2^n).
  Proof.
    rewrite splitmsb_msb. exact: msb_toNat_nonnil.
  Qed.

  Lemma toNat_splitmsb2 n (p : BITS (n.+1)) :
    toNat (splitmsb p).2 = toNat p %% 2^n.
  Proof.
    rewrite -{1}(toNatK p) splitmsb_fromNat /= toNat_fromNat.
    reflexivity.
  Qed.

  Lemma zeroExtend_catB n1 n2 (p : BITS n1) :
    zeroExtend n2 p = (zero n2) ## p.
  Proof.
    apply: toNat_inj. rewrite toNat_zeroExtend. reflexivity.
  Qed.

  Lemma low_zeroExtend n1 n2 (p : BITS n1) :
    low n1 (zeroExtend n2 p) = p.
  Proof.
    apply: toNat_inj. rewrite toNat_low toNat_zeroExtend -toNat_mod.
    reflexivity.
  Qed.

  Lemma high_zeroExtend n1 n2 (p : BITS n1) :
    high n2 (zeroExtend n2 p) = zero n2.
  Proof.
    rewrite zeroExtend_catB high_catB. reflexivity.
  Qed.

  Lemma toNat_high n1 n2 (p : BITS (n1 + n2)) :
    toNat (high n2 p) = (toNat p) %/ (2 ^ n1).
  Proof.
    have: (toNat p = toNat (high n2 p ## low n1 p)) by
        rewrite -(catB_high_low p). rewrite toNatCat => H.
    have: (toNat p) %/ (2 ^ n1) =
          (toNat (high n2 p) * 2 ^ n1 + toNat (low n1 p)) %/ (2 ^ n1)
      by rewrite -H. rewrite (divnMDl _ _ (expn2_gt0 n1)).
    rewrite (@divn_small (toNat (low n1 p))).
    - rewrite addn0 => ->; reflexivity.
    - exact: toNatBounded.
  Qed.

  Lemma width1_case (p : BITS 1) : p = singleBit false \/ p = singleBit true.
  Proof.
    destruct p. case: tval i.
    - done.
    - move=> b [].
      + case: b.
        * right. apply: val_inj => /=. reflexivity.
        * left. apply: val_inj => /=. reflexivity.
      + done.
  Qed.

  Lemma ltB_width1 (p1 p2 : BITS 1) :
    ltB p1 p2 ->
    p1 = singleBit false /\ p2 = singleBit true.
  Proof.
    case: (width1_case p1); case: (width1_case p2) => -> ->; done.
  Qed.

  Lemma ltB_width_gt0 n (p1 p2 : BITS n) : ltB p1 p2 -> (0 < n)%N.
  Proof.
    by case: n p1 p2.
  Qed.



  (* Operations *)

  Lemma carry_addB_nil (p1 p2 : BITS 0) :
    carry_addB p1 p2 = false.
  Proof.
    reflexivity.
  Qed.

  Lemma carry_addB_bounded n (p1 p2 : BITS n) :
    carry_addB p1 p2 < 2^n.
  Proof.
    case: n p1 p2.
    - done.
    - move=> n p1 p2.
      case: (carry_addB p1 p2) => /=.
      + exact: ltn_1_2expnS.
      + by rewrite expn_gt0.
  Qed.

  Lemma carry_addB_toNatn_toNat1 n (p1 p2 : BITS n) :
    @toNat n # (carry_addB p1 p2) = @toNat 1 # (carry_addB p1 p2).
  Proof.
    case: n p1 p2.
    - move=> p1 p2. reflexivity.
    - move=> n p1 p2.
      case: (carry_addB p1 p2) => /=.
      + rewrite fromNatK; first by reflexivity. exact: ltn_1_2expnS.
      + rewrite fromNatK; first by reflexivity. by rewrite expn_gt0.
  Qed.

  Lemma adcBmain_addB n (p1 p2 : BITS n) :
    adcBmain false p1 p2 = joinmsb (carry_addB p1 p2, addB p1 p2).
  Proof.
    Transparent adcB. rewrite /adcB eta_expand_eq splitmsbK. reflexivity.
  Qed.

  Lemma toNat_addn_bounded n (p1 p2 : BITS n) :
    toNat p1 + toNat p2 < 2^n.+1.
  Proof.
    move: (ltn_addn (toNatBounded p1) (toNatBounded p2)).
    rewrite addnn -mul2n -expnS. by apply.
  Qed.

  Lemma toNat_addn_ltn_two_power n (p1 p2 : BITS n.+1) :
    toNat p1 + toNat p2 < 2 ^ (n.+1 + n.+1).
  Proof.
    apply: (ltn_leq_trans (toNat_addn_bounded p1 p2)).
    rewrite (@leq_exp2l 2 _ _ is_true_true).
    rewrite -{1}(add0n (n.+1)) ltn_add2r. done.
  Qed.

  Lemma carry_addB_odd n (p1 p2 : BITS n) :
    nat_of_bool (carry_addB p1 p2) = odd ((toNat p1 + toNat p2) %/ 2^n).
  Proof.
    rewrite /adcB toNat_splitmsb1 toNat_adcBmain add0n.
    reflexivity.
  Qed.

  Lemma carry_addB_divn n (p1 p2 : BITS n) :
    nat_of_bool (carry_addB p1 p2) = (toNat p1 + toNat p2) %/ 2^n.
  Proof.
    rewrite carry_addB_odd odd_divn; first reflexivity.
    rewrite -mul2n -expnS. exact: toNat_addn_bounded.
  Qed.

  Lemma toNat_addB_bounded :
    forall (n : nat) (x y : BITS n),
      ~~ carry_addB x y ->
      toNat (addB x y) = (toNat x + toNat y).
  Proof.
    move=> n x y. rewrite /adcB -(toNat_adcBmain false x y)
                  -{3}(splitmsbK (adcBmain false x y)).
    case: (splitmsb (adcBmain false x y)). move=> carry p.
    case: carry => //=. rewrite toNat_joinmsb => _.
    reflexivity.
  Qed.

  Lemma toNat_addB_zeroExtend1 n (p1 p2 : BITS n) :
    toNat (addB (zeroExtend 1 p1) (zeroExtend 1 p2)) = toNat p1 + toNat p2.
  Proof.
    rewrite toNat_addB !toNat_zeroExtend modn_small.
    - reflexivity.
    - rewrite addn1. exact: (toNat_addn_bounded p1 p2).
  Qed.

  Lemma toNat_addB_zeroExtend n (p1 p2 : BITS n) :
    toNat (addB (zeroExtend n p1) (zeroExtend n p2)) = toNat p1 + toNat p2.
  Proof.
    case: n p1 p2.
    - move=> p1 p2. rewrite toNat_addB !toNat_zeroExtend modn_small;
      first reflexivity. rewrite !toNatNil. done.
    - move=> n p1 p2. rewrite toNat_addB !toNat_zeroExtend modn_small;
                        first reflexivity. exact: toNat_addn_ltn_two_power.
  Qed.

  Lemma low_addB_distr n1 n2 (p1 p2 : BITS (n1 + n2)) :
    low n1 (addB p1 p2) = addB (low n1 p1) (low n1 p2).
  Proof.
    apply: toNat_inj. rewrite toNat_low toNat_addB expnD modn_muln_modn_l.
    rewrite toNat_addB 2!toNat_low modnDm. reflexivity.
  Qed.

  Lemma addB_zeroExtend1_catB n (p1 p2 : BITS n) :
    addB (zeroExtend 1 p1) (zeroExtend 1 p2) =
    (fromNat (carry_addB p1 p2)) ## (addB p1 p2).
  Proof.
    apply: toNat_inj. rewrite toNat_addB_zeroExtend1.
    rewrite toNatCat. have Hc: carry_addB p1 p2 < 2 ^ 1.
    { by case: (carry_addB p1 p2). }
    rewrite (fromNatK Hc) => {Hc}. rewrite /adcB adcBmain_nat /= add0n.
    rewrite splitmsb_fromNat /=. rewrite toNat_fromNat.
    apply: odd_divn_eucl. rewrite -mul2n -expnS.
    exact: toNat_addn_bounded.
  Qed.

  Lemma addB_zeroExtend_catB n (p1 p2 : BITS n) :
    addB (zeroExtend n p1) (zeroExtend n p2) =
    (fromNat (carry_addB p1 p2)) ## (addB p1 p2).
  Proof.
    apply: toNat_inj. rewrite toNat_addB_zeroExtend.
    rewrite toNatCat. have Hc: carry_addB p1 p2 < 2 ^ n.
    { case: n p1 p2.
      - done.
      - move=> n p1 p2. apply: (@leq_ltn_trans 1).
        + by case: (carry_addB p1 p2).
        + exact: ltn_1_2expnS. }
    rewrite (fromNatK Hc) => {Hc}. rewrite /adcB adcBmain_nat /= add0n.
    rewrite splitmsb_fromNat /=. rewrite toNat_fromNat.
    apply: odd_divn_eucl. rewrite -mul2n -expnS.
    exact: toNat_addn_bounded.
  Qed.

  Lemma addB_zeroExtend1_high n (p1 p2 : BITS n) :
    high 1 (addB (zeroExtend 1 p1) (zeroExtend 1 p2)) =
    singleBit (carry_addB p1 p2).
  Proof.
    rewrite addB_zeroExtend1_catB high_catB /=. rewrite singleBit_fromNat.
    reflexivity.
  Qed.

  Lemma addB_zeroExtend1_high_ext n (p1 p2 : BITS n) :
    zeroExtend (n - 1) (high 1 (addB (zeroExtend 1 p1) (zeroExtend 1 p2))) =
    (fromNat (carry_addB p1 p2)).
  Proof.
    rewrite addB_zeroExtend1_high.
    apply: toNat_inj. rewrite toNat_zeroExtend.
    case: (carry_addB p1 p2).
    - rewrite fromNatK; first by reflexivity.
      exact: ltn_1_2expnS.
    - rewrite fromNatK; first by reflexivity.
      by rewrite expn_gt0.
  Qed.

  Lemma addB_zeroExtend_high n (p1 p2 : BITS n) :
    high n (addB (zeroExtend n p1) (zeroExtend n p2)) =
    fromNat (carry_addB p1 p2).
  Proof.
    rewrite addB_zeroExtend_catB high_catB.
    reflexivity.
  Qed.

  Lemma addB_zeroExtend1_low n (p1 p2 : BITS n) :
    low n (addB (zeroExtend 1 p1) (zeroExtend 1 p2)) =
    addB p1 p2.
  Proof.
    rewrite addB_zeroExtend1_catB low_catB. reflexivity.
  Qed.

  Lemma addB_zeroExtend_low n (p1 p2 : BITS n) :
    low n (addB (zeroExtend n p1) (zeroExtend n p2)) =
    addB p1 p2.
  Proof.
    rewrite addB_zeroExtend_catB low_catB. reflexivity.
  Qed.

  Lemma addB3_zeroExtend_low n (p1 p2 p3 : BITS n) :
    low n (addB (addB (zeroExtend n p1) (zeroExtend n p2)) (zeroExtend n p3)) =
    addB (addB p1 p2) p3.
  Proof.
    rewrite 2!low_addB_distr. rewrite 3!low_zeroExtend. reflexivity.
  Qed.

  Lemma toNat_addB_zeroExtend_bounded n (p1 p2 : BITS n) :
    high n (addB (zeroExtend n p1) (zeroExtend n p2)) = zero n ->
    toNat (low n (addB (zeroExtend n p1) (zeroExtend n p2))) =
    toNat p1 + toNat p2.
  Proof.
    rewrite addB_zeroExtend_low. case: n p1 p2.
    - move=> p1 p2 Hc. rewrite !toNatNil. reflexivity.
    - move=> n p1 p2. rewrite addB_zeroExtend_high.
      case Hc: (carry_addB p1 p2) => /=.
      + move=> H0; have: toNat (@fromNat n.+1 1) = toNat (zero n.+1)
                 by rewrite H0. rewrite fromNatK.
        * rewrite toNat_zero. discriminate.
        * done.
      + move=> _. move/negP/idP: Hc => Hc. exact: (toNat_addB_bounded Hc).
  Qed.

  Lemma toNat_addB3_zeroExtend_bounded n (p1 p2 p3 : BITS n) :
    ~~ carry_addB p1 p2 ->
    ~~ carry_addB (addB p1 p2) p3 ->
    toNat (low n (addB (addB (zeroExtend n p1) (zeroExtend n p2)) (zeroExtend n p3))) = toNat p1 + toNat p2 + toNat p3.
  Proof.
    move=> H1 H2. rewrite addB3_zeroExtend_low. rewrite (toNat_addB_bounded H2).
    rewrite (toNat_addB_bounded H1). reflexivity.
  Qed.

  Lemma toNat_addB3_bounded n (p1 p2 p3 : BITS n) :
    ~~ carry_addB p1 p2 ->
    ~~ carry_addB (addB p1 p2) p3 ->
    toNat (addB (addB p1 p2) p3) = toNat p1 + toNat p2 + toNat p3.
  Proof.
    move=> H1 H2. rewrite (toNat_addB_bounded H2) (toNat_addB_bounded H1).
    reflexivity.
  Qed.

  Lemma toNat_addn3_bounded_lt (n : nat) :
    3 * (2^n - 1) < 4^n.
  Proof.
    elim: n.
    - done.
    - move=> n IH. rewrite !expnS.
      have: 3 * (2 * 2 ^ n - 1) = 2 * 3 * (2^n - 1) + 3.
      { rewrite 2!mulnBr. change (3 * 1) with 3. rewrite mulnA.
        change (3 * 2) with 6. change (2 * 3) with 6. change (6 * 1) with 6.
        rewrite addnC addnBA.
        - rewrite addnC -subnBA; last by done. change (6 - 3) with 3.
          reflexivity.
        - rewrite -{1}(muln1 5). apply: ltn_leq_mul_ltn.
          + done.
          + done.
          + rewrite expn_gt0. done. }
      move=> ->. move: (ltn_leq_sub IH) => {IH} H.
      move: (leq_mul2l 2 (3 * (2^n - 1)) (4^n - 1)). rewrite H /= => {H} H.
      rewrite -(leq_add2r 3) mulnA in H. apply: (leq_ltn_trans H).
      rewrite mulnBr. change (2 * 1) with 2.
      have H1: 1 < 2 * 4 ^ n.
      { rewrite -{1}(muln1 1). apply: ltn_leq_mul_ltn.
        - done.
        - done.
        - rewrite expn_gt0. done. }
      rewrite addnC (addnBA _ H1) => {H1}. have H1: 1 < 3 by done.
      rewrite -addnC -(addnBA _ H1) => {H1}. change (3 - 2) with 1.
      change 4 with (2 + 2) at 2. rewrite mulnDl ltn_add2l.
      change 1 with (1 * 1) at 1. apply: ltn_leq_mul_ltn.
      + done.
      + done.
      + rewrite expn_gt0. done.
  Qed.

  Lemma toNat_addn3_ltn_two_power n (p1 p2 p3 : BITS n.+1) :
    toNat p1 + toNat p2 + toNat p3 < 2 ^ (n.+1 + n.+1).
  Proof.
    rewrite addnn -mul2n expnM.
    change (2^2) with 4.
    apply: (leq_ltn_trans _ (toNat_addn3_bounded_lt (n.+1))).
    move: (leq_add (leq_add (toNatBounded_leq p1) (toNatBounded_leq p2)) (toNatBounded_leq p3)).
    have Hlt: 0 < 2 ^ n.+1 by rewrite expn_gt0.
    rewrite 2!(addnBA _ Hlt) (addnC (2^n.+1 - 1) (2^n.+1)) (addnBA _ Hlt).
    rewrite addnn -mul2n -subnDA (addnC _ (2^n.+1)).
    have Hle: 1 + 1 <= 2 * 2 ^ n.+1.
    { change (1+1) with 2. apply: (leq_ltn_trans Hlt).
      rewrite -{1}(mul1n (2^n.+1)) ltn_mul2r Hlt. done. }
    rewrite (addnBA _ Hle) -subnDA -{1}(mul1n (2^n.+1)) -mulnDl.
    change (1+2) with 3. change (1+1+1) with 3. rewrite -{2}(muln1 3) -mulnBr.
    done.
  Qed.

  Lemma toNat_addB3_zeroExtend n (p1 p2 p3 : BITS n) :
    toNat (addB (addB (zeroExtend n p1) (zeroExtend n p2)) (zeroExtend n p3)) =
    toNat p1 + toNat p2 + toNat p3.
  Proof.
    case: n p1 p2 p3.
    - move=> p1 p2 p3. rewrite !toNat_addB !toNat_zeroExtend !modn_small;
                         first reflexivity; by rewrite !toNatNil.
    - move=> n p1 p2 p3. rewrite !toNat_addB !toNat_zeroExtend !modn_small;
                           first reflexivity.
      * exact: toNat_addn_ltn_two_power.
      * exact: toNat_addn3_ltn_two_power.
      * exact: toNat_addn_ltn_two_power.
  Qed.

  Lemma toNat_invB_nil (p : BITS 0) : toNat (invB p) = 0%N.
  Proof.
    rewrite toNatNil. reflexivity.
  Qed.

  Lemma toNat_negB_nil (p : BITS 0) : toNat (negB p) = 0%N.
  Proof.
    rewrite toNatNil. reflexivity.
  Qed.

  Lemma carry_subB_nil (p1 p2 : BITS 0) : carry_subB p1 p2 = false.
  Proof.
    reflexivity.
  Qed.

  Lemma carry_subB_leB n (x y : BITS n) : ~~ carry_subB x y -> (y <= x)%bits.
  Proof.
    move: (sbbB_ltB_leB x y). case: (sbbB false x y).
    move=> carry p /=. by case: carry.
  Qed.

  Lemma geB_carry_subB n (p1 p2 : BITS n) :
    leB p2 p1 -> ~~ carry_subB p1 p2.
  Proof.
    Transparent sbbB.
    rewrite leB_nat /sbbB /adcB /= => Hle. apply/negPn.
    rewrite toNat_splitmsb1 toNat_adcBmain toNat_invB /=.
    rewrite -subn1 (addnBA _ (toNatBounded_leq p2)).
    replace (1 + toNat p1 + (2 ^ n - 1)) with
            (1 + (2 ^ n - 1) + toNat p1) by ring.
    rewrite (subnKC (expn2_gt0 n)). rewrite -(addnBA _ Hle).
    replace (2^n) with (1 * 2^n) at 1; last by rewrite mul1n.
    rewrite (divnMDl _ _ (expn2_gt0 n)). rewrite divn_small.
    - done.
    - apply: (@ltn_leq_trans (2^n - toNat p2)).
      + apply: ltn_sub2r; exact: toNatBounded.
      + exact: leq_subr.
  Qed.

  Lemma ltB_carry_subB n (p1 p2 : BITS n) :
    ltB p1 p2 -> carry_subB p1 p2.
  Proof.
    rewrite ltB_nat /sbbB /adcB /= => Hlt.
    rewrite toNat_splitmsb1 toNat_adcBmain toNat_invB /=.
    rewrite -subn1 (addnBA _ (toNatBounded_leq p2)).
    replace (1 + toNat p1 + (2 ^ n - 1)) with
            (1 + (2 ^ n - 1) + toNat p1) by ring.
    rewrite (subnKC (expn2_gt0 n)). rewrite divn_small; first by done.
    apply: (@ltn_leq_trans (2^n + toNat p2 - toNat p2)).
    - apply: ltn_sub2r.
      + apply: ltn_addr. exact: toNatBounded.
      + rewrite ltn_add2l. exact: Hlt.
    - rewrite -(addnBA _ (leqnn (toNat p2))) subnn addn0. exact: leqnn.
  Qed.

  Lemma toNat_subB_bounded n (x y : BITS n) :
    ~~ carry_subB x y ->
    toNat (subB x y) = (toNat x - toNat y).
  Proof.
    move=> H. apply: toNat_subB. by apply: carry_subB_leB.
  Qed.

  Lemma toNat_subB3_bounded n (p1 p2 p3 : BITS n) :
    ~~ carry_subB p1 p2 ->
    ~~ carry_subB (subB p1 p2) p3 ->
    toNat (subB (subB p1 p2) p3) = (toNat p1 - toNat p2 - toNat p3).
  Proof.
    move=> H1 H2. rewrite (toNat_subB_bounded H2) (toNat_subB_bounded H1).
    reflexivity.
  Qed.

  Lemma toNat_high_addB_extn_ext1 n (p1 p2 : BITS n) :
    toNat (high n (addB (zeroExtend n p1) (zeroExtend n p2))) =
    toNat (high 1 (addB (zeroExtend 1 p1) (zeroExtend 1 p2))).
  Proof.
    rewrite addB_zeroExtend_catB addB_zeroExtend1_catB !high_catB.
    exact: carry_addB_toNatn_toNat1.
  Qed.

  Lemma toNat_mulB_zeroExtend n (p1 p2 : BITS n) :
    toNat (mulB (zeroExtend n p1) (zeroExtend n p2)) = toNat p1 * toNat p2.
  Proof.
    rewrite toNat_mulB !toNat_zeroExtend modn_small.
    - reflexivity.
    - rewrite expnD. apply: ltn_mul; exact: toNatBounded.
  Qed.

  Lemma mulB_zeroExtend_fullmulB n (p1 p2 : BITS n) :
    mulB (zeroExtend n p1) (zeroExtend n p2) = fullmulB p1 p2.
  Proof.
    apply: toNat_inj. rewrite toNat_mulB_zeroExtend toNat_fullmulB.
    reflexivity.
  Qed.

  Lemma mulB_zeroExtend_low n (p1 p2 : BITS n) :
    low n (mulB (zeroExtend n p1) (zeroExtend n p2)) = mulB p1 p2.
  Proof.
    rewrite mulB_zeroExtend_fullmulB. reflexivity.
  Qed.

  Lemma toNat_mulB_bounded n (p1 p2 : BITS n) :
    high n (fullmulB p1 p2) = zero n ->
    toNat (mulB p1 p2) = (toNat p1 * toNat p2).
  Proof.
    rewrite -mulB_zeroExtend_fullmulB => H.
    move: (toNatCat (high n (zeroExtend n p1 * zeroExtend n p2))
                    (low n (zeroExtend n p1 * zeroExtend n p2))).
    rewrite -(catB_high_low (zeroExtend n p1 * zeroExtend n p2)) H.
    rewrite toNat_mulB_zeroExtend toNat_zero mul0n add0n. move=> ->.
    rewrite mulB_zeroExtend_low. reflexivity.
  Qed.

  Lemma shlBn_mulB n i (p : BITS n) :
    shlBn p i = mulB p (fromNat (2^i)).
  Proof.
    elim: i n p => /=.
    - move=> n p. rewrite expn0. rewrite mulB1. reflexivity.
    - move=> i IH n p. rewrite shlB_asMul IH. rewrite -mulB_muln.
      rewrite -expnSr. reflexivity.
  Qed.

  Lemma toNat_shlB_bounded n (p : BITS n) :
    (p < shlBn (@fromNat n 1) (n - 1))%bits ->
    toNat (shlB p) = (toNat p * 2).
  Proof.
    case: n p.
    - done.
    - move=> n p. have H: n.+1 - 1 < n.+1.
      { rewrite subn1 succnK. done. }
      rewrite ltB_nat toNat_shlB (toNat_shlBn H). rewrite subn1 succnK.
      rewrite -muln2. move=> {H} H. rewrite modn_small; first by reflexivity.
      rewrite expnSr. apply: ltn_leq_mul_ltn; done.
  Qed.

  Lemma ltn_expn_subn_ltn i n : 0 < i < n -> 2 ^ (n - i) < 2 ^ n.
  Proof.
    move=> /andP [H0i Hin]. rewrite ltn_exp2l; last by done. rewrite -subn_gt0.
    rewrite (subKn (ltnW Hin)). assumption.
  Qed.

  Lemma shlBn0 n (p : BITS n) : shlBn p 0 = p.
  Proof.
    reflexivity.
  Qed.

  Lemma toNat_shlBn_bounded n i (p : BITS n) :
    (p < shlBn (@fromNat n 1) (n - i))%bits ->
    toNat (shlBn p i) = (toNat p * 2 ^ i).
  Proof.
    rewrite !shlBn_mulB. rewrite fromNat_mulBn mul1n.
    case Hi0: (i == 0).
    - rewrite (eqP Hi0) subn0 expn0 muln1 mulB1. reflexivity.
    - move/negP/idP: Hi0 => Hi0. case Hin: (i < n).
      + have Hlt1: 2 ^ (n - i) < 2 ^ n.
        { apply: ltn_expn_subn_ltn. rewrite Hin lt0n Hi0. done. }
        rewrite ltB_nat (fromNatK Hlt1) => Hp.
        have Hlt2: 2^i < 2^n.
        { by rewrite ltn_exp2l. }
        rewrite toNat_mulB (fromNatK Hlt2).
        rewrite modn_small; first by reflexivity.
        move: Hp => {Hlt1 Hlt2}. set m := toNat p. move: m => {p} m Hm.
        rewrite -(subnK (ltnW Hin)) expnD.
        apply: (ltn_leq_mul_ltn _ Hm (leqnn (2^i))).
        by rewrite expn_gt0.
      + move/negP/idP: Hin. rewrite -leqNgt => Hni.
        rewrite (eqP Hni) expn0 ltB_nat.
        case: n p Hni.
        * move=> p _ _. rewrite !toNatNil. reflexivity.
        * move=> n p Hni. move: (expn2_gt1 n) => H.
          rewrite (fromNatK H) toNat_mulB => Hlt.
          move: (ltn_leq_sub Hlt). change (1-1) with 0. rewrite leqn0.
          move=> Hp; rewrite (eqP Hp).
          rewrite !mul0n modn_small; first reflexivity. exact: expn2_gt0.
  Qed.

  Lemma toNat_shrBn n i (p : BITS n) :
    toNat (shrBn p i) = (toNat p) %/ (2^i).
  Proof.
    elim: i n p => /=.
    - move=> n p. rewrite expn0 divn1. reflexivity.
    - move=> i IH n p. rewrite toNat_shrB IH -divn2 -divnMA expnSr.
      reflexivity.
  Qed.

  Lemma toNat_shlBn_shrBn n i (p : BITS n) :
    toNat (shrBn (shlBn p (n - i)) (n - i)) = (toNat p) %% (2^i).
  Proof.
    rewrite toNat_shrBn. rewrite shlBn_mulB toNat_mulB.
    case Hi0: (i == 0).
    - rewrite (eqP Hi0) subn0 expn0 modn1. rewrite divn_small; first reflexivity.
      rewrite ltn_mod expn_gt0. done.
    - move/negP/idP: Hi0=> Hi0. case Hin: (i < n).
      + have Hlt1: 2 ^ (n - i) < 2 ^ n.
        { apply: ltn_expn_subn_ltn. rewrite Hin lt0n Hi0. done. }
        rewrite (fromNatK Hlt1) mulnC. set m := toNat p.
        move: m Hi0 Hin Hlt1 => {p} m Hi0 Hin Hlt1.
        rewrite -{2}(subnK (ltnW Hin)). rewrite expnD.
        move: (expn2_gt0 (n - i)) => Hlt2.
        rewrite -(muln_modr Hlt2). rewrite (mulKn _ Hlt2). reflexivity.
      + move/negP/idP: Hin. rewrite -leqNgt => Hni.
        rewrite (eqP Hni) expn0 divn1.
        case: n p Hni.
        * move=> p _. rewrite toNatNil mul0n !mod0n. reflexivity.
        * move=> n p Hni. move: (expn2_gt1 n) => H.
          rewrite (fromNatK H) muln1. rewrite !modn_small; first reflexivity.
          -- apply: (ltn_leq_trans (toNatBounded p)).
             rewrite (leq_exp2l); last done. exact: Hni.
          -- exact: toNatBounded.
  Qed.

  Lemma catB_shlBn_bounded n i (p1 p2 : BITS n) :
    i <= n ->
    (p1 < shlBn (@fromNat n 1) (n - i))%bits ->
    (p1 ## p2 < shlBn # (1) (n + n - i))%bits.
  Proof.
    move=> Hin. rewrite 2!ltB_nat toNatCat. case Hi0: (i == 0).
    - rewrite (eqP Hi0) 2!subn0 2!shlBn_overflow. rewrite fromNatK; first done.
      rewrite expn_gt0; done.
    - move/negP/idP: Hi0 => Hi0. rewrite -lt0n in Hi0.
      have H1: n - i < n.
      { rewrite -{2}(subn0 n). apply: (ltn_sub2l _ Hi0).
        exact: (ltn_leq_trans Hi0 Hin). }
      have H2: n + n - i < n + n.
      { rewrite -{2}(subn0 (n + n)). apply: (ltn_sub2l _ Hi0).
        apply: ltn_addr. exact: (ltn_leq_trans Hi0 Hin). }
      rewrite (toNat_shlBn H1) (toNat_shlBn H2). move=> H.
      move: (ltn_leq_sub H) => {H} H.
      move: (leq_mul2r (2^n) (toNat p1) (2^(n-i)-1)).
      rewrite H orbT => {H} H. move: (leq_add H (toNatBounded_leq p2)).
      rewrite mulnBl mul1n.
      have H3: 2 ^ n <= 2 ^ (n - i) * 2 ^ n.
      { apply: leq_pmull. exact: expn2_gt0. }
      rewrite (addnC _ (2^n - 1)) (addnBA _ H3).
      rewrite (addnC (2^n - 1)) -(subnBA _ (leq_subr 1 (2^n))).
      rewrite (subKn (expn2_gt0 n)) -expnD (addnC (n - i)) (addnBA _ Hin).
      move=> {Hi0 Hin H1 H2 H H3} H; apply: (leq_ltn_trans H).
      rewrite -{2}(subn0 (2^(n + n - i))). apply: ltn_sub2l; last done.
      exact: expn2_gt0.
  Qed.

  Lemma toNat_catB_shlBn n i (p1 p2 : BITS n) :
    i <= n ->
    (p1 < shlBn (@fromNat n 1) (n - i))%bits ->
    toNat (shlBn (p1 ## p2) i) = (toNat p1 * (2 ^ n) + toNat p2) * (2 ^ i).
  Proof.
    move=> Hin Hp1. rewrite toNat_shlBn_bounded.
    - rewrite toNatCat. reflexivity.
    - exact: catB_shlBn_bounded.
  Qed.



  (* toPosZ *)

  Local Open Scope Z_scope.

  Lemma toPosZCons n b (p : BITS n) :
    toPosZ (consB b p) = Z.b2z b + (toPosZ p) * 2.
  Proof.
    rewrite /toPosZ /= -/(toPosZ p).
    case: b.
    - rewrite Z.double_spec Z.add_comm Z.mul_comm. reflexivity.
    - rewrite /= Z.double_spec Z.mul_comm. reflexivity.
  Qed.

  Lemma toPosZNil (x : BITS 0) : toPosZ x = 0%Z.
  Proof.
    by rewrite (tuple0 x).
  Qed.

  Lemma toPosZ_toNat n (x : BITS n) :
    toPosZ x = Z.of_nat (toNat x).
  Proof.
    elim: n x.
    - move=> x. rewrite toPosZNil toNatNil. reflexivity.
    - move=> n IH; case/tupleP => b x.
      rewrite toPosZCons toNatCons Nat2Z.inj_add -muln2 Nat2Z.inj_mul IH.
      case: b; reflexivity.
  Qed.

  Lemma fromPosZ_fromNat n (m : nat) :
    @fromPosZ n (Z.of_nat m) = @fromNat n m.
  Proof.
    elim: n m.
    - reflexivity.
    - move=> n IH m /=.
      rewrite Z.negb_even /fromNat -/fromNat.
      rewrite -nat_N_Z -N2Z.inj_div2 -Nnat.Nat2N.inj_div2 nat_N_Z IH.
      rewrite nat_N_Z Nat2Z_inj_odd ssrodd_odd ssrdiv2_div2.
      reflexivity.
  Qed.

  Lemma toPosZK n : cancel (@toPosZ n) (@fromPosZ n).
  Proof.
    elim: n.
    - move=> x /=. exact: trivialBits.
    - move=> n IH. case/tupleP => b x.
      rewrite toPosZCons /fromPosZ -/fromPosZ /= Zhalf_bit_double.
      rewrite IH Z.negb_even Z.mul_comm Z.odd_add_mul_2. by case b.
  Qed.

  Definition toPosZ_inj n := can_inj (@toPosZK n).

  Lemma toPosZ_min n (x : BITS n) : 0 <= toPosZ x.
  Proof.
    destruct x as [x Hsize].
    rewrite /toPosZ => {Hsize n} /=.
    elim: x => /=.
    - done.
    - move=> b x.
      set n := (seq.foldr
                  (fun (b : bool) (z : Z) =>
                     if b then Z.succ (Z.double z) else Z.double z) (0%Z) x).
      move=> Hind /=.
      move: (Zdouble_positive Hind) => H.
      case Hb: b.
      + apply: (Zle_trans _ _ _ Hind).
        apply: (Zle_trans _ _ _ H).
        exact: Zle_succ.
      + exact: (Zle_trans _ _ _ Hind H).
  Qed.

  Lemma toPosZ_max n : forall (x : BITS n), toPosZ x < 2 ^ Z.of_nat n.
  Proof.
    rewrite -two_power_nat_equiv. elim: n.
    - move=> x.
      rewrite toPosZNil.
      exact: zero_lt_two_power_nat.
    - move=> n IHn.
      case/tupleP => [b x].
      case Hb: b; rewrite /toPosZ /=; fold (toPosZ x).
      + rewrite /Z.succ Z.double_spec two_power_nat_S.
        apply: ltn_Sdouble.
        exact: IHn.
      + rewrite Z.double_spec two_power_nat_S.
        apply: (Zmult_gt_0_lt_compat_l _ _ _ _ (IHn x)).
        done.
  Qed.

  Definition toPosZBounded := toPosZ_max.

  Corollary toPosZ_bound n (p : BITS n) :
    0 <= toPosZ p < 2 ^ Z.of_nat n.
  Proof.
    split; [ exact: toPosZ_min | exact: toPosZ_max ].
  Qed.

  Lemma toPosZ_fromPosZBounded_nat n m :
    (m < 2^n)%N ->
    toPosZ (fromPosZ (n:=n) (Z.of_nat m)) = (Z.of_nat m).
  Proof.
    rewrite toPosZ_toNat fromPosZ_fromNat => H.
    apply: (proj2 (Nat2Z.inj_iff (toNat (@fromNat n m)) m)).
    exact: toNat_fromNatBounded.
  Qed.

  Lemma toPosZ_fromPosZBounded n m :
    (0 <= m < Zpower_nat 2 n)%Z ->
    toPosZ (fromPosZ (n:=n) m) = m.
  Proof.
    move=> [H1 H2]. rewrite -{1}(Z2Nat.id m H1) toPosZ_fromPosZBounded_nat.
    - rewrite (Z2Nat.id m H1). reflexivity.
    - apply: lt_ltn. apply: (proj2 (Nat2Z.inj_lt (Z.to_nat m) (2^n)%N)).
      rewrite (Z2Nat.id _ H1). rewrite expn_pow Nat2Z_inj_pow /= -Zpower_nat_Z.
      exact: H2.
  Qed.

  Lemma toPosZ_zero n : toPosZ (zero n) = 0%Z.
  Proof.
    rewrite /toPosZ. elim: n => /=.
    - reflexivity.
    - move=> n Hind. rewrite Hind Z.double_spec. reflexivity.
  Qed.

  Lemma fromPosZBounded_eq m1 m2 n :
    (m1 < 2^n)%N -> (m2 < 2^n)%N ->
    (m1 == m2) = (@fromPosZ n (Z.of_nat m1) == @fromPosZ n (Z.of_nat m2)).
  Proof.
    move=> H1 H2. rewrite !fromPosZ_fromNat. exact: fromNatBounded_eq.
  Qed.

  Lemma fromPosZHalf n m :
    cons_tuple (odd m) (@fromPosZ n (Z.of_nat (m./2))) = fromPosZ (Z.of_nat m).
  Proof.
    rewrite !fromPosZ_fromNat. exact: fromNatHalf.
  Qed.

  Lemma fromPosZ_wrap n m :
    @fromPosZ n (Z.of_nat m) = @fromPosZ n (Z.of_nat (m + 2^n)).
  Proof.
    rewrite !fromPosZ_fromNat. exact: fromNat_wrap.
  Qed.

  Lemma fromPosZ_wrapMany (n c m : nat) :
    @fromPosZ n (Z.of_nat m) = @fromPosZ n (Z.of_nat (m + c * 2^n)).
  Proof.
    rewrite !fromPosZ_fromNat. exact: fromNat_wrapMany.
  Qed.

  Lemma toPosZ_joinlsb n (p : BITS n) b :
    toPosZ (joinlsb (p, b)) = (Z.b2z b + (toPosZ p) * 2)%Z.
  Proof.
    exact: toPosZCons.
  Qed.

  Lemma toPosZ_zeroExtend extra n (p : BITS n) :
    toPosZ (zeroExtend extra p) = toPosZ p.
  Proof.
    rewrite !toPosZ_toNat toNat_zeroExtend; reflexivity.
  Qed.

  Lemma toPosZ_low n1 n2 (p : BITS (n1 + n2)) :
    toPosZ (low n1 p) = (toPosZ p) mod (2 ^ Z.of_nat n1).
  Proof.
    rewrite toPosZ_toNat toNat_low. have H: (2 ^ n1)%N != 0%N.
    { rewrite -lt0n. exact: expn2_gt0. }
    rewrite (Nat2Z_inj_modn _ H). rewrite expn_pow Nat2Z_inj_pow.
    rewrite -toPosZ_toNat. reflexivity.
  Qed.

  Lemma toPosZ_high n1 n2 (p : BITS (n1 + n2)) :
    toPosZ (high n2 p) = (toPosZ p) / (2 ^ Z.of_nat n1).
  Proof.
    rewrite toPosZ_toNat toNat_high.
    rewrite Nat2Z_inj_divn. rewrite expn_pow Nat2Z_inj_pow.
    rewrite -toPosZ_toNat. reflexivity.
  Qed.

  Lemma fromPosZ0 n : fromPosZ 0 = zero n.
  Proof.
    replace 0 with (Z.of_nat 0); last by reflexivity.
    rewrite fromPosZ_fromNat. exact: fromNat0.
  Qed.

  Lemma toPosZCat m n (p : BITS m) (q: BITS n) :
    toPosZ (p ## q) = toPosZ p * 2 ^ (Z.of_nat n) + toPosZ q.
  Proof.
    rewrite toPosZ_toNat toNatCat Nat2Z.inj_add Nat2Z.inj_mul Nat2Z_inj_expn
            -!toPosZ_toNat. reflexivity.
  Qed.

  Lemma ltB_toPosZ n (p1 p2 : BITS n) :
    ltB p1 p2 -> toPosZ p1 < toPosZ p2.
  Proof.
    move=> H. rewrite !toPosZ_toNat.
    apply: (proj1 (Nat2Z.inj_lt (toNat p1) (toNat p2))).
    apply: ltn_lt. rewrite -ltB_nat. exact: H.
  Qed.

  Lemma toPosZ_ltB n (p1 p2 : BITS n) :
    toPosZ p1 < toPosZ p2 -> ltB p1 p2.
  Proof.
    move=> H. rewrite !toPosZ_toNat in H.
    move: (proj2 (Nat2Z.inj_lt (toNat p1) (toNat p2)) H) => {H} H.
    move: (lt_ltn H) => {H} H. rewrite -ltB_nat in H. exact: H.
  Qed.

  Lemma leB_toPosZ n (p1 p2 : BITS n) :
    leB p1 p2 -> toPosZ p1 <= toPosZ p2.
  Proof.
    move=> H. rewrite !toPosZ_toNat.
    apply: (proj1 (Nat2Z.inj_le (toNat p1) (toNat p2))).
    apply: leq_le. rewrite -leB_nat. exact: H.
  Qed.

  Lemma toPosZ_leB n (p1 p2 : BITS n) :
    toPosZ p1 <= toPosZ p2 -> leB p1 p2.
  Proof.
    move=> H. rewrite !toPosZ_toNat in H.
    move: (proj2 (Nat2Z.inj_le (toNat p1) (toNat p2)) H) => {H} H.
    move: (le_leq H) => {H} H. rewrite -leB_nat in H. exact: H.
  Qed.

  Lemma ltB_zeroExtend n m (p1 p2 : BITS n) :
    ltB p1 p2 -> ltB (zeroExtend m p1) (zeroExtend m p2).
  Proof.
    rewrite !ltB_nat. rewrite !toNat_zeroExtend. done.
  Qed.

  Lemma leB_zeroExtend n m (p1 p2 : BITS n) :
    leB p1 p2 -> leB (zeroExtend m p1) (zeroExtend m p2).
  Proof.
    rewrite !leB_nat. rewrite !toNat_zeroExtend. done.
  Qed.



  (* toPosZ and operations *)

  Lemma toPosZ_eucl n1 n2 (p : BITS (n2 + n1)) q r :
    (q, r) = Z.div_eucl (toPosZ p) (2 ^ Z.of_nat n2) ->
    q = toPosZ (high n1 p) /\ r = toPosZ (low n2 p).
  Proof.
    rewrite !toPosZ_toNat. exact: toNat_eucl.
  Qed.

  Lemma toPosZ_eucl_high n1 n2 (p : BITS (n2 + n1)) q r :
    (q, r) = Z.div_eucl (toPosZ p) (2 ^ Z.of_nat n2) ->
    q = toPosZ (high n1 p).
  Proof.
    rewrite !toPosZ_toNat. exact: toNat_eucl_high.
  Qed.

  Lemma toPosZ_eucl_low n1 n2 (p : BITS (n2 + n1)) q r :
    (q, r) = Z.div_eucl (toPosZ p) (2 ^ Z.of_nat n2) ->
    r = toPosZ (low n2 p).
  Proof.
    rewrite !toPosZ_toNat. exact: toNat_eucl_low.
  Qed.

  Corollary toPosZ_addB n (p1 p2: BITS n) :
    toPosZ (addB p1 p2) = (toPosZ p1 + toPosZ p2) mod 2 ^ (Z.of_nat n).
  Proof.
    rewrite !toPosZ_toNat. rewrite toNat_addB. rewrite Nat2Z_inj_modn.
    - rewrite Nat2Z.inj_add Nat2Z_inj_expn. reflexivity.
    - rewrite -lt0n expn2_gt0. done.
  Qed.

  Lemma toPosZ_addB_bounded n (p1 p2 : BITS n) :
    ~~ carry_addB p1 p2 ->
    toPosZ (p1 + p2) = toPosZ p1 + toPosZ p2.
  Proof.
    move=> Hc.
    rewrite {1}toPosZ_toNat (toNat_addB_bounded Hc).
    rewrite Nat2Z.inj_add -!toPosZ_toNat. reflexivity.
  Qed.

  Lemma toPosZ_addB_zeroExtend_high n q r (p1 p2 : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p1 + toPosZ p2) (2 ^ Z.of_nat n) ->
    toPosZ (high n (zeroExtend n p1 + zeroExtend n p2)) = q.
  Proof.
    rewrite !toPosZ_toNat -Nat2Z.inj_add -addn_add -toNat_addB_zeroExtend => H.
    rewrite -(toNat_eucl_high H). reflexivity.
  Qed.

  Lemma toPosZ_addB_zeroExtend_low n q r (p1 p2 : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p1 + toPosZ p2) (2 ^ Z.of_nat n) ->
    toPosZ (low n (zeroExtend n p1 + zeroExtend n p2)) = r.
  Proof.
    rewrite !toPosZ_toNat -Nat2Z.inj_add -addn_add -toNat_addB_zeroExtend => H.
    rewrite -(toNat_eucl_low H). reflexivity.
  Qed.

  Lemma toPosZ_addB3_zeroExtend_high n q r (p1 p2 p3 : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p1 + toPosZ p2 + toPosZ p3) (2 ^ Z.of_nat n) ->
    toPosZ (high n ((zeroExtend n p1 + zeroExtend n p2)%bits + zeroExtend n p3)) = q.
  Proof.
    rewrite !toPosZ_toNat -2!Nat2Z.inj_add -2!addn_add -toNat_addB3_zeroExtend.
    set p := ((zeroExtend n p1 + zeroExtend n p2)%bits + zeroExtend n p3)%bits.
    move=> H. symmetry. exact: (toNat_eucl_high H).
  Qed.

  Lemma toPosZ_addB3_zeroExtend_low n q r (p1 p2 p3 : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p1 + toPosZ p2 + toPosZ p3) (2 ^ Z.of_nat n) ->
    toPosZ (low n ((zeroExtend n p1 + zeroExtend n p2)%bits + zeroExtend n p3)) = r.
  Proof.
    rewrite !toPosZ_toNat -2!Nat2Z.inj_add -2!addn_add -toNat_addB3_zeroExtend.
    set p := ((zeroExtend n p1 + zeroExtend n p2)%bits + zeroExtend n p3)%bits.
    move=> H. symmetry. exact: (toNat_eucl_low H).
  Qed.

  Lemma toPosZ_addB3_zeroExtend_bounded n (p1 p2 p3 : BITS n) :
    ~~ carry_addB p1 p2 -> ~~ carry_addB (p1 + p2)%bits p3 ->
    toPosZ (low n ((zeroExtend n p1 + zeroExtend n p2) + zeroExtend n p3))%bits =
    (toPosZ p1 + toPosZ p2 + toPosZ p3)%Z.
  Proof.
    move=> H1 H2. rewrite !toPosZ_toNat (toNat_addB3_zeroExtend_bounded H1 H2).
    rewrite !Nat2Z.inj_add. reflexivity.
  Qed.

  Lemma toPosZ_addB3_bounded n (p1 p2 p3 : BITS n) :
    ~~ carry_addB p1 p2 -> ~~ carry_addB (p1 + p2)%bits p3 ->
    toPosZ ((p1 + p2) + p3)%bits =
    (toPosZ p1 + toPosZ p2 + toPosZ p3)%Z.
  Proof.
    move=> H1 H2. rewrite !toPosZ_toNat (toNat_addB3_bounded H1 H2).
    rewrite !Nat2Z.inj_add. reflexivity.
  Qed.

  Corollary toPosZ_negB n (p : BITS n) :
    toPosZ (negB p) =
    if toPosZ p == 0 then 0 else 2 ^ (Z.of_nat n) - toPosZ p.
  Proof.
    rewrite !toPosZ_toNat. rewrite toNat_negB.
    case H: (toNat p == 0)%N.
    - rewrite (eqP H) /=. reflexivity.
    - have Hz: (Z.of_nat (toNat p) == 0) = false.
      { replace 0 with (Z.of_nat 0); last by reflexivity.
        apply/negP => Heq. move/negP: H; apply.
        move: (Nat2Z.inj _ _ (eqP Heq)). by move=> ->. }
      rewrite Hz. rewrite Nat2Z.inj_sub.
      * rewrite expn_pow Nat2Z_inj_pow. reflexivity.
      * apply: leq_le. apply: ltnW. exact: (toNatBounded p).
  Qed.

  Lemma toPosZ_subB_geB n (p1 p2 : BITS n) :
    leB p2 p1 -> toPosZ (subB p1 p2) = toPosZ p1 - toPosZ p2.
  Proof.
    move=> H. have: (toNat p2 <= toNat p1)%coq_nat.
    { apply: leq_le. rewrite -leB_nat. exact: H. } move=> Hle.
    rewrite toPosZ_toNat (toNat_subB H) (Nat2Z.inj_sub _ _ Hle) -!toPosZ_toNat.
    reflexivity.
  Qed.

  Lemma toPosZ_subB_ltB n (p1 p2 : BITS n) :
    ltB p1 p2 -> toPosZ (subB p1 p2) = toPosZ p1 - toPosZ p2 + 2 ^ Z.of_nat n.
  Proof.
    move=> Hlt. rewrite subB_equiv_addB_negB toPosZ_addB toPosZ_negB.
    case Hp2: (toPosZ p2 == 0).
    - rewrite ltB_nat in Hlt. have: (toNat p2 = 0)%N.
      { apply: Nat2Z.inj. rewrite -toPosZ_toNat. rewrite (eqP Hp2). reflexivity. }
      move=> H; rewrite H in Hlt. done.
    - rewrite Z.add_sub_assoc Z.add_sub_swap. move: (ltB_toPosZ Hlt).
      move=> {Hlt Hp2} Hlt. rewrite Zmod_small; first by reflexivity. split.
      + rewrite -Z.add_sub_swap.
        apply: (proj2 (Z.le_0_sub (toPosZ p2) (toPosZ p1 + 2 ^ Z.of_nat n))).
        apply: Z.le_trans.
        * apply: Z.lt_le_incl. exact: (toPosZ_max p2).
        * rewrite -{1}(Zplus_0_l (2 ^ Z.of_nat n)).
          apply: (proj1 (Z.add_le_mono_r 0 (toPosZ p1) (2 ^ Z.of_nat n))).
          exact: toPosZ_min.
      + rewrite -{2}(Zplus_0_l (2 ^ Z.of_nat n)).
        apply: (proj1 (Z.add_lt_mono_r (toPosZ p1 - toPosZ p2)
                                       0 (2 ^ Z.of_nat n))).
        exact: (proj2 (Z.lt_sub_0 (toPosZ p1) (toPosZ p2)) Hlt).
  Qed.

  Lemma subB_zeroExtend_catB n (p1 p2 : BITS n) :
    subB (zeroExtend n p1) (zeroExtend n p2) =
    (negB (fromNat (carry_subB p1 p2))) ## (subB p1 p2).
  Proof.
    apply: toPosZ_inj. rewrite toPosZCat toPosZ_negB. case Hge: (leB p2 p1).
    - move: (geB_carry_subB Hge). move/negPf => Hc. rewrite Hc /=.
      rewrite (toPosZ_toNat (@fromNat n 0)) (fromNatK (expn2_gt0 n)) /=.
      rewrite (toPosZ_subB_geB (leB_zeroExtend n Hge)) !toPosZ_zeroExtend.
      rewrite (toPosZ_subB_geB Hge). reflexivity.
    - move/idP/negPn: Hge. rewrite -ltBNle => Hlt.
      move: (ltB_carry_subB Hlt) => Hc. rewrite Hc /=. case: n p1 p2 Hlt Hc.
      + move=> p1 p2 _ _. rewrite !toPosZNil /=. reflexivity.
      + move=> n. set m := n.+1. move=> p1 p2 Hlt Hc.
        rewrite (toPosZ_toNat (@fromNat m 1)) (fromNatK (ltn_1_2expnS n)) /=.
        rewrite (toPosZ_subB_ltB (ltB_zeroExtend m Hlt)) !toPosZ_zeroExtend.
        rewrite (toPosZ_subB_ltB Hlt).
        replace (Z.pow_pos 2 (Pos.of_succ_nat n)) with (2 ^ (Z.of_nat m))
          by reflexivity. rewrite -!Zpower_nat_Z Zpower_nat_is_exp.
        set x := toPosZ p1 - toPosZ p2. set y := Zpower_nat 2 m.
        rewrite Z.mul_sub_distr_r Z.mul_1_l. ring.
  Qed.

  Lemma subB_zeroExtend_high n (p1 p2 : BITS n) :
    high n (subB (zeroExtend n p1) (zeroExtend n p2)) =
    negB (fromNat (carry_subB p1 p2)).
  Proof.
    rewrite subB_zeroExtend_catB high_catB. reflexivity.
  Qed.

  Lemma subB_zeroExtend_low n (p1 p2 : BITS n) :
    low n (subB (zeroExtend n p1) (zeroExtend n p2)) =
    subB p1 p2.
  Proof.
    rewrite subB_zeroExtend_catB low_catB. reflexivity.
  Qed.

  Lemma toPosZ_subB_bounded n (p1 p2 : BITS n) :
    ~~ carry_subB p1 p2 ->
    toPosZ (subB p1 p2) = toPosZ p1 - toPosZ p2.
  Proof.
    move/negPf=> Hc. move: (sbbB_ltB_leB p1 p2). rewrite Hc.
    move=> H. rewrite !toPosZ_toNat (toNat_subB H).
    rewrite leB_nat in H. move: (leq_le H) => {H} H.
    rewrite -(Nat2Z.inj_sub _ _ H) subn_sub. reflexivity.
  Qed.

  Lemma subB_zeroExtend_high0_carry0 n (p1 p2 : BITS n) :
    high n (subB (zeroExtend n p1) (zeroExtend n p2)) = zero n ->
    carry_subB p1 p2 = false.
  Proof.
    rewrite subB_zeroExtend_high. case Hc: (carry_subB p1 p2).
    - move=> Hneg. have: toNat (negB (@fromNat n true)) = toNat (zero n) by
          rewrite Hneg. rewrite toNat_negB toNat_zero /= => {Hneg}.
      case: n p1 p2 Hc.
      + move=> p1 p2 Hc _. rewrite carry_subB_nil in Hc. discriminate.
      + move=> n p1 p2 Hc.
        case H: (toNat # (1) == 0%N).
        * rewrite (fromNatK (expn2_gt1 n)) in H. done.
        * rewrite (fromNatK (expn2_gt1 n)). move/eqP=> {Hc H} H.
          rewrite subn_eq0 leqNgt expn2_gt1 in H. done.
    - reflexivity.
  Qed.

  Lemma toPosZ_subB_zeroExtend_bounded n (p1 p2 : BITS n) :
    high n (subB (zeroExtend n p1) (zeroExtend n p2)) = zero n ->
    toPosZ (subB (zeroExtend n p1) (zeroExtend n p2)) = toPosZ p1 - toPosZ p2.
  Proof.
    move=> Hh. rewrite (catB_high_low (zeroExtend n p1 - zeroExtend n p2)).
    rewrite toPosZCat Hh toPosZ_zero subB_zeroExtend_low toPosZ_subB_bounded.
    - reflexivity.
    - by rewrite (subB_zeroExtend_high0_carry0 Hh).
  Qed.

  Lemma toPosZ_subB_eucl n (p1 p2 : BITS n) :
    toPosZ p1 - toPosZ p2 =
    (- (toPosZ (negB (high n (zeroExtend n p1 - zeroExtend n p2))))) *
    2 ^ (Z.of_nat n) +
        (toPosZ (low n (zeroExtend n p1 - zeroExtend n p2))).
  Proof.
    rewrite subB_zeroExtend_high subB_zeroExtend_low negBK.
    case Hge: (leB p2 p1).
    - move: (geB_carry_subB Hge). move/negPf => Hc. rewrite Hc /=.
      rewrite (toPosZ_toNat (@fromNat n 0)) (fromNatK (expn2_gt0 n)) /=.
      rewrite (toPosZ_subB_geB Hge). reflexivity.
    - move/idP/negPn: Hge. rewrite -ltBNle => Hlt.
      move: (ltB_carry_subB Hlt) => Hc. rewrite Hc /=. case: n p1 p2 Hlt Hc.
      + move=> p1 p2 _ _. rewrite !toPosZNil /=. reflexivity.
      + move=> n. set m := n.+1. move=> p1 p2 Hlt Hc.
        rewrite (toPosZ_toNat (@fromNat m 1)) (fromNatK (ltn_1_2expnS n)).
        rewrite (toPosZ_subB_ltB Hlt). set k := Z.of_nat m. ring.
  Qed.

  Lemma toPosZ_subB_zeroExtend_high n q r (p1 p2 : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p1 - toPosZ p2) (2 ^ Z.of_nat n) ->
    toPosZ (negB (high n (zeroExtend n p1 - zeroExtend n p2))) = (- q)%Z.
  Proof.
    move=> H. rewrite (Zdiv_eucl_q H) toPosZ_subB_eucl.
    rewrite (Z_div_plus_full_l _ _ _ (@two_power_of_nat_ne0 n)).
    move: (toPosZ_bound (low n (zeroExtend n p1 - zeroExtend n p2))) => Hb.
    rewrite (Zdiv_small _ _ Hb) Zplus_0_r Z.opp_involutive. reflexivity.
  Qed.

  Lemma toPosZ_subB_zeroExtend_low n q r (p1 p2 : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p1 - toPosZ p2) (2 ^ Z.of_nat n) ->
    toPosZ (low n (zeroExtend n p1 - zeroExtend n p2)) = r.
  Proof.
    move=> H. rewrite (Zdiv_eucl_r H) toPosZ_subB_eucl.
    rewrite Zplus_comm Z_mod_plus_full.
    rewrite Zmod_small; first by reflexivity.
    exact: (toPosZ_bound (low n (zeroExtend n p1 - zeroExtend n p2))).
  Qed.

  Lemma ltB_toPosZ_subB_zeroExtend_min n (p1 p2 : BITS n) :
    ltB p1 p2 ->
    2 ^ Z.of_nat (n + n) - 2 ^ Z.of_nat n <
    toPosZ (subB (zeroExtend n p1) (zeroExtend n p2)).
  Proof.
    move=> Hlt. rewrite (toPosZ_subB_ltB (ltB_zeroExtend _ Hlt))
                        !toPosZ_zeroExtend. move: (ltB_toPosZ Hlt) => {Hlt} Hlt.
    rewrite Zplus_comm. apply: (proj1 (Z.add_lt_mono_l _ _ _)).
    apply: (proj2 (Z.opp_lt_mono _ _)).
    rewrite Z.opp_involutive Z.opp_sub_distr Z.add_opp_l.
    rewrite -(Z.sub_0_r (2 ^ Z.of_nat n)). apply: Z.sub_lt_le_mono.
    - exact: toPosZ_max.
    - exact: toPosZ_min.
  Qed.

  Lemma ltB_subB3_zeroExtend n (p1 p2 p3 : BITS n) :
    ltB p1 p2 ->
    leB (zeroExtend n p3) (subB (zeroExtend n p1) (zeroExtend n p2)).
  Proof.
    move=> Hlt. apply: toPosZ_leB. apply: (Z.le_trans _ (2 ^ Z.of_nat n)).
    - rewrite toPosZ_zeroExtend. apply: Z.lt_le_incl. exact: toPosZ_max.
    - apply: (Z.le_trans _ (2 ^ Z.of_nat (n + n) - 2 ^ Z.of_nat n)).
      + rewrite -!Zpower_nat_Z Zpower_nat_is_exp.
        rewrite -{4}(Z.mul_1_r (Zpower_nat 2 n)) -Z.mul_sub_distr_l.
        rewrite -{1}(Z.mul_1_r (Zpower_nat 2 n)). apply: Zmult_le_compat_l.
        * replace 1 with (2 - 1) at 1 by done. apply: Z.sub_le_mono; last by done.
          replace 2 with (Zpower_nat 2 1) at 1 by done.
          rewrite !Zpower_nat_Z. apply: Z.pow_le_mono_r; first by done.
          apply: (proj1 (Nat2Z.inj_le _ _)). apply: leq_le. case: n p1 p2 p3 Hlt.
          -- move=> p1 p2 _ Hlt. move: (ltB_toPosZ Hlt). rewrite !toPosZNil.
             done.
          -- done.
        * apply: Z.lt_le_incl. apply: Z.gt_lt. exact: Zpower_nat_gt0.
      + apply: Z.lt_le_incl. exact: (ltB_toPosZ_subB_zeroExtend_min Hlt).
  Qed.

  Lemma geB_geB_subB3_zeroExtend n m (p1 p2 p3 : BITS n) :
    leB p2 p1 ->
    leB p3 (subB p1 p2) ->
    leB (zeroExtend m p3) (subB (zeroExtend m p1) (zeroExtend m p2)).
  Proof.
    move=> Hge Hle. apply: toPosZ_leB.
    rewrite (toPosZ_subB_geB (leB_zeroExtend _ Hge)) !toPosZ_zeroExtend.
    rewrite -(toPosZ_subB_geB Hge). exact: (leB_toPosZ Hle).
  Qed.

  Lemma geB_ltB_subB3_zeroExtend n m (p1 p2 p3 : BITS n) :
    leB p2 p1 ->
    ltB (subB p1 p2) p3 ->
    ltB (subB (zeroExtend m p1) (zeroExtend m p2)) (zeroExtend m p3) .
  Proof.
    move=> Hge Hlt. apply: toPosZ_ltB.
    rewrite (toPosZ_subB_geB (leB_zeroExtend _ Hge)) !toPosZ_zeroExtend.
    rewrite -(toPosZ_subB_geB Hge). exact: (ltB_toPosZ Hlt).
  Qed.

  Definition carry_subB3 n (p1 p2 p3 : BITS n) :=
    negB
      (high n
            (subB (subB (zeroExtend n p1) (zeroExtend n p2)) (zeroExtend n p3))).

  Lemma toPosZ_subB3_bounded n (p1 p2 p3 : BITS n) :
    ~~ carry_subB p1 p2 ->
    ~~ carry_subB (p1 - p2)%bits p3 ->
    toPosZ (p1 - p2 - p3)%bits = (toPosZ p1 - toPosZ p2 - toPosZ p3)%Z.
  Proof.
    move=> H1 H2. rewrite !toPosZ_toNat (toNat_subB3_bounded H1 H2).
    rewrite !Nat2Z.inj_sub.
    - reflexivity.
    - apply: leq_le. rewrite -leB_nat. exact: (carry_subB_leB H1).
    - apply: leq_le. rewrite -(toNat_subB_bounded H1) -leB_nat.
      exact: (carry_subB_leB H2).
  Qed.

  Lemma toPosZ_subB3_bound1 n (p1 p2 p3 : BITS n) :
    leB p2 p1 ->
    leB p3 (subB p1 p2) ->
    0 <= toPosZ p1 - toPosZ p2 - toPosZ p3 < 2 ^ Z.of_nat n.
  Proof.
    move=> Hge12 Hge123. rewrite -(toPosZ_subB_geB Hge12).
    rewrite -(toPosZ_subB_geB Hge123). exact: toPosZ_bound.
  Qed.

  Lemma toPosZ_subB3_bound2 n (p1 p2 p3 : BITS n) :
    ltB p1 p2 ->
    leB p3 (p1 - p2) ->
    - (2 ^ Z.of_nat n) <= toPosZ p1 - toPosZ p2 - toPosZ p3 < 0.
  Proof.
    move=> Hlt Hge. move: (@toPosZ_min _ p3) (leB_toPosZ Hge).
    rewrite (toPosZ_subB_ltB Hlt) => H1 H2.
    move: (proj1 (Z.opp_le_mono _ _) H1) (proj1 (Z.opp_le_mono _ _) H2).
    rewrite Z.opp_0 Z.opp_add_distr Z.add_opp_r => {H1 H2} H1 H2.
    move: (proj1 (Z.add_le_mono_l _ _ (toPosZ p1 - toPosZ p2)) H1).
    move: (proj1 (Z.add_le_mono_l _ _ (toPosZ p1 - toPosZ p2)) H2).
    rewrite Z.add_sub_assoc !Z.add_opp_r Z.sub_diag Z.sub_0_l Z.add_0_r.
    move=> {H1 H2} H1 H2. have: (toPosZ p1 - toPosZ p2 < 0).
    { apply: (proj2 (Z.lt_sub_lt_add_r _ _ _)). rewrite Z.add_0_l.
      exact: (ltB_toPosZ Hlt). }
    move=> H3; move: (Z.le_lt_trans _ _ _ H2 H3) => {H2 H3} H2.
    exact: (conj H1 H2).
  Qed.

  Lemma toPosZ_subB3_bound3 n (p1 p2 p3 : BITS n) :
    leB p2 p1 ->
    ltB (p1 - p2) p3 ->
    - (2 ^ Z.of_nat n) < toPosZ p1 - toPosZ p2 - toPosZ p3 < 0.
  Proof.
    move=> Hge Hlt. move: (@toPosZ_max _ p3) (ltB_toPosZ Hlt).
    rewrite (toPosZ_subB_geB Hge) => H1 H2.
    move: (proj1 (Z.opp_lt_mono _ _) H1) (proj1 (Z.opp_lt_mono _ _) H2).
    move=> {H1 H2} H1 H2.
    move: (proj1 (Z.add_lt_mono_l _ _ (toPosZ p1 - toPosZ p2)) H2).
    rewrite !Z.add_opp_r Z.sub_diag => {H2} H2.
    move: (leB_toPosZ Hge) => H3. move: (Zle_minus_le_0 _ _ H3) => {H3} H3.
    move: (Z.add_le_lt_mono _ _ _ _ H3 H1). rewrite !Z.add_opp_r Z.sub_0_l.
    move=> {H1 H3} H1. exact: (conj H1 H2).
  Qed.

  Lemma toPosZ_subB3_bound4 n (p1 p2 p3 : BITS n) :
    ltB p1 p2 ->
    ltB (p1 - p2) p3 ->
    -(2 * 2 ^ Z.of_nat n) < toPosZ p1 - toPosZ p2 - toPosZ p3 < -(2 ^ Z.of_nat n).
  Proof.
    move=> Hlt12 Hlt123.
    move: (ltB_toPosZ Hlt123) (@toPosZ_min _ p1) (toPosZ_max p2) (toPosZ_max p3).
    rewrite (toPosZ_subB_ltB Hlt12). move=> H1 H2 H3 H4.
    move: (proj1 (Z.opp_lt_mono _ _) H1) (proj1 (Z.opp_lt_mono _ _) H3)
                                         (proj1 (Z.opp_lt_mono _ _) H4).
    rewrite Z.opp_add_distr Z.add_opp_r => {H1 H3 H4} H1 H3 H4.
    move: (proj1 (Z.add_lt_mono_l _ _ (toPosZ p1 - toPosZ p2)) H1).
    rewrite Z.add_sub_assoc !Z.add_opp_r Z.sub_diag Z.sub_0_l => {H1} H1.
    move: (Z.add_le_lt_mono _ _ _ _ H2 H3). rewrite !Z.add_opp_r Z.sub_0_l.
    move=> {H2 H3} H2. move: (Z.add_lt_mono _ _ _ _ H2 H4). rewrite !Z.add_opp_r.
    replace (- 2 ^ Z.of_nat n - 2 ^ Z.of_nat n) with
            (- (2 * 2 ^ Z.of_nat n)) by ring.
    move=> {H2 H4} H2. exact: (conj H2 H1).
  Qed.

  Lemma ltB_ltB_subB_width_gt1 n (p1 p2 p3 : BITS n) :
    ltB p1 p2 -> ltB (subB p1 p2) p3 -> (1 < n)%N.
  Proof.
    case: n p1 p2 p3.
    - done.
    - move=> [].
      + move=> p1 p2 p3 Hlt12 Hlt123. apply: False_ind.
        move: (ltB_width1 Hlt12) => [H1 H2]. rewrite H1 H2 in Hlt123.
        have: (singleBit false - singleBit true)%bits = singleBit true.
        { apply: toPosZ_inj. reflexivity. }
        move=> H; rewrite H in Hlt123. rewrite ltBNle in Hlt123.
        move/negP: Hlt123; apply. rewrite leB_nat.
        exact: (toNatBounded_leq p3).
      + move=> n p1 p2 p3 Hlt12 Hlt123. done.
  Qed.

  Lemma toPosZ_subB3_zeroExtend_bounded_fact1 n :
    (0 < n)%N ->
    2 ^ (Z.of_nat n) <= 2 ^ Z.of_nat (n + n) - 2 ^ (Z.of_nat n).
  Proof.
    move=> H. rewrite Nat2Z.inj_add Z.pow_add_r;
                [idtac | exact: Nat2Z.is_nonneg | exact: Nat2Z.is_nonneg].
    rewrite -{4}(Z.mul_1_r (2 ^ Z.of_nat n)) -Z.mul_sub_distr_l.
    rewrite -{1}(Z.mul_1_r (2 ^ Z.of_nat n)).
    apply: (proj1 (Z.mul_le_mono_pos_l _ _ _ _));
      first exact: zero_lt_two_power_of_nat.
    apply: (proj1 (Z.le_add_le_sub_r _ _ _)) => /=.
    case: n H.
    - done.
    - move=> n _. rewrite -addn1 Nat2Z.inj_add Z.pow_add_r;
                    [idtac | exact: Nat2Z.is_nonneg | done].
      rewrite -{1}(Z.mul_1_l 2). replace (2 ^ Z.of_nat 1) with 2 by done.
      apply: (proj1 (Z.mul_le_mono_pos_r _ _ _ _)); first by done.
      move: (zero_lt_two_power_of_nat n)=> H. omega.
  Qed.

  Lemma toPosZ_subB3_zeroExtend_bounded_fact2 n :
    (1 < n)%N ->
    2 ^ (Z.of_nat n) <= 2 ^ Z.of_nat (n + n) - 2 * 2 ^ (Z.of_nat n).
  Proof.
    move=> H. rewrite Nat2Z.inj_add Z.pow_add_r;
                [idtac | exact: Nat2Z.is_nonneg | exact: Nat2Z.is_nonneg].
    apply: (proj1 (Z.le_add_le_sub_r _ _ _)).
    rewrite -{1}(Z.mul_1_l (2 ^ Z.of_nat n)) -Z.mul_add_distr_r.
    apply: Z.mul_le_mono_nonneg_r.
    - apply: Z.lt_le_incl. exact: zero_lt_two_power_of_nat.
    - move: (ltn_lt H) => {H} H. elim: H.
      + done.
      + move=> {n} m H IH. rewrite -addn1 Nat2Z.inj_add Z.pow_add_r;
                [idtac | exact: Nat2Z.is_nonneg | exact: Nat2Z.is_nonneg].
        rewrite -(Z.mul_1_r (1 + 2)).
        replace (2 ^ Z.of_nat 1) with 2 by reflexivity.
        by apply: Z.mul_le_mono_nonneg.
  Qed.

  Lemma toPosZ_subB3_zeroExtend_high_ne0_case n (p1 p2 p3 : BITS n) :
    high n (subB (subB (zeroExtend n p1) (zeroExtend n p2))
                 (zeroExtend n p3)) != zero n ->
    ltB p1 p2 \/ (leB p2 p1 /\ ltB (subB p1 p2) p3).
  Proof.
    move=> Hne. case Hge12: (leB p2 p1).
    - case Hge123: (leB p3 (p1 - p2)).
      + apply: False_ind. move/negP: Hne; apply. apply/eqP. apply: toPosZ_inj.
        rewrite toPosZ_high toPosZ_zero.
        rewrite (toPosZ_subB_geB (geB_geB_subB3_zeroExtend _ Hge12 Hge123)).
        rewrite (toPosZ_subB_geB (leB_zeroExtend _ Hge12)) !toPosZ_zeroExtend.
        rewrite Z.div_small; first by reflexivity.
        exact: toPosZ_subB3_bound1.
      + move/idP/negPn: Hge123. rewrite -ltBNle => Hlt123. by right.
    - move/idP/negPn: Hge12. rewrite -ltBNle => Hlt12. by left.
  Qed.

  Lemma toPosZ_subB3_zeroExtend_high_eq0_case n (p1 p2 p3 : BITS n) :
    high n (subB (subB (zeroExtend n p1) (zeroExtend n p2))
                 (zeroExtend n p3)) = zero n ->
    leB p2 p1 /\ leB p3 (subB p1 p2).
  Proof.
    move=> Heq. case Hge12: (leB p2 p1).
    - case Hge123: (leB p3 (p1 - p2)).
      + done.
      + move/idP/negPn: Hge123. rewrite -ltBNle => Hlt123. apply: False_ind.
        eq_add_posz Heq. rewrite toPosZ_high toPosZ_zero in Heq. move: Heq.
        rewrite (toPosZ_subB_ltB (geB_ltB_subB3_zeroExtend _ Hge12 Hlt123)).
        rewrite (toPosZ_subB_geB (leB_zeroExtend _ Hge12)) !toPosZ_zeroExtend.
        have: 2 ^ Z.of_nat n <
              toPosZ p1 - toPosZ p2 - toPosZ p3 + 2 ^ Z.of_nat (n + n).
        { move: (proj1 (toPosZ_subB3_bound3 Hge12 Hlt123)) => H.
          move: (proj1 (Z.add_lt_mono_r _ _ (2 ^ Z.of_nat (n + n))) H) => {H}.
          rewrite Z.add_comm Z.add_opp_r => H. apply: (Z.le_lt_trans _ _ _ _ H).
          apply: toPosZ_subB3_zeroExtend_bounded_fact1 => {H Hge12}.
          exact: (ltB_width_gt0 Hlt123). }
        move=> H. move: (Z.lt_le_incl _ _ H) => {H} H.
        move: (Z.div_str_pos _ _ (conj
                                    (zero_lt_two_power_of_nat n) H)).
        move=> {H} H Heq. rewrite Heq in H. done.
    - move/idP/negPn: Hge12. rewrite -ltBNle => Hlt12.
      case Hge123: (leB p3 (p1 - p2)).
      + apply: False_ind. eq_add_posz Heq. move: Heq.
        rewrite toPosZ_high toPosZ_zero.
        rewrite (toPosZ_subB_geB (ltB_subB3_zeroExtend _ Hlt12)).
        rewrite (toPosZ_subB_ltB (ltB_zeroExtend _ Hlt12)) !toPosZ_zeroExtend.
        replace (toPosZ p1 - toPosZ p2 + 2 ^ Z.of_nat (n + n) - toPosZ p3) with
        (toPosZ p1 - toPosZ p2 - toPosZ p3 + 2 ^ Z.of_nat (n + n)) by ring.
        have: 2 ^ Z.of_nat n <=
              toPosZ p1 - toPosZ p2 - toPosZ p3 + 2 ^ Z.of_nat (n + n).
        { move: (proj1 (toPosZ_subB3_bound2 Hlt12 Hge123)) => H.
          move: (proj1 (Z.add_le_mono_r _ _ (2 ^ Z.of_nat (n + n))) H) => {H}.
          rewrite Z.add_comm Z.add_opp_r => H. apply: (Z.le_trans _ _ _ _ H).
          apply: toPosZ_subB3_zeroExtend_bounded_fact1 => {H Hge123}.
          exact: (ltB_width_gt0 Hlt12). }
        move=> H. move: (Z.div_str_pos _ _
                                       (conj (zero_lt_two_power_of_nat n) H)).
        move=> {H} H Heq. rewrite Heq in H. done.
      + move/idP/negPn: Hge123. rewrite -ltBNle => Hlt123. apply: False_ind.
        eq_add_posz Heq. rewrite toPosZ_high toPosZ_zero in Heq. move: Heq.
        rewrite (toPosZ_subB_geB (ltB_subB3_zeroExtend _ Hlt12)).
        rewrite (toPosZ_subB_ltB (ltB_zeroExtend _ Hlt12)) !toPosZ_zeroExtend.
        replace (toPosZ p1 - toPosZ p2 + 2 ^ Z.of_nat (n + n) - toPosZ p3) with
        (toPosZ p1 - toPosZ p2 - toPosZ p3 + 2 ^ Z.of_nat (n + n)) by ring.
        move: (toPosZ_subB3_bound4 Hlt12 Hlt123) => H.
        move: (Z.add_lt_le_mono _ _ _ _ (proj1 H)
                                (Z.le_refl (2 ^ Z.of_nat (n + n)))) => {H}.
        rewrite Z.add_comm Z.add_opp_r => H1 Hh.
        move: (ltB_ltB_subB_width_gt1 Hlt12 Hlt123) => Hn.
        move: (toPosZ_subB3_zeroExtend_bounded_fact2 Hn) => H2.
        move: (Z.le_lt_trans _ _ _ H2 H1) => {H1 H2} H.
        move: (Z.div_str_pos _ _ (conj
                                    (zero_lt_two_power_of_nat n)
                                    (Z.lt_le_incl _ _ H))).
        rewrite Hh. done.
  Qed.

  Lemma subB3_zeroExtend_low n (p1 p2 p3 : BITS n) :
    low n (subB (subB (zeroExtend n p1) (zeroExtend n p2)) (zeroExtend n p3)) =
    subB (subB p1 p2) p3.
  Proof.
    apply: toPosZ_inj. rewrite toPosZ_low.
    case Hge123: (leB p3 (p1 - p2)).
    - rewrite (toPosZ_subB_geB Hge123). case Hge12: (leB p2 p1).
      + rewrite (toPosZ_subB_geB Hge12).
        rewrite (toPosZ_subB_geB (geB_geB_subB3_zeroExtend n Hge12 Hge123)).
        rewrite (toPosZ_subB_geB (leB_zeroExtend _ Hge12)) !toPosZ_zeroExtend.
        rewrite (Zmod_small _ _ (toPosZ_subB3_bound1 Hge12 Hge123)).
        reflexivity.
      + move/idP/negPn: Hge12. rewrite -ltBNle => Hlt12.
        rewrite (toPosZ_subB_ltB Hlt12).
        rewrite (toPosZ_subB_geB (ltB_subB3_zeroExtend p3 Hlt12)).
        rewrite (toPosZ_subB_ltB (ltB_zeroExtend _ Hlt12)).
        rewrite !toPosZ_zeroExtend.
        rewrite -!Zpower_nat_Z Zpower_nat_is_exp !Zpower_nat_Z.
        rewrite -(Z_mod_plus_full _ 1 (2 ^ Z.of_nat n)).
        replace (toPosZ p1 - toPosZ p2 +
                 2 ^ Z.of_nat n * 2 ^ Z.of_nat n -
                                      toPosZ p3 + 1 * 2 ^ Z.of_nat n) with
        (toPosZ p1 - toPosZ p2 + 2 ^ Z.of_nat n - toPosZ p3 +
                                     2 ^ Z.of_nat n * 2 ^ Z.of_nat n)
          by ring.
        rewrite Z_mod_plus_full Zmod_small; first by reflexivity.
        replace (toPosZ p1 - toPosZ p2 + 2 ^ Z.of_nat n - toPosZ p3) with
        (toPosZ p1 - toPosZ p2 - toPosZ p3 + 2 ^ Z.of_nat n) by ring.
        split.
        * apply: (proj1 (Z.le_sub_le_add_r _ _ _)). rewrite Z.sub_0_l.
          exact: (proj1 (toPosZ_subB3_bound2 Hlt12 Hge123)).
        * apply: (proj2 (Z.lt_add_lt_sub_r _ _ _)). rewrite Z.sub_diag.
          exact: (proj2 (toPosZ_subB3_bound2 Hlt12 Hge123)).
    - move/idP/negPn: Hge123. rewrite -ltBNle => Hlt123.
      rewrite (toPosZ_subB_ltB Hlt123). case Hge12: (leB p2 p1).
      + rewrite (toPosZ_subB_geB Hge12)
                (toPosZ_subB_ltB (geB_ltB_subB3_zeroExtend _ Hge12 Hlt123))
                (toPosZ_subB_geB (leB_zeroExtend _ Hge12)) !toPosZ_zeroExtend.
        rewrite -!Zpower_nat_Z Zpower_nat_is_exp !Zpower_nat_Z.
        rewrite -(Z_mod_plus_full _ 1 (2 ^ Z.of_nat n)).
        replace (toPosZ p1 - toPosZ p2 - toPosZ p3 +
                 2 ^ Z.of_nat n * 2 ^ Z.of_nat n + 1 * 2 ^ Z.of_nat n) with
        (toPosZ p1 - toPosZ p2 - toPosZ p3 +
         2 ^ Z.of_nat n + 2 ^ Z.of_nat n * 2 ^ Z.of_nat n) by ring.
        rewrite Z_mod_plus_full Zmod_small; first by reflexivity.
        split.
        * apply: (proj1 (Z.le_sub_le_add_r _ _ _)). rewrite Z.sub_0_l.
          apply: Z.lt_le_incl. exact: (proj1 (toPosZ_subB3_bound3 Hge12 Hlt123)).
        * apply: (proj2 (Z.lt_add_lt_sub_r _ _ _)). rewrite Z.sub_diag.
          exact: (proj2 (toPosZ_subB3_bound3 Hge12 Hlt123)).
      + move/idP/negPn: Hge12. rewrite -ltBNle => Hlt12.
        rewrite (toPosZ_subB_ltB Hlt12)
                (toPosZ_subB_geB (ltB_subB3_zeroExtend _ Hlt12))
                (toPosZ_subB_ltB (ltB_zeroExtend _ Hlt12)) !toPosZ_zeroExtend.
        replace (toPosZ p1 - toPosZ p2 + 2 ^ Z.of_nat n - toPosZ p3 +
                                             2 ^ Z.of_nat n) with
        (toPosZ p1 - toPosZ p2 - toPosZ p3 + 2 * 2 ^ Z.of_nat n) by ring.
        rewrite -(Z_mod_plus_full _ 2 (2 ^ Z.of_nat n)).
        replace (toPosZ p1 - toPosZ p2 +
                 2 ^ Z.of_nat (n + n) - toPosZ p3 + 2 * 2 ^ Z.of_nat n) with
        (toPosZ p1 - toPosZ p2 - toPosZ p3 +
         2 * 2 ^ Z.of_nat n + 2 ^ Z.of_nat (n + n)) by ring.
        rewrite -!Zpower_nat_Z Zpower_nat_is_exp !Zpower_nat_Z.
        rewrite Z_mod_plus_full Zmod_small; first by reflexivity.
        split.
        * apply: (proj1 (Z.le_sub_le_add_r _ _ _)). rewrite Z.sub_0_l.
          apply: Z.lt_le_incl. exact: (proj1 (toPosZ_subB3_bound4 Hlt12 Hlt123)).
        * apply: (proj2 (Z.lt_add_lt_sub_r _ _ _)).
          replace (2 ^ Z.of_nat n - 2 * 2 ^ Z.of_nat n) with
                  (- (2 ^ Z.of_nat n)) by ring.
          exact: (proj2 (toPosZ_subB3_bound4 Hlt12 Hlt123)).
  Qed.

  Lemma toPosZ_subB3_zeroExtend_bounded n (p1 p2 p3 : BITS n) :
    high n (subB (subB (zeroExtend n p1) (zeroExtend n p2))
                 (zeroExtend n p3)) = zero n ->
    toPosZ (subB (subB (zeroExtend n p1) (zeroExtend n p2))
                       (zeroExtend n p3)) = toPosZ p1 - toPosZ p2 - toPosZ p3.
  Proof.
    move=> Heq. move: (toPosZ_subB3_zeroExtend_high_eq0_case Heq) =>
                [Hge12 Hge123].
    rewrite (catB_high_low
               (zeroExtend n p1 - zeroExtend n p2 - zeroExtend n p3)%bits).
    rewrite toPosZCat Heq toPosZ_zero Zmult_0_l Zplus_0_l subB3_zeroExtend_low.
    rewrite (toPosZ_subB_geB Hge123) (toPosZ_subB_geB Hge12). reflexivity.
  Qed.

  Lemma toPosZ_subB3_eucl n (p1 p2 p3 : BITS n) :
    toPosZ p1 - toPosZ p2 - toPosZ p3 =
    (- (toPosZ (negB (high n (zeroExtend n p1 - zeroExtend n p2 - zeroExtend n p3)%bits)))) *
    2 ^ (Z.of_nat n) +
        (toPosZ (low n (zeroExtend n p1 - zeroExtend n p2 - zeroExtend n p3)%bits)).
  Proof.
    rewrite toPosZ_negB toPosZ_low.
    case Hh: (high n (subB (subB (zeroExtend n p1) (zeroExtend n p2))
                           (zeroExtend n p3)) == zero n).
    - rewrite (eqP Hh) toPosZ_zero /=.
      rewrite (toPosZ_subB3_zeroExtend_bounded (eqP Hh)).
      rewrite Zmod_small; first by reflexivity. split.
      + rewrite -(toPosZ_subB3_zeroExtend_bounded (eqP Hh)). exact: toPosZ_min.
      + apply: (proj2 (Z.lt_sub_lt_add_r (toPosZ p1 - toPosZ p2) (2 ^ Z.of_nat n)
                                         (toPosZ p3))).
        apply: (proj2 (Z.lt_sub_lt_add_r (toPosZ p1) _ (toPosZ p2))).
        apply: (Z.lt_le_trans _ (2 ^ Z.of_nat n)); first by exact: toPosZ_max.
        apply: Zle_plus_r; last by exact: toPosZ_min.
        apply: Zle_plus_r; last by exact: toPosZ_min. exact: Z.le_refl.
    - have: (toPosZ (high n ((zeroExtend n p1 - zeroExtend n p2)%bits - zeroExtend n p3)) == 0) = false.
      { apply/negP => H. move/negP: Hh; apply. apply/eqP. apply: toPosZ_inj.
        rewrite (eqP H) toPosZ_zero. reflexivity. }
      move=> ->. rewrite toPosZ_high. move/idP/negP: Hh => Hh.
      case: (toPosZ_subB3_zeroExtend_high_ne0_case Hh).
      + move=> Hlt12. rewrite (toPosZ_subB_geB (ltB_subB3_zeroExtend _ Hlt12)).
        rewrite (toPosZ_subB_ltB (ltB_zeroExtend _ Hlt12)) !toPosZ_zeroExtend.
        replace (toPosZ p1 - toPosZ p2 + 2 ^ Z.of_nat (n + n) - toPosZ p3) with
        (toPosZ p1 - toPosZ p2 - toPosZ p3 + 2 ^ Z.of_nat (n + n)) by ring.
        rewrite Nat2Z.inj_add Z.pow_add_r;
          [idtac | exact: Nat2Z.is_nonneg | exact: Nat2Z.is_nonneg].
        rewrite Z_mod_plus_full (Z_div_plus_full _ _ _ (@two_power_of_nat_ne0 n)).
        rewrite Z.sub_add_distr.
        replace (2 ^ Z.of_nat n -
                     (toPosZ p1 - toPosZ p2 - toPosZ p3) / 2 ^ Z.of_nat n -
                                                               2 ^ Z.of_nat n)
        with (2 ^ Z.of_nat n -
                  2 ^ Z.of_nat n -
                      (toPosZ p1 - toPosZ p2 - toPosZ p3) / 2 ^ Z.of_nat n)
          by ring.
        rewrite Z.sub_diag Z.sub_0_l Z.opp_involutive.
        rewrite Z.mul_comm. apply: Z_div_mod_eq. apply: Z.lt_gt.
        exact: zero_lt_two_power_of_nat.
      + move=> [Hge12 Hlt123].
        rewrite (toPosZ_subB_ltB (geB_ltB_subB3_zeroExtend _ Hge12 Hlt123)).
        rewrite (toPosZ_subB_geB (leB_zeroExtend _ Hge12)) !toPosZ_zeroExtend.
        rewrite Nat2Z.inj_add Z.pow_add_r;
          [idtac | exact: Nat2Z.is_nonneg | exact: Nat2Z.is_nonneg].
        rewrite Z_mod_plus_full (Z_div_plus_full _ _ _ (@two_power_of_nat_ne0 n)).
        rewrite Z.sub_add_distr.
        replace (2 ^ Z.of_nat n -
                     (toPosZ p1 - toPosZ p2 - toPosZ p3) / 2 ^ Z.of_nat n -
                                                               2 ^ Z.of_nat n)
        with (2 ^ Z.of_nat n -
                  2 ^ Z.of_nat n -
                      (toPosZ p1 - toPosZ p2 - toPosZ p3) / 2 ^ Z.of_nat n)
          by ring.
        rewrite Z.sub_diag Z.sub_0_l Z.opp_involutive.
        rewrite Z.mul_comm. apply: Z_div_mod_eq. apply: Z.lt_gt.
        exact: zero_lt_two_power_of_nat.
  Qed.

  Lemma toPosZ_subB3_zeroExtend_high n q r (p1 p2 p3 : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p1 - toPosZ p2 - toPosZ p3) (2 ^ Z.of_nat n) ->
    toPosZ (carry_subB3 p1 p2 p3) =
    (- q)%Z.
  Proof.
    move=> H. rewrite (Zdiv_eucl_q H). rewrite toPosZ_subB3_eucl.
    rewrite (Z_div_plus_full_l _ _ _ (@two_power_of_nat_ne0 n)).
    rewrite (Zdiv_small _ _ (toPosZ_bound _)).
    rewrite Zplus_0_r Z.opp_involutive. reflexivity.
  Qed.

  Lemma toPosZ_subB3_zeroExtend_low n q r (p1 p2 p3 : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p1 - toPosZ p2 - toPosZ p3) (2 ^ Z.of_nat n) ->
    toPosZ (low n (zeroExtend n p1 - zeroExtend n p2 - zeroExtend n p3)%bits) = r.
  Proof.
    move=> H. rewrite (Zdiv_eucl_r H). rewrite toPosZ_subB3_eucl.
    rewrite Zplus_comm Z_mod_plus_full.
    rewrite Zmod_small; first by reflexivity. exact: toPosZ_bound.
  Qed.

  Lemma toPosZ_mulB_bounded n (p1 p2 : BITS n) :
    high n (fullmulB p1 p2) = zero n ->
    toPosZ (mulB p1 p2) = (toPosZ p1 * toPosZ p2).
  Proof.
    move=> H. rewrite !toPosZ_toNat -Nat2Z.inj_mul -muln_mul.
    rewrite (toNat_mulB_bounded H). reflexivity.
  Qed.

  Lemma toPosZ_fullmulB_high n q r (p1 p2 : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p1 * toPosZ p2) (2 ^ Z.of_nat n) ->
    toPosZ (high n (fullmulB p1 p2)) = q.
  Proof.
    rewrite !toPosZ_toNat -Nat2Z.inj_mul -muln_mul.
    rewrite -toNat_mulB_zeroExtend mulB_zeroExtend_fullmulB. move=> H.
    rewrite -(toNat_eucl_high H). reflexivity.
  Qed.

  Lemma toPosZ_fullmulB_low n q r (p1 p2 : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p1 * toPosZ p2) (2 ^ Z.of_nat n) ->
    toPosZ (low n (fullmulB p1 p2)) = r.
  Proof.
    rewrite !toPosZ_toNat -Nat2Z.inj_mul -muln_mul.
    rewrite -toNat_mulB_zeroExtend mulB_zeroExtend_fullmulB. move=> H.
    rewrite -(toNat_eucl_low H). reflexivity.
  Qed.

  Lemma toPosZ_shlBn_bounded n i (p : BITS n) :
    (p < shlBn (@fromNat n 1) (n - i))%bits ->
    toPosZ (shlBn p i) = (toPosZ p * 2 ^ (Z.of_nat i)).
  Proof.
    move=> H. rewrite !toPosZ_toNat (toNat_shlBn_bounded H).
    rewrite Nat2Z.inj_mul expn_pow Nat2Z_inj_pow. reflexivity.
  Qed.

  Lemma toPosZ_shrBn n i (p : BITS n) :
    toPosZ (shrBn p i) = (toPosZ p) / (2 ^ Z.of_nat i).
  Proof.
    rewrite toPosZ_toNat toNat_shrBn.
    rewrite Nat2Z_inj_divn expn_pow Nat2Z_inj_pow -toPosZ_toNat.
    reflexivity.
  Qed.

  Lemma toPosZ_shrBn_high n q r i (p : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p) (2 ^ Z.of_nat i) ->
    toPosZ (shrBn p i) = q.
  Proof.
    rewrite !toPosZ_toNat. rewrite toNat_shrBn.
    set m := (toNat p). move: m => {p n} m H.
    rewrite (Zdiv_eucl_q H) => {H q r}.
    rewrite {2}(divn_eq m (2^i)) Nat2Z.inj_add Nat2Z.inj_mul.
    rewrite expn_pow Nat2Z_inj_pow /= -expn_pow.
    rewrite Z_div_plus_full_l.
    - rewrite Zdiv_small; first by rewrite Zplus_0_r; reflexivity. split.
      + change 0 with (Z.of_nat 0). apply: (proj1 (Nat2Z.inj_le 0 (m %% 2^i))).
        apply: leq_le. done.
      + change 2 with (Z.of_nat 2). rewrite expn_pow -Nat2Z_inj_pow -expn_pow.
        apply: (proj1 (Nat2Z.inj_lt (m %% 2^i) (2^i))).
        apply: ltn_lt. rewrite ltn_mod expn_gt0. done.
    - change 2 with (Z.of_nat 2). rewrite -Nat2Z_inj_pow -expn_pow.
      change 0 with (Z.of_nat 0). move=> H. move: (Nat2Z.inj _ _ H).
      apply/eqP. rewrite -lt0n expn_gt0. done.
  Qed.

  Lemma toPosZ_shrBn_low n q r i (p : BITS n) :
    (q, r) = Z.div_eucl (toPosZ p) (2 ^ Z.of_nat i) ->
    toPosZ (shrBn (shlBn p (n - i)) (n - i)) = r.
  Proof.
    rewrite !toPosZ_toNat. rewrite toNat_shlBn_shrBn.
    set m := (toNat p). move: m => {p n} m H.
    rewrite (Zdiv_eucl_r H) => {H q r}.
    rewrite {2}(divn_eq m (2^i)) Nat2Z.inj_add Nat2Z.inj_mul.
    rewrite expn_pow Nat2Z_inj_pow /= -expn_pow.
    rewrite Zplus_comm Z_mod_plus_full. rewrite Zmod_small; first reflexivity.
    split.
    - change 0 with (Z.of_nat 0). apply: (proj1 (Nat2Z.inj_le 0 (m %% 2^i))).
      apply: leq_le. done.
    - change 2 with (Z.of_nat 2). rewrite expn_pow -Nat2Z_inj_pow -expn_pow.
      apply: (proj1 (Nat2Z.inj_lt (m %% 2^i) (2^i))).
      apply: ltn_lt. rewrite ltn_pmod; first done.
      by rewrite expn_gt0.
  Qed.

  Lemma toPosZ_catB_shlBn_high n q r i (p1 p2 : BITS n) :
    (i <= n)%N ->
    (p1 < shlBn (@fromNat n 1) (n - i))%bits ->
    (q, r) =
    Z.div_eucl (toPosZ p1 * 2 ^ Z.of_nat n + toPosZ p2) (2 ^ Z.of_nat (n - i)) ->
    toPosZ (high n (shlBn (p1 ## p2) i)) = q.
  Proof.
    move=> Hin Hp1. rewrite !toPosZ_toNat => Heucl.
    rewrite toNat_high (toNat_catB_shlBn _ Hin Hp1).
    rewrite mulnDl -mulnA (mulnC (2^n)%N (2^i)%N) mulnA.
    rewrite (divnMDl _ _ (expn2_gt0 n)).
    move: (dvdn_exp2l 2 Hin) => H.
    rewrite -(divnA _ H) => {H}. have H1: (0 < 2)%N by done.
    rewrite -(expnB H1 Hin) => {H1}.
    rewrite (Zdiv_eucl_q Heucl).
    rewrite Nat2Z.inj_add Nat2Z.inj_mul expn_pow Nat2Z_inj_pow /=.
    rewrite Nat2Z_inj_divn expn_pow Nat2Z_inj_pow /=.
    set a := toNat p1; set b := toNat p2. move=> {Hp1 Heucl q r}.
    rewrite -{2}(subnK Hin). rewrite Nat2Z.inj_add.
    rewrite (Zpower_exp _ _ _
                        (Z.le_ge _ _ (Nat2Z.is_nonneg (n - i)))
                        (Z.le_ge _ _ (Nat2Z.is_nonneg i))).
    rewrite (Z.mul_comm (2^Z.of_nat(n-i)) (2^Z.of_nat i)) Z.mul_assoc.
    have Hne: 2 ^ Z.of_nat (n - i) <> 0.
    { change 2 with (Z.of_nat 2). rewrite -Nat2Z_inj_pow -expn_pow.
      change 0 with (Z.of_nat 0). move=> H; move: (Nat2Z.inj _ _ H).
      apply/eqP. rewrite -lt0n. exact: expn2_gt0. }
    rewrite (Z_div_plus_full_l _ _ _ Hne).
    reflexivity.
  Qed.

  Lemma toPosZ_catB_shlBn_low_shrBn n q r i (p1 p2 : BITS n) :
    (i <= n)%N ->
    (p1 < shlBn (@fromNat n 1) (n - i))%bits ->
    (q, r) =
    Z.div_eucl (toPosZ p1 * 2 ^ Z.of_nat n + toPosZ p2) (2 ^ Z.of_nat (n - i)) ->
    toPosZ (shrBn (low n (shlBn (p1 ## p2) i)) i) = r.
  Proof.
    move=> Hin Hp1. rewrite !toPosZ_toNat => Heucl.
    rewrite toNat_shrBn toNat_low (toNat_catB_shlBn _ Hin Hp1).
    rewrite mulnDl -mulnA (mulnC (2 ^ n)%N (2 ^ i)%N) mulnA modnMDl.
    rewrite (Zdiv_eucl_r Heucl).
    set a := toNat p1; set b := toNat p2. move: a b.
    move=> {q r p1 p2 Hp1 Heucl} a b.
    have Hn: (n = (n - i) + i)%N.
    { symmetry. apply: subnK. exact: Hin. }
    rewrite {2}Hn. rewrite Nat2Z.inj_add.
    rewrite (Zpower_exp _ _ _
                        (Z.le_ge _ _ (Nat2Z.is_nonneg (n - i)))
                        (Z.le_ge _ _ (Nat2Z.is_nonneg i))).
    rewrite (Z.mul_comm (2^Z.of_nat(n-i)) (2^Z.of_nat i)) Z.mul_assoc.
    rewrite Z.add_comm Z_mod_plus_full.
    rewrite {1}Hn expnD -(muln_modl (expn2_gt0 i)) (mulnK _ (expn2_gt0 i)).
    have Hne: (2 ^ (n - i))%N != 0%N. { rewrite -lt0n. exact: expn2_gt0. }
    rewrite (Nat2Z_inj_modn _ Hne) expn_pow Nat2Z_inj_pow.
    reflexivity.
  Qed.

  Local Close Scope Z_scope.



End BitsLemmas.



(** Ordering *)

Module BitsOrder <: OrderedType.

  Variable n : nat.

  Definition t := BITS n.

  Definition eq : t -> t -> Prop := fun x y : t => x == y.

  Definition lt : t -> t -> Prop := fun x y : t => ltB x y.

  Hint Unfold eq lt.

  Lemma eq_refl : forall x : t, eq x x.
  Proof.
    exact: eq_refl.
  Qed.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    move=> x y.
    by rewrite /eq eq_sym.
  Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    move=> x y z.
    rewrite /eq => Hxy Hyz.
    move/eqP: Hxy => Hxy.
    move/eqP: Hyz => Hyz.
    apply/eqP.
    by rewrite Hxy Hyz.
  Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    move=> x y z.
    exact: ltB_trans.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    move=> x y Hlt.
    move/eqP => Heq.
    apply/idP: Hlt.
    by rewrite Heq ltBnn.
  Qed.

  Lemma compare : forall x y : t, Compare lt eq x y.
  Proof.
    apply: bits_rec.
    - move=> y.
      case Hy0: (y == #0).
      + move/eqP: Hy0 => Hy0; rewrite Hy0.
        rewrite fromNat0.
        apply: EQ.
        exact: eq_refl.
      + apply: LT.
        rewrite /lt ltB_nat.
        rewrite toNat_zero.
        rewrite -(eqP (bits_ne0_toNat_gt0 y)).
        apply/negP.
        by rewrite Hy0.
    - move=> x Hind y.
      move: (toNat_incB x).
      case Hx: (x == ones n) => /= Hincx.
      + move: (toNat_decB y).
        case Hy: (y == #0) => /= Hdecy.
        * apply: EQ.
          rewrite /eq (eqP Hx) (eqP Hy) incB_ones fromNat0.
          exact: eqxx.
        * apply: LT.
          rewrite /lt ltB_nat Hincx.
          rewrite -(eqP (bits_ne0_toNat_gt0 y)).
          apply/negPf.
          exact: Hy.
      + move: (toNat_decB y).
        case Hy: (y == #0) => /= Hdecy.
        * apply: GT.
          rewrite /lt ltB_nat Hincx (eqP Hy) toNat_fromNat0.
          done.
        * move: (Hind (decB y)) => {Hind} Hind.
          case: Hind => Hcomp.
          -- apply: LT.
             rewrite /lt (ltB_nat x (decB y)) Hdecy in Hcomp.
             rewrite /lt (ltB_nat (incB x) y) Hincx.
             by rewrite -(eqP (lt_sub1r_add1l (toNat x) (toNat y))).
          -- apply: EQ.
             rewrite /eq in Hcomp *.
             rewrite (eqP Hcomp).
             by rewrite (decBK y).
          -- apply: GT.
             rewrite /lt ltB_nat Hdecy in Hcomp.
             rewrite /lt ltB_nat Hincx.
             rewrite -(ltn_add2r 1 ((toNat y).-1) (toNat x)) in Hcomp.
             have: (0 < toNat y).
             ++ rewrite -(eqP (bits_ne0_toNat_gt0 y)).
                apply/negP.
                by rewrite Hy.
             ++ move=> H0y.
                rewrite addn1 addn1 in Hcomp.
                rewrite (prednK H0y) in Hcomp.
                done.
  Qed.

  Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    move=> x y.
    apply: eq_comparable.
  Qed.

End BitsOrder.



(** Intervals *)

Section BitsInterval.

  Local Open Scope bits_scope.

  Definition min (n : nat) (x y : BITS n) :=
    if x < y then x else y.

  Definition max (n : nat) (x y : BITS n) :=
    if x < y then y else x.

  Inductive intv_op : Set :=
  | LT
  | LE.

  Definition eval_intv_op (op : intv_op) (n : nat) : BITS n -> BITS n -> bool :=
    match op with
    | LT => ltB (n := n)
    | LE => leB (n := n)
    end.

  Definition interval (n : nat) (a : BITS n) (op1 : intv_op) (x : BITS n) (op2 : intv_op) (b : BITS n) : bool :=
    eval_intv_op op1 a x && eval_intv_op op2 x b.

  Notation "x ∈ [ a , b ]" := (interval a LE x LE b) (at level 20) : bits_scope.
  Notation "x ∈ ( a , b ]" := (interval a LT x LE b) (at level 20) : bits_scope.
  Notation "x ∈ [ a , b )" := (interval a LE x LT b) (at level 20) : bits_scope.
  Notation "x ∈ ( a , b )" := (interval a LT x LT b) (at level 20) : bits_scope.

  Ltac case_intv H :=
    move: H; rewrite /interval /eval_intv_op => H; caseb H.

  Definition intv_op_join (op1 op2 : intv_op) :=
    match op1, op2 with
    | LE, LE => LE
    | LT, LE
    | LE, LT
    | LT, LT => LT
    end.

  Lemma intv_addB (n : nat) (a : BITS n) op1 x op2 b c op3 y op4 d :
    interval a op1 x op2 b -> interval c op3 y op4 d ->
    ~~ carry_addB a b -> ~~ carry_addB b d ->
    interval (a + c) (intv_op_join op1 op3) (x + y) (intv_op_join op2 op4) (b + d).
  Proof.
  Abort.

End BitsInterval.


Global Transparent adcB sbbB.
Ltac bvsimpl :=
  lazy beta iota zeta delta -[
    adcB adcBmain sbbB fullmulB mulB ltB leB
         rorB rolB shrB shrBn shlB shlBn
         zeroExtend signExtend high low
         fromNat toNat fromPosZ toPosZ fromZ toZ
  ].
Ltac bvzsimpl :=
  lazy beta iota zeta delta -[
    Zmult Zplus Zpower Z.pow_pos Zpower_nat Zminus Zopp Zdiv Zmod
          adcB adcBmain sbbB fullmulB mulB ltB leB
          rorB rolB shrB shrBn shlB shlBn
          zeroExtend signExtend high low
          fromNat toNat fromPosZ toPosZ fromZ toZ
  ].
Global Opaque adcB sbbB.

(* Don't simplify fullmulB. Otherwise, Coq freezes. *)
Global Opaque low high fullmulB mulB ltB leB shlBn shrBn.
