From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBConst BBAnd BBAdd BBShl BBSub BBMul BBLshr BBUge.
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

From Coq Require List.




Lemma dropmsb_zeros : forall n, dropmsb (zeros n) = zeros n.-1.
Proof.
  move => n. case n. done.
  move => n0. have->:(zeros n0.+1.-1=zeros n0) by rewrite-addn1-subn1 addnK.
  by rewrite-zeros_rcons/dropmsb/=belastd_rcons. 
Qed.


Lemma to_nat_joinlsb a n : to_nat (joinlsb a n) = (to_nat n).*2 + a.
Proof. by rewrite addnC. Qed.

Lemma to_nat_droplsb n: to_nat (droplsb n) = (to_nat n)./2.
Proof. elim n=>[|nhd ntl IH]/=. done. 
       rewrite -div.divn2 div.divnDr. case nhd ; (rewrite/= div.divn_small; last done).
       rewrite add0n; by rewrite -!muln2 div.mulnK. 
       rewrite add0n; by rewrite -!muln2 div.mulnK.
       rewrite div.dvdn2 odd_double; done.
Qed.       

Lemma to_nat_joinmsb a n : to_nat (joinmsb n a) = a * 2^(size n) + to_nat n.
Proof.
  move : a. elim n=>[|nhd ntl IH]a/=. by rewrite -muln2 mul0n !addn0 expn0 muln1. 
  rewrite (IH a) -!muln2 mulnDl expnS; ring. 
Qed.

Lemma to_nat_dropmsb n : to_nat (dropmsb (n)) = div.modn (to_nat n) (2^(size n).-1).
Proof.
  rewrite-(revK n). case (rev n); first by rewrite/= div.modn1.
  intros. rewrite/dropmsb/splitmsb/=rev_cons belastd_rcons size_rcons.
  have->:((size (rev l)).+1.-1=size (rev l)) by rewrite-addn1-subn1 addnK.
  case b; rewrite to_nat_rcons.
  - by rewrite mul1n-div.modnDmr div.modnn addn0 (div.modn_small (to_nat_bounded (rev l))).
  - by rewrite mul0n addn0 (div.modn_small (to_nat_bounded (rev l))).
Qed.


Lemma not_zero_to_nat (q : bits) : (q == zeros (size q))=false -> (to_nat q == 0)=false.  
Proof.
  intro. apply negbT in H; rewrite -ltB0n ltB_to_nat/= in H.
  apply/eqP. rewrite Nat.neq_0_lt_0. apply (Nats.ltn_lt H).
Qed.
Print div.divn_mulAC.

Lemma full_mul0n: forall m n, full_mul (zeros m) n = zeros (m + (size n)).
Proof.
  elim => [|ms IH]n /=. by rewrite from_natn0.
  by rewrite (IH n)/joinlsb. 
Qed.
  
Lemma full_muln0: forall n m, full_mul n (zeros m) = zeros ((size n) + m).
Proof.
  elim=>[| nhd ntl IH] m/=. by rewrite from_natn0 size_zeros.
  case nhd; rewrite (IH m); first by rewrite zext_zero addB0 unzip1_zip; [ done | by rewrite size_zeros]. 
  done.  
Qed.
  
Lemma mul0B n m: mulB (zeros m) n = zeros m.
Proof.
  rewrite/mulB full_mul0n/low!size_zeros subnDA subnn sub0n cats0-zeros_cats take_size_cat; [ done | by rewrite size_zeros]. Qed.

Lemma mulB_nil_l n : mulB [::] n = [::].
Proof. by rewrite/mulB/low/= take0. Qed.

Lemma full_mul_nil_r n : full_mul n [::]= zeros (size n).
Proof.
  elim n. done. intros. rewrite/=. case a. rewrite H zext_nil addB0 unzip1_zip; last by rewrite size_joinlsb. done.
  by rewrite H.
Qed.

Lemma mulB_nil_r n : mulB n [::] = zeros (size n).
Proof.  rewrite/mulB full_mul_nil_r/low size_zeros subnn cats0 take_oversize; last by rewrite size_zeros. done. Qed.

Lemma zip_nil_r S T (p:seq S) : @zip S T p [::] = [::].
Proof.
  case p; done. Qed.

Lemma full_adder_zip_0_l : forall p n, (full_adder_zip false (zip (zeros n) p)).2 = unzip2 (zip (zeros n) p).
Proof.
  intros. generalize dependent p. elim n => [|ns IH] p/=.
  by rewrite zip_nil. 
  elim p => [|phd ptl IH1]/=. done.
  case phd;
  case Hfadd : (full_adder_zip false (zip (zeros ns) ptl))=>[c tl]/=;
  by rewrite -(IH ptl) Hfadd.
Qed.
  
Lemma add0B : forall p n, addB (zeros n) p = unzip2 (zip (zeros n) p).
Proof.
  rewrite /addB/adcB/full_adder.  exact : full_adder_zip_0_l.
Qed.

Lemma to_nat_from_nat_bounded : forall n m, m < 2^n -> to_nat (from_nat n m) = m.
Proof.
  elim => [|ns IH] m /=. symmetry; rewrite-Nat.lt_1_r; rewrite expn0 in H; by apply Nats.ltn_lt. move => Hlt.
  rewrite(IH m./2); last (rewrite expnS Nats.muln_mul in Hlt; rewrite -div.divn2 Nats.divn_div; apply (Nats.lt_ltn (Nat.div_lt_upper_bound m 2 (2^ns)(Nat.neq_succ_0 1) (ltP Hlt)))).
  case Hodd: (odd m).
  - by rewrite -Hodd odd_double_half. 
  - rewrite add0n-div.divn2-muln2 div.divnK; first done. move : (div.dvdn2 m); by rewrite Hodd.
Qed.

Lemma from_nat_bounded_eq m1 m2 n : m1 < 2^n -> m2 < 2^n ->
  (m1==m2) = (from_nat n m1 == from_nat n m2).
Proof.
  move => Hlt1 Hlt2. case E: (m1 == m2); case E': (from_nat n m1 == from_nat n m2) => //.
  by rewrite (eqP E) eq_refl in E'.
  rewrite -(to_nat_from_nat_bounded Hlt1) -(to_nat_from_nat_bounded Hlt2) in E.
  by rewrite (eqP E') eq_refl in E.
Qed.

Lemma from_nat_dhalf n m : joinlsb (odd m) (from_nat n m./2) = from_nat n.+1 m.
Proof. done. Qed.

Lemma from_nat_wrap n : forall m, from_nat n m = from_nat n (m + 2^n).
Proof. induction n => //.
rewrite expnS.
move => m.
case ODD: (odd m); rewrite /from_nat-/from_nat /=ODD odd_add odd_mul/=ODD/= halfD ODD/=.
specialize (IHn m./2). by rewrite odd_mul/= add0n mul2n doubleK IHn.
specialize (IHn m./2). by rewrite add0n mul2n doubleK IHn.
Qed.

Lemma from_nat_wrapMany n c : forall m, from_nat n m = from_nat n (m + c * 2^n).
Proof. induction c => m. by rewrite mul0n addn0.
rewrite mulSn (addnC (2^n)) addnA from_nat_wrap. rewrite IHc.
by rewrite -addnA (addnC (2^n)) addnA.
Qed.

Lemma to_nat_mod p: to_nat p = div.modn (to_nat p) (2^(size p)).
Proof. rewrite div.modn_small => //. apply to_nat_bounded. Qed.

Lemma to_nat_from_nat n m : to_nat (from_nat n m) = div.modn m (2^n).
Proof. have H:= div.divn_eq m (2^n). rewrite {1}H.
have HH:= from_nat_wrapMany n (div.divn m (2^n)) (div.modn m (2^n)). rewrite addnC in HH. rewrite -HH.
rewrite to_nat_from_nat_bounded. done. apply div.ltn_pmod. apply expn_gt0. Qed.

Lemma adcB_nat p1 p2 c : (adcB c p1 p2).2 = from_nat (size (adcB c p1 p2).2) (c + to_nat p1 + to_nat p2).
Proof.
  move : p2 c. elim p1 => [|phd1 ptl1 IH1] p2 c/=.
  - by rewrite size_adcB/=min0n/=/adcB/full_adder zip_nil.
  - move : c. elim p2 => [|phd2 ptl2 IH2] c/=; first done.
    move :(IH1 ptl2 c). rewrite/adcB/full_adder/=/bool_adder.
    case Hc : c; case Hphd1 : phd1; case Hphd2: phd2; move => Hfazt;
    case Hfadderzt : (full_adder_zip true (zip ptl1 ptl2)) =>[c0 tl0]; case Hfadderzf : (full_adder_zip false (zip ptl1 ptl2)) =>[c1 tl1]; try (rewrite Hfadderzt/= in Hfazt; rewrite Hfazt/=).
    + rewrite!odd_add!odd_double/= size_from_nat-div.divn2 div.divnDl; last by rewrite div.dvdn2 odd_double. rewrite -2!muln2 (div.mulnK _ (Nats.lt_ltn (Nat.lt_0_succ 1))) (div.divnDr); last by rewrite div.dvdn_mull. rewrite div.divn_small; last done; rewrite add0n div.mulnK; last done.
      by rewrite add1n addSn.
    + rewrite add0n odd_add!odd_double/=size_from_nat-div.divn2 div.divnDr; last by rewrite div.dvdn2 odd_double. by rewrite-2!muln2!(div.mulnK _ (Nats.lt_ltn (Nat.lt_0_succ 1))) add1n addSn. 
    + rewrite add0n uphalf_half!odd_add!odd_double/=size_from_nat-div.divn2 div.divnDl; last by rewrite div.dvdn2 odd_double. rewrite div.divnDr; last by rewrite div.dvdn2 odd_double. rewrite-!muln2!(div.mulnK _ (Nats.lt_ltn (Nat.lt_0_succ 1)))div.divn_small; last done. by rewrite add0n addnA. 
    + rewrite-!muln2!add0n-/joinlsb size_joinlsb addn1-from_nat_dhalf-addnA-mulnDl-div.divn2 div.divnDr; last by rewrite div.dvdn2 muln2 odd_double. rewrite div.divn_small; last done. rewrite (div.mulnK _ (Nats.lt_ltn (Nat.lt_0_succ 1))) add0n odd_add muln2 odd_double/=.
      move: (IH1 ptl2 false); rewrite/adcB/full_adder Hfadderzf/=add0n. move=>Hfazf; by rewrite Hfazf/=size_from_nat.
    + rewrite!add0n-/joinlsb size_joinlsb addn1-from_nat_dhalf!odd_add!odd_double-div.divn2 addnACA div.divnDl; last by rewrite div.dvdn2. rewrite div.divnn/=div.divnDr; last by rewrite div.dvdn2 odd_double.
      rewrite-2!muln2!div.mulnK; try done. move : (IH1 ptl2 true); rewrite/adcB/full_adder Hfadderzt/=; move => Hfazf; by rewrite Hfazf size_from_nat addnA.
    + rewrite!add0n-/joinlsb size_joinlsb addn1-from_nat_dhalf!odd_add!odd_double-div.divn2!div.divnDr; try by rewrite div.dvdn2 odd_double. rewrite-!muln2!div.mulnK; try done. rewrite div.divn_small/=; try done.
      move: (IH1 ptl2 false); rewrite/adcB/full_adder size_full_adder_zip add0n Hfadderzf/=; move => Hfazf; by rewrite Hfazf size_zip size_from_nat.
    + rewrite!add0n-/joinlsb size_joinlsb addn1-from_nat_dhalf!odd_add!odd_double-div.divn2 div.divnDl; last by rewrite div.dvdn2 odd_double. rewrite div.divnDr; last by rewrite div.dvdn2 odd_double. rewrite-!muln2!div.mulnK; try done. rewrite div.divn_small/=; try done. move : (IH1 ptl2 false); rewrite/adcB/full_adder Hfadderzf!add0n/=; move => Hfazf; by rewrite Hfazf size_from_nat.
    + rewrite!add0n-/joinlsb size_joinlsb addn1-from_nat_dhalf odd_add!odd_double-div.divn2 div.divnDr; last by rewrite div.dvdn2 odd_double. rewrite-!muln2!div.mulnK; try done. move : (IH1 ptl2 false); rewrite/adcB/full_adder Hfadderzf add0n/=; move => Hfazf; by rewrite Hfazf size_from_nat.
Qed.

Corollary to_nat_adcB b p1 p2 : to_nat (adcB b p1 p2).2 = to_nat (from_nat (size (adcB b p1 p2).2) (b + to_nat p1 + to_nat p2)).
Proof.
rewrite adcB_nat. rewrite size_adcB!to_nat_from_nat size_from_nat=> //. 
Qed.

Lemma to_nat_addB p1 p2 : to_nat (addB p1 p2) = to_nat (from_nat (size (addB p1 p2)) (to_nat p1 + to_nat p2)). 
Proof.
  rewrite/addB. rewrite to_nat_adcB => //. 
Qed.  

Lemma to_nat_full_mul p1 p2 : to_nat (full_mul p1 p2) = to_nat (from_nat (size (full_mul p1 p2)) (to_nat p1 * to_nat p2)).
Proof.
  move : p2. elim p1 => [|phd1 ptl1 IH] p2 /=; first by rewrite!from_natn0 size_zeros!add0n. 
  move : (to_nat_bounded ptl1) => Hbd1; move : (to_nat_bounded p2) => Hbd2.
  move : (Nat.mul_lt_mono _ _ _ _ (ltP Hbd1) (ltP Hbd2)); rewrite-!Nats.muln_mul-expnD; move => Hbd.
  SearchAbout lt. move : (mult_S_lt_compat_l 1 _ _  Hbd). rewrite -!Nats.muln_mul mulnC -expnS => Hbdmul.
  case phd1.
  - rewrite/=to_nat_addB size_addB size_joinlsb to_nat_joinlsb (IH p2) size_full_mul size_zext to_nat_zext addn1-addSn addnC minnn addn0 !to_nat_from_nat-!muln2 div.muln_modl; last done. rewrite addnS expnS.
    have-> :(2 * 2 ^ (size p2 + size ptl1) = (2 ^ (size ptl1 + size p2) * 2)) by rewrite mulnC addnC. rewrite div.modnDml.
    have->:(((1 + to_nat ptl1 * 2) * to_nat p2) = to_nat ptl1 * to_nat p2 * 2 + to_nat p2) by rewrite mulnDl mul1n; ring. done.
  - rewrite size_joinlsb to_nat_joinlsb (IH p2) size_full_mul addn0 add0n-!muln2!to_nat_from_nat_bounded; first ring. rewrite addn1 mulnAC. apply/ltP; exact. apply/ltP; exact. 
Qed.

Lemma mulnB_eq0: forall m n : bits, (mulB m n == (zeros (size m))) = (m == zeros (size m)) || (n == zeros (size n)).
Proof.
  intros.
  case Hmz : (m == zeros (size m)).
  - by rewrite (eqP Hmz) mul0B size_zeros eq_refl.
  - case Hnz : (n == zeros (size n)).
    + rewrite (eqP Hnz)/mulB full_mul0/low size_zeros subnDA subnn sub0n cats0-zeros_cats take_size_cat/= ; last by rewrite size_zeros. exact: eq_refl.
    + move : Hmz Hnz. move : n.
      elim m => [|mhd mtl IH]n/=. by rewrite mulB_nil_l.
  rewrite /mulB/=. case Hmhd: mhd. intros.
  move : (IH n). rewrite/mulB/low size_addB size_joinlsb size_zext!size_full_mul addnAC addn1 subnDA subnn sub0n cats0. intros. rewrite addnC minnn subnDA subnAC subnn sub0n cats0. rewrite (take_nth false). 
Admitted.



Lemma subB_is_dropmsb_adcB_invB (p q: bits) : subB p q = dropmsb (adcB true p (invB q)).2.
Proof. 
Admitted.

Lemma sub0B : forall m, subB (zeros (size m)) m = negB m.
Proof.
  elim => [|mhd mtl IH]/=. done.
  case mhd. rewrite/subB/sbbB/adcB/full_adder/=.
  case Hfaddzf : (full_adder_zip false (zip (zeros (size mtl)) (~~# mtl)%bits))=>[c res]/=.
  have -> : res = (full_adder_zip false (zip (zeros (size mtl)) (~~# mtl)%bits)).2
    by rewrite Hfaddzf.
  rewrite full_adder_zip_0_l unzip2_zip ; last by rewrite size_zeros -BBNeg.invB_size_ss.
Admitted.
  
Lemma subB0: forall m n, subB m (zeros n) = m.
Proof.
Admitted.
  
Lemma mulB0' : forall m n, mulB m (zeros n) = zeros (size m).
Proof.
  intros. rewrite/mulB full_muln0/low -zeros_cats take_cat size_zeros/=.
  case H : (size m < size m). move : (Nat.lt_irrefl (size m))=>Heq.
  exfalso; apply Heq; apply Nats.ltn_lt; rewrite H; done.
  by rewrite size_cat size_zeros subnDA subnn take0 sub0n !cats0.
Qed.

Lemma toNat_shlB1 : forall (p: bits), to_nat (shlB1 p) = div.modn ((to_nat p).*2) (2^size p).
Proof. move => p. by rewrite /shlB1 to_nat_dropmsb to_nat_joinlsb size_joinlsb-subn1 addnK addn0-muln2.
Qed.

Lemma toNat_shlBn:
  forall n k, k < n -> to_nat (shlB k (from_nat n 1) ) = 2 ^ k.
Proof.
Admitted.

Lemma shlB_dropmsb n (p: bits) : shlB n (dropmsb p) = dropmsb (shlB n p).
Proof.
Admitted.
  

(* ===== bit_blast_udiv ===== *)

(*Fixpoint act_size' (b : bits) : nat :=
  match b with
  | [::] => 0
  | bhd :: btl => if bhd then size b else act_size' btl
  end.

Definition act_size b := act_size' (rev b).

Fixpoint act_sizel' (l : word) :=
  match l with
  |[::] => 0
  | lhd :: ltl => if (lhd==lit_tt) then size l else act_sizel' ltl
  end.

Definition act_sizel l := act_sizel' (rev l).
*)
(*Fixpoint udivB_rec (n m : bits) i : bits * bits :=
  match i with
  | 0 => (zeros (size n), shrB (act_size n - (act_size m) + 1) n)
  | S i' => 
    let ai := nth false n (act_size n - i' - (act_size m)) in
    let di := dropmsb (joinlsb ai (udivB_rec n m i').2 ) in
    let bi := negb (ltn (to_nat di) (to_nat m)) in
    let ri := if bi then subB di (zext (size di - size m) m) else di in
    let qi := dropmsb (joinlsb bi (udivB_rec n m i').1) in
    (qi, ri)
  end.

Definition udivB (n m : bits) :=
  if (m == zeros (size m)) then (zeros (size n), zeros (size n))
  else  udivB_rec n m `(act_size n - (act_size m) + 1).*)

Fixpoint udivB_rec (n m : bits) (q r : bits): bits * bits :=
  match n with
  | [::] => (q, r)
  | nhd :: ntl => let di := dropmsb (joinlsb nhd r) in
                  let bi := negb (ltn (to_nat di) (to_nat m)) in
                  let ri := if bi then subB di m else di in
                  let qi := dropmsb (joinlsb bi q) in
                  udivB_rec ntl m qi ri
  end.
Definition udivB (n m : bits) : bits * bits :=
  if ((from_nat (size n) (to_nat m)) == zeros (size n)) then (zeros (size n), n)
  else udivB_rec n (from_nat (size n) (to_nat m)) (zeros (size n)) (zeros (size n)).

(*Definition udivB_extzip (zip : seq (bool * bool)) (q r : bits) : bits * bits :=
  udivB_rec (rev (unzip1 zip)) (unzip2 zip) q r .

Definition udivB (n m : bits) : bits * bits :=
  if (m == zeros (size m)) then (zeros (maxn(size n)(size m)), unzip1 (extzip0 n m))
  else udivB_extzip (extzip0 n m) (zeros (maxn(size n)(size m))) (zeros (maxn(size n)(size m))).*)
 
Eval compute in (to_nat (udivB (from_nat 8 185) (from_nat 14 14)).1).
Eval compute in (to_nat (udivB (from_nat 8 185) (from_nat 14 13)).2).
Eval compute in (to_nat (udivB (from_nat 15 15) (from_nat 3 2)).1).
Eval compute in (to_nat (udivB (from_nat 15 15) (from_nat 3 2)).2).


Lemma size_udivB_rec n m q r : size (udivB_rec n m q r).1 = size q.
Proof.
  move : m q r.  elim n => [|nhd ntl IH]m q r/=; first done. 
  rewrite (IH m (dropmsb (joinlsb (~~ (to_nat (dropmsb (joinlsb nhd r)) < to_nat m)) q))
              (if ~~ (to_nat (dropmsb (joinlsb nhd r)) < to_nat m)
               then (dropmsb (joinlsb nhd r) -# m)%bits
               else dropmsb (joinlsb nhd r))).
    by rewrite size_dropmsb size_joinlsb addnK.
Qed.  

Lemma size_udivB n m : size (udivB n m).1 = (size n).
Proof.
  rewrite/udivB. case Hm0: ((size n) -bits of (to_nat m)%bits == zeros (size n)); first by rewrite size_zeros.
  by rewrite (size_udivB_rec n (size n) -bits of (to_nat m)%bits (zeros (size n)) (zeros (size n))) size_zeros.
Qed.


  Lemma udivB0 : forall n m, (udivB m (zeros n)) = (zeros (size m), m).
Proof.
  intros; rewrite/udivB. by rewrite to_nat_zeros from_natn0 eq_refl/=.
Qed.


Lemma udivB_rec0_aux : forall n(m : bits) s,
    ~~(m==zeros(size m)) -> udivB_rec (zeros n) m (zeros s) (zeros s)= (zeros s, zeros s).
Proof.
  elim. intros; first by done.
  intros. rewrite-zeros_cons/=to_nat_dropmsb to_nat_joinlsb to_nat_zeros div.mod0n. 
  move : (to_nat_zero m). move: H0; rewrite-eqbF_neg; move=>Hnotz; rewrite(eqP Hnotz)eqn0Ngt; move=>Htonat; rewrite Htonat/joinlsb zeros_cons dropmsb_zeros-pred_Sn. rewrite eqbF_neg in Hnotz.
  exact :(H m s Hnotz).
Qed.


  
Lemma udivB_rec0 : forall n (m : bits) q r ,
    ~~(m==zeros(size m)) -> udivB_rec (zeros n.+1) m q (zeros r)= (shlB n.+1 q, (zeros r)).
Proof.
  intros. rewrite-zeros_cons/=to_nat_dropmsb to_nat_joinlsb to_nat_zeros div.mod0n.
  move : (to_nat_zero m). move: H; rewrite-eqbF_neg; move=>Hnotz; rewrite(eqP Hnotz)eqn0Ngt; move=>Htonat; rewrite Htonat/joinlsb zeros_cons dropmsb_zeros-pred_Sn/shlB1. rewrite eqbF_neg in Hnotz.
  move: q r. elim n; first done.  intros. rewrite-zeros_cons/=to_nat_dropmsb to_nat_joinlsb to_nat_zeros div.mod0n Htonat/joinlsb zeros_cons dropmsb_zeros-addn1-subn1 addnK.
  move :(H (dropmsb (false :: q)) r). 
  rewrite/shlB1/joinlsb. have->: ((dropmsb (false :: q) <<# n0)%bits = dropmsb (false :: (q <<# n0)%bits)).
  rewrite/shlB/shlB1. elim n0; first done. rewrite/joinlsb/=; intros; by rewrite H0.
  done.
Qed.

Lemma udiv0B : forall n (m: bits), ~~(from_nat n (to_nat m) == zeros n)-> udivB (zeros n) m = (zeros n, zeros n).
Proof.
  move => n m Hm. move : (negbTE Hm) => Hnot0. rewrite/udivB size_zeros Hnot0. 
  move : Hnot0. elim n; first done.
  move => ns Hudiv Hnot0. rewrite udivB_rec0; first by rewrite/shlB shlB_mul2exp mul0B.
  by rewrite size_from_nat Hnot0.
Qed.
  
Lemma size_uremB_rec : forall  n m q r, size m = size r -> size (udivB_rec n m q r).2 = size r.
Proof.
  elim =>[|nhd ntl IH]m q r Hsz; first done.
  rewrite/=(IH m (dropmsb (joinlsb (~~ (to_nat (dropmsb (joinlsb nhd r)) < to_nat m)) q))
       (if ~~ (to_nat (dropmsb (joinlsb nhd r)) < to_nat m)
        then (dropmsb (joinlsb nhd r) -# m)%bits
        else dropmsb (joinlsb nhd r)));
  case H : ((to_nat (dropmsb (joinlsb nhd r)) < to_nat m)); try (by rewrite/=size_dropmsb size_joinlsb addnK|| by rewrite/=QFBV.size_subB size_dropmsb size_joinlsb addnK Hsz minnn).
Qed.    

Lemma size_uremB : forall n m , size (udivB n m).2 = size n.
Proof.
  rewrite/udivB. intros.
  case Hm0: ((size n) -bits of (to_nat m)%bits == zeros (size n)); first done. 
  rewrite size_uremB_rec; rewrite size_zeros; first done. by rewrite size_from_nat.
Qed.  

Lemma udivB_mulAC : forall d m n, (udivB d m).2 = zeros (size d) -> udivB m (mulB d n) = udivB (mulB m n) d.
Proof.
(*  elim =>[|dhd dtl IH] m n H; rewrite/udivB/=.
  - rewrite !size_mulB/mulB/= /low !take0 add0n sub0n zeros0 cats0/=/extzip0!unzip1_extzip!sub0n!cats0. 
  - case Hz : (dhd :: dtl == b0 :: zeros (size dtl)).
    + rewrite (eqP Hz)zeros_cons size_mulB size_zeros !mul0B/=.
      case Hzeros: (b0 :: zeros (size dtl) == b0 :: zeros (size dtl)); rewrite !size_mulB; first done.
      rewrite zeros_cons in Hzeros. move : (eq_refl (zeros (size dtl).+1)) => Hzeros'; rewrite Hzeros' in Hzeros; discriminate.
    + case Hmul0 : (((dhd :: dtl) *# n)%bits == zeros (size ((dhd :: dtl) *# n)%bits)).
      * rewrite size_mulB mulnB_eq0 in Hmul0. move : (orP Hmul0)=>[Hl| Hr].
        rewrite/= in Hl. rewrite Hl in Hz; discriminate.
        rewrite (eqP Hr) mulB0' act_size0 sub0n add0n. rewrite/=subn0 !act_size0 !sub0n add0n size_zeros nth0. have ->: (head false (zeros (size m))=false) by (case m=>[|mhd mtl]; by rewrite/=). rewrite/joinlsb/=/shrB1/= to_nat_dropmsb/=to_nat_droplsb/= to_nat_joinmsb mul0n to_nat_zeros addn0 div.mod0n. move : (to_nat_zero (dhd :: dtl))=> Heqz. rewrite Hz/= in Heqz. rewrite (neq0_lt0n Heqz)/= zeros_cons dropmsb_zeros. by rewrite/joinmsb zeros_rcons /droplsb/=zeros_cons dropmsb_zeros-addn1-subn1 addnK.
      * rewrite size_mulB mulnB_eq0 Hz/= in Hmul0.
*)
Admitted.
  
Lemma to_nat_shrB1 : forall bs, to_nat (shrB1 bs) = div.divn (to_nat bs) 2.
Proof.
  elim => [|bhd btl IH]/=. done.
  by rewrite/shrB1 to_nat_droplsb to_nat_joinmsb mul0n add0n/=-muln2-div.divn2.
Qed.
  
Lemma to_nat_shrB : forall n bs, to_nat (shrB n bs) = div.divn (to_nat bs) (2^n).
Proof.
  intros.
  elim n => [|ns IH]/=. by rewrite div.divn1.
  by rewrite to_nat_shrB1 IH-div.divnMA expnS mulnC. 
Qed.

Lemma ltn_neq0 : forall n m, n < m -> (m != 0).
Proof.
  elim => [| ns IH] m/=. by rewrite lt0n.
  - intro. rewrite-(eqP (Nats.lt_sub1r_add1l ns m)) in H; apply (IH m.-1) in H.
    rewrite-lt0n (eqP (Nats.lt_sub1r_add1l 0 m)) in H. move : (ltn_trans (ltn0Sn 0) H). by rewrite lt0n.
Qed.
(*
    Definition A:= Set->Set->Type.
    Definition B := A->Type.
    Definition C := B->Prop.
    Check C. 
    Definition id (T : Type) (x : T) : T := x. 
    Check id (id (Set->Prop)).
SearchAbout ltB.

Lemma lt0B_size : forall b, ([::] <# b)%bits -> 0 < size b.
Proof.
  elim; first done. intros; by rewrite ltn0Sn.
Qed.

Lemma odd_to_nat_lsb : forall b, odd (to_nat b) =lsb b.
Proof.
  elim; first by rewrite/lsb/splitlsb/=.
  move => a l IH.
  rewrite/lsb/=odd_add odd_double-negb_eqb. case Ha : a; done.
Qed.

Inductive par : Set := open | close. Print cat. Print app.

Inductive wp : list par -> Prop :=
| wp0 : wp nil
| wp1 : forall l, wp l -> wp (cons open (l ++ (close :: nil)))
| wp2 : forall l1 l2, wp l1 -> wp l2 -> wp (l1 ++ l2).

Theorem wp_oc : wp (cons open (cons close nil)).
Proof.
  have ->: (cons close nil = nil ++ (cons close nil)) . done.
  apply wp1. apply wp0.
Qed.

Theorem wp_oc2 : wp (cons open (cons open (cons close (cons close nil)))).
Proof.
set l := (open:: (close::nil)). assert (wp l) by apply wp_oc.
  apply wp1 with (l := (open:: (close::nil))). apply H.
Qed.

Lemma wp_o_head_c :
forall l1 l2:list par,
  wp l1 -> wp l2 -> wp (cons open (app l1 (cons close l2)%list))%list.
Proof.
  intros. have -> : (open :: (l1 ++ (close :: l2))%list = (open::(l1 ++ (close :: nil)))++l2). 
  rewrite!app_comm_cons. SearchAbout app. erewrite <-app_assoc.  rewrite{3}/app. done.
  apply wp2. apply wp1. apply H. apply H0.
Qed.

Require Import Relations.
Section perms.
Variable A : Set.

 Inductive transpose : list A -> list A -> Prop :=
   | transpose_hd :
       forall (a b:A) (l:list A), transpose (a :: b :: l) (b :: a :: l)
   | transpose_tl :
       forall (a:A) (l l':list A),
         transpose l l' -> transpose (a :: l) (a :: l').


Inductive perm (l:list A) : list A -> Prop :=
  | perm_id : perm l l
  | perm_tr :
      forall l' l'':list A, perm l l' -> transpose l' l'' -> perm l l''.


Lemma perm_refl : reflexive _ perm. 
Proof.
  unfold reflexive; left.
Qed.


Lemma perm_intro_r :
 forall l l1 l2:list A, transpose l l1 -> perm l1 l2 -> perm l l2.
Proof.
 intros l l1 l2 H H0; elim H0.
 eapply perm_tr; eauto.
 left.
 intros l' l''; intros; right with l'; auto.
Qed.

Lemma perm_trans : transitive _ perm.
Proof.
 unfold transitive; intros l l' l'' H; generalize l''.
 elim H.
 trivial.
 intros l'0 l''0 H0 H1; intros.
  apply H1;eapply perm_intro_r; eauto.
Qed.

Lemma transpose_sym : forall l l':list A, transpose l l' -> transpose l' l.
Proof.
 intros l l' H;elim H; [ left | right; auto ].
Qed.

Lemma perm_sym : symmetric _ perm. 
Proof.
 unfold symmetric; intros l l' H; elim H. 
 left.
 intros; eapply perm_intro_r.
 eapply transpose_sym; eauto.
 auto.
Qed.


Theorem equiv_perm : equiv _ perm.
Proof.
 repeat split.
 apply perm_refl.
 apply perm_trans.
 apply perm_sym.
Qed.

Inductive num : Type :=
| zero : num
| succ : num -> num
| doub : num -> num.

Inductive eqwal {A : Type} (x : A) : A -> Prop :=
    eqw_refl : eqwal x x.

Unset Elimination Schemes.

Inductive nawt : Prop :=
    | zewro : nawt
    | sawc  : nawt -> nawt.

Scheme nawt_ind := Induction for nawt Sort Prop.

Check nawt_ind.

Set Elimination Schemes.

Fixpoint plaws (m n : nawt) : nawt :=
    match m with
      | zewro => n
      | sawc m' => sawc (plaws m' n)
    end.

End perms.

Theorem eqwal_sym {A : Type} (x y : A) : eqwal x y -> eqwal y x.
Proof. intros H. destruct H. constructor. Qed.

Theorem neutral_r : forall n : nawt, eqwal (plaws n zewro) n.
Proof.
intros. induction n as [|ns IH]; simpl.
- done. - apply eqwal_sym in IH. destruct IH . constructor.
Qed.

Lemma predp : forall n: nat, (exists p: nat, n=S p) \/ n = 0.
intros n. case n.
right. done. intros p. left. exists p. reflexivity.
Defined.

Definition preds : forall n:nat, {p:nat | n = S p}+{n = 0}.
intros n. case n.
right. apply refl_equal.
intros p. left. exists p. reflexivity.
Defined.
Extraction preds.
Eval compute in (or False True). 
Definition eq_decx (A:Type) := forall x y: A, {x = y}+{x <> y}.
Eval compute in (Nat.eq_dec 1 1).
Print Nat.eq_dec.
Definition cmp_cmp : forall x y, {x>y}+{x<=y}. 
intros x. induction x. right. done. intros y. move :(IHx (y-1))=> Hm. destruct Hm. left. have ->:(x.+1 = x+1) by rewrite addn1. 
Admitted.
Eval compute in (cmp_cmp 1 2).

Module ccc.
  From Coq Require Import ZArith OrderedType Bool.
   Definition t := lit_eqType.
  Definition eqn (x y : t) := x == y.
  Definition ltn (x y : t) := lit_lt x y.
  Definition ltn_trans := lit_lt_trans.
  Definition ltn_not_eqn := lit_lt_not_eq.
Definition compare (x y : t) : Compare ltn eqn x y.
  Proof.
    case Heq: (x == y).
    - exact: (EQ Heq).
    - case Hlt: (lit_lt x y).
      + exact: (LT Hlt).
      + apply: GT. move: (proj1 (Z.ltb_ge (z_of_lit x) (z_of_lit y)) Hlt) => {Hlt} Hlt.
        have Hne: z_of_lit y <> z_of_lit x
          by move=> H; apply/eqP/idP: Heq; rewrite (z_of_lit_inj H) eqxx.
        apply/Z_ltP. apply: (proj2 (Z.le_neq _ _)). split; assumption.
  Defined.
End ccc.

Module ttt.
Axiom f : nat -> option nat.
Axiom H : nat -> bool.
Axiom no_error_in_f : forall n,
  H n = true -> exists u, f n = Some u.

Lemma no_error_in_f_bis : forall n,
  H n = true -> f n <> None.
Proof.
  intros. apply no_error_in_f in H0. destruct H0. rewrite H0. discriminate.
Qed.

Definition g n :=
  match H n as b return H n = b -> _ with
  | true => fun H =>
    match f n as f0 return f n = f0 -> _ with
    | Some n0 => fun _ => n0
    | None => fun H0 => match no_error_in_f_bis  H H0 with end
    end (Logic.eq_refl)
  | false => fun _ => n
  end Logic.eq_refl.


Require Import Coq.Sorting.Sorted.
Print Sorted.
Print HdRel. 
Function sort' (l : list Z): forall (R : Z -> Z -> Prop), {l': list Z | Sorted R l'}.
intros. case l.
- exists nil. done.
- intros. case l0.
  + exists (cons z nil). constructor; done. 
  + 


    move : (sort' [:: z, z0 & l1] R). intro. move : sort'0 l1. 
    constructor. constructor. 

Defined.  
  refine (
      fun (R: Z -> Z -> Prop) =>
        match l with
        | nil => _
        | cons x l2 => _
        end).
  - exists nil. done.
  - case l2.  exists (cons x nil). constructor; done.
    refine (
        fun (y: Z) (l3 : list Z) =>
          match l3 with
          | nil => fun _R : R => 
          | cons z l4 => _ end).
  - exists ()

    
Abort.

Definition sort' : forall (l : list Z) (R : Z -> Z -> Prop), {l': list Z | Sorted R l'}. 
  refine (
      fun (l: list Z) (R: Z -> Z -> Prop) =>
        match l with
        | nil => _
        | cons x l2 => _
        end).
  - exists nil. done.
  - case l2.  exists (cons x nil). constructor; done.
    refine (
        fun (y: Z) (l3 : list Z) =>
          match l3 with
          | nil => 


    
Defined.


End ttt.
*)



Lemma neq0_eq0_sizel : forall n (b : bits), b!=zeros (size b) -> from_nat n (to_nat b) == zeros n -> n < size b.
Proof.
  elim => [|ns IH] b/=; first by (rewrite-ltB0n eq_refl; move=> [Hneq Ht{Ht}]; exact (lt0B_size Hneq)).
  move=>[Hneq Heq]. move : (IH (droplsb b)) => Hm. rewrite-(eqP (Nats.lt_sub1r_add1l ns (size b)))-subn1-size_droplsb. apply Hm; last rewrite to_nat_droplsb.
  move : Hneq. rewrite-!to_nat_zero to_nat_droplsb-!lt0n half_gt0. move => Hgt0.
  case Hoddb: (odd (to_nat b)); first by rewrite Hoddb eqseq_cons andFb in Heq.
  rewrite Hoddb/joinlsb eqseq_cons andTb in Heq. rewrite Nats.ssrodd_odd-Nat.even_succ-Nat.negb_odd in Hoddb. move: (negbFE Hoddb)=>Hodd{Hoddb}. rewrite-Nats.ssrodd_odd in Hodd. rewrite-(ltn_add2r 1)2!addn1 in Hgt0. move : (odd_gt2 Hodd Hgt0)=> Hodd2.  move : (ltn_sub2r Hgt0 Hodd2). by rewrite!subn1/=. 
  rewrite eqseq_cons in Heq. move/andP : Heq=>[Hb0 Hzeq]. done.
Qed.

Lemma udivB_def: forall q d r, ltB r d -> (udivB (addB (mulB q d) r) d).2 = r.
Proof.
Admitted.
  
Lemma udivB_rec_to_nat : forall nhd ntl m q r, to_nat (udivB_rec (nhd::ntl) m q r).1 = addn (div.divn (addn (to_nat (shlB (size ntl).+1 r)) (to_nat (nhd::ntl))) (to_nat m)) (to_nat q).
Proof.
Admitted.
  
Lemma udivB_to_nat : forall p q,  to_nat (udivB p q).1 = (div.divn (to_nat p) (to_nat (from_nat (size p) (to_nat q)))).
Proof.
  (*
  intros. rewrite/udivB.
  case H0 : ((size p) -bits of (to_nat q)%bits == zeros (size p));
    first by rewrite/=(eqP H0) to_nat_zeros div.divn0. 
  move : q H0. elim p =>[|phd ptl IH] q H0/=; first done.
  have : (to_nat (dropmsb (zeros (size ptl).+1)) = 0) by rewrite to_nat_dropmsb to_nat_zeros div.mod0n.
  rewrite/dropmsb/splitmsb/=; move => Hbelast; rewrite Hbelast-muln2 mul0n addn0/=.
  case Hphd : phd; case Hoddq : (odd (to_nat q)); rewrite /=eqseq_cons Hoddq in H0; rewrite/=.
  - have Hgt0 : (0 < (to_nat (size ptl) -bits of ((to_nat q)./2)%bits)). admit.
    move : (muln_gt0 (to_nat (size ptl) -bits of ((to_nat q)./2)%bits) 2)=> Hgt0'; rewrite Hgt0(ltn0Sn 1)andTb muln2-(ltn_add2l 1)addn0 in Hgt0'.
    rewrite Hgt0'/=.

    
    rewrite Hgt0' udivB_rec_to_nat/shlB shlB_mul2exp/=add0n/mulB/=size_belast size_zeros/low size_addB size_joinlsb. 
*)
Admitted.  

Lemma uremB_to_nat : forall p q , to_nat (udivB p q).2 = (div.modn (to_nat p) (to_nat q)).
Proof.  
Admitted.

Fixpoint bit_blast_udiv_rec g ls1 ls2 cs qs rs: generator * cnf * word * word :=
  match ls1 with
  | [::] => (g, cs, qs, rs)
  | ls_hd1 :: ls_tl1 =>
    let di := dropmsl (joinlsl ls_hd1 rs) in
    let '(g_ge, cs_ge, lrs_ge) := bit_blast_uge g di ls2 in
    let qi := dropmsl (joinlsl lrs_ge qs) in
    if (lrs_ge==lit_tt) then
      let '(g_sub, cs_sub, lrs_sub) := bit_blast_sub g_ge di ls2 in
      bit_blast_udiv_rec g_sub ls_tl1 ls2 (catrev (catrev cs cs_ge) cs_sub) qi lrs_sub
    else if (lrs_ge == lit_ff) then bit_blast_udiv_rec g_ge ls_tl1 ls2 (catrev cs cs_ge) qi di
         else
           let '(g_and, cs_and, lrs_and) := bit_blast_and g_ge (copy (size ls2) lrs_ge) ls2 in
           let '(g_sub2, cs_sub2, lrs_sub2) := bit_blast_sub g_and di lrs_and in
           bit_blast_udiv_rec g_sub2 ls_tl1 ls2 (catrev (catrev (catrev cs cs_ge) cs_and) cs_sub2) qi lrs_sub2
  end.
 
Definition bit_blast_udiv g ls1 ls2 :=
  if ls2 == copy (size ls2) lit_ff then
    (g, [::], copy (size ls1) lit_ff, ls1)
    else
      bit_blast_udiv_rec g ls1 ls2 [::] (copy (size ls1) lit_ff) (copy (size ls1) lit_ff).

Fixpoint mk_env_udiv_rec (E: env) (g:generator) ls1 ls2 cs qs rs : env * generator * cnf * word * word :=
  match ls1 with
  | [::] => (E, g, cs, qs, rs)
  | ls1_hd :: ls1_tl =>
    let di := dropmsl (joinlsl ls1_hd rs) in
    let '(E_ge, g_ge, cs_ge, lrs_ge) := mk_env_uge E g di ls2 in
    let qi := dropmsl (joinlsl lrs_ge qs) in
    if (lrs_ge == lit_tt) then
      let '(E_sub, g_sub, cs_sub, lrs_sub) := mk_env_sub E_ge g_ge di ls2 in
      mk_env_udiv_rec E_sub g_sub ls1_tl ls2 (catrev (catrev cs cs_ge) cs_sub) qi lrs_sub
    else if (lrs_ge == lit_ff) then mk_env_udiv_rec E_ge g_ge ls1_tl ls2 (catrev cs cs_ge) qi di
         else
           let '(E_and, g_and, cs_and, lrs_and) := mk_env_and E_ge g_ge (copy (size ls2) lrs_ge) ls2 in
           let '(E_sub2, g_sub2, cs_sub2, lrs_sub2) := mk_env_sub E_and g_and di lrs_and in
           mk_env_udiv_rec E_sub2 g_sub2 ls1_tl ls2 (catrev (catrev (catrev cs cs_ge) cs_and) cs_sub2) qi lrs_sub2
  end.

Definition mk_env_udiv E g ls1 ls2 :=
  if ls2 == copy (size ls2) lit_ff then
    (E, g, [::], copy (size ls1) lit_ff, ls1)
    else
      mk_env_udiv_rec E g ls1 ls2 [::] (copy (size ls1) lit_ff) (copy (size ls1) lit_ff).

Lemma bit_blast_sub_size_ss : forall g ls1 ls2 g' cs' lrs,
    bit_blast_sub g ls1 ls2  = (g', cs', lrs) -> size ls1 = size ls2 -> size lrs = size ls2.
Proof.
  move => g ls1 ls2 g' cs lrs. rewrite/bit_blast_sub.
  case Hbbneg : (BBNeg.bit_blast_neg g ls2) => [[g_neg cs_neg] lrs_neg].
  case Hbbadd : (bit_blast_add g_neg ls1 lrs_neg) => [[ g_add cs_add] lrs_add].
  case => _ _ <- Hsz12. move: (bit_blast_neg_size_ss Hbbneg)=>Hszneg; rewrite Hszneg in Hsz12. rewrite-( bit_blast_add_size_ss Hbbadd Hsz12). by rewrite Hszneg Hsz12.
Qed.

Lemma bit_blast_udiv_rec_size_ss : forall g ls1 ls2 g' cs qs rs cs' qlrs rlrs  ,
    bit_blast_udiv_rec g ls1 ls2 cs qs rs = (g', cs', qlrs, rlrs) ->
    (*size ls1 = size ls2 -> *) size qs = size ls2 -> size rs = size ls2 ->
    (*enc_bits E ls1 bs1 ->  enc_bits E ls2 bs2 ->*) (size qlrs = size ls2 /\ size rlrs = size ls2).
Proof.
  move => g ls1; move : g.
  elim ls1 => [|ls1hd ls1tl IH] g ls2 g' cs qs rs cs' qlrs rlrs  Hbbdiv Hszqs Hszrs ; move : Hbbdiv; rewrite/bit_blast_udiv/=.
  case => _ _ <- <-; done.
  case Hbbuge: (bit_blast_uge g (dropmsl (joinlsl ls1hd rs)) ls2)=> [[g_ge cs_ge] lrs_ge].
  case Hgett : (lrs_ge == lit_tt).
  case Hbbsub : (bit_blast_sub g_ge (dropmsl (joinlsl ls1hd rs)) ls2) => [[g_sub cs_sub] lrs_sub].
  move => Hbbdiv. 
  move : (IH g_sub ls2 g' (catrev (catrev cs cs_ge) cs_sub) (dropmsl (joinlsl lrs_ge qs)) lrs_sub cs' qlrs rlrs  Hbbdiv)=> Hm. apply Hm. by rewrite size_dropmsl size_joinlsl addnK.
  move : (bit_blast_sub_size_ss Hbbsub)=>Hszsub. rewrite size_dropmsl size_joinlsl addnK in Hszsub; exact (Hszsub Hszrs). 
  case Hgeff: (lrs_ge == lit_ff).
  move => Hbbdiv.
  move : (IH g_ge ls2 g' (catrev cs cs_ge) (dropmsl (joinlsl lrs_ge qs)) (dropmsl (joinlsl ls1hd rs)) cs' qlrs rlrs  Hbbdiv)=> Hm. rewrite!size_dropmsl!size_joinlsl!addnK in Hm.
  exact : (Hm Hszqs Hszrs ).
  case Hbband : (bit_blast_and g_ge (copy (size ls2) lrs_ge) ls2) => [[g_and cs_and] lrs_and].
  case Hbbsub2 : (bit_blast_sub g_and (dropmsl (joinlsl ls1hd rs)) lrs_and) => [[g_sub2 cs_sub2] lrs_sub2].
  move => Hbbdiv.
  move : (IH g_sub2 ls2 g' (catrev (catrev (catrev cs cs_ge) cs_and) cs_sub2) (dropmsl (joinlsl lrs_ge qs)) lrs_sub2 cs' qlrs rlrs  Hbbdiv).
  move : (bit_blast_sub_size_ss Hbbsub2). move : (bit_blast_and_size_ss Hbband). 
  rewrite!size_dropmsl!size_joinlsl!addnK size_nseq. 
  move => Hszand Hszsub Hszdiv. rewrite -Hszand in Hszsub; last done. exact : (Hszdiv Hszqs (Hszsub Hszrs) ).
Qed.

Lemma bit_blast_udiv_size_ss : forall g ls1 ls2 g' cs qlrs rlrs ,
    bit_blast_udiv g ls1 ls2 = (g', cs, qlrs, rlrs) -> size ls1 = size ls2->
    (size qlrs = size ls2 /\ size rlrs = size ls2).
Proof.
  move => g ls1 ls2 g' cs qlrs rlrs .
  rewrite/bit_blast_udiv. case Hls2 : (ls2 == copy (size ls2) lit_ff).
  case => _ _ <- <-. move => Hsz . by rewrite size_nseq Hsz.
  move => Hbbudiv Hsz .
  have Hcopy1: size (copy (size ls1) lit_ff) = size ls2 by rewrite size_nseq Hsz.
  exact : (bit_blast_udiv_rec_size_ss Hbbudiv Hcopy1 Hcopy1 ). 
Qed.

Lemma bit_blast_udiv_rec_correct : forall g ls1 ls2 g' cs cs' lqs lrs qlrs rlrs E bs1 bs2 bsq bsr,
  bit_blast_udiv_rec g ls1 ls2 cs lqs lrs = (g', cs', qlrs, rlrs) ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  enc_bits E lqs bsq->
  enc_bits E lrs bsr ->
  interp_cnf E (add_prelude cs') ->
  enc_bits E qlrs (udivB_rec bs1 bs2 bsq bsr).1 /\
  enc_bits E rlrs (udivB_rec bs1 bs2 bsq bsr).2.
Proof.
  move => g ls1; move :g.
  elim ls1 => [|ls1_hd ls1_tl IH] g ls2 g' cs cs' lqs lrs qlrs rlrs E bs1 bs2 bsq bsr/=. 
  - case => _ _ <- <-.  move => Henc1 Henc2 Hencq Hencr Hcs.
    rewrite enc_bits_nil_l in Henc1. by rewrite (eqP Henc1)/= Hencq Hencr.
  - case Hbbuge : (bit_blast_uge g (dropmsl (joinlsl ls1_hd lrs)) ls2) => [[g_ge cs_ge] lrs_ge].
    case Hgett : (lrs_ge == lit_tt).
    case Hbbsub : (bit_blast_sub g_ge (dropmsl (joinlsl ls1_hd lrs)) ls2) => [[ge_sub cs_sub] lrs_sub].
    move => Hbbdiv Henc1 Henc2 Hencq Hencr Hcs. 
    move : (enc_bits_splitlsb (add_prelude_tt Hcs) Henc1) => /andP[Hls1hd Hls1tl].
    rewrite/= in Hls1tl.
Abort.

Variable div_pair :
  forall a b : Z, (0 < b)%Z -> { p:Z*Z | a = (p.1 * b + snd p)%Z}.
Definition dp (a b : Z):= { p:Z*Z | a = (p.1 * b + snd p)%Z /\ (0 <= p.2 < b)%Z}.
Definition bz := {b:Z|(0<b)%Z}. Check bz. Definition ga (b: bz):= let (a,_) := b in a. Check prod.
Definition div_pair' (a : Z) (x : {b:Z|(0<b)%Z}) : Z * Z :=
  match x with
  | exist b h => let (v, _) := div_pair a h in v
  end.
Extraction  div_pair.
Variable bb : Z. Variable bh: Prop.
Variable bc : Z -> Z -> Type.
Definition ss n:= sig (n<>1).
Eval compute in (div_pair' 1%Z (let bb:bz:= _ in bb)).
Check div_pair'.  Eval compute in (div_pair 0%Z Z.lt_0_1). 
     elim . intros. done.
    intros. rewrite addSn. rewrite-addn1. rewrite-addnA.
    apply H in H0.
    SearchAbout enc_bits.
    
Admitted.


Lemma bit_blast_udiv_correct g ls1 ls2 g' cs qlrs rlrs E bs1 bs2 :
  bit_blast_udiv g ls1 ls2 = (g', cs, qlrs, rlrs) ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E qlrs (udivB bs1 bs2).1 /\
  enc_bits E rlrs (udivB bs1 bs2).2.
Proof.
  rewrite/udivB/bit_blast_udiv.
  case Hzb: (bs2 == zeros (size bs2)); case Hzl: (ls2 == copy (size ls2) lit_ff).
  case => _ _ <- <-.
  intros. rewrite (enc_bits_size H)/=/zeros enc_bits_copy; first done. apply (add_prelude_enc_bit_ff H1).
  intros. rewrite (eqP Hzb) in H1. Search enc_bits.
  
Admitted.


Lemma mk_env_udiv_rec_is_bit_blast_udiv_rec E g ls1 ls2 i g' cs qlrs rlrs E' :
  mk_env_udiv_rec E g ls1 ls2 i = (E', g', cs, qlrs, rlrs) ->
  bit_blast_udiv_rec g ls1 ls2 i = (g', cs, qlrs, rlrs).
Proof.
Admitted.

