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

Lemma to_nat_take : forall n p, to_nat ((take n) p) = if n < size p then to_nat (from_nat n (to_nat p)) else to_nat p.
  elim => [| ns IH] p.
  rewrite take0/=.
  elim p => [| phd ptl IHm]; done.
  elim p => [| phd ptl IHm]; first done.
  rewrite to_nat_cons/=.
  case Hlt : (ns.+1 < (size ptl).+1); rewrite ltnS in Hlt. 
  rewrite odd_add odd_double oddb. rewrite (IH ptl) Hlt.
  case phd; first by rewrite/=uphalf_double. 
  by (rewrite/=3!add0n-3!muln2-div.divn2 div.mulnK; last done).
  by rewrite IH Hlt.
Qed.

Lemma to_nat_mulB p1 p2 : to_nat (mulB p1 p2) = to_nat (from_nat (size p1) (to_nat p1 * to_nat p2)).
Proof.
  rewrite/mulB/low size_full_mul to_nat_cat to_nat_zeros mul0n addn0 to_nat_take size_full_mul.
  case Hlt : (size p1 < size p1 + size p2).
  by rewrite to_nat_full_mul size_full_mul 3!to_nat_from_nat expnD Nats.modn_muln_modn_l. 
  rewrite to_nat_full_mul size_full_mul.
  have Hadd0 : size p1 = size p1 +0 by rewrite addn0. rewrite {1}Hadd0 ltn_add2l in Hlt.
  move/negP/negP: Hlt. rewrite-eqn0Ngt. move/eqP => Hlt. by rewrite Hlt addn0.
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

Lemma to_nat_shlB1 : forall (p: bits), to_nat (shlB1 p) = div.modn ((to_nat p).*2) (2^size p).
Proof. move => p. by rewrite /shlB1 to_nat_dropmsb to_nat_joinlsb size_joinlsb-subn1 addnK addn0-muln2.
Qed.

Lemma to_nat_shlBn:
  forall n k, k < n -> to_nat (shlB k (from_nat n 1) ) = 2 ^ k.
Proof.
Admitted.

Lemma shlB_dropmsb n (p: bits) : shlB n (dropmsb p) = dropmsb (shlB n p).
Proof.
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

Lemma udivB_rec0r : forall m n q r,  (udivB_rec m (zeros n) q r) = (addB (shlB (size m) q) (zext (size q - size m) (ones (size m))), addB (shlB (size m) r) (zext (size r - size m) (rev m))).
Proof. 
  elim => [|mhd mtl IH] n q r; rewrite/=. rewrite/rev/=!zext_nil!subn0!addB0 unzip1_zip; last by rewrite size_zeros. rewrite unzip1_zip; last by rewrite size_zeros. done.
  intros. rewrite to_nat_zeros/=subB0. 
  rewrite IH; first rewrite size_dropmsb size_joinlsb addnK. 
  rewrite /shlB1.
  assert ((dropmsb (joinlsb true q) <<# size mtl +# zext (size q - size mtl) (ones (size mtl)))%bits==(dropmsb (joinlsb false (q <<# size mtl)) +# zext (size q - (size mtl).+1) (b1 :: ones (size mtl)))%bits).
  rewrite shlB_dropmsb-to_nat_inj_ss; last by rewrite!size_addB!size_dropmsb!size_zext/=size_ones!QFBV.size_shlB size_joinlsb addnK -addn1 addnK; repeat rewrite-maxnE maxKn.
  rewrite 2!to_nat_addB 2!to_nat_zext/=to_nat_ones 2!to_nat_dropmsb to_nat_joinlsb. rewrite/shlB 2!shlB_mul2exp 2!to_nat_mulB addn0.  
  rewrite 2!size_addB 2!size_dropmsb 2!size_joinlsb 2!size_mulB size_joinlsb 2!size_zext-subn1 addnK/= size_ones-!maxnE !maxKn.
  rewrite !to_nat_from_nat.
  (*
  rewrite 2!div.modnMmr 2!div.modnDml. SearchAbout div.modn.
  rewrite -3!muln2. rewrite -mulnDr.*)
Admitted.
  
  
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
  


Lemma ltn_neq0 : forall n m, n < m -> (m != 0).
Proof.
  elim => [| ns IH] m/=. by rewrite lt0n.
  - intro. rewrite-(eqP (Nats.lt_sub1r_add1l ns m)) in H; apply (IH m.-1) in H.
    rewrite-lt0n (eqP (Nats.lt_sub1r_add1l 0 m)) in H. move : (ltn_trans (ltn0Sn 0) H). by rewrite lt0n.
Qed.

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

Lemma neq0_eq0_sizel : forall n (b : bits), b!=zeros (size b) -> from_nat n (to_nat b) == zeros n -> n < size b.
Proof.
  elim => [|ns IH] b/=; first by (rewrite-ltB0n eq_refl; move=> [Hneq Ht{Ht}]; exact (lt0B_size Hneq)).
  move=>[Hneq Heq]. move : (IH (droplsb b)) => Hm. rewrite-(eqP (Nats.lt_sub1r_add1l ns (size b)))-subn1-size_droplsb. apply Hm; last rewrite to_nat_droplsb.
  move : Hneq. rewrite-!to_nat_zero to_nat_droplsb-!lt0n half_gt0. move => Hgt0.
  case Hoddb: (odd (to_nat b)); first by rewrite Hoddb eqseq_cons andFb in Heq.
  rewrite Hoddb/joinlsb eqseq_cons andTb in Heq. rewrite Nats.ssrodd_odd-Nat.even_succ-Nat.negb_odd in Hoddb. move: (negbFE Hoddb)=>Hodd{Hoddb}. rewrite-Nats.ssrodd_odd in Hodd. rewrite-(ltn_add2r 1)2!addn1 in Hgt0. move : (odd_gt2 Hodd Hgt0)=> Hodd2.  move : (ltn_sub2r Hgt0 Hodd2). by rewrite!subn1/=. 
  rewrite eqseq_cons in Heq. move/andP : Heq=>[Hb0 Hzeq]. done.
Qed.

Print shlB_mul2exp.

Lemma to_nat_belast_0 : forall s, to_nat (belast false (zeros s)) = 0.
Proof.
  elim => [|ns IH]/=; first done. rewrite IH-muln2 mul0n; done.
Qed.

Lemma lt1_eq0 : forall (n:nat), n<1 -> n=0.
Proof. intros. induction n; try done.
Qed.


Lemma subB_joinmsb_dropmsb: forall b q n, size q = n.+1 -> (dropmsb (joinlsb b q) -# joinlsb b (zeros n))%bits = dropmsb (joinlsb false q).
Proof.
Admitted.
 (* 
Lemma udivB_rec1 : forall p s q r, p!=[::]->size r = s -> udivB_rec p (from_nat s 1) q r = (q, dropmsb (joinlsb (msb p) r)).
Proof.
  elim => [|ph pt IH]/=; first discriminate.
  move => s q r Hp Hsz.
  rewrite IH.
  move : Hsz. Print udivB_rec. case Hs : s=>[|ns]; rewrite/=. rewrite-zeros0 subB0. intros.
  move : (size0nil Hsz)=> Hrnil. rewrite Hrnil/joinlsb{2}/dropmsb/msb{-1}/dropmsb/=.
  (*(dropmsb (true :: q), [::]) = (q, [::])*) admit.
  rewrite from_natn0 to_nat_zeros-muln2 mul0n addn0. 
  case Hph : ph; rewrite/=; intro.
  destruct r; rewrite/=; first discriminate.
  rewrite subB_joinmsb_dropmsb; last done. rewrite/msb/=.
  
  
  (*(dropmsb (joinlsb true q),
  (dropmsb (joinlsb true (a :: r)) -# joinlsb true (zeros ns))%bits) = 
  (q, a :: r)*) admit.
  destruct r; first discriminate.
  case Hbr1 : (to_nat (dropmsb (joinlsb false (b :: r))) < 1).
  move/eqP: Hbr1. rewrite-addn1 addnK. move=> Hbr1.
  rewrite/=.
  (*(dropmsb (joinlsb false q), dropmsb (joinlsb false (b :: r))) = (q, b :: r)*) admit.
  rewrite/=. 
  (*(dropmsb (joinlsb true q),
  (dropmsb (joinlsb false (b :: r)) -# joinlsb true (zeros ns))%bits) = 
  (q, b :: r)*)
  admit.
  case Hlt : (to_nat (dropmsb (joinlsb ph r)) < to_nat (s) -bits of (1)%bits); rewrite/=.
  by rewrite size_dropmsb size_joinlsb addnK Hsz.
  by rewrite QFBV.size_subB size_dropmsb size_joinlsb addnK Hsz size_from_nat minnn.
*)

  
Lemma udivB1: forall p, udivB p (from_nat (size p) 1) = (p, from_nat (size p) 0).
Proof.
  elim=>[| ph pt IH]/=; first done. 
  rewrite/udivB!from_natn0 to_nat_joinlsb to_nat_zeros-muln2 mul0n add0n.
  rewrite-from_natn0 -from_nat_bounded_eq; [|by rewrite/=Nats.expn2_gt1|by rewrite Nats.expn2_gt0].
  rewrite/udivB in IH.
  rewrite/=!from_natn0 to_nat_zeros-!muln2 mul0n addn0 to_nat_belast_0 mul0n addn0. 
  case ph; rewrite/=.
Admitted.
  
Lemma shrB_div2exp:  forall i p , (iter i shrB1 p, from_nat (size p) 0) = udivB p (from_nat (size p) (2^ i)%nat).
Proof.
Admitted.
  
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

(*
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
*)

Fixpoint bit_blast_udiv_rec g ls1 ls2 qs rs :  generator * cnf * word * word :=
  match ls1 with
  | [::] => (g, [::], qs, rs)
  | ls1_hd :: ls1_tl =>
    let '(g_tl, cs_tl, lrs_tl, lqs_tl) := bit_blast_udiv_rec g ls1_tl ls2 qs rs in
    let di := dropmsl (joinlsl ls1_hd lrs_tl) in
    let '(g_hd, cs_hd, lrs_hd) := bit_blast_uge g_tl di ls2 in
    let qi := dropmsl (joinlsl lrs_hd lqs_tl) in
    if (lrs_hd == lit_tt) then
      let '(g_sub, cs_sub, lrs_sub) := bit_blast_sub g_hd di ls2 in
      (g_sub, (catrev (catrev cs_tl cs_hd) cs_sub), qi, lrs_sub)
    else if (lrs_hd == lit_ff) then
           (g_hd, catrev cs_tl cs_hd, qi, di)
         else let '(g_and, cs_and, lrs_and) := bit_blast_and g_hd (copy (size ls2) lrs_hd) ls2 in
              let '(g_sub2, cs_sub2, lrs_sub2) := bit_blast_sub g_and di lrs_and in
              (g_sub2, (catrev (catrev (catrev cs_tl cs_hd) cs_and) cs_sub2), qi, lrs_sub2)
  end.

              
 
Definition bit_blast_udiv g ls1 ls2 :=
  if ls2 == copy (size ls2) lit_ff then
    (g, [::], copy (size ls1) lit_ff, ls1)
    else
      bit_blast_udiv_rec g ls1 ls2 (copy (size ls1) lit_ff) (copy (size ls1) lit_ff).


Fixpoint mk_env_udiv_rec (E: env) (g:generator) ls1 ls2 qs rs : env * generator * cnf * word * word :=
  match ls1 with
  | [::] => (E, g, [::], qs, rs)
  | ls1_hd :: ls1_tl =>
    let '(E_tl, g_tl, cs_tl, lrs_tl, lqs_tl) := mk_env_udiv_rec E g ls1_tl ls2 qs rs in
    let di := dropmsl (joinlsl ls1_hd lrs_tl) in
    let '(E_hd, g_hd, cs_hd, lrs_hd) := mk_env_uge E_tl g_tl di ls2 in
    let qi := dropmsl (joinlsl lrs_hd lqs_tl) in
    if (lrs_hd == lit_tt) then
      let '(E_sub, g_sub, cs_sub, lrs_sub) := mk_env_sub E_hd g_hd di ls2 in
      (E_sub, g_sub, (catrev (catrev cs_tl cs_hd) cs_sub), qi, lrs_sub)
    else if (lrs_hd == lit_ff) then
           (E_hd, g_hd, catrev cs_tl cs_hd, qi, di)
         else let '(E_and, g_and, cs_and, lrs_and) := mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2 in
              let '(E_sub2, g_sub2, cs_sub2, lrs_sub2) := mk_env_sub E_and g_and di lrs_and in
              (E_sub2, g_sub2, (catrev (catrev (catrev cs_tl cs_hd) cs_and) cs_sub2), qi, lrs_sub2)
  end.

Definition mk_env_udiv E g ls1 ls2 :=
  if ls2 == copy (size ls2) lit_ff then
    (E, g, [::], copy (size ls1) lit_ff, ls1)
    else
      mk_env_udiv_rec E g ls1 ls2 (copy (size ls1) lit_ff) (copy (size ls1) lit_ff).

Lemma bit_blast_sub_size_ss : forall g ls1 ls2 g' cs' lrs,
    bit_blast_sub g ls1 ls2  = (g', cs', lrs) -> size ls1 = size ls2 -> size lrs = size ls2.
Proof.
  move => g ls1 ls2 g' cs lrs. rewrite/bit_blast_sub.
  case Hbbneg : (BBNeg.bit_blast_neg g ls2) => [[g_neg cs_neg] lrs_neg].
  case Hbbadd : (bit_blast_add g_neg ls1 lrs_neg) => [[ g_add cs_add] lrs_add].
  case => _ _ <- Hsz12. move: (bit_blast_neg_size_ss Hbbneg)=>Hszneg; rewrite Hszneg in Hsz12. rewrite-( bit_blast_add_size_ss Hbbadd Hsz12). by rewrite Hszneg Hsz12.
Qed.

Lemma bit_blast_udiv_rec_size_ss : forall g ls1 ls2 g' qs rs cs' qlrs rlrs  ,
    bit_blast_udiv_rec g ls1 ls2 qs rs = (g', cs', qlrs, rlrs) ->
    (*size ls1 = size ls2 -> *) size qs = size ls2 -> size rs = size ls2 ->
    (*enc_bits E ls1 bs1 ->  enc_bits E ls2 bs2 ->*) (size qlrs = size ls2 /\ size rlrs = size ls2).
Proof.
  move => g ls1; move : g.
  elim ls1 => [|ls1hd ls1tl IH] g ls2 g' qs rs cs' qlrs rlrs  Hbbdiv Hszqs Hszrs ; move : Hbbdiv; rewrite/bit_blast_udiv/=.
  case => _ _ <- <-; done.
  case Hbbdiv : (bit_blast_udiv_rec g ls1tl ls2 qs rs) => [[[g_tl cs_tl] lrs_tl] lqs_tl].
  case Hbbuge: (bit_blast_uge g_tl (dropmsl (joinlsl ls1hd lrs_tl)) ls2)=> [[g_hd cs_hd] lrs_hd].
  move : (IH _ _ _ _ _ _ _ _ Hbbdiv Hszqs Hszrs) => [Hszlrstl Hszlqstl].
  case Hhdtt : (lrs_hd == lit_tt).
  case Hbbsub : (bit_blast_sub g_hd (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[g_sub cs_sub] lrs_sub].
  case => _ _ <- <-. rewrite size_dropmsl size_joinlsl addnK.
  have Hszlrstl' :size (dropmsl (joinlsl ls1hd lrs_tl)) = size ls2 by rewrite size_dropmsl size_joinlsl addnK Hszlrstl.
  by rewrite Hszlqstl (bit_blast_sub_size_ss Hbbsub Hszlrstl'). 
  case Hhdff :(lrs_hd == lit_ff).
  case => _ _ <- <-. by rewrite !size_dropmsl !size_joinlsl !addnK. 
  case Hbband : (bit_blast_and g_hd (copy (size ls2) lrs_hd) ls2) => [[g_and cs_and] lrs_and].
  case Hbbsub2 : (bit_blast_sub g_and (dropmsl (joinlsl ls1hd lrs_tl)) lrs_and)=> [[g_sub2 cs_sub2] lrs_sub2].
  case => _ _ <- <-. rewrite size_dropmsl size_joinlsl addnK.
  have Hszlrstl' :size (dropmsl (joinlsl ls1hd lrs_tl)) = size lrs_and by (rewrite size_dropmsl size_joinlsl addnK Hszlrstl -(bit_blast_and_size_ss Hbband); rewrite size_nseq).
  by rewrite (bit_blast_sub_size_ss Hbbsub2 Hszlrstl') Hszlqstl -Hszlrstl' size_dropmsl size_joinlsl addnK Hszlrstl. 
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

Lemma bit_blast_udiv_rec_correct : forall g ls1 ls2 g' cs' lqs lrs qlrs rlrs E bs1 bs2 bsq bsr,
  bit_blast_udiv_rec g ls1 ls2 lqs lrs = (g', cs', qlrs, rlrs) ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  enc_bits E lqs bsq->
  enc_bits E lrs bsr ->
  interp_cnf E (add_prelude cs') ->
  enc_bits E qlrs (udivB_rec bs1 bs2 bsq bsr).1 /\
  enc_bits E rlrs (udivB_rec bs1 bs2 bsq bsr).2.
Proof.
  move => g ls1; move :g.
  elim ls1 => [|ls1_hd ls1_tl IH] g ls2 g' cs' lqs lrs qlrs rlrs E bs1 bs2 bsq bsr/=. 
  - case => _ _ <- <-.  move => Henc1 Henc2 Hencq Hencr Hcs.
    rewrite enc_bits_nil_l in Henc1. by rewrite (eqP Henc1)/= Hencq Hencr.
  -
    case Hbbudiv : (bit_blast_udiv_rec g ls1_tl ls2 lqs lrs) => [[[g_tl cs_tl] lqs_tl] lrs_tl].
    case Hbbuge : (bit_blast_uge g_tl (dropmsl (joinlsl ls1_hd lqs_tl)) ls2) => [[g_ge cs_ge] lrs_ge].
    case Hgett : (lrs_ge == lit_tt).
    case Hbbsub : (bit_blast_sub g_ge (dropmsl (joinlsl ls1_hd lqs_tl)) ls2) => [[ge_sub cs_sub] lrs_sub].
    case => _ <- <- <-.
    move => Henc1 Henc2 Hencq Hencr Hcs. 
    move : (enc_bits_splitlsb (add_prelude_tt Hcs) Henc1) => /andP[Hls1hd Hls1tl].
    rewrite/= in Hls1tl. 
    move : (add_prelude_tt Hcs) => Htt.
    have Hencsubls1: (enc_bits E (dropmsl (joinlsl ls1_hd lrs)) (dropmsb (joinlsb (lsb bs1) bsr))).
    apply (enc_bits_dropmsb Htt). rewrite enc_bits_joinlsb Hencr.
    move : (enc_bits_lsl Htt Henc1); rewrite/lsl/=; move => Henc1hd. by rewrite Henc1hd.
    
Admitted.

Lemma enc_bits_ff : forall E cs n, interp_cnf E (add_prelude cs) -> enc_bits E (copy n lit_ff) (zeros n).
Proof.
  intros. apply enc_bits_copy. apply add_prelude_enc_bit_ff with cs. done.
Qed.
  
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
  intros. rewrite (enc_bits_size H)/=(eqP Hzb) to_nat_zeros/=from_natn0 eq_refl enc_bits_copy; first done. apply (add_prelude_enc_bit_ff H1).
  intros. rewrite (eqP Hzb) in H1. rewrite (eqP Hzb) to_nat_zeros from_natn0 eq_refl/=.
  move : (enc_bits_ff (size ls1) H2) => Hff.
  move : (bit_blast_udiv_rec_correct H H0 H1 Hff Hff H2).
  move : (enc_bits_ff (size bs2) H2)=> Hencff. move : (enc_bits_size H0)=> Hencsz1. move : (enc_bits_size H1)=> Hencsz2. rewrite size_zeros in Hencsz2.
  rewrite Hencsz1 udivB_rec0r size_zeros subnn !zext0. 
Admitted.

Lemma mk_env_udiv_rec_is_bit_blast_udiv_rec: forall ls1 E g ls2 lq lr g' cs qlrs rlrs E',
  mk_env_udiv_rec E g ls1 ls2 lq lr = (E', g', cs, qlrs, rlrs) ->
  bit_blast_udiv_rec g ls1 ls2 lq lr = (g', cs, qlrs, rlrs).
Proof.
  elim => [| ls1hd ls1tl IH] E g ls2 lq lr g' cs qlrs rlrs E'.
  - rewrite/=. by case => _ <- <- <- <-.
  - rewrite/=.
    dcase (mk_env_udiv_rec E g ls1tl ls2 lq lr) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_uge E_tl g_tl (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lrs_tl)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    rewrite (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv) (mk_env_uge_is_bit_blast_uge Hmkuge) (mk_env_sub_is_bit_blast_sub Hmksub) (mk_env_and_is_bit_blast_and Hmkand) (mk_env_sub_is_bit_blast_sub Hmksub2). 
    case (lrs_hd == lit_tt); case (lrs_hd == lit_ff); by  move => [] _<- <- <- <-.
Qed.


Lemma mk_env_udiv_is_bit_blast_udiv : forall ls1 E g ls2 g' cs qlrs rlrs E',
  mk_env_udiv E g ls1 ls2 = (E', g', cs, qlrs, rlrs) ->
  bit_blast_udiv g ls1 ls2  = (g', cs, qlrs, rlrs).
Proof.
  rewrite/mk_env_udiv/bit_blast_udiv/=. move => ls1 E g ls2 g' cs qlrs rlrs E'.
  case (ls2 == copy (size ls2) lit_ff). by case => _ <- <- <- <- .
  apply (mk_env_udiv_rec_is_bit_blast_udiv_rec ).
Qed.

Lemma mk_env_udiv_rec_newer_gen :
  forall ls1 E g ls2 lq lr E' g' cs lqs lrs,
    mk_env_udiv_rec E g ls1 ls2 lq lr = (E', g', cs, lqs, lrs) ->
    (g <=? g')%positive.
Proof.
  elim  => [| ls1hd ls1tl IH] E g ls2 lq lr E' g' cs lqs lrs.
  - move => [] _ <- _ _ _. exact: Pos.leb_refl.
  - rewrite/=.
    dcase (mk_env_udiv_rec E g ls1tl ls2 lq lr) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_uge E_tl g_tl (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lrs_tl)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv) => Hgg0.
    move : (mk_env_uge_newer_gen Hmkuge) => Hg0g1.
    move : (mk_env_sub_newer_gen Hmksub) => Hg1g2.
    move : (mk_env_and_newer_gen Hmkand) => Hg1g3.
    move : (mk_env_sub_newer_gen Hmksub2) => Hg3g4.
    move : (pos_leb_trans Hgg0  Hg0g1) => Hgg1.
    move : (pos_leb_trans Hgg0 (pos_leb_trans Hg0g1 Hg1g2)) => Hgg2.
    move : (pos_leb_trans (pos_leb_trans Hgg0 Hg0g1) (pos_leb_trans Hg1g3 Hg3g4)) => Hgg4.
    case (lrs_hd == lit_tt); case (lrs_hd == lit_ff); (move => [] _ <- _ _ _; try exact).
Qed.

Lemma mk_env_udiv_newer_gen :
  forall ls1 E g ls2 E' g' cs lqs lrs,
    mk_env_udiv E g ls1 ls2 = (E', g', cs, lqs, lrs) ->
    (g <=? g')%positive.
Proof.
  rewrite/mk_env_udiv/bit_blast_udiv/=. move => ls1 E g ls2 E' g' cs qlrs rlrs .
  case (ls2 == copy (size ls2) lit_ff). case => _ <- _ _ _ . exact: Pos.leb_refl.
  apply (mk_env_udiv_rec_newer_gen).
Qed.

Lemma mk_env_udiv_rec_newer_res :
  forall ls1 E g ls2 lq lr E' g' cs lqs lrs,
    mk_env_udiv_rec E g ls1 ls2 lq lr = (E', g', cs, lqs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_lits g lq ->
    newer_than_lits g lr ->
    newer_than_lits g' lrs && newer_than_lits g' lqs.
Proof.
  elim  => [| ls1hd ls1tl IH] E g ls2 lq lr E' g' cs lqs lrs.
  - rewrite /=. case => _ <- _ <- <-.  move => Htt Hls1 Hls2 Hlq Hlr. by rewrite Hlq Hlr.
  - rewrite/=.
    dcase (mk_env_udiv_rec E g ls1tl ls2 lq lr) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_uge E_tl g_tl (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lrs_tl)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    move => Hres Htt Hls1 Hls2 Hlq Hlr.  move/andP: Hls1 => [Hls1hd Hls1tl].
    move/andP : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv Htt Hls1tl Hls2 Hlq Hlr) => [Hg0lq Hg0lr].
    move : (mk_env_uge_newer_res Hmkuge) => Hg1ls2.
    move : (mk_env_sub_newer_res Hmksub) => Hg2ls3.
    move : (mk_env_sub_newer_res Hmksub2) => Hg4ls5. 
    generalize Hres.
    move : (mk_env_uge_newer_gen Hmkuge) => Hg0g1.
    move : (mk_env_sub_newer_gen Hmksub) => Hg1g2.
    move : (pos_leb_trans Hg0g1  Hg1g2) => Hg0g2.
    move : (mk_env_and_newer_gen Hmkand) => Hg1g3.
    move : (mk_env_sub_newer_gen Hmksub2) => Hg3g4.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv) => Hgg0.
    move : (pos_leb_trans Hgg0  Hg0g1) => Hgg1.
    move : (pos_leb_trans Hg0g1 (pos_leb_trans Hg1g3 Hg3g4)) => Hg0g4.
    move : (pos_leb_trans Hg1g3 Hg3g4) => Hg1g4.
    move : (newer_than_lit_le_newer Hg1ls2 Hg1g2) => Hg5ls6.
    move : (newer_than_lits_le_newer Hg0lq Hg0g2) => Hg6ls7.
    move : (newer_than_lits_le_newer Hg0lq Hg0g4) => Hg7ls8.
    move : (newer_than_lit_le_newer Hg1ls2 Hg1g4) => Hg8ls9.
    move : (newer_than_lits_le_newer Hg0lr Hg0g1) => Hg0ls0.
    move : (newer_than_lit_le_newer Hls1hd Hgg1) => Hg9ls0.
    move : (newer_than_lits_le_newer Hg0lq Hg0g1) => Hg1ls1.
    case (lrs_hd == lit_tt); case (lrs_hd == lit_ff); move => [] _ <- _ <- <-;
    [rewrite Hg2ls3 andTb newer_than_lits_dropmsl; last rewrite newer_than_lits_joinlsl; done|rewrite Hg2ls3 andTb newer_than_lits_dropmsl; last rewrite newer_than_lits_joinlsl; done|auto|rewrite Hg4ls5 andTb newer_than_lits_dropmsl; last rewrite newer_than_lits_joinlsl;  done].
    rewrite newer_than_lits_dropmsl; last rewrite newer_than_lits_joinlsl; try done.
    rewrite andTb newer_than_lits_dropmsl; last rewrite newer_than_lits_joinlsl; done.
Qed.

Lemma mk_env_udiv_newer_res :
  forall ls1 E g ls2 E' g' cs lqs lrs,
    mk_env_udiv E g ls1 ls2  = (E', g', cs, lqs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_lits g' lrs && newer_than_lits g' lqs.
Proof.
  rewrite/mk_env_udiv/bit_blast_udiv/=. move => ls1 E g ls2 E' g' cs qlrs rlrs .
  case (ls2 == copy (size ls2) lit_ff). case => _ <- _ <- <- . move => Htt Hls1 Hls2.
  rewrite  Hls1 andTb newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff; done. 
  move => Hmk Htt Hls1 Hls2.  apply (mk_env_udiv_rec_newer_res Hmk Htt Hls1 Hls2); rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff; done.
Qed.

Lemma mk_env_udiv_rec_newer_cnf :
  forall ls1 E g ls2 lq lr E' g' cs lqs lrs,
    mk_env_udiv_rec E g ls1 ls2 lq lr = (E', g', cs, lqs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_lits g lq ->
    newer_than_lits g lr ->
    size lq = size ls2 -> size lr = size ls2 ->
    newer_than_cnf g' cs.
Proof.
    elim  => [| ls1hd ls1tl IH] E g ls2 lq lr E' g' cs lqs lrs.
  - rewrite /=. case => _ <- <- _ _.  move => Htt Hls1 Hls2 Hlq Hlr Hszq Hszr. done. 
  - rewrite/=.
    dcase (mk_env_udiv_rec E g ls1tl ls2 lq lr) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_uge E_tl g_tl (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lrs_tl)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    move => Hres Htt Hls1 Hls2 Hlq Hlr Hszq Hszr.  move/andP: Hls1 => [Hls1hd Hls1tl].
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv Htt Hls1tl Hls2 Hlq Hlr Hszq Hszr) => Hg0cs0.

    move : (mk_env_uge_newer_gen Hmkuge) => Hg0g1.
    move : (mk_env_sub_newer_gen Hmksub) => Hg1g2.
    move : (pos_leb_trans Hg0g1  Hg1g2) => Hg0g2.
    move : (mk_env_and_newer_gen Hmkand) => Hg1g3.
    move : (mk_env_sub_newer_gen Hmksub2) => Hg3g4.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv) => Hgg0.
    move : (pos_leb_trans Hgg0  Hg0g1) => Hgg1.
    move : (pos_leb_trans Hg0g1 (pos_leb_trans Hg1g3 Hg3g4)) => Hg0g4.
    move : (pos_leb_trans Hg1g3 Hg3g4) => Hg1g4.
    move: (newer_than_lit_le_newer Htt Hgg1) => Httg1. rewrite newer_than_lit_tt_ff in Httg1.
    move/andP : (mk_env_udiv_rec_newer_res Hmkudiv Htt Hls1tl Hls2 Hlq Hlr) => [Hlqstl Hlrstl].
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl (newer_than_lit_le_newer Hls1hd Hgg1) (newer_than_lits_le_newer Hlrstl Hg0g1))) => Hdj.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl (newer_than_lit_le_newer Hls1hd Hgg0) Hlrstl)) => Hdjtl.
    move : (newer_than_lits_le_newer Hls2 Hgg1) => Hg1ls2hd.
    move : (bit_blast_udiv_rec_size_ss (mk_env_udiv_rec_is_bit_blast_udiv_rec Hmkudiv) Hszq Hszr) => [Hszrtl Hszqtl].
    have Hszdj : (size (dropmsl (joinlsl ls1hd lrs_tl)) = size ls2) by rewrite size_dropmsl size_joinlsl addnK Hszrtl.
    move : (mk_env_sub_newer_cnf Hmksub Httg1 Hdj Hg1ls2hd Hszdj) => Hg2ls3.
    move : (newer_than_cnf_le_newer Hg0cs0 Hg0g2) => Hg2cs0.
    move : (mk_env_uge_newer_cnf Hmkuge (newer_than_lit_le_newer Htt Hgg0) Hdjtl (newer_than_lits_le_newer Hls2 Hgg0)) => Hg1cs2.
    move : (mk_env_uge_newer_res Hmkuge) => Hg1cs1.
    move : (newer_than_cnf_le_newer Hg1cs2 Hg1g2) => Hg2cs2.
    move : (mk_env_and_newer_res Hmkand (newer_than_lit_le_newer Htt Hgg1) (newer_than_lits_copy (size ls2) Hg1cs1) (newer_than_lits_le_newer Hls2 Hgg1)) => Hg3ls3.
    move : (mk_env_sub_newer_cnf Hmksub2 (newer_than_lit_le_newer Httg1 Hg1g3) (newer_than_lits_le_newer Hdj Hg1g3) Hg3ls3) => Hg4cs5. rewrite Hszdj in Hg4cs5.
    move : (mk_env_and_newer_cnf Hmkand (newer_than_lit_le_newer Htt Hgg1) (newer_than_lits_copy (size ls2) Hg1cs1) (newer_than_lits_le_newer Hls2 Hgg1)) => Hg3cs3.

    generalize Hres.
    case (lrs_hd == lit_tt); case (lrs_hd == lit_ff); move => [] _ <- <- _ _; rewrite !newer_than_cnf_catrev; try by rewrite Hg2ls3 Hg2cs0 Hg2cs2.
      by rewrite Hg1cs2 (newer_than_cnf_le_newer Hg0cs0  Hg0g1).
      rewrite (newer_than_cnf_le_newer Hg3cs3 Hg3g4) (newer_than_cnf_le_newer Hg0cs0 Hg0g4) (newer_than_cnf_le_newer Hg1cs2 Hg1g4) Hg4cs5; first done.
      rewrite -(bit_blast_and_size_ss (mk_env_and_is_bit_blast_and Hmkand)); by rewrite size_nseq.
Qed.

Lemma mk_env_udiv_newer_cnf :
  forall ls1 E g ls2 E' g' cs lqs lrs,
    mk_env_udiv E g ls1 ls2 = (E', g', cs, lqs, lrs) ->
    newer_than_lit g lit_tt ->
    size ls1 = size ls2 ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  rewrite/mk_env_udiv/bit_blast_udiv/=. move => ls1 E g ls2 E' g' cs qlrs rlrs .
  case (ls2 == copy (size ls2) lit_ff). case => _ <- <- _ _. move => Htt Hsz Hls1 Hls2. done.
  move => Hmk Htt Hsz Hls1 Hls2.  apply (mk_env_udiv_rec_newer_cnf Hmk Htt Hls1 Hls2); try (rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff; done); by rewrite size_nseq Hsz.
Qed.

Lemma mk_env_udiv_rec_preserve :
  forall ls1 E g ls2 lq lr E' g' cs lqs lrs,
    mk_env_udiv_rec E g ls1 ls2 lq lr = (E', g', cs, lqs, lrs) ->
    env_preserve E E' g.
Proof.
  elim => [|ls1hd ls1tl IH] E g ls2 lq lr E' g' cs lqs lrs.
  - by case => <- _ _ _. 
  - rewrite/=.
    dcase (mk_env_udiv_rec E g ls1tl ls2 lq lr) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_uge E_tl g_tl (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lrs_tl)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    move => Hres .  
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv ) => HEE0g.
    move : (mk_env_uge_preserve Hmkuge) => HE0E1g0.
    move : (mk_env_sub_preserve Hmksub) => HE1E2g1.
    move : (mk_env_and_preserve Hmkand) => HE1E3g1.
    move : (mk_env_sub_preserve Hmksub2) => HE3E4g3.
    move : (mk_env_uge_newer_gen Hmkuge) => Hg0g1.
    move : (mk_env_sub_newer_gen Hmksub) => Hg1g2.
    move : (pos_leb_trans Hg0g1  Hg1g2) => Hg0g2.
    move : (mk_env_and_newer_gen Hmkand) => Hg1g3.
    move : (mk_env_sub_newer_gen Hmksub2) => Hg3g4.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv) => Hgg0.
    move : (pos_leb_trans Hgg0  Hg0g1) => Hgg1.
    move : (pos_leb_trans Hg0g1 (pos_leb_trans Hg1g3 Hg3g4)) => Hg0g4.
    move : (pos_leb_trans Hg1g3 Hg3g4) => Hg1g4.
    move : (env_preserve_trans HEE0g (env_preserve_le HE0E1g0 Hgg0)) => HEE1g.
    move : (env_preserve_trans HEE1g (env_preserve_le HE1E2g1 Hgg1)) => HEE2g.
    move : (env_preserve_trans HEE1g (env_preserve_le HE1E3g1 Hgg1 )) => HEE3g.
    move : (env_preserve_trans HEE3g (env_preserve_le HE3E4g3 (pos_leb_trans Hgg1 Hg1g3))) => HEE4g.
    generalize Hres.
    case (lrs_hd == lit_tt); case (lrs_hd == lit_ff); move => [] <- _ _ _ _; try done.
Qed.

Lemma mk_env_udiv_preserve :
  forall E g ls1 ls2 E' g' cs lqs lrs,
    mk_env_udiv E g ls1 ls2 = (E', g', cs, lqs, lrs) ->
    env_preserve E E' g.
Proof.
  move => E g ls1 ls2 E' g' cs lqs lrs.
  rewrite /mk_env_udiv.
  case (ls2 == copy (size ls2) lit_ff). case => <- _ _ _ _. done. move => Hmk.
  apply (mk_env_udiv_rec_preserve Hmk).
Qed.

Lemma mk_env_udiv_rec_sat :
  forall ls1 E g ls2 lq lr E' g' cs lqs lrs,
    mk_env_udiv_rec E g ls1 ls2 lq lr = (E', g', cs, lqs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  elim => [|ls1hd ls1tl IH] E g ls2 lq lr E' g' cs lqs lrs.
  - by case => _ _ <- _ _ _ _.
  - rewrite/=.
    dcase (mk_env_udiv_rec E g ls1tl ls2 lq lr) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_uge E_tl g_tl (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lrs_tl)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    move => Hres Htt Hls1 Hls2. move/andP : Hls1 => [Hls1hd Hls1tl].
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv Htt Hls1tl Hls2 ) => HE0cs0.
    move : (mk_env_uge_newer_gen Hmkuge) => Hg0g1.
    move : (mk_env_sub_newer_gen Hmksub) => Hg1g2.
    move : (pos_leb_trans Hg0g1  Hg1g2) => Hg0g2.
    move : (mk_env_and_newer_gen Hmkand) => Hg1g3.
    move : (mk_env_sub_newer_gen Hmksub2) => Hg3g4.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv) => Hgg0.
    move : (pos_leb_trans Hgg0  Hg0g1) => Hgg1.
    move : (pos_leb_trans Hg0g1 (pos_leb_trans Hg1g3 Hg3g4)) => Hg0g4.
    move : (pos_leb_trans Hg1g3 Hg3g4) => Hg1g4.
    move : (mk_env_uge_sat Hmkuge (newer_than_lit_le_newer Htt Hgg0)).
Admitted.