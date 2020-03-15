From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBConst BBAnd BBAdd BBShl BBSub BBMul BBLshr BBUge BBEq BBNot BBIte.
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

From Coq Require List.
About div.divn.

(* Lemmas *)

(* Lemma dropmsb_zeros : forall n, dropmsb (zeros n) = zeros n.-1. *)
(* Proof. *)
(*   move => n. case n. done. *)
(*   move => n0. have->:(zeros n0.+1.-1=zeros n0) by rewrite-addn1-subn1 addnK. *)
(*   by rewrite-zeros_rcons/dropmsb/=belastd_rcons.  *)
(* Qed. *)


(* Lemma to_nat_joinlsb a n : to_nat (joinlsb a n) = (to_nat n).*2 + a. *)
(* Proof. by rewrite addnC. Qed. *)

(* Lemma to_nat_droplsb n: to_nat (droplsb n) = (to_nat n)./2. *)
(* Proof. elim n=>[|nhd ntl IH]/=. done.  *)
(*        rewrite -div.divn2 div.divnDr. case nhd ; (rewrite/= div.divn_small; last done). *)
(*        rewrite add0n; by rewrite -!muln2 div.mulnK.  *)
(*        rewrite add0n; by rewrite -!muln2 div.mulnK. *)
(*        rewrite div.dvdn2 odd_double; done. *)
(* Qed.        *)



(* Lemma to_nat_joinmsb a n : to_nat (joinmsb n a) = a * 2^(size n) + to_nat n. *)
(* Proof. *)
(*   move : a. elim n=>[|nhd ntl IH]a/=. by rewrite -muln2 mul0n !addn0 expn0 muln1.  *)
(*   rewrite (IH a) -!muln2 mulnDl expnS; ring.  *)
(* Qed. *)

(* Lemma to_nat_dropmsb n : to_nat (dropmsb (n)) = div.modn (to_nat n) (2^(size n).-1). *)
(* Proof. *)
(*   rewrite-(revK n). case (rev n); first by rewrite/= div.modn1. *)
(*   intros. rewrite/dropmsb/splitmsb/=rev_cons belastd_rcons size_rcons. *)
(*   have->:((size (rev l)).+1.-1=size (rev l)) by rewrite-addn1-subn1 addnK. *)
(*   case b; rewrite to_nat_rcons. *)
(*   - by rewrite mul1n-div.modnDmr div.modnn addn0 (div.modn_small (to_nat_bounded (rev l))). *)
(*   - by rewrite mul0n addn0 (div.modn_small (to_nat_bounded (rev l))). *)
(* Qed. *)


(* Lemma not_zero_to_nat (q : bits) : (q == zeros (size q))=false -> (to_nat q == 0)=false.   *)
(* Proof. *)
(*   intro. apply negbT in H; rewrite -ltB0n ltB_to_nat/= in H. *)
(*   apply/eqP. rewrite Nat.neq_0_lt_0. apply (Nats.ltn_lt H). *)
(* Qed. *)
(* Print div.divn_mulAC. *)

(* Lemma full_mul0n: forall m n, full_mul (zeros m) n = zeros (m + (size n)). *)
(* Proof. *)
(*   elim => [|ms IH]n /=. by rewrite from_natn0. *)
(*   by rewrite (IH n)/joinlsb.  *)
(* Qed. *)
  
(* Lemma full_muln0: forall n m, full_mul n (zeros m) = zeros ((size n) + m). *)
(* Proof. *)
(*   elim=>[| nhd ntl IH] m/=. by rewrite from_natn0 size_zeros. *)
(*   case nhd; rewrite (IH m); first by rewrite zext_zero addB0 unzip1_zip; [ done | by rewrite size_zeros].  *)
(*   done.   *)
(* Qed. *)
  
(* Lemma mul0B n m: mulB (zeros m) n = zeros m. *)
(* Proof. *)
(*   rewrite/mulB full_mul0n/low!size_zeros subnDA subnn sub0n cats0-zeros_cats take_size_cat; [ done | by rewrite size_zeros]. Qed. *)

(* Lemma mulB_nil_l n : mulB [::] n = [::]. *)
(* Proof. by rewrite/mulB/low/= take0. Qed. *)

(* Lemma full_mul_nil_r n : full_mul n [::]= zeros (size n). *)
(* Proof. *)
(*   elim n. done. intros. rewrite/=. case a. rewrite H zext_nil addB0 unzip1_zip; last by rewrite size_joinlsb. done. *)
(*   by rewrite H. *)
(* Qed. *)

(* Lemma mulB_nil_r n : mulB n [::] = zeros (size n). *)
(* Proof.  rewrite/mulB full_mul_nil_r/low size_zeros subnn cats0 take_oversize; last by rewrite size_zeros. done. Qed. *)

(* Lemma zip_nil_r S T (p:seq S) : @zip S T p [::] = [::]. *)
(* Proof. *)
(*   case p; done. Qed. *)

(* Lemma full_adder_zip_0_l : forall p n, (full_adder_zip false (zip (zeros n) p)).2 = unzip2 (zip (zeros n) p). *)
(* Proof. *)
(*   intros. generalize dependent p. elim n => [|ns IH] p/=. *)
(*   by rewrite zip_nil.  *)
(*   elim p => [|phd ptl IH1]/=. done. *)
(*   case phd; *)
(*   case Hfadd : (full_adder_zip false (zip (zeros ns) ptl))=>[c tl]/=; *)
(*   by rewrite -(IH ptl) Hfadd. *)
(* Qed. *)
  
(* Lemma add0B : forall p n, addB (zeros n) p = unzip2 (zip (zeros n) p). *)
(* Proof. *)
(*   rewrite /addB/adcB/full_adder.  exact : full_adder_zip_0_l. *)
(* Qed. *)

(* Lemma to_nat_from_nat_bounded : forall n m, m < 2^n -> to_nat (from_nat n m) = m. *)
(* Proof. *)
(*   elim => [|ns IH] m /=. symmetry; rewrite-Nat.lt_1_r; rewrite expn0 in H; by apply Nats.ltn_lt. move => Hlt. *)
(*   rewrite(IH m./2); last (rewrite expnS Nats.muln_mul in Hlt; rewrite -div.divn2 Nats.divn_div; apply (Nats.lt_ltn (Nat.div_lt_upper_bound m 2 (2^ns)(Nat.neq_succ_0 1) (ltP Hlt)))). *)
(*   case Hodd: (odd m). *)
(*   - by rewrite -Hodd odd_double_half.  *)
(*   - rewrite add0n-div.divn2-muln2 div.divnK; first done. move : (div.dvdn2 m); by rewrite Hodd. *)
(* Qed. *)

(* Lemma from_nat_bounded_eq m1 m2 n : m1 < 2^n -> m2 < 2^n -> *)
(*   (m1==m2) = (from_nat n m1 == from_nat n m2). *)
(* Proof. *)
(*   move => Hlt1 Hlt2. case E: (m1 == m2); case E': (from_nat n m1 == from_nat n m2) => //. *)
(*   by rewrite (eqP E) eq_refl in E'. *)
(*   rewrite -(to_nat_from_nat_bounded Hlt1) -(to_nat_from_nat_bounded Hlt2) in E. *)
(*   by rewrite (eqP E') eq_refl in E. *)
(* Qed. *)

(* Lemma from_nat_dhalf n m : joinlsb (odd m) (from_nat n m./2) = from_nat n.+1 m. *)
(* Proof. done. Qed. *)

(* Lemma from_nat_wrap n : forall m, from_nat n m = from_nat n (m + 2^n). *)
(* Proof. induction n => //. *)
(* rewrite expnS. *)
(* move => m. *)
(* case ODD: (odd m); rewrite /from_nat-/from_nat /=ODD odd_add odd_mul/=ODD/= halfD ODD/=. *)
(* specialize (IHn m./2). by rewrite odd_mul/= add0n mul2n doubleK IHn. *)
(* specialize (IHn m./2). by rewrite add0n mul2n doubleK IHn. *)
(* Qed. *)

(* Lemma from_nat_wrapMany n c : forall m, from_nat n m = from_nat n (m + c * 2^n). *)
(* Proof. induction c => m. by rewrite mul0n addn0. *)
(* rewrite mulSn (addnC (2^n)) addnA from_nat_wrap. rewrite IHc. *)
(* by rewrite -addnA (addnC (2^n)) addnA. *)
(* Qed. *)

(* Lemma to_nat_mod p: to_nat p = div.modn (to_nat p) (2^(size p)). *)
(* Proof. rewrite div.modn_small => //. apply to_nat_bounded. Qed. *)

(* Lemma to_nat_from_nat n m : to_nat (from_nat n m) = div.modn m (2^n). *)
(* Proof. have H:= div.divn_eq m (2^n). rewrite {1}H. *)
(* have HH:= from_nat_wrapMany n (div.divn m (2^n)) (div.modn m (2^n)). rewrite addnC in HH. rewrite -HH. *)
(* rewrite to_nat_from_nat_bounded. done. apply div.ltn_pmod. apply expn_gt0. Qed. *)

(* Lemma adcB_nat p1 p2 c : (adcB c p1 p2).2 = from_nat (size (adcB c p1 p2).2) (c + to_nat p1 + to_nat p2). *)
(* Proof. *)
(*   move : p2 c. elim p1 => [|phd1 ptl1 IH1] p2 c/=. *)
(*   - by rewrite size_adcB/=min0n/=/adcB/full_adder zip_nil. *)
(*   - move : c. elim p2 => [|phd2 ptl2 IH2] c/=; first done. *)
(*     move :(IH1 ptl2 c). rewrite/adcB/full_adder/=/bool_adder. *)
(*     case Hc : c; case Hphd1 : phd1; case Hphd2: phd2; move => Hfazt; *)
(*     case Hfadderzt : (full_adder_zip true (zip ptl1 ptl2)) =>[c0 tl0]; case Hfadderzf : (full_adder_zip false (zip ptl1 ptl2)) =>[c1 tl1]; try (rewrite Hfadderzt/= in Hfazt; rewrite Hfazt/=). *)
(*     + rewrite!odd_add!odd_double/= size_from_nat-div.divn2 div.divnDl; last by rewrite div.dvdn2 odd_double. rewrite -2!muln2 (div.mulnK _ (Nats.lt_ltn (Nat.lt_0_succ 1))) (div.divnDr); last by rewrite div.dvdn_mull. rewrite div.divn_small; last done; rewrite add0n div.mulnK; last done. *)
(*       by rewrite add1n addSn. *)
(*     + rewrite add0n odd_add!odd_double/=size_from_nat-div.divn2 div.divnDr; last by rewrite div.dvdn2 odd_double. by rewrite-2!muln2!(div.mulnK _ (Nats.lt_ltn (Nat.lt_0_succ 1))) add1n addSn.  *)
(*     + rewrite add0n uphalf_half!odd_add!odd_double/=size_from_nat-div.divn2 div.divnDl; last by rewrite div.dvdn2 odd_double. rewrite div.divnDr; last by rewrite div.dvdn2 odd_double. rewrite-!muln2!(div.mulnK _ (Nats.lt_ltn (Nat.lt_0_succ 1)))div.divn_small; last done. by rewrite add0n addnA.  *)
(*     + rewrite-!muln2!add0n-/joinlsb size_joinlsb addn1-from_nat_dhalf-addnA-mulnDl-div.divn2 div.divnDr; last by rewrite div.dvdn2 muln2 odd_double. rewrite div.divn_small; last done. rewrite (div.mulnK _ (Nats.lt_ltn (Nat.lt_0_succ 1))) add0n odd_add muln2 odd_double/=. *)
(*       move: (IH1 ptl2 false); rewrite/adcB/full_adder Hfadderzf/=add0n. move=>Hfazf; by rewrite Hfazf/=size_from_nat. *)
(*     + rewrite!add0n-/joinlsb size_joinlsb addn1-from_nat_dhalf!odd_add!odd_double-div.divn2 addnACA div.divnDl; last by rewrite div.dvdn2. rewrite div.divnn/=div.divnDr; last by rewrite div.dvdn2 odd_double. *)
(*       rewrite-2!muln2!div.mulnK; try done. move : (IH1 ptl2 true); rewrite/adcB/full_adder Hfadderzt/=; move => Hfazf; by rewrite Hfazf size_from_nat addnA. *)
(*     + rewrite!add0n-/joinlsb size_joinlsb addn1-from_nat_dhalf!odd_add!odd_double-div.divn2!div.divnDr; try by rewrite div.dvdn2 odd_double. rewrite-!muln2!div.mulnK; try done. rewrite div.divn_small/=; try done. *)
(*       move: (IH1 ptl2 false); rewrite/adcB/full_adder size_full_adder_zip add0n Hfadderzf/=; move => Hfazf; by rewrite Hfazf size_zip size_from_nat. *)
(*     + rewrite!add0n-/joinlsb size_joinlsb addn1-from_nat_dhalf!odd_add!odd_double-div.divn2 div.divnDl; last by rewrite div.dvdn2 odd_double. rewrite div.divnDr; last by rewrite div.dvdn2 odd_double. rewrite-!muln2!div.mulnK; try done. rewrite div.divn_small/=; try done. move : (IH1 ptl2 false); rewrite/adcB/full_adder Hfadderzf!add0n/=; move => Hfazf; by rewrite Hfazf size_from_nat. *)
(*     + rewrite!add0n-/joinlsb size_joinlsb addn1-from_nat_dhalf odd_add!odd_double-div.divn2 div.divnDr; last by rewrite div.dvdn2 odd_double. rewrite-!muln2!div.mulnK; try done. move : (IH1 ptl2 false); rewrite/adcB/full_adder Hfadderzf add0n/=; move => Hfazf; by rewrite Hfazf size_from_nat. *)
(* Qed. *)

(* Corollary to_nat_adcB b p1 p2 : to_nat (adcB b p1 p2).2 = to_nat (from_nat (size (adcB b p1 p2).2) (b + to_nat p1 + to_nat p2)). *)
(* Proof. *)
(* rewrite adcB_nat. rewrite size_adcB!to_nat_from_nat size_from_nat=> //.  *)
(* Qed. *)

(* Lemma to_nat_addB p1 p2 : to_nat (addB p1 p2) = to_nat (from_nat (size (addB p1 p2)) (to_nat p1 + to_nat p2)).  *)
(* Proof. *)
(*   rewrite/addB. rewrite to_nat_adcB => //.  *)
(* Qed.   *)

(* Lemma to_nat_full_mul p1 p2 : to_nat (full_mul p1 p2) = to_nat (from_nat (size (full_mul p1 p2)) (to_nat p1 * to_nat p2)). *)
(* Proof. *)
(*   move : p2. elim p1 => [|phd1 ptl1 IH] p2 /=; first by rewrite!from_natn0 size_zeros!add0n.  *)
(*   move : (to_nat_bounded ptl1) => Hbd1; move : (to_nat_bounded p2) => Hbd2. *)
(*   move : (Nat.mul_lt_mono _ _ _ _ (ltP Hbd1) (ltP Hbd2)); rewrite-!Nats.muln_mul-expnD; move => Hbd. *)
(*   SearchAbout lt. move : (mult_S_lt_compat_l 1 _ _  Hbd). rewrite -!Nats.muln_mul mulnC -expnS => Hbdmul. *)
(*   case phd1. *)
(*   - rewrite/=to_nat_addB size_addB size_joinlsb to_nat_joinlsb (IH p2) size_full_mul size_zext to_nat_zext addn1-addSn addnC minnn addn0 !to_nat_from_nat-!muln2 div.muln_modl; last done. rewrite addnS expnS. *)
(*     have-> :(2 * 2 ^ (size p2 + size ptl1) = (2 ^ (size ptl1 + size p2) * 2)) by rewrite mulnC addnC. rewrite div.modnDml. *)
(*     have->:(((1 + to_nat ptl1 * 2) * to_nat p2) = to_nat ptl1 * to_nat p2 * 2 + to_nat p2) by rewrite mulnDl mul1n; ring. done. *)
(*   - rewrite size_joinlsb to_nat_joinlsb (IH p2) size_full_mul addn0 add0n-!muln2!to_nat_from_nat_bounded; first ring. rewrite addn1 mulnAC. apply/ltP; exact. apply/ltP; exact.  *)
(* Qed. *)

(* Lemma to_nat_take : forall n p, to_nat ((take n) p) = if n < size p then to_nat (from_nat n (to_nat p)) else to_nat p. *)
(*   elim => [| ns IH] p. *)
(*   rewrite take0/=. *)
(*   elim p => [| phd ptl IHm]; done. *)
(*   elim p => [| phd ptl IHm]; first done. *)
(*   rewrite to_nat_cons/=. *)
(*   case Hlt : (ns.+1 < (size ptl).+1); rewrite ltnS in Hlt.  *)
(*   rewrite odd_add odd_double oddb. rewrite (IH ptl) Hlt. *)
(*   case phd; first by rewrite/=uphalf_double.  *)
(*   by (rewrite/=3!add0n-3!muln2-div.divn2 div.mulnK; last done). *)
(*   by rewrite IH Hlt. *)
(* Qed. *)

(* Lemma to_nat_mulB p1 p2 : to_nat (mulB p1 p2) = to_nat (from_nat (size p1) (to_nat p1 * to_nat p2)). *)
(* Proof. *)
(*   rewrite/mulB/low size_full_mul to_nat_cat to_nat_zeros mul0n addn0 to_nat_take size_full_mul. *)
(*   case Hlt : (size p1 < size p1 + size p2). *)
(*   by rewrite to_nat_full_mul size_full_mul 3!to_nat_from_nat expnD Nats.modn_muln_modn_l.  *)
(*   rewrite to_nat_full_mul size_full_mul. *)
(*   have Hadd0 : size p1 = size p1 +0 by rewrite addn0. rewrite {1}Hadd0 ltn_add2l in Hlt. *)
(*   move/negP/negP: Hlt. rewrite-eqn0Ngt. move/eqP => Hlt. by rewrite Hlt addn0. *)
(* Qed. *)
  
(* Lemma mulnB_eq0: forall m n : bits, (mulB m n == (zeros (size m))) = (m == zeros (size m)) || (n == zeros (size n)). *)
(* Proof. *)
(*   intros. *)
(*   case Hmz : (m == zeros (size m)). *)
(*   - by rewrite (eqP Hmz) mul0B size_zeros eq_refl. *)
(*   - case Hnz : (n == zeros (size n)). *)
(*     + rewrite (eqP Hnz)/mulB full_mul0/low size_zeros subnDA subnn sub0n cats0-zeros_cats take_size_cat/= ; last by rewrite size_zeros. exact: eq_refl. *)
(*     + move : Hmz Hnz. move : n. *)
(*       elim m => [|mhd mtl IH]n/=. by rewrite mulB_nil_l. *)
(*   rewrite /mulB/=. case Hmhd: mhd. intros. *)
(*   move : (IH n). rewrite/mulB/low size_addB size_joinlsb size_zext!size_full_mul addnAC addn1 subnDA subnn sub0n cats0. intros. rewrite addnC minnn subnDA subnAC subnn sub0n cats0. rewrite (take_nth false).  *)
(* Admitted. *)



(* Lemma subB_is_dropmsb_adcB_invB (p q: bits) : subB p q = dropmsb (adcB true p (invB q)).2. *)
(* Proof.  *)
(* Admitted. *)

(* Lemma sub0B : forall m, subB (zeros (size m)) m = negB m. *)
(* Proof. *)
(*   elim => [|mhd mtl IH]/=. done. *)
(*   case mhd. rewrite/subB/sbbB/adcB/full_adder/=. *)
(*   case Hfaddzf : (full_adder_zip false (zip (zeros (size mtl)) (~~# mtl)%bits))=>[c res]/=. *)
(*   have -> : res = (full_adder_zip false (zip (zeros (size mtl)) (~~# mtl)%bits)).2 *)
(*     by rewrite Hfaddzf. *)
(*   rewrite full_adder_zip_0_l unzip2_zip ; last by rewrite size_zeros -BBNeg.invB_size_ss. *)
(* Admitted. *)
  
(* Lemma subB0: forall m n, subB m (zeros n) = m. *)
(* Proof. *)
(* Admitted. *)
  
(* Lemma mulB0' : forall m n, mulB m (zeros n) = zeros (size m). *)
(* Proof. *)
(*   intros. rewrite/mulB full_muln0/low -zeros_cats take_cat size_zeros/=. *)
(*   case H : (size m < size m). move : (Nat.lt_irrefl (size m))=>Heq. *)
(*   exfalso; apply Heq; apply Nats.ltn_lt; rewrite H; done. *)
(*   by rewrite size_cat size_zeros subnDA subnn take0 sub0n !cats0. *)
(* Qed. *)

(* Lemma to_nat_shlB1 : forall (p: bits), to_nat (shlB1 p) = div.modn ((to_nat p).*2) (2^size p). *)
(* Proof. move => p. by rewrite /shlB1 to_nat_dropmsb to_nat_joinlsb size_joinlsb-subn1 addnK addn0-muln2. *)
(* Qed. *)

(* Lemma to_nat_shlBn: *)
(*   forall n k, k < n -> to_nat (shlB k (from_nat n 1) ) = 2 ^ k. *)
(* Proof. *)
(* Admitted. *)

(* Lemma shlB_dropmsb n (p: bits) : shlB n (dropmsb p) = dropmsb (shlB n p). *)
(* Proof. *)
(* Admitted. *)

(* Lemma to_nat_shrB1 : forall bs, to_nat (shrB1 bs) = div.divn (to_nat bs) 2. *)
(* Proof. *)
(*   elim => [|bhd btl IH]/=. done. *)
(*   by rewrite/shrB1 to_nat_droplsb to_nat_joinmsb mul0n add0n/=-muln2-div.divn2. *)
(* Qed. *)
  
(* Lemma to_nat_shrB : forall n bs, to_nat (shrB n bs) = div.divn (to_nat bs) (2^n). *)
(* Proof. *)
(*   intros. *)
(*   elim n => [|ns IH]/=. by rewrite div.divn1. *)
(*   by rewrite to_nat_shrB1 IH-div.divnMA expnS mulnC.  *)
(* Qed. *)
  

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


(* Fixpoint udivB_rec (n m : bits) (q r : bits): bits * bits := *)
(*   match n with *)
(*   | [::] => (q, r) *)
(*   | nhd :: ntl => let di := dropmsb (joinlsb nhd r) in *)
(*                   let bi := negb (ltn (to_nat di) (to_nat m)) in *)
(*                   let ri := if bi then subB di m else di in *)
(*                   let qi := dropmsb (joinlsb bi q) in *)
(*                   udivB_rec ntl m qi ri *)
(*   end. *)

(* Definition udivB (n' m : bits) : bits * bits := *)
(*   let n := rev n' in *)
(*   if ((from_nat (size n) (to_nat m)) == zeros (size n)) then (zeros (size n), n') *)
(*   else udivB_rec n (from_nat (size n) (to_nat m)) (zeros (size n)) (zeros (size n)). *)

(*Definition udivB_extzip (zip : seq (bool * bool)) (q r : bits) : bits * bits :=
  udivB_rec (rev (unzip1 zip)) (unzip2 zip) q r .

Definition udivB (n m : bits) : bits * bits :=
  if (m == zeros (size m)) then (zeros (maxn(size n)(size m)), unzip1 (extzip0 n m))
  else udivB_extzip (extzip0 n m) (zeros (maxn(size n)(size m))) (zeros (maxn(size n)(size m))).*)

(* Eval compute in (to_nat (udivB (from_nat 8 185) (from_nat 4 13)).1). *)
(* Eval compute in (to_nat (udivB (from_nat 8 185) (from_nat 4 13)).2). *)
(* Eval compute in (to_nat (udivB (from_nat 8 156) (from_nat 3 2)).1). *)
(* Eval compute in (to_nat (udivB (from_nat 8 16) (from_nat 3 2)).2). *)


(* Lemma size_udivB_rec n m q r : size (udivB_rec n m q r).1 = size q. *)
(* Proof. *)
(*   move : m q r.  elim n => [|nhd ntl IH]m q r/=; first done.  *)
(*   rewrite (IH m (dropmsb (joinlsb (~~ (to_nat (dropmsb (joinlsb nhd r)) < to_nat m)) q)) *)
(*               (if ~~ (to_nat (dropmsb (joinlsb nhd r)) < to_nat m) *)
(*                then (dropmsb (joinlsb nhd r) -# m)%bits *)
(*                else dropmsb (joinlsb nhd r))). *)
(*     by rewrite size_dropmsb size_joinlsb addnK. *)
(* Qed.   *)

(* Lemma size_udivB n m : size (udivB n m).1 = (size n). *)
(* Proof. *)
(*   rewrite/udivB. case Hm0: ((size (rev n)) -bits of (to_nat m)%bits == zeros (size (rev n))); first by rewrite size_rev size_zeros. *)
(*   by rewrite size_udivB_rec size_zeros size_rev. *)
(* Qed. *)

(* Lemma udivB_rec0r : forall m n q r,  (udivB_rec m (zeros n) q r) = (addB (shlB (size m) q) (zext (size q - size m) (ones (size m))), addB (shlB (size m) r) (zext (size r - size m) (rev m))). *)
(* Proof.  *)
(*   elim => [|mhd mtl IH] n q r; rewrite/=. rewrite/rev/=!zext_nil!subn0!addB0 unzip1_zip; last by rewrite size_zeros. rewrite unzip1_zip; last by rewrite size_zeros. done. *)
(*   intros. rewrite to_nat_zeros/=subB0.  *)
(*   rewrite IH; first rewrite size_dropmsb size_joinlsb addnK.  *)
(*   rewrite /shlB1. *)
(*   assert ((dropmsb (joinlsb true q) <<# size mtl +# zext (size q - size mtl) (ones (size mtl)))%bits==(dropmsb (joinlsb false (q <<# size mtl)) +# zext (size q - (size mtl).+1) (b1 :: ones (size mtl)))%bits). *)
(*   rewrite shlB_dropmsb-to_nat_inj_ss; last by rewrite!size_addB!size_dropmsb!size_zext/=size_ones!size_shlB size_joinlsb addnK -addn1 addnK; repeat rewrite-maxnE maxKn. *)
(*   rewrite 2!to_nat_addB 2!to_nat_zext/=to_nat_ones 2!to_nat_dropmsb to_nat_joinlsb. rewrite/shlB 2!shlB_mul2exp 2!to_nat_mulB addn0.   *)
(*   rewrite 2!size_addB 2!size_dropmsb 2!size_joinlsb 2!size_mulB size_joinlsb 2!size_zext-subn1 addnK/= size_ones-!maxnE !maxKn. *)
(*   rewrite !to_nat_from_nat. *)
(* Admitted. *)
  
  
(* Lemma udivB0 : forall n m, (udivB m (zeros n)) = (zeros (size m), m). *)
(* Proof. *)
(*   intros; rewrite/udivB. by rewrite to_nat_zeros from_natn0 eq_refl size_rev.  *)
(* Qed. *)


(* Lemma udivB_rec0_aux : forall n(m : bits) s, *)
(*     ~~(m==zeros(size m)) -> udivB_rec (zeros n) m (zeros s) (zeros s)= (zeros s, zeros s). *)
(* Proof. *)
(*   elim. intros; first by done. *)
(*   intros. rewrite-zeros_cons/=to_nat_dropmsb to_nat_joinlsb to_nat_zeros div.mod0n.  *)
(*   move : (to_nat_zero m). move: H0; rewrite-eqbF_neg; move=>Hnotz; rewrite(eqP Hnotz)eqn0Ngt; move=>Htonat; rewrite Htonat/joinlsb zeros_cons dropmsb_zeros-pred_Sn. rewrite eqbF_neg in Hnotz. *)
(*   exact :(H m s Hnotz). *)
(* Qed. *)


  
(* Lemma udivB_rec0 : forall n (m : bits) q r , *)
(*     ~~(m==zeros(size m)) -> udivB_rec (zeros n.+1) m q (zeros r)= (shlB n.+1 q, (zeros r)). *)
(* Proof. *)
(*   intros. rewrite-zeros_cons/=to_nat_dropmsb to_nat_joinlsb to_nat_zeros div.mod0n. *)
(*   move : (to_nat_zero m). move: H; rewrite-eqbF_neg; move=>Hnotz; rewrite(eqP Hnotz)eqn0Ngt; move=>Htonat; rewrite Htonat/joinlsb zeros_cons dropmsb_zeros-pred_Sn/shlB1. rewrite eqbF_neg in Hnotz. *)
(*   move: q r. elim n; first done.  intros. rewrite-zeros_cons/=to_nat_dropmsb to_nat_joinlsb to_nat_zeros div.mod0n Htonat/joinlsb zeros_cons dropmsb_zeros-addn1-subn1 addnK. *)
(*   move :(H (dropmsb (false :: q)) r).  *)
(*   rewrite/shlB1/joinlsb. have->: ((dropmsb (false :: q) <<# n0)%bits = dropmsb (false :: (q <<# n0)%bits)). *)
(*   rewrite/shlB/shlB1. elim n0; first done. rewrite/joinlsb/=; intros; by rewrite H0. *)
(*   done. *)
(* Qed. *)

(* Lemma rev_copy : forall T n (b: T), rev (copy n b) = copy n b. *)
(* Proof. *)
(* Admitted. *)
  
(* Lemma udiv0B : forall n (m: bits), ~~(from_nat n (to_nat m) == zeros n)-> udivB (zeros n) m = (zeros n, zeros n). *)
(* Proof. *)
(*   move => n m Hm. move : (negbTE Hm) => Hnot0. rewrite/udivB size_rev size_zeros Hnot0.  *)
(*   move : Hnot0. elim n; first done. *)
(*   move => ns Hudiv Hnot0.  rewrite rev_copy udivB_rec0; first by rewrite/shlB shlB_mul2exp mul0B. *)
(*   by rewrite size_from_nat Hnot0. *)
(* Qed. *)
  
(* Lemma size_uremB_rec : forall  n m q r, size m = size r -> size (udivB_rec n m q r).2 = size r. *)
(* Proof. *)
(*   elim =>[|nhd ntl IH]m q r Hsz; first done. *)
(*   rewrite/=(IH m (dropmsb (joinlsb (~~ (to_nat (dropmsb (joinlsb nhd r)) < to_nat m)) q)) *)
(*        (if ~~ (to_nat (dropmsb (joinlsb nhd r)) < to_nat m) *)
(*         then (dropmsb (joinlsb nhd r) -# m)%bits *)
(*         else dropmsb (joinlsb nhd r))); *)
(*   case H : ((to_nat (dropmsb (joinlsb nhd r)) < to_nat m)); try (by rewrite/=size_dropmsb size_joinlsb addnK|| by rewrite/=size_subB size_dropmsb size_joinlsb addnK Hsz minnn). *)
(* Qed.     *)

(* Lemma size_uremB : forall n m , size (udivB n m).2 = size n. *)
(* Proof. *)
(*   rewrite/udivB. intros. *)
(*   case Hm0: ((size (rev n)) -bits of (to_nat m)%bits == zeros (size (rev n))); first done.  *)
(*   rewrite size_rev size_uremB_rec; rewrite size_zeros; first done. by rewrite size_from_nat. *)
(* Qed.   *)

(* Lemma udivB_mulAC : forall d m n, (udivB d m).2 = zeros (size d) -> udivB m (mulB d n) = udivB (mulB m n) d. *)
(* Proof. *)
(*   elim =>[|dhd dtl IH] m n H; rewrite/udivB/=. *)
(*   - rewrite !size_mulB/mulB/= /low !take0 add0n sub0n zeros0 cats0/=/extzip0!unzip1_extzip!sub0n!cats0.  *)
(*   - case Hz : (dhd :: dtl == b0 :: zeros (size dtl)). *)
(*     + rewrite (eqP Hz)zeros_cons size_mulB size_zeros !mul0B/=. *)
(*       case Hzeros: (b0 :: zeros (size dtl) == b0 :: zeros (size dtl)); rewrite !size_mulB; first done. *)
(*       rewrite zeros_cons in Hzeros. move : (eq_refl (zeros (size dtl).+1)) => Hzeros'; rewrite Hzeros' in Hzeros; discriminate. *)
(*     + case Hmul0 : (((dhd :: dtl) *# n)%bits == zeros (size ((dhd :: dtl) *# n)%bits)). *)
(*       * rewrite size_mulB mulnB_eq0 in Hmul0. move : (orP Hmul0)=>[Hl| Hr]. *)
(*         rewrite/= in Hl. rewrite Hl in Hz; discriminate. *)
(*         rewrite (eqP Hr) mulB0' act_size0 sub0n add0n. rewrite/=subn0 !act_size0 !sub0n add0n size_zeros nth0. have ->: (head false (zeros (size m))=false) by (case m=>[|mhd mtl]; by rewrite/=). rewrite/joinlsb/=/shrB1/= to_nat_dropmsb/=to_nat_droplsb/= to_nat_joinmsb mul0n to_nat_zeros addn0 div.mod0n. move : (to_nat_zero (dhd :: dtl))=> Heqz. rewrite Hz/= in Heqz. rewrite (neq0_lt0n Heqz)/= zeros_cons dropmsb_zeros. by rewrite/joinmsb zeros_rcons /droplsb/=zeros_cons dropmsb_zeros-addn1-subn1 addnK. *)
(*       * rewrite size_mulB mulnB_eq0 Hz/= in Hmul0. *)

(* Admitted. *)
  


(* Lemma ltn_neq0 : forall n m, n < m -> (m != 0). *)
(* Proof. *)
(*   elim => [| ns IH] m/=. by rewrite lt0n. *)
(*   - intro. rewrite-(eqP (Nats.lt_sub1r_add1l ns m)) in H; apply (IH m.-1) in H. *)
(*     rewrite-lt0n (eqP (Nats.lt_sub1r_add1l 0 m)) in H. move : (ltn_trans (ltn0Sn 0) H). by rewrite lt0n. *)
(* Qed. *)

(* Lemma lt0B_size : forall b, ([::] <# b)%bits -> 0 < size b. *)
(* Proof. *)
(*   elim; first done. intros; by rewrite ltn0Sn. *)
(* Qed. *)

(* Lemma odd_to_nat_lsb : forall b, odd (to_nat b) =lsb b. *)
(* Proof. *)
(*   elim; first by rewrite/lsb/splitlsb/=. *)
(*   move => a l IH. *)
(*   rewrite/lsb/=odd_add odd_double-negb_eqb. case Ha : a; done. *)
(* Qed. *)

(* Lemma neq0_eq0_sizel : forall n (b : bits), b!=zeros (size b) -> from_nat n (to_nat b) == zeros n -> n < size b. *)
(* Proof. *)
(*   elim => [|ns IH] b/=; first by (rewrite-ltB0n eq_refl; move=> [Hneq Ht{Ht}]; exact (lt0B_size Hneq)). *)
(*   move=>[Hneq Heq]. move : (IH (droplsb b)) => Hm. rewrite-(eqP (Nats.lt_sub1r_add1l ns (size b)))-subn1-size_droplsb. apply Hm; last rewrite to_nat_droplsb. *)
(*   move : Hneq. rewrite-!to_nat_zero to_nat_droplsb-!lt0n half_gt0. move => Hgt0. *)
(*   case Hoddb: (odd (to_nat b)); first by rewrite Hoddb eqseq_cons andFb in Heq. *)
(*   rewrite Hoddb/joinlsb eqseq_cons andTb in Heq. rewrite Nats.ssrodd_odd-Nat.even_succ-Nat.negb_odd in Hoddb. move: (negbFE Hoddb)=>Hodd{Hoddb}. rewrite-Nats.ssrodd_odd in Hodd. rewrite-(ltn_add2r 1)2!addn1 in Hgt0. move : (odd_gt2 Hodd Hgt0)=> Hodd2.  move : (ltn_sub2r Hgt0 Hodd2). by rewrite!subn1/=.  *)
(*   rewrite eqseq_cons in Heq. move/andP : Heq=>[Hb0 Hzeq]. done. *)
(* Qed. *)


(* Lemma to_nat_belast_0 : forall s, to_nat (belast false (zeros s)) = 0. *)
(* Proof. *)
(*   elim => [|ns IH]/=; first done. rewrite IH-muln2 mul0n; done. *)
(* Qed. *)

(* Lemma lt1_eq0 : forall (n:nat), n<1 -> n=0. *)
(* Proof. intros. induction n; try done. *)
(* Qed. *)


(* Lemma subB_joinmsb_dropmsb: forall b q n, size q = n.+1 -> (dropmsb (joinlsb b q) -# joinlsb b (zeros n))%bits = dropmsb (joinlsb false q). *)
(* Proof. *)
(* Admitted. *)
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

  
(* Lemma udivB1: forall p, udivB p (from_nat (size p) 1) = (p, from_nat (size p) 0). *)
(* Proof. *)
(*   elim=>[| ph pt IH]/=; first done.  *)
(*   rewrite/udivB!from_natn0 to_nat_joinlsb to_nat_zeros-muln2 mul0n add0n. *)
(*   rewrite-from_natn0 -from_nat_bounded_eq; [|by rewrite/=size_rev Nats.expn2_gt1|by rewrite size_rev Nats.expn2_gt0]. *)
(*   rewrite/udivB in IH. *)
(*   rewrite/=!from_natn0 size_rev/=.  *)
(* Admitted. *)
  
(* Lemma shrB_div2exp:  forall i p , (iter i shrB1 p, from_nat (size p) 0) = udivB p (from_nat (size p) (2^ i)%nat). *)
(* Proof. *)
(* Admitted. *)
  
(* Lemma udivB_def: forall q d r, ltB r d -> (udivB (addB (mulB q d) r) d).2 = r. *)
(* Proof. *)
(* Admitted. *)
  
(* Lemma udivB_rec_to_nat : forall nhd ntl m q r, to_nat (udivB_rec (nhd::ntl) m q r).1 = addn (div.divn (addn (to_nat (shlB (size ntl).+1 r)) (to_nat (nhd::ntl))) (to_nat m)) (to_nat q). *)
(* Proof. *)
(* Admitted. *)
  
(* Lemma udivB_to_nat : forall p q,  to_nat (udivB p q).1 = (div.divn (to_nat p) (to_nat (from_nat (size p) (to_nat q)))). *)
(* Proof. *)
  
(*   intros. rewrite/udivB. *)
(*   case H0 : ((size p) -bits of (to_nat q)%bits == zeros (size p)); *)
(*     first by rewrite/=(eqP H0) to_nat_zeros div.divn0.  *)
(*   move : q H0. elim p =>[|phd ptl IH] q H0/=; first done. *)
(*   have : (to_nat (dropmsb (zeros (size ptl).+1)) = 0) by rewrite to_nat_dropmsb to_nat_zeros div.mod0n. *)
(*   rewrite/dropmsb/splitmsb/=; move => Hbelast; rewrite Hbelast-muln2 mul0n addn0/=. *)
(*   case Hphd : phd; case Hoddq : (odd (to_nat q)); rewrite /=eqseq_cons Hoddq in H0; rewrite/=. *)
(*   - have Hgt0 : (0 < (to_nat (size ptl) -bits of ((to_nat q)./2)%bits)). admit. *)
(*     move : (muln_gt0 (to_nat (size ptl) -bits of ((to_nat q)./2)%bits) 2)=> Hgt0'; rewrite Hgt0(ltn0Sn 1)andTb muln2-(ltn_add2l 1)addn0 in Hgt0'. *)
(*     rewrite Hgt0'/=. *)

    
(*     rewrite Hgt0' udivB_rec_to_nat/shlB shlB_mul2exp/=add0n/mulB/=size_belast size_zeros/low size_addB size_joinlsb.  *)

(* Admitted.   *)

(* Lemma uremB_to_nat : forall p q , to_nat (udivB p q).2 = (div.modn (to_nat p) (to_nat q)). *)
(* Proof.   *)
(* Admitted. *)

(*
Fixpoint bit_blast_udiv_rec_t g ls1 ls2 cs qs rs: generator * cnf * word * word :=

  match ls1 with
  | [::] => (g, cs, qs, rs)
  | ls_hd1 :: ls_tl1 =>
    let di := dropmsl (joinlsl ls_hd1 rs) in
    let '(g_ge, cs_ge, lrs_ge) := bit_blast_uge g di ls2 in
    let qi := dropmsl (joinlsl lrs_ge qs) in
    if (lrs_ge==lit_tt) then
      let '(g_sub, cs_sub, lrs_sub) := bit_blast_sub g_ge di ls2 in
      bit_blast_udiv_rec_t g_sub ls_tl1 ls2 (catrev (catrev cs cs_ge) cs_sub) qi lrs_sub
    else if (lrs_ge == lit_ff) then bit_blast_udiv_rec_t g_ge ls_tl1 ls2 (catrev cs cs_ge) qi di
         else
           let '(g_and, cs_and, lrs_and) := bit_blast_and g_ge (copy (size ls2) lrs_ge) ls2 in
           let '(g_sub2, cs_sub2, lrs_sub2) := bit_blast_sub g_and di lrs_and in
           bit_blast_udiv_rec_t g_sub2 ls_tl1 ls2 (catrev (catrev (catrev cs cs_ge) cs_and) cs_sub2) qi lrs_sub2
  end.
*)

(*
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
*)


Fixpoint bit_blast_udiv_rec g ls1 ls2 qs rs :  generator * cnf * word * word :=
  match ls1 with
  | [::] => (g, [::], qs, rs)
  | ls1_hd :: ls1_tl =>
    let di := dropmsl (joinlsl ls1_hd rs) in
    let '(g_uge, cs_uge, lrs_uge) := bit_blast_uge g di ls2 in
    let qi := dropmsl (joinlsl lrs_uge qs) in
    if (lrs_uge == lit_tt) then
      let '(g_sub, cs_sub, lrs_sub) := bit_blast_sub g_uge di ls2 in
      let '(g_tl, cs_tl, lqs_tl, lrs_tl) := bit_blast_udiv_rec g_sub ls1_tl ls2 qi lrs_sub in
      (g_tl, (catrev (catrev cs_tl cs_sub) cs_uge), lqs_tl, lrs_tl)
    else if (lrs_uge == lit_ff) then
           let '(g_tl, cs_tl, lqs_tl, lrs_tl) := bit_blast_udiv_rec g_uge ls1_tl ls2 qi di in
           (g_tl, catrev cs_tl cs_uge, lqs_tl, lrs_tl)
         else let '(g_and, cs_and, lrs_and) := bit_blast_and g_uge (copy (size ls2) lrs_uge) ls2 in
              let '(g_sub2, cs_sub2, lrs_sub2) := bit_blast_sub g_and di lrs_and in
              let '(g_tl, cs_tl, lrs_tl, lqs_tl) := bit_blast_udiv_rec g_sub2 ls1_tl ls2 qi lrs_sub2 in
              (g_tl, (catrev (catrev (catrev cs_tl cs_sub2) cs_and) cs_uge), lrs_tl, lqs_tl)
  end.             

Compute ( (udivB_rec [:: true; false; true; false] (zeros 4) (zeros 4) (zeros 4))).

Definition bit_blast_udiv g ls1' ls2 :=
  let ls1 := rev ls1' in
  let '(g_eq, cs_eq, lrs_eq) := bit_blast_eq g ls2 (copy (size ls2) lit_ff) in
  if lrs_eq == lit_tt then
    (g_eq, cs_eq, copy (size ls2) lit_ff, ls1')
  else if lrs_eq == lit_ff then
    let '(g_udivr, cs_udivr, lqs_udivr, lrs_udivr) :=
        bit_blast_udiv_rec g_eq ls1 ls2 (copy (size ls1) lit_ff) (copy (size ls1) lit_ff)
    in (g_udivr, catrev cs_udivr cs_eq, lqs_udivr, lrs_udivr)
       else
         let '(g_udivr, cs_udivr, lqs_udivr, lrs_udivr) :=
        bit_blast_udiv_rec g_eq ls1 ls2 (copy (size ls1) lit_ff) (copy (size ls1) lit_ff) in 
         let '(g_and, cs_and, lrs_and) := bit_blast_and g_udivr (copy (size lqs_udivr) (neg_lit lrs_eq)) lqs_udivr  in
         let '(g_ite, cs_ite, lrs_ite) := bit_blast_ite g_and lrs_eq (rev lrs_udivr) lrs_udivr in
         (g_ite, catrev (catrev (catrev cs_ite cs_and) cs_udivr) cs_eq, lrs_and, lrs_ite).

Fixpoint mk_env_udiv_rec E g ls1 ls2 qs rs : env * generator * cnf * word * word :=
  match ls1 with
  | [::] => (E, g, [::], qs, rs)
  | ls1_hd :: ls1_tl =>
    let di := dropmsl (joinlsl ls1_hd rs) in
    let '(E_uge, g_uge, cs_uge, lrs_uge) := mk_env_uge E g di ls2 in
    let qi := dropmsl (joinlsl lrs_uge qs) in
    if (lrs_uge == lit_tt) then
      let '(E_sub, g_sub, cs_sub, lrs_sub) := mk_env_sub E_uge g_uge di ls2 in
      let '(E_tl, g_tl, cs_tl, lqs_tl, lrs_tl) := mk_env_udiv_rec E_sub g_sub ls1_tl ls2 qi lrs_sub in
      (E_tl, g_tl, (catrev (catrev cs_tl cs_sub) cs_uge), lqs_tl, lrs_tl)
    else if (lrs_uge == lit_ff) then
           let '(E_tl, g_tl, cs_tl, lqs_tl, lrs_tl) := mk_env_udiv_rec E_uge g_uge ls1_tl ls2 qi di in
           (E_tl, g_tl, catrev cs_tl cs_uge, lqs_tl, lrs_tl)
         else let '(E_and, g_and, cs_and, lrs_and) := mk_env_and E_uge g_uge (copy (size ls2) lrs_uge) ls2 in
              let '(E_sub2, g_sub2, cs_sub2, lrs_sub2) := mk_env_sub E_and g_and di lrs_and in
              let '(E_tl, g_tl, cs_tl, lrs_tl, lqs_tl) := mk_env_udiv_rec E_sub2 g_sub2 ls1_tl ls2 qi lrs_sub2 in
              (E_tl, g_tl, (catrev (catrev (catrev cs_tl cs_sub2) cs_and) cs_uge), lrs_tl, lqs_tl)
  end.       

(*
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
 *)


Definition mk_env_udiv E g ls1' ls2 :=
  let ls1 := rev ls1' in
  let '(E_eq, g_eq, cs_eq, lrs_eq) := mk_env_eq E g ls2 (copy (size ls2) lit_ff) in
  if lrs_eq == lit_tt then
    (E_eq, g_eq, cs_eq, copy (size ls2) lit_ff, ls1')
  else if lrs_eq == lit_ff then
    let '(E_udivr, g_udivr, cs_udivr, lqs_udivr, lrs_udivr) :=
        mk_env_udiv_rec E_eq g_eq ls1 ls2 (copy (size ls1) lit_ff) (copy (size ls1) lit_ff)
    in (E_udivr, g_udivr, catrev cs_udivr cs_eq, lqs_udivr, lrs_udivr)
       else
         let '(E_udivr, g_udivr, cs_udivr, lqs_udivr, lrs_udivr) :=
             mk_env_udiv_rec E_eq g_eq ls1 ls2 (copy (size ls1) lit_ff) (copy (size ls1) lit_ff) in 
         let '(E_and, g_and, cs_and, lrs_and) := mk_env_and E_udivr g_udivr (copy (size lqs_udivr) (neg_lit lrs_eq)) lqs_udivr  in
         let '(E_ite, g_ite, cs_ite, lrs_ite) := mk_env_ite E_and g_and lrs_eq (rev lrs_udivr) lrs_udivr in
         (E_ite, g_ite, catrev (catrev (catrev cs_ite cs_and) cs_udivr) cs_eq, lrs_and, lrs_ite).

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
  (*case Hbbdiv : (bit_blast_udiv_rec g ls1tl ls2 qs rs) => [[[g_tl cs_tl] lrs_tl] lqs_tl].*)
  case Hbbuge: (bit_blast_uge g (dropmsl (joinlsl ls1hd rs)) ls2)=> [[g_hd cs_hd] lrs_hd].
  case Hbbsub : (bit_blast_sub g_hd (dropmsl (joinlsl ls1hd rs)) ls2) => [[g_sub cs_sub] lrs_sub].
  case Hbband : (bit_blast_and g_hd (copy (size ls2) lrs_hd) ls2) => [[g_and cs_and] lrs_and].
  case Hbbsub2 : (bit_blast_sub g_and (dropmsl (joinlsl ls1hd rs)) lrs_and) => [[g_sub2 cs_sub2] lrs_sub2].
  case Hbbdiv : (bit_blast_udiv_rec g_sub ls1tl ls2 (dropmsl (joinlsl lrs_hd qs)) lrs_sub) => [[[g_tl cs_tl] lrs_tl] lqs_tl].
  case Hbbdiv2 : (bit_blast_udiv_rec g_hd ls1tl ls2 (dropmsl (joinlsl lrs_hd qs)) (dropmsl (joinlsl ls1hd rs))) => [[[g_tl2 cs_tl2] lrs_tl2] lqs_tl2].
  case Hbbdiv3 : (bit_blast_udiv_rec g_sub2 ls1tl ls2 (dropmsl (joinlsl lrs_hd qs)) lrs_sub2)=> [[[g_tl3 cs_tl3] lrs_tl3] lqs_tl3].
  have Hszdj : (size (dropmsl (joinlsl lrs_hd qs)) = size ls2) by rewrite size_dropmsl size_joinlsl addnK Hszqs.
  have Hszdj2: (size (dropmsl (joinlsl ls1hd rs)) = size ls2) by rewrite size_dropmsl size_joinlsl addnK Hszrs.
  move : (bit_blast_sub_size_ss Hbbsub Hszdj2) => Hszsub.
  have Hszcp : (size (copy (size ls2) lrs_hd) = size ls2 ) by rewrite size_nseq.
  move : (bit_blast_and_size_ss Hbband Hszcp) => Hszand. 
  have Hszdj3 : (size (dropmsl (joinlsl ls1hd rs)) = size lrs_and) by rewrite size_dropmsl size_joinlsl addnK Hszrs -Hszand size_nseq.
  move : (bit_blast_sub_size_ss Hbbsub2 Hszdj3) => Hszsub2. generalize Hszsub2; move => Hszsub3. rewrite -Hszdj3 size_dropmsl size_joinlsl addnK Hszrs in Hszsub3.
  move : (IH _ _ _ _ _ _ _ _ Hbbdiv Hszdj Hszsub) => [Hszlrstl Hszlqstl]. 
  move : (IH _ _ _ _ _ _ _ _ Hbbdiv2 Hszdj Hszdj2) => [Hszlrstl2 Hszlqstl2]. 
  move : (IH _ _ _ _ _ _ _ _ Hbbdiv3 Hszdj Hszsub3) => [Hszlrstl3 Hszlqstl3]. 
  case Hhdtt : (lrs_hd == lit_tt). (case => _ _ <- <-). done.
  case Hhdff :(lrs_hd == lit_ff); case => _ _ <- <-; done.
Qed.

Lemma bit_blast_ite_size_ss : forall g l ls1 ls2 g' cs rlrs ,
    bit_blast_ite g l ls1 ls2 = (g', cs, rlrs) -> size ls1 = size ls2->
    size rlrs = size ls1.
Proof.
Admitted.

Lemma bit_blast_udiv_size_ss : forall g ls1 ls2 g' cs qlrs rlrs ,
    bit_blast_udiv g ls1 ls2 = (g', cs, qlrs, rlrs) -> size ls1 = size ls2->
    (size qlrs = size ls2 /\ size rlrs = size ls2).
Proof.
  move => g ls1 ls2 g' cs qlrs rlrs .
  rewrite/bit_blast_udiv.
  dcase (bit_blast_eq g ls2 (copy (size ls2) lit_ff)) => [[[g_eq] cs_eq] lrs_eq] Hbbeq.
  case Hbbudivr: (bit_blast_udiv_rec g_eq (rev ls1) ls2 (copy (size (rev ls1)) lit_ff)
        (copy (size (rev ls1)) lit_ff) ) => [[[g_udivr cs_udivr] lqs_udivr] lrs_udir].
  dcase (bit_blast_and g_udivr (copy (size lqs_udivr) (neg_lit lrs_eq)) lqs_udivr) => [[[g_and] cs_and] lrs_and] Hbband.
  dcase (bit_blast_ite g_and lrs_eq (rev lrs_udir) lrs_udir) => [[[g_ite] cs_ite] lrs_ite] Hbbite.
  case Hls2t : (lrs_eq == lit_tt).
  case => _ _ <- <-. move => Hsz . by rewrite size_nseq Hsz.
  case Hls2f : (lrs_eq == lit_ff).
  case => _ _ <- <-.
  move => Hsz12. have Hszcp : size (copy (size (rev ls1)) lit_ff) = size ls2 by rewrite size_nseq size_rev. 
  exact : (bit_blast_udiv_rec_size_ss Hbbudivr Hszcp Hszcp).
  case => _ _ <- <-.
  move => Hsz12.
  have Hszcp : size (copy (size (rev ls1)) lit_ff) = size ls2 by rewrite size_nseq size_rev.
  move : (bit_blast_udiv_rec_size_ss Hbbudivr Hszcp Hszcp).
  have Hszaux :size (copy (size lqs_udivr) (neg_lit lrs_eq)) = size lqs_udivr by rewrite size_nseq.
  SearchAbout bit_blast_ite. 
  move : (bit_blast_ite_size_ss Hbbite (size_rev lrs_udir)) => Hszite.
  move : (bit_blast_and_size_ss Hbband Hszaux) => Hszn. by rewrite -Hszn size_nseq Hszite size_rev.
Qed.

(*
Lemma add_prelude_enc_bit_is_true:
  forall (E : env) (cs : seq (seq literal)) (b : bool_eqType),
    interp_cnf E (add_prelude cs) -> enc_bit E lit_tt b = (b == true).
Proof.
  intros. case b; rewrite eqb_id; exact :(add_prelude_enc_bit_true _ H).
Qed.*)

Lemma bit_blast_udiv_rec_correct : forall ls1 g ls2 g' cs' lqs lrs qlrs rlrs E bs1 bs2 bsq bsr,
    bit_blast_udiv_rec g ls1 ls2 lqs lrs = (g', cs', qlrs, rlrs) ->
    size lqs = size ls2 -> size lrs = size ls2 ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    enc_bits E lqs bsq->
    enc_bits E lrs bsr ->
    interp_cnf E (add_prelude cs') ->
    enc_bits E qlrs (udivB_rec bs1 bs2 bsq bsr).1 /\
    enc_bits E rlrs (udivB_rec bs1 bs2 bsq bsr).2.
Proof.
  elim => [| ls1hd ls1tl IH] g ls2 g' cs' lqs lrs qlrs rlrs E bs1 bs2 bsq bsr.
  rewrite/bit_blast_udiv_rec. case => _ <- <- <-.
  rewrite enc_bits_nil_l.
  move => Hsz1 Hsz2. move => Hnil; rewrite (eqP Hnil)/=. done.
  rewrite /bit_blast_udiv_rec. rewrite-/bit_blast_udiv_rec.
  dcase (bit_blast_uge g (dropmsl (joinlsl ls1hd lrs)) ls2) => [[[guge] csuge] lrsuge] Hbbuge.
  dcase (bit_blast_sub guge (dropmsl (joinlsl ls1hd lrs)) ls2) =>[[[gsub] cssub] lrssub] Hbbsub.
  dcase (bit_blast_udiv_rec gsub ls1tl ls2 (dropmsl (joinlsl lrsuge lqs)) lrssub)=> [[[[gudivr] csudivr] lqrudivr] lrsudivr] Hbbudivr.
  case Hbbudivr2 : (bit_blast_udiv_rec guge ls1tl ls2 (dropmsl (joinlsl lrsuge lqs))) => [[[gudivr2 csudivr2] lqrudivr2] lrsudivr2].
  dcase (bit_blast_and guge (copy (size ls2) lrsuge) ls2) =>[[[gand] csand] lrsand] Hbband.
  dcase (bit_blast_sub gand (dropmsl (joinlsl ls1hd lrs)) lrsand) => [[[gsub2] cssub2] lrssub2] Hbbsub2.
  dcase (bit_blast_udiv_rec gsub2 ls1tl ls2 (dropmsl (joinlsl lrsuge lqs)) lrssub2) => [[[[gudivr3] csudivr3] lqrudivr3] lrsudivr3] Hudivr3.
  case bs1 => [| bs1hd bs1tl ]; first by rewrite enc_bits_nil_r.
  case Hlrsuget : (lrsuge == lit_tt).
  - case => _ <- <- <-.
    rewrite enc_bits_cons. 
    move => Hszlqs Hszlrs. move/andP => [Hencls1hd Hencls1tl].
    move => Henc2 Hencq Hencr.
    rewrite add_prelude_expand !interp_cnf_catrev.
    move/andP => [Htt Hand]. move/andP : Hand => [Hcsudivr Hcsuge]. move/andP: Hcsudivr => [Hcsudivr Hcssub].
    rewrite/=.
    have Hszuge : size (dropmsl (joinlsl ls1hd lrs)) = size ls2 by rewrite size_dropmsl size_joinlsl addnK Hszlrs.
    have Hencjl : enc_bits E (joinlsl ls1hd lrs) (joinlsb bs1hd bsr) by rewrite enc_bits_joinlsb Hencls1hd Hencr.
    have Hencuge1 : enc_bits E (dropmsl (joinlsl ls1hd lrs)) (dropmsb (joinlsb bs1hd bsr)) by rewrite (enc_bits_dropmsb Htt Hencjl).
    have Hevar : E var_tt. done.
    move : (add_prelude_to Hevar Hcsuge) => Haddcsuge.
    move : (bit_blast_uge_correct Hbbuge Hszuge Hencuge1 Henc2 Haddcsuge) => Hencugers.
    rewrite (eqP Hlrsuget) in Hencugers.
    move : (add_prelude_enc_bit_true  (dropmsb (joinlsb bs1hd bsr) >=# bs2)%bits Haddcsuge) . rewrite Hencugers /geB leBNlt.
    move => HnotltB. symmetry in HnotltB. rewrite ->Bool.negb_true_iff in HnotltB.
    rewrite ltB_to_nat in HnotltB. rewrite HnotltB/=.
    have Hszudiv1 : size (dropmsl (joinlsl lrsuge lqs)) = size ls2 by rewrite size_dropmsl size_joinlsl addnK Hszlqs.
    move : (bit_blast_sub_size_ss Hbbsub Hszuge) => Hszsub.
    move : (add_prelude_to Hevar Hcssub) => Haddcssub.
    move : (bit_blast_sub_correct Hbbsub Hencuge1 Henc2 Haddcssub Hszuge) => Hencsublrs.
    have Hencjtq : (enc_bits E (joinlsl lit_tt lqs) (joinlsb true bsq)) by rewrite enc_bits_joinlsb (add_prelude_enc_bit_true _ Haddcssub) Hencq. 
    have Hencdjlqs : enc_bits E (dropmsl (joinlsl lrsuge lqs)) (dropmsb (joinlsb true bsq)) by rewrite (eqP Hlrsuget) (enc_bits_dropmsb Htt Hencjtq).
    move : (add_prelude_to Hevar Hcsudivr) => Haddcsudivr.
    exact : (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Hbbudivr Hszudiv1 Hszsub Hencls1tl Henc2 Hencdjlqs Hencsublrs Haddcsudivr).
  - case Hlrsugef : (lrsuge == lit_ff).
    + case => _ <- <- <-.
      rewrite enc_bits_cons. 
      move => Hszlqs Hszlrs. move/andP => [Hencls1hd Hencls1tl].
      move => Henc2 Hencq Hencr.
      rewrite add_prelude_expand !interp_cnf_catrev.
      move/andP => [Htt Hudivr]. move/andP : Hudivr => [Hcsudivr Hcsuge].
      rewrite/=.
      have Hszuge : size (dropmsl (joinlsl lrsuge lqs)) = size ls2 by rewrite size_dropmsl size_joinlsl addnK Hszlqs.
      have Hszudivr : size (dropmsl (joinlsl ls1hd lrs)) = size ls2 by rewrite size_dropmsl size_joinlsl addnK Hszlrs.
      have Hencjl : enc_bits E (joinlsl ls1hd lrs) (joinlsb bs1hd bsr) by rewrite enc_bits_joinlsb Hencls1hd Hencr.
      have Hencuge1 : enc_bits E (dropmsl (joinlsl ls1hd lrs)) (dropmsb (joinlsb bs1hd bsr)) by rewrite (enc_bits_dropmsb Htt Hencjl).
      have Hevar : E var_tt. done.
      move : (add_prelude_to Hevar Hcsuge) => Haddcsuge.
      move : (bit_blast_uge_correct Hbbuge Hszudivr Hencuge1 Henc2 Haddcsuge) => Hencugers.
      rewrite (eqP Hlrsugef) in Hencugers.
      move : (add_prelude_enc_bit_is_not_true (dropmsb (joinlsb bs1hd bsr) >=# bs2)%bits Haddcsuge) . rewrite Hencugers /geB leBNlt Bool.negb_involutive. 
      move => HnotltB. 
      rewrite ltB_to_nat in HnotltB. rewrite -HnotltB/=.
      have Hencjtq : (enc_bits E (joinlsl lrsuge lqs) (joinlsb false bsq)) by rewrite enc_bits_joinlsb (eqP Hlrsugef) (add_prelude_enc_bit_is_not_true _ Haddcsuge) Hencq. 
      have Hencdjlqs : enc_bits E (dropmsl (joinlsl lrsuge lqs)) (dropmsb (joinlsb false bsq)) by rewrite (enc_bits_dropmsb Htt Hencjtq).
      move : (add_prelude_to Hevar Hcsudivr) => Haddcsudivr.
      exact : (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Hbbudivr2 Hszuge Hszudivr Hencls1tl Henc2 Hencdjlqs Hencuge1 Haddcsudivr).
    + case => _ <- <- <-.
      rewrite enc_bits_cons.
      move => Hszlqs Hszlrs. move/andP => [Hencls1hd Hencls1tl].
      move => Henc2 Hencq Hencr.
      rewrite add_prelude_expand !interp_cnf_catrev.
      move/andP => [Htt Hudivr]. move/andP : Hudivr => [Hcsudivr Hcsuge].
      move/andP : Hcsudivr => [Hcsudivr Hcsand].
      move/andP : Hcsudivr => [Hcsudivr Hcssub].
      rewrite/=.
      have Hszuge : size (dropmsl (joinlsl ls1hd lrs)) = size ls2 by rewrite size_dropmsl size_joinlsl addnK Hszlrs.
      have Hencjl : enc_bits E (joinlsl ls1hd lrs) (joinlsb bs1hd bsr) by rewrite enc_bits_joinlsb Hencls1hd Hencr.
      have Hencuge1 : enc_bits E (dropmsl (joinlsl ls1hd lrs)) (dropmsb (joinlsb bs1hd bsr)) by rewrite (enc_bits_dropmsb Htt Hencjl).
      have Hevar : E var_tt by done.
      move : (add_prelude_to Hevar Hcsuge) => Haddcsuge.
      move : (bit_blast_uge_correct Hbbuge Hszuge Hencuge1 Henc2 Haddcsuge) => Hencugers.
      rewrite /geB leBNlt ltB_to_nat in Hencugers.
      have Hszand : size (copy (size ls2) lrsuge) = size ls2 by rewrite size_nseq.
      have Henccp : enc_bits E (copy (size ls2) lrsuge) (copy (size ls2) (~~ (to_nat (dropmsb (joinlsb bs1hd bsr)) < to_nat bs2))) by rewrite (enc_bits_copy (size ls2) Hencugers).
      move : (add_prelude_to Hevar Hcsand) => Haddcsand.
      move : (bit_blast_and_correct Hbband Henccp Henc2 Haddcsand) => Hencandrs.
      move : (bit_blast_and_size_ss Hbband Hszand) => Hszandrs.
      have Hszsub : size (dropmsl (joinlsl ls1hd lrs)) = size lrsand by rewrite size_dropmsl size_joinlsl addnK -Hszandrs size_nseq Hszlrs.
      move : (add_prelude_to Hevar Hcssub) => Haddcssub.
      move : (bit_blast_sub_correct Hbbsub2 Hencuge1 Hencandrs Haddcssub Hszsub) => Hencsubrs.
      have Hencjlqs : enc_bits E (joinlsl lrsuge lqs) (joinlsb (~~ (to_nat (dropmsb (joinlsb bs1hd bsr)) < to_nat bs2)) bsq) by rewrite enc_bits_joinlsb Hencugers Hencq.
      have Hdjlqs : enc_bits E (dropmsl (joinlsl lrsuge lqs)) (dropmsb (joinlsb (~~ (to_nat (dropmsb (joinlsb bs1hd bsr)) < to_nat bs2)) bsq)) by rewrite (enc_bits_dropmsb Htt Hencjlqs).
      have Hszudivr : size (dropmsl (joinlsl lrsuge lqs)) = size ls2 by rewrite size_dropmsl size_joinlsl addnK Hszlqs.
      move : (bit_blast_sub_size_ss Hbbsub2 Hszsub) => Hszsubrs.
      have Hszlrssub2 : size lrssub2 = size ls2 by rewrite Hszsubrs -Hszandrs size_nseq.
      move : (add_prelude_to Hevar Hcsudivr) => Haddcsudivr.
      move : (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Hudivr3 Hszudivr Hszlrssub2 Hencls1tl Henc2 Hdjlqs Hencsubrs Haddcsudivr).
      move : (enc_bits_size Henc2) => Hszlsbs2. rewrite Hszlsbs2 andB_copy_case.
      case (~~ (to_nat (dropmsb (joinlsb bs1hd bsr)) < to_nat bs2)); first done.
      by rewrite from_natn0 subB0.
Qed.

Lemma enc_bits_ff : forall E cs n, interp_cnf E (add_prelude cs) -> enc_bits E (copy n lit_ff) (zeros n).
Proof.
  intros. apply enc_bits_copy. apply add_prelude_enc_bit_ff with cs. done.
Qed.

Lemma udivB_rec_0r:
  forall (n : nat) (m : bits),
  udivB_rec m (zeros n) (zeros n) (zeros n) = (ones n, m).
Proof.
Admitted.

Lemma bit_blast_udiv_correct g ls1 ls2 g' cs qlrs rlrs E bs1 bs2 :
  bit_blast_udiv g ls1 ls2 = (g', cs, qlrs, rlrs) ->
  size ls1 = size ls2 ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E qlrs (udivB bs1 bs2).1 /\
  enc_bits E rlrs (udivB bs1 bs2).2.
Proof.
  rewrite/bit_blast_udiv.
  dcase (bit_blast_eq g ls2 (copy (size ls2) lit_ff)) => [[[g_eq] cs_eq] lrs_eq] Hbbeq.
  case Hbbudivr : (bit_blast_udiv_rec g_eq (rev ls1) ls2 (copy (size (rev ls1)) lit_ff)
        (copy (size (rev ls1)) lit_ff)) => [[[g_udivr cs_udivr] lqs_udivr] lrs_udivr].
  dcase (bit_blast_and g_udivr (copy (size lqs_udivr) (neg_lit lrs_eq)) lqs_udivr) => [[[g_and] cs_and] lrs_and] Hbband.
  dcase (bit_blast_ite g_and lrs_eq (rev lrs_udivr) lrs_udivr) => [[[g_ite] cs_ite] lrs_ite] Hbbite.
  have Hszcp :  size ls2 = size (copy (size ls2) lit_ff) by rewrite size_nseq.
  case Hlrseqt : (lrs_eq == lit_tt).
  - case => _ <- <- <- .
    move => Hsz12 Henc1 Henc2 Hcnf.
    move : (add_prelude_enc_bit_ff Hcnf) => Hff.
    move : (enc_bits_copy (size ls2) Hff) => Hencff.
    move : (bit_blast_eq_correct Hbbeq Hszcp Henc2 Hencff Hcnf).
    rewrite/udivB (eqP Hlrseqt) (add_prelude_enc_bit_true (bs2 == copy (size ls2) false) Hcnf). move => Hbs20.
    rewrite (eqP Hbs20) size_rev -/b0 -/(zeros (size ls2)) to_nat_zeros from_natn0 eq_refl.
    move : (enc_bits_size Henc1) => Hszls1bs1.
      by rewrite/= -Hszls1bs1 Hsz12 /zeros (enc_bits_copy _ Hff) Henc1.
  - case Hlrseqf : (lrs_eq == lit_ff).
    + case => _ <- <- <- .
      move => Hsz12 Henc1 Henc2. rewrite add_prelude_catrev.
      move/andP => [Hcsudivr Hcseq].
      move : (add_prelude_enc_bit_ff Hcseq) => Hff.
      move : (enc_bits_copy (size ls2) Hff) => Hencff.
      move : (bit_blast_eq_correct Hbbeq Hszcp Henc2 Hencff Hcseq).
      move : (enc_bits_size Henc1) => Hszlsbs1.
      move : (enc_bits_size Henc2) => Hszlsbs2.
      rewrite/udivB (eqP Hlrseqf) size_rev/= -Hszlsbs1 Hsz12 Hszlsbs2 from_nat_to_nat -/b0 -/(zeros (size bs2)).
      move => Hencbs20.
      move : (add_prelude_enc_bit_is_not_true (bs2 == copy (size ls2) false) Hcseq).
      rewrite -/(zeros (size ls2)) Hszlsbs2 Hencbs20. move => Hbs2not0; symmetry in Hbs2not0.
      rewrite<-Bool.negb_false_iff in Hbs2not0. rewrite Bool.negb_involutive in Hbs2not0. rewrite Hbs2not0.
      move : (enc_bits_rev Henc1) => Hencrev1.
      generalize Hencff. rewrite -Hsz12 -(size_rev ls1). move => Hencffrev.
      generalize Hszcp. move => Hszcprev; symmetry in Hszcprev. rewrite -{1}Hsz12 -{1}(size_rev ls1) in Hszcprev. 
      move : (bit_blast_udiv_rec_correct Hbbudivr Hszcprev Hszcprev Hencrev1 Henc2 Hencffrev Hencffrev Hcsudivr). 
        by rewrite size_rev -/b0 Hsz12 Hszlsbs2 -/(zeros (size bs2)).
    + case => _ <- <- <- .
      move => Hsz12 Henc1 Henc2. rewrite !add_prelude_catrev.
      move/andP => [Hcsudivr Hcseq]. move/andP : Hcsudivr => [Hcsand Hcsudivr].
      move/andP : Hcsand => [Hcsite Hcsand].
      move : (add_prelude_enc_bit_ff Hcseq) => Hff.
      move : (enc_bits_copy (size ls2) Hff) => Hencff.
      move : (bit_blast_eq_correct Hbbeq Hszcp Henc2 Hencff Hcseq).
      move : (enc_bits_size Henc1) => Hszlsbs1.
      move : (enc_bits_size Henc2) => Hszlsbs2.
      rewrite/udivB size_rev/= -Hszlsbs1 Hsz12 Hszlsbs2 from_nat_to_nat -/b0 -/(zeros (size bs2)) . (*-(Bool.negb_involutive (bs2 == zeros (size bs2))) .*)
      move => Hencbs20t. generalize Hencbs20t. rewrite enc_bit_not. move => Hencbs20.
      (*
      move : (add_prelude_enc_bit_is_not_true (bs2 == copy (size ls2) false) Hcseq).
      rewrite -/(zeros (size ls2)) Hszlsbs2. move => Hbs2not0; symmetry in Hbs2not0.*)
      move : (enc_bits_rev Henc1) => Hencrev1.
      generalize Hencff. rewrite -Hsz12 -(size_rev ls1). move => Hencffrev.
      generalize Hszcp. move => Hszcprev; symmetry in Hszcprev. rewrite -{1}Hsz12 -{1}(size_rev ls1) in Hszcprev. 
      move : (bit_blast_udiv_rec_correct Hbbudivr Hszcprev Hszcprev Hencrev1 Henc2 Hencffrev Hencffrev Hcsudivr).
      rewrite size_rev -/b0 -/(zeros (size ls1)) Hsz12 Hszlsbs2.
      move => [Hencq Hencr].
      generalize Hencff. rewrite -Hsz12. move => Hencff1.
      move : (enc_bits_copy (size lqs_udivr)  Hencbs20) => Henccp.
      move : (bit_blast_and_correct Hbband Henccp Hencq Hcsand).
      move : (bit_blast_udiv_rec_size_ss Hbbudivr Hszcprev Hszcprev)=> [Hszq Hszr].
      move : (size_udivB_rec (rev bs1) bs2 (zeros (size bs2)) (zeros (size bs2))).
      rewrite size_zeros -Hszlsbs2 -{3}Hszq. move => Hszudivr.
      rewrite -{1}Hszudivr andB_copy_case.
      case Hbs20 : (bs2 == zeros (size ls2)).
      * move : Hencr. rewrite (eqP Hbs20) size_zeros udivB_rec_0r/= size_ones from_natn0. move => Hencrrev. move : (enc_bits_rev Hencrrev). rewrite revK.
        move => Henclrsudivr. move : (size_rev lrs_udivr). move/eqP => Hszrev.
        move : (bit_blast_ite_correct Hszrev Hbbite Hencbs20t Henclrsudivr Hencrrev Hcsite). by rewrite -Hszlsbs2 Hbs20.
      * rewrite/=.
        move => Henclrsudivr. move : (size_rev lrs_udivr). move/eqP => Hszrev.
        move : (enc_bits_rev Hencr) => Hencrrev.
        move : (bit_blast_ite_correct Hszrev Hbbite Hencbs20t Hencrrev Hencr Hcsite).
        by rewrite -Hszlsbs2 Hbs20.
Qed.

Lemma mk_env_udiv_rec_is_bit_blast_udiv_rec: forall ls1 E g ls2 lq lr g' cs qlrs rlrs E',
  mk_env_udiv_rec E g ls1 ls2 lq lr = (E', g', cs, qlrs, rlrs) ->
  bit_blast_udiv_rec g ls1 ls2 lq lr = (g', cs, qlrs, rlrs).
Proof.
  elim => [| ls1hd ls1tl IH] E g ls2 lq lr g' cs qlrs rlrs E'.
  - rewrite/=. by case => _ <- <- <- <-.
  - rewrite/=. 
    dcase (mk_env_uge E g (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lr)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    dcase (mk_env_udiv_rec E_sub g_sub ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_udiv_rec E_hd g_hd ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) (dropmsl (joinlsl ls1hd lr))) => [[[[[E_tl2 g_tl2] cs_tl2] lrs_tl2] lqs_tl2] Hmkudiv2].
    dcase (mk_env_udiv_rec E_sub2 g_sub2 ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub2) => [[[[[E_tl3 g_tl3] cs_tl3] lrs_tl3] lqs_tl3] Hmkudiv3].
    rewrite (mk_env_uge_is_bit_blast_uge Hmkuge) (mk_env_sub_is_bit_blast_sub Hmksub) (mk_env_and_is_bit_blast_and Hmkand) (mk_env_sub_is_bit_blast_sub Hmksub2) (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv) (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv2) (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv3). 
    case (lrs_hd == lit_tt); case (lrs_hd == lit_ff); by  move => [] _<- <- <- <-.
Qed.

Lemma mk_env_udiv_is_bit_blast_udiv : forall ls1 E g ls2 g' cs qlrs rlrs E',
  mk_env_udiv E g ls1 ls2 = (E', g', cs, qlrs, rlrs) ->
  bit_blast_udiv g ls1 ls2  = (g', cs, qlrs, rlrs).
Proof.
  rewrite/mk_env_udiv/bit_blast_udiv/=. move => ls1 E g ls2 g' cs qlrs rlrs E'.
  dcase (mk_env_eq E g ls2 (copy (size ls2) lit_ff)) => [[[[E_eq] g_eq] cs_eq] lrs_eq] Hmkeq.
  dcase (mk_env_udiv_rec E_eq g_eq (rev ls1) ls2 (copy (size (rev ls1)) lit_ff) (copy (size (rev ls1)) lit_ff)) => [[[[[E_udivr] g_udivr] cs_udivr] lqs_udivr] lrs_udivr] Hmkudivr.
  dcase (mk_env_and E_udivr g_udivr (copy (size lqs_udivr) (neg_lit lrs_eq)) lqs_udivr)=> [[[[E_and] g_and] cs_and] lrs_and] Hmkand.
  dcase (mk_env_ite E_and g_and lrs_eq (rev lrs_udivr) lrs_udivr) =>[[[[E_ite] g_ite] cs_ite] lrs_ite] Hmkite.
  rewrite (mk_env_eq_is_bit_blast_eq Hmkeq) (mk_env_udiv_rec_is_bit_blast_udiv_rec Hmkudivr) (mk_env_and_is_bit_blast_and Hmkand) (mk_env_ite_is_bit_blast_ite Hmkite).
  case (lrs_eq == lit_tt);
  case (lrs_eq == lit_ff); by case => _ <- <- <- <- .
Qed.  

Lemma mk_env_udiv_rec_newer_gen :
  forall ls1 E g ls2 lq lr E' g' cs lqs lrs,
    mk_env_udiv_rec E g ls1 ls2 lq lr = (E', g', cs, lqs, lrs) ->
    (g <=? g')%positive.
Proof.
  elim  => [| ls1hd ls1tl IH] E g ls2 lq lr E' g' cs lqs lrs.
  - move => [] _ <- _ _ _. exact: Pos.leb_refl.
  - rewrite/=.
    (*dcase (mk_env_udiv_rec E g ls1tl ls2 lq lr) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].*)
    dcase (mk_env_uge E g (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lr)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    dcase (mk_env_udiv_rec E_sub g_sub ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_udiv_rec E_hd g_hd ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) (dropmsl (joinlsl ls1hd lr))) => [[[[[E_tl2 g_tl2] cs_tl2] lrs_tl2] lqs_tl2] Hmkudiv2].
    dcase (mk_env_udiv_rec E_sub2 g_sub2 ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub2) => [[[[[E_tl3 g_tl3] cs_tl3] lrs_tl3] lqs_tl3] Hmkudiv3].
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv) => Hg2g5.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv2) => Hg0g5.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv3) => Hg4g5.
    move : (mk_env_uge_newer_gen Hmkuge) => Hgg0.
    move : (mk_env_sub_newer_gen Hmksub) => Hg0g2.
    move : (mk_env_and_newer_gen Hmkand) => Hg0g3.
    move : (mk_env_sub_newer_gen Hmksub2) => Hg3g4.
    move : (pos_leb_trans Hgg0 Hg0g5) => Hgg5.
    move : (pos_leb_trans Hgg0 (pos_leb_trans Hg0g2 Hg2g5)) => Hgg52.
    move : (pos_leb_trans (pos_leb_trans Hgg0 Hg0g3) (pos_leb_trans Hg3g4 Hg4g5)) => Hgg53.
    case (lrs_hd == lit_tt); case (lrs_hd == lit_ff); (move => [] _ <- _ _ _; try exact).
Qed.

Lemma mk_env_udiv_newer_gen :
  forall ls1 E g ls2 E' g' cs lqs lrs,
    mk_env_udiv E g ls1 ls2 = (E', g', cs, lqs, lrs) ->
    (g <=? g')%positive.
Proof.
  rewrite/mk_env_udiv/bit_blast_udiv/=. move => ls1 E g ls2 E' g' cs qlrs rlrs .
  dcase (mk_env_eq E g ls2 (copy (size ls2) lit_ff)) => [[[[E_eq] g_eq] cs_eq] lrs_eq] Hmkeq.
  dcase (mk_env_udiv_rec E_eq g_eq (rev ls1) ls2 (copy (size (rev ls1)) lit_ff) (copy (size (rev ls1)) lit_ff)) => [[[[[E_udivr] g_udivr] cs_udivr] lqs_udivr] lrs_udivr] Hmkudivr.
  dcase (mk_env_and E_udivr g_udivr (copy (size lqs_udivr) (neg_lit lrs_eq)) lqs_udivr)=> [[[[E_and] g_and] cs_and] lrs_and] Hmkand.
  dcase (mk_env_ite E_and g_and lrs_eq (rev lrs_udivr) lrs_udivr) =>[[[[E_ite] g_ite] cs_ite] lrs_ite] Hmkite.
  case (lrs_eq == lit_tt); case (lrs_eq == lit_ff); case => _ <- _ _ _ ; try apply (mk_env_eq_newer_gen Hmkeq).
  move: (mk_env_udiv_rec_newer_gen Hmkudivr) => Hnewudivr. move : (mk_env_eq_newer_gen Hmkeq) => Hneweq. 
  exact : (pos_leb_trans Hneweq Hnewudivr).
  move : (mk_env_ite_newer_gen Hmkite) => Hnewite. move : (mk_env_and_newer_gen Hmkand) => Hnewand. move: (mk_env_udiv_rec_newer_gen Hmkudivr) => Hnewudivr. move : (mk_env_eq_newer_gen Hmkeq) => Hneweq. 
  exact : (pos_leb_trans (pos_leb_trans Hneweq Hnewudivr) (pos_leb_trans Hnewand Hnewite)).
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
    dcase (mk_env_uge E g (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lr)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    dcase (mk_env_udiv_rec E_sub g_sub ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_udiv_rec E_hd g_hd ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) (dropmsl (joinlsl ls1hd lr))) => [[[[[E_tl2 g_tl2] cs_tl2] lrs_tl2] lqs_tl2] Hmkudiv2].
    dcase (mk_env_udiv_rec E_sub2 g_sub2 ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub2) => [[[[[E_tl3 g_tl3] cs_tl3] lrs_tl3] lqs_tl3] Hmkudiv3].
    (*
    dcase (mk_env_udiv_rec E g ls1tl ls2 lq lr) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_uge E_tl g_tl (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lrs_tl)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].*)
    move => Hres Htt Hls1 Hls2 Hlq Hlr.  move/andP: Hls1 => [Hls1hd Hls1tl].
    generalize Hres.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv) => Hg2g5.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv2) => Hg0g5.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv3) => Hg4g5.
    move : (mk_env_uge_newer_gen Hmkuge) => Hgg0.
    move : (mk_env_sub_newer_gen Hmksub) => Hg0g2.
    move : (mk_env_and_newer_gen Hmkand) => Hg0g3.
    move : (mk_env_sub_newer_gen Hmksub2) => Hg3g4.
    move : (pos_leb_trans Hgg0 Hg0g5) => Hgg5.
    move : (pos_leb_trans Hgg0 (pos_leb_trans Hg0g2 Hg2g5)) => Hgg52.
    move : (pos_leb_trans (pos_leb_trans Hgg0 Hg0g3) (pos_leb_trans Hg3g4 Hg4g5)) => Hgg53.
    move : (pos_leb_trans Hgg0 (pos_leb_trans Hg0g3 Hg3g4 )) => Hgg4.
    move : ((pos_leb_trans Hg0g3 Hg3g4 )) => Hg0g4.
    move : (mk_env_uge_newer_res Hmkuge) => Hg0ls2.
    move : (mk_env_sub_newer_res Hmksub) => Hg2ls3.
    move : (mk_env_sub_newer_res Hmksub2) => Hg4ls5. 
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl Hg0ls2 (newer_than_lits_le_newer Hlq Hgg0))) => Hdjlq.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl Hls1hd ( Hlr ))) => Hdjlr.
    move : (newer_than_lits_le_newer Hdjlr Hgg0) => Hdjlrg0.
    move/andP : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hgg0 Hg0g2)) (newer_than_lits_le_newer Hls1tl (pos_leb_trans Hgg0 Hg0g2)) (newer_than_lits_le_newer Hls2 (pos_leb_trans Hgg0 Hg0g2)) (newer_than_lits_le_newer Hdjlq Hg0g2)   Hg2ls3) => [Hg0lq Hg0lr].
    move/andP : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv2 (newer_than_lit_le_newer Htt  Hgg0) (newer_than_lits_le_newer Hls1tl (Hgg0 )) (newer_than_lits_le_newer Hls2 ( Hgg0 )) (Hdjlq ) Hdjlrg0  ) => [Hgtl2lq Hgtl2lr].
    move/andP : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv3 (newer_than_lit_le_newer Htt  Hgg4) (newer_than_lits_le_newer Hls1tl (Hgg4 )) (newer_than_lits_le_newer Hls2 ( Hgg4 )) (newer_than_lits_le_newer Hdjlq Hg0g4) Hg4ls5) => [Hgtl3lq Hgtl3lr].
    move : (newer_than_lit_le_newer Hg0ls2 Hg0g2) => Hg5ls6.
    move : (newer_than_lit_le_newer Hg0ls2 Hg0g3) => Hg8ls9.
    move : (newer_than_lit_le_newer Hls1hd Hgg0) => Hg9ls0.
    case (lrs_hd == lit_tt); case (lrs_hd == lit_ff); move => [] _ <- _ <- <-.
    by rewrite Hg0lq Hg0lr. by rewrite Hg0lq Hg0lr.
    by rewrite Hgtl2lq Hgtl2lr. by rewrite Hgtl3lq Hgtl3lr. 
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
  dcase (mk_env_eq E g ls2 (copy (size ls2) lit_ff)) => [[[[E_eq] g_eq] cs_eq] lrs_eq] Hmkeq.
  dcase (mk_env_udiv_rec E_eq g_eq (rev ls1) ls2 (copy (size (rev ls1)) lit_ff) (copy (size (rev ls1)) lit_ff)) => [[[[[E_udivr] g_udivr] cs_udivr] lqs_udivr] lrs_udivr] Hmkudivr.
  dcase (mk_env_and E_udivr g_udivr (copy (size lqs_udivr) (neg_lit lrs_eq)) lqs_udivr)=> [[[[E_and] g_and] cs_and] lrs_and] Hmkand.
  dcase (mk_env_ite E_and g_and lrs_eq (rev lrs_udivr) lrs_udivr) =>[[[[E_ite] g_ite] cs_ite] lrs_ite] Hmkite.
  move : (mk_env_ite_newer_gen Hmkite) => Hnewite. move : (mk_env_and_newer_gen Hmkand) => Hnewand. move: (mk_env_udiv_rec_newer_gen Hmkudivr) => Hnewudivr. move : (mk_env_eq_newer_gen Hmkeq) => Hneweq. 
  case (lrs_eq == lit_tt); case (lrs_eq == lit_ff); case => _ <- _ <- <- ; move => Htt Hls1 Hls2.
  rewrite (newer_than_lits_le_newer Hls1 Hneweq) newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff (newer_than_lit_le_newer Htt Hneweq); done.
  rewrite (newer_than_lits_le_newer Hls1 Hneweq) newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff (newer_than_lit_le_newer Htt Hneweq); done.
  have Hnewcp : (newer_than_lits g_eq (copy (size (rev ls1)) lit_ff)) by (rewrite newer_than_lits_copy; last by rewrite -newer_than_lit_tt_ff (newer_than_lit_le_newer Htt Hneweq)).
  exact : (mk_env_udiv_rec_newer_res Hmkudivr (newer_than_lit_le_newer Htt Hneweq) (newer_than_lits_le_newer (newer_than_lits_rev Hls1) Hneweq) (newer_than_lits_le_newer Hls2 Hneweq) Hnewcp Hnewcp).
  rewrite (mk_env_ite_newer_res Hmkite).
  move : (pos_leb_trans Hneweq Hnewudivr) => Hgudivr.
  have Hnewcp : (newer_than_lits g_udivr (copy (size lqs_udivr) (neg_lit lrs_eq))) by rewrite newer_than_lits_copy; last by rewrite newer_than_lit_neg (newer_than_lit_le_newer (mk_env_eq_newer_res Hmkeq) Hnewudivr).
  have Hnewrev : (newer_than_lits g_eq (rev ls1)) by rewrite (newer_than_lits_rev (newer_than_lits_le_newer Hls1 Hneweq)).
  have Hnewcpeq : (newer_than_lits g_eq (copy (size (rev ls1)) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite -newer_than_lit_tt_ff (newer_than_lit_le_newer Htt Hneweq).
  
  move/andP : (mk_env_udiv_rec_newer_res Hmkudivr (newer_than_lit_le_newer Htt Hneweq) Hnewrev (newer_than_lits_le_newer Hls2 Hneweq) Hnewcpeq Hnewcpeq) => [Hnewq Hnewr].
  by rewrite (newer_than_lits_le_newer (mk_env_and_newer_res Hmkand (newer_than_lit_le_newer Htt Hgudivr) Hnewcp Hnewr) Hnewite).
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
    (*dcase (mk_env_udiv_rec E g ls1tl ls2 lq lr) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_uge E_tl g_tl (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lrs_tl)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].*)
    dcase (mk_env_uge E g (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_udiv_rec E_sub g_sub ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub) =>[[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_udiv_rec E_hd g_hd ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) (dropmsl (joinlsl ls1hd lr))) =>
    [[[[[E_tl2 g_tl2] cs_tl2] lrs_tl2] lqs_tl2] Hmkudiv2].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lr)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    dcase (mk_env_udiv_rec E_sub2 g_sub2 ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub2) =>
    [[[[[E_tl3 g_tl3] cs_tl3] lrs_tl3] lqs_tl3] Hmkudiv3].
    move => Hres Htt Hls1 Hls2 Hlq Hlr Hszq Hszr.  move/andP: Hls1 => [Hls1hd Hls1tl].
    move : (mk_env_uge_newer_gen Hmkuge) => Hg0g1.
    move : (mk_env_sub_newer_gen Hmksub) => Hg1g2.
    move : (pos_leb_trans Hg0g1  Hg1g2) => Hg0g2.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv) => Hg2g3.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv2) => Hg2g3'.
    move : (mk_env_and_newer_gen Hmkand) => Hg1g2''.
    move : (mk_env_sub_newer_gen Hmksub2) => Hg2''g3''.
    move : (pos_leb_trans Hg0g1 (pos_leb_trans Hg1g2 Hg2g3)) => Hg0g3.
    move : (pos_leb_trans Hg1g2'' Hg2''g3'') => Hg1g3''.
    move : (pos_leb_trans Hg0g1 Hg1g3'') => Hg0g3''.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv3) => Hg3''g4''.
    move : (pos_leb_trans Hg1g3'' Hg3''g4'') => Hg1g4''.
    move: (newer_than_lit_le_newer Htt Hg0g1) => Httg1. rewrite newer_than_lit_tt_ff in Httg1.
    move : (mk_env_uge_newer_res Hmkuge) => Hlrshd.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl (newer_than_lit_le_newer Hlrshd Hg1g2) (newer_than_lits_le_newer Hlq Hg0g2))) => Hdjlq.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl ( Hlrshd ) (newer_than_lits_le_newer Hlq Hg0g1))) => Hdjlq0.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl ( Hls1hd ) ( Hlr ))) => Hdjlr0.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl (newer_than_lit_le_newer Hls1hd Hg0g2) (newer_than_lits_le_newer Hlr Hg0g2))) => Hdjlr.
    move : (mk_env_sub_newer_res Hmksub) => Hlrssub.
    move : (mk_env_sub_newer_res Hmksub2) => Hlrssub2.
    move/andP : (mk_env_udiv_rec_newer_res Hmkudiv (newer_than_lit_le_newer Htt Hg0g2) (newer_than_lits_le_newer Hls1tl Hg0g2) (newer_than_lits_le_newer Hls2 Hg0g2) Hdjlq Hlrssub) => [Hlqstl Hlrstl].
    (*move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl (newer_than_lit_le_newer Hls1hd Hg0g1) (newer_than_lits_le_newer Hlrstl Hg0g1))) => Hdj.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl (newer_than_lit_le_newer Hls1hd Hgg0) Hlrstl)) => Hdjtl.
    move : (newer_than_lits_le_newer Hls2 Hgg1) => Hg1ls2hd.*)
    have Hszdjq : (size (dropmsl (joinlsl lrs_hd lq)) = size  ls2) by rewrite size_dropmsl size_joinlsl addnK.
    have Hszdjr : (size (dropmsl (joinlsl ls1hd lr)) = size ls2) by rewrite size_dropmsl size_joinlsl addnK.
    move : (bit_blast_sub_size_ss (mk_env_sub_is_bit_blast_sub Hmksub) Hszdjr) => Hsz1.
    have Hszcp : size (copy (size ls2) lrs_hd) = size ls2 by rewrite size_nseq.
    move : (bit_blast_and_size_ss (mk_env_and_is_bit_blast_and Hmkand) Hszcp) => Hszcp0.
    have  Hdjand : (size (dropmsl (joinlsl ls1hd lr)) = size lrs_and) by rewrite size_dropmsl size_joinlsl addnK Hszr -Hszcp0 size_nseq.
    move : (bit_blast_sub_size_ss (mk_env_sub_is_bit_blast_sub Hmksub2) Hdjand) => Hsz2.
    rewrite -Hszcp0 size_nseq in Hsz2.
    move : (bit_blast_udiv_rec_size_ss (mk_env_udiv_rec_is_bit_blast_udiv_rec Hmkudiv) Hszdjq Hsz1) => [Hszrtl Hszqtl].
    have Hszdj : (size (dropmsl (joinlsl ls1hd lrs_tl)) = size ls2) by rewrite size_dropmsl size_joinlsl addnK Hszrtl.
    move : (mk_env_sub_newer_cnf Hmksub Httg1 (newer_than_lits_le_newer Hdjlr0 Hg0g1) (newer_than_lits_le_newer Hls2 Hg0g1)) => Hg2ls3.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv (newer_than_lit_le_newer Htt Hg0g2) (newer_than_lits_le_newer Hls1tl Hg0g2) (newer_than_lits_le_newer Hls2 Hg0g2) Hdjlq Hlrssub Hszdjq Hsz1) => Hg0cs0.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv2 (newer_than_lit_le_newer Htt Hg0g1) (newer_than_lits_le_newer Hls1tl Hg0g1) (newer_than_lits_le_newer Hls2 Hg0g1) Hdjlq0 (newer_than_lits_le_newer Hdjlr0 Hg0g1) Hszdjq Hszdjr) => Hg1cs1.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv3 (newer_than_lit_le_newer Htt (Hg0g3'' )) (newer_than_lits_le_newer Hls1tl Hg0g3'') (newer_than_lits_le_newer Hls2 Hg0g3'') (newer_than_lits_le_newer Hdjlq0 Hg1g3'') Hlrssub2 Hszdjq Hsz2) => Hg3cs3.
    move : (mk_env_uge_newer_cnf Hmkuge (Htt ) Hdjlr0 (Hls2 )) => Hg1cs2.
    move : (mk_env_uge_newer_res Hmkuge) => Hg1rs1.
    move : (newer_than_cnf_le_newer Hg1cs2 Hg1g2) => Hg2cs2.
    move : (mk_env_and_newer_res Hmkand (newer_than_lit_le_newer Htt Hg0g1) (newer_than_lits_copy (size ls2) Hg1rs1) (newer_than_lits_le_newer Hls2 Hg0g1)) => Hg3ls3.
    move : (mk_env_sub_newer_cnf Hmksub2 (newer_than_lit_le_newer Httg1 Hg1g2'') (newer_than_lits_le_newer Hdjlr0 (pos_leb_trans Hg0g1 Hg1g2'')) Hg3ls3) => Hg4cs5. (*rewrite Hszdj in Hg4cs5.*)
    move : (mk_env_and_newer_cnf Hmkand (newer_than_lit_le_newer Htt Hg0g1) (newer_than_lits_copy (size ls2) Hg1rs1) (newer_than_lits_le_newer Hls2 Hg0g1)) => Hg4cs4.
    generalize Hres.
    case (lrs_hd == lit_tt); case (lrs_hd == lit_ff); move => [] _ <- <- _ _; rewrite !newer_than_cnf_catrev; 
    try by rewrite Hg0cs0 (newer_than_cnf_le_newer Hg2ls3 Hg2g3) (newer_than_cnf_le_newer Hg2cs2 Hg2g3).
    by rewrite Hg1cs1 (newer_than_cnf_le_newer Hg1cs2 Hg2g3').
    by rewrite Hg3cs3 (newer_than_cnf_le_newer Hg4cs5 Hg3''g4'') (newer_than_cnf_le_newer Hg4cs4 (pos_leb_trans Hg2''g3'' Hg3''g4'')) (newer_than_cnf_le_newer Hg1cs2 Hg1g4'').
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
  dcase (mk_env_eq E g ls2 (copy (size ls2) lit_ff)) => [[[[E_eq] g_eq] cs_eq] lrs_eq] Hmkeq.
  dcase (mk_env_udiv_rec E_eq g_eq (rev ls1) ls2 (copy (size (rev ls1)) lit_ff) (copy (size (rev ls1)) lit_ff)) => [[[[[E_udivr] g_udivr] cs_udivr] lqs_udivr] lrs_udivr] Hmkudivr.
  dcase (mk_env_and E_udivr g_udivr (copy (size lqs_udivr) (neg_lit lrs_eq)) lqs_udivr)=> [[[[E_and] g_and] cs_and] lrs_and] Hmkand.
  dcase (mk_env_ite E_and g_and lrs_eq (rev lrs_udivr) lrs_udivr) =>[[[[E_ite] g_ite] cs_ite] lrs_ite] Hmkite.
  move : (mk_env_ite_newer_gen Hmkite) => Hnewite. move : (mk_env_and_newer_gen Hmkand) => Hnewand. move: (mk_env_udiv_rec_newer_gen Hmkudivr) => Hnewudivr. move : (mk_env_eq_newer_gen Hmkeq) => Hneweq. 
  case (lrs_eq == lit_tt); case (lrs_eq == lit_ff); case => _ <- <- _ _; move => Htt Hsz Hls1 Hls2.
  - have Hcp2: (newer_than_lits g (copy (size ls2) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    exact: (mk_env_eq_newer_cnf Hmkeq Htt Hls2 Hcp2).
  - have Hcp2: (newer_than_lits g (copy (size ls2) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    exact: (mk_env_eq_newer_cnf Hmkeq Htt Hls2 Hcp2).
  - rewrite newer_than_cnf_catrev. 
    have Hrev1 : (newer_than_lits g (rev ls1)) by rewrite (newer_than_lits_rev Hls1).
    have Hcp2: (newer_than_lits g (copy (size (rev ls1)) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    have Hszcp : (size (copy (size (rev ls1)) lit_ff) = size ls2) by rewrite size_nseq size_rev.
    rewrite (mk_env_udiv_rec_newer_cnf Hmkudivr (newer_than_lit_le_newer Htt Hneweq) (newer_than_lits_le_newer Hrev1 Hneweq) (newer_than_lits_le_newer Hls2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) Hszcp Hszcp).
    have Hcpf : (newer_than_lits g (copy (size ls2) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    by rewrite (newer_than_cnf_le_newer (mk_env_eq_newer_cnf Hmkeq Htt Hls2 Hcpf) Hnewudivr).
  - rewrite 3!newer_than_cnf_catrev. 
    have Hrev1 : (newer_than_lits g (rev ls1)) by rewrite (newer_than_lits_rev Hls1).
    have Hcp2: (newer_than_lits g (copy (size (rev ls1)) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    have Hszcp : (size (copy (size (rev ls1)) lit_ff) = size ls2) by rewrite size_nseq size_rev.
    move: (mk_env_udiv_rec_newer_cnf Hmkudivr (newer_than_lit_le_newer Htt Hneweq) (newer_than_lits_le_newer Hrev1 Hneweq) (newer_than_lits_le_newer Hls2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) Hszcp Hszcp).
    have Hcpf : (newer_than_lits g (copy (size ls2) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    move : (newer_than_cnf_le_newer (mk_env_eq_newer_cnf Hmkeq Htt Hls2 Hcpf) Hnewudivr).
    move => Hncnfeq Hncnfudivr.
    move : (pos_leb_trans Hnewand Hnewite) => Hgnewite.
    rewrite (newer_than_cnf_le_newer Hncnfeq Hgnewite) (newer_than_cnf_le_newer Hncnfudivr Hgnewite).
    move : (pos_leb_trans (pos_leb_trans Hneweq Hnewudivr) Hnewand) => Hgand.
    move : (pos_leb_trans Hnewudivr Hnewand) => Hgeqand.
    move : (mk_env_eq_newer_res Hmkeq ) => Hnlrseq.
    move/andP : (mk_env_udiv_rec_newer_res Hmkudivr (newer_than_lit_le_newer Htt Hneweq) (newer_than_lits_le_newer Hrev1 Hneweq) (newer_than_lits_le_newer Hls2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq)) => [Hnewq Hnewr].
    have Hnewerv : newer_than_lits g_and (rev lrs_udivr) by rewrite newer_than_lits_rev; last rewrite (newer_than_lits_le_newer Hnewq Hnewand).
    move : (mk_env_ite_newer_cnf Hmkite (newer_than_lit_le_newer Htt Hgand) (newer_than_lit_le_newer Hnlrseq Hgeqand) Hnewerv (newer_than_lits_le_newer Hnewq Hnewand)) => Hncnfite.
    rewrite Hncnfite.
    move : (pos_leb_trans Hneweq Hnewudivr) => Hgudivr.
    have Hnewcp : (newer_than_lits g_udivr (copy (size lqs_udivr) (neg_lit lrs_eq))) by rewrite newer_than_lits_copy; last by rewrite newer_than_lit_neg (newer_than_lit_le_newer (mk_env_eq_newer_res Hmkeq) Hnewudivr).
    move : (mk_env_and_newer_cnf Hmkand (newer_than_lit_le_newer Htt Hgudivr) Hnewcp Hnewr) => Hncnfand.
    by rewrite (newer_than_cnf_le_newer Hncnfand Hnewite).
Qed.

Lemma mk_env_udiv_rec_preserve :
  forall ls1 E g ls2 lq lr E' g' cs lqs lrs,
    mk_env_udiv_rec E g ls1 ls2 lq lr = (E', g', cs, lqs, lrs) ->
    env_preserve E E' g.
Proof.
  elim => [|ls1hd ls1tl IH] E g ls2 lq lr E' g' cs lqs lrs.
  - by case => <- _ _ _. 
  - rewrite/=.
    (*dcase (mk_env_udiv_rec E g ls1tl ls2 lq lr) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_uge E_tl g_tl (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lrs_tl)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].*)
    dcase (mk_env_uge E g (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_udiv_rec E_sub g_sub ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub) =>[[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_udiv_rec E_hd g_hd ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) (dropmsl (joinlsl ls1hd lr))) =>
    [[[[[E_tl2 g_tl2] cs_tl2] lrs_tl2] lqs_tl2] Hmkudiv2].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lr)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    dcase (mk_env_udiv_rec E_sub2 g_sub2 ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub2) =>
    [[[[[E_tl3 g_tl3] cs_tl3] lrs_tl3] lqs_tl3] Hmkudiv3].
    move => Hres .  
    
    move : (mk_env_uge_preserve Hmkuge) => HE0E1g0.
    move : (mk_env_sub_preserve Hmksub) => HE1E2g1.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv ) => HE2E3g.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv2 ) => HE2E3'g.
    move : (mk_env_and_preserve Hmkand) => HE1E2''g1.
    move : (mk_env_sub_preserve Hmksub2) => HE2''E3''g3.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv3 ) => HE3''E4''g.
    move : (mk_env_uge_newer_gen Hmkuge) => Hg0g1.
    move : (mk_env_sub_newer_gen Hmksub) => Hg1g2.
    move : (pos_leb_trans Hg0g1  Hg1g2) => Hg0g2.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv) => Hg2g3.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv2) => Hg2g3'.
    move : (mk_env_and_newer_gen Hmkand) => Hg1g2''.
    move : (mk_env_sub_newer_gen Hmksub2) => Hg2''g3''.
    move : (pos_leb_trans Hg0g1 (pos_leb_trans Hg1g2 Hg2g3)) => Hg0g3.
    move : (pos_leb_trans Hg1g2'' Hg2''g3'') => Hg1g3''.
    move : (pos_leb_trans Hg0g1 Hg1g3'') => Hg0g3''.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv3) => Hg3''g4''.
    move : (pos_leb_trans Hg1g3'' Hg3''g4'') => Hg1g4''.
    generalize Hres.
    case (lrs_hd == lit_tt); case (lrs_hd == lit_ff); move => [] <- _ _ _ _; 
    try by (move : (env_preserve_trans HE0E1g0 (env_preserve_le HE1E2g1 Hg0g1)) => HE0E2g0;
    exact : (env_preserve_trans HE0E2g0 (env_preserve_le HE2E3g Hg0g2))).
    exact : (env_preserve_trans HE0E1g0 (env_preserve_le HE2E3'g Hg0g1)).
    move : (env_preserve_trans HE0E1g0 (env_preserve_le HE1E2''g1 Hg0g1)) => HE0E2''g0.
    move : (env_preserve_trans HE0E2''g0 (env_preserve_le HE2''E3''g3 (pos_leb_trans Hg0g1 Hg1g2''))) => HE0E3''g0.
    exact : (env_preserve_trans HE0E3''g0 (env_preserve_le HE3''E4''g Hg0g3'')).
Qed.

Lemma mk_env_udiv_preserve :
  forall E g ls1 ls2 E' g' cs lqs lrs,
    mk_env_udiv E g ls1 ls2 = (E', g', cs, lqs, lrs) ->
    env_preserve E E' g.
Proof.
  move => E g ls1 ls2 E' g' cs lqs lrs.
  rewrite /mk_env_udiv.
  dcase (mk_env_eq E g ls2 (copy (size ls2) lit_ff)) => [[[[E_eq] g_eq] cs_eq] lrs_eq] Hmkeq.
  dcase (mk_env_udiv_rec E_eq g_eq (rev ls1) ls2 (copy (size (rev ls1)) lit_ff) (copy (size (rev ls1)) lit_ff)) => [[[[[E_udivr] g_udivr] cs_udivr] lqs_udivr] lrs_udivr] Hmkudivr.
  dcase (mk_env_and E_udivr g_udivr (copy (size lqs_udivr) (neg_lit lrs_eq)) lqs_udivr)=> [[[[E_and] g_and] cs_and] lrs_and] Hmkand.
  dcase (mk_env_ite E_and g_and lrs_eq (rev lrs_udivr) lrs_udivr) =>[[[[E_ite] g_ite] cs_ite] lrs_ite] Hmkite.
  move : (mk_env_ite_newer_gen Hmkite) => Hnewite. move : (mk_env_and_newer_gen Hmkand) => Hnewand. move: (mk_env_udiv_rec_newer_gen Hmkudivr) => Hnewudivr. move : (mk_env_eq_newer_gen Hmkeq) => Hneweq. 
  case (lrs_eq == lit_tt); case (lrs_eq == lit_ff); case => <- _ _ _ _; try (exact : (mk_env_eq_preserve Hmkeq)).
  - move : (mk_env_udiv_rec_preserve Hmkudivr) => HEEudivrgeq.
    move : (mk_env_eq_preserve Hmkeq) => HEEeq.
    move : (env_preserve_le HEEudivrgeq Hneweq) => HEEudivr.
    exact : (env_preserve_trans HEEeq HEEudivr).
  - move : (mk_env_ite_preserve Hmkite) => HEandEitegand.
    move : (mk_env_and_preserve Hmkand) => HEuEandgu.
    move : (mk_env_udiv_rec_preserve Hmkudivr) => HEEudivrgeq.
    move : (mk_env_eq_preserve Hmkeq) => HEEeq.
    move : (env_preserve_trans HEEeq (env_preserve_le HEEudivrgeq Hneweq)) => HEEu.
    move : (pos_leb_trans Hneweq Hnewudivr) => Hggu.
    move : (env_preserve_trans HEEu (env_preserve_le HEuEandgu Hggu)) => HEEand.
    move : (pos_leb_trans Hneweq (pos_leb_trans Hnewudivr Hnewand)) => Hggand.
    exact : (env_preserve_trans HEEand (env_preserve_le HEandEitegand Hggand)).
Qed.

Lemma mk_env_udiv_rec_sat :
  forall ls1 E g ls2 lq lr E' g' cs lqs lrs,
    mk_env_udiv_rec E g ls1 ls2 lq lr = (E', g', cs, lqs, lrs) ->
    size lq = size ls2 -> size lr = size ls2 -> 
    newer_than_lit g lit_tt ->
    newer_than_lits g lq ->
    newer_than_lits g lr ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  elim => [|ls1hd ls1tl IH] E g ls2 lq lr E' g' cs lqs lrs.
  - by case => _ _ <- _ _ _ _.
  - rewrite/=.
    dcase (mk_env_uge E g (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_udiv_rec E_sub g_sub ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub) =>[[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_udiv_rec E_hd g_hd ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) (dropmsl (joinlsl ls1hd lr))) =>
    [[[[[E_tl2 g_tl2] cs_tl2] lrs_tl2] lqs_tl2] Hmkudiv2].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lr)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    dcase (mk_env_udiv_rec E_sub2 g_sub2 ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub2) =>
    [[[[[E_tl3 g_tl3] cs_tl3] lrs_tl3] lqs_tl3] Hmkudiv3].
    (*
    dcase (mk_env_udiv_rec E g ls1tl ls2 lq lr) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_uge E_tl g_tl (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lrs_tl)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
     *)
    move=> Hres Hszq Hszr Htt Hlq Hlr Hls1 Hls2. move/andP : Hls1 => [Hls1hd Hls1tl].
    have Hszdjq : (size (dropmsl (joinlsl lrs_hd lq)) = size  ls2) by rewrite size_dropmsl size_joinlsl addnK.
    have Hszdjr : (size (dropmsl (joinlsl ls1hd lr)) = size ls2) by rewrite size_dropmsl size_joinlsl addnK.
    move : (bit_blast_sub_size_ss (mk_env_sub_is_bit_blast_sub Hmksub) Hszdjr) => Hsz1.
    have Hszcp : size (copy (size ls2) lrs_hd) = size ls2 by rewrite size_nseq.
    move : (bit_blast_and_size_ss (mk_env_and_is_bit_blast_and Hmkand) Hszcp) => Hszcp0.
    have  Hdjand : (size (dropmsl (joinlsl ls1hd lr)) = size lrs_and) by rewrite size_dropmsl size_joinlsl addnK Hszr -Hszcp0 size_nseq.
    move : (bit_blast_sub_size_ss (mk_env_sub_is_bit_blast_sub Hmksub2) Hdjand) => Hsz2.
    rewrite -Hszcp0 size_nseq in Hsz2.
    move : (bit_blast_udiv_rec_size_ss (mk_env_udiv_rec_is_bit_blast_udiv_rec Hmkudiv) Hszdjq Hsz1) => [Hszrtl Hszqtl].
    have Hszdj : (size (dropmsl (joinlsl ls1hd lrs_tl)) = size ls2) by rewrite size_dropmsl size_joinlsl addnK Hszrtl.
    move : (mk_env_uge_preserve Hmkuge) => HE0E1g0.
    move : (mk_env_sub_preserve Hmksub) => HE1E2g1.
    move : (mk_env_uge_newer_gen Hmkuge) => Hg0g1.
    move : (mk_env_sub_newer_gen Hmksub) => Hg1g2.
    move : (pos_leb_trans Hg0g1  Hg1g2) => Hg0g2.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv) => Hg2g3.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv2) => Hg2g3'.
    move : (mk_env_and_newer_gen Hmkand) => Hg1g2''.
    move : (mk_env_sub_newer_gen Hmksub2) => Hg2''g3''.
    move : (pos_leb_trans Hg0g1 (pos_leb_trans Hg1g2 Hg2g3)) => Hg0g3.
    move : (pos_leb_trans Hg1g2'' Hg2''g3'') => Hg1g3''.
    move : (pos_leb_trans Hg0g1 Hg1g3'') => Hg0g3''.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv3) => Hg3''g4''.
    move : (pos_leb_trans Hg1g3'' Hg3''g4'') => Hg1g4''.

    move : (mk_env_uge_newer_res Hmkuge) => Hlrshd.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl (newer_than_lit_le_newer Hlrshd Hg1g2) (newer_than_lits_le_newer Hlq Hg0g2))) => Hdjlq.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl ( Hlrshd ) (newer_than_lits_le_newer Hlq Hg0g1))) => Hdjlq0.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl ( Hls1hd ) ( Hlr ))) => Hdjlr0.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl (newer_than_lit_le_newer Hls1hd Hg0g2) (newer_than_lits_le_newer Hlr Hg0g2))) => Hdjlr.
    move : (mk_env_sub_newer_res Hmksub) => Hlrssub.
    move : (mk_env_sub_newer_res Hmksub2) => Hlrssub2.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv Hszdjq Hsz1 (newer_than_lit_le_newer Htt Hg0g2) Hdjlq Hlrssub (newer_than_lits_le_newer Hls1tl Hg0g2) (newer_than_lits_le_newer Hls2 Hg0g2) )=> HE2E3g.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv2 Hszdjq Hszdjr (newer_than_lit_le_newer Htt Hg0g1) Hdjlq0 (newer_than_lits_le_newer Hdjlr0 Hg0g1) (newer_than_lits_le_newer Hls1tl Hg0g1) (newer_than_lits_le_newer Hls2 Hg0g1)) => HE2E3'g.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv3 Hszdjq Hsz2 (newer_than_lit_le_newer Htt Hg0g3'') (newer_than_lits_le_newer Hdjlq0 Hg1g3'' ) Hlrssub2 (newer_than_lits_le_newer Hls1tl Hg0g3'') (newer_than_lits_le_newer Hls2 Hg0g3'')) => HE2E3'g3''.
    move : (mk_env_and_preserve Hmkand) => HEhdEandg1.
    move : (mk_env_sub_preserve Hmksub2) => HEandEsub2g3.
    move : (mk_env_uge_preserve Hmkuge) => HEEhdg0.
    move : (mk_env_udiv_rec_preserve Hmkudiv)=>HEsubEtlg3.
    have Hff : (newer_than_lit g lit_ff) by rewrite -newer_than_lit_tt_ff; done. 
    move : (mk_env_sub_preserve Hmksub) => HEhdEsub.
    move : (mk_env_sub_newer_cnf Hmksub (newer_than_lit_le_newer Hff Hg0g1) (newer_than_lits_le_newer Hdjlr0 Hg0g1) (newer_than_lits_le_newer Hls2 Hg0g1)) => Hntcsub.
    move : (mk_env_uge_sat Hmkuge Htt Hdjlr0 Hls2) => HEhdcshd.
    move : (mk_env_uge_newer_cnf Hmkuge Htt Hdjlr0 Hls2) => Hghdcshd.
    move : (env_preserve_cnf (env_preserve_trans HEhdEsub (env_preserve_le HEsubEtlg3 Hg1g2)) Hghdcshd) => Hcshdeq. rewrite HEhdcshd in Hcshdeq.
    move : (env_preserve_cnf HEsubEtlg3 Hntcsub) => Hcssubeq.
    move : (mk_env_sub_sat Hmksub (newer_than_lit_le_newer Hff Hg0g1) (newer_than_lits_le_newer Hdjlr0 Hg0g1) (newer_than_lits_le_newer Hls2 Hg0g1)) =>HEsubcssub.
    rewrite HEsubcssub in Hcssubeq.
    move : (mk_env_udiv_rec_preserve Hmkudiv2) => HEhdEtl2ghd.
    move : (env_preserve_cnf HEhdEtl2ghd Hghdcshd) => HEtl2cshdeq.
    rewrite HEhdcshd in HEtl2cshdeq.
    move : (mk_env_and_newer_res Hmkand (newer_than_lit_le_newer Htt Hg0g1) (newer_than_lits_copy _ Hlrshd) (newer_than_lits_le_newer Hls2 Hg0g1)) => Hgandlrsand.
    move : (mk_env_sub_sat Hmksub2 (newer_than_lit_le_newer Hff (pos_leb_trans Hg0g1 Hg1g2'')) (newer_than_lits_le_newer Hdjlr0 (pos_leb_trans Hg0g1 Hg1g2'')) Hgandlrsand) => HEsub2cssub2.
    
    move :Hres;
      case : (lrs_hd == lit_tt); case :(lrs_hd == lit_ff); move => [] <- _ <- _ _; rewrite !interp_cnf_catrev; try by rewrite HE2E3g Hcssubeq Hcshdeq.
    by rewrite HE2E3'g HEtl2cshdeq.
    rewrite HE2E3'g3''.
    move : (mk_env_udiv_rec_preserve Hmkudiv3)=> HEsub2Etl3.
    move : (mk_env_and_sat Hmkand (newer_than_lit_le_newer Htt Hg0g1) (newer_than_lits_copy _ Hlrshd) (newer_than_lits_le_newer Hls2 Hg0g1)) => HEandcsand.
    move : (mk_env_and_newer_cnf Hmkand (newer_than_lit_le_newer Htt Hg0g1) (newer_than_lits_copy _ Hlrshd) (newer_than_lits_le_newer Hls2 Hg0g1)) => Hgandcsand.
    move : (env_preserve_cnf HEsub2Etl3 (newer_than_cnf_le_newer Hgandcsand Hg2''g3'')) => Hcsandeq.
    move : (env_preserve_cnf HEandEsub2g3 Hgandcsand ) => Hcsandeq2.
    rewrite HEandcsand in Hcsandeq2. rewrite Hcsandeq2 in Hcsandeq.
    rewrite Hcsandeq.
    move : (mk_env_sub_newer_cnf Hmksub2 (newer_than_lit_le_newer Hff (pos_leb_trans Hg0g1 Hg1g2'') ) (newer_than_lits_le_newer Hdjlr0 (pos_leb_trans Hg0g1 Hg1g2'')) Hgandlrsand) => Hgsub2cssub2.
    move : (env_preserve_cnf HEsub2Etl3 Hgsub2cssub2) => Hcssub2eq.
    rewrite HEsub2cssub2 in Hcssub2eq. rewrite Hcssub2eq.
    move : (env_preserve_trans HEhdEandg1 (env_preserve_le HEandEsub2g3 Hg1g2'')) => HEhdEsub2.
    move : (env_preserve_trans HEhdEsub2 (env_preserve_le HEsub2Etl3 Hg1g3'')) => HEhdEtl3.
    by rewrite (env_preserve_cnf HEhdEtl3 Hghdcshd) HEhdcshd. 
Qed.


Lemma mk_env_udiv_sat :
  forall E g ls1 ls2 E' g' cs lqs lrs,
    mk_env_udiv E g ls1 ls2 = (E', g', cs, lqs, lrs) ->
    size ls1 = size ls2 -> 
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move => E g ls1 ls2 E' g' cs lqs lrs.
  rewrite /mk_env_udiv.
  dcase (mk_env_eq E g ls2 (copy (size ls2) lit_ff)) => [[[[E_eq] g_eq] cs_eq] lrs_eq] Hmkeq.
  dcase (mk_env_udiv_rec E_eq g_eq (rev ls1) ls2 (copy (size (rev ls1)) lit_ff) (copy (size (rev ls1)) lit_ff)) => [[[[[E_udivr] g_udivr] cs_udivr] lqs_udivr] lrs_udivr] Hmkudivr.
  dcase (mk_env_and E_udivr g_udivr (copy (size lqs_udivr) (neg_lit lrs_eq)) lqs_udivr)=> [[[[E_and] g_and] cs_and] lrs_and] Hmkand.
  dcase (mk_env_ite E_and g_and lrs_eq (rev lrs_udivr) lrs_udivr) =>[[[[E_ite] g_ite] cs_ite] lrs_ite] Hmkite.
  move : (mk_env_ite_newer_gen Hmkite) => Hnewite. move : (mk_env_and_newer_gen Hmkand) => Hnewand. move: (mk_env_udiv_rec_newer_gen Hmkudivr) => Hnewudivr. move : (mk_env_eq_newer_gen Hmkeq) => Hneweq. 
  case (lrs_eq == lit_tt); case (lrs_eq == lit_ff); case => <- _ <- _ _; move => Hsz Htt Hls1 Hls2.
  - have Hnewcp :newer_than_lits g (copy (size ls2) lit_ff). by rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff Htt.
    exact : (mk_env_eq_sat Hmkeq Htt Hls2 Hnewcp).
  - have Hnewcp :newer_than_lits g (copy (size ls2) lit_ff). by rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff Htt.
    exact : (mk_env_eq_sat Hmkeq Htt Hls2 Hnewcp).
  - rewrite interp_cnf_catrev.
    have Hnewcp :newer_than_lits g (copy (size ls2) lit_ff). by rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff Htt.
    have Hszcp : size (copy (size (rev ls1)) lit_ff) = size ls2 by rewrite size_nseq size_rev Hsz.
    have Hnrev1 : newer_than_lits g_eq (rev ls1) by rewrite newer_than_lits_rev; last rewrite (newer_than_lits_le_newer Hls1 Hneweq).
    have Hncprev1: newer_than_lits g_eq (copy (size (rev ls1)) lit_ff) by rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff (newer_than_lit_le_newer Htt Hneweq).
    move : (mk_env_udiv_rec_sat Hmkudivr Hszcp Hszcp (newer_than_lit_le_newer Htt Hneweq) Hncprev1 Hncprev1 Hnrev1 (newer_than_lits_le_newer Hls2 Hneweq)) => HEucsu.
    rewrite HEucsu.
    move: (mk_env_eq_sat Hmkeq Htt Hls2 Hnewcp) => Hcnfeq.
    move : (mk_env_udiv_rec_preserve Hmkudivr) => HEeqEugeq.
    move : (mk_env_eq_newer_cnf Hmkeq Htt Hls2 Hnewcp) => Hncnfeq.
    by rewrite  (env_preserve_cnf HEeqEugeq Hncnfeq) Hcnfeq.
  - rewrite 3!interp_cnf_catrev.
    have Hnewcp :newer_than_lits g (copy (size ls2) lit_ff). by rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff Htt.
    have Hszcp : size (copy (size (rev ls1)) lit_ff) = size ls2 by rewrite size_nseq size_rev Hsz.
    have Hnrev1 : newer_than_lits g_eq (rev ls1) by rewrite newer_than_lits_rev; last rewrite (newer_than_lits_le_newer Hls1 Hneweq).
    have Hncprev1: newer_than_lits g_eq (copy (size (rev ls1)) lit_ff) by rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff (newer_than_lit_le_newer Htt Hneweq).
    move : (mk_env_udiv_rec_sat Hmkudivr Hszcp Hszcp (newer_than_lit_le_newer Htt Hneweq) Hncprev1 Hncprev1 Hnrev1 (newer_than_lits_le_newer Hls2 Hneweq)) => HEucsu.
    move : (mk_env_ite_preserve Hmkite) => HEandEitegand.
    move : (mk_env_and_preserve Hmkand) => HEuEandgu.
    move: (mk_env_eq_sat Hmkeq Htt Hls2 Hnewcp) => Hcnfeq.
    move : (mk_env_udiv_rec_preserve Hmkudivr) => HEeqEugeq.
    move : (mk_env_eq_newer_cnf Hmkeq Htt Hls2 Hnewcp) => Hncnfeq.
    move : (env_preserve_trans HEeqEugeq (env_preserve_le HEuEandgu Hnewudivr)) => HEeqEandgeq.
    move : ( env_preserve_trans HEeqEandgeq (env_preserve_le HEandEitegand (pos_leb_trans Hnewudivr Hnewand))) => HEeqEitegeq.
    rewrite (env_preserve_cnf HEeqEitegeq Hncnfeq) Hcnfeq.
    move : (env_preserve_trans HEuEandgu (env_preserve_le HEandEitegand Hnewand)) => HEuEitegu.
    have Hrev1 : (newer_than_lits g (rev ls1)) by rewrite (newer_than_lits_rev Hls1).
    have Hcp2: (newer_than_lits g (copy (size (rev ls1)) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    move: (mk_env_udiv_rec_newer_cnf Hmkudivr (newer_than_lit_le_newer Htt Hneweq) (newer_than_lits_le_newer Hrev1 Hneweq) (newer_than_lits_le_newer Hls2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) Hszcp Hszcp) => Hncsu.
    rewrite (env_preserve_cnf HEuEitegu Hncsu) HEucsu.
    move : (pos_leb_trans Hneweq Hnewudivr) => Hggu.
    have Hnewcpneg : (newer_than_lits g_udivr (copy (size lqs_udivr) (neg_lit lrs_eq))) by rewrite newer_than_lits_copy; last by rewrite newer_than_lit_neg (newer_than_lit_le_newer (mk_env_eq_newer_res Hmkeq) Hnewudivr).
    move/andP : (mk_env_udiv_rec_newer_res Hmkudivr (newer_than_lit_le_newer Htt Hneweq) (newer_than_lits_le_newer Hrev1 Hneweq) (newer_than_lits_le_newer Hls2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq)) => [Hnewq Hnewr].
    move : (mk_env_and_sat Hmkand (newer_than_lit_le_newer Htt Hggu) Hnewcpneg Hnewr) => HEandcsand.
    move : (mk_env_and_newer_cnf Hmkand (newer_than_lit_le_newer Htt Hggu) Hnewcpneg Hnewr) => Hncnfand.
    rewrite (env_preserve_cnf HEandEitegand Hncnfand) HEandcsand .
    move : (pos_leb_trans (pos_leb_trans Hneweq Hnewudivr) Hnewand) => Hggand.
    move : (mk_env_eq_newer_res Hmkeq) => Hgeqlrseq.
    have Hnewerv : newer_than_lits g_and (rev lrs_udivr) by rewrite newer_than_lits_rev; last rewrite (newer_than_lits_le_newer Hnewq Hnewand).
    by rewrite (mk_env_ite_sat Hmkite (newer_than_lit_le_newer Htt Hggand) (newer_than_lit_le_newer Hgeqlrseq (pos_leb_trans Hnewudivr Hnewand)) Hnewerv (newer_than_lits_le_newer Hnewq Hnewand)).
Qed.
