From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBConst BBAnd BBAdd BBShl BBSub BBMul BBAshr BBUge.
From ssrlib Require Import Var ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ===== bit_blast_udiv ===== *)

Fixpoint act_size' (b : bits) : nat :=
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

Fixpoint udivB_rec (n m : bits) i : bits * bits :=
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
  else  udivB_rec n m (act_size n - (act_size m) + 1).

(*Eval compute in (to_nat (udivB (from_nat 8 185) (from_nat 4 13)).1).
Eval compute in (to_nat (udivB (from_nat 8 185) (from_nat 4 13)).2).
Eval compute in (to_nat (udivB (from_nat 15 15) (from_nat 3 2)).1).
Eval compute in (to_nat (udivB (from_nat 15 15) (from_nat 3 2)).2).
 *)

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
       
Lemma size_udivB1 n m : size (udivB n m).1 = size n.
Proof.
  rewrite/udivB.
  case Hm0: (m == zeros (size m)); first by rewrite size_zeros.
  elim ((act_size n - act_size m + 1)) =>[|sz IH]; first by rewrite/=size_zeros.
  by rewrite/=size_dropmsb size_joinlsb IH addnK.
Qed.

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

Lemma to_nat_full_mul p1 p2 : to_nat (full_mul p1 p2) = (to_nat p1 * to_nat p2).
Proof.
  move : p2. elim p1 => [|phd1 ptl1 IH] p2 /=. by rewrite from_natn0 to_nat_zeros mul0n.
  case phd1. 
Admitted.  
  
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

Lemma udivB0 : forall m n, (udivB m (zeros n)) = (zeros (size m), zeros (size m)).
Proof.
  elim => [|mhd mtl IH]n /=. by rewrite/udivB size_zeros eq_refl/=.
  by rewrite/udivB size_zeros eq_refl/=.
Qed.

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

Lemma act_size'0: forall m , act_size' (zeros m) = 0.
Proof. elim . done. intros. by rewrite-zeros_cons/=. 
Qed.

Lemma rev0 : forall m, rev (zeros m) = zeros m.
Proof. elim. done. intros. by rewrite-zeros_cons rev_cons H zeros_rcons zeros_cons.
Qed.

Lemma act_size0: forall m , act_size (zeros m) = 0.
Proof.
  elim. done. intros. by rewrite/act_size rev0 act_size'0. Qed.

Lemma act_size_nil : act_size nil = 0.
Proof. done. Qed.

Lemma size_udivB2 : forall n m , size (udivB n m).2 = size n.
Proof.
  rewrite/udivB. intros.
  case Hm0: (m == zeros (size m)); first by rewrite size_zeros.
  elim ((act_size n - act_size m + 1)) =>[|sz IH]; first by rewrite size_shrB.
  rewrite/=. case Hhd : (to_nat
         (dropmsb
            (joinlsb (nth false n (act_size n - sz - act_size m)) (udivB_rec n m sz).2)) <
       to_nat m).
  by rewrite/= size_dropmsb size_joinlsb IH addnK.
  rewrite /=size_subB size_zext !size_dropmsb !size_joinlsb !IH !addnK minnE. 
  by rewrite subnDA subnn subn0.
Qed.


Lemma mulB0' : forall m n, mulB m (zeros n) = zeros (size m).
Proof.
  intros. rewrite/mulB full_muln0/low -zeros_cats take_cat size_zeros/=.
  case H : (size m < size m). move : (Nat.lt_irrefl (size m))=>Heq.
  exfalso; apply Heq; apply Nats.ltn_lt; rewrite H; done.
  by rewrite size_cat size_zeros subnDA subnn take0 sub0n !cats0.
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

Lemma dropmsb_zeros : forall n, dropmsb (zeros n) = zeros n.-1.
Proof.
  move => n. case n. done.
  move => n0. have->:(zeros n0.+1.-1=zeros n0) by rewrite-addn1-subn1 addnK.
  by rewrite-zeros_rcons/dropmsb/=belastd_rcons. 
Qed.

Lemma udivB_rec0 : forall n m, udivB (zeros n) m = (zeros n, zeros n).
Proof.
  intros. rewrite/udivB act_size0 sub0n add0n. case Hm : (m == zeros (size m)).
  by rewrite size_zeros.
  elim n. rewrite /=. apply negbT in Hm; rewrite -ltB0n ltB_to_nat/= in Hm. by rewrite/= Hm/= /shrB1/=/droplsb/=/joinlsb/dropmsb.
  intros. rewrite/= zeros_cons act_size0 subnn sub0n add0n nth0/=.
  rewrite/ shrB1/=. have-> : (to_nat (dropmsb (joinlsb b0 (droplsb (b0 :: joinmsb (zeros n0) b0)))) = 0). by rewrite to_nat_dropmsb to_nat_joinlsb to_nat_droplsb/= to_nat_joinmsb mul0n to_nat_zeros size_droplsb/=size_joinmsb size_zeros div.mod0n. 
  apply negbT in Hm; rewrite -ltB0n ltB_to_nat/= in Hm. rewrite Hm/=.
  rewrite size_zeros droplsb_joinlsb/=/joinmsb zeros_rcons joinlsb_false_zeros.
  rewrite dropmsb_zeros-2!addn1-subn1-addnBA; last done. by rewrite subnn addn0 zeros_cons addn1.
Qed.

Lemma udivB_mulAC : forall d m n, (udivB d m).2 = zeros (size d) -> udivB m (mulB d n) = udivB (mulB m n) d.
Proof.
  elim =>[|dhd dtl IH] m n H; rewrite/udivB/=.
  - by rewrite !size_mulB/mulB/=/low !take0 add0n sub0n zeros0 cats0/=.
  - case Hz : (dhd :: dtl == b0 :: zeros (size dtl)).
    + rewrite (eqP Hz)zeros_cons size_mulB size_zeros !mul0B/=.
      case Hzeros: (b0 :: zeros (size dtl) == b0 :: zeros (size dtl)); rewrite !size_mulB; first done.
      rewrite zeros_cons in Hzeros. move : (eq_refl (zeros (size dtl).+1)) => Hzeros'; rewrite Hzeros' in Hzeros; discriminate.
    + case Hmul0 : (((dhd :: dtl) *# n)%bits == zeros (size ((dhd :: dtl) *# n)%bits)).
      *  rewrite size_mulB mulnB_eq0 in Hmul0. move : (orP Hmul0)=>[Hl| Hr].
         rewrite/= in Hl. rewrite Hl in Hz; discriminate.
         rewrite (eqP Hr) mulB0' act_size0 sub0n add0n. rewrite/=subn0 !act_size0 !sub0n add0n size_zeros nth0. have ->: (head false (zeros (size m))=false) by (case m=>[|mhd mtl]; by rewrite/=). rewrite/joinlsb/=/shrB1/= to_nat_dropmsb/=to_nat_droplsb/= to_nat_joinmsb mul0n to_nat_zeros addn0 div.mod0n.
Admitted.
  
Lemma udivB_to_nat : forall p q, (*size p = size q ->*) (udivB p q).1 = from_nat (size p) (div.divn (to_nat p) (to_nat q)).
Proof.
  elim =>[|phd ptl IH] q /=; rewrite/udivB/=. case H0: (q == zeros (size q)); first done.
  apply negbT in H0; rewrite-ltB0n ltB_to_nat/= in H0; by rewrite H0/=/joinlsb/dropmsb. 
  case H0: (q == zeros (size q)).
  by rewrite/=(eqP H0)to_nat_zeros div.divn0/=from_natn0/joinlsb.
  rewrite-div.divn2-div.divnMA.
  case phd.

Admitted.  
  
  
Fixpoint bit_blast_udiv_rec g ls1 ls2 i : generator * cnf * word * word :=
  match i with
  | 0 => let '(g_shr, cs_shr, lrs_shr) := bit_blast_ashr_int g ls1 (act_sizel ls1 - act_sizel ls2 +1) in (g_shr, cs_shr, (copy (size ls1) lit_ff), lrs_shr)
  | S i' =>
    let ai := nth lit_ff ls1 (act_sizel ls1 - i' - act_sizel ls2 +1 ) in
    let '(g_udiv, cs_udiv, q_udiv, r_udiv) := bit_blast_udiv_rec g ls1 ls2 i' in
    let di := dropmsl (joinlsl ai r_udiv) in
    let '(g_ge, cs_ge, lrs_ge) := bit_blast_uge g_udiv di ls2 in
    let qi := dropmsl (joinlsl lrs_ge q_udiv) in
    if (lrs_ge==lit_tt) then
      let '(g_sub, cs_sub, lrs_sub) := bit_blast_sub g_ge di ls2 in
      (g_sub, catrev (catrev cs_udiv cs_ge) cs_sub, qi, lrs_sub)
    else (g_ge, catrev cs_udiv cs_ge, qi, di)
  end.

Definition bit_blast_udiv g ls1 ls2 := bit_blast_udiv_rec g ls1 ls2 (act_sizel ls1 -act_sizel ls2 +1).

Fixpoint mk_env_udiv_rec E g ls1 ls2 i : env * generator * cnf * word * word :=
  match i with
  | 0 => let '(E_shr, g_shr, cs_shr, lrs_shr) := mk_env_ashr_int E g ls1 (act_sizel ls1 - act_sizel ls2 +1) in (E_shr, g_shr, cs_shr, (copy (size ls1) lit_ff), lrs_shr)
  | S i' =>
    let ai := nth lit_ff ls1 (act_sizel ls1 - i' - act_sizel ls2 +1 ) in
    let '(E_udiv, g_udiv, cs_udiv, q_udiv, r_udiv) := mk_env_udiv_rec E g ls1 ls2 i' in
    let di := dropmsl (joinlsl ai r_udiv) in
    let '(E_ge, g_ge, cs_ge, lrs_ge) := mk_env_uge E g_udiv di ls2 in
    let qi := dropmsl (joinlsl lrs_ge q_udiv) in
    if (lrs_ge==lit_tt) then
      let '(E_sub, g_sub, cs_sub, lrs_sub) := mk_env_sub E g_ge di ls2 in
      (E_sub, g_sub, catrev (catrev cs_udiv cs_ge) cs_sub, qi, lrs_sub)
    else (E_ge, g_ge, catrev cs_udiv cs_ge, qi, di)
  end.

Definition mk_env_udiv E g ls1 ls2 := mk_env_udiv_rec E g ls1 ls2 (act_sizel ls1 -act_sizel ls2 +1).

Lemma bit_blast_udiv_rec_correct g ls1 ls2 i g' cs qlrs rlrs E bs1 bs2 :
  bit_blast_udiv_rec g ls1 ls2 i = (g', cs, qlrs, rlrs) ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E qlrs (udivB_rec bs1 bs2 i).1 ->
  enc_bits E rlrs (udivB_rec bs1 bs2 i).2.
Proof.
Admitted.


Lemma bit_blast_udiv_correct g ls1 ls2 g' cs qlrs rlrs E bs1 bs2 :
  bit_blast_udiv g ls1 ls2 = (g', cs, qlrs, rlrs) ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E qlrs (udivB bs1 bs2).1 ->
  enc_bits E rlrs (udivB bs1 bs2).2.
Proof.
Admitted.


Lemma mk_env_udiv_rec_is_bit_blast_udiv_rec E g ls1 ls2 i g' cs qlrs rlrs E' :
  mk_env_udiv_rec E g ls1 ls2 i = (E', g', cs, qlrs, rlrs) ->
  bit_blast_udiv_rec g ls1 ls2 i = (g', cs, qlrs, rlrs).
Proof.
Admitted.

