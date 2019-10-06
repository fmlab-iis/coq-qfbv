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
  
Definition udivB (n m : bits) := udivB_rec n m (act_size n - (act_size m) + 1).

Eval compute in (to_nat (udivB (from_nat 8 185) (from_nat 4 13)).1).
Eval compute in (to_nat (udivB (from_nat 8 185) (from_nat 4 13)).2).

Eval compute in (to_nat (udivB (from_nat 15 15) (from_nat 3 2)).1).
Eval compute in (to_nat (udivB (from_nat 15 15) (from_nat 3 2)).2).



Fixpoint bit_blast_udiv_rec g ls1 ls2 i : generator * cnf * word * word :=
  match i with
  | 0 => let '(g_shr, cs_shr, lrs_shr) := bit_blast_ashr_int g ls1 (act_sizel ls1 - act_sizel ls2 +1) in (g_shr, cs_shr, (copy (size ls1) lit_ff), lrs_shr)
  | S i' =>
    let ai := nth lit_ff ls1 (act_sizel ls1 - act_sizel ls2 +1 ) in
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

