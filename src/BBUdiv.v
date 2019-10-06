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

Lemma udivB_to_nat : forall p q, size p = size q -> (udivB p q).1 = from_nat (size p) (div.divn (to_nat p) (to_nat q)).
Proof.
  elim =>[|phd ptl IH] q /= Hsz.
  symmetry in Hsz; by rewrite  (size0nil Hsz)/=.
  rewrite /udivB/=.
  case Hq0: (q == zeros (size q)).
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

