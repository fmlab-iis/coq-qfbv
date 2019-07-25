
(*
 * Require the following libraries:
 * - coq-bit from https://github.com/mht208/coq-bits
 * - ssrlib from https://github.com/mht208/coq-ssrlib.git
 *)

From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice div.
From BitBlasting Require Import QFBVSimple CNF BBExport.
From ssrlib Require Import Bools Var Store SsrOrdered ZAriths Tuples Tactics.
From Bits Require Export bits.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_udiv ===== *)

Lemma toNat_shrBn :
  forall w n d,
    toNat (shrBn n d) = (@toNat w n)/(2^d).
Proof.
  elim.
  - move => n d.
    rewrite !toNatNil. rewrite -Nats.divn_div div0n; reflexivity.
  - move => n IHn.
    case/tupleP => [n_hd n_tl] d.
    rewrite toNatCons.
    destruct d.
    + rewrite expn0 Nat.div_1_r/=. apply toNatCons.
      rewrite  (shrBn_Sn) -Nats.divn_div expnS divnMA.
      rewrite -muln2 addnC divnMDl; [|replace 2 with (2^1) by apply expn1; apply Nats.expn2_gt0].
      case Hn_hd : n_hd.
      * rewrite/=.
        assert (1<2*2) as Hlt12 by (rewrite mulnn; apply Nats.ltn_1_2expnS; rewrite muln2 in Hlt12).
        rewrite muln2 in Hlt12. move : (Nats.divn01 Hlt12) => Hdiv01.
        destruct Hdiv01 as [Hdiv0|Hdiv1]; try discriminate.
        rewrite Hdiv0 addn0 Nats.divn_div -(IHn n_tl d) shrBn_joinmsb0 toNat_joinmsb0.
        reflexivity.
      * rewrite/= div0n addn0 Nats.divn_div -(IHn n_tl d) shrBn_joinmsb0 toNat_joinmsb0.
        reflexivity.
Qed.

Fixpoint setLitAux {A: Type} {n} i b : n.-tuple A -> n.-tuple A :=
  if n is _.+1
  then fun p => let (p,oldb) := splitlsb p in
                if i is i'.+1 then joinlsb (setLitAux i' b p, oldb) else joinlsb (p,b)
  else fun p => nilB.

Definition setLit {A: Type} {n} (p: n.-tuple A) i b := setLitAux i b p.

Fixpoint bit_blast_udiv_rec w wn (g:generator) :
  w.-tuple literal -> wn.-tuple literal -> wn.-tuple literal -> wn.-tuple literal -> nat->
  generator * cnf * wn.-tuple literal * wn.-tuple literal :=
  if w is n.+1 then
  fun lsn lsd lr lq i =>
    let (lsn_tl, lsn_hd) := eta_expand (splitlsb lsn) in
    (*let '(g_shl, cs_shl, lr_shl) := bit_blast_shl_int g lsn_tl i in*)
    let lr_new := dropmsb (joinlsb (lr, lsn_hd)) in
    let '(g_div, cs_div, lrs_div, lq') := bit_blast_udiv_rec g lsn_tl lsd lr_new lq (i+1) in
    let '(g_uge, cs_uge, lrs_uge) := bit_blast_uge g_div lrs_div lsd in
    if (lrs_uge == lit_tt ) then
      let '(g_sub, cs_sub, lrs_sub) := bit_blast_sub g_uge lrs_div lsd in
      let lq_new := setLit lq i lit_tt in
      (g_sub, cs_div(*++cs_shl*)++cs_uge++cs_sub, lrs_sub, lq_new)
    else if (lrs_uge == lit_ff ) then
           (g_div, cs_div, lrs_div, lq)
         else
           let '(g_and, cs_and, lrs_and) := bit_blast_and g_uge lsd (copy wn lrs_uge) in
           let '(g_sub2, cs_sub2, lrs_sub2) := bit_blast_sub g_and lrs_div lrs_and in
           let lq_new := setLit lq i lit_tt in
           (g_sub2, cs_div++cs_uge++cs_and++cs_sub2, lrs_sub2, lq_new)
  else
    fun _ _ _ _ _=>
      (*(g, [], copy wn lit_ff, copy wn lit_ff).*)
      (bit_blast_const g (@fromNat wn 0), copy wn lit_ff).

Definition bit_blast_udiv w (g: generator) (ls1 ls2:  w.-tuple literal) :generator * cnf * w.-tuple literal * w.-tuple literal:=
  bit_blast_udiv_rec g ls1 ls2 (copy w lit_ff) (copy w lit_ff) 0 .

(*
Lemma  bit_blast_udiv_rec_correct :
  forall w wn g (bs1 : BITS w) (bs2 : BITS wn) br bq i E (ls1:w.-tuple literal) (ls2 : wn.-tuple literal) lr lq g' cs lrs lrq,
    bit_blast_udiv_rec g ls1 ls2 lr lq i = (g', cs, lrs, lrq) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    enc_bits E lr br ->
    enc_bits E lq bq ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (# ((toNat bs1)-((toNat bs2) * (toNat br)))).
Proof.
  elim.
  - move => wn ig ibs1 ibs2 br bq i E ils1 ils2 lr_new lq og cs olrs olrq.
    case=> _ <- <- _ Henc1 Henc2 Henclr Henclq Hcnf.
    apply: (bit_blast_const_correct (g:=ig) _ Hcnf).
    apply: injective_projections => /=; first by reflexivity.
    rewrite toNatNil -Nats.divn_div div0n. reflexivity.
  - move => wn IH w ig.
    case/tupleP => [ibs1_hd ibs1_tl] ibs2 br bq i E.
    case/tupleP => [ils1_hd ils1_tl] ils2 lr lq og cs olrs olrq.
    rewrite /bit_blast_udiv_rec -/bit_blast_udiv_rec
            (lock interp_cnf) (lock bit_blast_uge) (lock bit_blast_sub) (lock bit_blast_and) (lock enc_bits) /= !theadE !beheadCons -!lock.
    (*set lr_new := (dropmsb (joinlsb (copy w lit_ff, ils1_hd))).*)
    set lr_new := (dropmsb (joinlsb (lr, ils1_hd))).
    case Htl: (bit_blast_udiv_rec ig ils1_tl ils2 lr_new lq (i+1)) => [[[g_div cs_div] ls_div] lq_div].
    case Huge : (bit_blast_uge g_div ls_div ils2)=> [[g_uge cs_uge] ls_uge].
    case Hsub1: (bit_blast_sub g_uge ls_div ils2) => [[g_sub1 cs_sub1] lrs_sub1].
    case Hand: (bit_blast_and g_uge ils2 (copy w ls_uge))=> [[g_and cs_and] lrs_and].
    case Hsub2: (bit_blast_sub g_and ls_div lrs_and) => [[g_sub2 cs_sub2] lrs_sub2].
    case Htt: (ls_uge == lit_tt); last case Hff: (ls_uge == lit_ff).
    + (*rewrite (eqP Htt) => {Hsub2 lrs_sub2 cs_sub2 g_sub2 Hand lrs_and cs_and g_and}.*)
      case=> Hog Hcs Holrs Horlq Henc1 Henc2 Henclr Henclq Hcnf. rewrite -Holrs => {Holrs olrs Hog og}.
      move: (enc_bits_thead Henc1) (enc_bits_behead Henc1) => {Henc1}.
      rewrite !theadE !beheadCons => Henc1_hd Henc1_tl.
      rewrite -Hcs 2!add_prelude_append in Hcnf.
      move/andP: Hcnf => [Hcnf_div /andP [Hcnf_uge Hcnf_sub1]].
      (*rewrite (add_prelude_enc_bit_true _ Hcnf_div) in Henc1_hd. rewrite Henc2_hd.*)
      rewrite toNatCons -muln2 /=.
      (*have ->: ((1+toNat ibs1_tl*2) * 2^i) = ((2^i) + (toNat ibs1_tl) * (2^(i+1))).
      {
        rewrite mulnDl mul1n -mulnA -expnS addn1. reflexivity.
      }*)
      assert (enc_bits E lr_new (dropmsb (joinlsb (br, ibs1_hd)))) as Henclrnew by (apply enc_bits_dropmsb; rewrite enc_bits_joinlsb Henc1_hd Henclr; done).
      (*
      move: (IH _ _ _ _ _ _ (i+1) _ _ _ _ _ _ _ _ _ Htl Henc1_tl Henc2 Henclrnew Hcnf_div) => Henc_div.

      move : (bit_blast_sub_correct Hsub1 Henclrnew Henc2 Hcnf_sub1)=> Hlrs_sub.
      assert ((subB (dropmsb (joinlsb (br, ibs1_hd))) ibs2) = # ((ibs1_hd + toNat ibs1_tl * 2) / toNat ibs2)).
      apply toNat_inj. rewrite toNat_subB.
      rewrite toNat_dropmsb toNat_joinlsb -muln2.*)
Admitted.
*)

(* ===== bit_blast_sdiv ===== *)
(*
Definition bb_abs (w:nat) (g: generator) cs :
  w.+1.-tuple literal-> generator * cnf * w.+1.-tuple literal :=
    fun ls1  =>
      let (sign1, uls1) := eta_expand (splitmsb ls1) in
      if sign1 == lit_tt then
        let '(g_neg, cs_neg, lrs_neg):= bit_blast_neg g ls1 in
        (g_neg, cs++cs_neg, lrs_neg)
      else (g, cs, ls1).

Definition bit_blast_sdiv w (g: generator): w.+1.-tuple literal -> w.+1.-tuple literal-> generator * cnf * w.+1.-tuple literal :=
  fun ls1 ls2 =>
    let (sign1, uls1) := eta_expand (splitmsb ls1) in
    let (sign2, uls2) := eta_expand (splitmsb ls2) in
    let '(g_abs1, cs_abs1, lrs_abs1) := bb_abs g [] ls1 in
    let '(g_abs2, cs_abs2, lrs_abs2) := bb_abs g_abs1 [] ls2 in
    if (sign1 == sign2) then
      let '(g_udiv1, cs_udiv1, lr_udiv1, lq_udiv1) := bit_blast_udiv g lrs_abs1 lrs_abs2 in
      (g_udiv1, cs_udiv1, lq_udiv1)
    else if (sign1 != sign2) then
           let '(g_udiv2, cs_udiv2, lr_udiv2, lq_udiv2) := bit_blast_udiv g lrs_abs1 lrs_abs2 in
           let '(g_neg1, cs_neg1, lrs_neg1) := bit_blast_neg g_abs1 lq_udiv2 in
           (g_neg1, cs_neg1, lrs_neg1)
         else let '(g_or, cs_or, lrs_or) := bit_blast_or g_abs1 (copy w.+1 sign1) (copy w.+1 sign2) in
        let '(g_udiv3, cs_udiv3, lr_udiv3, lq_udiv3) := bit_blast_udiv g_or lrs_abs1 lrs_abs2 in
        let '(g_xor, cs_xor, lrs_xor) := bit_blast_xor g_udiv3 lq_udiv3 lrs_or in
        (g_xor, cs_xor, lrs_xor).

Definition bit_blast_srem  w (g: generator): w.+1.-tuple literal -> w.+1.-tuple literal-> generator * cnf * w.+1.-tuple literal :=
  fun ls1 ls2 =>
    let (sign1, uls1) := eta_expand (splitmsb ls1) in
    let '(g_abs1, cs_abs1, lrs_abs1) := bb_abs g [] ls1 in
    let '(g_abs2, cs_abs2, lrs_abs2) := bb_abs g_abs1 [] ls2 in
    let '(g_udiv1, cs_udiv1, lr_udiv1, lq_udiv1) := bit_blast_udiv g lrs_abs1 lrs_abs2 in
    if (sign1 == lit_tt) then
      let '(g_neg1, cs_neg1, lrs_neg1) := bit_blast_neg g_udiv1 lr_udiv1 in
      (g_neg1, cs_neg1, lrs_neg1)
    else if (sign1 == lit_ff) then
           (g_udiv1, cs_udiv1, lr_udiv1)
         else let '(g_xor, cs_xor, lrs_xor) := bit_blast_xor g_udiv1 lr_udiv1 (copy w.+1 sign1) in
              (g_xor, cs_xor, lrs_xor).

Definition bit_blast_smod w (g: generator): w.+1.-tuple literal -> w.+1.-tuple literal-> generator * cnf * w.+1.-tuple literal :=
  fun ls1 ls2 =>
    let (sign1, uls1) := eta_expand (splitmsb ls1) in
    let (sign2, uls2) := eta_expand (splitmsb ls2) in
    let '(g_srem, cs_srem, lrs_srem) := bit_blast_srem g ls1 ls2 in
    let '(g_eq, cs_eq, lrs_eq) := bit_blast_eq g_srem lrs_srem (copy w.+1 lit_ff) in
    if (lrs_eq == lit_tt) || (sign1 == sign2) then
      (g_srem, cs_srem, lrs_srem)
    else let '(g_add, cs_add, lrs_add) := bit_blast_add g_srem lrs_srem ls2 in
         (g_add, cs_add, lrs_add).
 *)



(* ===== bit_blast_exp and bit_blast_bexp ===== *)

Fixpoint bit_blast_exp w (m : vm) (g : generator) (e : QFBV64.exp w) : vm * generator * cnf * w.-tuple literal :=
  match e with
  | QFBV64.bvVar v =>
    match VM.find v m with
    | None => let '(g', cs, rs) := bit_blast_var g v in
              (VM.add v rs m, g', cs, rs)
    | Some rs => (m, g, [], rs)
    end
  | QFBV64.bvConst w n => let '(g', cs, rs) := bit_blast_const g n in
                          (m, g', cs, rs)
  | QFBV64.bvNot w e1 =>
    let '(m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let '(gr, csr, lsr) := bit_blast_not g1 ls1 in
    (m1, gr, cs1++csr, lsr)
  | QFBV64.bvAnd w e1 e2 =>
    let '(m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let '(gr, csr, lsr) := bit_blast_and g2 ls1 ls2 in
    (m2, gr, cs1++cs2++csr, lsr)
  | QFBV64.bvOr w e1 e2 => let '(m1, g1, cs1, rs1) := bit_blast_exp  m  g e1 in
                           let '(m2, g2, cs2, rs2) := bit_blast_exp m1 g1 e2 in
                           let '(g', cs, rs) := bit_blast_or g2 rs1 rs2 in
                           (m2, g', cs1 ++ cs2 ++ cs, rs)
  | QFBV64.bvXor w e1 e2 =>
    let '(m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let '(gr, csr, lsr) := bit_blast_xor g2 ls1 ls2 in
    (m2, gr, cs1++cs2++csr, lsr)
  | QFBV64.bvNeg w e =>
    let '(m1, g1, cs1, ls1) := bit_blast_exp m g e in
    let '(gr, csr, lsr) := bit_blast_neg g1 ls1 in
    (m1, gr, cs1++csr, lsr)
  | QFBV64.bvAdd w e1 e2 =>
    let '(m1, g1, cs1, rs1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, rs2) := bit_blast_exp m1 g1 e2 in
    let '(g', cs, rs) := bit_blast_add g2 rs1 rs2 in
    (m2, g', cs1 ++ cs2 ++ cs, rs)
  | QFBV64.bvSub w e1 e2 =>
    let '(m1, g1, cs1, rs1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, rs2) := bit_blast_exp m1 g1 e2 in
    let '(g', cs, rs) := bit_blast_sub g2 rs1 rs2 in
    (m2, g', cs1 ++ cs2 ++ cs, rs)
  | QFBV64.bvMul w e1 e2 =>
    let '(m1, g1, cs1, rs1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, rs2) := bit_blast_exp m1 g1 e2 in
    let '(g', cs, rs) := bit_blast_mul g2 rs1 rs2 in
    (m2, g', cs1 ++ cs2 ++ cs, rs)
  | QFBV64.bvMod w e1 e2 => (m, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvSrem w e1 e2 => (m, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvSmod w e1 e2 => (m, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvShl w e1 e2 =>
    let: (m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let: (m', g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let: (g', cs, ls) := bit_blast_shl g2 ls1 ls2 in
    (m', g', cs1 ++ cs2 ++ cs, ls)
  | QFBV64.bvLshr w e1 e2 =>
    let: (m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let: (m', g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let: (g', cs, ls) := bit_blast_lshr g2 ls1 ls2 in
    (m', g', cs1 ++ cs2 ++ cs, ls)
  | QFBV64.bvAshr w e1 e2 =>
    let: (m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let: (m', g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let: (g', cs, ls) := bit_blast_ashr g2 ls1 ls2 in
    (m', g', cs1 ++ cs2 ++ cs, ls)
  | QFBV64.bvConcat w1 w2 e1 e2 => let '(m1, g1, cs1, rs1) := bit_blast_exp m g e1 in
                                   let '(m', g2, cs2, rs2) := bit_blast_exp m1 g1 e2 in
                                   let '(g', cs, rs) := bit_blast_concat g2 rs1 rs2 in (m', g', cs1 ++ cs2 ++ cs, rs)
  | QFBV64.bvExtract w i j e =>
    let: (m', ge, cse, lse) := bit_blast_exp m g e in
    let: (g', cs, ls') := bit_blast_extract ge lse in
    (m', g', cse ++ cs, ls')
  | QFBV64.bvSlice w1 w2 w3 e =>
    let: (m', ge, cse, lse) := bit_blast_exp m g e in
    let: (g', cs, ls') := bit_blast_slice ge lse in
    (m', g', cse ++ cs, ls')
  | QFBV64.bvHigh wh wl e =>
    let: (m', ge, cse, lse) := bit_blast_exp m g e in
    let: (g', cs, ls') := bit_blast_high ge lse in
    (m', g', cse ++ cs, ls')
  | QFBV64.bvLow wh wl e =>
    let: (m', ge, cse, lse) := bit_blast_exp m g e in
    let: (g', cs, ls') := bit_blast_low ge lse in
    (m', g', cse ++ cs, ls')
  | QFBV64.bvZeroExtend w n e => let '(m', ge, cse, lse) := bit_blast_exp m g e in
                                 let '(g', cs, ls) := bit_blast_zeroextend n ge lse in
                                 (m', g', cse ++ cs, ls)
  | QFBV64.bvSignExtend w n e => let: (m', ge, cse, lse) := bit_blast_exp m g e in
                                 let: (g', cs, ls) := bit_blast_signextend n ge lse in
                                 (m', g', cse ++ cs, ls)
  | QFBV64.bvIte w c e1 e2 =>
    let '(mc, gc, csc, lc) := bit_blast_bexp m g c in
    let '(m1, g1, cs1, ls1) := bit_blast_exp mc gc e1 in
    let '(m2, g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let '(gr, csr, lsr) := bit_blast_ite g2 lc ls1 ls2 in
    (m2, gr, csc++cs1++cs2++csr, lsr)
  end
with
bit_blast_bexp (m : vm) (g : generator) (e : QFBV64.bexp) : vm * generator * cnf * literal :=
  match e with
  | QFBV64.bvFalse => (m, g, [], lit_ff)
  | QFBV64.bvTrue => (m, g, [], lit_tt)
  | QFBV64.bvEq _ e1 e2 =>
    let '(m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let '(g', cs, r) := bit_blast_eq g2 ls1 ls2 in
    (m2, g', cs1++cs2++cs, r)
  | QFBV64.bvUlt w e1 e2 =>
    let '(m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let '(g', cs, r) := bit_blast_ult g2 ls1 ls2 in
    (m2, g', cs1++cs2++cs, r)
  | QFBV64.bvUle w e1 e2 =>
    let '(m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let '(g', cs, r) := bit_blast_ule g2 ls1 ls2 in
    (m2, g', cs1++cs2++cs, r)
  | QFBV64.bvUgt w e1 e2 =>
    let '(m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let '(g', cs, r) := bit_blast_ugt g2 ls1 ls2 in
    (m2, g', cs1++cs2++cs, r)
  | QFBV64.bvUge w e1 e2 =>
    let '(m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let '(g', cs, r) := bit_blast_uge g2 ls1 ls2 in
    (m2, g', cs1++cs2++cs, r)
  | QFBV64.bvSlt w e1 e2 =>
    let '(m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let '(gr, csr, lr) := bit_blast_slt g2 ls1 ls2 in
    (m2, gr, cs1++cs2++csr, lr)
  | QFBV64.bvSle w e1 e2 =>
    let '(m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let '(gr, csr, lr) := bit_blast_sle g2 ls1 ls2 in
    (m2, gr, cs1++cs2++csr, lr)
  | QFBV64.bvSgt w e1 e2 =>
    let '(m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let '(gr, csr, lr) := bit_blast_sgt g2 ls1 ls2 in
    (m2, gr, cs1++cs2++csr, lr)
  | QFBV64.bvSge w e1 e2 =>
    let '(m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let '(gr, csr, lr) := bit_blast_sge g2 ls1 ls2 in
    (m2, gr, cs1++cs2++csr, lr)
  | QFBV64.bvUaddo w e1 e2 =>
    let '(m1, g1, cs1, rs1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, rs2) := bit_blast_exp m1 g1 e2 in
    let '(g', cs, lr) := bit_blast_uaddo g2 rs1 rs2 in
    (m2, g', cs1 ++ cs2 ++ cs, lr)
  | QFBV64.bvUsubo w e1 e2 =>
    let '(m1, g1, cs1, rs1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, rs2) := bit_blast_exp m1 g1 e2 in
    let '(g', cs, lr) := bit_blast_usubo g2 rs1 rs2 in
    (m2, g', cs1 ++ cs2 ++ cs, lr)
  | QFBV64.bvUmulo w e1 e2 =>
    let '(m1, g1, cs1, rs1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, rs2) := bit_blast_exp m1 g1 e2 in
    let '(g', cs, lr) := bit_blast_umulo g2 rs1 rs2 in
    (m2, g', cs1 ++ cs2 ++ cs, lr)
  | QFBV64.bvSaddo w e1 e2 =>
    let '(m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let '(gr, csr, lr) := bit_blast_saddo g2 ls1 ls2 in
    (m2, gr, cs1++cs2++csr, lr)
  | QFBV64.bvSsubo w e1 e2 =>
    let '(m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let '(gr, csr, lr) := bit_blast_ssubo g2 ls1 ls2 in
    (m2, gr, cs1++cs2++csr, lr)
  | QFBV64.bvSmulo w e1 e2 =>
    let '(m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let '(gr, csr, lr) := bit_blast_smulo g2 ls1 ls2 in
    (m2, gr, cs1++cs2++csr, lr)
  | QFBV64.bvLneg e  =>
    let '(m1, g1, cs1, l1) := bit_blast_bexp m g e in
    let '(g', cs, r) := bit_blast_lneg g1 l1 in
    (m1, g', cs1++cs, r)
  | QFBV64.bvConj e1 e2 =>
    let '(m1, g1, cs1, l1) := bit_blast_bexp m g e1 in
    let '(m2, g2, cs2, l2) := bit_blast_bexp m1 g1 e2 in
    let '(g', cs, r) := bit_blast_conj g2 l1 l2 in
    (m2, g', cs1++cs2++cs, r)
  | QFBV64.bvDisj e1 e2 =>
    let '(m1, g1, cs1, l1) := bit_blast_bexp m g e1 in
    let '(m2, g2, cs2, l2) := bit_blast_bexp m1 g1 e2 in
    let '(g', cs, r) := bit_blast_disj g2 l1 l2 in
    (m2, g', cs1++cs2++cs, r)
    (*(m, g, [], lit_ff)*) (* TODO *)
  end.

Fixpoint mk_env_exp w (m : vm) (s : QFBV64.State.t) (E : env) (g : generator) (e : QFBV64.exp w) : vm * env * generator * cnf * w.-tuple literal :=
  match e with
  | QFBV64.bvVar v =>
    match VM.find v m with
    | None => let '(E', g', cs, rs) := mk_env_var E g (QFBV64.State.acc v s) v in
              (VM.add v rs m, E', g', cs, rs)
    | Some rs => (m, E, g, [], rs)
    end
  | QFBV64.bvConst _ n => let '(E', g', cs, rs) := mk_env_const E g n in
                          (m, E', g', cs, rs)
  | QFBV64.bvNot w e1 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(Er, gr, csr, lsr) := mk_env_not E1 g1 ls1 in
    (m1, Er, gr, cs1++csr, lsr)
  | QFBV64.bvAnd w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(Er, gr, csr, lsr) := mk_env_and E2 g2 ls1 ls2 in
    (m2, Er, gr, cs1++cs2++csr, lsr)
  | QFBV64.bvOr w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(E', g', cs, ls) := mk_env_or E2 g2 ls1 ls2 in
    (m2, E', g', cs1 ++ cs2 ++ cs, ls)
  | QFBV64.bvXor w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(Er, gr, csr, lsr) := mk_env_xor E2 g2 ls1 ls2 in
    (m2, Er, gr, cs1++cs2++csr, lsr)
  | QFBV64.bvNeg w e =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e in
    let '(Er, gr, csr, lsr) := mk_env_neg E1 g1 ls1 in
    (m1, Er, gr, cs1++csr, lsr)
  | QFBV64.bvAdd w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(Er, gr, csr, lsr) := mk_env_add E2 g2 ls1 ls2 in
    (m2, Er, gr, cs1++cs2++csr, lsr)
  | QFBV64.bvSub w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(Er, gr, csr, lsr) := mk_env_sub E2 g2 ls1 ls2 in
    (m2, Er, gr, cs1++cs2++csr, lsr)
  | QFBV64.bvMul w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(Er, gr, csr, lsr) := mk_env_mul E2 g2 ls1 ls2 in
    (m2, Er, gr, cs1++cs2++csr, lsr)
  | QFBV64.bvMod w e1 e2 => (m, E, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvSrem w e1 e2 => (m, E, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvSmod w e1 e2 => (m, E, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvShl w e1 e2 =>
    let: (m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let: (m', E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let: (E', g', cs, ls) := mk_env_shl E2 g2 ls1 ls2 in
    (m', E', g', cs1 ++ cs2 ++ cs, ls)
  | QFBV64.bvLshr w e1 e2 =>
    let: (m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let: (m', E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let: (E', g', cs, ls) := mk_env_lshr E2 g2 ls1 ls2 in
    (m', E', g', cs1 ++ cs2 ++ cs, ls)
  | QFBV64.bvAshr w e1 e2 =>
    let: (m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let: (m', E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let: (E', g', cs, ls) := mk_env_ashr E2 g2 ls1 ls2 in
    (m', E', g', cs1 ++ cs2 ++ cs, ls)
  | QFBV64.bvConcat w1 w2 e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m', E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(E', g', cs, ls) := mk_env_concat E2 g2 ls1 ls2 in
    (m', E', g', cs1 ++ cs2 ++ cs, ls)
  | QFBV64.bvExtract w i j e =>
    let: (m', Ee, ge, cse, lse) := mk_env_exp m s E g e in
    let: (E', g', cs, ls') := mk_env_extract Ee ge lse in
    (m', E', g', cse ++ cs, ls')
  | QFBV64.bvSlice w1 w2 w3 e =>
    let: (m', Ee, ge, cse, lse) := mk_env_exp m s E g e in
    let: (E', g', cs, ls') := mk_env_slice Ee ge lse in
    (m', E', g', cse ++ cs, ls')
  | QFBV64.bvHigh wh wl e =>
    let: (m', Ee, ge, cse, lse) := mk_env_exp m s E g e in
    let: (E', g', cs, ls') := mk_env_high Ee ge lse in
    (m', E', g', cse ++ cs, ls')
  | QFBV64.bvLow wh wl e =>
    let: (m', Ee, ge, cse, lse) := mk_env_exp m s E g e in
    let: (E', g', cs, ls') := mk_env_low Ee ge lse in
    (m', E', g', cse ++ cs, ls')
  | QFBV64.bvZeroExtend w n e =>
    let '(m', Ee, ge, cse, lse) := mk_env_exp m s E g e in
    let '(E', g', cs, ls') := mk_env_zeroextend n Ee ge lse in
    (m', E', g', cse ++ cs, ls')
  | QFBV64.bvSignExtend w n e =>
    let: (m', Ee, ge, cse, lse) := mk_env_exp m s E g e in
    let: (E', g', cs, ls') := mk_env_signextend n Ee ge lse in
    (m', E', g', cse ++ cs, ls')
  | QFBV64.bvIte w c e1 e2 =>
    let '(mc, Ec, gc, csc, lc) := mk_env_bexp m s E g c in
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp mc s Ec gc e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(Er, gr, csr, lsr) := mk_env_ite E2 g2 lc ls1 ls2 in
    (m2, Er, gr, csc++cs1++cs2++csr, lsr)
  end
with
mk_env_bexp (m : vm) (s : QFBV64.State.t) (E : env) (g : generator) (e : QFBV64.bexp) : vm * env * generator * cnf * literal :=
  match e with
  | QFBV64.bvFalse => (m, E, g, [], lit_ff)
  | QFBV64.bvTrue => (m, E, g, [], lit_tt)
  | QFBV64.bvEq _ e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(E', g', cs, r) := mk_env_eq E2 g2 ls1 ls2 in
    (m2, E', g', cs1++cs2++cs, r)
  | QFBV64.bvUlt w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(E', g', cs, r) := mk_env_ult E2 g2 ls1 ls2 in
    (m2, E', g', cs1++cs2++cs, r)
  | QFBV64.bvUle w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(E', g', cs, r) := mk_env_ule E2 g2 ls1 ls2 in
    (m2, E', g', cs1++cs2++cs, r)
  | QFBV64.bvUgt w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(E', g', cs, r) := mk_env_ugt E2 g2 ls1 ls2 in
    (m2, E', g', cs1++cs2++cs, r)
  | QFBV64.bvUge w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(E', g', cs, r) := mk_env_uge E2 g2 ls1 ls2 in
    (m2, E', g', cs1++cs2++cs, r)
  | QFBV64.bvSlt w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(Er, gr, csr, lr) := mk_env_slt E2 g2 ls1 ls2 in
    (m2, Er, gr, cs1++cs2++csr, lr)
  | QFBV64.bvSle w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(Er, gr, csr, lr) := mk_env_sle E2 g2 ls1 ls2 in
    (m2, Er, gr, cs1++cs2++csr, lr)
  | QFBV64.bvSgt w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(Er, gr, csr, lr) := mk_env_sgt E2 g2 ls1 ls2 in
    (m2, Er, gr, cs1++cs2++csr, lr)
  | QFBV64.bvSge w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(Er, gr, csr, lr) := mk_env_sge E2 g2 ls1 ls2 in
    (m2, Er, gr, cs1++cs2++csr, lr)
  | QFBV64.bvUaddo w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(Er, gr, csr, lr) := mk_env_uaddo E2 g2 ls1 ls2 in
    (m2, Er, gr, cs1++cs2++csr, lr)
  | QFBV64.bvUsubo w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(Er, gr, csr, lr) := mk_env_usubo E2 g2 ls1 ls2 in
    (m2, Er, gr, cs1++cs2++csr, lr)
  | QFBV64.bvUmulo w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(Er, gr, csr, lr) := mk_env_umulo E2 g2 ls1 ls2 in
    (m2, Er, gr, cs1++cs2++csr, lr)
  | QFBV64.bvSaddo w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(Er, gr, csr, lr) := mk_env_saddo E2 g2 ls1 ls2 in
    (m2, Er, gr, cs1++cs2++csr, lr)
  | QFBV64.bvSsubo w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(Er, gr, csr, lr) := mk_env_ssubo E2 g2 ls1 ls2 in
    (m2, Er, gr, cs1++cs2++csr, lr)
  | QFBV64.bvSmulo w e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(Er, gr, csr, lr) := mk_env_smulo E2 g2 ls1 ls2 in
    (m2, Er, gr, cs1++cs2++csr, lr)
  | QFBV64.bvLneg e =>
    let '(m1, E1, g1, cs1, l1) := mk_env_bexp m s E g e in
    let '(E', g', cs, r) := mk_env_lneg E1 g1 l1 in
    (m1, E', g', cs1++cs, r)
  | QFBV64.bvConj e1 e2 =>
    let '(m1, E1, g1, cs1, l1) := mk_env_bexp m s E g e1 in
    let '(m2, E2, g2, cs2, l2) := mk_env_bexp m1 s E1 g1 e2 in
    let '(E', g', cs, r) := mk_env_conj E2 g2 l1 l2 in
    (m2, E', g', cs1++cs2++cs, r)
  | QFBV64.bvDisj e1 e2 =>
    let '(m1, E1, g1, cs1, l1) := mk_env_bexp m s E g e1 in
    let '(m2, E2, g2, cs2, l2) := mk_env_bexp m1 s E1 g1 e2 in
    let '(E', g', cs, r) := mk_env_disj E2 g2 l1 l2 in
    (m2, E', g', cs1++cs2++cs, r)
      (*(m, E, g, [], lit_ff)*) (* TODO *)
  end.



(* = bit_blast_exp_preserve and bit_blast_bexp_preserve = *)

Ltac bb_exp_bexp_vm_preserve :=
  lazymatch goal with
  | |- vm_preserve ?m ?m => exact: vm_preserve_refl
  | H1 : context f [bit_blast_exp _ _ ?e = (_, _, _, _) -> vm_preserve _ _],
         H2 : bit_blast_exp ?m1 _ ?e = (?m2, _, _, _)
    |- vm_preserve ?m1 ?m2 =>
    eapply H1; exact: H2
  | H1 : context f [bit_blast_bexp _ _ ?e = (_, _, _, _) -> vm_preserve _ _],
         H2 : bit_blast_bexp ?m1 _ ?e = (?m2, _, _, _)
    |- vm_preserve ?m1 ?m2 =>
    eapply H1; exact: H2
  | H1 : context f [bit_blast_exp _ _ ?e = (_, _, _, _) -> vm_preserve _ _],
         H2 : bit_blast_exp ?m1 _ ?e = (?m2, _, _, _)
    |- vm_preserve _ ?m2 =>
    apply: (@vm_preserve_trans _ m1);
    [bb_exp_bexp_vm_preserve | bb_exp_bexp_vm_preserve]
  | H1 : context f [bit_blast_bexp _ _ ?e = (_, _, _, _) -> vm_preserve _ _],
         H2 : bit_blast_bexp ?m1 _ ?e = (?m2, _, _, _)
    |- vm_preserve _ ?m2 =>
    apply: (@vm_preserve_trans _ m1);
    [bb_exp_bexp_vm_preserve | bb_exp_bexp_vm_preserve]
  | |- _ => idtac
  end.

(* Solve vm_preserve for those cases in bit_blast_exp and bit_blast_bexp
   that does not update vm. *)
Ltac auto_bit_blast_vm_preserve :=
  simpl; intros; dcase_hyps; subst; bb_exp_bexp_vm_preserve.

Lemma bit_blast_exp_preserve_var :
  forall (t : VarOrder.t) (m : vm) (g : generator) (m' : vm)
         (g' : generator) (cs : cnf) (lrs : wordsize.-tuple literal),
    bit_blast_exp m g (QFBV64.bvVar t) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  move=> v m g m' g' cs lrs /=. case Hfind: (VM.find v m).
  - case=> <- _ _ _. exact: vm_preserve_refl.
  - case Hv: (bit_blast_var g v)=> [[og ocs] olrs].
    case=> <- _ _ _. exact: vm_preserve_add_diag.
Qed.

Lemma bit_blast_exp_preserve_const :
  forall (w : nat) (b : BITS w) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
    bit_blast_exp m g (QFBV64.bvConst w b) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_not :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (m : vm) (g : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
      bit_blast_exp m g (QFBV64.bvNot w e1) = (m', g', cs, lrs) ->
      vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_and :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
        bit_blast_exp m g (QFBV64.bvAnd w e1 e2) = (m', g', cs, lrs) ->
        vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_or :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m  : vm) (g  : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e1 : QFBV64.exp w),
      (forall (m  : vm) (g  : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (m  : vm) (g  : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
      bit_blast_exp m g (QFBV64.bvOr w e0 e1) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_xor :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
        bit_blast_exp m g (QFBV64.bvXor w e1 e2) = (m', g', cs, lrs) ->
        vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_neg :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (m : vm) (g : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
      bit_blast_exp m g (QFBV64.bvNeg w e1) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_add :
  forall (w : nat),
  forall (e : QFBV64.exp w) ,
    (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : w.-tuple literal),
        bit_blast_exp m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (m : vm) (g : generator) (m' : vm) (g' : generator)
             (cs : cnf) (lrs : w.-tuple literal),
    bit_blast_exp m g (QFBV64.bvAdd w e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_sub :
  forall (w : nat),
  forall (e : QFBV64.exp w) ,
    (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : w.-tuple literal),
        bit_blast_exp m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (m : vm) (g : generator) (m' : vm) (g' : generator)
             (cs : cnf) (lrs : w.-tuple literal),
    bit_blast_exp m g (QFBV64.bvSub w e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_mul :
    forall (w0 : nat),
  forall (e : QFBV64.exp w0) ,
    (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : w0.-tuple literal),
        bit_blast_exp m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : w0.-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (m : vm) (g : generator) (m' : vm) (g' : generator)
             (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvMul w0 e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_mod :
  forall (w0 : nat) (e : QFBV64.exp w0) (e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvMod w0 e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_srem :
  forall (w0 : nat) (e : QFBV64.exp w0) (e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvSrem w0 e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_smod :
  forall (w0 : nat) (e : QFBV64.exp w0) (e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvSmod w0 e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_shl :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (m : vm) (g : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
      bit_blast_exp m g (QFBV64.bvShl w e0 e1) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed .

Lemma bit_blast_exp_preserve_lshr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (m : vm) (g : generator) (m' : vm) (g' : generator)
           (cs : cnf) (lrs : w.-tuple literal),
      bit_blast_exp m g (QFBV64.bvLshr w e0 e1) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed .

Lemma bit_blast_exp_preserve_ashr :
  forall (w : nat),
  forall (e0 : QFBV64.exp (w.+1)),
      (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : (w.+1).-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
  forall (e1 : QFBV64.exp (w.+1)),
      (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : (w.+1).-tuple literal),
          bit_blast_exp m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (m : vm) (g : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : (w.+1).-tuple literal),
      bit_blast_exp m g (QFBV64.bvAshr w e0 e1) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve .
Qed .

Lemma bit_blast_exp_preserve_concat :
  forall (w0 w1 : nat),
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : w0.-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e1 : QFBV64.exp w1),
      (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : w1.-tuple literal),
          bit_blast_exp m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (m : vm) (g : generator) (m' : vm) (g' : generator)
           (cs : cnf) (lrs : (w1 + w0).-tuple literal),
      bit_blast_exp m g (QFBV64.bvConcat w0 w1 e0 e1) = (m', g', cs, lrs) ->
      vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed .

Lemma bit_blast_exp_preserve_extract :
  forall (w i j : nat),
    forall (e : QFBV64.exp (j + (i - j + 1) + w)),
      (forall (m  : vm) (g  : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : (j + (i-j+1) + w).-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (m : vm) (g : generator) (m' : vm) (g' : generator) (cs : cnf)
           (lrs : (i - j + 1).-tuple literal),
      bit_blast_exp m g (QFBV64.bvExtract w i j e) = (m', g', cs, lrs) ->
      vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve .
Qed .

Lemma bit_blast_exp_preserve_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV64.exp (w3 + w2 + w1)),
      (forall (m  : vm) (g  : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : (w3+w2+w1).-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (m : vm) (g : generator) (m' : vm) (g' : generator)
           (cs : cnf) (lrs : w2.-tuple literal),
      bit_blast_exp m g (QFBV64.bvSlice w1 w2 w3 e) = (m', g', cs, lrs) ->
      vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve .
Qed .

Lemma bit_blast_exp_preserve_high :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m  : vm) (g  : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : (wl + wh).-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (m : vm) (g : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
    bit_blast_exp m g (QFBV64.bvHigh wh wl e) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve .
Qed .

Lemma bit_blast_exp_preserve_low :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m  : vm) (g  : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : (wl + wh).-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (m : vm) (g : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : wl.-tuple literal),
      bit_blast_exp m g (QFBV64.bvLow wh wl e) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve .
Qed .

Lemma bit_blast_exp_preserve_zeroextend :
  forall (w n : nat),
    forall (e : QFBV64.exp w),
      (forall (m  : vm) (g  : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (m : vm) (g : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : (w + n).-tuple literal),
    bit_blast_exp m g (QFBV64.bvZeroExtend w n e) = (m', g', cs, lrs) ->
    vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve .
Qed .

Lemma bit_blast_exp_preserve_signextend :
  forall (w n : nat),
    forall (e : QFBV64.exp w.+1),
      (forall (m  : vm) (g  : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : (w.+1).-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (m : vm) (g : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : (w.+1 + n).-tuple literal),
      bit_blast_exp m g (QFBV64.bvSignExtend w n e) = (m', g', cs, lrs) ->
      vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve .
Qed .

Lemma bit_blast_exp_preserve_ite :
  forall (w : nat) (b : QFBV64.bexp),
    (forall (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp m g b = (m', g', cs, lr) -> vm_preserve m m') ->
    forall (e : QFBV64.exp w),
      (forall (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (e0 : QFBV64.exp w),
        (forall (m : vm) (g : generator)
                (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
            bit_blast_exp m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
        forall (m : vm) (g : generator)
               (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g (QFBV64.bvIte w b e e0) = (m', g', cs, lrs) ->
          vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_false :
  forall (m : vm) (g : generator) (m' : vm) (g' : generator)
         (cs : cnf) (lrs : literal),
    bit_blast_bexp m g QFBV64.bvFalse = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_true :
  forall (m : vm) (g : generator) (m' : vm) (g' : generator)
         (cs : cnf) (lrs : literal),
    bit_blast_bexp m g QFBV64.bvTrue = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_eq :
  forall (w : nat) (e1 : QFBV64.exp w)
         (IH1 : forall (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e1 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (e2 : QFBV64.exp w)
         (IH2 : forall (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e2 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvEq w e1 e2) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_ult :
  forall (w : nat) (e1 : QFBV64.exp w)
         (IH1 : forall (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e1 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (e2 : QFBV64.exp w)
         (IH2 : forall (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e2 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvUlt w e1 e2) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_ule :
  forall (w : nat) (e1 : QFBV64.exp w)
         (IH1 : forall (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e1 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (e2 : QFBV64.exp w)
         (IH2 : forall (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e2 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvUle w e1 e2) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_ugt :
  forall (w : nat) (e1 : QFBV64.exp w)
         (IH1 : forall (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e1 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (e2 : QFBV64.exp w)
         (IH2 : forall (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e2 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvUgt w e1 e2) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_uge :
  forall (w : nat) (e1 : QFBV64.exp w)
         (IH1 : forall (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e1 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (e2 : QFBV64.exp w)
         (IH2 : forall (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e2 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvUge w e1 e2) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_slt :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
          bit_blast_exp m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp m g (QFBV64.bvSlt w e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_sle :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
          bit_blast_exp m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp m g (QFBV64.bvSle w e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_sgt :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
          bit_blast_exp m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp m g (QFBV64.bvSgt w e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_sge :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
          bit_blast_exp m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp m g (QFBV64.bvSge w e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_uaddo :
  forall (w : nat),
  forall (e : QFBV64.exp w) ,
    (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : w.-tuple literal),
        bit_blast_exp m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (m : vm) (g : generator) (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvUaddo w e e0) = (m', g', cs, lr) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_usubo :
  forall (w : nat),
  forall (e : QFBV64.exp w) ,
    (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : w.-tuple literal),
        bit_blast_exp m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (m : vm) (g : generator) (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvUsubo w e e0) = (m', g', cs, lr) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_umulo :
  forall (w : nat),
  forall (e : QFBV64.exp w) ,
    (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : w.-tuple literal),
        bit_blast_exp m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (m : vm) (g : generator) (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvUmulo w e e0) = (m', g', cs, lr) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_saddo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
          bit_blast_exp m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp m g (QFBV64.bvSaddo w e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_ssubo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
          bit_blast_exp m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp m g (QFBV64.bvSsubo w e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_smulo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
          bit_blast_exp m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp m g (QFBV64.bvSmulo w e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_lneg :
  forall (b : QFBV64.bexp)
         (IH :
            forall (m : vm) (g : generator)
                   (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
              bit_blast_bexp m g b = (m', g', cs, lrs) ->
              vm_preserve m m')
         (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvLneg b) = (m', g', cs, lrs) ->
    vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_conj :
  forall (b : QFBV64.bexp)
         (IH :
            forall (m : vm) (g : generator)
                   (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
              bit_blast_bexp m g b = (m', g', cs, lrs) ->
              vm_preserve m m')
         (b0 : QFBV64.bexp)
         (IH0 :
            forall (m : vm) (g : generator)
                   (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
              bit_blast_bexp m g b0 = (m', g', cs, lrs) ->
              vm_preserve m m')
         (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvConj b b0) = (m', g', cs, lrs) ->
    vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_disj :
  forall (b : QFBV64.bexp)
         (IH :
            forall (m : vm) (g : generator)
                   (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
              bit_blast_bexp m g b = (m', g', cs, lrs) ->
              vm_preserve m m')
         (b0 : QFBV64.bexp)
         (IH0 :
            forall (m : vm) (g : generator)
                   (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
              bit_blast_bexp m g b0 = (m', g', cs, lrs) ->
              vm_preserve m m')
         (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvDisj b b0) = (m', g', cs, lrs) ->
    vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Corollary bit_blast_exp_preserve :
  forall w (e : QFBV64.exp w) m g m' g' cs lrs,
    bit_blast_exp m g e = (m', g', cs, lrs) ->
    vm_preserve m m'
  with
    bit_blast_bexp_preserve :
      forall (e : QFBV64.bexp) m g m' g' cs lrs,
        bit_blast_bexp m g e = (m', g', cs, lrs) ->
        vm_preserve m m'.
Proof.
  (* bit_blast_exp_preserve *)
  move=> w [] {w}.
  - exact: bit_blast_exp_preserve_var.
  - exact: bit_blast_exp_preserve_const.
  - move=> w e.
    move: (bit_blast_exp_preserve _ e) => IH.
    exact: (bit_blast_exp_preserve_not IH).
  - move=> w e1 e2.
    move: (bit_blast_exp_preserve _ e1) (bit_blast_exp_preserve _ e2) => IH1 IH2.
    exact: (bit_blast_exp_preserve_and IH1 IH2).
  - move=> w e0 e1 .
    move: (bit_blast_exp_preserve _ e0) (bit_blast_exp_preserve _ e1) => IH0 IH1 .
    exact: (bit_blast_exp_preserve_or IH0 IH1) .
  - move=> w e1 e2.
    move: (bit_blast_exp_preserve _ e1) (bit_blast_exp_preserve _ e2) => IH1 IH2.
    exact: (bit_blast_exp_preserve_xor IH1 IH2).
  - move=> w e.
    move: (bit_blast_exp_preserve _ e) => IH.
    exact: (bit_blast_exp_preserve_neg IH).
  - move=> w e0 e1 .
    move: (bit_blast_exp_preserve _ e0) (bit_blast_exp_preserve _ e1) => IH0 IH1 .
    exact: bit_blast_exp_preserve_add.
  - move=> w e0 e1 .
    move: (bit_blast_exp_preserve _ e0) (bit_blast_exp_preserve _ e1) => IH0 IH1 .
    exact: (bit_blast_exp_preserve_sub IH0 IH1).
  - move=> w e0 e1.
    move: (bit_blast_exp_preserve _ e0) (bit_blast_exp_preserve _ e1) => IH0 IH1.
    exact: bit_blast_exp_preserve_mul.
  - exact: bit_blast_exp_preserve_mod.
  - exact: bit_blast_exp_preserve_srem.
  - exact: bit_blast_exp_preserve_smod.
  - move=> w e0 e1.
    apply: (bit_blast_exp_preserve_shl (bit_blast_exp_preserve _ e0)
                                       (bit_blast_exp_preserve _ e1)) .
  - move=> w e0 e1.
    apply: (bit_blast_exp_preserve_lshr (bit_blast_exp_preserve _ e0)
                                        (bit_blast_exp_preserve _ e1)) .
  - move=> w e0 e1.
    apply: (bit_blast_exp_preserve_ashr (bit_blast_exp_preserve _ e0)
                                        (bit_blast_exp_preserve _ e1)) .
  - move => w0 w1 e0 e1 .
    move: (bit_blast_exp_preserve _ e0) (bit_blast_exp_preserve _ e1)
    => IHe0 IHe1 .
    exact: (bit_blast_exp_preserve_concat IHe0 IHe1) .
  - move => w i j e .
    apply: bit_blast_exp_preserve_extract (bit_blast_exp_preserve _ e) .
  - move => w1 w2 w3 e .
    apply: bit_blast_exp_preserve_slice (bit_blast_exp_preserve _ e) .
  - move => wh wl e .
    apply: bit_blast_exp_preserve_high (bit_blast_exp_preserve _ e) .
  - move => wh wl e .
    apply: bit_blast_exp_preserve_low (bit_blast_exp_preserve _ e) .
  - move=> w n e .
    apply: bit_blast_exp_preserve_zeroextend (bit_blast_exp_preserve _ e) .
  - move => w n e .
    apply : bit_blast_exp_preserve_signextend (bit_blast_exp_preserve _ e) .
  - move=> w c e1 e2.
    move: (bit_blast_bexp_preserve c) (bit_blast_exp_preserve _ e1)
                                      (bit_blast_exp_preserve _ e2) => IHc IH1 IH2.
    exact: (bit_blast_exp_preserve_ite IHc IH1 IH2).
  (* bit_blast_bexp_preserve *)
  move=> [].
  - exact: bit_blast_bexp_preserve_false.
  - exact: bit_blast_bexp_preserve_true.
  - move=> w e1 e2.
    move: (bit_blast_exp_preserve _ e1) (bit_blast_exp_preserve _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_eq IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_preserve w e1) (bit_blast_exp_preserve w e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_ult IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_preserve w e1) (bit_blast_exp_preserve w e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_ule IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_preserve w e1) (bit_blast_exp_preserve w e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_ugt IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_preserve w e1) (bit_blast_exp_preserve w e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_uge IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_preserve _ e1) (bit_blast_exp_preserve _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_slt IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_preserve _ e1) (bit_blast_exp_preserve _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_sle IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_preserve _ e1) (bit_blast_exp_preserve _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_sgt IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_preserve _ e1) (bit_blast_exp_preserve _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_sge IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_preserve _ e1) (bit_blast_exp_preserve _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_uaddo IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_preserve _ e1) (bit_blast_exp_preserve _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_usubo IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_preserve _ e1) (bit_blast_exp_preserve _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_umulo IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_preserve _ e1) (bit_blast_exp_preserve _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_saddo IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_preserve _ e1) (bit_blast_exp_preserve _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_ssubo IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_preserve _ e1) (bit_blast_exp_preserve _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_smulo IH1 IH2).
  - move => e.
    move: (bit_blast_bexp_preserve e) => IH.
    exact: (bit_blast_bexp_preserve_lneg IH).
  - move=> e1 e2.
    move: (bit_blast_bexp_preserve e1) (bit_blast_bexp_preserve e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_conj IH1 IH2).
  - move=> e1 e2.
    move: (bit_blast_bexp_preserve e1) (bit_blast_bexp_preserve e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_disj IH1 IH2).
Qed.



(* = bit_blast_exp_correct and bit_blast_bexp_correct = *)

Lemma bit_blast_exp_var :
  forall (t : VarOrder.t) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : wordsize.-tuple literal),
    bit_blast_exp m g (QFBV64.bvVar t) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvVar t) s).
Proof.
  move=> v im ig s E om og ocs olrs. move=> Hblast Hcon Hcnf.
  move: (Hcon v) Hblast => {Hcon} Hcon. rewrite /=. case Hfind: (VM.find v im).
  - case=> Hm Hg Hcs Hlrs. move: Hcon; rewrite /consistent1.
    rewrite -Hm Hfind Hlrs. by apply.
  - case Hblast: (bit_blast_var ig v) => [[vg vcs] vlrs].
    case=> [Hom Hog Hocs Holrs]. move: Hcon; rewrite /consistent1.
    rewrite -Hom. rewrite (VM.Lemmas.find_add_eq _ _ (eq_refl v)).
    rewrite Holrs; by apply.
Qed.

Lemma bit_blast_exp_const :
  forall (w0 : nat) (b : BITS w0) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvConst w0 b) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvConst w0 b) s).
Proof.
  move=> w bv im ig s E om og ocs olrs. case=> _ _ <- <- _ Hprelude.
  move: (add_prelude_tt Hprelude) => /= Htt {im ig s om og ocs olrs Hprelude}.
  elim: w bv; first by done. move=> w IH. case/tupleP => hd tl.
  rewrite /= mapCons !theadE !beheadCons. apply/andP; split.
  - rewrite /enc_bit. case: hd => /=; by rewrite Htt.
  - exact: IH.
Qed.

Lemma bit_blast_exp_not :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bits E lrs (QFBV64.eval_exp e1 s)) ->
    forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
           (m' : vm) (g' : generator)
           (cs : cnf) (lrs : w.-tuple literal),
      bit_blast_exp m g (QFBV64.bvNot w e1) = (m', g', cs, lrs) ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvNot w e1) s).
Proof.
  move=> w e1 IH1 m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp m g e1) => [[[m1 g1] cs1] ls1].
  case Hr : (bit_blast_not g1 ls1) => [[gr csr] lsr].
  case=> <- _ <- <-. move=> Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_append. move/andP=> [Hic1 Hicr].
  apply: (bit_blast_not_correct Hr _ Hicr).
  exact: (IH1 _ _ _ _ _ _ _ _ He1 Hcons1 Hic1).
Qed.

Lemma bit_blast_exp_and :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bits E lrs (QFBV64.eval_exp e1 s)) ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e2 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e2 s)) ->
      forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lrs : w.-tuple literal),
        bit_blast_exp m g (QFBV64.bvAnd w e1 e2) = (m', g', cs, lrs) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvAnd w e1 e2) s).
Proof.
  move=> w e1 IH1 e2 IH2 m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_and g2 ls1 ls2) => [[gr csr] lsr].
  case=> <- _ <- <-. move=> Hcons2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcons2) => Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_append. move/andP=> [Hic1 /andP [Hic2 Hicr]].
  apply: (bit_blast_and_correct Hr _ _ Hicr).
  - exact: (IH1 _ _ _ _ _ _ _ _ He1 Hcons1 Hic1).
  - exact: (IH2 _ _ _ _ _ _ _ _ He2 Hcons2 Hic2).
Qed.


Lemma bit_blast_exp_or :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e0 s)) ->
    forall (e1 : QFBV64.exp w),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e1 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e1 s)) ->
    forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
      bit_blast_exp m g (QFBV64.bvOr w e0 e1) = (m', g', cs, lrs) ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvOr w e0 e1) s).
Proof.
  move=> w e0 IHe0 e1 IHe1 m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock. dcase_goal. case; intros; subst.
  rewrite !add_prelude_append in H7.
  move: H7 => /andP [Hcs0 /andP [Hcs1 Hcs2]] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve H0) H6) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve H) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ H Hcon1 Hcs0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ H0 H6 Hcs1) => Hencls1.
  apply: (bit_blast_or_correct H1 Hencls0 Hencls1 Hcs2).
Qed .

Lemma bit_blast_exp_xor :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bits E lrs (QFBV64.eval_exp e1 s)) ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e2 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e2 s)) ->
      forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lrs : w.-tuple literal),
        bit_blast_exp m g (QFBV64.bvXor w e1 e2) = (m', g', cs, lrs) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvXor w e1 e2) s).
Proof.
  move=> w e1 IH1 e2 IH2 m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_xor g2 ls1 ls2) => [[gr csr] lsr].
  case=> <- _ <- <-. move=> Hcons2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcons2) => Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_append. move/andP=> [Hic1 /andP [Hic2 Hicr]].
  apply: (bit_blast_xor_correct Hr _ _ Hicr).
  - exact: (IH1 _ _ _ _ _ _ _ _ He1 Hcons1 Hic1).
  - exact: (IH2 _ _ _ _ _ _ _ _ He2 Hcons2 Hic2).
Qed.

Lemma bit_blast_exp_neg :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
        bit_blast_exp m g e = (m', g', cs, lrs) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bits E lrs (QFBV64.eval_exp e s)) ->
    forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
           (m' : vm) (g' : generator)
           (cs : cnf) (lrs : w.-tuple literal),
    bit_blast_exp m g (QFBV64.bvNeg w e) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvNeg w e) s).
Proof.
  move=> w e IH1 m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp m g e) => [[[m1 g1] cs1] ls1].
  case Hr : (bit_blast_neg g1 ls1) => [[gr csr] lsr].
  case=> <- _ <- <-. move=> Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_append. move/andP=> [Hic1 Hicr].
  apply: (bit_blast_neg_correct Hr _ Hicr).
  exact : (IH1 _ _ _ _ _ _ _ _ He1 Hcons1 Hic1).
Qed.

Lemma bit_blast_exp_add :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e0 s)) ->
    forall (e1 : QFBV64.exp w),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e1 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e1 s)) ->
    forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
      bit_blast_exp m g (QFBV64.bvAdd w e0 e1) = (m', g', cs, lrs) ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvAdd w e0 e1) s).
Proof.
  move => w e0 IHe0 e1 IHe1 m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock. dcase_goal. case; intros; subst.
  rewrite !add_prelude_append in H7.
  move: H7 => /andP [Hcs0 /andP [Hcs1 Hcs2]] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve H0) H6) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve H) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ H Hcon1 Hcs0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ H0 H6 Hcs1) => Hencls1.
  set br:=(addB (QFBV64.eval_exp e0 s) (QFBV64.eval_exp e1 s)).
  apply (bit_blast_add_correct H1 Hencls0 Hencls1); done.
Qed.

Lemma bit_blast_exp_sub :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e0 s)) ->
    forall (e1 : QFBV64.exp w),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e1 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e1 s)) ->
    forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
    bit_blast_exp m g (QFBV64.bvSub w e0 e1) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvSub w e0 e1) s).
Proof.
  move => w e0 IHe0 e1 IHe1 m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock. dcase_goal. case; intros; subst.
  rewrite !add_prelude_append in H7.
  move: H7 => /andP [Hcs0 /andP [Hcs1 Hcs2]] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve H0) H6) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve H) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ H Hcon1 Hcs0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ H0 H6 Hcs1) => Hencls1.
  set br:=(subB (QFBV64.eval_exp e0 s) (QFBV64.eval_exp e1 s)).
  apply (bit_blast_sub_correct H1 Hencls0 Hencls1); done.
Qed.

Lemma bit_blast_exp_mul :
    forall (w : nat),
    forall (e : QFBV64.exp w),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e s)) ->
    forall (e0 : QFBV64.exp w),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e0 s)) ->
    forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
    bit_blast_exp m g (QFBV64.bvMul w e e0) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvMul w e e0) s).
Proof.
  move => w e0 IHe0 e1 IHe1 m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock. dcase_goal. case; intros; subst.
  rewrite !add_prelude_append in H7.
  move : H7 => /andP [Hcs0 /andP [Hcs1 Hcs2]].
  move : (vm_preserve_consistent (bit_blast_exp_preserve H0) H6) => Hconm0.
  move : (vm_preserve_consistent (bit_blast_exp_preserve H) Hconm0) => Hconm.
  move : (IHe0 _ _ _ _ _ _ _ _ H Hconm0 Hcs0) => Hence0.
  move : (IHe1 _ _ _ _ _ _ _ _ H0 H6 Hcs1) => Hence1.
  set br :=( mulB (QFBV64.eval_exp e0 s) (QFBV64.eval_exp e1 s)).
  apply (bit_blast_mul_correct H1 Hence0 Hence1); done.
Qed.

Lemma bit_blast_exp_mod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvMod w0 e e0) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvMod w0 e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_srem :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvSrem w0 e e0) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvSrem w0 e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_smod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvSmod w0 e e0) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvSmod w0 e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_shl :
  forall (w : nat),
    forall (e0: QFBV64.exp w),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e0 s)) ->
    forall (e1: QFBV64.exp w),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e1 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e1 s)) ->
    forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
      bit_blast_exp m g (QFBV64.bvShl w e0 e1) = (m', g', cs, lrs) ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvShl w e0 e1) s).
Proof.
  move => w e0 IHe0 e1 IHe1 m g s E m' g' cs lrs .
  rewrite (lock interp_cnf) /= -lock. dcase_goal. case; intros; subst.
  rewrite !add_prelude_append in H7 .
  move: H7 => /andP [Hcs0 /andP [Hcs1 Hcs2]] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve H0) H6) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve H) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ H Hcon1 Hcs0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ H0 H6 Hcs1) => Hencls1.
  apply (bit_blast_shl_correct H1 Hencls0 Hencls1 Hcs2) .
Qed .

Lemma bit_blast_exp_lshr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e0 s)) ->
    forall (e1 : QFBV64.exp w),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e1 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e1 s)) ->
    forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
      bit_blast_exp m g (QFBV64.bvLshr w e0 e1) = (m', g', cs, lrs) ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvLshr w e0 e1) s).
Proof.
  move => w e0 IHe0 e1 IHe1 m g s E m' g' cs lrs .
  rewrite (lock interp_cnf) /= -lock. dcase_goal. case; intros; subst.
  rewrite !add_prelude_append in H7 .
  move: H7 => /andP [Hcs0 /andP [Hcs1 Hcs2]] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve H0) H6) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve H) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ H Hcon1 Hcs0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ H0 H6 Hcs1) => Hencls1.
  apply (bit_blast_lshr_correct H1 Hencls0 Hencls1 Hcs2) .
Qed .

Lemma bit_blast_exp_ashr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w.+1),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator)
              (cs : cnf) (lrs : (w.+1).-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e0 s)) ->
    forall (e1 : QFBV64.exp w.+1),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator)
              (cs : cnf) (lrs : (w.+1).-tuple literal),
          bit_blast_exp m g e1 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e1 s)) ->
    forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
           (m' : vm) (g' : generator)
           (cs : cnf) (lrs : (w.+1).-tuple literal),
      bit_blast_exp m g (QFBV64.bvAshr w e0 e1) = (m', g', cs, lrs) ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvAshr w e0 e1) s).
Proof.
  move => w e0 IHe0 e1 IHe1 m g s E m' g' cs lrs .
  rewrite (lock interp_cnf) /= -lock. dcase_goal. case; intros; subst.
  rewrite !add_prelude_append in H7 .
  move: H7 => /andP [Hcs0 /andP [Hcs1 Hcs2]] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve H0) H6) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve H) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ H Hcon1 Hcs0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ H0 H6 Hcs1) => Hencls1.
  apply (bit_blast_ashr_correct H1 Hencls0 Hencls1 Hcs2) .
Qed .

Lemma bit_blast_exp_concat :
  forall (w0 w1 : nat),
    forall (e0 : QFBV64.exp w0),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
          bit_blast_exp m g e0 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e0 s)) ->
    forall (e1 : QFBV64.exp w1),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w1.-tuple literal),
          bit_blast_exp m g e1 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e1 s)) ->
    forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : (w1 + w0).-tuple literal),
      bit_blast_exp m g (QFBV64.bvConcat w0 w1 e0 e1) = (m', g', cs, lrs) ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvConcat w0 w1 e0 e1) s).
Proof.
  move => w0 w1 e0 IHe0 e1 IHe1 m g s E m' g' cs lrs .
  rewrite (lock interp_cnf) /= -lock. dcase_goal. case; intros; subst.
  rewrite !add_prelude_append in H6 .
  move: H6 => /andP [Hcs0 /andP [Hcs1 _]] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve H0) H5) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve H) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ H Hcon1 Hcs0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ H0 H5 Hcs1) => Hencls1.
  apply: (bit_blast_concat_correct Hencls0 Hencls1).
Qed .

Lemma bit_blast_exp_extract :
  forall (w i j : nat),
    forall (e : QFBV64.exp (j + (i - j + 1) + w)),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf)
              (lrs : (j + (i - j + 1) + w).-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e s)) ->
    forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : (i - j + 1).-tuple literal),
      bit_blast_exp m g (QFBV64.bvExtract w i j e) = (m', g', cs, lrs) ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvExtract w i j e) s).
Proof.
  move=> w i j e IH m g s E m' g' cs lr .
  rewrite (lock interp_cnf) /= -lock. dcase_goal. case; intros; subst.
  rewrite !add_prelude_append in H5.
  move: H5 => /andP [Hcs0 _] .
  move: (IH _ _ _ _ _ _ _ _ H H4 Hcs0) => Henc .
  apply: bit_blast_slice_correct Henc Hcs0 .
Qed .

Lemma bit_blast_exp_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV64.exp (w3 + w2 + w1)),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : (w3 + w2 +w1).-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e s)) ->
    forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf)
           (lrs : w2.-tuple literal),
      bit_blast_exp m g (QFBV64.bvSlice w1 w2 w3 e) = (m', g', cs, lrs) ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvSlice w1 w2 w3 e) s).
Proof.
  move=> w1 w2 w3 e IH m g s E m' g' cs lr .
  rewrite (lock interp_cnf) /= -lock. dcase_goal. case; intros; subst.
  rewrite !add_prelude_append in H5.
  move: H5 => /andP [Hcs0 _] .
  move: (IH _ _ _ _ _ _ _ _ H H4 Hcs0) => Henc .
  apply: bit_blast_slice_correct Henc Hcs0 .
Qed .

Lemma bit_blast_exp_high :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : (wl + wh).-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e s)) ->
    forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
      bit_blast_exp m g (QFBV64.bvHigh wh wl e) = (m', g', cs, lrs) ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvHigh wh wl e) s).
Proof.
  move=> wh wl e IH m g s E m' g' cs lr .
  rewrite (lock interp_cnf) /= -lock. dcase_goal. case; intros; subst.
  rewrite !add_prelude_append in H5.
  move: H5 => /andP [Hcs0 _] .
  move: (IH _ _ _ _ _ _ _ _ H H4 Hcs0) => Henc .
  apply: bit_blast_high_correct Henc Hcs0 .
Qed .

Lemma bit_blast_exp_low :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : (wl + wh).-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e s)) ->
    forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : wl.-tuple literal),
      bit_blast_exp m g (QFBV64.bvLow wh wl e) = (m', g', cs, lrs) ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvLow wh wl e) s).
Proof.
  move=> wh wl e IH m g s E m' g' cs lr .
  rewrite (lock interp_cnf) /= -lock. dcase_goal. case; intros; subst.
  rewrite !add_prelude_append in H5.
  move: H5 => /andP [Hcs0 _] .
  move: (IH _ _ _ _ _ _ _ _ H H4 Hcs0) => Henc .
  apply: bit_blast_low_correct Henc Hcs0 .
Qed .

Lemma bit_blast_exp_zeroextend :
  forall (w n : nat),
    forall (e : QFBV64.exp w),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e s)) ->
    forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : (w + n).-tuple literal),
      bit_blast_exp m g (QFBV64.bvZeroExtend w n e) = (m', g', cs, lrs) ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvZeroExtend w n e) s).
Proof.
  move=> w n e IH m g s E m' g' cs lr .
  rewrite (lock interp_cnf) /= -lock. dcase_goal. case; intros; subst.
  rewrite !add_prelude_append in H5.
  move: H5 => /andP [Hcs0 _] .
  move: (IH _ _ _ _ _ _ _ _ H H4 Hcs0) => Henc .
  apply: bit_blast_zeroextend_correct Henc Hcs0 .
Qed .

Lemma bit_blast_exp_signextend :
  forall (w n : nat),
    forall (e : QFBV64.exp w.+1),
      (forall (m  : vm) (g  : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : (w.+1).-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e s)) ->
    forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : (w.+1 + n).-tuple literal),
    bit_blast_exp m g (QFBV64.bvSignExtend w n e) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvSignExtend w n e) s).
Proof.
  move => w n e IH m g s E m' g' cs lr .
  rewrite (lock interp_cnf) /= -lock. dcase_goal. case; intros; subst.
  rewrite !add_prelude_append in H5.
  move: H5 => /andP [Hcs0 _] .
  move: (IH _ _ _ _ _ _ _ _ H H4 Hcs0) => Henc .
  by move: (bit_blast_signextend_correct n Henc Hcs0) .
Qed .

Lemma bit_blast_exp_ite :
  forall (w : nat) (b : QFBV64.bexp),
    (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp m g b = (m', g', cs, lr) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bit E lr (QFBV64.eval_bexp b s)) ->
    forall (e : QFBV64.exp w),
      (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e s)) ->
      forall (e0 : QFBV64.exp w),
        (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
            bit_blast_exp m g e0 = (m', g', cs, lrs) ->
            consistent m' E s ->
            interp_cnf E (add_prelude cs) ->
            enc_bits E lrs (QFBV64.eval_exp e0 s)) ->
        forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
               (m' : vm) (g' : generator)
               (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g (QFBV64.bvIte w b e e0) = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvIte w b e e0) s).
Proof.
  move=> w c IHc e1 IH1 e2 IH2 m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock. dcase_goal. case; intros; subst.
  rewrite !add_prelude_append in H8.
  move: H8 => /andP [Hcs0 /andP [Hcs1 /andP [Hcs2 Hcs3]]].
  move: (vm_preserve_consistent (bit_blast_exp_preserve H1) H7) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve H0) Hcon1) => Hcon0.
  move: (IHc _ _ _ _ _ _ _ _ H Hcon0 Hcs0) => Hencl.
  move: (IH1 _ _ _ _ _ _ _ _ H0 Hcon1 Hcs1) => Hencls.
  move: (IH2 _ _ _ _ _ _ _ _ H1 H7 Hcs2) => Hencls0.
  apply: (bit_blast_ite_correct H2 Hencl Hencls Hencls0 Hcs3). reflexivity.
Qed.

Lemma bit_blast_bexp_false :
  forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g QFBV64.bvFalse = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) -> enc_bit E lr (QFBV64.eval_bexp QFBV64.bvFalse s).
Proof.
  move=> im ig s E om og ocs olr [] <- _ <- <- Hcon Hcs /=.
  exact: (add_prelude_enc_bit_ff Hcs).
Qed.

Lemma bit_blast_bexp_true :
  forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g QFBV64.bvTrue = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) -> enc_bit E lr (QFBV64.eval_bexp QFBV64.bvTrue s).
Proof.
  move=> im ig s E om og ocs olr [] <- _ <- <- Hcon Hcs /=.
  exact: (add_prelude_enc_bit_tt Hcs).
Qed.

Lemma bit_blast_bexp_eq :
  forall (w : nat)
         (e : QFBV64.exp w)
         (IH : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e = (m', g', cs, lrs) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bits E lrs (QFBV64.eval_exp e s))
         (e0 : QFBV64.exp w)
         (IH0 : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e0 = (m', g', cs, lrs) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bits E lrs (QFBV64.eval_exp e0 s))
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvEq w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvEq w e e0) s).
Proof.
  move=> w e1 IH1 e2 IH2 im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblasteq: (bit_blast_eq g2 rs1 rs2) => [[geq cseq] req].
  case => Hom Hog Hocs Holrs Hcon Hcs. rewrite -Hocs in Hcs => {Hocs ocs}.
  rewrite Hog in Hblasteq => {Hog geq}. rewrite Hom in Hblast2 => {Hom m2}.
  rewrite Holrs in Hblasteq => {Holrs req}.
  rewrite 2!add_prelude_append in Hcs. move/andP: Hcs => [Hcs1 Hcs].
  move/andP: Hcs => [Hcs2 Hcseq].
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon'.
  move: (IH1 _ _ _ _ _ _ _ _ Hblast1 Hcon' Hcs1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ Hblast2 Hcon Hcs2) => Henc2.
  exact: (bit_blast_eq_correct Hblasteq Henc1 Henc2 Hcseq).
Qed.

Lemma bit_blast_bexp_ult :
  forall (w : nat)
         (e : QFBV64.exp w)
         (IH : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e = (m', g', cs, lrs) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bits E lrs (QFBV64.eval_exp e s))
         (e0 : QFBV64.exp w)
         (IH0 : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e0 = (m', g', cs, lrs) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bits E lrs (QFBV64.eval_exp e0 s))
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvUlt w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvUlt w e e0) s).
Proof.
  move=> w e1 IH1 e2 IH2 im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastult: (bit_blast_ult g2 rs1 rs2) => [[gult csult] rult].
  case => Hom Hog Hocs Holrs Hcon Hcs. rewrite -Hocs in Hcs => {Hocs ocs}.
  rewrite Hog in Hblastult => {Hog gult}. rewrite Hom in Hblast2 => {Hom m2}.
  rewrite Holrs in Hblastult => {Holrs rult}.
  rewrite 2!add_prelude_append in Hcs. move/andP: Hcs => [Hcs1 Hcs].
  move/andP: Hcs => [Hcs2 Hcsult].
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon'.
  move: (IH1 _ _ _ _ _ _ _ _ Hblast1 Hcon' Hcs1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ Hblast2 Hcon Hcs2) => Henc2.
  exact: (bit_blast_ult_correct Hblastult Henc1 Henc2 Hcsult).
Qed.

Lemma bit_blast_bexp_ule :
  forall (w : nat)
         (e : QFBV64.exp w)
         (IH : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e = (m', g', cs, lrs) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bits E lrs (QFBV64.eval_exp e s))
         (e0 : QFBV64.exp w)
         (IH0 : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e0 = (m', g', cs, lrs) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bits E lrs (QFBV64.eval_exp e0 s))
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvUle w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvUle w e e0) s).
Proof.
  move=> w e1 IH1 e2 IH2 im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastule: (bit_blast_ule g2 rs1 rs2) => [[gule csule] rule].
  case => Hom Hog Hocs Holrs Hcon Hcs. rewrite -Hocs in Hcs => {Hocs ocs}.
  rewrite Hog in Hblastule => {Hog gule}. rewrite Hom in Hblast2 => {Hom m2}.
  rewrite Holrs in Hblastule => {Holrs rule}.
  rewrite 2!add_prelude_append in Hcs. move/andP: Hcs => [Hcs1 Hcs].
  move/andP: Hcs => [Hcs2 Hcsule].
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon'.
  move: (IH1 _ _ _ _ _ _ _ _ Hblast1 Hcon' Hcs1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ Hblast2 Hcon Hcs2) => Henc2.
  exact: (bit_blast_ule_correct Hblastule Henc1 Henc2 Hcsule).
Qed.

Lemma bit_blast_bexp_ugt :
  forall (w : nat)
         (e : QFBV64.exp w)
         (IH : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e = (m', g', cs, lrs) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bits E lrs (QFBV64.eval_exp e s))
         (e0 : QFBV64.exp w)
         (IH0 : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e0 = (m', g', cs, lrs) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bits E lrs (QFBV64.eval_exp e0 s))
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvUgt w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvUgt w e e0) s).
Proof.
  move=> w e1 IH1 e2 IH2 im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastugt: (bit_blast_ugt g2 rs1 rs2) => [[gugt csugt] rugt].
  case => Hom Hog Hocs Holrs Hcon Hcs. rewrite -Hocs in Hcs => {Hocs ocs}.
  rewrite Hog in Hblastugt => {Hog gugt}. rewrite Hom in Hblast2 => {Hom m2}.
  rewrite Holrs in Hblastugt => {Holrs rugt}.
  rewrite 2!add_prelude_append in Hcs. move/andP: Hcs => [Hcs1 Hcs].
  move/andP: Hcs => [Hcs2 Hcsugt].
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon'.
  move: (IH1 _ _ _ _ _ _ _ _ Hblast1 Hcon' Hcs1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ Hblast2 Hcon Hcs2) => Henc2.
  exact: (bit_blast_ugt_correct Hblastugt Henc1 Henc2 Hcsugt).
Qed.

Lemma bit_blast_bexp_uge :
  forall (w : nat)
         (e : QFBV64.exp w)
         (IH : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e = (m', g', cs, lrs) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bits E lrs (QFBV64.eval_exp e s))
         (e0 : QFBV64.exp w)
         (IH0 : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e0 = (m', g', cs, lrs) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bits E lrs (QFBV64.eval_exp e0 s))
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvUge w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvUge w e e0) s).
Proof.
  move=> w e1 IH1 e2 IH2 im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastuge: (bit_blast_uge g2 rs1 rs2) => [[guge csuge] ruge].
  case => Hom Hog Hocs Holrs Hcon Hcs. rewrite -Hocs in Hcs => {Hocs ocs}.
  rewrite Hog in Hblastuge => {Hog guge}. rewrite Hom in Hblast2 => {Hom m2}.
  rewrite Holrs in Hblastuge => {Holrs ruge}.
  rewrite 2!add_prelude_append in Hcs. move/andP: Hcs => [Hcs1 Hcs].
  move/andP: Hcs => [Hcs2 Hcsuge].
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon'.
  move: (IH1 _ _ _ _ _ _ _ _ Hblast1 Hcon' Hcs1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ Hblast2 Hcon Hcs2) => Henc2.
  exact: (bit_blast_uge_correct Hblastuge Henc1 Henc2 Hcsuge).
Qed.

Lemma bit_blast_bexp_slt :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bits E lrs (QFBV64.eval_exp e1 s)) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
          bit_blast_exp m g e2 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e2 s)) ->
      forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp m g (QFBV64.bvSlt w e1 e2) = (m', g', cs, lr) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvSlt w e1 e2) s).
Proof.
  move=> w e1 IH1 e2 IH2 m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_slt g2 ls1 ls2) => [[gr csr] r].
  case=> <- _ <- <-. move=> Hcons2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcons2) => Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_append. move/andP=> [Hic1 /andP [Hic2 Hicr]].
  apply: (bit_blast_slt_correct Hr _ _ Hicr).
  - exact: (IH1 _ _ _ _ _ _ _ _ He1 Hcons1 Hic1).
  - exact: (IH2 _ _ _ _ _ _ _ _ He2 Hcons2 Hic2).
Qed.

Lemma bit_blast_bexp_sle :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bits E lrs (QFBV64.eval_exp e1 s)) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
          bit_blast_exp m g e2 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e2 s)) ->
      forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp m g (QFBV64.bvSle w e1 e2) = (m', g', cs, lr) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvSle w e1 e2) s).
Proof.
  move=> w e1 IH1 e2 IH2 m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_sle g2 ls1 ls2) => [[gr csr] r].
  case=> <- _ <- <-. move=> Hcons2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcons2) => Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_append. move/andP=> [Hic1 /andP [Hic2 Hicr]].
  apply: (bit_blast_sle_correct Hr _ _ Hicr).
  - exact: (IH1 _ _ _ _ _ _ _ _ He1 Hcons1 Hic1).
  - exact: (IH2 _ _ _ _ _ _ _ _ He2 Hcons2 Hic2).
Qed.

Lemma bit_blast_bexp_sgt :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bits E lrs (QFBV64.eval_exp e1 s)) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
          bit_blast_exp m g e2 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e2 s)) ->
      forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp m g (QFBV64.bvSgt w e1 e2) = (m', g', cs, lr) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvSgt w e1 e2) s).
Proof.
  move=> w e1 IH1 e2 IH2 m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_sgt g2 ls1 ls2) => [[gr csr] r].
  case=> <- _ <- <-. move=> Hcons2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcons2) => Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_append. move/andP=> [Hic1 /andP [Hic2 Hicr]].
  apply: (bit_blast_sgt_correct Hr _ _ Hicr).
  - exact: (IH1 _ _ _ _ _ _ _ _ He1 Hcons1 Hic1).
  - exact: (IH2 _ _ _ _ _ _ _ _ He2 Hcons2 Hic2).
Qed.

Lemma bit_blast_bexp_sge :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bits E lrs (QFBV64.eval_exp e1 s)) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
          bit_blast_exp m g e2 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e2 s)) ->
      forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp m g (QFBV64.bvSge w e1 e2) = (m', g', cs, lr) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvSge w e1 e2) s).
Proof.
  move=> w e1 IH1 e2 IH2 m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_sge g2 ls1 ls2) => [[gr csr] r].
  case=> <- _ <- <-. move=> Hcons2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcons2) => Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_append. move/andP=> [Hic1 /andP [Hic2 Hicr]].
  apply: (bit_blast_sge_correct Hr _ _ Hicr).
  - exact: (IH1 _ _ _ _ _ _ _ _ He1 Hcons1 Hic1).
  - exact: (IH2 _ _ _ _ _ _ _ _ He2 Hcons2 Hic2).
Qed.

Lemma bit_blast_bexp_uaddo :
  forall (w : nat)
         (e : QFBV64.exp w)
         (IH : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e = (m', g', cs, lrs) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bits E lrs (QFBV64.eval_exp e s))
         (e0 : QFBV64.exp w)
         (IH0 : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e0 = (m', g', cs, lrs) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bits E lrs (QFBV64.eval_exp e0 s))
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvUaddo w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvUaddo w e e0) s).
Proof.
  move=> w e1 IH1 e2 IH2 im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastuaddo: (bit_blast_uaddo g2 rs1 rs2) => [[guaddo csuaddo] ruaddo].
  case => Hom Hog Hocs Holrs Hcon Hcs. rewrite -Hocs in Hcs => {Hocs ocs}.
  rewrite Hog in Hblastuaddo => {Hog guaddo}. rewrite Hom in Hblast2 => {Hom m2}.
  rewrite Holrs in Hblastuaddo => {Holrs ruaddo}.
  rewrite 2!add_prelude_append in Hcs. move/andP: Hcs => [Hcs1 Hcs].
  move/andP: Hcs => [Hcs2 Hcsuaddo].
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon'.
  move: (IH1 _ _ _ _ _ _ _ _ Hblast1 Hcon' Hcs1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ Hblast2 Hcon Hcs2) => Henc2.
  apply (bit_blast_uaddo_correct Hblastuaddo Henc1 Henc2 Hcsuaddo).
Qed.

Lemma bit_blast_bexp_usubo :
  forall (w : nat)
         (e : QFBV64.exp w)
         (IH : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e = (m', g', cs, lrs) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bits E lrs (QFBV64.eval_exp e s))
         (e0 : QFBV64.exp w)
         (IH0 : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e0 = (m', g', cs, lrs) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bits E lrs (QFBV64.eval_exp e0 s))
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvUsubo w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvUsubo w e e0) s).
Proof.
  move=> w e1 IH1 e2 IH2 im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastusubo: (bit_blast_usubo g2 rs1 rs2) => [[gusubo csusubo] rusubo].
  case => Hom Hog Hocs Holrs Hcon Hcs. rewrite -Hocs in Hcs => {Hocs ocs}.
  rewrite Hog in Hblastusubo => {Hog gusubo}. rewrite Hom in Hblast2 => {Hom m2}.
  rewrite Holrs in Hblastusubo => {Holrs rusubo}.
  rewrite 2!add_prelude_append in Hcs. move/andP: Hcs => [Hcs1 Hcs].
  move/andP: Hcs => [Hcs2 Hcsusubo].
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon'.
  move: (IH1 _ _ _ _ _ _ _ _ Hblast1 Hcon' Hcs1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ Hblast2 Hcon Hcs2) => Henc2.
  remember (carry_subB (QFBV64.eval_exp e1 s) (QFBV64.eval_exp e2 s)) as br .
  symmetry in Heqbr.
  apply (bit_blast_usubo_correct Hblastusubo Henc1 Henc2 Heqbr Hcsusubo).
Qed.

Lemma bit_blast_bexp_umulo :
  forall (w : nat)
         (e : QFBV64.exp w)
         (IH : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e = (m', g', cs, lrs) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bits E lrs (QFBV64.eval_exp e s))
         (e0 : QFBV64.exp w)
         (IH0 : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e0 = (m', g', cs, lrs) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bits E lrs (QFBV64.eval_exp e0 s))
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvUmulo w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvUmulo w e e0) s).
Proof.
  move=> w e1 IH1 e2 IH2 im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastumulo: (bit_blast_umulo g2 rs1 rs2) => [[gumulo csumulo] rumulo].
  case => Hom Hog Hocs Holrs Hcon Hcs. rewrite -Hocs in Hcs => {Hocs ocs}.
  rewrite Hog in Hblastumulo => {Hog gumulo}. rewrite Hom in Hblast2 => {Hom m2}.
  rewrite Holrs in Hblastumulo => {Holrs rumulo}.
  rewrite 2!add_prelude_append in Hcs. move/andP: Hcs => [Hcs1 Hcs].
  move/andP: Hcs => [Hcs2 Hcsumulo].
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon'.
  move: (IH1 _ _ _ _ _ _ _ _ Hblast1 Hcon' Hcs1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ Hblast2 Hcon Hcs2) => Henc2.
  apply (bit_blast_umulo_correct Hblastumulo Henc1 Henc2 Hcsumulo).
Qed.

Lemma bit_blast_bexp_saddo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bits E lrs (QFBV64.eval_exp e1 s)) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
          bit_blast_exp m g e2 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e2 s)) ->
      forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp m g (QFBV64.bvSaddo w e1 e2) = (m', g', cs, lr) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvSaddo w e1 e2) s).
Proof.
  move=> w e1 IH1 e2 IH2 m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_saddo g2 ls1 ls2) => [[gr csr] r].
  case=> <- _ <- <-. move=> Hcons2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcons2) => Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_append. move/andP=> [Hic1 /andP [Hic2 Hicr]].
  apply: (bit_blast_saddo_correct Hr _ _ Hicr).
  - exact: (IH1 _ _ _ _ _ _ _ _ He1 Hcons1 Hic1).
  - exact: (IH2 _ _ _ _ _ _ _ _ He2 Hcons2 Hic2).
Qed.

Lemma bit_blast_bexp_ssubo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bits E lrs (QFBV64.eval_exp e1 s)) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
          bit_blast_exp m g e2 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e2 s)) ->
      forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp m g (QFBV64.bvSsubo w e1 e2) = (m', g', cs, lr) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvSsubo w e1 e2) s).
Proof.
  move=> w e1 IH1 e2 IH2 m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_ssubo g2 ls1 ls2) => [[gr csr] r].
  case=> <- _ <- <-. move=> Hcons2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcons2) => Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_append. move/andP=> [Hic1 /andP [Hic2 Hicr]].
  apply: (bit_blast_ssubo_correct Hr _ _ Hicr).
  - exact: (IH1 _ _ _ _ _ _ _ _ He1 Hcons1 Hic1).
  - exact: (IH2 _ _ _ _ _ _ _ _ He2 Hcons2 Hic2).
Qed.

Lemma bit_blast_bexp_smulo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
        bit_blast_exp m g e1 = (m', g', cs, lrs) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bits E lrs (QFBV64.eval_exp e1 s)) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.+1.-tuple literal),
          bit_blast_exp m g e2 = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e2 s)) ->
      forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp m g (QFBV64.bvSmulo w e1 e2) = (m', g', cs, lr) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvSmulo w e1 e2) s).
Proof.
  move=> w e1 IH1 e2 IH2 m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_smulo g2 ls1 ls2) => [[gr csr] r].
  case=> <- _ <- <-. move=> Hcons2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcons2) => Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_append. move/andP=> [Hic1 /andP [Hic2 Hicr]].
  apply: (bit_blast_smulo_correct Hr _ _ Hicr).
  - exact: (IH1 _ _ _ _ _ _ _ _ He1 Hcons1 Hic1).
  - exact: (IH2 _ _ _ _ _ _ _ _ He2 Hcons2 Hic2).
Qed.

Lemma bit_blast_bexp_lneg :
  forall (b : QFBV64.bexp)
         (IH : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
             bit_blast_bexp m g b = (m', g', cs, lr) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bit E lr (QFBV64.eval_bexp b s))
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvLneg b) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvLneg b) s).
Proof.
  move=> e1 IH m g s E m' g' cs lr.
  rewrite /bit_blast_bexp. rewrite -/bit_blast_bexp.
  case Hblast : (bit_blast_bexp m g e1) => [[[m1 g1 ]cs1] r1].
  case Hlneg: (bit_blast_lneg g1 r1) => [[og ocs] olr].
  case => <- _ <- <- Hcon Hcs. rewrite add_prelude_append in Hcs.
  move: Hcs => /andP [Hcs1 Hocs]. rewrite /=.
  apply: (bit_blast_lneg_correct Hlneg _  Hocs).
  exact: (IH _ _ _ _ _ _ _ _ Hblast Hcon Hcs1).
Qed.

Lemma bit_blast_bexp_conj :
  forall (b : QFBV64.bexp)
         (IH : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
             bit_blast_bexp m g b = (m', g', cs, lr) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bit E lr (QFBV64.eval_bexp b s))
         (b0 : QFBV64.bexp)
         (IH0 : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
             bit_blast_bexp m g b0 = (m', g', cs, lr) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bit E lr (QFBV64.eval_bexp b0 s))
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvConj b b0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvConj b b0) s).
Proof.
  move=> e1 IH1 e2 IH2 m g s E m' g' cs lr.
  rewrite /bit_blast_bexp -/bit_blast_bexp.
  case Hblast1: (bit_blast_bexp m g e1) => [[[m1 g1] cs1] r1].
  case Hblast2: (bit_blast_bexp m1 g1 e2) => [[[m2 g2] cs2] r2].
  case Hconj: (bit_blast_conj g2 r1 r2) => [[og ocs] olr].
  case=> <- _ <- <- Hcon Hcs. rewrite !add_prelude_append in Hcs.
  move: Hcs => /andP [Hcs1 /andP [Hcs2 Hocs]]. rewrite /=.
  apply: (bit_blast_conj_correct Hconj _ _ Hocs).
  - move: (vm_preserve_consistent (bit_blast_bexp_preserve Hblast2) Hcon) => Hcon'.
    exact: (IH1 _ _ _ _ _ _ _ _ Hblast1 Hcon' Hcs1).
  - exact: (IH2 _ _ _ _ _ _ _ _ Hblast2 Hcon Hcs2).
Qed.

Lemma bit_blast_bexp_disj :
  forall (b : QFBV64.bexp)
         (IH : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
             bit_blast_bexp m g b = (m', g', cs, lr) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bit E lr (QFBV64.eval_bexp b s))
         (b0 : QFBV64.bexp)
         (IH0 : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
             bit_blast_bexp m g b0 = (m', g', cs, lr) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bit E lr (QFBV64.eval_bexp b0 s))
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvDisj b b0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvDisj b b0) s).
Proof.
  move=> e1 IH1 e2 IH2 m g s E m' g' cs lr.
  rewrite /bit_blast_bexp -/bit_blast_bexp.
  case Hblast1: (bit_blast_bexp m g e1) => [[[m1 g1] cs1] r1].
  case Hblast2: (bit_blast_bexp m1 g1 e2) => [[[m2 g2] cs2] r2].
  case Hdisj: (bit_blast_disj g2 r1 r2) => [[og ocs] olr].
  case=> <- _ <- <- Hcon Hcs. rewrite !add_prelude_append in Hcs.
  move: Hcs => /andP [Hcs1 /andP [Hcs2 Hocs]]. rewrite /=.
  apply: (bit_blast_disj_correct Hdisj _ _ Hocs).
  - move: (vm_preserve_consistent (bit_blast_bexp_preserve Hblast2) Hcon) => Hcon'.
    exact: (IH1 _ _ _ _ _ _ _ _ Hblast1 Hcon' Hcs1).
  - exact: (IH2 _ _ _ _ _ _ _ _ Hblast2 Hcon Hcs2).
Qed.

Corollary bit_blast_exp_correct :
  forall w (e : QFBV64.exp w) m g s E m' g' cs lrs,
    bit_blast_exp m g e = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp e s)
  with
    bit_blast_bexp_correct :
      forall (e : QFBV64.bexp) m g s E m' g' cs lr,
        bit_blast_bexp m g e = (m', g', cs, lr) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bit E lr (QFBV64.eval_bexp e s).
Proof.
  (* bit_blast_exp_correct *)
  move=> w [] {w}.
  - exact: bit_blast_exp_var.
  - exact: bit_blast_exp_const.
  - move=> w e.
    move: (bit_blast_exp_correct _ e) => IH.
    exact: (bit_blast_exp_not IH).
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_exp_and IH1 IH2).
  - move => w e0 e1 .
    move: (bit_blast_exp_correct _ e0) (bit_blast_exp_correct _ e1) => IHe0 IHe1 .
    exact: (bit_blast_exp_or IHe0 IHe1) .
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_exp_xor IH1 IH2).
  - move=> w e.
    move: (bit_blast_exp_correct _ e) => IH.
    exact: (bit_blast_exp_neg IH).
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_exp_add IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_exp_sub IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: bit_blast_exp_mul.
  - exact: bit_blast_exp_mod.
  - exact: bit_blast_exp_srem.
  - exact: bit_blast_exp_smod.
  - move => w0 e0 e1 .
    apply: (bit_blast_exp_shl (bit_blast_exp_correct _ e0)
                              (bit_blast_exp_correct _ e1)) .
  - move => w0 e0 e1 .
    apply: (bit_blast_exp_lshr (bit_blast_exp_correct _ e0)
                               (bit_blast_exp_correct _ e1)) .
  - move => w0 e0 e1 .
    apply: (bit_blast_exp_ashr (bit_blast_exp_correct _ e0)
                               (bit_blast_exp_correct _ e1)) .
  - move => w0 w1 e0 e1 .
    move: (bit_blast_exp_correct _ e0) (bit_blast_exp_correct _ e1)
    => IHe0 IHe1 .
    exact: (bit_blast_exp_concat IHe0 IHe1) .
  - move => w i j e .
    apply: bit_blast_exp_extract (bit_blast_exp_correct _ e) .
  - move => w1 w2 w3 e .
    apply: bit_blast_exp_slice (bit_blast_exp_correct _ e) .
  - move => wh wl e .
    apply: bit_blast_exp_high (bit_blast_exp_correct _ e) .
  - move => wh wl e .
    apply: bit_blast_exp_low (bit_blast_exp_correct _ e) .
  - move=> w n e .
    apply: bit_blast_exp_zeroextend (bit_blast_exp_correct _ e) .
  - move => w n e.
    apply: bit_blast_exp_signextend (bit_blast_exp_correct _ e) .
  - move=> w c e1 e2.
    move: (bit_blast_bexp_correct c) (bit_blast_exp_correct _ e1)
                                     (bit_blast_exp_correct _ e2) => IHc IH1 IH2.
    exact: (bit_blast_exp_ite IHc IH1 IH2).
  (* bit_blast_bexp_correct *)
  move=> [].
  - exact: bit_blast_bexp_false.
  - exact: bit_blast_bexp_true.
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_eq IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_ult IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_ule IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_ugt IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_uge IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_slt IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_sle IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_sgt IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_sge IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_uaddo IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_usubo IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_umulo IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_saddo IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_ssubo IH1 IH2).
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_smulo IH1 IH2).
  - move => e.
    move: (bit_blast_bexp_correct e) => IH.
    exact: (bit_blast_bexp_lneg IH).
  - move=> e1 e2.
    move: (bit_blast_bexp_correct e1) (bit_blast_bexp_correct e2) => IH1 IH2.
    exact: (bit_blast_bexp_conj IH1 IH2).
  - move=> e1 e2.
    move: (bit_blast_bexp_correct e1) (bit_blast_bexp_correct e2) => IH1 IH2.
    exact: (bit_blast_bexp_disj IH1 IH2).
Qed.



(* = mk_env_exp_is_bit_blast_exp and mk_env_bexp_is_bit_blast_bexp = *)

Lemma mk_env_exp_is_bit_blast_exp_var :
  forall (t : VarOrder.t) (m : vm) (E : env) (g : generator)
         (s : QFBV64.State.t) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : wordsize.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvVar t) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvVar t) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  - case; intros; subst; reflexivity.
  - rewrite (mk_env_var_is_bit_blast_var H). reflexivity.
Qed.

Lemma mk_env_exp_is_bit_blast_exp_const :
  forall (w0 : nat) (b : BITS w0) (m : vm) (E : env) (g : generator)
         (s : QFBV64.State.t) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConst w0 b) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvConst w0 b) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst; reflexivity.
Qed.

Lemma mk_env_exp_is_bit_blast_exp_not :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e1 = (m', g', cs, lrs)) ->
    forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvNot w e1) = (m', E', g', cs, lrs) ->
      bit_blast_exp m g (QFBV64.bvNot w e1) = (m', g', cs, lrs).
Proof.
  move=> w e1 IH1 m E g s m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Hmke1).
  by rewrite (mk_env_not_is_bit_blast_not Hmkr).
Qed.

Lemma mk_env_exp_is_bit_blast_exp_and :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e2 = (m', g', cs, lrs)) ->
      forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : w.-tuple literal),
        mk_env_exp m s E g (QFBV64.bvAnd w e1 e2) = (m', E', g', cs, lrs) ->
        bit_blast_exp m g (QFBV64.bvAnd w e1 e2) = (m', g', cs, lrs).
Proof.
  move=> w e1 IH1 e2 IH2 m E g s m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Hmke1) (IH2 _ _ _ _ _ _ _ _ _ Hmke2).
  by rewrite (mk_env_and_is_bit_blast_and Hmkr).
Qed.

Lemma mk_env_exp_is_bit_blast_exp_or :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
    forall (e1 : QFBV64.exp w),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e1 = (m', g', cs, lrs)) ->
    forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvOr w e0 e1) = (m', E', g', cs, lrs) ->
      bit_blast_exp m g (QFBV64.bvOr w e0 e1) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _ _ _ _ H1) (H0 _ _ _ _ _ _ _ _ _ H3) .
  rewrite (mk_env_or_is_bit_blast_or H2). reflexivity.
Qed .

Lemma mk_env_exp_is_bit_blast_exp_xor :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e2 = (m', g', cs, lrs)) ->
      forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : w.-tuple literal),
        mk_env_exp m s E g (QFBV64.bvXor w e1 e2) = (m', E', g', cs, lrs) ->
        bit_blast_exp m g (QFBV64.bvXor w e1 e2) = (m', g', cs, lrs).
Proof.
  move=> w e1 IH1 e2 IH2 m E g s m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Hmke1) (IH2 _ _ _ _ _ _ _ _ _ Hmke2).
  by rewrite (mk_env_xor_is_bit_blast_xor Hmkr).
Qed.

Lemma mk_env_exp_is_bit_blast_exp_neg :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e1 = (m', g', cs, lrs)) ->
    forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNeg w e1) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvNeg w e1) = (m', g', cs, lrs).
Proof.
  move=> w e1 IH1 m E g s m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Hmke1).
  by rewrite (mk_env_neg_is_bit_blast_neg Hmkr).
Qed.

Lemma mk_env_exp_is_bit_blast_exp_add :
  forall (w0 : nat),
  forall (e : QFBV64.exp w0),
    (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w0.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV64.exp w0),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
      forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : w0.-tuple literal),
        mk_env_exp m s E g (QFBV64.bvAdd w0 e e0) = (m', E', g', cs, lrs) ->
        bit_blast_exp m g (QFBV64.bvAdd w0 e e0) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _ _ _ _ H1) (H0 _ _ _ _ _ _ _ _ _ H3) .
  rewrite (mk_env_add_is_bit_blast_add H2). reflexivity.
Qed.

Lemma mk_env_exp_is_bit_blast_exp_sub :
  forall (w0 : nat),
  forall (e : QFBV64.exp w0),
    (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w0.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV64.exp w0),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
      forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSub w0 e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvSub w0 e e0) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _ _ _ _ H1) (H0 _ _ _ _ _ _ _ _ _ H3) .
  rewrite (mk_env_sub_is_bit_blast_sub H2). reflexivity.
Qed.

Lemma mk_env_exp_is_bit_blast_exp_mul :
  forall (w0 : nat),
  forall (e : QFBV64.exp w0),
    (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w0.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV64.exp w0),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
      forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMul w0 e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvMul w0 e e0) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _ _ _ _ H1) (H0 _ _ _ _ _ _ _ _ _ H3) (mk_env_mul_is_bit_blast_mul H2).
  done.
Qed.

Lemma mk_env_exp_is_bit_blast_exp_mod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMod w0 e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvMod w0 e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_srem :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSrem w0 e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvSrem w0 e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_smod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSmod w0 e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvSmod w0 e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_shl :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
    forall (e1 : QFBV64.exp w),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e1 = (m', g', cs, lrs)) ->
    forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvShl w e0 e1) = (m', E', g', cs, lrs) ->
      bit_blast_exp m g (QFBV64.bvShl w e0 e1) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _ _ _ _ H1) (H0 _ _ _ _ _ _ _ _ _ H3) .
  by rewrite (mk_env_shl_is_bit_blast_shl H2).
Qed .

Lemma mk_env_exp_is_bit_blast_exp_lshr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
    forall (e1 : QFBV64.exp w),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e1 = (m', g', cs, lrs)) ->
    forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvLshr w e0 e1) = (m', E', g', cs, lrs) ->
      bit_blast_exp m g (QFBV64.bvLshr w e0 e1) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _ _ _ _ H1) (H0 _ _ _ _ _ _ _ _ _ H3) .
  by rewrite (mk_env_lshr_is_bit_blast_lshr H2).
Qed .

Lemma mk_env_exp_is_bit_blast_exp_ashr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w.+1),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
    forall (e1 : QFBV64.exp w.+1),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e1 = (m', g', cs, lrs)) ->
    forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w.+1).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvAshr w e0 e1) = (m', E', g', cs, lrs) ->
      bit_blast_exp m g (QFBV64.bvAshr w e0 e1) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _ _ _ _ H1) (H0 _ _ _ _ _ _ _ _ _ H3) .
  by rewrite (mk_env_ashr_is_bit_blast_ashr H2).
Qed .

Lemma mk_env_exp_is_bit_blast_exp_concat :
  forall (w0 w1 : nat),
    forall (e0 : QFBV64.exp w0),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
    forall (e1 : QFBV64.exp w1),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w1.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e1 = (m', g', cs, lrs)) ->
    forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : (w1 + w0).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConcat w0 w1 e0 e1) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvConcat w0 w1 e0 e1) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  by rewrite (H _ _ _ _ _ _ _ _ _ H1) (H0 _ _ _ _ _ _ _ _ _ H3) .
Qed .

Lemma mk_env_exp_is_bit_blast_exp_extract :
  forall (w i j : nat),
    forall (e : QFBV64.exp (j + (i - j + 1) + w)),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (j + (i - j + 1) + w).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : (i - j + 1).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvExtract w i j e) = (m', E', g', cs, lrs) ->
      bit_blast_exp m g (QFBV64.bvExtract w i j e) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
    by rewrite (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_is_bit_blast_exp_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV64.exp (w3 + w2 + w1)),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      bit_blast_exp m g (QFBV64.bvSlice w1 w2 w3 e) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
    by rewrite (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_is_bit_blast_exp_high :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (wl + wh).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (m : vm)
         (E : env) (g : generator) (s : QFBV64.State.t) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvHigh wh wl e) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvHigh wh wl e) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
    by rewrite (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_is_bit_blast_exp_low :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (wl + wh).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : wl.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvLow wh wl e) = (m', E', g', cs, lrs) ->
      bit_blast_exp m g (QFBV64.bvLow wh wl e) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
    by rewrite (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_is_bit_blast_exp_zeroextend :
  forall (w n : nat),
    forall (e : QFBV64.exp w),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e = (m', g', cs, lrs)) ->
      forall (m : vm) (E : env)
             (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
             (g' : generator) (cs : cnf) (lrs : (w + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvZeroExtend w n e) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvZeroExtend w n e) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
    by rewrite (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_is_bit_blast_exp_signextend :
  forall (w n : nat),
    forall (e : QFBV64.exp w.+1),
      (forall (m  : vm) (E  : env) (g  : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : (w.+1 + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSignExtend w n e) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvSignExtend w n e) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst .
  by rewrite (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_is_bit_blast_exp_ite :
  forall (w : nat) (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        bit_blast_bexp m g b = (m', g', cs, lr)) ->
  forall (e : QFBV64.exp w),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV64.exp w),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
    forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvIte w b e e0) = (m', E', g', cs, lrs) ->
      bit_blast_exp m g (QFBV64.bvIte w b e e0) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _ _ _ _ H2) (H0 _ _ _ _ _ _ _ _ _ H4) (H1 _ _ _ _ _ _ _ _ _ H3).
  rewrite (mk_env_ite_is_bit_blast_ite H5). reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) ->
    bit_blast_bexp m g QFBV64.bvFalse = (m', g', cs, lr).
Proof.
  rewrite /=; intros; dcase_hyps; subst; reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) ->
    bit_blast_bexp m g QFBV64.bvTrue = (m', g', cs, lr).
Proof.
  rewrite /=; intros; dcase_hyps; subst; reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_eq :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvEq w e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvEq w e e0) = (m', g', cs, lr).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _ _ _ _ H1). rewrite (H0 _ _ _ _ _ _ _ _ _ H3).
  rewrite (mk_env_eq_is_bit_blast_eq H2). reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_ult :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUlt w e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvUlt w e e0) = (m', g', cs, lr).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _ _ _ _ H1). rewrite (H0 _ _ _ _ _ _ _ _ _ H3).
  rewrite (mk_env_ult_is_bit_blast_ult H2). reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_ule :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUle w e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvUle w e e0) = (m', g', cs, lr).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _ _ _ _ H1). rewrite (H0 _ _ _ _ _ _ _ _ _ H3).
  rewrite (mk_env_ule_is_bit_blast_ule H2). reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_ugt :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUgt w e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvUgt w e e0) = (m', g', cs, lr).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _ _ _ _ H1). rewrite (H0 _ _ _ _ _ _ _ _ _ H3).
  rewrite (mk_env_ugt_is_bit_blast_ugt H2). reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_uge :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUge w e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvUge w e e0) = (m', g', cs, lr).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _ _ _ _ H1). rewrite (H0 _ _ _ _ _ _ _ _ _ H3).
  rewrite (mk_env_uge_is_bit_blast_uge H2). reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_slt :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e2 = (m', g', cs, lrs)) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSlt w e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvSlt w e1 e2) = (m', g', cs, lr).
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- _ <- <- <-.
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Hmke1) (IH2 _ _ _ _ _ _ _ _ _ Hmke2).
  by rewrite (mk_env_slt_is_bit_blast_slt Hmkr).
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_sle :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e2 = (m', g', cs, lrs)) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSle w e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvSle w e1 e2) = (m', g', cs, lr).
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- _ <- <- <-.
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Hmke1) (IH2 _ _ _ _ _ _ _ _ _ Hmke2).
  by rewrite (mk_env_sle_is_bit_blast_sle Hmkr).
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_sgt :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e2 = (m', g', cs, lrs)) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSgt w e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvSgt w e1 e2) = (m', g', cs, lr).
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- _ <- <- <-.
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Hmke1) (IH2 _ _ _ _ _ _ _ _ _ Hmke2).
  by rewrite (mk_env_sgt_is_bit_blast_sgt Hmkr).
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_sge :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e2 = (m', g', cs, lrs)) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSge w e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvSge w e1 e2) = (m', g', cs, lr).
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- _ <- <- <-.
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Hmke1) (IH2 _ _ _ _ _ _ _ _ _ Hmke2).
  by rewrite (mk_env_sge_is_bit_blast_sge Hmkr).
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_uaddo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUaddo w e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvUaddo w e e0) = (m', g', cs, lr).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _ _ _ _ H1). rewrite (H0 _ _ _ _ _ _ _ _ _ H3).
  rewrite (mk_env_uaddo_is_bit_blast_uaddo H2). reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_usubo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUsubo w e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvUsubo w e e0) = (m', g', cs, lr).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _ _ _ _ H1). rewrite (H0 _ _ _ _ _ _ _ _ _ H3).
  rewrite (mk_env_usubo_is_bit_blast_usubo H2). reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_umulo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUmulo w e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvUmulo w e e0) = (m', g', cs, lr).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _ _ _ _ H1). rewrite (H0 _ _ _ _ _ _ _ _ _ H3).
  rewrite (mk_env_umulo_is_bit_blast_umulo H2). reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_saddo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e2 = (m', g', cs, lrs)) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSaddo w e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvSaddo w e1 e2) = (m', g', cs, lr).
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- _ <- <- <-.
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Hmke1) (IH2 _ _ _ _ _ _ _ _ _ Hmke2).
  by rewrite (mk_env_saddo_is_bit_blast_saddo Hmkr).
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_ssubo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e2 = (m', g', cs, lrs)) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSsubo w e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvSsubo w e1 e2) = (m', g', cs, lr).
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- _ <- <- <-.
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Hmke1) (IH2 _ _ _ _ _ _ _ _ _ Hmke2).
  by rewrite (mk_env_ssubo_is_bit_blast_ssubo Hmkr).
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_smulo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e2 = (m', g', cs, lrs)) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSmulo w e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvSmulo w e1 e2) = (m', g', cs, lr).
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- _ <- <- <-.
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Hmke1) (IH2 _ _ _ _ _ _ _ _ _ Hmke2).
  by rewrite (mk_env_smulo_is_bit_blast_smulo Hmkr).
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_lneg :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        bit_blast_bexp m g b = (m', g', cs, lr)) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvLneg b) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvLneg b) = (m', g', cs, lr).
Proof.
 rewrite /=. intros. dcase_hyps. subst.
 rewrite (H _ _ _ _ _ _ _ _ _ H0). done.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_conj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        bit_blast_bexp m g b = (m', g', cs, lr)) ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          bit_blast_bexp m g b0 = (m', g', cs, lr)) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvConj b b0) = (m', g', cs, lr).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _  _ _ _ H1). rewrite (H0 _ _ _ _ _ _  _ _ _ H3). reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_disj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        bit_blast_bexp m g b = (m', g', cs, lr)) ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          bit_blast_bexp m g b0 = (m', g', cs, lr)) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvDisj b b0) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvDisj b b0) = (m', g', cs, lr).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _  _ _ _ H1). rewrite (H0 _ _ _ _ _ _  _ _ _ H3). reflexivity.
Qed.

Corollary mk_env_exp_is_bit_blast_exp :
  forall w (e : QFBV64.exp w) m E g s m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    bit_blast_exp m g e = (m', g', cs, lrs)
  with
    mk_env_bexp_is_bit_blast_bexp :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        bit_blast_bexp m g e = (m', g', cs, lr).
Proof.
  (* mk_env_exp_is_bit_blast_exp *)
  move=> w [] {w}.
  - exact: mk_env_exp_is_bit_blast_exp_var.
  - exact: mk_env_exp_is_bit_blast_exp_const.
  - move=> w e.
    move: (mk_env_exp_is_bit_blast_exp _ e) => IH.
    exact: (mk_env_exp_is_bit_blast_exp_not IH).
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1)
          (mk_env_exp_is_bit_blast_exp _ e2) => IH1 IH2.
    exact: (mk_env_exp_is_bit_blast_exp_and IH1 IH2).
  - move => w e0 e1 .
    move: (mk_env_exp_is_bit_blast_exp _ e0)
            (mk_env_exp_is_bit_blast_exp _ e1) => IHe0 IHe1 .
    exact: (mk_env_exp_is_bit_blast_exp_or IHe0 IHe1) .
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1)
          (mk_env_exp_is_bit_blast_exp _ e2) => IH1 IH2.
    exact: (mk_env_exp_is_bit_blast_exp_xor IH1 IH2).
  - move=> w e.
    move: (mk_env_exp_is_bit_blast_exp _ e) => IH.
    exact: (mk_env_exp_is_bit_blast_exp_neg IH).
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1) (mk_env_exp_is_bit_blast_exp _ e2) => IH1 IH2.
    exact: (mk_env_exp_is_bit_blast_exp_add IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1) (mk_env_exp_is_bit_blast_exp _ e2) => IH1 IH2.
    exact: (mk_env_exp_is_bit_blast_exp_sub IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1) (mk_env_exp_is_bit_blast_exp _ e2) => IH1 IH2.
    exact: mk_env_exp_is_bit_blast_exp_mul.
  - exact: mk_env_exp_is_bit_blast_exp_mod.
  - exact: mk_env_exp_is_bit_blast_exp_srem.
  - exact: mk_env_exp_is_bit_blast_exp_smod.
  - move => w e0 e1 .
    apply: (mk_env_exp_is_bit_blast_exp_shl
              (mk_env_exp_is_bit_blast_exp _ e0)
              (mk_env_exp_is_bit_blast_exp _ e1)) .
  - move => w e0 e1 .
    apply: (mk_env_exp_is_bit_blast_exp_lshr
              (mk_env_exp_is_bit_blast_exp _ e0)
              (mk_env_exp_is_bit_blast_exp _ e1)) .
  - move => w e0 e1 .
    apply: (mk_env_exp_is_bit_blast_exp_ashr
              (mk_env_exp_is_bit_blast_exp _ e0)
              (mk_env_exp_is_bit_blast_exp _ e1)) .
  - move => w0 w1 e0 e1 .
    move: (mk_env_exp_is_bit_blast_exp _ e0)
            (mk_env_exp_is_bit_blast_exp _ e1) => IHe0 IHe1 .
    exact: (mk_env_exp_is_bit_blast_exp_concat IHe0 IHe1) .
  - move => w i j e .
    apply: mk_env_exp_is_bit_blast_exp_extract
             (mk_env_exp_is_bit_blast_exp _ e) .
  - move => w1 w2 w3 e .
    apply: mk_env_exp_is_bit_blast_exp_slice
             (mk_env_exp_is_bit_blast_exp _ e) .
  - move => wh wl e .
    apply: mk_env_exp_is_bit_blast_exp_high
             (mk_env_exp_is_bit_blast_exp _ e) .
  - move => wh wl e .
    apply: mk_env_exp_is_bit_blast_exp_low
             (mk_env_exp_is_bit_blast_exp _ e) .
  - move => w n e .
    apply: mk_env_exp_is_bit_blast_exp_zeroextend
             (mk_env_exp_is_bit_blast_exp _ e) .
  - move => w n e .
    apply: mk_env_exp_is_bit_blast_exp_signextend
             (mk_env_exp_is_bit_blast_exp _ e) .
  - move=> w c e1 e2.
    move: (mk_env_bexp_is_bit_blast_bexp c)
            (mk_env_exp_is_bit_blast_exp _ e1)
            (mk_env_exp_is_bit_blast_exp _ e2) => IHc IH1 IH2.
    exact: (mk_env_exp_is_bit_blast_exp_ite IHc IH1 IH2).
  (* mk_env_bexp_is_bit_blast_bexp *)
  case.
  - exact: mk_env_bexp_is_bit_blast_bexp_false.
  - exact: mk_env_bexp_is_bit_blast_bexp_true.
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1) (mk_env_exp_is_bit_blast_exp _ e2)
    => IH1 IH2. exact: (mk_env_bexp_is_bit_blast_bexp_eq IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1) (mk_env_exp_is_bit_blast_exp _ e2)
    => IH1 IH2. exact: (mk_env_bexp_is_bit_blast_bexp_ult IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1) (mk_env_exp_is_bit_blast_exp _ e2)
    => IH1 IH2. exact: (mk_env_bexp_is_bit_blast_bexp_ule IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1) (mk_env_exp_is_bit_blast_exp _ e2)
    => IH1 IH2. exact: (mk_env_bexp_is_bit_blast_bexp_ugt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1) (mk_env_exp_is_bit_blast_exp _ e2)
    => IH1 IH2. exact: (mk_env_bexp_is_bit_blast_bexp_uge IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1)
          (mk_env_exp_is_bit_blast_exp _ e2) => IH1 IH2.
    exact: (mk_env_bexp_is_bit_blast_bexp_slt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1)
          (mk_env_exp_is_bit_blast_exp _ e2) => IH1 IH2.
    exact: (mk_env_bexp_is_bit_blast_bexp_sle IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1)
          (mk_env_exp_is_bit_blast_exp _ e2) => IH1 IH2.
    exact: (mk_env_bexp_is_bit_blast_bexp_sgt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1)
          (mk_env_exp_is_bit_blast_exp _ e2) => IH1 IH2.
    exact: (mk_env_bexp_is_bit_blast_bexp_sge IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1) (mk_env_exp_is_bit_blast_exp _ e2)
    => IH1 IH2. exact: (mk_env_bexp_is_bit_blast_bexp_uaddo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1) (mk_env_exp_is_bit_blast_exp _ e2)
    => IH1 IH2. exact: (mk_env_bexp_is_bit_blast_bexp_usubo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1) (mk_env_exp_is_bit_blast_exp _ e2)
    => IH1 IH2. exact: (mk_env_bexp_is_bit_blast_bexp_umulo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1) (mk_env_exp_is_bit_blast_exp _ e2)
    => IH1 IH2. exact: (mk_env_bexp_is_bit_blast_bexp_saddo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1) (mk_env_exp_is_bit_blast_exp _ e2)
    => IH1 IH2. exact: (mk_env_bexp_is_bit_blast_bexp_ssubo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1) (mk_env_exp_is_bit_blast_exp _ e2)
    => IH1 IH2. exact: (mk_env_bexp_is_bit_blast_bexp_smulo IH1 IH2).
  - move => e.
    move: (mk_env_bexp_is_bit_blast_bexp e) => IH.
    exact: (mk_env_bexp_is_bit_blast_bexp_lneg IH).
  - move=> e1 e2.
    move: (mk_env_bexp_is_bit_blast_bexp e1) (mk_env_bexp_is_bit_blast_bexp e2) =>
    IH1 IH2. exact: (mk_env_bexp_is_bit_blast_bexp_conj IH1 IH2).
  - move=> e1 e2.
    move: (mk_env_bexp_is_bit_blast_bexp e1) (mk_env_bexp_is_bit_blast_bexp e2) =>
    IH1 IH2.
    exact: (mk_env_bexp_is_bit_blast_bexp_disj IH1 IH2).
Qed.



(* = mk_env_exp_newer_gen and mk_env_bexp_newer_gen = *)

Lemma mk_env_exp_newer_gen_var :
  forall (t : VarOrder.t) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : wordsize.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvVar t) = (m', E', g', cs, lrs) -> (g <=? g')%positive.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case: (VM.find v m).
  - move=> ls [] _ _ <- _ _. exact: Pos.leb_refl.
  - case Henv: (mk_env_var E g (QFBV64.State.acc v s) v) => [[[oE og] ocs] olrs].
    case=> _ _ <- _ _. exact: (mk_env_var_newer_gen Henv).
Qed.

Lemma mk_env_exp_newer_gen_const :
  forall (w0 : nat) (b : BITS w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConst w0 b) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> w bs m s E g m' E' g' cs lrs /=. case=> _ _ <- _ _. exact: Pos.leb_refl.
Qed.

Lemma mk_env_exp_newer_gen_not :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvNot w e1) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> w e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (mk_env_not_newer_gen Hmkr) => Hg1gr.
  apply: (pos_leb_trans Hg0g1). done.
Qed.

Lemma mk_env_exp_newer_gen_and :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : w.-tuple literal),
        mk_env_exp m s E g (QFBV64.bvAnd w e1 e2) = (m', E', g', cs, lrs) ->
        (g <=? g')%positive.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_and_newer_gen Hmkr) => Hg2gr.
  apply: (pos_leb_trans Hg0g1). apply (pos_leb_trans Hg1g2). done.
Qed.

Lemma mk_env_exp_newer_gen_or :
  forall (w : nat),
    forall (e0: QFBV64.exp w),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1: QFBV64.exp w),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvOr w e0 e1) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_or_newer_gen H2) => Hg2g'.
  move: (H0 _ _ _ _ _ _ _ _ _ H3) => Hg1g2.
  move: (H  _ _ _ _ _ _ _ _ _ H1) => Hg0g1 .
  apply: (pos_leb_trans _ Hg2g'). by [ apply: (pos_leb_trans _ Hg1g2)] .
Qed .

Lemma mk_env_exp_newer_gen_xor :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : w.-tuple literal),
        mk_env_exp m s E g (QFBV64.bvXor w e1 e2) = (m', E', g', cs, lrs) ->
        (g <=? g')%positive.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_xor_newer_gen Hmkr) => Hg2gr.
  apply: (pos_leb_trans Hg0g1). apply (pos_leb_trans Hg1g2). done.
Qed.

Lemma mk_env_exp_newer_gen_neg :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNeg w e1) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> w e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (mk_env_neg_newer_gen Hmkr) => Hg1gr.
  apply: (pos_leb_trans Hg0g1). done.
Qed.

Lemma mk_env_exp_newer_gen_add :
  forall (w : nat),
    forall (e0: QFBV64.exp w),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1: QFBV64.exp w),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAdd w e0 e1) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_add_newer_gen H2) => Hg1g'.
  move: (H0 _ _ _ _ _ _ _ _ _ H3) => Hgg'.
  move: (H  _ _ _ _ _ _ _ _ _ H1) => Hgg0.
  apply: (pos_leb_trans _ Hg1g'). by [ apply: (pos_leb_trans _ Hgg')] .
Qed.

Lemma mk_env_exp_newer_gen_sub :
  forall (w : nat),
    forall (e0: QFBV64.exp w),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1: QFBV64.exp w),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSub w e0 e1) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_sub_newer_gen H2) => Hg1g'.
  move: (H0 _ _ _ _ _ _ _ _ _ H3) => Hgg'.
  move: (H  _ _ _ _ _ _ _ _ _ H1) => Hgg0.
  apply: (pos_leb_trans _ Hg1g'). by [ apply: (pos_leb_trans _ Hgg')].
Qed.

Lemma mk_env_exp_newer_gen_mul :
  forall (w0 : nat),
    forall (e: QFBV64.exp w0),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0: QFBV64.exp w0),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMul w0 e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_mul_newer_gen H2) => Hg1g'.
  move: (H0 _ _ _ _ _ _ _ _ _ H3) => Hg0g1.
  move: (H  _ _ _ _ _ _ _ _ _ H1) => Hgg0.
  apply: (pos_leb_trans _ Hg1g'). by [ apply: (pos_leb_trans _ Hg0g1)] .
Qed.

Lemma mk_env_exp_newer_gen_mod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMod w0 e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_srem :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSrem w0 e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_smod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSmod w0 e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_shl :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1 : QFBV64.exp w),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvShl w e0 e1) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_shl_newer_gen H2) => Hg2g'.
  move: (H0 _ _ _ _ _ _ _ _ _ H3) => Hg1g2.
  move: (H  _ _ _ _ _ _ _ _ _ H1) => Hg0g1 .
  apply: (pos_leb_trans _ Hg2g'). by [ apply: (pos_leb_trans _ Hg1g2)] .
Qed .

Lemma mk_env_exp_newer_gen_lshr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1 : QFBV64.exp w),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvLshr w e0 e1) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_lshr_newer_gen H2) => Hg2g'.
  move: (H0 _ _ _ _ _ _ _ _ _ H3) => Hg1g2.
  move: (H  _ _ _ _ _ _ _ _ _ H1) => Hg0g1 .
  apply: (pos_leb_trans _ Hg2g'). by [ apply: (pos_leb_trans _ Hg1g2)] .
Qed .

Lemma mk_env_exp_newer_gen_ashr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w.+1),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1 : QFBV64.exp w.+1),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w.+1).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvAshr w e0 e1) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_ashr_newer_gen H2) => Hg2g'.
  move: (H0 _ _ _ _ _ _ _ _ _ H3) => Hg1g2.
  move: (H  _ _ _ _ _ _ _ _ _ H1) => Hg0g1 .
  apply: (pos_leb_trans _ Hg2g'). by [ apply: (pos_leb_trans _ Hg1g2)] .
Qed .

Lemma mk_env_exp_newer_gen_concat :
  forall (w0 w1 : nat),
    forall (e0: QFBV64.exp w0),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1: QFBV64.exp w1),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w1.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : (w1 + w0).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvConcat w0 w1 e0 e1) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (H0 _ _ _ _ _ _ _ _ _ H3) => Hg0g'.
  move: (H  _ _ _ _ _ _ _ _ _ H1) => Hgg0 .
  by apply: (pos_leb_trans _ Hg0g').
Qed .

Lemma mk_env_exp_newer_gen_extract :
  forall (w i j : nat),
    forall (e : QFBV64.exp (j + (i - j + 1) + w)),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (j + (i - j + 1) + w).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : (i - j + 1).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvExtract w i j e) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_newer_gen_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV64.exp (w3 + w2 + w1)),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_newer_gen_high :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (wl + wh).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm)
           (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
           (E' : env) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvHigh wh wl e) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_newer_gen_low :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (wl + wh).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : wl.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvLow wh wl e) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_newer_gen_zeroextend :
  forall (w n : nat),
    forall (e: QFBV64.exp w),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : QFBV64.State.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvZeroExtend w n e) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_newer_gen_signextend :
  forall (w n : nat),
    forall (e: QFBV64.exp w.+1),
      (forall (m  : vm) (s  : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : QFBV64.State.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w.+1 + n).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSignExtend w n e) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_newer_gen_ite :
  forall (w : nat) (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
    forall (e : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (e0 : QFBV64.exp w),
        (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : w.-tuple literal),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
        forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g (QFBV64.bvIte w b e e0) = (m', E', g', cs, lrs) ->
          (g <=? g')%positive.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_ite_newer_gen H5) => Hg2g'. move: (H1 _ _ _ _ _ _ _ _ _ H3) => Hg1g2.
  move: (H0 _ _ _ _ _ _ _ _ _ H4) => Hg0g1. move: (H _ _ _ _ _ _ _ _ _ H2) => Hgg0.
  apply: (pos_leb_trans _ Hg2g'). apply: (pos_leb_trans _ Hg1g2).
  apply: (pos_leb_trans _ Hg0g1). exact: Hgg0.
Qed.

Lemma mk_env_bexp_newer_gen_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) -> (g <=? g')%positive.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- _ _. exact: Pos.leb_refl.
Qed.

Lemma mk_env_bexp_newer_gen_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) -> (g <=? g')%positive.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- _ _. exact: Pos.leb_refl.
Qed.

Lemma mk_env_bexp_newer_gen_eq :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvEq w e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- _ _. apply: (pos_leb_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (pos_leb_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  exact: (mk_env_eq_newer_gen Heq).
Qed.

Lemma mk_env_bexp_newer_gen_ult :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUlt w e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hult: (mk_env_ult E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- _ _. apply: (pos_leb_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (pos_leb_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  exact: (mk_env_ult_newer_gen Hult).
Qed.


Lemma mk_env_bexp_newer_gen_ule :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUle w e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hule: (mk_env_ule E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- _ _. apply: (pos_leb_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (pos_leb_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  exact: (mk_env_ule_newer_gen Hule).
Qed.

Lemma mk_env_bexp_newer_gen_ugt :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUgt w e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hugt: (mk_env_ugt E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- _ _. apply: (pos_leb_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (pos_leb_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  exact: (mk_env_ugt_newer_gen Hugt).
Qed.


Lemma mk_env_bexp_newer_gen_uge :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUge w e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Huge: (mk_env_uge E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- _ _. apply: (pos_leb_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (pos_leb_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  exact: (mk_env_uge_newer_gen Huge).
Qed.

Lemma mk_env_bexp_newer_gen_slt :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSlt w e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_slt_newer_gen Hmkr) => Hg2gr.
  apply: (pos_leb_trans Hg0g1). apply (pos_leb_trans Hg1g2). done.
Qed.

Lemma mk_env_bexp_newer_gen_sle :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSle w e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_sle_newer_gen Hmkr) => Hg2gr.
  apply: (pos_leb_trans Hg0g1). apply (pos_leb_trans Hg1g2). done.
Qed.

Lemma mk_env_bexp_newer_gen_sgt :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSgt w e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_sgt_newer_gen Hmkr) => Hg2gr.
  apply: (pos_leb_trans Hg0g1). apply (pos_leb_trans Hg1g2). done.
Qed.

Lemma mk_env_bexp_newer_gen_sge :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSge w e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_sge_newer_gen Hmkr) => Hg2gr.
  apply: (pos_leb_trans Hg0g1). apply (pos_leb_trans Hg1g2). done.
Qed.

Lemma mk_env_bexp_newer_gen_uaddo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUaddo w e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Huaddo: (mk_env_uaddo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- _ _. apply: (pos_leb_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (pos_leb_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  exact: (mk_env_uaddo_newer_gen Huaddo).
Qed.

Lemma mk_env_bexp_newer_gen_usubo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUsubo w e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Husubo: (mk_env_usubo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- _ _. apply: (pos_leb_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (pos_leb_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  exact: (mk_env_usubo_newer_gen Husubo).
Qed.

Lemma mk_env_bexp_newer_gen_umulo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUmulo w e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Humulo: (mk_env_umulo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- _ _. apply: (pos_leb_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (pos_leb_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  exact: (mk_env_umulo_newer_gen Humulo).
Qed.

Lemma mk_env_bexp_newer_gen_saddo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSaddo w e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_saddo_newer_gen Hmkr) => Hg2gr.
  apply: (pos_leb_trans Hg0g1). apply (pos_leb_trans Hg1g2). done.
Qed.

Lemma mk_env_bexp_newer_gen_ssubo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSsubo w e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_ssubo_newer_gen Hmkr) => Hg2gr.
  apply: (pos_leb_trans Hg0g1). apply (pos_leb_trans Hg1g2). done.
Qed.

Lemma mk_env_bexp_newer_gen_smulo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSmulo w e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_smulo_newer_gen Hmkr) => Hg2gr.
  apply: (pos_leb_trans Hg0g1). apply (pos_leb_trans Hg1g2). done.
Qed.

Lemma mk_env_bexp_newer_gen_lneg :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvLneg b) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move => e IH m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv: (mk_env_bexp m s E g e) => [[[[m1 E1] g1] cs1] lr1].
  case Hlneg: (mk_env_lneg E1 g1 lr1) => [[[oE og] ocs] olr].
  case. move => _ _ <- _ _.
  apply: (pos_leb_trans (IH _ _ _ _ _ _ _ _ _ Henv)).
  exact: (mk_env_lneg_newer_gen Hlneg).
Qed.

Lemma mk_env_bexp_newer_gen_conj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case Hconj: (mk_env_conj E2 g2 lr1 lr2)=> [[[oE og] ocs] olr].
  case=> _ _ <- _ _. apply: (pos_leb_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (pos_leb_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  exact: (mk_env_conj_newer_gen Hconj).
Qed.

Lemma mk_env_bexp_newer_gen_disj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvDisj b b0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case Hdisj: (mk_env_disj E2 g2 lr1 lr2)=> [[[oE og] ocs] olr].
  case=> _ _ <- _ _. apply: (pos_leb_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (pos_leb_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  exact: (mk_env_disj_newer_gen Hdisj).
Qed.

Corollary mk_env_exp_newer_gen :
  forall w (e : QFBV64.exp w) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    (g <=? g')%positive
  with
    mk_env_bexp_newer_gen :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  (* mk_env_exp_newer_gen *)
  move=> w [] {w}.
  - exact: mk_env_exp_newer_gen_var.
  - exact: mk_env_exp_newer_gen_const.
  - move=> w e.
    move: (mk_env_exp_newer_gen _ e) => IH.
    exact: (mk_env_exp_newer_gen_not IH).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IH1 IH2.
    exact: (mk_env_exp_newer_gen_and IH1 IH2).
  - move => w e0 e1 .
    move: (mk_env_exp_newer_gen _ e0) (mk_env_exp_newer_gen _ e1) => IHe0 IHe1 .
    exact: (mk_env_exp_newer_gen_or IHe0 IHe1) .
  - move=> w e1 e2.
    move: (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IH1 IH2.
    exact: (mk_env_exp_newer_gen_xor IH1 IH2).
  - move=> w e.
    move: (mk_env_exp_newer_gen _ e) => IH.
    exact: (mk_env_exp_newer_gen_neg IH).
  - move => w e e0 .
    move: (mk_env_exp_newer_gen _ e) (mk_env_exp_newer_gen _ e0) => IHe IHe0.
    exact: mk_env_exp_newer_gen_add.
  - move => w e e0 .
    move: (mk_env_exp_newer_gen _ e) (mk_env_exp_newer_gen _ e0) => IHe IHe0.
    exact: (mk_env_exp_newer_gen_sub IHe IHe0).
  - move => w e e0 .
    move: (mk_env_exp_newer_gen _ e) (mk_env_exp_newer_gen _ e0) => IHe IHe0.
    exact: mk_env_exp_newer_gen_mul.
  - exact: mk_env_exp_newer_gen_mod.
  - exact: mk_env_exp_newer_gen_srem.
  - exact: mk_env_exp_newer_gen_smod.
  - move => w e0 e1 .
    exact: (mk_env_exp_newer_gen_shl
              (mk_env_exp_newer_gen _ e0) (mk_env_exp_newer_gen _ e1)) .
  - move => w e0 e1 .
    exact: (mk_env_exp_newer_gen_lshr
              (mk_env_exp_newer_gen _ e0) (mk_env_exp_newer_gen _ e1)) .
  - move => w e0 e1 .
    exact: (mk_env_exp_newer_gen_ashr
              (mk_env_exp_newer_gen _ e0) (mk_env_exp_newer_gen _ e1)) .
  - move => w0 w1 e0 e1 .
    move: (mk_env_exp_newer_gen _ e0) (mk_env_exp_newer_gen _ e1)
    => IHe0 IHe1 .
    apply (mk_env_exp_newer_gen_concat IHe0 IHe1) .
  - move => w i j e .
    apply: mk_env_exp_newer_gen_extract (mk_env_exp_newer_gen _ e) .
  - move => w1 w2 w3 e .
    apply: mk_env_exp_newer_gen_slice (mk_env_exp_newer_gen _ e) .
  - move => wh wl e .
    apply: mk_env_exp_newer_gen_high (mk_env_exp_newer_gen _ e) .
  - move => wh wl e .
    apply: mk_env_exp_newer_gen_low (mk_env_exp_newer_gen _ e) .
  - move=> w n e .
    apply: mk_env_exp_newer_gen_zeroextend
             (mk_env_exp_newer_gen _ e) .
  - move => w n e .
    apply: mk_env_exp_newer_gen_signextend (mk_env_exp_newer_gen _ e) .
  - move=> w c e1 e2.
    move: (mk_env_bexp_newer_gen c)
            (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IHc IH1 IH2.
    exact: (mk_env_exp_newer_gen_ite IHc IH1 IH2).
  (* mk_env_bexp_newer_gen *)
  case.
  - exact: mk_env_bexp_newer_gen_false.
  - exact: mk_env_bexp_newer_gen_true.
  - move=> w e1 e2.
    move: (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_eq IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_ult IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_ule IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_ugt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_uge IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_slt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_sle IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_sgt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_sge IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_uaddo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_usubo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_umulo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_saddo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_ssubo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_smulo IH1 IH2).
  - move => e.
    move: (mk_env_bexp_newer_gen e) => IH.
    exact: (mk_env_bexp_newer_gen_lneg IH).
  - move=> e1 e2.
    move: (mk_env_bexp_newer_gen e1) (mk_env_bexp_newer_gen e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_conj IH1 IH2).
  - move=> e1 e2.
    move: (mk_env_bexp_newer_gen e1) (mk_env_bexp_newer_gen e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_disj IH1 IH2).
Qed.



(* = mk_env_exp_newer_vm and mk_env_bexp_newer_vm = *)

Lemma mk_env_exp_newer_vm_var :
  forall (t : VarOrder.t) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : wordsize.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvVar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case Hfind: (VM.find v m).
  - case=> <- _ <- _ _ Hnew_gm. exact: Hnew_gm.
  - case Henv: (mk_env_var E g (QFBV64.State.acc v s) v) => [[[oE og] ocs] olrs].
    case=> <- _ <- _ _ Hnew_gm. move=> x lxs. case Hxv: (x == v).
    + rewrite (VM.Lemmas.find_add_eq m olrs Hxv). case=> <-.
      exact: (mk_env_var_newer_res Henv).
    + move/negP: Hxv => Hxv. rewrite (VM.Lemmas.find_add_neq m olrs Hxv) => Hfindx.
      move: (Hnew_gm x lxs Hfindx) => Hnew_og.
      apply: (newer_than_lits_le_newer Hnew_og). exact: (mk_env_var_newer_gen Henv).
Qed.

Lemma mk_env_exp_newer_vm_const :
  forall (w0 : nat) (b : BITS w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConst w0 b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w b m s E g m' E' g' cs lrs. case=> <- _ <- _ _. by apply.
Qed.

Lemma mk_env_exp_newer_vm_not :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvNot w e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (mk_env_not_newer_gen Hmkr) => Hg1gr.
  exact: (newer_than_vm_le_newer Hg1m1 Hg1gr).
Qed.

Lemma mk_env_exp_newer_vm_and :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : w.-tuple literal),
        mk_env_exp m s E g (QFBV64.bvAnd w e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_and_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_exp_newer_vm_or :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvOr w e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  rewrite /=; intros; dcase_hyps; subst. move: (mk_env_or_newer_gen H3) => Hg2g'.
  apply: (newer_than_vm_le_newer _ Hg2g').
  apply: (H0 _ _ _ _ _ _ _ _ _ H4) .
  by [apply: (H _ _ _ _ _ _ _ _ _ H1)] .
Qed .

Lemma mk_env_exp_newer_vm_xor :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : w.-tuple literal),
        mk_env_exp m s E g (QFBV64.bvXor w e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_xor_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_exp_newer_vm_neg :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNeg w e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (mk_env_neg_newer_gen Hmkr) => Hg1gr.
  exact: (newer_than_vm_le_newer Hg1m1 Hg1gr).
Qed.

Lemma mk_env_exp_newer_vm_add :
  forall (w0 : nat),
    forall (e : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAdd w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  rewrite /=; intros; dcase_hyps; subst. move: (mk_env_add_newer_gen H3) => Hg2g'.
  apply: (newer_than_vm_le_newer _ Hg2g').
  apply: (H0 _ _ _ _ _ _ _ _ _ H4) .
  by [apply: (H _ _ _ _ _ _ _ _ _ H1)] .
Qed.

Lemma mk_env_exp_newer_vm_sub :
  forall (w0 : nat),
    forall (e : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSub w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  rewrite /=; intros; dcase_hyps; subst. move: (mk_env_sub_newer_gen H3) => Hg2g'.
  apply: (newer_than_vm_le_newer _ Hg2g').
  apply: (H0 _ _ _ _ _ _ _ _ _ H4).
  by apply: (H _ _ _ _ _ _ _ _ _ H1).
Qed.

Lemma mk_env_exp_newer_vm_mul :
  forall (w0 : nat),
    forall (e : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMul w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_mul_newer_gen H3) => Hg1g'.
  apply: (newer_than_vm_le_newer _ Hg1g').
  apply: (H0 _ _ _ _ _ _ _ _ _ H4) .
  by [apply: (H _ _ _ _ _ _ _ _ _ H1)] .
Qed.

Lemma mk_env_exp_newer_vm_mod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_srem :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSrem w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_smod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSmod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_shl :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvShl w e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_shl_newer_gen H3) => Hg2g'.
  apply: (newer_than_vm_le_newer _ Hg2g').
  apply: (H0 _ _ _ _ _ _ _ _ _ H4) .
  by [apply: (H _ _ _ _ _ _ _ _ _ H1)] .
Qed .

Lemma mk_env_exp_newer_vm_lshr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvLshr w e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_lshr_newer_gen H3) => Hg2g'.
  apply: (newer_than_vm_le_newer _ Hg2g').
  apply: (H0 _ _ _ _ _ _ _ _ _ H4) .
  by [apply: (H _ _ _ _ _ _ _ _ _ H1)] .
Qed .

Lemma mk_env_exp_newer_vm_ashr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e1 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w.+1).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvAshr w e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_ashr_newer_gen H3) => Hg2g'.
  apply: (newer_than_vm_le_newer _ Hg2g').
  apply: (H0 _ _ _ _ _ _ _ _ _ H4) .
  by [apply: (H _ _ _ _ _ _ _ _ _ H1)] .
Qed .

Lemma mk_env_exp_newer_vm_concat :
  forall (w0 w1 : nat),
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e1 : QFBV64.exp w1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w1.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : (w1 + w0).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvConcat w0 w1 e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H0 _ _ _ _ _ _ _ _ _ H4) .
  by apply: (H _ _ _ _ _ _ _ _ _ H1) .
Qed .

Lemma mk_env_exp_newer_vm_extract :
  forall (w i j : nat),
    forall (e : QFBV64.exp (j + (i - j + 1) + w)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (j + (i - j + 1) + w).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : (i - j + 1).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvExtract w i j e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  by apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_newer_vm_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV64.exp (w3 + w2 + w1)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  by apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_newer_vm_high :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (wl + wh).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm)
           (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
           (E' : env) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvHigh wh wl e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  by apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_newer_vm_low :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (wl + wh).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : wl.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvLow wh wl e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  by apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_newer_vm_zeroextend :
  forall (w n : nat),
    forall (e : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : (w + n).-tuple literal),
        mk_env_exp m s E g (QFBV64.bvZeroExtend w n e) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  by apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_newer_vm_signextend :
  forall (w n : nat),
    forall (e : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : QFBV64.State.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w.+1 + n).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSignExtend w n e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  by apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_newer_vm_ite :
  forall (w : nat) (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (e0 : QFBV64.exp w),
        (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : w.-tuple literal),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
            newer_than_vm g m -> newer_than_vm g' m') ->
        forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g (QFBV64.bvIte w b e e0) = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  rewrite /=; intros; dcase_hyps; subst. move: (mk_env_ite_newer_gen H6) => Hg2g'.
  apply: (newer_than_vm_le_newer _ Hg2g').
  apply: (H1 _ _ _ _ _ _ _ _ _ H4). apply: (H0 _ _ _ _ _ _ _ _ _ H5).
  exact: (H _ _ _ _ _ _ _ _ _ H2).
Qed.

Lemma mk_env_bexp_newer_vm_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> m s E g m' E' g' cs lr. case=> <- _ <- _ _. done.
Qed.

Lemma mk_env_bexp_newer_vm_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> m s E g m' E' g' cs lr. case=> <- _ <- _ _. done.
Qed.

Lemma mk_env_bexp_newer_vm_eq :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvEq w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> <- _ <- _ _ Hnew.
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew) => Hnew1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1) => Hnew2.
  apply: (newer_than_vm_le_newer Hnew2). exact: (mk_env_eq_newer_gen Heq).
Qed.

Lemma mk_env_bexp_newer_vm_ult :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUlt w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hult: (mk_env_ult E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> <- _ <- _ _ Hnew.
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew) => Hnew1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1) => Hnew2.
  apply: (newer_than_vm_le_newer Hnew2). exact: (mk_env_ult_newer_gen Hult).
Qed.

Lemma mk_env_bexp_newer_vm_ule :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUle w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hule: (mk_env_ule E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> <- _ <- _ _ Hnew.
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew) => Hnew1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1) => Hnew2.
  apply: (newer_than_vm_le_newer Hnew2). exact: (mk_env_ule_newer_gen Hule).
Qed.

Lemma mk_env_bexp_newer_vm_ugt :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUgt w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hugt: (mk_env_ugt E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> <- _ <- _ _ Hnew.
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew) => Hnew1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1) => Hnew2.
  apply: (newer_than_vm_le_newer Hnew2). exact: (mk_env_ugt_newer_gen Hugt).
Qed.

Lemma mk_env_bexp_newer_vm_uge :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUge w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Huge: (mk_env_uge E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> <- _ <- _ _ Hnew.
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew) => Hnew1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1) => Hnew2.
  apply: (newer_than_vm_le_newer Hnew2). exact: (mk_env_uge_newer_gen Huge).
Qed.


Lemma mk_env_bexp_newer_vm_slt :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSlt w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_slt_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_sle :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSle w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_sle_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_sgt :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSgt w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_sgt_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_sge :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSge w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_sge_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_uaddo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUaddo w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Huaddo: (mk_env_uaddo E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> <- _ <- _ _ Hnew.
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew) => Hnew1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1) => Hnew2.
  apply: (newer_than_vm_le_newer Hnew2). exact: (mk_env_uaddo_newer_gen Huaddo).
Qed.

Lemma mk_env_bexp_newer_vm_usubo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUsubo w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Husubo: (mk_env_usubo E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> <- _ <- _ _ Hnew.
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew) => Hnew1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1) => Hnew2.
  apply: (newer_than_vm_le_newer Hnew2). exact: (mk_env_usubo_newer_gen Husubo).
Qed.

Lemma mk_env_bexp_newer_vm_umulo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUmulo w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Humulo: (mk_env_umulo E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> <- _ <- _ _ Hnew.
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew) => Hnew1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1) => Hnew2.
  apply: (newer_than_vm_le_newer Hnew2). exact: (mk_env_umulo_newer_gen Humulo).
Qed.

Lemma mk_env_bexp_newer_vm_saddo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSaddo w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_saddo_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_ssubo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSsubo w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_ssubo_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_smulo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSmulo w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_smulo_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_lneg :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvLneg b) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e IH m s E g m' E' g' cs lr /=.
  case Henv: (mk_env_bexp m s E g e) => [[[[m1 E1] g1] cs1] lr1].
  case => <- _ <- _ _ Hnew. apply newer_than_vm_add_r.
  apply: (IH _ _ _ _ _ _ _ _ _ Henv).
  exact.
Qed.

Lemma mk_env_bexp_newer_vm_conj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /=.
  case Henv1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case=> <- _ <- _ _ Hnew. apply: newer_than_vm_add_r.
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2). apply: (IH1 _ _ _ _ _ _ _ _ _ Henv1).
  exact: Hnew.
Qed.

Lemma mk_env_bexp_newer_vm_disj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvDisj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /=.
  case Henv1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case=> <- _ <- _ _ Hnew. apply: newer_than_vm_add_r.
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2). apply: (IH1 _ _ _ _ _ _ _ _ _ Henv1).
  exact: Hnew.
Qed.

Corollary mk_env_exp_newer_vm :
  forall w (e : QFBV64.exp w) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_vm g' m'
  with
    mk_env_bexp_newer_vm :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  (* mk_env_exp_newer_vm *)
  move=> w [] {w}.
  - exact: mk_env_exp_newer_vm_var.
  - exact: mk_env_exp_newer_vm_const.
  - move=> w e.
    move: (mk_env_exp_newer_vm _ e) => IH.
    exact: (mk_env_exp_newer_vm_not IH).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IH1 IH2.
    exact: (mk_env_exp_newer_vm_and IH1 IH2).
  - move => w e0 e1 .
    move: (mk_env_exp_newer_vm _ e0) (mk_env_exp_newer_vm _ e1) => IHe0 IHe1 .
    exact: (mk_env_exp_newer_vm_or IHe0 IHe1) .
  - move=> w e1 e2.
    move: (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IH1 IH2.
    exact: (mk_env_exp_newer_vm_xor IH1 IH2).
  - move=> w e.
    move: (mk_env_exp_newer_vm _ e) => IH.
    exact: (mk_env_exp_newer_vm_neg IH).
  - move => w e0 e1.
    move: (mk_env_exp_newer_vm _ e0) (mk_env_exp_newer_vm _ e1) => IHe0 IHe1.
    exact: (mk_env_exp_newer_vm_add IHe0 IHe1).
  - move => w e0 e1.
    move: (mk_env_exp_newer_vm _ e0) (mk_env_exp_newer_vm _ e1) => IHe0 IHe1.
    exact: (mk_env_exp_newer_vm_sub IHe0 IHe1).
  - move => w e0 e1 .
    move: (mk_env_exp_newer_vm _ e0) (mk_env_exp_newer_vm _ e1) => IHe0 IHe1 .
    exact: (mk_env_exp_newer_vm_mul IHe0 IHe1).
  - exact: mk_env_exp_newer_vm_mod.
  - exact: mk_env_exp_newer_vm_srem.
  - exact: mk_env_exp_newer_vm_smod.
  - move => w e0 e1 .
    exact: (mk_env_exp_newer_vm_shl (mk_env_exp_newer_vm _ e0)
                                    (mk_env_exp_newer_vm _ e1)) .
  - move => w e0 e1 .
    exact: (mk_env_exp_newer_vm_lshr (mk_env_exp_newer_vm _ e0)
                                     (mk_env_exp_newer_vm _ e1)) .
  - move => w e0 e1 .
    exact: (mk_env_exp_newer_vm_ashr (mk_env_exp_newer_vm _ e0)
                                     (mk_env_exp_newer_vm _ e1)) .
  - move => w0 w1 e0 e1 .
    move: (mk_env_exp_newer_vm _ e0) (mk_env_exp_newer_vm _ e1) => IHe0 IHe1 .
    exact: (mk_env_exp_newer_vm_concat IHe0 IHe1) .
  - move => w i j e .
    apply: mk_env_exp_newer_vm_extract (mk_env_exp_newer_vm _ e) .
  - move => w1 w2 w3 e .
    apply: mk_env_exp_newer_vm_slice (mk_env_exp_newer_vm _ e) .
  - move => wh wl e .
    apply: mk_env_exp_newer_vm_high (mk_env_exp_newer_vm _ e) .
  - move => wh wl e .
    apply: mk_env_exp_newer_vm_low (mk_env_exp_newer_vm _ e) .
  - move => w n e .
    apply: mk_env_exp_newer_vm_zeroextend
             (mk_env_exp_newer_vm _ e) .
  - move => w n e .
    apply: mk_env_exp_newer_vm_signextend (mk_env_exp_newer_vm _ e) .
  - move=> w c e1 e2.
    move: (mk_env_bexp_newer_vm c)
            (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IHc IH1 IH2.
    exact: (mk_env_exp_newer_vm_ite IHc IH1 IH2).
  (* mk_env_bexp_newer_vm *)
  case.
  - exact: mk_env_bexp_newer_vm_false.
  - exact: mk_env_bexp_newer_vm_true.
  - move=> w e1 e2.
    move: (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_eq IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_ult IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_ule IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_ugt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_uge IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_slt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_sle IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_sgt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_sge IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_uaddo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_usubo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_umulo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_saddo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_ssubo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_smulo IH1 IH2).
  - move=> e.
    move: (mk_env_bexp_newer_vm e) => IH.
    exact: (mk_env_bexp_newer_vm_lneg IH).
  - move=> e1 e2.
    move: (mk_env_bexp_newer_vm e1) (mk_env_bexp_newer_vm e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_conj IH1 IH2).
  - move=> e1 e2.
    move: (mk_env_bexp_newer_vm e1) (mk_env_bexp_newer_vm e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_disj IH1 IH2).
Qed.



(* = mk_env_exp_newer_res and mk_env_bexp_newer_res = *)

Lemma mk_env_exp_newer_res_var :
  forall (t : VarOrder.t) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : wordsize.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvVar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case Hfind: (VM.find v m).
  - case=> _ _ <- _ <- Hnew_gm Hnew_gtt. exact: (Hnew_gm v _ Hfind).
  - case Henv: (mk_env_var E g (QFBV64.State.acc v s) v)=> [[[Ev gv] csv] lrsv].
    case=> _ _ <- _ <- Hnew_gm Hnew_gtt. exact: (mk_env_var_newer_res Henv).
Qed.

Lemma mk_env_exp_newer_res_const :
  forall (w0 : nat) (b : BITS w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConst w0 b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> w bs m s E g m' E' g' cs lrs. rewrite /mk_env_exp.
  case Henv: (mk_env_const E g bs)=> [[[oE og] ocs] olrs].
  case=> _ _ <- _ <- Hnew_gm Hnew_tt. exact: (mk_env_const_newer_res Henv Hnew_tt).
Qed.

Lemma mk_env_exp_newer_res_not :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator)
            (cs : cnf) (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        newer_than_lits g' lrs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvNot w e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> w e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  exact: (mk_env_not_newer_res Hmkr Hg1l1).
Qed.

Lemma mk_env_exp_newer_res_and :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator)
            (cs : cnf) (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        newer_than_lits g' lrs) ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : w.-tuple literal),
        mk_env_exp m s E g (QFBV64.bvAnd w e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  (* now mk_env_and_newer_res is available *)
  exact: (mk_env_and_newer_res Hmkr Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_newer_res_or :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvOr w e0 e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  intros w e0 IHe0 e1 IHe1 .
  rewrite /=; intros; dcase_hyps; subst .
  move : (mk_env_exp_newer_gen H) => Hgg0 .
  move : (mk_env_exp_newer_gen H3) => Hg0g1 .
  move : (mk_env_exp_newer_vm H H0) => Hg0m0 .
  move : (newer_than_lit_le_newer H1 Hgg0) => {Hgg0} Hg0tt .
  move : (IHe0 _ _ _ _ _ _ _ _ _ H H0 H1) => {H H0 IHe0} IHg0ls .
  move : (IHe1 _ _ _ _ _ _ _ _ _ H3 Hg0m0 Hg0tt) => {IHe1 Hg0m0} Hg1ls0 .
  move : (newer_than_lits_le_newer IHg0ls Hg0g1) => {IHg0ls} Hg1ls .
  move : (newer_than_lit_le_newer Hg0tt Hg0g1) => {Hg0tt} Hg1tt .
  exact : (mk_env_or_newer_res H2 Hg1tt Hg1ls Hg1ls0) .
Qed .

Lemma mk_env_exp_newer_res_xor :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator)
            (cs : cnf) (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        newer_than_lits g' lrs) ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : w.-tuple literal),
        mk_env_exp m s E g (QFBV64.bvXor w e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  (* now mk_env_and_newer_res is available *)
  exact: (mk_env_xor_newer_res Hmkr Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_newer_res_neg :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator)
            (cs : cnf) (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        newer_than_lits g' lrs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : w.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNeg w e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> w e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  exact : (mk_env_neg_newer_res Hmkr (newer_than_lit_le_newer Hgt (mk_env_exp_newer_gen Hmke1)) Hg1l1).
Qed.

Lemma mk_env_exp_newer_res_add :
  forall (w0 : nat),
    forall (e : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAdd w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  intros w e0 IHe0 e1 IHe1.
  rewrite /=; intros; dcase_hyps; subst.
  exact : (mk_env_add_newer_res H2).
Qed.

Lemma mk_env_exp_newer_res_sub :
  forall (w0 : nat),
    forall (e : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSub w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  intros w e0 IHe0 e1 IHe1.
  rewrite /=; intros; dcase_hyps; subst.
  exact : (mk_env_sub_newer_res H2).
Qed.

Lemma mk_env_exp_newer_res_mul :
  forall (w0 : nat),
    forall (e : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMul w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move => w e IHe e0 IHe0.
  rewrite /=; intros; dcase_hyps; subst.
  apply (mk_env_mul_newer_res H2).
  move : (mk_env_exp_newer_gen H) => Hgg0.
  move : (mk_env_exp_newer_gen H3) => Hg0g3.
  rewrite /newer_than_lit.
  apply : (newer_than_var_le_newer _ Hg0g3).
  apply : (newer_than_var_le_newer _ Hgg0).
  exact.
Qed.

Lemma mk_env_exp_newer_res_mod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_srem :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSrem w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_smod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSmod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_shl :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvShl w e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  intros w e0 IHe0 e1 IHe1 .
  rewrite /=; intros; dcase_hyps; subst .
  move : (mk_env_exp_newer_gen H) => Hgg0 .
  move : (mk_env_exp_newer_gen H3) => Hg0g1 .
  move : (mk_env_exp_newer_vm H H0) => Hg0m0 .
  move : (newer_than_lit_le_newer H1 Hgg0) => {Hgg0} Hg0tt .
  move : (IHe0 _ _ _ _ _ _ _ _ _ H H0 H1) => {H H0 IHe0} IHg0ls .
  move : (IHe1 _ _ _ _ _ _ _ _ _ H3 Hg0m0 Hg0tt) => {IHe1 Hg0m0} Hg1ls0 .
  move : (newer_than_lits_le_newer IHg0ls Hg0g1) => {IHg0ls} Hg1ls .
  move : (newer_than_lit_le_newer Hg0tt Hg0g1) => {Hg0tt} Hg1tt .
  exact : (mk_env_shl_newer_res Hg1tt Hg1ls Hg1ls0 H2) .
Qed .

Lemma mk_env_exp_newer_res_lshr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvLshr w e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  intros w e0 IHe0 e1 IHe1 .
  rewrite /=; intros; dcase_hyps; subst .
  move : (mk_env_exp_newer_gen H) => Hgg0 .
  move : (mk_env_exp_newer_gen H3) => Hg0g1 .
  move : (mk_env_exp_newer_vm H H0) => Hg0m0 .
  move : (newer_than_lit_le_newer H1 Hgg0) => {Hgg0} Hg0tt .
  move : (IHe0 _ _ _ _ _ _ _ _ _ H H0 H1) => {H H0 IHe0} IHg0ls .
  move : (IHe1 _ _ _ _ _ _ _ _ _ H3 Hg0m0 Hg0tt) => {IHe1 Hg0m0} Hg1ls0 .
  move : (newer_than_lits_le_newer IHg0ls Hg0g1) => {IHg0ls} Hg1ls .
  move : (newer_than_lit_le_newer Hg0tt Hg0g1) => {Hg0tt} Hg1tt .
  exact : (mk_env_lshr_newer_res Hg1tt Hg1ls Hg1ls0 H2) .
Qed .

Lemma mk_env_exp_newer_res_ashr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e1 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w.+1).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvAshr w e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  intros w e0 IHe0 e1 IHe1 .
  rewrite /=; intros; dcase_hyps; subst .
  move : (mk_env_exp_newer_gen H) => Hgg0 .
  move : (mk_env_exp_newer_gen H3) => Hg0g1 .
  move : (mk_env_exp_newer_vm H H0) => Hg0m0 .
  move : (newer_than_lit_le_newer H1 Hgg0) => {Hgg0} Hg0tt .
  move : (IHe0 _ _ _ _ _ _ _ _ _ H H0 H1) => {H H0 IHe0} IHg0ls .
  move : (IHe1 _ _ _ _ _ _ _ _ _ H3 Hg0m0 Hg0tt) => {IHe1 Hg0m0} Hg1ls0 .
  move : (newer_than_lits_le_newer IHg0ls Hg0g1) => {IHg0ls} Hg1ls .
  move : (newer_than_lit_le_newer Hg0tt Hg0g1) => {Hg0tt} Hg1tt .
  exact : (mk_env_ashr_newer_res Hg1tt Hg1ls Hg1ls0 H2) .
Qed .

Lemma mk_env_exp_newer_res_concat :
  forall (w0 w1 : nat),
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e1 : QFBV64.exp w1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : w1.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : (w1 + w0).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvConcat w0 w1 e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  intros w0 w1 e0 IHe0 e1 IHe1 .
  rewrite /=; intros; dcase_hyps; subst .
  move : (mk_env_exp_newer_gen H) => Hgg0 .
  move : (mk_env_exp_newer_gen H3) => Hg0g1 .
  move : (mk_env_exp_newer_vm H H0) => Hg0m0 .
  move : (newer_than_lit_le_newer H1 Hgg0) => {Hgg0} Hg0tt .
  move : (IHe0 _ _ _ _ _ _ _ _ _ H H0 H1) => {H H0 IHe0} IHg0ls .
  move : (IHe1 _ _ _ _ _ _ _ _ _ H3 Hg0m0 Hg0tt) => {IHe1 Hg0m0} Hg'ls0 .
  move : (newer_than_lits_le_newer IHg0ls Hg0g1) => {IHg0ls} Hg'ls .
  by rewrite newer_than_lits_append Hg'ls0 Hg'ls .
Qed .

Lemma mk_env_exp_newer_res_extract :
  forall (w i j : nat),
    forall (e : QFBV64.exp (j + (i - j + 1) + w)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : (j + (i - j + 1) + w).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : (i - j + 1).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvExtract w i j e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move => w i j e IHe .
  rewrite /=; intros; dcase_hyps; subst .
  move: (IHe _ _ _ _ _ _ _ _ _ H H0 H1) => Hg'ls .
  apply: newer_than_lits_get_high_aux .
  by apply: newer_than_lits_get_low_aux .
Qed .

Lemma mk_env_exp_newer_res_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV64.exp (w3 + w2 + w1)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move => w1 w2 w3 e IHe .
  rewrite /=; intros; dcase_hyps; subst .
  move: (IHe _ _ _ _ _ _ _ _ _ H H0 H1) => Hg'ls .
  apply: newer_than_lits_get_high_aux .
  by apply: newer_than_lits_get_low_aux .
Qed .

Lemma mk_env_exp_newer_res_high :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : (wl + wh).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm)
         (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvHigh wh wl e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move => wh wl e IHe .
  rewrite /=; intros; dcase_hyps; subst .
  move: (IHe _ _ _ _ _ _ _ _ _ H H0 H1) => Hg'ls .
  by apply: newer_than_lits_get_high_aux .
Qed .

Lemma mk_env_exp_newer_res_low :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : (wl + wh).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : wl.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvLow wh wl e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move => wh wl e IHe .
  rewrite /=; intros; dcase_hyps; subst .
  move: (IHe _ _ _ _ _ _ _ _ _ H H0 H1) => Hg'ls .
  by apply: newer_than_lits_get_low_aux .
Qed .

Lemma mk_env_exp_newer_res_zeroextend :
  forall (w n : nat),
    forall (e : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : QFBV64.State.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w + n).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvZeroExtend w n e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  intros w n e IHe .
  rewrite /=; intros; dcase_hyps; subst .
  move: (mk_env_exp_newer_gen H) => Hgg' .
  move: (newer_than_lit_le_newer H1 Hgg') .
  rewrite -newer_than_lit_neg => Hg'ff .
  rewrite newer_than_lits_append .
  rewrite (IHe _ _ _ _ _ _ _ _ _ H H0 H1) {H H0} .
  rewrite -[neg_lit lit_tt]/lit_ff in Hg'ff .
  rewrite (newer_than_lits_nseq_lit n Hg'ff) .
  done .
Qed .

Lemma mk_env_exp_newer_res_signextend :
  forall (w n : nat),
    forall (e : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : QFBV64.State.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w.+1 + n).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSignExtend w n e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  intros w n e IHe .
  rewrite /=; intros; dcase_hyps; subst .
  move: (IHe _ _ _ _ _ _ _ _ _ H H0 H1) => Hg'ls .
  rewrite newer_than_lits_append .
  apply /andP; split; first done .
  apply newer_than_lits_nseq_lit .
  by apply: newer_than_lits_last .
Qed .

Lemma mk_env_exp_newer_res_ite :
  forall (w : nat) (b : QFBV64.bexp) (e e0 : QFBV64.exp w)
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvIte w b e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. exact: (mk_env_ite_newer_res H4).
Qed.

Lemma mk_env_bexp_newer_res_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- _ <- Hnvm Hnew. exact: Hnew.
Qed.

Lemma mk_env_bexp_newer_res_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- _ <- Hnvm Hnew. exact: Hnew.
Qed.

Lemma mk_env_bexp_newer_res_eq :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvEq w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  exact: (mk_env_eq_newer_res H2).
Qed.

Lemma mk_env_bexp_newer_res_ult :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUlt w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_exp_newer_gen H) => tmp1.
  move: (mk_env_exp_newer_gen H3) => tmp2.
  move: (pos_leb_trans tmp1 tmp2) => tmp3.
  move: (newer_than_lit_le_newer H1 tmp3) => H4.
  exact: (mk_env_ult_newer_res H2).
Qed.


Lemma mk_env_bexp_newer_res_ule :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUle w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_exp_newer_gen H) => tmp1.
  move: (mk_env_exp_newer_gen H3) => tmp2.
  move: (pos_leb_trans tmp1 tmp2) => tmp3.
  move: (newer_than_lit_le_newer H1 tmp3) => H4.
  exact: (mk_env_ule_newer_res H2).
Qed.

Lemma mk_env_bexp_newer_res_ugt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUgt w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_exp_newer_gen H) => tmp1.
  move: (mk_env_exp_newer_gen H3) => tmp2.
  move: (pos_leb_trans tmp1 tmp2) => tmp3.
  move: (newer_than_lit_le_newer H1 tmp3) => H4.
  exact: (mk_env_ugt_newer_res H2).
Qed.

Lemma mk_env_bexp_newer_res_uge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUge w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_exp_newer_gen H) => tmp1.
  move: (mk_env_exp_newer_gen H3) => tmp2.
  move: (pos_leb_trans tmp1 tmp2) => tmp3.
  move: (newer_than_lit_le_newer H1 tmp3) => H4.
  exact: (mk_env_uge_newer_res H2).
Qed.

Lemma mk_env_bexp_newer_res_slt :
  forall (w : nat) (e1 e2 : QFBV64.exp w.+1) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSlt w e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> w e1 e2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- _ <- Hnvm Hgt.
  exact: (mk_env_slt_newer_res Hmkr).
Qed.

Lemma mk_env_bexp_newer_res_sle :
  forall (w : nat) (e1 e2 : QFBV64.exp w.+1) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSle w e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> w e1 e2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- _ <- Hnvm Hgt.
  exact: (mk_env_sle_newer_res Hmkr).
Qed.

Lemma mk_env_bexp_newer_res_sgt :
  forall (w : nat) (e1 e2 : QFBV64.exp w.+1) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSgt w e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> w e1 e2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- _ <- Hnvm Hgt.
  exact: (mk_env_sgt_newer_res Hmkr).
Qed.

Lemma mk_env_bexp_newer_res_sge :
  forall (w : nat) (e1 e2 : QFBV64.exp w.+1) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSge w e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> w e1 e2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- _ <- Hnvm Hgt.
  exact: (mk_env_sge_newer_res Hmkr).
Qed.

Lemma mk_env_bexp_newer_res_uaddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUaddo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_exp_newer_gen H) => tmp1.
  move: (mk_env_exp_newer_gen H3) => tmp2.
  move: (pos_leb_trans tmp1 tmp2) => tmp3.
  move: (newer_than_lit_le_newer H1 tmp3) => H4.
  exact: (mk_env_uaddo_newer_res H2).
Qed.

Lemma mk_env_bexp_newer_res_usubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUsubo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_exp_newer_gen H) => tmp1.
  move: (mk_env_exp_newer_gen H3) => tmp2.
  move: (pos_leb_trans tmp1 tmp2) => tmp3.
  move: (newer_than_lit_le_newer H1 tmp3) => H4.
  exact: (mk_env_usubo_newer_res H2).
Qed.

Lemma mk_env_bexp_newer_res_umulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUmulo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_exp_newer_gen H) => tmp1.
  move: (mk_env_exp_newer_gen H3) => tmp2.
  move: (pos_leb_trans tmp1 tmp2) => tmp3.
  move: (newer_than_lit_le_newer H1 tmp3) => H4.
  exact: (mk_env_umulo_newer_res H2).
Qed.

Lemma mk_env_bexp_newer_res_saddo :
  forall (w : nat) (e1 e2 : QFBV64.exp w.+1) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSaddo w e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> w e1 e2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- _ <- Hnvm Hgt.
  exact: (mk_env_saddo_newer_res Hmkr).
Qed.

Lemma mk_env_bexp_newer_res_ssubo :
  forall (w : nat) (e1 e2 : QFBV64.exp w.+1) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSsubo w e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> w e1 e2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- _ <- Hnvm Hgt.
  exact: (mk_env_ssubo_newer_res Hmkr).
Qed.

Lemma mk_env_bexp_newer_res_smulo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator)
            (cs : cnf) (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        newer_than_lits g' lrs) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSmulo w e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> w e1 IH1 e2 IH2  m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1tt.
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt.
  exact: (mk_env_smulo_newer_res Hmkr).
Qed.

Lemma mk_env_bexp_newer_res_lneg :
  forall (b : QFBV64.bexp) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvLneg b) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  exact: newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_bexp_newer_res_conj :
  forall (b b0 : QFBV64.bexp) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  exact: newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_bexp_newer_res_disj :
  forall (b b0 : QFBV64.bexp) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvDisj b b0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite/=; intros; dcase_hyps; subst.
  exact: newer_than_lit_add_diag_r.
Qed.

Corollary mk_env_exp_newer_res :
  forall w (e : QFBV64.exp w) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs
  with
    mk_env_bexp_newer_res :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_lit g' lr.
Proof.
  (* mk_env_exp_newer_res *)
  move=> w [].
  - exact: mk_env_exp_newer_res_var.
  - exact: mk_env_exp_newer_res_const.
  - move=> w0 e.
    move: (mk_env_exp_newer_res _ e) => IH.
    exact: (mk_env_exp_newer_res_not IH).
  - move=> w0 e1 e2.
    move: (mk_env_exp_newer_res _ e1) (mk_env_exp_newer_res _ e2) => IH1 IH2.
    exact: (mk_env_exp_newer_res_and IH1 IH2).
  - intros . move: (mk_env_exp_newer_res _ e) => IHe .
    move: (mk_env_exp_newer_res _ e0) => IHe0 .
    exact: (mk_env_exp_newer_res_or IHe IHe0 H H0 H1) .
  - move=> w0 e1 e2.
    move: (mk_env_exp_newer_res _ e1) (mk_env_exp_newer_res _ e2) => IH1 IH2.
    exact: (mk_env_exp_newer_res_xor IH1 IH2).
  - move=> w0 e.
    move: (mk_env_exp_newer_res _ e) => IH.
    exact: (mk_env_exp_newer_res_neg IH).
  - move => w0 e0 e1.
    intros. move: (mk_env_exp_newer_res _ e0) => IHe.
    move: (mk_env_exp_newer_res _ e1) => IHe0.
    exact: (mk_env_exp_newer_res_add IHe IHe0 H H0 H1).
  - move => w0 e0 e1.
    intros. move: (mk_env_exp_newer_res _ e0) => IHe.
    move: (mk_env_exp_newer_res _ e1) => IHe0.
    exact: (mk_env_exp_newer_res_sub IHe IHe0 H H0 H1).
  - move => w0 e0 e1.
    intros. move: (mk_env_exp_newer_res _ e0) => IHe.
    move: (mk_env_exp_newer_res _ e1) => IHe0.
    exact: (mk_env_exp_newer_res_mul IHe IHe0 H H0 H1).
  - exact: mk_env_exp_newer_res_mod.
  - exact: mk_env_exp_newer_res_srem.
  - exact: mk_env_exp_newer_res_smod.
  - move => w0 e0 e1 .
    exact: (mk_env_exp_newer_res_shl (mk_env_exp_newer_res _ e0)
                                     (mk_env_exp_newer_res _ e1)) .
  - move => w0 e0 e1 .
    exact: (mk_env_exp_newer_res_lshr (mk_env_exp_newer_res _ e0)
                                      (mk_env_exp_newer_res _ e1)) .
  - move => w0 e0 e1 .
    exact: (mk_env_exp_newer_res_ashr (mk_env_exp_newer_res _ e0)
                                      (mk_env_exp_newer_res _ e1)) .
  - move => w0 w1 e0 e1 .
    move: (mk_env_exp_newer_res _ e0) (mk_env_exp_newer_res _ e1)
    => IHe0 IHe1 .
    exact: (mk_env_exp_newer_res_concat IHe0 IHe1) .
  - move => w0 i j e .
    apply: mk_env_exp_newer_res_extract (mk_env_exp_newer_res _ e) .
  - move => w1 w2 w3 e .
    apply: mk_env_exp_newer_res_slice (mk_env_exp_newer_res _ e) .
  - move => wh wl e .
    apply: mk_env_exp_newer_res_high (mk_env_exp_newer_res _ e) .
  - move => wh wl e .
    apply: mk_env_exp_newer_res_low (mk_env_exp_newer_res _ e) .
  - move => w' n e .
    apply: mk_env_exp_newer_res_zeroextend (mk_env_exp_newer_res _ e) .
  - move => w' n e .
    apply: mk_env_exp_newer_res_signextend (mk_env_exp_newer_res _ e) .
  - exact: mk_env_exp_newer_res_ite.
  (* mk_env_bexp_newer_res *)
  case.
  - exact: mk_env_bexp_newer_res_false.
  - exact: mk_env_bexp_newer_res_true.
  - exact: mk_env_bexp_newer_res_eq.
  - exact: mk_env_bexp_newer_res_ult.
  - exact: mk_env_bexp_newer_res_ule.
  - exact: mk_env_bexp_newer_res_ugt.
  - exact: mk_env_bexp_newer_res_uge.
  - exact: mk_env_bexp_newer_res_slt.
  - exact: mk_env_bexp_newer_res_sle.
  - exact: mk_env_bexp_newer_res_sgt.
  - exact: mk_env_bexp_newer_res_sge.
  - exact: mk_env_bexp_newer_res_uaddo.
  - exact: mk_env_bexp_newer_res_usubo.
  - exact: mk_env_bexp_newer_res_umulo.
  - exact: mk_env_bexp_newer_res_saddo.
  - exact: mk_env_bexp_newer_res_ssubo.
  - move=> w e1 e2.
    move: (mk_env_exp_newer_res _ e1) (mk_env_exp_newer_res _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_res_smulo IH1 IH2).
  - exact: mk_env_bexp_newer_res_lneg.
  - exact: mk_env_bexp_newer_res_conj.
  - exact: mk_env_bexp_newer_res_disj.
Qed.



(* = mk_env_exp_newer_cnf and mk_env_bexp_newer_cnf = *)

Lemma mk_env_exp_newer_cnf_var :
  forall (t : VarOrder.t) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : wordsize.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvVar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case: (VM.find v m).
  - move=> lxs [] _ _ <- <- _ Hnew_gm Hnew_gtt. done.
  - case Henv: (mk_env_var E g (QFBV64.State.acc v s) v)=> [[[Ev gv] csv] lrsv].
    case=> _ _ <- <- _ Hnew_gm Hnew_gtt. exact: (mk_env_var_newer_cnf Henv).
Qed.

Lemma mk_env_exp_newer_cnf_const :
  forall (w0 : nat) (b : BITS w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConst w0 b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
  move=> w bs m s E g m' E' g' cs lrs /=. case=> _ _ <- <- _ Hnew_gm Hnew_gtt. done.
Qed.

Lemma mk_env_exp_newer_cnf_not :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvNot w e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt.
  rewrite !newer_than_cnf_append.
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1c1.
  move: (mk_env_not_newer_gen Hmkr) => Hg1gr.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1gr) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  exact: (mk_env_not_newer_cnf Hmkr Hg1l1).
Qed.

Lemma mk_env_exp_newer_cnf_and :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : w.-tuple literal),
        mk_env_exp m s E g (QFBV64.bvAnd w e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt.
  rewrite !newer_than_cnf_append.
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_and_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  exact: (mk_env_and_newer_cnf Hmkr Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_newer_cnf_or :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvOr w e0 e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !newer_than_cnf_append.
  move: (mk_env_exp_newer_gen H1) => Hgg0 .
  move: (mk_env_exp_newer_gen H5) => Hg0g1.
  move: (mk_env_or_newer_gen H4) => Hg1g'.
  (* newer_than_cnf g' cs0 *)
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => Hnew_g0cs0.
  move: (pos_leb_trans Hg0g1 Hg1g') => Hg0g'.
  rewrite (newer_than_cnf_le_newer Hnew_g0cs0 Hg0g') /=.
  (* newer_than_cnf g' cs1 *)
  move: (mk_env_exp_newer_vm H1 H2) => Hnew_g0m0.
  move: (newer_than_lit_le_newer H3 Hgg0) => {Hgg0} Hg0tt.
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hnew_g0m0 Hg0tt) => Hnew_g1cs1.
  rewrite (newer_than_cnf_le_newer Hnew_g1cs1 Hg1g') /=.
  (* newer_than_cnf g' cs2 *)
  move: (mk_env_exp_newer_res H1 H2 H3) => Hnew_g0ls.
  move: (mk_env_exp_newer_res H5 Hnew_g0m0 Hg0tt) => Hnew_g1ls0 .
  move: (newer_than_lits_le_newer Hnew_g0ls Hg0g1) => Hnew_g1ls .
  exact: (mk_env_or_newer_cnf H4 Hnew_g1ls Hnew_g1ls0) .
Qed.

Lemma mk_env_exp_newer_cnf_xor :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : w.-tuple literal),
        mk_env_exp m s E g (QFBV64.bvXor w e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt.
  rewrite !newer_than_cnf_append.
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_xor_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  exact: (mk_env_xor_newer_cnf Hmkr Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_newer_cnf_neg :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
     mk_env_exp m s E g (QFBV64.bvNeg w e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt.
  rewrite !newer_than_cnf_append.
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1c1.
  move: (mk_env_neg_newer_gen Hmkr) => Hg1gr.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1gr) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  exact : (mk_env_neg_newer_cnf Hmkr (newer_than_lit_le_newer Hgt (mk_env_exp_newer_gen Hmke1)) Hg1l1).
Qed.

Lemma mk_env_exp_newer_cnf_add :
  forall (w0 : nat),
    forall (e : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAdd w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !newer_than_cnf_append.
  move: (mk_env_exp_newer_gen H1) => Hgg0.
  move: (mk_env_exp_newer_gen H5) => Hg0g1.
  move: (mk_env_add_newer_gen H4) => Hg1g'.
  move : (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => Hnewg0cs0.
  move : (pos_leb_trans Hg0g1 Hg1g')  => Hg0g'.
  rewrite (newer_than_cnf_le_newer Hnewg0cs0 Hg0g')/=.
  move : (mk_env_exp_newer_vm H1 H2) => Hg0m0.
  move : (newer_than_lit_le_newer H3 Hgg0) => {Hgg0} Hg0tt.
  move : (newer_than_lit_le_newer Hg0tt Hg0g1) => Hg1tt.
  move : (H0 _ _ _ _ _ _ _ _ _ H5 Hg0m0 Hg0tt) => Hg1cs1.
  rewrite (newer_than_cnf_le_newer Hg1cs1 Hg1g') /=.
  move: (mk_env_exp_newer_res H1 H2 H3) => Hg0ls.
  move: (mk_env_exp_newer_res H5 Hg0m0 Hg0tt) => Hg1ls0 .
  move: (newer_than_lits_le_newer Hg0ls Hg0g1) => Hg1ls .
  exact : (mk_env_add_newer_cnf H4 Hg1tt Hg1ls Hg1ls0).
Qed.

Lemma mk_env_exp_newer_cnf_sub :
  forall (w0 : nat),
    forall (e : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSub w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !newer_than_cnf_append.
  move: (mk_env_exp_newer_gen H1) => Hgg0.
  move: (mk_env_exp_newer_gen H5) => Hg0g1.
  move: (mk_env_sub_newer_gen H4) => Hg1g'.
  move : (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => Hnewg0cs0.
  move : (pos_leb_trans Hg0g1 Hg1g')  => Hg0g'.
  rewrite (newer_than_cnf_le_newer Hnewg0cs0 Hg0g')/=.
  move : (mk_env_exp_newer_vm H1 H2) => Hg0m0.
  move : (newer_than_lit_le_newer H3 Hgg0) => {Hgg0} Hg0tt.
  move : (newer_than_lit_le_newer Hg0tt Hg0g1) => Hg1tt.
  move : (H0 _ _ _ _ _ _ _ _ _ H5 Hg0m0 Hg0tt) => Hg1cs1.
  rewrite (newer_than_cnf_le_newer Hg1cs1 Hg1g') /=.
  move: (mk_env_exp_newer_res H1 H2 H3) => Hg0ls.
  move: (mk_env_exp_newer_res H5 Hg0m0 Hg0tt) => Hg1ls0 .
  move: (newer_than_lits_le_newer Hg0ls Hg0g1) => Hg1ls .
  exact : (mk_env_sub_newer_cnf H4 Hg1tt Hg1ls Hg1ls0).
Qed.

Lemma mk_env_exp_newer_cnf_mul :
  forall (w0 : nat),
    forall (e : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMul w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !newer_than_cnf_append.
  move: (mk_env_exp_newer_gen H1) => Hgg0.
  move: (mk_env_exp_newer_gen H5) => Hg0g1.
  move: (mk_env_mul_newer_gen H4) => Hg1g'.
  move : (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => Hnewg0cs0.
  move : (pos_leb_trans Hg0g1 Hg1g')  => Hg0g'.
  rewrite (newer_than_cnf_le_newer Hnewg0cs0 Hg0g')/=.
  move : (mk_env_exp_newer_vm H1 H2) => Hg0m0.
  move : (newer_than_lit_le_newer H3 Hgg0) => {Hgg0} Hg0tt.
  move : (newer_than_lit_le_newer Hg0tt Hg0g1) => Hg1tt.
  move : (H0 _ _ _ _ _ _ _ _ _ H5 Hg0m0 Hg0tt) => Hg1cs1.
  rewrite (newer_than_cnf_le_newer Hg1cs1 Hg1g') /=.
  move: (mk_env_exp_newer_res H1 H2 H3) => Hg0ls.
  move: (mk_env_exp_newer_res H5 Hg0m0 Hg0tt) => Hg1ls0 .
  move: (newer_than_lits_le_newer Hg0ls Hg0g1) => Hg1ls .
  exact : (mk_env_mul_newer_cnf H4 Hg1tt Hg1ls Hg1ls0).
Qed.

Lemma mk_env_exp_newer_cnf_mod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_srem :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSrem w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_smod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSmod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_shl :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvShl w e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      newer_than_cnf g' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !newer_than_cnf_append.
  move: (mk_env_exp_newer_gen H1) => Hgg0 .
  move: (mk_env_exp_newer_gen H5) => Hg0g1.
  move: (mk_env_shl_newer_gen H4) => Hg1g'.
  (* newer_than_cnf g' cs0 *)
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => Hnew_g0cs0.
  move: (pos_leb_trans Hg0g1 Hg1g') => Hg0g'.
  rewrite (newer_than_cnf_le_newer Hnew_g0cs0 Hg0g') /=.
  (* newer_than_cnf g' cs1 *)
  move: (mk_env_exp_newer_vm H1 H2) => Hnew_g0m0.
  move: (newer_than_lit_le_newer H3 Hgg0) => {Hgg0} Hg0tt.
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hnew_g0m0 Hg0tt) => Hnew_g1cs1.
  rewrite (newer_than_cnf_le_newer Hnew_g1cs1 Hg1g') /=.
  (* newer_than_cnf g' cs2 *)
  move: (mk_env_exp_newer_res H1 H2 H3) => Hnew_g0ls.
  move: (newer_than_lit_le_newer Hg0tt Hg0g1) => Hg1tt .
  move: (mk_env_exp_newer_res H5 Hnew_g0m0 Hg0tt) => Hnew_g1ls0 .
  move: (newer_than_lits_le_newer Hnew_g0ls Hg0g1) => Hnew_g1ls .
  exact : (mk_env_shl_newer_cnf H4 Hg1tt Hnew_g1ls Hnew_g1ls0) .
Qed .

Lemma mk_env_exp_newer_cnf_lshr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvLshr w e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      newer_than_cnf g' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !newer_than_cnf_append.
  move: (mk_env_exp_newer_gen H1) => Hgg0 .
  move: (mk_env_exp_newer_gen H5) => Hg0g1.
  move: (mk_env_lshr_newer_gen H4) => Hg1g'.
  (* newer_than_cnf g' cs0 *)
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => Hnew_g0cs0.
  move: (pos_leb_trans Hg0g1 Hg1g') => Hg0g'.
  rewrite (newer_than_cnf_le_newer Hnew_g0cs0 Hg0g') /=.
  (* newer_than_cnf g' cs1 *)
  move: (mk_env_exp_newer_vm H1 H2) => Hnew_g0m0.
  move: (newer_than_lit_le_newer H3 Hgg0) => {Hgg0} Hg0tt.
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hnew_g0m0 Hg0tt) => Hnew_g1cs1.
  rewrite (newer_than_cnf_le_newer Hnew_g1cs1 Hg1g') /=.
  (* newer_than_cnf g' cs2 *)
  move: (mk_env_exp_newer_res H1 H2 H3) => Hnew_g0ls.
  move: (newer_than_lit_le_newer Hg0tt Hg0g1) => Hg1tt .
  move: (mk_env_exp_newer_res H5 Hnew_g0m0 Hg0tt) => Hnew_g1ls0 .
  move: (newer_than_lits_le_newer Hnew_g0ls Hg0g1) => Hnew_g1ls .
  exact : (mk_env_lshr_newer_cnf H4 Hg1tt Hnew_g1ls Hnew_g1ls0) .
Qed .

Lemma mk_env_exp_newer_cnf_ashr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (e1 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w.+1).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvAshr w e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      newer_than_cnf g' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !newer_than_cnf_append.
  move: (mk_env_exp_newer_gen H1) => Hgg0 .
  move: (mk_env_exp_newer_gen H5) => Hg0g1.
  move: (mk_env_ashr_newer_gen H4) => Hg1g'.
  (* newer_than_cnf g' cs0 *)
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => Hnew_g0cs0.
  move: (pos_leb_trans Hg0g1 Hg1g') => Hg0g'.
  rewrite (newer_than_cnf_le_newer Hnew_g0cs0 Hg0g') /=.
  (* newer_than_cnf g' cs1 *)
  move: (mk_env_exp_newer_vm H1 H2) => Hnew_g0m0.
  move: (newer_than_lit_le_newer H3 Hgg0) => {Hgg0} Hg0tt.
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hnew_g0m0 Hg0tt) => Hnew_g1cs1.
  rewrite (newer_than_cnf_le_newer Hnew_g1cs1 Hg1g') /=.
  (* newer_than_cnf g' cs2 *)
  move: (mk_env_exp_newer_res H1 H2 H3) => Hnew_g0ls.
  move: (newer_than_lit_le_newer Hg0tt Hg0g1) => Hg1tt .
  move: (mk_env_exp_newer_res H5 Hnew_g0m0 Hg0tt) => Hnew_g1ls0 .
  move: (newer_than_lits_le_newer Hnew_g0ls Hg0g1) => Hnew_g1ls .
  exact : (mk_env_ashr_newer_cnf H4 Hg1tt Hnew_g1ls Hnew_g1ls0) .
Qed .

Lemma mk_env_exp_newer_cnf_concat :
  forall (w0 w1 : nat),
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (e1 : QFBV64.exp w1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w1.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : (w1 + w0).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvConcat w0 w1 e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      newer_than_cnf g' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !newer_than_cnf_append.
  move: (mk_env_exp_newer_gen H1) => Hgg0 .
  move: (mk_env_exp_newer_gen H5) => Hg0g'.
  (* newer_than_cnf g' cs0 *)
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => Hnew_g0cs0.
  move: (pos_leb_trans Hgg0 Hg0g') => Hgg'.
  rewrite (newer_than_cnf_le_newer Hnew_g0cs0 Hg0g') /=.
  (* newer_than_cnf g' cs1 *)
  move: (mk_env_exp_newer_vm H1 H2) => Hnew_g0m0.
  move: (newer_than_lit_le_newer H3 Hgg0) => {Hgg0} Hg0tt.
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hnew_g0m0 Hg0tt) => Hnew_g'cs1.
  by rewrite Hnew_g'cs1 .
Qed .

Lemma mk_env_exp_newer_cnf_extract :
  forall (w i j : nat),
    forall (e : QFBV64.exp (j + (i - j + 1) + w)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (j + (i - j + 1) + w).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : (i - j + 1).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvExtract w i j e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      newer_than_cnf g' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !newer_than_cnf_append.
  move: (mk_env_exp_newer_gen H0) => Hgg0 .
  (* newer_than_cnf g' cs0 *)
  by rewrite (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .

Lemma mk_env_exp_newer_cnf_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV64.exp (w3 + w2 + w1)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      newer_than_cnf g' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !newer_than_cnf_append.
  move: (mk_env_exp_newer_gen H0) => Hgg0 .
  (* newer_than_cnf g' cs0 *)
  by rewrite (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .

Lemma mk_env_exp_newer_cnf_high :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (wl + wh).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (m : vm)
           (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
           (E' : env) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvHigh wh wl e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      newer_than_cnf g' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !newer_than_cnf_append.
  move: (mk_env_exp_newer_gen H0) => Hgg0 .
  (* newer_than_cnf g' cs0 *)
  by rewrite (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .

Lemma mk_env_exp_newer_cnf_low :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (wl + wh).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : wl.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvLow wh wl e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      newer_than_cnf g' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !newer_than_cnf_append.
  move: (mk_env_exp_newer_gen H0) => Hgg0 .
  (* newer_than_cnf g' cs0 *)
  by rewrite (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .

Lemma mk_env_exp_newer_cnf_zeroextend :
  forall (w n : nat),
    forall (e : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (m : vm) (s : QFBV64.State.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvZeroExtend w n e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !newer_than_cnf_append.
  move: (mk_env_exp_newer_gen H0) => Hgg0 .
  (* newer_than_cnf g' cs0 *)
  by rewrite (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .

Lemma mk_env_exp_newer_cnf_signextend :
  forall (w n : nat),
    forall (e : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (m : vm) (s : QFBV64.State.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w.+1 + n).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSignExtend w n e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      newer_than_cnf g' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !newer_than_cnf_append.
  move: (mk_env_exp_newer_gen H0) => Hgg0 .
  (* newer_than_cnf g' cs0 *)
  by rewrite (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .

Lemma mk_env_exp_newer_cnf_ite :
  forall (w : nat) (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
    forall (e : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
      forall (e0 : QFBV64.exp w),
        (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : w.-tuple literal),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
            newer_than_vm g m ->
            newer_than_lit g lit_tt ->
            newer_than_cnf g' cs) ->
        forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g (QFBV64.bvIte w b e e0) = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !newer_than_cnf_append.
  move: (mk_env_bexp_newer_gen H2) => Hgg0.
  move: (mk_env_exp_newer_gen H6) => Hg0g1.
  move: (mk_env_exp_newer_gen H5) => Hg1g2.
  move: (mk_env_ite_newer_gen H7) => Hg2g'.
  (* newer_than_cnf g' cs0 *)
  move: (H _ _ _ _ _ _ _ _ _ H2 H3 H4) => Hnew_g0cs0.
  move: (pos_leb_trans Hg0g1 Hg1g2) => Hg0g2.
  move: (pos_leb_trans Hg0g2 Hg2g') => Hg0g'.
  rewrite (newer_than_cnf_le_newer Hnew_g0cs0 Hg0g') /=.
  (* newer_than_cnf g' cs1 *)
  move: (mk_env_bexp_newer_vm H2 H3) => Hnew_g0m0.
  move: (newer_than_lit_le_newer H4 Hgg0) => Hg0tt.
  move: (H0 _ _ _ _ _ _ _ _ _ H6 Hnew_g0m0 Hg0tt) => Hnew_g1cs1.
  move: (pos_leb_trans Hg1g2 Hg2g') => Hg1g'.
  rewrite (newer_than_cnf_le_newer Hnew_g1cs1 Hg1g') /=.
  (* newer_than_cnf g' cs2 *)
  move: (mk_env_exp_newer_vm H6 Hnew_g0m0) => Hnew_g1m1.
  move: (newer_than_lit_le_newer Hg0tt Hg0g1) => Hg1tt.
  move: (H1 _ _ _ _ _ _ _ _ _ H5 Hnew_g1m1 Hg1tt) => Hnew_g2cs2.
  rewrite (newer_than_cnf_le_newer Hnew_g2cs2 Hg2g') /=.
  (* newer_than_cnf g' cs3 *)
  move: (mk_env_bexp_newer_res H2 H3 H4) => Hnew_g0l.
  move: (newer_than_lit_le_newer Hnew_g0l Hg0g2) => {Hnew_g0l} Hnew_g2l.
  move: (mk_env_exp_newer_res H6 Hnew_g0m0 Hg0tt) => Hnew_g1ls.
  move: (newer_than_lits_le_newer Hnew_g1ls Hg1g2) => {Hnew_g1ls} Hnew_g2ls.
  move: (mk_env_exp_newer_res H5 Hnew_g1m1 Hg1tt) => Hnew_g2ls0.
  rewrite (mk_env_ite_newer_cnf H7 Hnew_g2l Hnew_g2ls Hnew_g2ls0).
  done.
Qed.

Lemma mk_env_bexp_newer_cnf_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- <- _ Hnew_gm Hnew_gtt. done.
Qed.

Lemma mk_env_bexp_newer_cnf_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- <- _ Hnew_gm Hnew_gtt. done.
Qed.

Lemma mk_env_bexp_newer_cnf_eq :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvEq w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt. rewrite !newer_than_cnf_append.
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => {Hnew_g1cs1} Hnew_g2cs1.
  move: (mk_env_eq_newer_gen Heq) => H_g2og.
  move: (newer_than_cnf_le_newer Hnew_g2cs1 H_g2og) => {Hnew_g2cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (mk_env_exp_newer_gen Henv1) => H_gg1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (newer_than_cnf_le_newer Hnew_g2cs2 H_g2og) => {Hnew_g2cs2} Hnew_ogcs2.
  rewrite Hnew_ogcs2 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_exp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1ls1.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1g2) => {Hnew_g1ls1} Hnew_g2ls1.
  move: (mk_env_exp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2ls2.
  exact: (mk_env_eq_newer_cnf Heq Hnew_g2ls1 Hnew_g2ls2).
Qed.

Lemma mk_env_bexp_newer_cnf_ult :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUlt w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hult: (mk_env_ult E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt. rewrite !newer_than_cnf_append.
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => {Hnew_g1cs1} Hnew_g2cs1.
  move: (mk_env_ult_newer_gen Hult) => H_g2og.
  move: (newer_than_cnf_le_newer Hnew_g2cs1 H_g2og) => {Hnew_g2cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (mk_env_exp_newer_gen Henv1) => H_gg1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (newer_than_cnf_le_newer Hnew_g2cs2 H_g2og) => {Hnew_g2cs2} Hnew_ogcs2.
  rewrite Hnew_ogcs2 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_exp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1ls1.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1g2) => {Hnew_g1ls1} Hnew_g2ls1.
  move: (mk_env_exp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2ls2.
  move: (pos_leb_trans H_gg1 H_g1g2) => H_gg2.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg2) => Hnew_g2tt.
  exact: (mk_env_ult_newer_cnf Hult Hnew_g2tt Hnew_g2ls1 Hnew_g2ls2).
Qed.

Lemma mk_env_bexp_newer_cnf_ule :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUle w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hule: (mk_env_ule E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt. rewrite !newer_than_cnf_append.
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => {Hnew_g1cs1} Hnew_g2cs1.
  move: (mk_env_ule_newer_gen Hule) => H_g2og.
  move: (newer_than_cnf_le_newer Hnew_g2cs1 H_g2og) => {Hnew_g2cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (mk_env_exp_newer_gen Henv1) => H_gg1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (newer_than_cnf_le_newer Hnew_g2cs2 H_g2og) => {Hnew_g2cs2} Hnew_ogcs2.
  rewrite Hnew_ogcs2 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_exp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1ls1.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1g2) => {Hnew_g1ls1} Hnew_g2ls1.
  move: (mk_env_exp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2ls2.
  move: (pos_leb_trans H_gg1 H_g1g2) => H_gg2.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg2) => Hnew_g2tt.
  exact: (mk_env_ule_newer_cnf Hule Hnew_g2tt Hnew_g2ls1 Hnew_g2ls2).
Qed.

Lemma mk_env_bexp_newer_cnf_ugt :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUgt w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hugt: (mk_env_ugt E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt. rewrite !newer_than_cnf_append.
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => {Hnew_g1cs1} Hnew_g2cs1.
  move: (mk_env_ugt_newer_gen Hugt) => H_g2og.
  move: (newer_than_cnf_le_newer Hnew_g2cs1 H_g2og) => {Hnew_g2cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (mk_env_exp_newer_gen Henv1) => H_gg1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (newer_than_cnf_le_newer Hnew_g2cs2 H_g2og) => {Hnew_g2cs2} Hnew_ogcs2.
  rewrite Hnew_ogcs2 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_exp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1ls1.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1g2) => {Hnew_g1ls1} Hnew_g2ls1.
  move: (mk_env_exp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2ls2.
  move: (pos_leb_trans H_gg1 H_g1g2) => H_gg2.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg2) => Hnew_g2tt.
  exact: (mk_env_ugt_newer_cnf Hugt Hnew_g2tt Hnew_g2ls1 Hnew_g2ls2).
Qed.

Lemma mk_env_bexp_newer_cnf_uge :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUge w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Huge: (mk_env_uge E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt. rewrite !newer_than_cnf_append.
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => {Hnew_g1cs1} Hnew_g2cs1.
  move: (mk_env_uge_newer_gen Huge) => H_g2og.
  move: (newer_than_cnf_le_newer Hnew_g2cs1 H_g2og) => {Hnew_g2cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (mk_env_exp_newer_gen Henv1) => H_gg1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (newer_than_cnf_le_newer Hnew_g2cs2 H_g2og) => {Hnew_g2cs2} Hnew_ogcs2.
  rewrite Hnew_ogcs2 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_exp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1ls1.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1g2) => {Hnew_g1ls1} Hnew_g2ls1.
  move: (mk_env_exp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2ls2.
  move: (pos_leb_trans H_gg1 H_g1g2) => H_gg2.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg2) => Hnew_g2tt.
  exact: (mk_env_uge_newer_cnf Huge Hnew_g2tt Hnew_g2ls1 Hnew_g2ls2).
Qed.

Lemma mk_env_bexp_newer_cnf_slt :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSlt w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- <- _ Hgm Hgt.
  rewrite !newer_than_cnf_append.
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_slt_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  move: (pos_leb_trans Hgg1 Hg1g2) => Hgg2.
  move: (newer_than_lit_le_newer Hgt Hgg2) => Hg2t.
  exact: (mk_env_slt_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_sle :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSle w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- <- _ Hgm Hgt.
  rewrite !newer_than_cnf_append.
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_sle_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  move: (pos_leb_trans Hgg1 Hg1g2) => Hgg2.
  move: (newer_than_lit_le_newer Hgt Hgg2) => Hg2t.
  exact: (mk_env_sle_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_sgt :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSgt w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- <- _ Hgm Hgt.
  rewrite !newer_than_cnf_append.
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_sgt_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  move: (pos_leb_trans Hgg1 Hg1g2) => Hgg2.
  move: (newer_than_lit_le_newer Hgt Hgg2) => Hg2t.
  exact: (mk_env_sgt_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_sge :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSge w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- <- _ Hgm Hgt.
  rewrite !newer_than_cnf_append.
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_sge_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  move: (pos_leb_trans Hgg1 Hg1g2) => Hgg2.
  move: (newer_than_lit_le_newer Hgt Hgg2) => Hg2t.
  exact: (mk_env_sge_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_uaddo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUaddo w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Huaddo: (mk_env_uaddo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt. rewrite !newer_than_cnf_append.
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => {Hnew_g1cs1} Hnew_g2cs1.
  move: (mk_env_uaddo_newer_gen Huaddo) => H_g2og.
  move: (newer_than_cnf_le_newer Hnew_g2cs1 H_g2og) => {Hnew_g2cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (mk_env_exp_newer_gen Henv1) => H_gg1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (newer_than_cnf_le_newer Hnew_g2cs2 H_g2og) => {Hnew_g2cs2} Hnew_ogcs2.
  rewrite Hnew_ogcs2 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_exp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1ls1.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1g2) => {Hnew_g1ls1} Hnew_g2ls1.
  move: (mk_env_exp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2ls2.
  move: (pos_leb_trans H_gg1 H_g1g2) => H_gg2.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg2) => Hnew_g2tt.
  exact: (mk_env_uaddo_newer_cnf Huaddo Hnew_g2tt Hnew_g2ls1 Hnew_g2ls2).
Qed.

Lemma mk_env_bexp_newer_cnf_usubo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUsubo w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Husubo: (mk_env_usubo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt. rewrite !newer_than_cnf_append.
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => {Hnew_g1cs1} Hnew_g2cs1.
  move: (mk_env_usubo_newer_gen Husubo) => H_g2og.
  move: (newer_than_cnf_le_newer Hnew_g2cs1 H_g2og) => {Hnew_g2cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (mk_env_exp_newer_gen Henv1) => H_gg1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (newer_than_cnf_le_newer Hnew_g2cs2 H_g2og) => {Hnew_g2cs2} Hnew_ogcs2.
  rewrite Hnew_ogcs2 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_exp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1ls1.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1g2) => {Hnew_g1ls1} Hnew_g2ls1.
  move: (mk_env_exp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2ls2.
  move: (pos_leb_trans H_gg1 H_g1g2) => H_gg2.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg2) => Hnew_g2tt.
  exact: (mk_env_usubo_newer_cnf Husubo Hnew_g2tt Hnew_g2ls1 Hnew_g2ls2).
Qed.

Lemma mk_env_bexp_newer_cnf_umulo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUmulo w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Humulo: (mk_env_umulo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt. rewrite !newer_than_cnf_append.
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => {Hnew_g1cs1} Hnew_g2cs1.
  move: (mk_env_umulo_newer_gen Humulo) => H_g2og.
  move: (newer_than_cnf_le_newer Hnew_g2cs1 H_g2og) => {Hnew_g2cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (mk_env_exp_newer_gen Henv1) => H_gg1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (newer_than_cnf_le_newer Hnew_g2cs2 H_g2og) => {Hnew_g2cs2} Hnew_ogcs2.
  rewrite Hnew_ogcs2 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_exp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1ls1.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1g2) => {Hnew_g1ls1} Hnew_g2ls1.
  move: (mk_env_exp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2ls2.
  move: (pos_leb_trans H_gg1 H_g1g2) => H_gg2.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg2) => Hnew_g2tt.
  exact: (mk_env_umulo_newer_cnf Humulo Hnew_g2tt Hnew_g2ls1 Hnew_g2ls2).
Qed.

Lemma mk_env_bexp_newer_cnf_saddo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSaddo w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- <- _ Hgm Hgt.
  rewrite !newer_than_cnf_append.
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_saddo_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  move: (pos_leb_trans Hgg1 Hg1g2) => Hgg2.
  move: (newer_than_lit_le_newer Hgt Hgg2) => Hg2t.
  exact: (mk_env_saddo_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_ssubo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSsubo w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- <- _ Hgm Hgt.
  rewrite !newer_than_cnf_append.
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_ssubo_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  move: (pos_leb_trans Hgg1 Hg1g2) => Hgg2.
  move: (newer_than_lit_le_newer Hgt Hgg2) => Hg2t.
  exact: (mk_env_ssubo_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_smulo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSmulo w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ _ <- <- _ Hgm Hgt.
  rewrite !newer_than_cnf_append.
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_smulo_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  move: (pos_leb_trans Hgg1 Hg1g2) => Hgg2.
  move: (newer_than_lit_le_newer Hgt Hgg2) => Hg2t.
  exact: (mk_env_smulo_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_lneg :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvLneg b) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
  move=> e IH m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv: (mk_env_bexp m s E g e) => [[[[m1 E1] g1] cs1] lr1].
  case Hlneg: (mk_env_lneg E1 g1 lr1) => [[[oE og] ocs] olr].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt. rewrite newer_than_cnf_append.
  (* newer_than_cnf og cs1 *)
  move: (IH _ _ _ _ _ _ _ _ _ Henv Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (mk_env_lneg_newer_gen Hlneg) => H_g1og.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1og). move => {Hnew_g1cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_bexp_newer_res Henv Hnew_gm Hnew_gtt) => Hnew_g1lr1.
  exact: (mk_env_lneg_newer_cnf Hlneg Hnew_g1lr1).
Qed.


Lemma mk_env_bexp_newer_cnf_conj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case Hconj: (mk_env_conj E2 g2 lr1 lr2)=> [[[oE og] ocs] olr].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt. rewrite !newer_than_cnf_append.
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (mk_env_bexp_newer_gen Henv2) => H_g1g2.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => {Hnew_g1cs1} Hnew_g2cs1.
  move: (mk_env_conj_newer_gen Hconj) => H_g2og.
  move: (newer_than_cnf_le_newer Hnew_g2cs1 H_g2og) => {Hnew_g2cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og cs2 *)
  move: (mk_env_bexp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (mk_env_bexp_newer_gen Henv1) => H_gg1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (newer_than_cnf_le_newer Hnew_g2cs2 H_g2og) => {Hnew_g2cs2} Hnew_ogcs2.
  rewrite Hnew_ogcs2 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_bexp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1lr1.
  move: (newer_than_lit_le_newer Hnew_g1lr1 H_g1g2) => {Hnew_g1lr1} Hnew_g2lr1.
  move: (mk_env_bexp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2lr2.
  exact: (mk_env_conj_newer_cnf Hconj Hnew_g2lr1 Hnew_g2lr2).
Qed.

Lemma mk_env_bexp_newer_cnf_disj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvDisj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case Hdisj: (mk_env_disj E2 g2 lr1 lr2)=> [[[oE og] ocs] olr].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt. rewrite !newer_than_cnf_append.
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (mk_env_bexp_newer_gen Henv2) => H_g1g2.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => {Hnew_g1cs1} Hnew_g2cs1.
  move: (mk_env_disj_newer_gen Hdisj) => H_g2og.
  move: (newer_than_cnf_le_newer Hnew_g2cs1 H_g2og) => {Hnew_g2cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og cs2 *)
  move: (mk_env_bexp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (mk_env_bexp_newer_gen Henv1) => H_gg1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (newer_than_cnf_le_newer Hnew_g2cs2 H_g2og) => {Hnew_g2cs2} Hnew_ogcs2.
  rewrite Hnew_ogcs2 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_bexp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1lr1.
  move: (newer_than_lit_le_newer Hnew_g1lr1 H_g1g2) => {Hnew_g1lr1} Hnew_g2lr1.
  move: (mk_env_bexp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2lr2.
  exact: (mk_env_disj_newer_cnf Hdisj Hnew_g2lr1 Hnew_g2lr2).
Qed.

Corollary mk_env_exp_newer_cnf :
  forall w (e : QFBV64.exp w) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs
  with
    mk_env_bexp_newer_cnf :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs.
Proof.
  (* mk_env_exp_newer_cnf *)
  move=> w [] {w}.
  - exact: mk_env_exp_newer_cnf_var.
  - exact: mk_env_exp_newer_cnf_const.
  - move=> w e.
    move: (mk_env_exp_newer_cnf _ e) => IH.
    exact: (mk_env_exp_newer_cnf_not IH).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IH1 IH2.
    exact: (mk_env_exp_newer_cnf_and IH1 IH2).
  - move=> w e0 e1.
    move: (mk_env_exp_newer_cnf _ e0) (mk_env_exp_newer_cnf _ e1) => IHe0 IHe1.
    exact: (mk_env_exp_newer_cnf_or IHe0 IHe1).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IH1 IH2.
    exact: (mk_env_exp_newer_cnf_xor IH1 IH2).
  - move=> w e.
    move: (mk_env_exp_newer_cnf _ e) => IH.
    exact: (mk_env_exp_newer_cnf_neg IH).
  - move=> w e0 e1.
    move: (mk_env_exp_newer_cnf _ e0) (mk_env_exp_newer_cnf _ e1) => IHe0 IHe1.
    exact: mk_env_exp_newer_cnf_add.
  - move=> w e0 e1.
    move: (mk_env_exp_newer_cnf _ e0) (mk_env_exp_newer_cnf _ e1) => IHe0 IHe1.
    exact: (mk_env_exp_newer_cnf_sub IHe0 IHe1).
  - move=> w e0 e1.
    move: (mk_env_exp_newer_cnf _ e0) (mk_env_exp_newer_cnf _ e1) => IHe0 IHe1.
    exact: mk_env_exp_newer_cnf_mul.
  - exact: mk_env_exp_newer_cnf_mod.
  - exact: mk_env_exp_newer_cnf_srem.
  - exact: mk_env_exp_newer_cnf_smod.
  - move => w e0 e1 .
    exact: (mk_env_exp_newer_cnf_shl (mk_env_exp_newer_cnf _ e0)
                                     (mk_env_exp_newer_cnf _ e1)) .
  - move => w e0 e1 .
    exact: (mk_env_exp_newer_cnf_lshr (mk_env_exp_newer_cnf _ e0)
                                      (mk_env_exp_newer_cnf _ e1)) .
  - move => w e0 e1 .
    exact: (mk_env_exp_newer_cnf_ashr (mk_env_exp_newer_cnf _ e0)
                                      (mk_env_exp_newer_cnf _ e1)) .
  - move => w0 w1 e0 e1 .
    move : (mk_env_exp_newer_cnf _ e0) (mk_env_exp_newer_cnf _ e1)
    => IHe0 IHe1 .
    exact: (mk_env_exp_newer_cnf_concat IHe0 IHe1) .
  - move => w i j e .
    apply: mk_env_exp_newer_cnf_extract (mk_env_exp_newer_cnf _ e) .
  - move => w1 w2 w3 e .
    apply: mk_env_exp_newer_cnf_slice (mk_env_exp_newer_cnf _ e) .
  - move => wh wl e .
    apply: mk_env_exp_newer_cnf_high (mk_env_exp_newer_cnf _ e) .
  - move => wh wl e .
    apply: mk_env_exp_newer_cnf_low (mk_env_exp_newer_cnf _ e) .
  - move => w n e .
    apply: mk_env_exp_newer_cnf_zeroextend
             (mk_env_exp_newer_cnf _ e) .
  - move => w n e .
    apply: mk_env_exp_newer_cnf_signextend (mk_env_exp_newer_cnf _ e) .
  - move=> w c e1 e2.
    move: (mk_env_bexp_newer_cnf c)
            (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IHc IH1 IH2.
    exact: (mk_env_exp_newer_cnf_ite IHc IH1 IH2).
  (* mk_env_bexp_newer_cnf *)
  case.
  - exact: mk_env_bexp_newer_cnf_false.
  - exact: mk_env_bexp_newer_cnf_true.
  - move=> w e1 e2.
    move: (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_cnf_eq IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_cnf_ult IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_cnf_ule IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_cnf_ugt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_cnf_uge IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_cnf_slt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_cnf_sle IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_cnf_sgt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_cnf_sge IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_cnf_uaddo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_cnf_usubo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_cnf_umulo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_cnf_saddo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_cnf_ssubo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_cnf_smulo IH1 IH2).
  - move=> e.
    move: (mk_env_bexp_newer_cnf e) => IH.
    exact: (mk_env_bexp_newer_cnf_lneg IH).
  - move=> e1 e2.
    move: (mk_env_bexp_newer_cnf e1) (mk_env_bexp_newer_cnf e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_cnf_conj IH1 IH2).
  -  move=> e1 e2.
     move: (mk_env_bexp_newer_cnf e1) (mk_env_bexp_newer_cnf e2) => IH1 IH2.
     exact: (mk_env_bexp_newer_cnf_disj IH1 IH2).
Qed.



(* = mk_env_exp_consistent and mk_env_bexp_consistent = *)

Lemma mk_env_exp_consistent_var :
  forall (t : VarOrder.t) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : wordsize.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvVar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case Hfind: (VM.find v m).
  - case=> <- <- _ _ _ Hnew_gm Hcon. assumption.
  - case Henv: (mk_env_var E g (QFBV64.State.acc v s) v) => [[[E_v g_v] cs_v] lrs_v].
    case=> <- <- _ _ _ Hnew_gm Hcon. move=> x. rewrite /consistent1.
    case Hxv: (x == v).
    + rewrite (VM.Lemmas.find_add_eq _ _ Hxv). rewrite (eqP Hxv).
      exact: (mk_env_var_enc Henv).
    + move/negP: Hxv => Hxv. rewrite (VM.Lemmas.find_add_neq _ _ Hxv).
      move: (Hcon x). rewrite /consistent1.
      case Hfind_xm: (VM.find x m).
      * move=> Henc. move: (Hnew_gm x _ Hfind_xm) => Hnew.
        exact: (env_preserve_enc_bits (mk_env_var_preserve Henv) Hnew Henc).
      * done.
Qed.

Lemma mk_env_exp_consistent_const :
  forall (w0 : nat) (b : BITS w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConst w0 b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w bs m s E g m' E' g' cs lrs /=. case=> <- <- _ _ _ Hnew_gm Hcon.
  assumption.
Qed.

Lemma mk_env_exp_consistent_not :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvNot w e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_not_preserve Hmkr) => HpE1Er.
  exact: (env_preserve_consistent Hg1m1 HpE1Er Hcm1E1).
Qed.

Lemma mk_env_exp_consistent_and :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : w.-tuple literal),
        mk_env_exp m s E g (QFBV64.bvAnd w e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_and_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_exp_consistent_or :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : QFBV64.State.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvOr w e0 e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_exp_newer_vm H1 H2) => Hnew_g0m0.
  move: (mk_env_exp_newer_vm H5 Hnew_g0m0) => Hnew_g1m'.
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => Hm0E0 .
  move: (mk_env_or_preserve H4) => HE1E'g1 .
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hnew_g0m0 Hm0E0) => Hm'E1 .
  exact: (env_preserve_consistent Hnew_g1m' HE1E'g1 Hm'E1) .
Qed .

Lemma mk_env_exp_consistent_xor :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : w.-tuple literal),
        mk_env_exp m s E g (QFBV64.bvXor w e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_xor_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_exp_consistent_neg :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNeg w e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_neg_preserve Hmkr) => HpE1Er.
  exact: (env_preserve_consistent Hg1m1 HpE1Er Hcm1E1).
Qed.

Lemma mk_env_exp_consistent_add :
  forall (w0 : nat),
    forall (e : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAdd w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_exp_newer_vm H1 H2) => Hg0m0.
  move: (mk_env_exp_newer_vm H5 Hg0m0) => Hg1m'.
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => Hm0E0.
  move: (mk_env_add_preserve H4) => HE1E'g1.
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hg0m0 Hm0E0) => Hm'E1.
  exact: (env_preserve_consistent Hg1m' HE1E'g1 Hm'E1).
Qed.

Lemma mk_env_exp_consistent_sub :
  forall (w0 : nat),
    forall (e : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSub w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_exp_newer_vm H1 H2) => Hg0m0.
  move: (mk_env_exp_newer_vm H5 Hg0m0) => Hg1m'.
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => Hm0E0.
  move: (mk_env_sub_preserve H4) => HE1E'g1.
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hg0m0 Hm0E0) => Hm'E1.
  exact: (env_preserve_consistent Hg1m' HE1E'g1 Hm'E1).
Qed.

Lemma mk_env_exp_consistent_mul :
  forall (w0 : nat),
    forall (e : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMul w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_exp_newer_vm H1 H2) => Hg0m0.
  move: (mk_env_exp_newer_vm H5 Hg0m0) => Hg1m'.
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => Hm0E0.
  move: (mk_env_mul_preserve H4) => HE1E'g1.
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hg0m0 Hm0E0) => Hm'E1.
  exact: (env_preserve_consistent Hg1m' HE1E'g1 Hm'E1).
Qed.

Lemma mk_env_exp_consistent_mod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_srem :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSrem w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_smod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSmod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_shl :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvShl w e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_exp_newer_vm H1 H2) => Hnew_g0m0.
  move: (mk_env_exp_newer_vm H5 Hnew_g0m0) => Hnew_g1m'.
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => Hm0E0 .
  move: (mk_env_shl_preserve H4) => HE1E'g1 .
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hnew_g0m0 Hm0E0) => Hm'E1 .
  exact: (env_preserve_consistent Hnew_g1m' HE1E'g1 Hm'E1) .
Qed .

Lemma mk_env_exp_consistent_lshr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvLshr w e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_exp_newer_vm H1 H2) => Hnew_g0m0.
  move: (mk_env_exp_newer_vm H5 Hnew_g0m0) => Hnew_g1m'.
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => Hm0E0 .
  move: (mk_env_lshr_preserve H4) => HE1E'g1 .
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hnew_g0m0 Hm0E0) => Hm'E1 .
  exact: (env_preserve_consistent Hnew_g1m' HE1E'g1 Hm'E1) .
Qed .

Lemma mk_env_exp_consistent_ashr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e1 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w.+1).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvAshr w e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_exp_newer_vm H1 H2) => Hnew_g0m0.
  move: (mk_env_exp_newer_vm H5 Hnew_g0m0) => Hnew_g1m'.
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => Hm0E0 .
  move: (mk_env_ashr_preserve H4) => HE1E'g1 .
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hnew_g0m0 Hm0E0) => Hm'E1 .
  exact: (env_preserve_consistent Hnew_g1m' HE1E'g1 Hm'E1) .
Qed .

Lemma mk_env_exp_consistent_concat :
  forall (w0 w1 : nat),
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e1 : QFBV64.exp w1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w1.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : (w1 + w0).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvConcat w0 w1 e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_exp_newer_vm H1 H2) => Hnew_g0m0.
  move: (mk_env_exp_newer_vm H5 Hnew_g0m0) => Hnew_g'm'.
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => Hm0E0 .
  apply: (H0 _ _ _ _ _ _ _ _ _ H5 Hnew_g0m0 Hm0E0) .
Qed .

Lemma mk_env_exp_consistent_extract :
  forall (w i j : nat),
    forall (e : QFBV64.exp (j + (i - j + 1) + w)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (j + (i - j + 1) + w).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : (i - j + 1).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvExtract w i j e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .

Lemma mk_env_exp_consistent_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV64.exp (w3 + w2 + w1)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .

Lemma mk_env_exp_consistent_high :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (wl + wh).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm)
           (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
           (E' : env) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvHigh wh wl e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .

Lemma mk_env_exp_consistent_low :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (wl + wh).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : wl.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvLow wh wl e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .

Lemma mk_env_exp_consistent_zeroextend :
  forall (w n : nat),
    forall (e : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : (w + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvZeroExtend w n e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .

Lemma mk_env_exp_consistent_signextend :
  forall (w n : nat),
    forall (e : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : QFBV64.State.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w.+1 + n).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSignExtend w n e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .

Lemma mk_env_exp_consistent_ite :
  forall (w : nat) (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (e0 : QFBV64.exp w),
        (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : w.-tuple literal),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
            newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
        forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g (QFBV64.bvIte w b e e0) = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_bexp_newer_vm H2 H3) => Hnew_g0m0.
  move: (mk_env_exp_newer_vm H6 Hnew_g0m0) => Hnew_g1m1.
  move: (mk_env_exp_newer_vm H5 Hnew_g1m1) => Hnew_g2m'.
  apply: (env_preserve_consistent Hnew_g2m' (mk_env_ite_preserve H7)).
  apply: (H1 _ _ _ _ _ _ _ _ _ H5 Hnew_g1m1).
  apply: (H0 _ _ _ _ _ _ _ _ _ H6 Hnew_g0m0).
  exact: (H _ _ _ _ _ _ _ _ _ H2 H3 H4).
Qed.

Lemma mk_env_bexp_consistent_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> <- <- _ _ _. move=> _ H; exact: H.
Qed.

Lemma mk_env_bexp_consistent_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> <- <- _ _ _. move=> _ H; exact: H.
Qed.

Lemma mk_env_bexp_consistent_eq :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvEq w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_eq_preserve Heq)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_ult :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUlt w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hult: (mk_env_ult E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_ult_preserve Hult)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_ule :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUle w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hule: (mk_env_ule E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_ule_preserve Hule)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_ugt :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUgt w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hugt: (mk_env_ugt E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_ugt_preserve Hugt)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_uge :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUge w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Huge: (mk_env_uge E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_uge_preserve Huge)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_slt :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSlt w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_slt_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_sle :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSle w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_sle_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_sgt :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSgt w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_sgt_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_sge :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSge w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_sge_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_uaddo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUaddo w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Huaddo: (mk_env_uaddo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_uaddo_preserve Huaddo)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_usubo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUsubo w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Husubo: (mk_env_usubo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_usubo_preserve Husubo)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_umulo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUmulo w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Humulo: (mk_env_umulo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_umulo_preserve Humulo)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_saddo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSaddo w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_saddo_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_ssubo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSsubo w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_ssubo_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_smulo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSmulo w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_smulo_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_lneg :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvLneg b) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e IH m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv: (mk_env_bexp m s E g e)=> [[[[m1 E1] g1] cs1] lr1].
  case Hlneg: (mk_env_lneg E1 g1 lr1)=> [[[oE og] ocs] olr].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_bexp_newer_vm Henv Hnew) => Hnew1.
  apply: (env_preserve_consistent Hnew1 (mk_env_lneg_preserve Hlneg)).
  apply: (IH _ _ _ _ _ _ _ _ _ Henv Hnew). exact: Hcon.
Qed.

Lemma mk_env_bexp_consistent_conj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case Hconj: (mk_env_conj E2 g2 lr1 lr2)=> [[[oE og] ocs] olr].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_bexp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_bexp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_conj_preserve Hconj)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  apply: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew). exact: Hcon.
Qed.

Lemma mk_env_bexp_consistent_disj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvDisj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case Hdisj: (mk_env_disj E2 g2 lr1 lr2)=> [[[oE og] ocs] olr].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_bexp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_bexp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_disj_preserve Hdisj)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  apply: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew). exact: Hcon.
Qed.

Corollary mk_env_exp_consistent :
  forall w (e : QFBV64.exp w) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    consistent m E s -> consistent m' E' s
  with
    mk_env_bexp_consistent :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        consistent m E s ->
        consistent m' E' s.
Proof.
  (* mk_env_exp_consistent *)
  move=> w [] {w}.
  - exact: mk_env_exp_consistent_var.
  - exact: mk_env_exp_consistent_const.
  - move=> w e.
    move: (mk_env_exp_consistent _ e) => IH.
    exact: (mk_env_exp_consistent_not IH).
  - move=> w e1 e2.
    move: (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => IH1 IH2.
    exact: (mk_env_exp_consistent_and IH1 IH2).
  - move=> w e0 e1 .
    move: (mk_env_exp_consistent _ e0) (mk_env_exp_consistent _ e1) => IHe0 IHe1 .
    exact: (mk_env_exp_consistent_or IHe0 IHe1) .
  - move=> w e1 e2.
    move: (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => IH1 IH2.
    exact: (mk_env_exp_consistent_xor IH1 IH2).
  - move=> w e.
    move: (mk_env_exp_consistent _ e) => IH.
    exact: (mk_env_exp_consistent_neg IH).
  - move=> w e0 e1 .
    move: (mk_env_exp_consistent _ e0) (mk_env_exp_consistent _ e1) => IHe0 IHe1 .
    exact: mk_env_exp_consistent_add.
  - move=> w e0 e1 .
    move: (mk_env_exp_consistent _ e0) (mk_env_exp_consistent _ e1) => IHe0 IHe1.
    exact: (mk_env_exp_consistent_sub IHe0 IHe1).
  - move=> w e0 e1 .
    move: (mk_env_exp_consistent _ e0) (mk_env_exp_consistent _ e1) => IHe0 IHe1 .
    exact: mk_env_exp_consistent_mul.
  - exact: mk_env_exp_consistent_mod.
  - exact: mk_env_exp_consistent_srem.
  - exact: mk_env_exp_consistent_smod.
  - move => w e0 e1 .
    exact: (mk_env_exp_consistent_shl (mk_env_exp_consistent _ e0)
                                      (mk_env_exp_consistent _ e1)) .
  - move => w e0 e1 .
    exact: (mk_env_exp_consistent_lshr (mk_env_exp_consistent _ e0)
                                       (mk_env_exp_consistent _ e1)) .
  - move => w e0 e1 .
    exact: (mk_env_exp_consistent_ashr (mk_env_exp_consistent _ e0)
                                       (mk_env_exp_consistent _ e1)) .
  - move => w0 w1 e0 e1 .
    move: (mk_env_exp_consistent _ e0) (mk_env_exp_consistent _ e1)
    => IHe0 IHe1 .
    exact: (mk_env_exp_consistent_concat IHe0 IHe1) .
  - move => w i j e .
    apply: mk_env_exp_consistent_extract (mk_env_exp_consistent _ e) .
  - move => w1 w2 w3 e .
    apply: mk_env_exp_consistent_slice (mk_env_exp_consistent _ e) .
  - move => wh wl e .
    apply: mk_env_exp_consistent_high (mk_env_exp_consistent _ e) .
  - move => wh wl e .
    apply: mk_env_exp_consistent_low (mk_env_exp_consistent _ e) .
  - move => m n e .
    apply: mk_env_exp_consistent_zeroextend (mk_env_exp_consistent _ e) .
  - move => m n e .
    apply: mk_env_exp_consistent_signextend (mk_env_exp_consistent _ e) .
  - move=> w c e1 e2.
    move: (mk_env_bexp_consistent c)
            (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => IHc IH1 IH2.
    exact: (mk_env_exp_consistent_ite IHc IH1 IH2).
  (* mk_env_bexp_consistent *)
  case.
  - exact: mk_env_bexp_consistent_false.
  - exact: mk_env_bexp_consistent_true.
  - move=> w e1 e2.
    move: (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => IH1 IH2.
    exact: (mk_env_bexp_consistent_eq IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => ih1 ih2.
    exact: (mk_env_bexp_consistent_ult ih1 ih2).
  - move=> w e1 e2.
    move: (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => ih1 ih2.
    exact: (mk_env_bexp_consistent_ule ih1 ih2).
  - move=> w e1 e2.
    move: (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => ih1 ih2.
    exact: (mk_env_bexp_consistent_ugt ih1 ih2).
  - move=> w e1 e2.
    move: (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => ih1 ih2.
    exact: (mk_env_bexp_consistent_uge ih1 ih2).
  - move=> w e1 e2.
    move: (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => IH1 IH2.
    exact: (mk_env_bexp_consistent_slt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => IH1 IH2.
    exact: (mk_env_bexp_consistent_sle IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => IH1 IH2.
    exact: (mk_env_bexp_consistent_sgt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => IH1 IH2.
    exact: (mk_env_bexp_consistent_sge IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => IH1 IH2.
    exact: (mk_env_bexp_consistent_uaddo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => IH1 IH2.
    exact: (mk_env_bexp_consistent_usubo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => IH1 IH2.
    exact: (mk_env_bexp_consistent_umulo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => IH1 IH2.
    exact: (mk_env_bexp_consistent_saddo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => IH1 IH2.
    exact: (mk_env_bexp_consistent_ssubo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => IH1 IH2.
    exact: (mk_env_bexp_consistent_smulo IH1 IH2).
  - move=> e.
    move: (mk_env_bexp_consistent e) => IH.
    exact: (mk_env_bexp_consistent_lneg IH).
  - move=> e1 e2.
    move: (mk_env_bexp_consistent e1) (mk_env_bexp_consistent e2) => IH1 IH2.
    exact: (mk_env_bexp_consistent_conj IH1 IH2).
  - move=> e1 e2.
    move: (mk_env_bexp_consistent e1) (mk_env_bexp_consistent e2) => IH1 IH2.
    exact: (mk_env_bexp_consistent_disj IH1 IH2).
Qed.



(* = mk_env_exp_preserve and mk_env_bexp_preserve = *)

Lemma mk_env_exp_preserve_var :
  forall (t : VarOrder.t) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : wordsize.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvVar t) = (m', E', g', cs, lrs) -> env_preserve E E' g.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case Hfind: (VM.find v m).
  - case=> _ <- _ _ _. exact: env_preserve_refl.
  - case Henv: (mk_env_var E g (QFBV64.State.acc v s) v) => [[[E_v g_v] cs_v] lrs_v].
    case=> _ <- _ _ _. exact: (mk_env_var_preserve Henv).
Qed.

Lemma mk_env_exp_preserve_const :
  forall (w0 : nat) (b : BITS w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConst w0 b) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> w bs m s E g m' E' g' cs lrs /=. case=> _ <- _ _ _. exact: env_preserve_refl.
Qed.

Lemma mk_env_exp_preserve_not :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvNot w e1) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> w e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (mk_env_not_preserve Hmkr) => HpE1Erg1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (env_preserve_le HpE1Erg1 Hgg1) => HpE1Erg.
  exact: (env_preserve_trans HpEE1g HpE1Erg).
Qed.

Lemma mk_env_exp_preserve_and :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : w.-tuple literal),
        mk_env_exp m s E g (QFBV64.bvAnd w e1 e2) = (m', E', g', cs, lrs) ->
        env_preserve E E' g.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_and_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_exp_preserve_or :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvOr w e0 e1) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  rewrite /=; intros; dcase_hyps; subst .
  move: (H _ _ _ _ _ _ _ _ _ H1) => {H} HEE0g .
  move: (H0 _ _ _ _ _ _ _ _ _ H3) => {H0} HE0E1g0 .
  move: (mk_env_exp_newer_gen H1) => Hgg0 .
  move: (env_preserve_le HE0E1g0 Hgg0) => HE0E1g .
  move: (env_preserve_trans HEE0g HE0E1g)
  => {HEE0g HE0E1g0 HE0E1g} HEE1g .
  move: (mk_env_or_preserve H2) => HE1E'g1 .
  move: (mk_env_exp_newer_gen H3) => Hg0g1 .
  move: (env_preserve_le HE1E'g1 Hg0g1) => HE1E'g0 .
  move: (env_preserve_le HE1E'g0 Hgg0) => HE1E'g .
  exact: (env_preserve_trans HEE1g HE1E'g) .
Qed .

Lemma mk_env_exp_preserve_xor :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : w.-tuple literal),
        mk_env_exp m s E g (QFBV64.bvXor w e1 e2) = (m', E', g', cs, lrs) ->
        env_preserve E E' g.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_xor_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_exp_preserve_neg :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNeg w e1) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> w e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (mk_env_neg_preserve Hmkr) => HpE1Erg1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (env_preserve_le HpE1Erg1 Hgg1) => HpE1Erg.
  exact: (env_preserve_trans HpEE1g HpE1Erg).
Qed.

Lemma mk_env_exp_preserve_add :
    forall (w0 : nat),
    forall (e : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAdd w0 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (H _ _ _ _ _ _ _ _ _ H1) => {H} HEE0g.
  move: (H0 _ _ _ _ _ _ _ _ _ H3) => {H0} HE0E1g0.
  move: (mk_env_exp_newer_gen H1) => Hgg0.
  move: (env_preserve_le HE0E1g0 Hgg0) => HE0E1g.
  move: (env_preserve_trans HEE0g HE0E1g) => {HEE0g HE0E1g0 HE0E1g} HEE1g .
  move: (mk_env_add_preserve H2) => HE1E'g1.
  move: (mk_env_exp_newer_gen H3) => Hg0g1.
  move: (env_preserve_le HE1E'g1 Hg0g1) =>HE1E'g0.
  move: (env_preserve_le HE1E'g0 Hgg0) => HE1E'g.
  exact: (env_preserve_trans HEE1g HE1E'g).
Qed.

Lemma mk_env_exp_preserve_sub :
    forall (w0 : nat),
    forall (e : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSub w0 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (H _ _ _ _ _ _ _ _ _ H1) => {H} HEE0g.
  move: (H0 _ _ _ _ _ _ _ _ _ H3) => {H0} HE0E1g0.
  move: (mk_env_exp_newer_gen H1) => Hgg0.
  move: (env_preserve_le HE0E1g0 Hgg0) => HE0E1g.
  move: (env_preserve_trans HEE0g HE0E1g) => {HEE0g HE0E1g0 HE0E1g} HEE1g .
  move: (mk_env_sub_preserve H2) => HE1E'g1.
  move: (mk_env_exp_newer_gen H3) => Hg0g1.
  move: (env_preserve_le HE1E'g1 Hg0g1) =>HE1E'g0.
  move: (env_preserve_le HE1E'g0 Hgg0) => HE1E'g.
  exact: (env_preserve_trans HEE1g HE1E'g).
Qed.

Lemma mk_env_exp_preserve_mul :
  forall (w0 : nat),
    forall (e : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMul w0 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (H _ _ _ _ _ _ _ _ _ H1) => {H} HEE0g.
  move: (H0 _ _ _ _ _ _ _ _ _ H3) => {H0} HE0E1g0.
  move: (mk_env_exp_newer_gen H1) => Hgg0.
  move: (env_preserve_le HE0E1g0 Hgg0) => HE0E1g.
  move: (env_preserve_trans HEE0g HE0E1g) => {HEE0g HE0E1g0 HE0E1g} HEE1g .
  move: (mk_env_mul_preserve H2) => HE1E'g1.
  move: (mk_env_exp_newer_gen H3) => Hg0g1.
  move: (env_preserve_le HE1E'g1 Hg0g1) =>HE1E'g0.
  move: (env_preserve_le HE1E'g0 Hgg0) => HE1E'g.
  exact: (env_preserve_trans HEE1g HE1E'g).
Qed.

Lemma mk_env_exp_preserve_mod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMod w0 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_srem :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSrem w0 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_smod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSmod w0 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_shl :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvShl w e0 e1) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  rewrite /=; intros; dcase_hyps; subst .
  move: (H _ _ _ _ _ _ _ _ _ H1) => {H} HEE0g .
  move: (H0 _ _ _ _ _ _ _ _ _ H3) => {H0} HE0E1g0 .
  move: (mk_env_exp_newer_gen H1) => Hgg0 .
  move: (env_preserve_le HE0E1g0 Hgg0) => HE0E1g .
  move: (env_preserve_trans HEE0g HE0E1g)
  => {HEE0g HE0E1g0 HE0E1g} HEE1g .
  move: (mk_env_shl_preserve H2) => HE1E'g1 .
  move: (mk_env_exp_newer_gen H3) => Hg0g1 .
  move: (env_preserve_le HE1E'g1 Hg0g1) => HE1E'g0 .
  move: (env_preserve_le HE1E'g0 Hgg0) => HE1E'g .
  exact: (env_preserve_trans HEE1g HE1E'g) .
Qed .

Lemma mk_env_exp_preserve_lshr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvLshr w e0 e1) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  rewrite /=; intros; dcase_hyps; subst .
  move: (H _ _ _ _ _ _ _ _ _ H1) => {H} HEE0g .
  move: (H0 _ _ _ _ _ _ _ _ _ H3) => {H0} HE0E1g0 .
  move: (mk_env_exp_newer_gen H1) => Hgg0 .
  move: (env_preserve_le HE0E1g0 Hgg0) => HE0E1g .
  move: (env_preserve_trans HEE0g HE0E1g)
  => {HEE0g HE0E1g0 HE0E1g} HEE1g .
  move: (mk_env_lshr_preserve H2) => HE1E'g1 .
  move: (mk_env_exp_newer_gen H3) => Hg0g1 .
  move: (env_preserve_le HE1E'g1 Hg0g1) => HE1E'g0 .
  move: (env_preserve_le HE1E'g0 Hgg0) => HE1E'g .
  exact: (env_preserve_trans HEE1g HE1E'g) .
Qed .

Lemma mk_env_exp_preserve_ashr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e1 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w.+1).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvAshr w e0 e1) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  rewrite /=; intros; dcase_hyps; subst .
  move: (H _ _ _ _ _ _ _ _ _ H1) => {H} HEE0g .
  move: (H0 _ _ _ _ _ _ _ _ _ H3) => {H0} HE0E1g0 .
  move: (mk_env_exp_newer_gen H1) => Hgg0 .
  move: (env_preserve_le HE0E1g0 Hgg0) => HE0E1g .
  move: (env_preserve_trans HEE0g HE0E1g)
  => {HEE0g HE0E1g0 HE0E1g} HEE1g .
  move: (mk_env_ashr_preserve H2) => HE1E'g1 .
  move: (mk_env_exp_newer_gen H3) => Hg0g1 .
  move: (env_preserve_le HE1E'g1 Hg0g1) => HE1E'g0 .
  move: (env_preserve_le HE1E'g0 Hgg0) => HE1E'g .
  exact: (env_preserve_trans HEE1g HE1E'g) .
Qed .

Lemma mk_env_exp_preserve_concat :
  forall (w0 w1 : nat),
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e1 : QFBV64.exp w1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w1.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : (w1 + w0).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvConcat w0 w1 e0 e1) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (H _ _ _ _ _ _ _ _ _ H1) => {H} HEE0g .
  move: (H0 _ _ _ _ _ _ _ _ _ H3) => {H0} HE0E1g0 .
  move: (mk_env_exp_newer_gen H1) => Hgg0 .
  move: (env_preserve_le HE0E1g0 Hgg0) => HE0E'g .
  move: (env_preserve_trans HEE0g HE0E'g)
  => {HEE0g HE0E1g0 HE0E'g} HEE'g .
  done .
Qed .

Lemma mk_env_exp_preserve_extract :
  forall (w i j : nat),
    forall (e : QFBV64.exp (j + (i - j + 1) + w)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (j + (i - j + 1) + w).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : (i - j + 1).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvExtract w i j e) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_preserve_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV64.exp (w3 + w2 + w1)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_preserve_high :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (wl + wh).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm)
           (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
           (E' : env) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvHigh wh wl e) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_preserve_low :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (wl + wh).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : wl.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvLow wh wl e) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_preserve_zeroextend :
  forall (w n : nat),
    forall (e : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : QFBV64.State.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w + n).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvZeroExtend w n e) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_preserve_signextend :
  forall (w n : nat),
    forall (e : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : QFBV64.State.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w.+1 + n).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSignExtend w n e) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .

Lemma mk_env_exp_preserve_ite :
  forall (w : nat) (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        env_preserve E E' g) ->
    forall (e : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (e0 : QFBV64.exp w),
        (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : w.-tuple literal),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
        forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g (QFBV64.bvIte w b e e0) = (m', E', g', cs, lrs) ->
          env_preserve E E' g.
Proof.
  rewrite /=; intros; dcase_hyps; subst. move: (mk_env_ite_preserve H5) => Hpre_E2E'g2.
  move: (H1 _ _ _ _ _ _ _ _ _ H3) => Hpre_E1E2g1.
  move: (H0 _ _ _ _ _ _ _ _ _ H4) => Hpre_E0E1g0.
  move: (H _ _ _ _ _ _ _ _ _ H2) => Hpre_EE0g.
  move: (mk_env_bexp_newer_gen H2) => Hgg0. move: (mk_env_exp_newer_gen H4) => Hg0g1.
  move: (mk_env_exp_newer_gen H3) => Hg1g2. move: (pos_leb_trans Hgg0 Hg0g1) => Hgg1.
  move: (pos_leb_trans Hgg1 Hg1g2) => Hgg2.
  apply: (env_preserve_trans _ (env_preserve_le Hpre_E2E'g2 Hgg2)).
  apply: (env_preserve_trans _ (env_preserve_le Hpre_E1E2g1 Hgg1)).
  exact: (env_preserve_trans Hpre_EE0g (env_preserve_le Hpre_E0E1g0 Hgg0)).
Qed.

Lemma mk_env_bexp_preserve_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) -> env_preserve E E' g.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ <- _ _ _. exact: env_preserve_refl.
Qed.

Lemma mk_env_bexp_preserve_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) -> env_preserve E E' g.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ <- _ _ _. exact: env_preserve_refl.
Qed.

Lemma mk_env_bexp_preserve_eq :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvEq w e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv2)).
  exact: (mk_env_eq_preserve Heq).
Qed.

Lemma mk_env_bexp_preserve_ult :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUlt w e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hult: (mk_env_ult E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv2)).
  exact: (mk_env_ult_preserve Hult).
Qed.

Lemma mk_env_bexp_preserve_ule :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUle w e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hule: (mk_env_ule E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv2)).
  exact: (mk_env_ule_preserve Hule).
Qed.

Lemma mk_env_bexp_preserve_ugt :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUgt w e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hugt: (mk_env_ugt E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv2)).
  exact: (mk_env_ugt_preserve Hugt).
Qed.

Lemma mk_env_bexp_preserve_uge :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUge w e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Huge: (mk_env_uge E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv2)).
  exact: (mk_env_uge_preserve Huge).
Qed.

Lemma mk_env_bexp_preserve_slt :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSlt w e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_slt_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_bexp_preserve_sle :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSle w e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_sle_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_bexp_preserve_sgt :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSgt w e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_sgt_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_bexp_preserve_sge :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSge w e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_sge_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_bexp_preserve_uaddo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUaddo w e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Huaddo: (mk_env_uaddo E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv2)).
  exact: (mk_env_uaddo_preserve Huaddo).
Qed.

Lemma mk_env_bexp_preserve_usubo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUsubo w e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Husubo: (mk_env_usubo E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv2)).
  exact: (mk_env_usubo_preserve Husubo).
Qed.

Lemma mk_env_bexp_preserve_umulo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUmulo w e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Humulo: (mk_env_umulo E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv2)).
  exact: (mk_env_umulo_preserve Humulo).
Qed.

Lemma mk_env_bexp_preserve_saddo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSaddo w e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_saddo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_bexp_preserve_ssubo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSsubo w e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_ssubo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_bexp_preserve_smulo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSmulo w e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_smulo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_bexp_preserve_lneg :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvLneg b) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e IH m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv: (mk_env_bexp m s E g e) => [[[[m1 E1] g1] cs1] lr1].
  case Hlneg: (mk_env_lneg E1 g1 lr1) => [[[oE og] ocs] olr].
  case => _ <- _ _ _.
  apply: (env_preserve_trans (IH _ _ _ _ _ _ _ _ _ Henv)).
  apply: (env_preserve_le _ (mk_env_bexp_newer_gen Henv)).
  exact: (mk_env_lneg_preserve Hlneg).
Qed.

Lemma mk_env_bexp_preserve_conj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        env_preserve E E' g) ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case Hconj: (mk_env_conj E2 g2 lr1 lr2) => [[[oE og] ocs] olr].
  case => _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_bexp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_bexp_newer_gen Henv2)).
  exact: (mk_env_conj_preserve Hconj).
Qed.

Lemma mk_env_bexp_preserve_disj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        env_preserve E E' g) ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvDisj b b0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case Hdisj: (mk_env_disj E2 g2 lr1 lr2) => [[[oE og] ocs] olr].
  case => _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_bexp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_bexp_newer_gen Henv2)).
  exact: (mk_env_disj_preserve Hdisj).
Qed.

Corollary mk_env_exp_preserve :
  forall w (e : QFBV64.exp w) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    env_preserve E E' g
  with
    mk_env_bexp_preserve :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  (* mk_env_exp_preserve *)
  move=> w [] {w}.
  - exact: mk_env_exp_preserve_var.
  - exact: mk_env_exp_preserve_const.
  - move=> w e.
    move: (mk_env_exp_preserve _ e) => IH.
    exact: (mk_env_exp_preserve_not IH).
  - move=> w e1 e2.
    move: (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IH1 IH2.
    exact: (mk_env_exp_preserve_and IH1 IH2).
  - move => w e0 e1 .
    move: (mk_env_exp_preserve _ e0) (mk_env_exp_preserve _ e1) => IHe0 IHe1 .
    exact: (mk_env_exp_preserve_or IHe0 IHe1) .
  - move=> w e1 e2.
    move: (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IH1 IH2.
    exact: (mk_env_exp_preserve_xor IH1 IH2).
  - move=> w e.
    move: (mk_env_exp_preserve _ e) => IH.
    exact: (mk_env_exp_preserve_neg IH).
  - move => w e0 e1.
    move: (mk_env_exp_preserve _ e0) (mk_env_exp_preserve _ e1) => IHe0 IHe1.
    exact: mk_env_exp_preserve_add.
  - move => w e0 e1.
    move: (mk_env_exp_preserve _ e0) (mk_env_exp_preserve _ e1) => IHe0 IHe1.
    exact: (mk_env_exp_preserve_sub IHe0 IHe1).
  - move => w e0 e1.
    move: (mk_env_exp_preserve _ e0) (mk_env_exp_preserve _ e1) => IHe0 IHe1.
    exact: mk_env_exp_preserve_mul.
  - exact: mk_env_exp_preserve_mod.
  - exact: mk_env_exp_preserve_srem.
  - exact: mk_env_exp_preserve_smod.
  - move => w e0 e1 .
    exact: (mk_env_exp_preserve_shl (mk_env_exp_preserve _ e0)
                                    (mk_env_exp_preserve _ e1)) .
  - move => w e0 e1 .
    exact: (mk_env_exp_preserve_lshr (mk_env_exp_preserve _ e0)
                                     (mk_env_exp_preserve _ e1)) .
  - move => w e0 e1 .
    exact: (mk_env_exp_preserve_ashr (mk_env_exp_preserve _ e0)
                                     (mk_env_exp_preserve _ e1)) .
  - move => w0 w1 e0 e1 .
    move : (mk_env_exp_preserve _ e0) (mk_env_exp_preserve _ e1)
    => IHe0 IHe1 .
    exact: (mk_env_exp_preserve_concat IHe0 IHe1) .
  - move => w i j e .
    apply: mk_env_exp_preserve_extract (mk_env_exp_preserve _ e) .
  - move => w1 w2 w3 e .
    apply: mk_env_exp_preserve_slice (mk_env_exp_preserve _ e) .
  - move => wh wl e .
    apply: mk_env_exp_preserve_high (mk_env_exp_preserve _ e) .
  - move => wh wl e .
    apply: mk_env_exp_preserve_low (mk_env_exp_preserve _ e) .
  - move => w n e .
    apply : mk_env_exp_preserve_zeroextend
              (mk_env_exp_preserve _ e) .
  - move => w n e .
    apply: mk_env_exp_preserve_signextend (mk_env_exp_preserve _ e) .
  - move=> w c e1 e2.
    move: (mk_env_bexp_preserve c)
            (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IHc IH1 IH2.
    exact: (mk_env_exp_preserve_ite IHc IH1 IH2).
  (* mk_env_exp_preserve *)
  case.
  - exact: mk_env_bexp_preserve_false.
  - exact: mk_env_bexp_preserve_true.
  - move=> w e1 e2.
    move: (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_eq IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_ult IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_ule IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_ugt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_uge IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_slt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_sle IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_sgt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_sge IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_uaddo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_usubo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_umulo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_saddo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_ssubo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_smulo IH1 IH2).
  - move=> e.
    move: (mk_env_bexp_preserve e) => IH.
    exact: (mk_env_bexp_preserve_lneg IH).
  - move=> e1 e2.
    move: (mk_env_bexp_preserve e1) (mk_env_bexp_preserve e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_conj IH1 IH2).
  - move=> e1 e2.
    move: (mk_env_bexp_preserve e1) (mk_env_bexp_preserve e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_disj IH1 IH2).
Qed.



(* = mk_env_exp_sat and mk_env_bexp_sat = *)

Lemma mk_env_exp_sat_var :
  forall (t : VarOrder.t) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : wordsize.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvVar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case Hfind: (VM.find v m).
  - case=> _ <- _ <- _ Hnew_gm Hnew_gtt. done.
  - case Henv: (mk_env_var E g (QFBV64.State.acc v s) v) => [[[E_v g_v] cs_v] lrs_v].
    case=> _ <- _ <- _ Hnew_gm Hnew_gtt. exact: (mk_env_var_sat Henv).
Qed.

Lemma mk_env_exp_sat_const :
  forall (w0 : nat) (b : BITS w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConst w0 b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
  move=> w bs m s E g m' E' g' cs lrs /=. case=> _ <- _ <- _ Hnew_gm Hnew_gtt. done.
Qed.

Lemma mk_env_exp_sat_not :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvNot w e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt. rewrite !interp_cnf_append.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => HiE1c1.
  move: (mk_env_not_preserve Hmkr) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  exact: (mk_env_not_sat Hmkr Hg1l1).
Qed.

Lemma mk_env_exp_sat_and :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : w.-tuple literal),
        mk_env_exp m s E g (QFBV64.bvAnd w e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt. rewrite !interp_cnf_append.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_and_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  exact: (mk_env_and_sat Hmkr Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_sat_or :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvOr w e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      interp_cnf E' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !interp_cnf_append.
  move: (mk_env_exp_newer_gen H1) => Hgg0.
  move: (mk_env_exp_newer_gen H5) => Hg0g1.
  move: (mk_env_or_newer_gen H4) => Hg1g'.
  move: (mk_env_exp_newer_vm H1 H2) => Hg0m0.
  move: (mk_env_exp_newer_vm H5 Hg0m0) => Hg1m'.
  move: (newer_than_lit_le_newer H3 Hgg0) => Hg0tt.
  move: (newer_than_lit_le_newer Hg0tt Hg0g1) => Hg1tt.
  move: (mk_env_exp_newer_cnf H1 H2 H3) => Hg0cs0 .
  move: (mk_env_exp_newer_cnf H5 Hg0m0 Hg0tt) => Hg1cs1 .
  move: (mk_env_exp_preserve H1) => HEE0g .
  move: (mk_env_exp_preserve H5) => HE0E1g0 .
  move: (mk_env_or_preserve H4) => HE1E'g1 .
  (* interp_cnf E' cs0 *)
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => HE0cs0 .
  move: (env_preserve_trans HE0E1g0 (env_preserve_le HE1E'g1 Hg0g1)) => HE0E'g0 .
  rewrite (env_preserve_cnf HE0E'g0 Hg0cs0) HE0cs0 .
  (* interp_cnf E' cs1 *)
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hg0m0 Hg0tt) => HE1cs1 .
  rewrite (env_preserve_cnf HE1E'g1 Hg1cs1) HE1cs1 .
  (* interp_cnf E' cs2 *)
  move: (newer_than_lits_le_newer (mk_env_exp_newer_res H1 H2 H3) Hg0g1) => Hg1ls .
  move: (mk_env_exp_newer_res H5 Hg0m0 Hg0tt) => Hg1ls0 .
  exact: (mk_env_or_sat H4 Hg1ls Hg1ls0) => HE2cs2 .
Qed.

Lemma mk_env_exp_sat_xor :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e2 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : w.-tuple literal),
        mk_env_exp m s E g (QFBV64.bvXor w e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt. rewrite !interp_cnf_append.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_xor_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  exact: (mk_env_xor_sat Hmkr Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_sat_neg :
  forall (w : nat) (e1 : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNeg w e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
  move=> w e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt. rewrite !interp_cnf_append.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => HiE1c1.
  move: (mk_env_neg_preserve Hmkr) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  exact : (mk_env_neg_sat Hmkr (newer_than_lit_le_newer Hgt (mk_env_exp_newer_gen Hmke1)) Hg1l1).
Qed.

Lemma mk_env_exp_sat_add :
  forall (w0 : nat),
    forall (e : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
  forall (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAdd w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !interp_cnf_append.
  move: (mk_env_exp_newer_gen H1) => Hgg0.
  move: (mk_env_exp_newer_gen H5) => Hg0g1.
  move: (mk_env_add_newer_gen H4) => Hg1g'.
  move: (mk_env_exp_newer_vm H1 H2) => Hg0m0.
  move: (mk_env_exp_newer_vm H5 Hg0m0) => Hg1m'.
  move: (newer_than_lit_le_newer H3 Hgg0) => Hg0tt.
  move: (newer_than_lit_le_newer Hg0tt Hg0g1) => Hg1tt.
  move: (mk_env_exp_newer_cnf H1 H2 H3) => Hg0cs0.
  move: (mk_env_exp_newer_cnf H5 Hg0m0 Hg0tt) => Hg1cs1.
  move: (mk_env_exp_preserve H1) => HEE0g.
  move: (mk_env_exp_preserve H5) => HE0E1g0.
  move: (mk_env_add_preserve H4) => HE1E'g1.
  (* interp_cnf E' cs0 *)
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => HE0cs0.
  move: (env_preserve_trans HE0E1g0 (env_preserve_le HE1E'g1 Hg0g1)) => HE0E'g0 .
  rewrite (env_preserve_cnf HE0E'g0 Hg0cs0) HE0cs0.
  (* interp_cnf E' cs1 *)
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hg0m0 Hg0tt) => HE1cs1.
  rewrite (env_preserve_cnf HE1E'g1 Hg1cs1) HE1cs1.
  (* interp_cnf E' cs2 *)
  move: (newer_than_lits_le_newer (mk_env_exp_newer_res H1 H2 H3) Hg0g1) => Hg1ls.
  move: (mk_env_exp_newer_res H5 Hg0m0 Hg0tt) => Hg1ls0.
  exact: (mk_env_add_sat H4 Hg1tt Hg1ls Hg1ls0).
Qed.

Lemma mk_env_exp_sat_sub :
  forall (w0 : nat),
    forall (e : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
  forall (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSub w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
    rewrite /=; intros; dcase_hyps; subst. rewrite !interp_cnf_append.
  move: (mk_env_exp_newer_gen H1) => Hgg0.
  move: (mk_env_exp_newer_gen H5) => Hg0g1.
  move: (mk_env_sub_newer_gen H4) => Hg1g'.
  move: (mk_env_exp_newer_vm H1 H2) => Hg0m0.
  move: (mk_env_exp_newer_vm H5 Hg0m0) => Hg1m'.
  move: (newer_than_lit_le_newer H3 Hgg0) => Hg0tt.
  move: (newer_than_lit_le_newer Hg0tt Hg0g1) => Hg1tt.
  move: (mk_env_exp_newer_cnf H1 H2 H3) => Hg0cs0.
  move: (mk_env_exp_newer_cnf H5 Hg0m0 Hg0tt) => Hg1cs1.
  move: (mk_env_exp_preserve H1) => HEE0g.
  move: (mk_env_exp_preserve H5) => HE0E1g0.
  move: (mk_env_sub_preserve H4) => HE1E'g1.
  (* interp_cnf E' cs0 *)
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => HE0cs0.
  move: (env_preserve_trans HE0E1g0 (env_preserve_le HE1E'g1 Hg0g1)) => HE0E'g0 .
  rewrite (env_preserve_cnf HE0E'g0 Hg0cs0) HE0cs0.
  (* interp_cnf E' cs1 *)
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hg0m0 Hg0tt) => HE1cs1.
  rewrite (env_preserve_cnf HE1E'g1 Hg1cs1) HE1cs1.
  (* interp_cnf E' cs2 *)
  move: (newer_than_lits_le_newer (mk_env_exp_newer_res H1 H2 H3) Hg0g1) => Hg1ls.
  move: (mk_env_exp_newer_res H5 Hg0m0 Hg0tt) => Hg1ls0.
  exact: (mk_env_sub_sat H4 Hg1tt Hg1ls Hg1ls0).
Qed.

Lemma mk_env_exp_sat_mul :
  forall (w0 : nat),
    forall (e : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
  forall (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMul w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !interp_cnf_append.
  move: (mk_env_exp_newer_gen H1) => Hgg0.
  move: (mk_env_exp_newer_gen H5) => Hg0g1.
  move: (mk_env_mul_newer_gen H4) => Hg1g'.
  move: (mk_env_exp_newer_vm H1 H2) => Hg0m0.
  move: (mk_env_exp_newer_vm H5 Hg0m0) => Hg1m'.
  move: (newer_than_lit_le_newer H3 Hgg0) => Hg0tt.
  move: (newer_than_lit_le_newer Hg0tt Hg0g1) => Hg1tt.
  move: (mk_env_exp_newer_cnf H1 H2 H3) => Hg0cs0.
  move: (mk_env_exp_newer_cnf H5 Hg0m0 Hg0tt) => Hg1cs1.
  move: (mk_env_exp_preserve H1) => HEE0g.
  move: (mk_env_exp_preserve H5) => HE0E1g0.
  move: (mk_env_mul_preserve H4) => HE1E'g1.
  (* interp_cnf E' cs0 *)
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => HE0cs0.
  move: (env_preserve_trans HE0E1g0 (env_preserve_le HE1E'g1 Hg0g1)) => HE0E'g0 .
  rewrite (env_preserve_cnf HE0E'g0 Hg0cs0) HE0cs0.
  (* interp_cnf E' cs1 *)
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hg0m0 Hg0tt) => HE1cs1.
  rewrite (env_preserve_cnf HE1E'g1 Hg1cs1) HE1cs1.
  (* interp_cnf E' cs2 *)
  move: (newer_than_lits_le_newer (mk_env_exp_newer_res H1 H2 H3) Hg0g1) => Hg1ls.
  move: (mk_env_exp_newer_res H5 Hg0m0 Hg0tt) => Hg1ls0.
  exact: (mk_env_mul_sat H4 Hg1tt Hg1ls Hg1ls0).
Qed.

Lemma mk_env_exp_sat_mod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_srem :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSrem w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_smod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSmod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_shl :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvShl w e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      interp_cnf E' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !interp_cnf_append.
  move: (mk_env_exp_newer_gen H1) => Hgg0.
  move: (mk_env_exp_newer_gen H5) => Hg0g1.
  move: (mk_env_shl_newer_gen H4) => Hg1g'.
  move: (mk_env_exp_newer_vm H1 H2) => Hg0m0.
  move: (mk_env_exp_newer_vm H5 Hg0m0) => Hg1m'.
  move: (newer_than_lit_le_newer H3 Hgg0) => Hg0tt.
  move: (newer_than_lit_le_newer Hg0tt Hg0g1) => Hg1tt.
  move: (mk_env_exp_newer_cnf H1 H2 H3) => Hg0cs0 .
  move: (mk_env_exp_newer_cnf H5 Hg0m0 Hg0tt) => Hg1cs1 .
  move: (mk_env_exp_preserve H1) => HEE0g .
  move: (mk_env_exp_preserve H5) => HE0E1g0 .
  move: (mk_env_shl_preserve H4) => HE1E'g1 .
  (* interp_cnf E' cs0 *)
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => HE0cs0 .
  move: (env_preserve_trans HE0E1g0 (env_preserve_le HE1E'g1 Hg0g1)) => HE0E'g0 .
  rewrite (env_preserve_cnf HE0E'g0 Hg0cs0) HE0cs0 .
  (* interp_cnf E' cs1 *)
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hg0m0 Hg0tt) => HE1cs1 .
  rewrite (env_preserve_cnf HE1E'g1 Hg1cs1) HE1cs1 .
  (* interp_cnf E' cs2 *)
  move: (newer_than_lits_le_newer (mk_env_exp_newer_res H1 H2 H3) Hg0g1) => Hg1ls .
  move: (mk_env_exp_newer_res H5 Hg0m0 Hg0tt) => Hg1ls0 .
  exact: (mk_env_shl_sat H4 Hg1tt Hg1ls Hg1ls0) => HE2cs2 .
Qed .

Lemma mk_env_exp_sat_lshr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (e1 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvLshr w e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      interp_cnf E' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !interp_cnf_append.
  move: (mk_env_exp_newer_gen H1) => Hgg0.
  move: (mk_env_exp_newer_gen H5) => Hg0g1.
  move: (mk_env_lshr_newer_gen H4) => Hg1g'.
  move: (mk_env_exp_newer_vm H1 H2) => Hg0m0.
  move: (mk_env_exp_newer_vm H5 Hg0m0) => Hg1m'.
  move: (newer_than_lit_le_newer H3 Hgg0) => Hg0tt.
  move: (newer_than_lit_le_newer Hg0tt Hg0g1) => Hg1tt.
  move: (mk_env_exp_newer_cnf H1 H2 H3) => Hg0cs0 .
  move: (mk_env_exp_newer_cnf H5 Hg0m0 Hg0tt) => Hg1cs1 .
  move: (mk_env_exp_preserve H1) => HEE0g .
  move: (mk_env_exp_preserve H5) => HE0E1g0 .
  move: (mk_env_lshr_preserve H4) => HE1E'g1 .
  (* interp_cnf E' cs0 *)
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => HE0cs0 .
  move: (env_preserve_trans HE0E1g0 (env_preserve_le HE1E'g1 Hg0g1)) => HE0E'g0 .
  rewrite (env_preserve_cnf HE0E'g0 Hg0cs0) HE0cs0 .
  (* interp_cnf E' cs1 *)
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hg0m0 Hg0tt) => HE1cs1 .
  rewrite (env_preserve_cnf HE1E'g1 Hg1cs1) HE1cs1 .
  (* interp_cnf E' cs2 *)
  move: (newer_than_lits_le_newer (mk_env_exp_newer_res H1 H2 H3) Hg0g1) => Hg1ls .
  move: (mk_env_exp_newer_res H5 Hg0m0 Hg0tt) => Hg1ls0 .
  exact: (mk_env_lshr_sat H4 Hg1tt Hg1ls Hg1ls0) => HE2cs2 .
Qed .

Lemma mk_env_exp_sat_ashr :
  forall (w : nat),
    forall (e0 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (e1 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w.+1).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvAshr w e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      interp_cnf E' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !interp_cnf_append.
  move: (mk_env_exp_newer_gen H1) => Hgg0.
  move: (mk_env_exp_newer_gen H5) => Hg0g1.
  move: (mk_env_ashr_newer_gen H4) => Hg1g'.
  move: (mk_env_exp_newer_vm H1 H2) => Hg0m0.
  move: (mk_env_exp_newer_vm H5 Hg0m0) => Hg1m'.
  move: (newer_than_lit_le_newer H3 Hgg0) => Hg0tt.
  move: (newer_than_lit_le_newer Hg0tt Hg0g1) => Hg1tt.
  move: (mk_env_exp_newer_cnf H1 H2 H3) => Hg0cs0 .
  move: (mk_env_exp_newer_cnf H5 Hg0m0 Hg0tt) => Hg1cs1 .
  move: (mk_env_exp_preserve H1) => HEE0g .
  move: (mk_env_exp_preserve H5) => HE0E1g0 .
  move: (mk_env_ashr_preserve H4) => HE1E'g1 .
  (* interp_cnf E' cs0 *)
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => HE0cs0 .
  move: (env_preserve_trans HE0E1g0 (env_preserve_le HE1E'g1 Hg0g1)) => HE0E'g0 .
  rewrite (env_preserve_cnf HE0E'g0 Hg0cs0) HE0cs0 .
  (* interp_cnf E' cs1 *)
  move: (H0 _ _ _ _ _ _ _ _ _ H5 Hg0m0 Hg0tt) => HE1cs1 .
  rewrite (env_preserve_cnf HE1E'g1 Hg1cs1) HE1cs1 .
  (* interp_cnf E' cs2 *)
  move: (newer_than_lits_le_newer (mk_env_exp_newer_res H1 H2 H3) Hg0g1) => Hg1ls .
  move: (mk_env_exp_newer_res H5 Hg0m0 Hg0tt) => Hg1ls0 .
  exact: (mk_env_ashr_sat H4 Hg1tt Hg1ls Hg1ls0) => HE2cs2 .
Qed .

Lemma mk_env_exp_sat_concat :
  forall (w0 w1 : nat),
    forall (e0 : QFBV64.exp w0),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w0.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (e1 : QFBV64.exp w1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w1.-tuple literal),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : (w1 + w0).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvConcat w0 w1 e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      interp_cnf E' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !interp_cnf_append.
  move: (mk_env_exp_newer_gen H1) => Hgg0.
  move: (mk_env_exp_newer_gen H5) => Hg0g'.
  move: (mk_env_exp_newer_vm H1 H2) => Hg0m0.
  move: (mk_env_exp_newer_vm H5 Hg0m0) => Hg'm'.
  move: (newer_than_lit_le_newer H3 Hgg0) => Hg0tt.
  move: (newer_than_lit_le_newer Hg0tt Hg0g') => Hg'tt.
  move: (mk_env_exp_newer_cnf H1 H2 H3) => Hg0cs0 .
  move: (mk_env_exp_newer_cnf H5 Hg0m0 Hg0tt) => Hg'cs1 .
  move: (mk_env_exp_preserve H1) => HEE0g .
  move: (mk_env_exp_preserve H5) => HE0E'g0 .
  (* interp_cnf E' cs0 *)
  move: (H _ _ _ _ _ _ _ _ _ H1 H2 H3) => HE0cs0 .
  rewrite (env_preserve_cnf HE0E'g0 Hg0cs0) HE0cs0 .
  (* interp_cnf E' cs1 *)
  by rewrite (H0 _ _ _ _ _ _ _ _ _ H5 Hg0m0 Hg0tt) .
Qed .

Lemma mk_env_exp_sat_extract :
  forall (w i j : nat),
    forall (e : QFBV64.exp (j + (i - j + 1) + w)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (j + (i - j + 1) + w).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : (i - j + 1).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvExtract w i j e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      interp_cnf E' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !interp_cnf_append.
  by rewrite (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .

Lemma mk_env_exp_sat_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV64.exp (w3 + w2 + w1)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      interp_cnf E' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !interp_cnf_append.
  by rewrite (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .

Lemma mk_env_exp_sat_high :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (wl + wh).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (m : vm)
           (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
           (E' : env) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvHigh wh wl e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      interp_cnf E' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !interp_cnf_append.
  by rewrite (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .

Lemma mk_env_exp_sat_low :
  forall (wh wl : nat),
    forall (e : QFBV64.exp (wl + wh)),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (wl + wh).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : wl.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvLow wh wl e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      interp_cnf E' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !interp_cnf_append.
  by rewrite (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .

Lemma mk_env_exp_sat_zeroextend :
  forall (w n : nat),
    forall (e : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (m : vm) (s : QFBV64.State.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w + n).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvZeroExtend w n e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      interp_cnf E' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !interp_cnf_append.
  by rewrite (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .

Lemma mk_env_exp_sat_signextend :
  forall (w n : nat),
    forall (e : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w.+1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (m : vm) (s : QFBV64.State.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : (w.+1 + n).-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSignExtend w n e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      interp_cnf E' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !interp_cnf_append.
  by rewrite (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .

Lemma mk_env_exp_sat_ite :
  forall (w : nat) (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
      forall (e0 : QFBV64.exp w),
        (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : w.-tuple literal),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
            newer_than_vm g m ->
            newer_than_lit g lit_tt ->
            interp_cnf E' cs) ->
        forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g (QFBV64.bvIte w b e e0) = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !interp_cnf_append.
  move: (mk_env_bexp_newer_gen H2) => Hgg0.
  move: (mk_env_exp_newer_gen H6) => Hg0g1.
  move: (mk_env_exp_newer_gen H5) => Hg1g2.
  move: (mk_env_ite_newer_gen H7) => Hg2g'.
  move: (mk_env_bexp_newer_vm H2 H3) => Hg0m0.
  move: (mk_env_exp_newer_vm H6 Hg0m0) => Hg1m1.
  move: (mk_env_exp_newer_vm H5 Hg1m1) => Hg2m2.
  move: (newer_than_lit_le_newer H4 Hgg0) => Hg0tt.
  move: (newer_than_lit_le_newer Hg0tt Hg0g1) => Hg1tt.
  (* interp_cnf E' cs0 *)
  move: (mk_env_ite_preserve H7) => Hpre_E2E'g2.
  move: (env_preserve_le Hpre_E2E'g2 Hg1g2) => Hpre_E2E'g1.
  move: (mk_env_exp_preserve H5) => Hpre_E1E2g1.
  move: (env_preserve_trans Hpre_E1E2g1 Hpre_E2E'g1) => Hpre_E1E'g1.
  move: (mk_env_exp_preserve H6) => Hpre_E0E1g0.
  move: (env_preserve_le Hpre_E1E'g1 Hg0g1) => Hpre_E1E'g0.
  move: (env_preserve_trans Hpre_E0E1g0 Hpre_E1E'g0) => Hpre_E0E'g0.
  move: (mk_env_bexp_newer_cnf H2 H3 H4) => Hg0cs0.
  rewrite (@env_preserve_cnf E0 E' g0 cs0 Hpre_E0E'g0 Hg0cs0).
  rewrite (H _ _ _ _ _ _ _ _ _ H2 H3 H4) /=.
  (* interp_cnf E' cs1 *)
  move: (mk_env_exp_newer_cnf H6 Hg0m0 Hg0tt) => Hg1cs1.
  rewrite (@env_preserve_cnf E1 E' g1 cs1 Hpre_E1E'g1 Hg1cs1).
  rewrite (H0 _ _ _ _ _ _ _ _ _ H6 Hg0m0 Hg0tt) /=.
  (* interp_cnf E' cs2 *)
  move: (mk_env_exp_newer_cnf H5 Hg1m1 Hg1tt) => Hg2cs2.
  rewrite (@env_preserve_cnf E2 E' g2 cs2 Hpre_E2E'g2 Hg2cs2).
  rewrite (H1 _ _ _ _ _ _ _ _ _ H5 Hg1m1 Hg1tt) /=.
  (* interp_cnf E' cs3 *)
  move: (pos_leb_trans Hg0g1 Hg1g2) => Hg0g2.
  move: (mk_env_bexp_newer_res H2 H3 H4) => Hg0l.
  move: (newer_than_lit_le_newer Hg0l Hg0g2) => Hg2l.
  move: (mk_env_exp_newer_res H6 Hg0m0 Hg0tt) => Hg1ls.
  move: (newer_than_lits_le_newer Hg1ls Hg1g2) => Hg2ls.
  move: (mk_env_exp_newer_res H5 Hg1m1 Hg1tt) => Hg2ls0.
  rewrite (mk_env_ite_sat H7 Hg2l Hg2ls Hg2ls0).
  done.
Qed.

Lemma mk_env_bexp_sat_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ <- _ <- _ Hnew_gm Hnew_gtt. done.
Qed.

Lemma mk_env_bexp_sat_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ <- _ <- _ Hnew_gm Hnew_gtt. done.
Qed.

Lemma mk_env_bexp_sat_eq :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvEq w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 ls1 ls2) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hnew_gm Hnew_gtt. rewrite !interp_cnf_append.
  move: (mk_env_exp_preserve Henv2) => Hpre_E1E2g1.
  move: (mk_env_exp_newer_gen Henv1) => H_gg1.
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (mk_env_exp_newer_cnf Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => Hnew_g2cs1.
  move: (mk_env_exp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (mk_env_exp_newer_cnf Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (mk_env_exp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1ls1.
  move: (mk_env_exp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2ls2.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1g2) =>
  {H_g1g2 Hnew_g1ls1} Hnew_g2ls1.
  (* interp_cnf oE cs1 *)
  rewrite (env_preserve_cnf (mk_env_eq_preserve Heq) Hnew_g2cs1).
  rewrite (env_preserve_cnf Hpre_E1E2g1 Hnew_g1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) andTb.
  (* interp_cnf oE cs2 *)
  rewrite (env_preserve_cnf (mk_env_eq_preserve Heq) Hnew_g2cs2).
  rewrite (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) andTb.
  (* interp_cnf oE ocs *)
  exact: (mk_env_eq_sat Heq Hnew_g2ls1 Hnew_g2ls2).
Qed.

Lemma mk_env_bexp_sat_ult :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUlt w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hult: (mk_env_ult E2 g2 ls1 ls2) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hnew_gm Hnew_gtt. rewrite !interp_cnf_append.
  move: (mk_env_exp_preserve Henv2) => Hpre_E1E2g1.
  move: (mk_env_exp_newer_gen Henv1) => H_gg1.
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (mk_env_exp_newer_cnf Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => Hnew_g2cs1.
  move: (mk_env_exp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (mk_env_exp_newer_cnf Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (mk_env_exp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1ls1.
  move: (mk_env_exp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2ls2.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1g2) =>
  {H_g1g2 Hnew_g1ls1} Hnew_g2ls1.
  (* interp_cnf oE cs1 *)
  rewrite (env_preserve_cnf (mk_env_ult_preserve Hult) Hnew_g2cs1).
  rewrite (env_preserve_cnf Hpre_E1E2g1 Hnew_g1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) andTb.
  (* interp_cnf oE cs2 *)
  rewrite (env_preserve_cnf (mk_env_ult_preserve Hult) Hnew_g2cs2).
  rewrite (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) andTb.
  (* interp_cnf oE ocs *)
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (pos_leb_trans H_gg1 H_g1g2) => H_gg2.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg2) => Hnew_g2tt.
  exact: (mk_env_ult_sat Hult Hnew_g2tt Hnew_g2ls1 Hnew_g2ls2).
Qed.

Lemma mk_env_bexp_sat_ule :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUle w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hule: (mk_env_ule E2 g2 ls1 ls2) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hnew_gm Hnew_gtt. rewrite !interp_cnf_append.
  move: (mk_env_exp_preserve Henv2) => Hpre_E1E2g1.
  move: (mk_env_exp_newer_gen Henv1) => H_gg1.
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (mk_env_exp_newer_cnf Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => Hnew_g2cs1.
  move: (mk_env_exp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (mk_env_exp_newer_cnf Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (mk_env_exp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1ls1.
  move: (mk_env_exp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2ls2.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1g2) =>
  {H_g1g2 Hnew_g1ls1} Hnew_g2ls1.
  (* interp_cnf oE cs1 *)
  rewrite (env_preserve_cnf (mk_env_ule_preserve Hule) Hnew_g2cs1).
  rewrite (env_preserve_cnf Hpre_E1E2g1 Hnew_g1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) andTb.
  (* interp_cnf oE cs2 *)
  rewrite (env_preserve_cnf (mk_env_ule_preserve Hule) Hnew_g2cs2).
  rewrite (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) andTb.
  (* interp_cnf oE ocs *)
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (pos_leb_trans H_gg1 H_g1g2) => H_gg2.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg2) => Hnew_g2tt.
  exact: (mk_env_ule_sat Hule Hnew_g2tt Hnew_g2ls1 Hnew_g2ls2).
Qed.

Lemma mk_env_bexp_sat_ugt :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUgt w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hugt: (mk_env_ugt E2 g2 ls1 ls2) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hnew_gm Hnew_gtt. rewrite !interp_cnf_append.
  move: (mk_env_exp_preserve Henv2) => Hpre_E1E2g1.
  move: (mk_env_exp_newer_gen Henv1) => H_gg1.
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (mk_env_exp_newer_cnf Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => Hnew_g2cs1.
  move: (mk_env_exp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (mk_env_exp_newer_cnf Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (mk_env_exp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1ls1.
  move: (mk_env_exp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2ls2.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1g2) =>
  {H_g1g2 Hnew_g1ls1} Hnew_g2ls1.
  (* interp_cnf oE cs1 *)
  rewrite (env_preserve_cnf (mk_env_ugt_preserve Hugt) Hnew_g2cs1).
  rewrite (env_preserve_cnf Hpre_E1E2g1 Hnew_g1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) andTb.
  (* interp_cnf oE cs2 *)
  rewrite (env_preserve_cnf (mk_env_ugt_preserve Hugt) Hnew_g2cs2).
  rewrite (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) andTb.
  (* interp_cnf oE ocs *)
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (pos_leb_trans H_gg1 H_g1g2) => H_gg2.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg2) => Hnew_g2tt.
  exact: (mk_env_ugt_sat Hugt Hnew_g2tt Hnew_g2ls1 Hnew_g2ls2).
Qed.

Lemma mk_env_bexp_sat_uge :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUge w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Huge: (mk_env_uge E2 g2 ls1 ls2) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hnew_gm Hnew_gtt. rewrite !interp_cnf_append.
  move: (mk_env_exp_preserve Henv2) => Hpre_E1E2g1.
  move: (mk_env_exp_newer_gen Henv1) => H_gg1.
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (mk_env_exp_newer_cnf Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => Hnew_g2cs1.
  move: (mk_env_exp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (mk_env_exp_newer_cnf Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (mk_env_exp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1ls1.
  move: (mk_env_exp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2ls2.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1g2) =>
  {H_g1g2 Hnew_g1ls1} Hnew_g2ls1.
  (* interp_cnf oE cs1 *)
  rewrite (env_preserve_cnf (mk_env_uge_preserve Huge) Hnew_g2cs1).
  rewrite (env_preserve_cnf Hpre_E1E2g1 Hnew_g1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) andTb.
  (* interp_cnf oE cs2 *)
  rewrite (env_preserve_cnf (mk_env_uge_preserve Huge) Hnew_g2cs2).
  rewrite (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) andTb.
  (* interp_cnf oE ocs *)
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (pos_leb_trans H_gg1 H_g1g2) => H_gg2.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg2) => Hnew_g2tt.
  exact: (mk_env_uge_sat Huge Hnew_g2tt Hnew_g2ls1 Hnew_g2ls2).
Qed.

Lemma mk_env_bexp_sat_slt :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSlt w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ <- _ Hgm Hgt. rewrite !interp_cnf_append.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_slt_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  exact: (mk_env_slt_sat Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_sat_sle :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSle w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ <- _ Hgm Hgt. rewrite !interp_cnf_append.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_sle_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  exact: (mk_env_sle_sat Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_sat_sgt :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSgt w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ <- _ Hgm Hgt. rewrite !interp_cnf_append.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_sgt_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  exact: (mk_env_sgt_sat Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_sat_sge :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSge w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ <- _ Hgm Hgt. rewrite !interp_cnf_append.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_sge_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  exact: (mk_env_sge_sat Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_sat_uaddo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUaddo w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Huaddo: (mk_env_uaddo E2 g2 ls1 ls2) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hnew_gm Hnew_gtt. rewrite !interp_cnf_append.
  move: (mk_env_exp_preserve Henv2) => Hpre_E1E2g1.
  move: (mk_env_exp_newer_gen Henv1) => H_gg1.
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (mk_env_exp_newer_cnf Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => Hnew_g2cs1.
  move: (mk_env_exp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (mk_env_exp_newer_cnf Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (mk_env_exp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1ls1.
  move: (mk_env_exp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2ls2.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1g2) =>
  {H_g1g2 Hnew_g1ls1} Hnew_g2ls1.
  (* interp_cnf oE cs1 *)
  rewrite (env_preserve_cnf (mk_env_uaddo_preserve Huaddo) Hnew_g2cs1).
  rewrite (env_preserve_cnf Hpre_E1E2g1 Hnew_g1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) andTb.
  (* interp_cnf oE cs2 *)
  rewrite (env_preserve_cnf (mk_env_uaddo_preserve Huaddo) Hnew_g2cs2).
  rewrite (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) andTb.
  (* interp_cnf oE ocs *)
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (pos_leb_trans H_gg1 H_g1g2) => H_gg2.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg2) => Hnew_g2tt.
  exact: (mk_env_uaddo_sat Huaddo Hnew_g2tt Hnew_g2ls1 Hnew_g2ls2).
Qed.

Lemma mk_env_bexp_sat_usubo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUsubo w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Husubo: (mk_env_usubo E2 g2 ls1 ls2) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hnew_gm Hnew_gtt. rewrite !interp_cnf_append.
  move: (mk_env_exp_preserve Henv2) => Hpre_E1E2g1.
  move: (mk_env_exp_newer_gen Henv1) => H_gg1.
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (mk_env_exp_newer_cnf Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => Hnew_g2cs1.
  move: (mk_env_exp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (mk_env_exp_newer_cnf Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (mk_env_exp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1ls1.
  move: (mk_env_exp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2ls2.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1g2) =>
  {H_g1g2 Hnew_g1ls1} Hnew_g2ls1.
  (* interp_cnf oE cs1 *)
  rewrite (env_preserve_cnf (mk_env_usubo_preserve Husubo) Hnew_g2cs1).
  rewrite (env_preserve_cnf Hpre_E1E2g1 Hnew_g1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) andTb.
  (* interp_cnf oE cs2 *)
  rewrite (env_preserve_cnf (mk_env_usubo_preserve Husubo) Hnew_g2cs2).
  rewrite (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) andTb.
  (* interp_cnf oE ocs *)
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (pos_leb_trans H_gg1 H_g1g2) => H_gg2.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg2) => Hnew_g2tt.
  exact: (mk_env_usubo_sat Husubo Hnew_g2tt Hnew_g2ls1 Hnew_g2ls2).
Qed.

Lemma mk_env_bexp_sat_umulo :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvUmulo w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Humulo: (mk_env_umulo E2 g2 ls1 ls2) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hnew_gm Hnew_gtt. rewrite !interp_cnf_append.
  move: (mk_env_exp_preserve Henv2) => Hpre_E1E2g1.
  move: (mk_env_exp_newer_gen Henv1) => H_gg1.
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (mk_env_exp_newer_cnf Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => Hnew_g2cs1.
  move: (mk_env_exp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (mk_env_exp_newer_cnf Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (mk_env_exp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1ls1.
  move: (mk_env_exp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2ls2.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1g2) =>
  {H_g1g2 Hnew_g1ls1} Hnew_g2ls1.
  (* interp_cnf oE cs1 *)
  rewrite (env_preserve_cnf (mk_env_umulo_preserve Humulo) Hnew_g2cs1).
  rewrite (env_preserve_cnf Hpre_E1E2g1 Hnew_g1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) andTb.
  (* interp_cnf oE cs2 *)
  rewrite (env_preserve_cnf (mk_env_umulo_preserve Humulo) Hnew_g2cs2).
  rewrite (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) andTb.
  (* interp_cnf oE ocs *)
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (pos_leb_trans H_gg1 H_g1g2) => H_gg2.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg2) => Hnew_g2tt.
  exact: (mk_env_umulo_sat Humulo Hnew_g2tt Hnew_g2ls1 Hnew_g2ls2).
Qed.

Lemma mk_env_bexp_sat_saddo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSaddo w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ <- _ Hgm Hgt. rewrite !interp_cnf_append.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_saddo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  exact: (mk_env_saddo_sat Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_sat_ssubo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSsubo w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ <- _ Hgm Hgt. rewrite !interp_cnf_append.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_ssubo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  exact: (mk_env_ssubo_sat Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_sat_smulo :
  forall (w : nat) (e1 : QFBV64.exp w.+1),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.+1.-tuple literal),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e2 : QFBV64.exp w.+1),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.+1.-tuple literal),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvSmulo w e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ <- _ Hgm Hgt. rewrite !interp_cnf_append.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_smulo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  exact: (mk_env_smulo_sat Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_sat_lneg :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvLneg b) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> e IH m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv: (mk_env_bexp m s E g e) => [[[[m1 E1] g1] cs1] lr1].
  case Hlneg: (mk_env_lneg E1 g1 lr1) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hnew_gm Hnew_gtt. rewrite !interp_cnf_append.
  move: (mk_env_bexp_newer_gen Henv) => H_gg1.
  move: (mk_env_bexp_newer_cnf Henv Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (mk_env_bexp_newer_vm Henv Hnew_gm) => Hnew_g1m1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => {H_gg1} Hnew_g1tt.
  move: (mk_env_bexp_newer_res Henv Hnew_gm Hnew_gtt) => Hnew_g1lr1.
  (* interp_cnf E2 cs1 *)
  rewrite (env_preserve_cnf (mk_env_lneg_preserve Hlneg) Hnew_g1cs1).
  rewrite (IH _ _ _ _ _ _ _ _ _ Henv Hnew_gm Hnew_gtt) andTb.
  (* interp_cnf oE ocs *)
  exact: (mk_env_lneg_sat Hlneg Hnew_g1lr1).
Qed.

Lemma mk_env_bexp_sat_conj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case Hconj: (mk_env_conj E2 g2 lr1 lr2) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hnew_gm Hnew_gtt. rewrite !interp_cnf_append.
  move: (mk_env_bexp_preserve Henv2) => Hpre_E1E2g1.
  move: (mk_env_bexp_newer_gen Henv1) => H_gg1.
  move: (mk_env_bexp_newer_gen Henv2) => H_g1g2.
  move: (mk_env_bexp_newer_cnf Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => Hnew_g2cs1.
  move: (mk_env_bexp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => {H_gg1} Hnew_g1tt.
  move: (mk_env_bexp_newer_cnf Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (mk_env_bexp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1lr1.
  move: (mk_env_bexp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2lr2.
  move: (newer_than_lit_le_newer Hnew_g1lr1 H_g1g2) => {H_g1g2 Hnew_g1lr1} Hnew_g2lr1.
  (* interp_cnf E2 cs1 *)
  rewrite (env_preserve_cnf (mk_env_conj_preserve Hconj) Hnew_g2cs1).
  rewrite (env_preserve_cnf Hpre_E1E2g1 Hnew_g1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) andTb.
  (* interp_cnf E2 cs2 *)
  rewrite (env_preserve_cnf (mk_env_conj_preserve Hconj) Hnew_g2cs2).
  rewrite (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) andTb.
  (* interp_cnf oE ocs *)
  exact: (mk_env_conj_sat Hconj Hnew_g2lr1 Hnew_g2lr2).
Qed.

Lemma mk_env_bexp_sat_disj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvDisj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case Hdisj: (mk_env_disj E2 g2 lr1 lr2) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hnew_gm Hnew_gtt. rewrite !interp_cnf_append.
  move: (mk_env_bexp_preserve Henv2) => Hpre_E1E2g1.
  move: (mk_env_bexp_newer_gen Henv1) => H_gg1.
  move: (mk_env_bexp_newer_gen Henv2) => H_g1g2.
  move: (mk_env_bexp_newer_cnf Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => Hnew_g2cs1.
  move: (mk_env_bexp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => {H_gg1} Hnew_g1tt.
  move: (mk_env_bexp_newer_cnf Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (mk_env_bexp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1lr1.
  move: (mk_env_bexp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2lr2.
  move: (newer_than_lit_le_newer Hnew_g1lr1 H_g1g2) => {H_g1g2 Hnew_g1lr1} Hnew_g2lr1.
  (* interp_cnf E2 cs1 *)
  rewrite (env_preserve_cnf (mk_env_disj_preserve Hdisj) Hnew_g2cs1).
  rewrite (env_preserve_cnf Hpre_E1E2g1 Hnew_g1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) andTb.
  (* interp_cnf E2 cs2 *)
  rewrite (env_preserve_cnf (mk_env_disj_preserve Hdisj) Hnew_g2cs2).
  rewrite (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) andTb.
  (* interp_cnf oE ocs *)
  exact: (mk_env_disj_sat Hdisj Hnew_g2lr1 Hnew_g2lr2).
Qed.

Corollary mk_env_exp_sat :
  forall w (e : QFBV64.exp w) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs
  with
    mk_env_bexp_sat :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        interp_cnf E' cs.
Proof.
  (* mk_env_exp_sat *)
  move=> w [] {w}.
  - exact: mk_env_exp_sat_var.
  - exact: mk_env_exp_sat_const.
  - move=> w e.
    move: (mk_env_exp_sat _ e) => IH.
    exact: (mk_env_exp_sat_not IH).
  - move=> w e1 e2.
    move: (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IH1 IH2.
    exact: (mk_env_exp_sat_and IH1 IH2).
  - move=> w e0 e1 .
    move: (mk_env_exp_sat _ e0) (mk_env_exp_sat _ e1) => IHe0 IHe1 .
    exact: (mk_env_exp_sat_or IHe0 IHe1) .
  - move=> w e1 e2.
    move: (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IH1 IH2.
    exact: (mk_env_exp_sat_xor IH1 IH2).
  - move=> w e.
    move: (mk_env_exp_sat _ e) => IH.
    exact: (mk_env_exp_sat_neg IH).
  - move=> w e0 e1 .
    move: (mk_env_exp_sat _ e0) (mk_env_exp_sat _ e1) => IHe0 IHe1 .
    exact: mk_env_exp_sat_add.
  - move=> w e0 e1 .
    move: (mk_env_exp_sat _ e0) (mk_env_exp_sat _ e1) => IHe0 IHe1.
    exact: (mk_env_exp_sat_sub IHe0 IHe1).
  - move=> w e0 e1 .
    move: (mk_env_exp_sat _ e0) (mk_env_exp_sat _ e1) => IHe0 IHe1 .
    exact: mk_env_exp_sat_mul.
  - exact: mk_env_exp_sat_mod.
  - exact: mk_env_exp_sat_srem.
  - exact: mk_env_exp_sat_smod.
  - move => w e0 e1 .
    exact: (mk_env_exp_sat_shl (mk_env_exp_sat _ e0) (mk_env_exp_sat _ e1)) .
  - move => w e0 e1 .
    exact: (mk_env_exp_sat_lshr (mk_env_exp_sat _ e0) (mk_env_exp_sat _ e1)) .
  - move => w e0 e1 .
    exact: (mk_env_exp_sat_ashr (mk_env_exp_sat _ e0) (mk_env_exp_sat _ e1)) .
  - move => w0 w1 e0 e1 .
    move: (mk_env_exp_sat _ e0) (mk_env_exp_sat _ e1) => IHe0 IHe1 .
    exact: (mk_env_exp_sat_concat IHe0 IHe1) .
  - move => w i j e .
    apply: mk_env_exp_sat_extract (mk_env_exp_sat _ e) .
  - move => w1 w2 w3 e .
    apply: mk_env_exp_sat_slice (mk_env_exp_sat _ e) .
  - move => wh wl e .
    apply: mk_env_exp_sat_high (mk_env_exp_sat _ e) .
  - move => wh wl e .
    apply: mk_env_exp_sat_low (mk_env_exp_sat _ e) .
  - move => w n e .
    apply : mk_env_exp_sat_zeroextend (mk_env_exp_sat _ e) .
  - move => w n e .
    apply : mk_env_exp_sat_signextend (mk_env_exp_sat _ e) .
  - move=> w c e1 e2.
    move: (mk_env_bexp_sat c)
            (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IHc IH1 IH2.
    exact: (mk_env_exp_sat_ite IHc IH1 IH2).
  (* mk_env_exp_sat *)
  case.
  - exact: mk_env_bexp_sat_false.
  - exact: mk_env_bexp_sat_true.
  - move=> w e1 e2.
    move: (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_eq IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_ult IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_ule IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_ugt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_uge IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_slt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_sle IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_sgt IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_sge IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_uaddo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_usubo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_umulo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_saddo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_ssubo IH1 IH2).
  - move=> w e1 e2.
    move: (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_smulo IH1 IH2).
  - move=> e.
    move: (mk_env_bexp_sat e) => IH.
    exact: (mk_env_bexp_sat_lneg IH).
  - move=> e1 e2.
    move: (mk_env_bexp_sat e1) (mk_env_bexp_sat e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_conj IH1 IH2).
  - move=> e1 e2.
    move: (mk_env_bexp_sat e1) (mk_env_bexp_sat e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_disj IH1 IH2).
Qed.



(* ===== mk_env ===== *)

Definition init_vm := VM.empty (wordsize.-tuple literal).
Definition init_gen := (var_tt + 1)%positive.
Definition init_env : env := fun _ => true.

Lemma init_newer_than_vm :
  newer_than_vm init_gen init_vm.
Proof.
  done.
Qed.

Lemma init_newer_than_tt :
  newer_than_lit init_gen lit_tt.
Proof.
  done.
Qed.

Lemma init_tt :
  interp_lit init_env lit_tt.
Proof.
  done.
Qed.

Definition mk_env (s : QFBV64.State.t) (e : QFBV64.bexp) : env :=
  let '(m', E', g, cs, lr) := mk_env_bexp init_vm s init_env init_gen e in
  E'.

Lemma init_consistent :
  forall s, consistent init_vm init_env s.
Proof.
  move=> s x. rewrite /consistent1 /init_vm. rewrite VM.Lemmas.empty_o. done.
Qed.

Lemma mk_env_consistent :
  forall s e m g cs lr,
    bit_blast_bexp init_vm init_gen e = (m, g, cs, lr) ->
    consistent m (mk_env s e) s.
Proof.
  move=> s e m g cs lr Hbb. rewrite /mk_env.
  case Henv: (mk_env_bexp init_vm s init_env init_gen e) => [[[[m' E'] g'] cs'] lr'].
  move: (mk_env_bexp_is_bit_blast_bexp Henv). rewrite Hbb. case=> Hm Hg Hcs Hlr.
  rewrite Hm. apply: (mk_env_bexp_consistent Henv init_newer_than_vm).
  exact: init_consistent.
Qed.

Lemma mk_env_tt :
  forall s e, interp_lit (mk_env s e) lit_tt.
Proof.
  move=> s e. rewrite /mk_env.
  set m' := mk_env_bexp init_vm s init_env init_gen e.
  have: mk_env_bexp init_vm s init_env init_gen e = m' by reflexivity. move: m'.
  case=> [[[[m' E'] g'] cs'] lr'] Henv.
  rewrite (env_preserve_lit (mk_env_bexp_preserve Henv) init_newer_than_tt).
  exact: init_tt.
Qed.

Lemma mk_env_sat :
  forall s e m g cs lr,
    bit_blast_bexp init_vm init_gen e = (m, g, cs, lr) ->
    interp_cnf (mk_env s e) cs.
Proof.
  move=> s e m g cs lr Hbb. move: (mk_env_tt s e). rewrite /mk_env.
  set m' := mk_env_bexp init_vm s init_env init_gen e.
  have: mk_env_bexp init_vm s init_env init_gen e = m' by reflexivity. move: m'.
  case=> [[[[m' E'] g'] cs'] lr'] Henv. move: (mk_env_bexp_is_bit_blast_bexp Henv).
  rewrite Hbb; case=> _ _ -> _ Htt.
  exact: (mk_env_bexp_sat Henv init_newer_than_vm init_newer_than_tt).
Qed.



(* ===== mk_state ===== *)

Fixpoint lits_as_bits w E : w.-tuple literal -> BITS w :=
  if w is _.+1 then
    fun ls =>
      let (ls_tl, ls_hd) := eta_expand (splitlsb ls) in
      joinlsb (lits_as_bits E ls_tl, interp_lit E ls_hd)
  else
    fun _ =>
      nilB.

Lemma enc_bits_lits_as_bits :
  forall w E (ls : w.-tuple literal),
    enc_bits E ls (lits_as_bits E ls).
Proof.
  elim.
  - done.
  - move=> w IH E. case/tupleP=> [ls_hd ls_tl]. rewrite /= !theadE !beheadCons /=.
    rewrite IH andbT. exact: eqxx.
Qed.

Definition init_state : QFBV64.State.t := fun _ => fromNat 0.

Definition mk_state (E : env) (m : vm) : QFBV64.State.t :=
  (VM.fold (fun v ls s => QFBV64.State.upd v (lits_as_bits E ls) s) m init_state).

Lemma mk_state_find :
  forall E m x ls,
    VM.find x m = Some ls ->
    QFBV64.State.acc x (mk_state E m) = lits_as_bits E ls.
Proof.
  move=> E m.
  apply: (@VM.Lemmas.OP.P.fold_rec
            (wordsize.-tuple literal) (QFBV64.State.t)
            (fun m s =>
               forall x ls,
                 VM.find x m = Some ls ->
                 QFBV64.State.acc x s = lits_as_bits E ls)
            (fun v ls s => QFBV64.State.upd v (lits_as_bits E ls) s)
            init_state
            m).
  - move=> m0 Hempty x ls Hfind. rewrite (VM.Lemmas.Empty_find _ Hempty) in Hfind.
    discriminate.
  - move=> x lsx s m' m'' Hmapsto_xm Hin_xm' Hadd IH. move=> y lsy Hfind_y.
    case Hyx: (y == x).
    + rewrite (QFBV64.State.acc_upd_eq _ _ Hyx). move: (Hadd y).
      rewrite Hfind_y (VM.Lemmas.find_add_eq _ _ Hyx). case=> ->. reflexivity.
    + move/idP/negP: Hyx => Hyx. rewrite (QFBV64.State.acc_upd_neq _ _ Hyx).
      apply: IH. move: (Hadd y). rewrite Hfind_y. move/negP: Hyx => Hyx.
      rewrite (VM.Lemmas.find_add_neq _ _ Hyx). by move=> ->; reflexivity.
Qed.

Lemma mk_state_consistent :
  forall E m, consistent m E (mk_state E m).
Proof.
  move=> E m x. rewrite /consistent1. case Hfind: (VM.find x m); last by trivial.
  rewrite (mk_state_find _ Hfind). exact: enc_bits_lits_as_bits.
Qed.



(* ===== Soundness and completeness ===== *)

Lemma valid_implies_unsat :
  forall premises goal,
    (forall E, ~~ interp_cnf E (add_prelude premises) || interp_lit E goal) ->
    ~ (sat (add_prelude ([neg_lit goal]::premises))).
Proof.
  move=> premises goal H1 [E H2]. move: (H1 E) => {H1} H1.
  rewrite add_prelude_cons in H2. move/andP: H2 => [H2 H3].
  move/orP: H1. case => H1.
  - move/negP: H1. apply. exact: H3.
  - rewrite add_prelude_expand in H2. move/andP: H2 => [_ H2].
    rewrite /= interp_lit_neg_lit in H2. move/negP: H2; apply.
    exact: H1.
Qed.

Lemma unsat_implies_valid :
  forall premises goal,
    ~ (sat (add_prelude ([neg_lit goal]::premises))) ->
    (forall E, ~~ interp_cnf E (add_prelude premises) || interp_lit E goal).
Proof.
  move=> premises goal H E. case Hgoal: (interp_lit E goal).
  - by rewrite orbT.
  - rewrite orbF. apply/negP => H2. apply: H. exists E.
    rewrite add_prelude_cons H2 andbT.
    rewrite add_prelude_expand /=  interp_lit_neg_lit.
    rewrite Hgoal andbT. exact: (add_prelude_tt H2).
Qed.

Theorem bit_blast_sound :
  forall (e : QFBV64.bexp) m' g' cs lr,
    bit_blast_bexp init_vm init_gen e = (m', g', cs, lr) ->
    ~ (sat (add_prelude ([neg_lit lr]::cs))) ->
    QFBV64.valid e.
Proof.
  move=> e m' g' cs lr Hblast Hsat s.
  move: (unsat_implies_valid Hsat) => {Hsat} Hsat.
  move: (Hsat (mk_env s e)) => {Hsat} Hsat.
  move: (mk_env_sat s Hblast) => Hcs. move: (mk_env_tt s e) => Htt.
  have Hprelude: interp_cnf (mk_env s e) (add_prelude cs)
    by rewrite add_prelude_expand Hcs Htt.
  move: ((bit_blast_bexp_correct Hblast (mk_env_consistent s Hblast) Hprelude)).
  rewrite /enc_bit. move=> /eqP <-.
  rewrite Hprelude /= in Hsat. exact: Hsat.
Qed.

Theorem bit_blast_complete :
  forall (e : QFBV64.bexp) m' g' cs lr,
    bit_blast_bexp init_vm init_gen e = (m', g', cs, lr) ->
    QFBV64.valid e ->
    ~ (sat (add_prelude ([neg_lit lr]::cs))).
Proof.
  move=> e m' g' cs lr Hblast He.
  move=> [E Hcs]. move: (He (mk_state E m')) => {He} He.
  rewrite add_prelude_cons in Hcs. move/andP: Hcs => [Hlr Hcs].
  rewrite add_prelude_expand in Hlr. move/andP: Hlr => [Htt Hlr].
  rewrite /= interp_lit_neg_lit in Hlr.
  move: (bit_blast_bexp_correct Hblast (mk_state_consistent E m') Hcs).
  rewrite /enc_bit => /eqP H. rewrite -H in He.
  rewrite He in Hlr. exact: not_false_is_true.
Qed.
