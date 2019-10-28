From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport
     BitBlastingDef BitBlastingNewer .

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* bit_blast_exp_preserve, bit_blast_bexp_preserve, mk_env_exp_preserve_vm,
   mk_env_bexp_preserve_vm *)

Ltac bb_exp_bexp_vm_preserve :=
  lazymatch goal with
  | |- vm_preserve ?m ?m => exact: vm_preserve_refl
  | H1 : context f [bit_blast_exp _ _ _ ?e = (_, _, _, _) -> vm_preserve _ _],
         H2 : bit_blast_exp _ ?m1 _ ?e = (?m2, _, _, _)
    |- vm_preserve ?m1 ?m2 =>
    eapply H1; exact: H2
  | H1 : context f [bit_blast_bexp _ _ _ ?e = (_, _, _, _) -> vm_preserve _ _],
         H2 : bit_blast_bexp _ ?m1 _ ?e = (?m2, _, _, _)
    |- vm_preserve ?m1 ?m2 =>
    eapply H1; exact: H2
  | H1 : context f [bit_blast_exp _ _ _ ?e = (_, _, _, _) -> vm_preserve _ _],
         H2 : bit_blast_exp _ ?m1 _ ?e = (?m2, _, _, _)
    |- vm_preserve _ ?m2 =>
    apply: (@vm_preserve_trans _ m1);
    [bb_exp_bexp_vm_preserve | bb_exp_bexp_vm_preserve]
  | H1 : context f [bit_blast_bexp _ _ _ ?e = (_, _, _, _) -> vm_preserve _ _],
         H2 : bit_blast_bexp _ ?m1 _ ?e = (?m2, _, _, _)
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
  forall t (te : SSATE.env) (m : vm) (g : generator) (m' : vm)
         (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Evar t) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  move=> v te m g m' g' cs lrs /=. case Hfind: (SSAVM.find v m).
  - case=> <- _ _ _. exact: vm_preserve_refl.
  - case Hv: (bit_blast_var te g v)=> [[og ocs] olrs].
    case=> <- _ _ _. exact: vm_preserve_add_diag.
Qed.

Lemma bit_blast_exp_preserve_const :
  forall (b : bits) (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Econst b) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_not :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop QFBV.Unot e1) = (m', g', cs, lrs) ->
      vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H0 .
  dcase (bit_blast_exp te m g e1) => [[[[m1 g1] cs1] s1] Hexp] .
  dcase (bit_blast_not g1 s1) => [[[gr csr] lsr] Hnot] .
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_and :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g (QFBV.Ebinop QFBV.Band e1 e2) = (m', g', cs, lrs) ->
        vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e1) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_and g2 ls1 ls2) => [[[gr csr] lsr] Hand] .
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_or :
  forall (e0 : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (g  : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m  : vm) (g  : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] rs1] Hexp0] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] rs2] Hexp1] .
  dcase (bit_blast_or g2 rs1 rs2) => [[[g'0 cs0] rs] Hor] .
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_xor :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', g', cs, lrs) ->
        vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e1) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_xor g2 ls1 ls2) => [[[gr csr] lsr] Hxor] .
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_neg :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop QFBV.Uneg e1) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H0 .
  dcase (bit_blast_exp te m g e1) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_neg g1 ls1) => [[[gr csr] lsr] Hneg] .
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_add :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : word),
        bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
             (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Badd e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e0) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_add g2 ls1 ls2) => [[[g'0 cs0] rs] Hadd] .
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_sub :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : word),
        bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
             (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bsub e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  rewrite /=; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e0) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_sub g2 ls1 ls2) => [[[g'0 cs0] rs] Hsub] .
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_mul :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : word),
        bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
             (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bmul e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e0) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_mul g2 ls1 ls2) => [[[g'0 cs0] rs] Hmul] .
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_mod :
  forall (e : QFBV.exp) (e0 : QFBV.exp) (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bmod e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_srem :
  forall (e : QFBV.exp) (e0 : QFBV.exp) (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_smod :
  forall (e : QFBV.exp) (e0 : QFBV.exp) (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_shl :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_shl g2 ls1 ls2) => [[[g'0 cs0] ls] Hshl] .
  auto_bit_blast_vm_preserve.
Qed .

Lemma bit_blast_exp_preserve_lshr :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
           (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_lshr g2 ls1 ls2) => [[[g'0 cs0] ls] Hlshr] .
  auto_bit_blast_vm_preserve.
Qed .

Lemma bit_blast_exp_preserve_ashr :
  forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
  forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_ashr g2 ls1 ls2) => [[[g'0 cs0] ls] Hashr] .
  auto_bit_blast_vm_preserve .
Qed .

Lemma bit_blast_exp_preserve_concat :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
           (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', g', cs, lrs) ->
      vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hexp2] .
  auto_bit_blast_vm_preserve.
Qed .

Lemma bit_blast_exp_preserve_extract :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (i j :nat) (g' : generator) (cs : cnf)
           (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', g', cs, lrs) ->
      vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H0 .
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  auto_bit_blast_vm_preserve .
Qed .

(*
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
*)

Lemma bit_blast_exp_preserve_high :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator) (n :nat)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H0 .
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  auto_bit_blast_vm_preserve .
Qed .

Lemma bit_blast_exp_preserve_low :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator) (n : nat)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop (QFBV.Ulow n) e) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H0 .
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  auto_bit_blast_vm_preserve .
Qed .

Lemma bit_blast_exp_preserve_zeroextend :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator) (n : nat)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Eunop (QFBV.Uzext n) e) = (m', g', cs, lrs) ->
    vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H0 .
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  auto_bit_blast_vm_preserve .
Qed .

Lemma bit_blast_exp_preserve_signextend :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator) (n : nat)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop (QFBV.Usext n) e) = (m', g', cs, lrs) ->
      vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H0 .
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  auto_bit_blast_vm_preserve .
Qed .

Lemma bit_blast_exp_preserve_ite :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp te m g b = (m', g', cs, lr) -> vm_preserve m m') ->
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (e0 : QFBV.exp),
        (forall (te : SSATE.env) (m : vm) (g : generator)
                (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
            bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
        forall (te : SSATE.env) (m : vm) (g : generator)
               (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g (QFBV.Eite b e e0) = (m', g', cs, lrs) ->
          vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  rewrite /=; intros .
  move : H2 .
  dcase (bit_blast_bexp te m g b) => [[[[mc gc] csc] lc] Hbexp] .
  dcase (bit_blast_exp te mc gc e) => [[[[m1 g1] cs1] ls1] Hexpe] .
  dcase (bit_blast_exp te m1 g1 e0)=> [[[[m2 g2] cs2] ls2] Hexpe0] .
  dcase (bit_blast_ite g2 lc ls1 ls2) => [[[gr csr] lsr] Hite] .
auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_false :
  forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
         (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g QFBV.Bfalse = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_true :
  forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
         (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g QFBV.Btrue = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_eq :
  forall (e1 : QFBV.exp)
         (IH1 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (e2 : QFBV.exp)
         (IH2 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Beq e1 e2) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_eq g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_ult :
  forall (e1 : QFBV.exp)
         (IH1 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (e2 : QFBV.exp)
         (IH2 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bult e1 e2) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_ult g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_ule :
  forall (e1 : QFBV.exp)
         (IH1 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (e2 : QFBV.exp)
         (IH2 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bule e1 e2) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_ule g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_ugt :
  forall (e1 : QFBV.exp)
         (IH1 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (e2 : QFBV.exp)
         (IH2 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bugt e1 e2) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_eq g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_uge :
  forall (e1 : QFBV.exp)
         (IH1 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (e2 : QFBV.exp)
         (IH2 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Buge e1 e2) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_eq g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_slt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_slt g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_sle :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_sle g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_sgt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_sgt g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_sge :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_sge g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_uaddo :
  forall (e : QFBV.exp) ,
    (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : word),
        bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', g', cs, lr) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  dcase (bit_blast_exp te m'0 ge e0) => [[[[m2 g2] cs2] ls2] Hexp0] .
  dcase (bit_blast_uaddo g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_usubo :
  forall (e : QFBV.exp) ,
    (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : word),
        bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Busubo e e0) = (m', g', cs, lr) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  dcase (bit_blast_exp te m'0 ge e0) => [[[[m2 g2] cs2] ls2] Hexp0] .
  dcase (bit_blast_usubo g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_umulo :
  forall (e : QFBV.exp) ,
    (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : word),
        bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', g', cs, lr) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  dcase (bit_blast_exp te m'0 ge e0) => [[[[m2 g2] cs2] ls2] Hexp0] .
  dcase (bit_blast_umulo g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_saddo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_saddo g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_ssubo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_ssubo g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_smulo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_smulo g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_lneg :
  forall (b : QFBV.bexp)
         (IH :
            forall (te : SSATE.env) (m : vm) (g : generator)
                   (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
              bit_blast_bexp te m g b = (m', g', cs, lrs) ->
              vm_preserve m m')
         (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g (QFBV.Blneg b) = (m', g', cs, lrs) ->
    vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_conj :
  forall (b : QFBV.bexp)
         (IH :
            forall (te : SSATE.env) (m : vm) (g : generator)
                   (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
              bit_blast_bexp te m g b = (m', g', cs, lrs) ->
              vm_preserve m m')
         (b0 : QFBV.bexp)
         (IH0 :
            forall (te : SSATE.env) (m : vm) (g : generator)
                   (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
              bit_blast_bexp te m g b0 = (m', g', cs, lrs) ->
              vm_preserve m m')
         (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g (QFBV.Bconj b b0) = (m', g', cs, lrs) ->
    vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_disj :
  forall (b : QFBV.bexp)
         (IH :
            forall (te : SSATE.env) (m : vm) (g : generator)
                   (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
              bit_blast_bexp te m g b = (m', g', cs, lrs) ->
              vm_preserve m m')
         (b0 : QFBV.bexp)
         (IH0 :
            forall (te : SSATE.env) (m : vm) (g : generator)
                   (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
              bit_blast_bexp te m g b0 = (m', g', cs, lrs) ->
              vm_preserve m m')
         (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g (QFBV.Bdisj b b0) = (m', g', cs, lrs) ->
    vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Corollary bit_blast_exp_preserve :
  forall (e : QFBV.exp) te m g m' g' cs lrs,
    bit_blast_exp te m g e = (m', g', cs, lrs) ->
    vm_preserve m m'
  with
    bit_blast_bexp_preserve :
      forall (e : QFBV.bexp) te m g m' g' cs lrs,
        bit_blast_bexp te m g e = (m', g', cs, lrs) ->
        vm_preserve m m'.
Proof.
  (* bit_blast_exp_preserve *)
  move => e te m g m' g' cs lrs .
  case : e .
  - move => t; exact : bit_blast_exp_preserve_var.
  - move => b; exact : bit_blast_exp_preserve_const.
  - case .
    + move => e .
      apply : bit_blast_exp_preserve_not;
        exact : bit_blast_exp_preserve .
    + move => e .
      apply : bit_blast_exp_preserve_neg;
        exact : bit_blast_exp_preserve .
    + move => i j e .
      apply : bit_blast_exp_preserve_extract;
        exact : bit_blast_exp_preserve .
    + move => n e .
      apply : bit_blast_exp_preserve_high;
        exact : bit_blast_exp_preserve .
    + move => n e .
      apply : bit_blast_exp_preserve_low;
        exact : bit_blast_exp_preserve .
    + move => n e .
      apply : bit_blast_exp_preserve_zeroextend;
        exact : bit_blast_exp_preserve .
    + move => n e .
      apply : bit_blast_exp_preserve_signextend;
        exact : bit_blast_exp_preserve .
  - case; move => e0 e1.
    + apply : bit_blast_exp_preserve_and;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_or;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_xor;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_add;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_sub;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_mul;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_mod;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_srem;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_smod;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_shl;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_lshr;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_ashr;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_concat;
        exact : bit_blast_exp_preserve .
  - move => b e0 e1 .
    apply : bit_blast_exp_preserve_ite;
      (exact : bit_blast_bexp_preserve ||
       exact : bit_blast_exp_preserve) .
(* bit_blast_bexp_preserve *)
  move => e te m g m' g' cs lrs .
  case : e .
  - apply : bit_blast_bexp_preserve_false .
  - apply : bit_blast_bexp_preserve_true .
  - case; move => e0 e1 .
    + apply : bit_blast_bexp_preserve_eq;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_ult;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_ule;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_ugt;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_uge;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_slt;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_sle;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_sgt;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_sge;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_uaddo;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_usubo;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_umulo;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_saddo;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_ssubo;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_smulo;
        exact : bit_blast_exp_preserve .
  - move => b .
    apply : bit_blast_bexp_preserve_lneg;
      exact : bit_blast_bexp_preserve .
  - move => b0 b1 .
    apply : bit_blast_bexp_preserve_conj;
      exact : bit_blast_bexp_preserve .
  - move => b0 b1 .
    apply : bit_blast_bexp_preserve_disj;
      exact : bit_blast_bexp_preserve .
Qed.

Corollary mk_env_exp_preserve_vm :
  forall (e : QFBV.exp) E m s g E' m' g' cs' lrs',
    mk_env_exp m s E g e = (m', E', g', cs', lrs') ->
    vm_preserve m m'
  with
    mk_env_bexp_preserve_vm :
      forall (e : QFBV.bexp) E m s g E' m' g' cs' lrs',
        mk_env_bexp m s E g e = (m', E', g', cs', lrs') ->
        vm_preserve m m'.
Proof .
  (* mk_env_exp_preserve_vm *)
  elim . (*  rewrite /= . *)
  - move => v E m s g E' m' g' cs' lrs' /= .
    case Hf : (SSAVM.find v m) .
    + case => <- _ _ _ _; apply : vm_preserve_refl .
    + dcase (mk_env_var E g (SSAStore.acc v s) v) => [[[[E'0 g'0] cs] rs] Hmke] .
      case => <- _ _ _ _ .
      exact : vm_preserve_add_diag .
  - rewrite /=; t_auto_preserve; exact : vm_preserve_refl .
  - elim => /= [e IHe E m s g E' m' g' cs' lrs' |
                e IHe E m s g E' m' g' cs' lrs' |
                i j e IHe E m s g E' m' g' cs' lrs' |
                n e IHe E m s g E' m' g' cs' lrs' |
                n e IHe E m s g E' m' g' cs' lrs' |
                n e IHe E m s g E' m' g' cs' lrs' |
                n e IHe E m s g E' m' g' cs' lrs'];
      dcase (mk_env_exp m s E g e) => [[[[[m1 E1] g1] cs1] ls1] Hmke] .
    + dcase (mk_env_not E1 g1 ls1) => [[[[Er gr] csr] lsr] Hmkr];
      case => <- _ _ _ _; exact : (IHe _ _ _ _ _ _ _ _ _ Hmke) .
    + dcase (mk_env_neg E1 g1 ls1) => [[[[Er gr] csr] lsr] Hmkr];
      case => <- _ _ _ _; exact : (IHe _ _ _ _ _ _ _ _ _ Hmke) .
    + case => <- _ _ _ _; exact : (IHe _ _ _ _ _ _ _ _ _ Hmke) .
    + case => <- _ _ _ _; exact : (IHe _ _ _ _ _ _ _ _ _ Hmke) .
    + case => <- _ _ _ _; exact : (IHe _ _ _ _ _ _ _ _ _ Hmke) .
    + case => <- _ _ _ _; exact : (IHe _ _ _ _ _ _ _ _ _ Hmke) .
    + case => <- _ _ _ _; exact : (IHe _ _ _ _ _ _ _ _ _ Hmke) .
  - elim => e0 IH0 e1 IH1 E m s g E' m' g' cs' lrs' /=;
      dcase (mk_env_exp m s E g e0) => [[[[[m1 E1] g1] cs1] ls1] Hmke0];
      dcase (mk_env_exp m1 s E1 g1 e1) => [[[[[m2 E2] g2] cs2] ls2] Hmke1] .
    + dcase (mk_env_and E2 g2 ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + dcase (mk_env_or E2 g2 ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + dcase (mk_env_xor E2 g2 ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + dcase (mk_env_add E2 g2 ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + dcase (mk_env_sub E2 g2 ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + dcase (mk_env_mul E2 g2 ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + dcase (mk_env_shl E2 g2 ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + dcase (mk_env_lshr E2 g2 ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + dcase (mk_env_ashr E2 g2 ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
  - move => c e0 IH0 e1 IH1 E m s g E' m' g' cs' lrs' /= .
    dcase (mk_env_bexp m s E g c) => [[[[[mc Ec] gc] csc] lc] Hmkc] .
    dcase (mk_env_exp mc s Ec gc e0) => [[[[[m1 E1] g1] cs1] ls1] Hmke0] .
    dcase (mk_env_exp m1 s E1 g1 e1) => [[[[[m2 E2] g2] cs2] ls2] Hmke1] .
    dcase (mk_env_ite E2 g2 lc ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
    case => <- _ _ _ _ .
    exact: (vm_preserve_trans
              (vm_preserve_trans
                 (mk_env_bexp_preserve_vm c _ _ _ _ _ _ _ _ _ Hmkc)
                 (IH0 _ _ _ _ _ _ _ _ _ Hmke0))
              (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
  (* mk_env_bexp_preserve_vm *)
  elim .
  - move => E m s g E' m' g' cs' lrs' .
    case => <- _ _ _ _; exact : vm_preserve_refl .
  - move => E m s g E' m' g' cs' lrs' .
    case => <- _ _ _ _; exact : vm_preserve_refl .
  - elim => e0 e1 E m s g E' m' g' cs' lrs'; rewrite /=;
      dcase (mk_env_exp m s E g e0) => [[[[[m1 E1] g1] cs1] ls1] Hmke0];
      dcase (mk_env_exp m1 s E1 g1 e1) => [[[[[m2 E2] g2] cs2] ls2] Hmke1];
      move : (mk_env_exp_preserve_vm e0 _ _ _ _ _ _ _ _ _ Hmke0)
             (mk_env_exp_preserve_vm e1 _ _ _ _ _ _ _ _ _ Hmke1)
    => Hmm1 Hm1m2 .
    + dcase (mk_env_eq E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_ult E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_ule E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_ugt E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_uge E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_slt E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_sle E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_sgt E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_sge E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_uaddo E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_usubo E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_umulo E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_saddo E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_ssubo E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_smulo E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
  - move => b IHb E m s g E' m' g' cs' lrs' /= .
    dcase (mk_env_bexp m s E g b) => [[[[[m1 E1] g1] cs1] l1] Hmkb] .
    case => <- _ _ _ _ .
    exact : (IHb _ _ _ _ _ _ _ _ _ Hmkb) .
  - move => b0 IH0 b1 IH1 E m s g E' m' g' cs' lrs' /= .
    dcase (mk_env_bexp m s E g b0) => [[[[[m1 E1] g1] cs1] l1] Hmkb0 ] .
    dcase (mk_env_bexp m1 s E1 g1 b1) => [[[[[m2 E2] g2] cs2] l2] Hmkb1] .
    case => <- _ _ _ _ .
    exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmkb0)
                               (IH1 _ _ _ _ _ _ _ _ _ Hmkb1)) .
  - move => b0 IH0 b1 IH1 E m s g E' m' g' cs' lrs' /= .
    dcase (mk_env_bexp m s E g b0) => [[[[[m1 E1] g1] cs1] l1] Hmkb0 ] .
    dcase (mk_env_bexp m1 s E1 g1 b1) => [[[[[m2 E2] g2] cs2] l2] Hmkb1] .
    case => <- _ _ _ _ .
    exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmkb0)
                               (IH1 _ _ _ _ _ _ _ _ _ Hmkb1)) .
Qed .

(* = mk_env_exp_preserve and mk_env_bexp_preserve = *)

Lemma mk_env_exp_preserve_var :
  forall t (m : vm) (s : SSAStore.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Evar t) = (m', E', g', cs, lrs) -> env_preserve E E' g.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case Hfind: (SSAVM.find v m).
  - case=> _ <- _ _ _. exact: env_preserve_refl.
  - case Henv: (mk_env_var E g (SSAStore.acc v s) v) => [[[E_v g_v] cs_v] lrs_v].
    case=> _ <- _ _ _. exact: (mk_env_var_preserve Henv).
Qed.

Lemma mk_env_exp_preserve_const :
  forall (b : bits) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Econst b) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> bs m s E g m' E' g' cs lrs /=. case=> _ <- _ _ _. exact: env_preserve_refl.
Qed.

Lemma mk_env_exp_preserve_not :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop QFBV.Unot e1) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
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
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Band e1 e2) = (m', E', g', cs, lrs) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
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
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_or E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_or_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed .

Lemma mk_env_exp_preserve_xor :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', E', g', cs, lrs) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
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
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop QFBV.Uneg e1) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
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
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Badd e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_add E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_add_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_exp_preserve_sub :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsub e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sub E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_sub_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_exp_preserve_mul :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmul e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_mul E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_mul_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_exp_preserve_mod :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmod e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_srem :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_smod :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_shl :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_shl E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_shl_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed .

Lemma mk_env_exp_preserve_lshr :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_lshr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_lshr_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed .

Lemma mk_env_exp_preserve_ashr :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ashr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_ashr_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed .

Lemma mk_env_exp_preserve_concat :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  exact: (env_preserve_trans _ HpE1E2g).
Qed .

Lemma mk_env_exp_preserve_extract :
  forall (i j : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> i j e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ _ _.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
Qed .

(*
Lemma mk_env_exp_preserve_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV.exp (w3 + w2 + w1)),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .
*)

Lemma mk_env_exp_preserve_high :
    forall (n : nat) (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm)
           (s : SSAStore.t) (E : env) (g : generator) (m' : vm)
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ _ _.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) .
Qed .

Lemma mk_env_exp_preserve_low :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Ulow n) e) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ _ _.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) .
Qed .

Lemma mk_env_exp_preserve_zeroextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uzext n) e) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ _ _.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
Qed .

Lemma mk_env_exp_preserve_signextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Usext n) e) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ _ _.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) .
Qed .

Lemma mk_env_exp_preserve_ite :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        env_preserve E E' g) ->
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (e0 : QFBV.exp),
        (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : word),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
        forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp m s E g (QFBV.Eite b e e0) = (m', E', g', cs, lrs) ->
          env_preserve E E' g.
Proof.
  move=> c IHc e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmkc : (mk_env_bexp m s E g c) => [[[[mc Ec] gc] csc] lsc].
  case Hmke1 : (mk_env_exp mc s Ec gc e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ite E2 g2 lsc ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IHc _ _ _ _ _ _ _ _ _ Hmkc) => HpEEcg.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEcE1gc.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_ite_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_bexp_newer_gen Hmkc) (mk_env_exp_newer_gen Hmke1)
        (mk_env_exp_newer_gen Hmke2) => Hggc Hgcg1 Hg1g2.
  move: (env_preserve_le HpEcE1gc Hggc) => HpEcE1g.
  move: (env_preserve_le HpE1E2g1 (pos_leb_trans Hggc Hgcg1)) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2
                         (pos_leb_trans Hggc (pos_leb_trans Hgcg1 Hg1g2))) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  apply: (env_preserve_trans _ HpE1E2g).
  exact: (env_preserve_trans _ HpEcE1g) .
Qed.

Lemma mk_env_bexp_preserve_false :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Bfalse = (m', E', g', cs, lr) -> env_preserve E E' g.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ <- _ _ _. exact: env_preserve_refl.
Qed.

Lemma mk_env_bexp_preserve_true :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Btrue = (m', E', g', cs, lr) -> env_preserve E E' g.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ <- _ _ _. exact: env_preserve_refl.
Qed.

Lemma mk_env_bexp_preserve_eq :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Beq e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
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
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bult e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
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
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bule e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
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
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bugt e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
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
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buge e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
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
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
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
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
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
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
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
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
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
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
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
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Busubo e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
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
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
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
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
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
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
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
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
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
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Blneg b) = (m', E', g', cs, lr) ->
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
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        env_preserve E E' g) ->
    forall (b0 : QFBV.bexp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bconj b b0) = (m', E', g', cs, lr) ->
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
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        env_preserve E E' g) ->
    forall (b0 : QFBV.bexp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bdisj b b0) = (m', E', g', cs, lr) ->
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
  forall (e : QFBV.exp) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    env_preserve E E' g
  with
    mk_env_bexp_preserve :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  elim .
  - exact: mk_env_exp_preserve_var .
  - exact: mk_env_exp_preserve_const .
  - elim .
    + exact: mk_env_exp_preserve_not .
    + exact: mk_env_exp_preserve_neg .
    + exact: mk_env_exp_preserve_extract .
    + exact: mk_env_exp_preserve_high .
    + exact: mk_env_exp_preserve_low .
    + exact: mk_env_exp_preserve_zeroextend .
    + exact: mk_env_exp_preserve_signextend .
  - elim .
    + exact: mk_env_exp_preserve_and .
    + exact: mk_env_exp_preserve_or .
    + exact: mk_env_exp_preserve_xor .
    + exact: mk_env_exp_preserve_add .
    + exact: mk_env_exp_preserve_sub .
    + exact: mk_env_exp_preserve_mul .
    + exact: mk_env_exp_preserve_mod .
    + exact: mk_env_exp_preserve_srem .
    + exact: mk_env_exp_preserve_smod .
    + exact: mk_env_exp_preserve_shl .
    + exact: mk_env_exp_preserve_lshr .
    + exact: mk_env_exp_preserve_ashr .
    + exact: mk_env_exp_preserve_concat .
  - move => b;
      move : b (mk_env_bexp_preserve b);
      exact: mk_env_exp_preserve_ite .
  (* mk_env_bexp_preserve *)
  elim .
  - exact: mk_env_bexp_preserve_false .
  - exact: mk_env_bexp_preserve_true .
  - elim; move => e0 e1;
      move : e0 (mk_env_exp_preserve e0)
             e1 (mk_env_exp_preserve e1) .
    + exact: mk_env_bexp_preserve_eq .
    + exact: mk_env_bexp_preserve_ult .
    + exact: mk_env_bexp_preserve_ule .
    + exact: mk_env_bexp_preserve_ugt .
    + exact: mk_env_bexp_preserve_uge .
    + exact: mk_env_bexp_preserve_slt .
    + exact: mk_env_bexp_preserve_sle .
    + exact: mk_env_bexp_preserve_sgt .
    + exact: mk_env_bexp_preserve_sge .
    + exact: mk_env_bexp_preserve_uaddo .
    + exact: mk_env_bexp_preserve_usubo .
    + exact: mk_env_bexp_preserve_umulo .
    + exact: mk_env_bexp_preserve_saddo .
    + exact: mk_env_bexp_preserve_ssubo .
    + exact: mk_env_bexp_preserve_smulo .
  - exact: mk_env_bexp_preserve_lneg .
  - exact: mk_env_bexp_preserve_conj .
  - exact: mk_env_bexp_preserve_disj .
Qed.


