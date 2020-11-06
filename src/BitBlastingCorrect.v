From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport AdhereConform
     BitBlastingDef BitBlastingPreserve .

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* = bit_blast_exp_correct and bit_blast_bexp_correct = *)

Lemma bit_blast_exp_var :
  forall v (te : SSATE.env) (m : vm) (g : generator)
         (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Evar v) = (m', g', cs, lrs) ->
    AdhereConform.conform_exp (QFBV.Evar v) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Evar v) te ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Evar v) s) .
Proof .
  move=> v te im ig s E om og ocs olrs. move=> Hblast _ Hcon _ Hcnf.
  move: (Hcon v) Hblast => {Hcon} Hcon. rewrite /=. case Hfind: (SSAVM.find v im).
  - case=> Hm Hg Hcs Hlrs. move: Hcon; rewrite /consistent1.
    rewrite -Hm Hfind Hlrs // .
  - case Hblast: (bit_blast_var te ig v) => [[vg vcs] vlrs].
    case=> [Hom Hog Hocs Holrs]. move: Hcon; rewrite /consistent1.
    rewrite -Hom. rewrite (SSAVM.Lemmas.find_add_eq (eq_refl v)).
    rewrite Holrs // .
Qed.

Lemma bit_blast_exp_const :
  forall (b : bits) (te : SSATE.env) (m : vm) (g : generator)
         (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Econst b) = (m', g', cs, lrs) ->
    AdhereConform.conform_exp (QFBV.Econst b) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Econst b) te ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Econst b) s).
Proof.
  move=> bv te im ig s E om og ocs olrs. case=> _ _ <- <- _ _ Hprelude _ .
  move: (add_prelude_enc_bit_tt Hprelude) => Htt {im ig om og ocs olrs Hprelude}.
  elim: bv; first by done. move=> a l IH. 
  rewrite enc_bits_cons; apply /andP; split .
  - rewrite enc_bit_lit_of_bool // .
  - exact : IH .
Qed.

Lemma bit_blast_exp_not :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp (QFBV.Eunop QFBV.Unot e1) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator)
           (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop QFBV.Unot e1) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Eunop QFBV.Unot e1) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.QFBV.well_formed_exp (QFBV.Eunop QFBV.Unot e1) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Eunop QFBV.Unot e1) s).
Proof.
  move=> e1 IH1 te m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case Hr : (bit_blast_not g1 ls1) => [[gr csr] lsr].
  case=> <- _ <- <-. move=> Hcf Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_cat. move/andP=> [Hic1 Hicr] Hwf .
  apply: (bit_blast_not_correct Hr _ Hicr).
  exact: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf Hcons1 Hic1 Hwf).
Qed.


Lemma bit_blast_exp_and :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e1 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e2 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e2 te ->
          enc_bits E lrs (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lrs : word),
        bit_blast_exp te m g (QFBV.Ebinop QFBV.Band e1 e2) = (m', g', cs, lrs) ->
        AdhereConform.conform_exp (QFBV.Ebinop QFBV.Band e1 e2) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Band e1 e2) te ->
        enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Band e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_and g2 ls1 ls2) => [[gr csr] lsr].
  case=> <- _ <- <-. move=> /andP [Hcf1 Hcf2] Hcons2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcons2) => Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_cat. move/andP=> [Hic1 /andP [Hic2 Hicr]] .
  move => /andP [/andP [/andP [Hwf1 Hwf2] _] _] .
  apply: (bit_blast_and_correct Hr _ _ Hicr).
  - exact: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcons1 Hic1 Hwf1).
  - exact: (IH2 _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcons2 Hic2 Hwf2).
Qed.


Lemma bit_blast_exp_or :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e0 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e0 te ->
          enc_bits E lrs (QFBV.eval_exp e0 s)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e1 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e1 te ->
          enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bor e0 e1) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bor e0 e1) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bor e0 e1) s).
Proof.
  move=> e0 IHe0 e1 IHe1 te m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] rs1] Hexp0] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] rs2] Hexp1] .
  dcase (bit_blast_or g2 rs1 rs2) => [[[g'0 cs0] rs] Hor] .
  case => <- _ <- <- .
  move => /andP [Hcf0 Hcf1] Hcon Hprelude /andP [/andP [/andP [Hwf0 Hwf1] _] _] .
  rewrite !add_prelude_cat in Hprelude.
  move: Hprelude => /andP [Hcs0 /andP [Hcs1 Hcs2]] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp1) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp0) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ _ Hexp0 Hcf0 Hcon1 Hcs0 Hwf0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ _ Hexp1 Hcf1 Hcon Hcs1 Hwf1) => Hencls1.
  apply: (bit_blast_or_correct Hor Hencls0 Hencls1 Hcs2).
Qed .

Lemma bit_blast_exp_xor :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e1 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e2 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e2 te ->
          enc_bits E lrs (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lrs : word),
        bit_blast_exp te m g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', g', cs, lrs) ->
        AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bxor e1 e2) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bxor e1 e2) te ->
        enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bxor e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_xor g2 ls1 ls2) => [[gr csr] lsr].
  case=> <- _ <- <-. move=> /andP [Hcf1 Hcf2] Hcons2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcons2) => Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_cat.
  move/andP=> [Hic1 /andP [Hic2 Hicr]] /andP [/andP [/andP [Hwf1 Hwf2] _] _].
  apply: (bit_blast_xor_correct Hr _ _ Hicr).
  - exact: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcons1 Hic1 Hwf1).
  - exact: (IH2 _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcons2 Hic2 Hwf2).
Qed.

Lemma bit_blast_exp_neg :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e te ->
        enc_bits E lrs (QFBV.eval_exp e s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator)
           (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Eunop QFBV.Uneg e) = (m', g', cs, lrs) ->
    AdhereConform.conform_exp (QFBV.Eunop QFBV.Uneg e)s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Eunop QFBV.Uneg e) te ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Eunop QFBV.Uneg e) s).
Proof.
  move=> e IH1 te m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e) => [[[m1 g1] cs1] ls1].
  case Hr : (bit_blast_neg g1 ls1) => [[gr csr] lsr].
  case=> <- _ <- <-. move=> Hcf Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_cat.
  move/andP=> [Hic1 Hicr] Hwf .
  apply: (bit_blast_neg_correct Hr _ Hicr).
  exact : (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf Hcons1 Hic1 Hwf).
Qed.

Lemma bit_blast_exp_add :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e0 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e0 te ->
          enc_bits E lrs (QFBV.eval_exp e0 s)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e1 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e1 te ->
          enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Badd e0 e1) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Badd e0 e1) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Badd e0 e1) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Badd e0 e1) s).
Proof.
  move => e0 IHe0 e1 IHe1 te m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] rs1] Hexp0] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] rs2] Hexp1] .
  dcase (bit_blast_add g2 rs1 rs2) => [[[g'0 cs0] rs] Hadd] .
  case => <- _ <- <- .
  move => /andP [Hcf0 Hcf1] Hcon Hprelude /andP [/andP [/andP [Hwf0 Hwf1] _] Hsize] .
  rewrite !add_prelude_cat in Hprelude.
  move: Hprelude => /andP [Hcs0 /andP [Hcs1 Hcs2]] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp1) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp0) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ _ Hexp0 Hcf0 Hcon1 Hcs0 Hwf0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ _ Hexp1 Hcf1 Hcon Hcs1 Hwf1) => Hencls1.
  apply : (bit_blast_add_correct Hadd Hencls0 Hencls1); [done|done|idtac] .
  rewrite (enc_bits_size Hencls0) (enc_bits_size Hencls1)
          (AdhereConform.eval_conform_exp_size Hwf0 Hcf0) (AdhereConform.eval_conform_exp_size Hwf1 Hcf1)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_exp_sub :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e0 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e0 te ->
          enc_bits E lrs (QFBV.eval_exp e0 s)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e1 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e1 te ->
          enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bsub e0 e1) = (m', g', cs, lrs) ->
    AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bsub e0 e1) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsub e0 e1) te ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bsub e0 e1) s).
Proof.
  move => e0 IHe0 e1 IHe1 te m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] rs1] Hexp0] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] rs2] Hexp1] .
  dcase (bit_blast_sub g2 rs1 rs2) => [[[g'0 cs0] rs] Hsub] .
  case => <- _ <- <- /andP [Hcf0 Hcf1] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs0 /andP [Hcs1 Hcs2]] /andP [/andP [/andP [Hwf0 Hwf1] _] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp1) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp0) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ _ Hexp0 Hcf0 Hcon1 Hcs0 Hwf0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ _ Hexp1 Hcf1 Hcon Hcs1 Hwf1) => Hencls1.
  apply (bit_blast_sub_correct Hsub Hencls0 Hencls1); first done .
  rewrite (enc_bits_size Hencls0) (enc_bits_size Hencls1)
          (AdhereConform.eval_conform_exp_size Hwf0 Hcf0) (AdhereConform.eval_conform_exp_size Hwf1 Hcf1)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_exp_mul :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e te ->
          enc_bits E lrs (QFBV.eval_exp e s)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e0 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e0 te ->
          enc_bits E lrs (QFBV.eval_exp e0 s)) ->
    forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bmul e e0) = (m', g', cs, lrs) ->
    AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bmul e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bmul e e0) te ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bmul e e0) s).
Proof.
  move => e0 IHe0 e1 IHe1 te m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] rs1] Hexp0] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] rs2] Hexp1] .
  dcase (bit_blast_mul g2 rs1 rs2) => [[[g'0 cs0] rs] Hmul] .
  case => <- _ <- <- /andP [Hcf0 Hcf1] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs0 /andP [Hcs1 Hcs2]] /andP [/andP [/andP [Hwf0 Hwf1] _] Hsize] .
  move : (vm_preserve_consistent (bit_blast_exp_preserve Hexp1) Hcon) => Hconm0.
  move : (vm_preserve_consistent (bit_blast_exp_preserve Hexp0) Hconm0) => Hconm.
  move : (IHe0 _ _ _ _ _ _ _ _ _ Hexp0 Hcf0 Hconm0 Hcs0 Hwf0) => Hence0.
  move : (IHe1 _ _ _ _ _ _ _ _ _ Hexp1 Hcf1 Hcon Hcs1 Hwf1) => Hence1.
  apply : (bit_blast_mul_correct Hmul Hence0 Hence1); first done.
  rewrite (enc_bits_size Hence0) (enc_bits_size Hence1)
          (AdhereConform.eval_conform_exp_size Hwf0 Hcf0) (AdhereConform.eval_conform_exp_size Hwf1 Hcf1)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_exp_mod :
  forall (e e0 : QFBV.exp) (te : SSATE.env) (m : vm) (g : generator)
         (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bmod e e0) = (m', g', cs, lrs) ->
    AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bmod e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bmod e e0) te ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bmod e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_srem :
  forall (e e0 : QFBV.exp) (te : SSATE.env) (m : vm) (g : generator)
         (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', g', cs, lrs) ->
    AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bsrem e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsrem e e0) te ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bsrem e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_smod :
  forall (e e0 : QFBV.exp) (te : SSATE.env) (m : vm) (g : generator)
         (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', g', cs, lrs) ->
    AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bsmod e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsmod e e0) te ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bsmod e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_shl :
    forall (e0: QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e0 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e0 te ->
          enc_bits E lrs (QFBV.eval_exp e0 s)) ->
    forall (e1: QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e1 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e1 te ->
          enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bshl e0 e1) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bshl e0 e1) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bshl e0 e1) s).
Proof.
  move => e0 IHe0 e1 IHe1 te m g s E m' g' cs lrs .
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] rs1] Hexp0] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] rs2] Hexp1] .
  dcase (bit_blast_shl g2 rs1 rs2) => [[[g'0 cs0] rs] Hshl] .
  case => <- _ <- <- /andP [Hcf0 Hcf1] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs0 /andP [Hcs1 Hcs2]] /andP [/andP [/andP [Hwf0 Hwf1] Hszgt0] Hszeq] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp1) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp0) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ _ Hexp0 Hcf0 Hcon1 Hcs0 Hwf0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ _ Hexp1 Hcf1 Hcon Hcs1 Hwf1) => Hencls1.
  have : size rs1 > 0 .
  {
    move : (enc_bits_size Hencls0) .
    rewrite (eval_conform_exp_size Hwf0 Hcf0) => Hszrs1 .
    by rewrite -Hszrs1 in Hszgt0 .
  }
  move => {Hszgt0} Hszrs1gt0 .
  have : size rs1 = size rs2 .
  { 
    move : (enc_bits_size Hencls0) (enc_bits_size Hencls1) .
    case => -> -> .
    rewrite (eval_conform_exp_size Hwf0 Hcf0)
            (eval_conform_exp_size Hwf1 Hcf1) .
    by rewrite (eqP Hszeq) .
  }
  move => {Hszeq} Hszrs1rs2 .
  exact : (bit_blast_shl_correct Hszrs1gt0 Hszrs1rs2 Hshl Hencls0 Hencls1 Hcs2) .
Qed .

Lemma bit_blast_exp_lshr :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e0 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e0 te ->
          enc_bits E lrs (QFBV.eval_exp e0 s)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e1 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e1 te ->
          enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Blshr e0 e1) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Blshr e0 e1) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Blshr e0 e1) s).
Proof.
  move => e0 IHe0 e1 IHe1 te m g s E m' g' cs lrs .
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] rs1] Hexp0] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] rs2] Hexp1] .
  dcase (bit_blast_lshr g2 rs1 rs2) => [[[g'0 cs0] rs] Hlshr] .
  case => <- _ <- <- /andP [Hcf0 Hcf1] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs0 /andP [Hcs1 Hcs2]] /andP [/andP [/andP [Hwf0 Hwf1] _] _] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp1) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp0) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ _ Hexp0 Hcf0 Hcon1 Hcs0 Hwf0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ _ Hexp1 Hcf1 Hcon Hcs1 Hwf1) => Hencls1.
  have : size rs1 > 0 .
  {
    move : (enc_bits_size Hencls0) .
    rewrite (eval_conform_exp_size Hwf0 Hcf0) => Hszrs1 .
    by rewrite -Hszrs1 in Hszgt0 .
  }
  move => {Hszgt0} Hszrs1gt0 .
  have : size rs1 = size rs2 .
  { 
    move : (enc_bits_size Hencls0) (enc_bits_size Hencls1) .
    case => -> -> .
    rewrite (eval_conform_exp_size Hwf0 Hcf0)
            (eval_conform_exp_size Hwf1 Hcf1) .
    by rewrite (eqP Hszeq) .
  }
  move => {Hszeq} Hszrs1rs2 .
  apply (bit_blast_lshr_correct Hlshr Hencls0 Hencls1 Hcs2) .
Qed .

Lemma bit_blast_exp_ashr :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e0 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e0 te ->
          enc_bits E lrs (QFBV.eval_exp e0 s)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e1 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e1 te ->
          enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator)
           (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bashr e0 e1) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bashr e0 e1) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bashr e0 e1) s).
Proof.
  move => e0 IHe0 e1 IHe1 te m g s E m' g' cs lrs .
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] rs1] Hexp0] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] rs2] Hexp1] .
  dcase (bit_blast_ashr g2 rs1 rs2) => [[[g'0 cs0] rs] Hashr] .
  case => <- _ <- <- /andP [Hcf0 Hcf1] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs0 /andP [Hcs1 Hcs2]] /andP [/andP [/andP [Hwf0 Hwf1] _] _].
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp1) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp0) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ _ Hexp0 Hcf0 Hcon1 Hcs0 Hwf0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ _ Hexp1 Hcf1 Hcon Hcs1 Hwf1) => Hencls1.
  have : size rs1 > 0 .
  {
    move : (enc_bits_size Hencls0) .
    rewrite (eval_conform_exp_size Hwf0 Hcf0) => Hszrs1 .
    by rewrite -Hszrs1 in Hszgt0 .
  }
  move => {Hszgt0} Hszrs1gt0 .
  have : size rs1 = size rs2 .
  { 
    move : (enc_bits_size Hencls0) (enc_bits_size Hencls1) .
    case => -> -> .
    rewrite (eval_conform_exp_size Hwf0 Hcf0)
            (eval_conform_exp_size Hwf1 Hcf1) .
    by rewrite (eqP Hszeq) .
  }
  move => {Hszeq} Hszrs1rs2 .
  apply (bit_blast_ashr_correct Hashr Hszrs1gt0 Hszrs1rs2 Hencls0 Hencls1 Hcs2) .
Qed .

Lemma bit_blast_exp_concat :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e0 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e0 te ->
          enc_bits E lrs (QFBV.eval_exp e0 s)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e1 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e1 te ->
          enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bconcat e0 e1) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bconcat e0 e1) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bconcat e0 e1) s).
Proof.
  move => e0 IHe0 e1 IHe1 te m g s E m' g' cs lrs .
  rewrite (lock interp_cnf) /= -lock .
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] rs1] Hexp0] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] rs2] Hexp1] .
  case => <- _ <- <- /andP [Hcf0 Hcf1] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs0 /andP [Hcs1 _]] /andP [/andP [/andP [Hwf0 Hwf1] _] _].
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp1) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp0) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ _ Hexp0 Hcf0 Hcon1 Hcs0 Hwf0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ _ Hexp1 Hcf1 Hcon Hcs1 Hwf1) => Hencls1.
  apply : (@bit_blast_concat_correct E g _ _ rs2 rs1 g _ _ _ Hencls1 Hencls0) .
  rewrite /bit_blast_concat // .
Qed .

Lemma bit_blast_exp_extract :
    forall (i j : nat) (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf)
              (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e te ->
          enc_bits E lrs (QFBV.eval_exp e s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Eunop (QFBV.Uextr i j) e) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uextr i j) e) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Eunop (QFBV.Uextr i j) e) s).
Proof.
  move=> i j e IH te m g s E m' g' cs lr .
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  case => <- _ <- <- Hcf Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcse Hcs0] Hwf .
  move: (IH _ _ _ _ _ _ _ _ _ Hexp Hcf Hcon Hcse Hwf) => Henc .
  apply : (@bit_blast_extract_correct E g _ _ _ _ _ _ _ _ Henc Hcs0) .
  rewrite /bit_blast_extract // .
Qed .

(*
Lemma bit_blast_exp_slice :
  forall (w1 w2 w3 : nat),
    forall (e : exp (w3 + w2 + w1)),
      (forall (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : (w3 + w2 +w1).-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV.eval_exp e s)) ->
    forall (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf)
           (lrs : w2.-tuple literal),
      bit_blast_exp m g (QFBV64.bvSlice w1 w2 w3 e) = (m', g', cs, lrs) ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      enc_bits E lrs (QFBV.eval_exp (QFBV64.bvSlice w1 w2 w3 e) s).
Proof.
  move=> w1 w2 w3 e IH m g s E m' g' cs lr .
  rewrite (lock interp_cnf) /= -lock. dcase_goal. case; intros; subst.
  rewrite !add_prelude_append in H5.
  move: H5 => /andP [Hcs0 _] .
  move: (IH _ _ _ _ _ _ _ _ H H4 Hcs0) => Henc .
  apply: bit_blast_slice_correct Henc Hcs0 .
Qed .
*)

Lemma bit_blast_exp_high :
    forall (n : nat) (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e te ->
          enc_bits E lrs (QFBV.eval_exp e s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Eunop (QFBV.Uhigh n) e) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uhigh n) e) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Eunop (QFBV.Uhigh n) e) s).
Proof.
  move=> n e IH te m g s E m' g' cs lr .
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  case => <- _ <- <- Hcf Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcse Hcs0] Hwf .
  move: (IH _ _ _ _ _ _ _ _ _ Hexp Hcf Hcon Hcse Hwf) => Henc .
  apply: (@bit_blast_high_correct _ g _ _ _ g _ _ _ Henc Hcs0) .
  rewrite /bit_blast_high // .
Qed .

Lemma bit_blast_exp_low :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e te ->
          enc_bits E lrs (QFBV.eval_exp e s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop (QFBV.Ulow n) e) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Eunop (QFBV.Ulow n) e) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Ulow n) e) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Eunop (QFBV.Ulow n) e) s).
Proof.
  move=> n e IH te m g s E m' g' cs lr .
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  case => <- _ <- <- Hcf Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcse Hcs0] Hwf .
  move: (IH _ _ _ _ _ _ _ _ _ Hexp Hcf Hcon Hcse Hwf) => Henc .
  apply: (@bit_blast_low_correct _ g _ _ _ g _ _ _ Henc Hcs0) .
  rewrite /bit_blast_low // .
Qed .

Lemma bit_blast_exp_zeroextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e te ->
          enc_bits E lrs (QFBV.eval_exp e s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop (QFBV.Uzext n) e) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Eunop (QFBV.Uzext n) e) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uzext n) e) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Eunop (QFBV.Uzext n) e) s).
Proof.
  move=> n e IH te m g s E m' g' cs lr .
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  case => <- _ <- <- Hcf Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcse Hcs0] Hwf .
  move: (IH _ _ _ _ _ _ _ _ _ Hexp Hcf Hcon Hcse Hwf) => Henc .
  apply: (@bit_blast_zeroextend_correct _ g _ _ _ g _ _ _ Henc Hcs0) .
  rewrite /bit_blast_zeroextend // .
Qed .

Lemma bit_blast_exp_signextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e te ->
          enc_bits E lrs (QFBV.eval_exp e s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Eunop (QFBV.Usext n) e) = (m', g', cs, lrs) ->
    AdhereConform.conform_exp (QFBV.Eunop (QFBV.Usext n) e) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Eunop (QFBV.Usext n) e) te ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Eunop (QFBV.Usext n) e) s).
Proof.
  move => n e IH te m g s E m' g' cs lr .
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  case => <- _ <- <- Hcf Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcse Hcs0] Hwf .
  move: (IH _ _ _ _ _ _ _ _ _ Hexp Hcf Hcon Hcse Hwf) => Henc .
  apply : (@bit_blast_signextend_correct _ g _ _ _ g _ _ _ Henc Hcs0) .
  rewrite /bit_blast_signextend // .
Qed .

Lemma bit_blast_exp_ite :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp te m g b = (m', g', cs, lr) ->
        AdhereConform.conform_bexp b s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp b te ->
        enc_bit E lr (QFBV.eval_bexp b s)) ->
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e te ->
          enc_bits E lrs (QFBV.eval_exp e s)) ->
      forall (e0 : QFBV.exp),
        (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
            bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
            AdhereConform.conform_exp e0 s te ->
            consistent m' E s ->
            interp_cnf E (add_prelude cs) ->
            QFBV.well_formed_exp e0 te ->
            enc_bits E lrs (QFBV.eval_exp e0 s)) ->
        forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
               (m' : vm) (g' : generator)
               (cs : cnf) (lrs : word),
          bit_blast_exp te m g (QFBV.Eite b e e0) = (m', g', cs, lrs) ->
          AdhereConform.conform_exp (QFBV.Eite b e e0) s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp (QFBV.Eite b e e0) te ->
          enc_bits E lrs (QFBV.eval_exp (QFBV.Eite b e e0) s) .
Proof.
  move=> c IHc e1 IH1 e2 IH2 te m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_bexp te m g c) => [[[[mc gc] csc] lc] Hexpc] .
  dcase (bit_blast_exp te mc gc e1) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_ite g2 lc ls1 ls2) => [[[gr csr] lsr] Hite] .
  case => <- _ <- <- /andP [/andP [Hcfc Hcf1] Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs0 /andP [Hcs1 /andP [Hcs2 Hcs3]]]
          /andP [/andP [/andP [Hwfc Hwf1] Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp2) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp1) Hcon1) => Hcon0.
  move: (IHc _ _ _ _ _ _ _ _ _ Hexpc Hcfc Hcon0 Hcs0 Hwfc) => Hencl.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hexp1 Hcf1 Hcon1 Hcs1 Hwf1) => Hencls.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hexp2 Hcf2 Hcon Hcs2 Hwf2) => Hencls0.
  apply: (bit_blast_ite_correct _ Hite Hencl Hencls Hencls0 Hcs3).
  rewrite (enc_bits_size Hencls) (enc_bits_size Hencls0)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_false :
  forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g QFBV.Bfalse = (m', g', cs, lr) ->
    AdhereConform.conform_bexp QFBV.Bfalse s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp QFBV.Bfalse te ->
    enc_bit E lr (QFBV.eval_bexp QFBV.Bfalse s).
Proof.
  move=> te im ig s E om og ocs olr [] <- _ <- <- Hcf Hcon Hcs _ /=.
  exact: (add_prelude_enc_bit_ff Hcs).
Qed.

Lemma bit_blast_bexp_true :
  forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g QFBV.Btrue = (m', g', cs, lr) ->
    AdhereConform.conform_bexp QFBV.Btrue s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp QFBV.QFBV.Btrue te ->
    enc_bit E lr (QFBV.QFBV.eval_bexp QFBV.QFBV.Btrue s).
Proof.
  move=> te im ig s E om og ocs olr [] <- _ <- <- Hcf Hcon Hcs _ /=.
  exact: (add_prelude_enc_bit_tt Hcs).
Qed.

Lemma bit_blast_bexp_eq :
  forall (e : QFBV.exp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e te ->
             enc_bits E lrs (QFBV.eval_exp e s))
         (e0 : QFBV.exp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e0 te ->
             enc_bits E lrs (QFBV.eval_exp e0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Beq e e0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Beq e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Beq e e0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq e e0) s).
Proof.
  move=> e1 IH1 e2 IH2 te im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp te im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblasteq: (bit_blast_eq g2 rs1 rs2) => [[geq cseq] req].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcseq]] /andP [/andP [Hwf1 Hwf2] Hsize].
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast1) Hcon1) => Hcon2.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon1 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_eq_correct Hblasteq _ Henc1 Henc2 Hcseq) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_ult :
  forall (e : QFBV.exp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e te ->
             enc_bits E lrs (QFBV.eval_exp e s))
         (e0 : QFBV.exp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e0 te ->
             enc_bits E lrs (QFBV.eval_exp e0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bult e e0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bult e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bult e e0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bult e e0) s).
Proof.
  move=> e1 IH1 e2 IH2 te im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp te im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastult: (bit_blast_ult g2 rs1 rs2) => [[gult csult] rult].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsult]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon2 .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_ult_correct Hblastult Henc1 Henc2 Hcsult) .
Qed.

Lemma bit_blast_bexp_ule :
  forall (e : QFBV.exp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e te ->
             enc_bits E lrs (QFBV.eval_exp e s))
         (e0 : QFBV.exp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e0 te ->
             enc_bits E lrs (QFBV.eval_exp e0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bule e e0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bule e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bule e e0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bule e e0) s).
Proof.
  move=> e1 IH1 e2 IH2 te im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp te im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastule: (bit_blast_ule g2 rs1 rs2) => [[gule csule] rule].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsule]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_ule_correct Hblastule _ Henc1 Henc2 Hcsule) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_ugt :
  forall (e : QFBV.exp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e te ->
             enc_bits E lrs (QFBV.eval_exp e s))
         (e0 : QFBV.exp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e0 te ->
             enc_bits E lrs (QFBV.eval_exp e0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bugt e e0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bugt e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bugt e e0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bugt e e0) s).
Proof.
  move=> e1 IH1 e2 IH2 te im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp te im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastugt: (bit_blast_ugt g2 rs1 rs2) => [[gugt csugt] rugt].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsugt]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_ugt_correct Hblastugt Henc1 Henc2 Hcsugt) .
Qed.

Lemma bit_blast_bexp_uge :
  forall (e : QFBV.exp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e te ->
             enc_bits E lrs (QFBV.eval_exp e s))
         (e0 : QFBV.exp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e0 te ->
             enc_bits E lrs (QFBV.eval_exp e0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Buge e e0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Buge e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Buge e e0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Buge e e0) s).
Proof.
  move=> e1 IH1 e2 IH2 te im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp te im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastuge: (bit_blast_uge g2 rs1 rs2) => [[guge csuge] ruge].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsuge]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_uge_correct Hblastuge _ Henc1 Henc2 Hcsuge) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_slt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e1 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e2 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e2 te ->
          enc_bits E lrs (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', g', cs, lr) ->
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bslt e1 e2) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bslt e1 e2) te ->
        enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bslt e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_slt g2 ls1 ls2) => [[gr csr] r].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsslt]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_slt_correct Hr Henc1 Henc2 Hcsslt) .
Qed.

Lemma bit_blast_bexp_sle :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e1 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e2 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e2 te ->
          enc_bits E lrs (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', g', cs, lr) ->
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsle e1 e2) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsle e1 e2) te ->
        enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bsle e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_sle g2 ls1 ls2) => [[gr csr] r].
  case=> <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat.
  move => /andP [Hic1 /andP [Hic2 Hicr]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcon1) => Hcon2.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcon1 Hic1 Hwf1) => Henc1 .
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcon Hic2 Hwf2) => Henc2 .
  apply: (bit_blast_sle_correct Hr _ Henc1 Henc2 Hicr).
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_sgt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e1 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e2 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e2 te ->
          enc_bits E lrs (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', g', cs, lr) ->
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsgt e1 e2) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsgt e1 e2) te ->
        enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bsgt e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_sgt g2 ls1 ls2) => [[gr csr] r].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsult]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_sgt_correct Hr Henc1 Henc2 Hcsult) .
Qed.

Lemma bit_blast_bexp_sge :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e1 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e2 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e2 te ->
          enc_bits E lrs (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', g', cs, lr) ->
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsge e1 e2) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsge e1 e2) te ->
        enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bsge e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_sge g2 ls1 ls2) => [[gr csr] r].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsult]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_sge_correct Hr _ Henc1 Henc2 Hcsult) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_uaddo :
  forall (e : QFBV.exp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e te ->
             enc_bits E lrs (QFBV.eval_exp e s))
         (e0 : QFBV.exp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e0 te ->
             enc_bits E lrs (QFBV.eval_exp e0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Buaddo e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Buaddo e e0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Buaddo e e0) s).
Proof.
  move=> e1 IH1 e2 IH2 te im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp te im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastuaddo: (bit_blast_uaddo g2 rs1 rs2) => [[guaddo csuaddo] ruaddo].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsult]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_uaddo_correct Hblastuaddo _ Henc1 Henc2 Hcsult) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_usubo :
  forall (e : QFBV.exp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e te ->
             enc_bits E lrs (QFBV.eval_exp e s))
         (e0 : QFBV.exp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e0 te ->
             enc_bits E lrs (QFBV.eval_exp e0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Busubo e e0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Busubo e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Busubo e e0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Busubo e e0) s).
Proof.
  move=> e1 IH1 e2 IH2 te im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp te im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastusubo: (bit_blast_usubo g2 rs1 rs2) => [[gusubo csusubo] rusubo].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsult]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_usubo_correct Hblastusubo _ Henc1 Henc2 Hcsult) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_umulo :
  forall (e : QFBV.exp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e te ->
             enc_bits E lrs (QFBV.eval_exp e s))
         (e0 : QFBV.exp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e0 te ->
             enc_bits E lrs (QFBV.eval_exp e0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bumulo e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bumulo e e0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bumulo e e0) s).
Proof.
  move=> e1 IH1 e2 IH2 te im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp te im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastumulo: (bit_blast_umulo g2 rs1 rs2) => [[gumulo csumulo] rumulo].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsult]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_umulo_correct Hblastumulo _ Henc1 Henc2 Hcsult) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_saddo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e1 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e2 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e2 te ->
          enc_bits E lrs (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', g', cs, lr) ->
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsaddo e1 e2) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsaddo e1 e2) te ->
        enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bsaddo e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_saddo g2 ls1 ls2) => [[gr csr] r].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsult]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_saddo_correct Hr _ Henc1 Henc2 Hcsult) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_ssubo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e1 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e2 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e2 te ->
          enc_bits E lrs (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', g', cs, lr) ->
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bssubo e1 e2) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bssubo e1 e2) te ->
        enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bssubo e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_ssubo g2 ls1 ls2) => [[gr csr] r].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsult]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_ssubo_correct Hr _ Henc1 Henc2 Hcsult) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_smulo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e1 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e2 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e2 te ->
          enc_bits E lrs (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', g', cs, lr) ->
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsmulo e1 e2) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsmulo e1 e2) te ->
        enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bsmulo e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_smulo g2 ls1 ls2) => [[gr csr] r].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsult]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_smulo_correct Hr _ Henc1 Henc2 Hcsult) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_lneg :
  forall (b : QFBV.bexp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
             bit_blast_bexp te m g b = (m', g', cs, lr) ->
             AdhereConform.conform_bexp b s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_bexp b te ->
             enc_bit E lr (QFBV.eval_bexp b s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Blneg b) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Blneg b) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Blneg b) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Blneg b) s).
Proof.
  move=> e1 IH te m g s E m' g' cs lr.
  rewrite /bit_blast_bexp /= -/bit_blast_bexp.
  case Hblast : (bit_blast_bexp te m g e1) => [[[m1 g1 ]cs1] r1].
  case => <- _ <- <- Hcf Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 Hocs] Hwf .
  move: (IH _ _ _ _ _ _ _ _ _ Hblast Hcf Hcon Hcs1 Hwf) => Henc.
  apply: (@bit_blast_lneg_correct g1 _ _ _ _ _ _ _ Henc Hocs).
  rewrite /bit_blast_lneg // .
Qed.

Lemma bit_blast_bexp_conj :
  forall (b : QFBV.bexp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
             bit_blast_bexp te m g b = (m', g', cs, lr) ->
             AdhereConform.conform_bexp b s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_bexp b te ->
             enc_bit E lr (QFBV.eval_bexp b s))
         (b0 : QFBV.bexp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
             bit_blast_bexp te m g b0 = (m', g', cs, lr) ->
             AdhereConform.conform_bexp b0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_bexp b0 te ->
             enc_bit E lr (QFBV.eval_bexp b0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bconj b b0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bconj b b0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bconj b b0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bconj b b0) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lr.
  rewrite /bit_blast_bexp /= -/bit_blast_bexp.
  case Hblast1: (bit_blast_bexp te m g e1) => [[[m1 g1] cs1] r1].
  case Hblast2: (bit_blast_bexp te m1 g1 e2) => [[[m2 g2] cs2] r2].
  case=> <- _ <- <- /andP [Hcf1 Hcf2] Hcon.
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hocs]] /andP [Hwf1 Hwf2] .
  move: (vm_preserve_consistent (bit_blast_bexp_preserve Hblast2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_bexp_preserve Hblast1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (@bit_blast_conj_correct g2 _ _ _ _ _ _ _ _ _ Henc1 Henc2 Hocs) .
  rewrite /bit_blast_conj // .
Qed.

Lemma bit_blast_bexp_disj :
  forall (b : QFBV.bexp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
             bit_blast_bexp te m g b = (m', g', cs, lr) ->
             AdhereConform.conform_bexp b s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_bexp b te ->
             enc_bit E lr (QFBV.eval_bexp b s))
         (b0 : QFBV.bexp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
             bit_blast_bexp te m g b0 = (m', g', cs, lr) ->
             AdhereConform.conform_bexp b0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_bexp b0 te ->
             enc_bit E lr (QFBV.eval_bexp b0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bdisj b b0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bdisj b b0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bdisj b b0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bdisj b b0) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lr.
  rewrite /bit_blast_bexp /= -/bit_blast_bexp.
  case Hblast1: (bit_blast_bexp te m g e1) => [[[m1 g1] cs1] r1].
  case Hblast2: (bit_blast_bexp te m1 g1 e2) => [[[m2 g2] cs2] r2].
  case=> <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hocs]] /andP [Hwf1 Hwf2] .
  move: (vm_preserve_consistent (bit_blast_bexp_preserve Hblast2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_bexp_preserve Hblast1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (@bit_blast_disj_correct g2 _ _ _ _ _ _ _ _ _ Henc1 Henc2 Hocs) .
  rewrite /bit_blast_disj // .
Qed.

Corollary bit_blast_exp_correct :
  forall (e : QFBV.exp) te m g s E m' g' cs lrs,
    bit_blast_exp te m g e = (m', g', cs, lrs) ->
    AdhereConform.conform_exp e s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp e te ->
    enc_bits E lrs (QFBV.eval_exp e s)
  with
    bit_blast_bexp_correct :
      forall (e : QFBV.bexp) te m g s E m' g' cs lr,
        bit_blast_bexp te m g e = (m', g', cs, lr) ->
        AdhereConform.conform_bexp e s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp e te ->
        enc_bit E lr (QFBV.eval_bexp e s) .
Proof .
  (* bit_blast_exp_correct *)
  move => e te m g s E m' g' cs lrs .
  case : e .
  - move => v; apply : bit_blast_exp_var .
  - move => bs; apply : bit_blast_exp_const .
  - elim .
    + move => e; apply : bit_blast_exp_not; apply : bit_blast_exp_correct .
    + move => e; apply : bit_blast_exp_neg; apply bit_blast_exp_correct .
    + move => i j e; apply : bit_blast_exp_extract; apply bit_blast_exp_correct .
    + move => n e; apply : bit_blast_exp_high; apply bit_blast_exp_correct .
    + move => n e; apply : bit_blast_exp_low; apply bit_blast_exp_correct .
    + move => n e; apply : bit_blast_exp_zeroextend; apply bit_blast_exp_correct .
    + move => n e; apply : bit_blast_exp_signextend; apply bit_blast_exp_correct .
  - elim; move => e0 e1 .
    + apply : bit_blast_exp_and; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_or; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_xor; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_add; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_sub; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_mul; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_mod; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_srem; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_smod; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_shl; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_lshr; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_ashr; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_concat; apply bit_blast_exp_correct .
  - move => b e0 e1;
      apply bit_blast_exp_ite;
      first apply : bit_blast_bexp_correct;
      apply : bit_blast_exp_correct .
  (* bit_blast_bexp_correct *)
  elim .
  - exact : bit_blast_bexp_false .
  - exact : bit_blast_bexp_true .
  - elim => e0 e1 .
    + apply : bit_blast_bexp_eq; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_ult; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_ule; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_ugt; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_uge; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_slt; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_sle; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_sgt; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_sge; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_uaddo; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_usubo; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_umulo; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_saddo; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_ssubo; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_smulo; apply : bit_blast_exp_correct .
  - apply : bit_blast_bexp_lneg .
  - apply : bit_blast_bexp_conj .
  - apply : bit_blast_bexp_disj .
Qed.

