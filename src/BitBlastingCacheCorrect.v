From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport AdhereConform
     Cache BitBlastingCacheDef BitBlastingCacheWF BitBlastingCachePreserve .

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* = bit_blast_exp_cache_correct_cache and bit_blast_bexp_cache_correct_cache = *)

Lemma bit_blast_exp_cache_correct_nocache_var :
  forall (t : SSAVarOrder.t) (te : SSATE.env) (m : SSAVM.t word) 
         (ca : cache) (g : generator) (s : SSAStore.t) (E : env) 
         (m' : vm) (ca' : cache) (g' : generator) (cs : cnf) (lrs : word),
    find_cet (QFBV.Evar t) ca = None ->
    find_het (QFBV.Evar t) ca = None ->
    bit_blast_exp_cache te m ca g (QFBV.Evar t) = (m', ca', g', cs, lrs) ->
    conform_exp (QFBV.Evar t) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Evar t) te ->
    well_formed ca ->
    correct E s ca ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Evar t) s) /\ correct E s ca'.
Proof.
  move=> v te im ica ig s E om oca og ocs olrs. 
  move=> Hfcet Hfhet Hblast _ Hcon _ Hwf Hwfica HcEsica.
  move: (Hcon v) Hblast => {Hcon} Hcon. rewrite /= Hfcet Hfhet.
  case Hfind: (SSAVM.find v im).
  - case=> Hm Hca Hg Hcs Hlrs. move: Hcon; rewrite /consistent1.
    rewrite -Hm -Hca Hfind Hlrs /=. 
    move=> Henc. split; first done.
    apply correct_add_het. split; last done. by rewrite -correct_add_cet.
  - case Hblast: (bit_blast_var te ig v) => [[vg vcs] vlrs].
    case=> [Hom Hoca Hog Hocs Holrs]. move: Hcon; rewrite /consistent1.
    rewrite -Hom -Hoca. rewrite (SSAVM.Lemmas.find_add_eq (eq_refl v)).
    rewrite Holrs /=. move=> Henc. split; first done.
    apply correct_add_het. split; last done. by rewrite -correct_add_cet.
Qed.

Lemma bit_blast_exp_cache_correct_nocache_and :
  forall e : QFBV.exp,
    (forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
            (g : generator) (s : SSAStore.t) (E : env) (m' : vm) 
            (ca' : cache) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp_cache te m ca g e = (m', ca', g', cs, lrs) ->
        conform_exp e s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e te ->
        well_formed ca ->
        correct E s ca -> 
        enc_bits E lrs (QFBV.eval_exp e s) /\ correct E s ca') ->
    forall e0 : QFBV.exp,
      (forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
              (g : generator) (s : SSAStore.t) (E : env) (m' : vm) 
              (ca' : cache) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp_cache te m ca g e0 = (m', ca', g', cs, lrs) ->
          conform_exp e0 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e0 te ->
          well_formed ca ->
          correct E s ca -> 
          enc_bits E lrs (QFBV.eval_exp e0 s) /\ correct E s ca') ->
      forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
             (g : generator) (s : SSAStore.t) (E : env) (m' : vm) 
             (ca' : cache) (g' : generator) (cs : cnf) (lrs : word),
        find_cet (QFBV.Ebinop QFBV.Band e e0) ca = None ->
        find_het (QFBV.Ebinop QFBV.Band e e0) ca = None ->
        bit_blast_exp_cache te m ca g (QFBV.Ebinop QFBV.Band e e0) =
        (m', ca', g', cs, lrs) ->
  conform_exp (QFBV.Ebinop QFBV.Band e e0) s te ->
  consistent m' E s ->
  interp_cnf E (add_prelude cs) ->
  QFBV.well_formed_exp (QFBV.Ebinop QFBV.Band e e0) te ->
  well_formed ca ->
  correct E s ca ->
  enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Band e e0) s) /\ correct E s ca'.
Proof.
  move=> e1 IH1 e2 IH2 te m ca g s E m' ca' g' cs lrs Hfcet Hfhet.
  rewrite (lock interp_cnf) /= -lock Hfcet Hfhet /=.
  case He1 : (bit_blast_exp_cache te m ca g e1) => [[[[m1 ca1] g1] cs1] ls1].
  case He2 : (bit_blast_exp_cache te m1 ca1 g1 e2) => [[[[m2 ca2] g2] cs2] ls2].
  case Hr : (bit_blast_and g2 ls1 ls2) => [[gr csr] lsr].
  case=> <- <- _ <- <-. move=> /andP [Hcf1 Hcf2] Hcons2.
  move: (vm_preserve_consistent (bit_blast_exp_cache_preserve He2) Hcons2) => Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_cache_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_catrev. move/andP=> [Hic1 /andP [Hic2 Hicr]] .
  move => /andP [/andP [Hwf1 Hwf2] _] .
  move=> Hwfca.
  move: (bit_blast_exp_cache_well_formed He1 Hwfca) => Hwfca1.
  move: (bit_blast_exp_cache_well_formed He2 Hwfca1) => Hwfca2.
  move=> HcEsca.
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcons1 Hic1 Hwf1 Hwfca HcEsca) 
  => [Henc1 HcEsca1].
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcons2 Hic2 Hwf2 Hwfca1 HcEsca1) 
  => [Henc2 HcEsca2].
  have Hencr : enc_bits E lsr (QFBV.eval_exp e1 s &&# QFBV.eval_exp e2 s)%bits
    by apply: (bit_blast_and_correct Hr _ _ Hicr).    
  split; first done.
  (* correct E s ca' *)
  apply correct_add_het. split; last done. by apply correct_add_cet. 
Qed.

Lemma bit_blast_bexp_cache_correct_cache_conj :
forall b1 : QFBV.bexp,
  (forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
          (g : generator) (s : SSAStore.t) (E : env) (m' : vm) 
          (ca' : cache) (g' : generator) (cs : cnf) (lr : literal),
      bit_blast_bexp_cache te m ca g b1 = (m', ca', g', cs, lr) ->
      conform_bexp b1 s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_bexp b1 te ->
      well_formed ca ->
      correct E s ca -> 
      enc_bit E lr (QFBV.eval_bexp b1 s) /\ correct E s ca') ->
  forall b2 : QFBV.bexp,
    (forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
            (g : generator) (s : SSAStore.t) (E : env) (m' : vm) 
            (ca' : cache) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp_cache te m ca g b2 = (m', ca', g', cs, lr) ->
        conform_bexp b2 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp b2 te ->
        well_formed ca ->
        correct E s ca -> 
        enc_bit E lr (QFBV.eval_bexp b2 s) /\ correct E s ca') ->
    forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
           (g : generator) (s : SSAStore.t) (E : env) (m' : vm) 
           (ca' : cache) (g' : generator) (cs : cnf) (lr : literal),
      find_cbt (QFBV.Bconj b1 b2) ca = None ->
      find_hbt (QFBV.Bconj b1 b2) ca = None ->
      bit_blast_bexp_cache te m ca g (QFBV.Bconj b1 b2) = (m', ca', g', cs, lr) ->
      conform_bexp (QFBV.Bconj b1 b2) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_bexp (QFBV.Bconj b1 b2) te ->
      well_formed ca ->
      correct E s ca ->
      enc_bit E lr (QFBV.eval_bexp (QFBV.Bconj b1 b2) s) /\ correct E s ca'.
Proof.
  move=> e1 IH1 e2 IH2 te m ca g s E m' ca' g' cs lr Hfcbt Hfhbt.
  rewrite /bit_blast_bexp_cache /= -/bit_blast_bexp_cache Hfcbt Hfhbt. 
  case Hblast1: (bit_blast_bexp_cache te m ca g e1) => [[[[m1 ca1] g1] cs1] r1].
  case Hblast2: (bit_blast_bexp_cache te m1 ca1 g1 e2) => [[[[m2 ca2] g2] cs2] r2].
  case=> <- <- _ <- <- /andP [Hcf1 Hcf2] Hcon.
  rewrite !add_prelude_catrev .
  move => /andP [Hcs1 /andP [Hcs2 Hocs]] /andP [Hwf1 Hwf2] .
  move: (vm_preserve_consistent (bit_blast_bexp_cache_preserve Hblast2) Hcon) 
  => Hcon1.
  move: (vm_preserve_consistent (bit_blast_bexp_cache_preserve Hblast1) Hcon1) 
  => Hcon0.
  move=> Hwfca.
  move: (bit_blast_bexp_cache_well_formed Hblast1 Hwfca) => Hwfca1.
  move: (bit_blast_bexp_cache_well_formed Hblast2 Hwfca1) => Hwfca2.
  move=> HcEsca.
  move: (IH1 _ _ _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon1 Hcs1 Hwf1 Hwfca HcEsca) 
  => [Henc1 HcEsca1].
  move: (IH2 _ _ _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2 Hwfca1 HcEsca1) 
  => [Henc2 HcEsca2].
  have Hencr : enc_bit E (Pos g2) (QFBV.eval_bexp e1 s && QFBV.eval_bexp e2 s)
    by apply : (@bit_blast_conj_correct g2 _ _ _ _ _ _ _ _ _ Henc1 Henc2 Hocs) .
  split; first done.
  (* correct E s ca' *)
  apply correct_add_hbt. split; last done. by apply correct_add_cbt. 
Qed.


Corollary bit_blast_exp_cache_correct_cache :
  forall (e : QFBV.exp) te m ca g s E m' ca' g' cs lrs,
    bit_blast_exp_cache te m ca g e = (m', ca', g', cs, lrs) ->
    AdhereConform.conform_exp e s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp e te ->
    Cache.well_formed ca -> Cache.correct E s ca ->
    enc_bits E lrs (QFBV.eval_exp e s) /\ Cache.correct E s ca'
  with
    bit_blast_bexp_cache_correct_cache :
      forall (e : QFBV.bexp) te m ca g s E m' ca' g' cs lr,
        bit_blast_bexp_cache te m ca g e = (m', ca', g', cs, lr) ->
        AdhereConform.conform_bexp e s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp e te ->
        Cache.well_formed ca -> Cache.correct E s ca ->
        enc_bit E lr (QFBV.eval_bexp e s) /\ Cache.correct E s ca'.
Proof.
  (* bit_blast_exp_cache_correct_cache *)
  move=> e te m ca g s E m' ca' g' cs lrs.
  case Hfcet: (find_cet e ca) => [ls|]. 
  - rewrite bit_blast_exp_cache_equation Hfcet /=.
    case=> _ <- _ _ <-. move=> _ _ _ _ Hwfca HcEsca. 
    split; last done.
    move: (Cache.correct_well_formed_correct_ct HcEsca Hwfca) => [Hct _].
    by apply (Hct _ _ Hfcet).
  - case Hfhet: (find_het e ca) => [[csh lsh]|].
    + rewrite bit_blast_exp_cache_equation Hfcet Hfhet /=. 
      case=> _ <- _ _ <-. move=> _ _ _ _ _ HcEsca.
      split; last by rewrite -correct_add_cet.
      move: HcEsca => [Hht _]. by apply (Hht _ _ _ Hfhet).
    + move: e te m ca g s E m' ca' g' cs lrs Hfcet Hfhet.
      case.
      * exact: bit_blast_exp_cache_correct_nocache_var.
      * admit. (* bit_blast_exp_const  *)
      * elim. 
        -- admit. (* bit_blast_exp_not *)
        -- admit. (* bit_blast_exp_neg *)
        -- admit. (* bit_blast_exp_extract *)
        -- admit. (* bit_blast_exp_high *)
        -- admit. (* bit_blast_exp_low *)
        -- admit. (* bit_blast_exp_zeroextend *)
        -- admit. (* : bit_blast_exp_signextend; apply bit_blast_exp_correct . *)
      * elim.
        -- move=> e1 e2; apply bit_blast_exp_cache_correct_nocache_and;
                    by apply bit_blast_exp_cache_correct_cache.
        -- admit. (* apply : bit_blast_exp_or; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_xor; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_add; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_sub; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_mul; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_mod; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_srem; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_smod; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_shl; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_lshr; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_ashr; apply bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_exp_concat; apply bit_blast_exp_correct . *)
      * admit. (* move => b e1 e2; *)
      (* apply bit_blast_exp_ite; *)
      (* first apply : bit_blast_bexp_correct; *)
      (* apply : bit_blast_exp_correct . *)
  (* bit_blast_bexp_cache_correct_cache *)
  move=> e te m ca g s E m' ca' g' cs lr.
  case Hfcbt: (find_cbt e ca) => [l|]. 
  - rewrite bit_blast_bexp_cache_equation Hfcbt /=.
    case=> _ <- _ _ <-. move=> _ _ _ _ Hwfca HcEsca. 
    split; last done.
    move: (Cache.correct_well_formed_correct_ct HcEsca Hwfca) => [_ Hct].
    by apply (Hct _ _ Hfcbt).
  - case Hfhbt: (find_hbt e ca) => [[csh lh]|].
    + rewrite bit_blast_bexp_cache_equation Hfcbt Hfhbt /=. 
      case=> _ <- _ _ <-. move=> _ _ _ _ _ HcEsca.
      split; last by rewrite -correct_add_cbt.
      move: HcEsca => [_ Hht]. by apply (Hht _ _ _ Hfhbt).
    + move: e te m ca g s E m' ca' g' cs lr Hfcbt Hfhbt.
      case.
      * admit. (* exact : bit_blast_bexp_false . *)
      * admit. (* exact : bit_blast_bexp_true . *)
      * elim => e1 e2 .
        -- admit. (* apply : bit_blast_bexp_eq; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_ult; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_ule; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_ugt; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_uge; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_slt; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_sle; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_sgt; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_sge; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_uaddo; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_usubo; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_umulo; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_saddo; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_ssubo; apply : bit_blast_exp_correct . *)
        -- admit. (* apply : bit_blast_bexp_smulo; apply : bit_blast_exp_correct . *)
      * admit. (* apply : bit_blast_bexp_lneg . *)
      * move=> b1 b2; apply: bit_blast_bexp_cache_correct_cache_conj;
                 by apply: bit_blast_bexp_cache_correct_cache.
      * admit. (* apply : bit_blast_bexp_disj . *)
Admitted.


(* = bit_blast_exp_cache_correct and bit_blast_bexp_cache_correct = *)

Corollary bit_blast_exp_cache_correct :
  forall (e : QFBV.exp) te m ca g s E m' ca' g' cs lrs,
    bit_blast_exp_cache te m ca g e = (m', ca', g', cs, lrs) ->
    AdhereConform.conform_exp e s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp e te ->
    Cache.well_formed ca -> Cache.correct E s ca ->
    enc_bits E lrs (QFBV.eval_exp e s).
Proof. 
  move=> e te m ca g s E m' ca' g' cs lrs Hbb Hcf Hcon Hcnf Hwf Hwfca Hcr. 
  move: (bit_blast_exp_cache_correct_cache Hbb Hcf Hcon Hcnf Hwf Hwfca Hcr) => [H _].
  done.
Qed.

Corollary bit_blast_bexp_cache_correct :
  forall (e : QFBV.bexp) te m ca g s E m' ca' g' cs lr,
    bit_blast_bexp_cache te m ca g e = (m', ca', g', cs, lr) ->
    AdhereConform.conform_bexp e s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp e te ->
    Cache.well_formed ca -> Cache.correct E s ca ->
    enc_bit E lr (QFBV.eval_bexp e s).
Proof.
  move=> e te m ca g s E m' ca' g' cs lr Hbb Hcf Hcon Hcnf Hwf Hwfca Hcr. 
  move: (bit_blast_bexp_cache_correct_cache Hbb Hcf Hcon Hcnf Hwf Hwfca Hcr) => [H _].
  done.
Qed.
