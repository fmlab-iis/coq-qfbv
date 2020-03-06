From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport 
     AdhereConform.
(* From BBCache Require Import Cache BitBlastingCacheDef BitBlastingCacheNewer  *)
(*      BitBlastingCachePreserve BitBlastingCacheCorrect BitBlastingCacheMkEnv  *)
(*      BitBlastingCacheConsistent BitBlastingCacheSat BitBlastingCacheAdhere *)
(*      BitBlastingCacheBound. *)
From newBBCache Require Import CompTable CompCache BitBlastingCCacheDef 
     BitBlastingCCachePreserve BitBlastingCCacheFind BitBlastingCCacheCorrect
     BitBlastingInit BitBlastingCCacheAdhere BitBlastingCCacheBound
     BitBlastingCCacheComplete BitBlastingCCacheDefGen.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Lemma mk_state_conform_bexps :
  forall es te E m',
    bound_bexps es m' ->
    AdhereConform.adhere m' te ->
    AdhereConform.conform_bexps es (mk_state E m') te .
Proof .
Admitted.


Theorem bit_blast_ccache_complete_general :
  forall (e : QFBV.bexp) (es: seq QFBV.bexp) te m c g cs lr,
    bit_blast_bexps_ccache te (e::es) = (m, c, g, cs, lr) ->
    well_formed_bexps (e::es) te ->
    (forall s, AdhereConform.conform_bexps (e::es) s te ->
               QFBV.eval_bexp e s)
    ->
    ~ (sat (add_prelude ([::neg_lit lr]::cs))).
Proof.
  move=> e es te m' c' g' cs' lr' Hbb Hwf He.
  move=> [E Hcs].
  rewrite add_prelude_cons in Hcs. move/andP: Hcs => [Hlr Hcs].
  rewrite add_prelude_expand in Hlr. move/andP: Hlr => [Htt Hlr].
  rewrite /= interp_lit_neg_lit in Hlr.
  move : (bit_blast_bexps_ccache_adhere Hbb) => Hadm' .
  move : (bit_blast_bexps_ccache_bound Hbb) => Hbound .
  move : (mk_state_conform_bexps E Hbound Hadm') => Hcf .
  move : (He (mk_state E m') Hcf) => {He} He .
  move: Hbb => /=.
  case Hbbes: (bit_blast_bexps_ccache te es) => [[[[m c] g] cs] lr].
  move: Hwf Hcf => /= /andP [Hwfe Hwfes] /andP [Hcfe Hcfes] Hbbe. 
  move: (bit_blast_bexps_ccache_correct_cache Hbbes Hwfes) => Hcr.
  move: (correct_reset_ct Hcr) => {Hcr} Hcr.
  move: (bit_blast_bexp_ccache_correct Hbbe Hcfe (mk_state_consistent E m') 
                                       Hwfe (reset_ct_well_formed c)
                                       Hcs (interp_cache_ct_reset_ct E c) Hcr).
  rewrite /enc_bit => /eqP H. rewrite -H in He.
  rewrite He in Hlr. exact: not_false_is_true.
Qed.

