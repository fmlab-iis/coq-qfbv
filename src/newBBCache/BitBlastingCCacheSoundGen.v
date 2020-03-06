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
     BitBlastingCCacheMkEnv BitBlastingCCacheConsistent BitBlastingCCacheSat
     BitBlastingCCacheCompleteGen BitBlastingCCacheDefGen BitBlastingCCacheSound.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ===== generalized mk_env ===== *)

Definition mk_env_ccache (s : SSAStore.t) (es : seq QFBV.bexp) : env :=
  let '(m, c, E, g, cs, l) := mk_env_bexps_ccache s es in
  E.


Lemma mk_env_ccache_tt :
  forall es s, interp_lit (mk_env_ccache s es) lit_tt.
Proof.
  move=> es s. rewrite /mk_env_ccache.
  case Hmkes : (mk_env_bexps_ccache s es) => [[[[[m c] E] g] cs] l].  
  exact: (mk_env_bexps_ccache_tt Hmkes).
Qed.


Lemma mk_env_ccache_consistent :
  forall es s te m c g cs l,
    bit_blast_bexps_ccache te es = (m, c, g, cs, l) ->
    AdhereConform.conform_bexps es s te ->
    well_formed_bexps es te ->
    consistent m (mk_env_ccache s es) s.
Proof.
  move=> es s te m c g cs l Hbb Hcf Hwf.
  rewrite /mk_env_ccache.
  case Hmk: (mk_env_bexps_ccache s es) => [[[[[m' c'] E'] g'] cs'] l'].
  rewrite (mk_env_bexps_ccache_is_bit_blast_bexps_ccache Hmk Hcf Hwf) in Hbb.
  case: Hbb => <- _ _ _ _.
  exact: (mk_env_bexps_ccache_consistent Hmk).
Qed.


Lemma mk_env_ccache_sat :
  forall es s te m c g cs l,
    bit_blast_bexps_ccache te es = (m, c, g, cs, l) ->
    AdhereConform.conform_bexps es s te ->
    well_formed_bexps es te ->
    interp_cnf (mk_env_ccache s es) cs.
Proof.
  move=> es s te m c g cs l Hbb Hcf Hwf.
  rewrite /mk_env_ccache.
  case Hmk: (mk_env_bexps_ccache s es) => [[[[[m' c'] E'] g'] cs'] l'].
  rewrite (mk_env_bexps_ccache_is_bit_blast_bexps_ccache Hmk Hcf Hwf) in Hbb.
  case: Hbb => _ _ _ <- _.
  exact: (mk_env_bexps_ccache_sat Hmk).
Qed.


Theorem bit_blast_ccache_sound_general :
  forall (e : QFBV.bexp) (es : seq QFBV.bexp) te m c g cs lr,
    bit_blast_bexps_ccache te (e::es) = (m, c, g, cs, lr) ->
    well_formed_bexps (e::es) te ->
    ~ (sat (add_prelude ([::neg_lit lr]::cs))) ->
    (forall s, AdhereConform.conform_bexps (e::es) s te ->
               QFBV.eval_bexp e s) .
Proof.
  move=> e es te m' c' g' cs' lr' Hbb Hwf Hsat s Hcf.
  move: (unsat_implies_valid Hsat) => {Hsat} Hsat.
  move: (Hsat (mk_env_ccache s (e::es))) => {Hsat} Hsat.
  move: (mk_env_ccache_sat Hbb Hcf Hwf) => Hcs. 
  move: (mk_env_ccache_tt (e::es) s) => Htt.
  have Hprelude: interp_cnf (mk_env_ccache s (e::es)) (add_prelude cs')
    by rewrite add_prelude_expand Hcs Htt.
  rewrite Hprelude /= in Hsat. 
  move: (mk_env_ccache_consistent Hbb Hcf Hwf) => Hcon.
  move: Hbb => /=.
  case Hbbes: (bit_blast_bexps_ccache te es) => [[[[m c] g] cs] lr].
  move: Hwf Hcf => /= /andP [Hwfe Hwfes] /andP [Hcfe Hcfes] Hbbe. 
  move: (bit_blast_bexps_ccache_correct_cache Hbbes Hwfes) => Hcr.
  move: (correct_reset_ct Hcr) => {Hcr} Hcr.
  move: (interp_cache_ct_reset_ct (mk_env_ccache s (e::es)) c) => Hic.
  move: (reset_ct_well_formed c) => Hwfc.
  move: (bit_blast_bexp_ccache_correct Hbbe Hcfe Hcon Hwfe Hwfc Hprelude Hic Hcr).
  rewrite /enc_bit. move=> /eqP <-.
  exact: Hsat.
Qed.

