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
     BitBlastingCCacheComplete BitBlastingCCacheMkEnv BitBlastingCCacheConsistent
     BitBlastingCCacheSat.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ================================================ *)
(* ================================================ *)
(* ======= bit-blasting with multiple bexps ======= *)
(* ================================================ *)
(* ================================================ *)


(* ====== bit-blasting using a sequence of bexps ====== *)
(* from the end of the sequence *)

Fixpoint bit_blast_bexps_ccache te (es : seq QFBV.bexp) :=
  match es with 
  | [::] => (init_vm, init_ccache, init_gen, add_prelude [::], lit_tt)
  | e :: es' => 
    let '(m, c, g, cs, lr) := bit_blast_bexps_ccache te es' in
    bit_blast_bexp_ccache te m (reset_ct c) g e
  end.

Fixpoint mk_env_bexps_ccache (s : SSAStore.t) (es : seq QFBV.bexp) :=
  match es with 
  | [::] => (init_vm, init_ccache, init_env, init_gen, add_prelude [::], lit_tt)
  | e :: es' => 
    let '(m, c, E, g, cs, l) := mk_env_bexps_ccache s es' in
    mk_env_bexp_ccache m (reset_ct c) s E g e
  end.


Fixpoint well_formed_bexps (bs : seq QFBV.bexp) te : bool :=
  match bs with
  | [::] => true
  | b :: bs' => QFBV.well_formed_bexp b te && well_formed_bexps bs' te
  end.

Fixpoint bound_bexps (bs : seq QFBV.bexp) vm : bool :=
  match bs with
  | [::] => true
  | b :: bs' => bound_bexp b vm && bound_bexps bs' vm
  end.

Lemma mk_env_bexps_ccache_is_bit_blast_bexps_ccache :
  forall es s te m c E g cs l,
    mk_env_bexps_ccache s es = (m, c, E, g, cs, l) ->
    AdhereConform.conform_bexps es s te ->
    well_formed_bexps es te ->
    bit_blast_bexps_ccache te es = (m, c, g, cs, l).
Proof.
  elim.
  - move=> s te m c E g cs l /=. 
    case=> <- <- _ <- <- <- _ _. done.
  - move=> e es IHes s te m c E g cs l /=.
    case Hmkes: (mk_env_bexps_ccache s es) => [[[[[mes ces] Ees] ges] cses] les].
    move=> Hmke /andP [Hcfe Hcfes] /andP [Hwfe Hwfes].
    move: (IHes _ te _ _ _ _ _ _ Hmkes Hcfes Hwfes) => Hbbes.
    rewrite Hbbes.
    exact: (mk_env_bexp_ccache_is_bit_blast_bexp_ccache Hcfe Hwfe Hmke).
Qed.    

Lemma bit_blast_bexps_ccache_adhere :
  forall es te m c g cs l,
    bit_blast_bexps_ccache te es = (m, c, g, cs, l) ->
    AdhereConform.adhere m te .
Proof.
Admitted.


Lemma bit_blast_bexps_ccache_bound :
  forall es te m c g cs l,
    bit_blast_bexps_ccache te es = (m, c, g, cs, l) ->
    bound_bexps es m.
Proof.
Admitted.

Lemma bit_blast_bexps_ccache_correct_cache :
  forall es te m c g cs l,
    bit_blast_bexps_ccache te es = (m, c, g, cs, l) ->
    well_formed_bexps es te ->
    CompCache.correct m c.
Proof.
Admitted.

Lemma mk_env_bexps_ccache_newer_than_tt :
  forall es s m c E g cs l, 
    mk_env_bexps_ccache s es = (m, c, E, g, cs, l) ->
    newer_than_lit g lit_tt.
Proof.
(*   elim. *)
(*   - move=> s m ca E g cs lr /=. case=> _ _ _ <- _ _. done. *)
(*   - move=> e tl IHtl s m' ca' E' g' cs' lr'.  *)
(*     rewrite /mk_env_bexps_cache -/mk_env_bexps_cache. *)
(*     case Hmktl : (mk_env_bexps_cache s tl) => [[[[[m ca] E] g] cs] lr]. *)
(*     move=> Hmke. *)
(*     move: (IHtl _ _ _ _ _ _ _ Hmktl) => Hgtt. *)
(*     move: (mk_env_bexp_cache_newer_gen Hmke) => Hgg'. *)
(*     exact: (newer_than_lit_le_newer Hgtt Hgg'). *)
(* Qed. *)
Admitted.

Lemma mk_env_bexps_ccache_newer_than_vm :
  forall es s m c E g cs l, 
    mk_env_bexps_ccache s es = (m, c, E, g, cs, l) ->
    newer_than_vm g m.
Proof.
(*   elim. *)
(*   - move=> s m ca E g cs lr /=. case=> <- _ _ <- _ _. done. *)
(*   - move=> e tl IHtl s m' ca' E' g' cs' lr'.  *)
(*     rewrite /mk_env_bexps_cache -/mk_env_bexps_cache. *)
(*     case Hmktl : (mk_env_bexps_cache s tl) => [[[[[m ca] E] g] cs] lr]. *)
(*     move=> Hmke. *)
(*     move: (IHtl _ _ _ _ _ _ _ Hmktl) => Hgm. *)
(*     exact: (mk_env_bexp_cache_newer_vm Hmke Hgm). *)
(* Qed. *)
Admitted.

Lemma mk_env_bexps_ccache_tt :
  forall es s m c E g cs l, 
    mk_env_bexps_ccache s es = (m, c, E, g, cs, l) ->
    interp_lit E lit_tt.
Proof.
  elim.
  - move=> s m c E g cs l /=. case=> _ _ <- _ _ _. done.
  - move=> e tl IHtl s m' c' E' g' cs' l'. 
    rewrite /mk_env_bexps_ccache -/mk_env_bexps_ccache.
    case Hmktl : (mk_env_bexps_ccache s tl) => [[[[[m c] E] g] cs] l].
    move=> Hmke.
    move: (mk_env_bexps_ccache_newer_than_tt Hmktl) => Hgtt.
    rewrite (env_preserve_lit (mk_env_bexp_ccache_preserve Hmke) Hgtt).
    exact: (IHtl _ _ _ _ _ _ _ Hmktl).
Qed.

Lemma mk_env_bexps_ccache_consistent :
  forall es s m c E g cs l,
    mk_env_bexps_ccache s es = (m, c, E, g, cs, l) ->
    consistent m E s.
Proof.
  elim.
  - move=> s m c E g cs l /=. case=> <- _ <- _ _ _. done.
  - move=> e tl IHtl s m' c' E' g' cs' l'. 
    rewrite /mk_env_bexps_ccache -/mk_env_bexps_ccache.
    case Hmktl : (mk_env_bexps_ccache s tl) => [[[[[m c] E] g] cs] l].
    move=> Hmke.
    move: (IHtl _ _ _ _ _ _ _ Hmktl) => HcmEs.
    move: (mk_env_bexps_ccache_newer_than_vm Hmktl) => Hgm.
    exact: (mk_env_bexp_ccache_consistent Hmke Hgm HcmEs). 
Qed.

Lemma mk_env_bexps_ccache_newer_than_cache :
  forall es s m c E g cs l,
    mk_env_bexps_ccache s es = (m, c, E, g, cs, l) ->
    newer_than_cache g c.
Proof.
Admitted.

Lemma mk_env_bexps_ccache_interp_cache :
  forall es s m c E g cs l,
    mk_env_bexps_ccache s es = (m, c, E, g, cs, l) ->
    CompCache.interp_cache E c.
Proof.
Admitted.

Lemma mk_env_bexps_ccache_sat :
  forall es s m c E g cs l,
    mk_env_bexps_ccache s es = (m, c, E, g, cs, l) ->
    interp_cnf E cs.
Proof.
  case.
  - move=> s m c E g cs l /=. case=> _ _ <- _ <- _. done.
  - move=> e tl s m' c' E' g' cs' l'. 
    rewrite /mk_env_bexps_ccache -/mk_env_bexps_ccache.
    case Hmktl : (mk_env_bexps_ccache s tl) => [[[[[m c] E] g] cs] l].
    move=> Hmke.
    move: (mk_env_bexps_ccache_newer_than_vm Hmktl) => Hgm.
    move: (mk_env_bexps_ccache_newer_than_tt Hmktl) => Hgtt.
    (* move: (mk_env_bexps_cache_well_formed Hmktl) => Hwfca. *)
    move: (well_formed_reset_ct c) => Hwfrc.
    move: (mk_env_bexps_ccache_newer_than_cache Hmktl).
    rewrite CompCache.newer_than_cache_reset_ct => Hgrc.
    move: (mk_env_bexps_ccache_interp_cache Hmktl).
    rewrite CompCache.interp_cache_reset_ct => HiErc.
    exact: (mk_env_bexp_ccache_sat Hmke Hgm Hgtt Hwfrc Hgrc HiErc).
Qed.


(*
Lemma mk_env_bexps_ccache_correct :
  forall es s m c E g cs l te,
    mk_env_bexps_ccache s es = (m, c, E, g, cs, l) ->
    AdhereConform.conform_bexps es s te ->
    well_formed_bexps es te ->
    CompCache.correct m c.
Proof.
  elim.
  - move=> s m c E g cs l te /=. case=> <- <- _ _ _ _ _ _. done.
  - move=> e tl IHtl s m' c' E' g' cs' l' te Hmk Hcf Hwf. 
    move: (mk_env_bexps_ccache_consistent Hmk) => HconmpEps.
    move: (mk_env_bexps_ccache_sat Hmk) => HiEpcsp.
    move: (mk_env_bexps_ccache_tt Hmk) => Htt.
    have Hpre: interp_cnf E' (add_prelude cs')
      by rewrite add_prelude_expand HiEpcsp Htt.
    move: Hcf Hwf Hmk => /= /andP [Hcfe Hcftl] /andP [Hwfe Hwftl] {Htt HiEpcsp}.
    case Hmktl : (mk_env_bexps_ccache s tl) => [[[[[m c] E] g] cs] l].
    move=> Hmke.
    move: (mk_env_bexp_ccache_is_bit_blast_bexp_ccache Hcfe Hwfe Hmke) => Hbbe.
    move: (IHtl _ _ _ _ _ _ _ _ Hmktl Hcftl Hwftl) => Hcrmc.
    move: (mk_env_bexp_ccache_preserve Hmke) => HpEEpg.
    move: (mk_env_bexps_ccache_newer_than_cache Hmktl) => Hgc.
    move: Hcrmc. 
Check bit_blast_bexps_ccache_correct_cache.

(* todo *)
    rewrite -(env_preserve_correct s HpEEpg Hgca) => {HpEEpg Hgc} HcEpsca.
    move: (bit_blast_bexp_cache_correct_cache Hbbe Hcfe HconmpEps Hpre Hwfe 
                                              (reset_ct_well_formed ca) HcEpsca).
    by move=> [_ H].
Qed.
*)
