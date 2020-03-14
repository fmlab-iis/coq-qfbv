From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport AdhereConform.
From BBCache Require Import CompCache BitBlastingCCacheDef BitBlastingInit
     BitBlastingCCachePreserve BitBlastingCCacheAdhere BitBlastingCCacheBound
     BitBlastingCCacheMkEnv BitBlastingCCacheConsistent BitBlastingCCacheNewer
     BitBlastingCCacheSat BitBlastingCCacheCorrect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ====== bit-blasting a sequence of bexps ====== *)
(* = from the end of the sequence = *)

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

Lemma vm_preserve_bound_bexps :
  forall es m m', vm_preserve m m' -> bound_bexps es m -> bound_bexps es m'.
Proof.
  elim.
  - move=> m m' Hpre. done.
  - move=> e es IHes m m' Hpre /= /andP [Hbdem Hbdesm].
    move: (vm_preserve_bound_bexp Hbdem Hpre) => Hbdem'.
    move: (IHes _ _ Hpre Hbdesm) => Hbdesm'.
    by rewrite Hbdem' Hbdesm'.
Qed.


Lemma mk_env_bexps_ccache_is_bit_blast_bexps_ccache :
  forall es s te m c E g cs l,
    mk_env_bexps_ccache s es = (m, c, E, g, cs, l) ->
    AdhereConform.conform_bexps es s te ->
    well_formed_bexps es te ->
    bit_blast_bexps_ccache te es = (m, c, g, cs, l).
Proof.
  elim.
  - move=> s te m c E g cs l /=. case=> <- <- _ <- <- <- _ _. done.
  - move=> e es IHes s te m' c' E' g' cs' l' /=.
    case Hmkes: (mk_env_bexps_ccache s es) => [[[[[m c] E] g] cs] l].
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
  elim.
  - move=> te m c g cs l /=. case=> <- _ _ _ _. exact: init_vm_adhere.
  - move=> e es IHes te m' c' g' cs' l' /=.
    case Hbbes: (bit_blast_bexps_ccache te es) => [[[[m c] g] cs] l].
    move=> Hbbe.
    move: (IHes _ _ _ _ _ _ Hbbes) => Hadm.
    exact: (bit_blast_bexp_ccache_adhere Hadm Hbbe).
Qed.

Lemma bit_blast_bexps_ccache_bound_cache :
  forall es te m c g cs l,
    bit_blast_bexps_ccache te es = (m, c, g, cs, l) ->
    CompCache.bound c m.
Proof.
  elim.
  - move=> te m c g cs l /=. case=> <- <- _ _ _. done.
  - move=> e es IHes te m' c' g' cs' l' /=.
    case Hbbes: (bit_blast_bexps_ccache te es) => [[[[m c] g] cs] l].
    move=> Hbbe.
    move: (IHes _ _ _ _ _ _ Hbbes).
    rewrite bound_reset_ct => Hbdc.
    move: (well_formed_reset_ct c) => Hwfc.
    move: (bit_blast_bexp_ccache_bound_cache Hbbe Hwfc Hbdc)=> [_ H].
    exact: H.
Qed.

Lemma bit_blast_bexps_ccache_bound :
  forall es te m c g cs l,
    bit_blast_bexps_ccache te es = (m, c, g, cs, l) ->
    bound_bexps es m.
Proof.
  elim.
  - move=> te m c g cs l /=. done.
  - move=> e es IHes te m' c' g' cs' l' /=.
    case Hbbes: (bit_blast_bexps_ccache te es) => [[[[m c] g] cs] l].
    move=> Hbbe.
    move: (IHes _ _ _ _ _ _ Hbbes) => Hbdes.
    move: (bit_blast_bexp_ccache_preserve Hbbe) => Hpre.
    move: (vm_preserve_bound_bexps Hpre Hbdes) => {Hbdes} Hbdes.
    move: (bit_blast_bexps_ccache_bound_cache Hbbes). 
    rewrite bound_reset_ct => Hbdc.
    move: (well_formed_reset_ct c) => Hwfc.
    move: (bit_blast_bexp_ccache_bound Hbbe Hwfc Hbdc) => Hbde.
    by rewrite Hbde Hbdes.
Qed.

Lemma bit_blast_bexps_ccache_correct_cache :
  forall es te m c g cs l,
    bit_blast_bexps_ccache te es = (m, c, g, cs, l) ->
    well_formed_bexps es te ->
    CompCache.correct m c.
Proof.
  elim.
  - move=> te m c g cs l /=. case=> _ <- _ _ _ _. exact: init_correct.
  - move=> e es IHes te m' c' g' cs' l' /=.
    case Hbbes: (bit_blast_bexps_ccache te es) => [[[[m c] g] cs] l].
    move=> Hbbe /andP [Hwfe Hwfes].
    move: (IHes _ _ _ _ _ _ Hbbes Hwfes) => Hcrc.
    move: (correct_reset_ct Hcrc) => {Hcrc} Hcrc.
    move: (well_formed_reset_ct c) => Hwfc.
    exact: (bit_blast_bexp_ccache_correct_cache Hbbe Hwfe Hwfc).
Qed.

Lemma mk_env_bexps_ccache_newer_than_tt :
  forall es s m c E g cs l, 
    mk_env_bexps_ccache s es = (m, c, E, g, cs, l) ->
    newer_than_lit g lit_tt.
Proof.
  elim.
  - move=> s m c E g cs l /=. case=> _ _ _ <- _ _. exact: init_newer_than_tt.
  - move=> e es IHes s m' c' E' g' cs' l' /=.
    case Hmkes : (mk_env_bexps_ccache s es) => [[[[[m c] E] g] cs] l].
    move=> Hmke.
    move: (IHes _ _ _ _ _ _ _ Hmkes) => Hgtt.
    move: (mk_env_bexp_ccache_newer_gen Hmke) => Hgg'.
    exact: (newer_than_lit_le_newer Hgtt Hgg').
Qed.

Lemma mk_env_bexps_ccache_newer_than_vm :
  forall es s m c E g cs l, 
    mk_env_bexps_ccache s es = (m, c, E, g, cs, l) ->
    newer_than_vm g m.
Proof.
  elim.
  - move=> s m c E g cs l /=. case=> <- _ _ <- _ _. exact: init_newer_than_vm.
  - move=> e es IHes s m' c' E' g' cs' l' /=.
    case Hmkes : (mk_env_bexps_ccache s es) => [[[[[m c] E] g] cs] l].
    move=> Hmke.
    move: (IHes _ _ _ _ _ _ _ Hmkes) => Hgm.
    exact: (mk_env_bexp_ccache_newer_vm Hmke Hgm).
Qed.

Lemma mk_env_bexps_ccache_tt :
  forall es s m c E g cs l, 
    mk_env_bexps_ccache s es = (m, c, E, g, cs, l) ->
    interp_lit E lit_tt.
Proof.
  elim.
  - move=> s m c E g cs l /=. case=> _ _ <- _ _ _. exact: init_tt.
  - move=> e es IHes s m' c' E' g' cs' l'.
    rewrite /mk_env_bexps_ccache -/mk_env_bexps_ccache.
    case Hmkes : (mk_env_bexps_ccache s es) => [[[[[m c] E] g] cs] l].
    move=> Hmke.
    move: (mk_env_bexps_ccache_newer_than_tt Hmkes) => Hgtt.
    rewrite (env_preserve_lit (mk_env_bexp_ccache_preserve Hmke) Hgtt).
    exact: (IHes _ _ _ _ _ _ _ Hmkes).
Qed.

Lemma mk_env_bexps_ccache_consistent :
  forall es s m c E g cs l,
    mk_env_bexps_ccache s es = (m, c, E, g, cs, l) ->
    consistent m E s.
Proof.
  elim.
  - move=> s m c E g cs l /=. case=> <- _ <- _ _ _. exact: init_consistent. 
  - move=> e es IHes s m' c' E' g' cs' l' /=. 
    case Hmkes : (mk_env_bexps_ccache s es) => [[[[[m c] E] g] cs] l].
    move=> Hmke.
    move: (IHes _ _ _ _ _ _ _ Hmkes) => HcmEs.
    move: (mk_env_bexps_ccache_newer_than_vm Hmkes) => Hgm.
    exact: (mk_env_bexp_ccache_consistent Hmke Hgm HcmEs). 
Qed.

Lemma mk_env_bexps_ccache_newer_than_cache :
  forall es s m c E g cs l,
    mk_env_bexps_ccache s es = (m, c, E, g, cs, l) ->
    newer_than_cache g c.
Proof.
  elim.
  - move=> s m c E g cs l /=. case=> _ <- _ <- _ _. exact: init_newer_than_cache. 
  - move=> e es IHes s m' c' E' g' cs' l' /=. 
    case Hmkes : (mk_env_bexps_ccache s es) => [[[[[m c] E] g] cs] l].
    move=> Hmke.
    move: (IHes _ _ _ _ _ _ _ Hmkes).
    rewrite newer_than_cache_reset_ct => Hgc.
    move: (mk_env_bexps_ccache_newer_than_vm Hmkes) => Hgm.
    move: (mk_env_bexps_ccache_newer_than_tt Hmkes) => Hgtt.
    exact: (mk_env_bexp_ccache_newer_cache Hmke Hgm Hgtt). 
Qed.

Lemma mk_env_bexps_ccache_interp_cache :
  forall es s m c E g cs l,
    mk_env_bexps_ccache s es = (m, c, E, g, cs, l) ->
    CompCache.interp_cache E c.
Proof.
  elim.
  - move=> s m c E g cs l /=. case=> _ <- <- _ _ _. exact: init_interp_cache. 
  - move=> e es IHes s m' c' E' g' cs' l' /=. 
    case Hmkes : (mk_env_bexps_ccache s es) => [[[[[m c] E] g] cs] l].
    move=> Hmke.
    move: (IHes _ _ _ _ _ _ _ Hmkes).
    rewrite interp_cache_reset_ct => HiEc.
    move: (mk_env_bexps_ccache_newer_than_vm Hmkes) => Hgm.
    move: (mk_env_bexps_ccache_newer_than_tt Hmkes) => Hgtt.
    move: (well_formed_reset_ct c) => Hwfc.
    move: (mk_env_bexps_ccache_newer_than_cache Hmkes) => Hgc.
    move: (mk_env_bexp_ccache_interp_cache Hmke Hgm Hgtt Hwfc Hgc HiEc) => [_ H].
    exact: H.
Qed.

Lemma mk_env_bexps_ccache_sat :
  forall es s m c E g cs l,
    mk_env_bexps_ccache s es = (m, c, E, g, cs, l) ->
    interp_cnf E cs.
Proof.
  case.
  - move=> s m c E g cs l /=. case=> _ _ <- _ <- _. done.
  - move=> e es s m' c' E' g' cs' l' /=. 
    case Hmkes : (mk_env_bexps_ccache s es) => [[[[[m c] E] g] cs] l].
    move=> Hmke.
    move: (mk_env_bexps_ccache_newer_than_vm Hmkes) => Hgm.
    move: (mk_env_bexps_ccache_newer_than_tt Hmkes) => Hgtt.
    move: (well_formed_reset_ct c) => Hwfc.
    move: (mk_env_bexps_ccache_newer_than_cache Hmkes).
    rewrite newer_than_cache_reset_ct => Hgc.
    move: (mk_env_bexps_ccache_interp_cache Hmkes).
    rewrite interp_cache_reset_ct => HiEc.
    exact: (mk_env_bexp_ccache_sat Hmke Hgm Hgtt Hwfc Hgc HiEc).
Qed.
