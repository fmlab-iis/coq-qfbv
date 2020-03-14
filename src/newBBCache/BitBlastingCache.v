From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
From newBBCache Require Import Cache BitBlastingInit BitBlastingCCacheDef 
     BitBlastingCCache BitBlastingCCacheDefGeneral BitBlastingCCacheGeneral
     BitBlastingCacheDef .

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ==== basic case ==== *)
(* = bit-blasting only one bexp = *)

Theorem bit_blast_cache_sound :
  forall (e : QFBV.bexp) te m c g cs lr,
    bit_blast_bexp_cache te init_vm init_cache init_gen e = (m, c, g, cs, lr) ->
    QFBV.well_formed_bexp e te ->
    ~ (sat (add_prelude ([::neg_lit lr]::cs))) 
    ->
    (forall s, AdhereConform.conform_bexp e s te ->
               QFBV.eval_bexp e s) .
Proof.
  move=> e te m c g cs lr Hcache. 
  move: (bit_blast_bexp_cache_is_bit_blast_bexp_ccache init_compatible Hcache)
        => [cc [Hccache _]].
  exact: (bit_blast_ccache_sound Hccache).
Qed.


Theorem bit_blast_cache_complete :
  forall (e : QFBV.bexp) te m c g cs lr,
    bit_blast_bexp_cache te init_vm init_cache init_gen e = (m, c, g, cs, lr) ->
    QFBV.well_formed_bexp e te ->
    (forall s, AdhereConform.conform_bexp e s te ->
               QFBV.eval_bexp e s)
    ->
    ~ (sat (add_prelude ([::neg_lit lr]::cs))).
Proof.
  move=> e te m c g cs lr Hcache. 
  move: (bit_blast_bexp_cache_is_bit_blast_bexp_ccache init_compatible Hcache)
        => [cc [Hccache _]].
  exact: (bit_blast_ccache_complete Hccache).
Qed.


(* ==== general case ==== *)
(* = bit-blasting multiple bexps = *)

Fixpoint bit_blast_bexps_cache te (es : seq QFBV.bexp) :=
  match es with 
  | [::] => (init_vm, init_cache, init_gen, add_prelude [::], lit_tt)
  | e :: es' => 
    let '(m, c, g, cs, lr) := bit_blast_bexps_cache te es' in
    bit_blast_bexp_cache te m (Cache.reset_ct c) g e
  end.

Lemma bit_blast_bexps_cache_is_bit_blast_bexps_ccache :
  forall es te m c g cs l,
    bit_blast_bexps_cache te es = (m, c, g, cs, l)
    -> exists cc, bit_blast_bexps_ccache te es = (m, cc, g, cs, l) 
                  /\ Cache.compatible c cc.
Proof.
  elim.
  - move=> te m c g cs l /=. case=> <- <- <- <- <-. exists init_ccache; done.
  - move=> e tl IHtl te m' c' g' cs' l' /=. 
    case Hbbtl : (bit_blast_bexps_cache te tl) => [[[[m c] g] cs] l].
    move=> Hbbe.
    move: (IHtl _ _ _ _ _ _ Hbbtl) => [cc [-> Hcomptl]].
    move: (Cache.compatible_reset_ct Hcomptl) => {Hcomptl} Hcomptl.
    exact: (bit_blast_bexp_cache_is_bit_blast_bexp_ccache Hcomptl Hbbe).
Qed.


Theorem bit_blast_cache_sound_general :
  forall (e : QFBV.bexp) (es : seq QFBV.bexp) te m c g cs lr,
    bit_blast_bexps_cache te (e::es) = (m, c, g, cs, lr) ->
    well_formed_bexps (e::es) te ->
    ~ (sat (add_prelude ([::neg_lit lr]::cs))) 
    ->
    (forall s, AdhereConform.conform_bexps (e::es) s te ->
               QFBV.eval_bexp e s) .
Proof.
  move=> e es te m c g cs lr Hcache. 
  move: (bit_blast_bexps_cache_is_bit_blast_bexps_ccache Hcache)
        => [cc [Hccache _]].
  exact: (bit_blast_ccache_sound_general Hccache).
Qed.


Theorem bit_blast_cache_complete_general :
  forall (e : QFBV.bexp) (es: seq QFBV.bexp) te m c g cs lr,
    bit_blast_bexps_cache te (e::es) = (m, c, g, cs, lr) ->
    well_formed_bexps (e::es) te ->
    (forall s, AdhereConform.conform_bexps (e::es) s te ->
               QFBV.eval_bexp e s)
    ->
    ~ (sat (add_prelude ([::neg_lit lr]::cs))).
Proof.
  move=> e es te m c g cs lr Hcache. 
  move: (bit_blast_bexps_cache_is_bit_blast_bexps_ccache Hcache)
        => [cc [Hccache _]].
  exact: (bit_blast_ccache_complete_general Hccache).
Qed.
