From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF Cache BBExport
     BitBlastingCacheDef .

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* = mk_env_exp_cache_well_formed and mk_env_bexp_cache_well_formed = *)

Corollary mk_env_exp_cache_well_formed :
  forall (e : QFBV.exp) m ca s E g m' ca' E' g' cs lrs,
    mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
    Cache.well_formed ca -> Cache.well_formed ca'
  with
    mk_env_bexp_cache_well_formed :
      forall e m ca s E g m' ca' E' g' cs lr,
        mk_env_bexp_cache m ca s E g e = (m', ca', E', g', cs, lr) ->
        Cache.well_formed ca -> Cache.well_formed ca'.
Proof.
Admitted.

Corollary bit_blast_exp_cache_well_formed :
  forall (e : QFBV.exp) te m ca g m' ca' g' cs lrs,
    bit_blast_exp_cache te m ca g e = (m', ca', g', cs, lrs) ->
    Cache.well_formed ca -> Cache.well_formed ca'
  with
    bit_blast_bexp_cache_well_formed :
      forall e te m ca g m' ca' g' cs lr,
        bit_blast_bexp_cache te m ca g e = (m', ca', g', cs, lr) ->
        Cache.well_formed ca -> Cache.well_formed ca'.
Proof.
Admitted.
