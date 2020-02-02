From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF Cache BBExport
     BitBlastingCacheDef BitBlastingCacheNewer .

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* bit_blast_exp_preserve, bit_blast_bexp_preserve, mk_env_exp_preserve_vm,
   mk_env_bexp_preserve_vm *)

Corollary bit_blast_exp_cache_preserve :
  forall (e : QFBV.exp) te m ca g m' ca' g' cs lrs,
    bit_blast_exp_cache te m ca g e = (m', ca', g', cs, lrs) ->
    vm_preserve m m'
  with
    bit_blast_bexp_cache_preserve :
      forall (e : QFBV.bexp) te m ca g m' ca' g' cs lrs,
        bit_blast_bexp_cache te m ca g e = (m', ca', g', cs, lrs) ->
        vm_preserve m m'.
Proof.
Admitted.


Corollary mk_env_exp_cache_preserve :
  forall (e : QFBV.exp) m ca s E g m' ca' E' g' cs lrs,
    mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
    env_preserve E E' g
  with
    mk_env_bexp_cache_preserve :
      forall e m ca s E g m' ca' E' g' cs lr,
        mk_env_bexp_cache m ca s E g e = (m', ca', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
Admitted.
