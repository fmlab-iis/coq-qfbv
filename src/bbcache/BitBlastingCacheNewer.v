From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
From BBCache Require Import Cache BitBlastingCacheDef.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* = mk_env_exp_cache_newer_gen and mk_env_bexp_cache_newer_gen = *)

Corollary mk_env_exp_cache_newer_gen :
  forall (e : QFBV.exp) m ca s E g m' ca' E' g' cs lrs,
    mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
    (g <=? g')%positive
  with
    mk_env_bexp_cache_newer_gen :
      forall e m ca s E g m' ca' E' g' cs lr,
        mk_env_bexp_cache m ca s E g e = (m', ca', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
Admitted.


Corollary mk_env_exp_cache_newer_vm :
  forall (e : QFBV.exp) m ca s E g m' ca' E' g' cs lrs,
    mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'
  with
    mk_env_bexp_cache_newer_vm :
      forall e m ca s E g m' ca' E' g' cs lr,
        mk_env_bexp_cache m ca s E g e = (m', ca', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.





Corollary mk_env_exp_cache_newer_res :
  forall (e : QFBV.exp) m ca s E g m' ca' E' g' cs lrs,
    mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> 
    Cache.well_formed ca -> newer_than_cache g ca ->
    newer_than_lits g' lrs
  with
    mk_env_bexp_cache_newer_res :
      forall e m ca s E g m' ca' E' g' cs lr,
        mk_env_bexp_cache m ca s E g e = (m', ca', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        Cache.well_formed ca -> newer_than_cache g ca ->
        newer_than_lit g' lr.
Proof.
Admitted.




Corollary mk_env_exp_cache_newer_cnf :
  forall (e : QFBV.exp) m ca s E g m' ca' E' g' cs lrs,
    mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    (* QFBV.well_formed_exp e te -> *)
    Cache.well_formed ca -> newer_than_cache g ca ->
    newer_than_cnf g' cs
  with
    mk_env_bexp_cache_newer_cnf :
      forall e m ca s E g m' ca' E' g' cs lr,
        mk_env_bexp_cache m ca s E g e = (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_bexp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca ->
        newer_than_cnf g' cs.
Proof.
Admitted.


Corollary mk_env_exp_cache_newer_cache :
  forall (e : QFBV.exp) m ca s E g m' ca' E' g' cs lrs,
    mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    (* QFBV.well_formed_exp e te -> *)
    Cache.well_formed ca -> newer_than_cache g ca ->
    newer_than_cache g' ca'
  with
    mk_env_bexp_cache_newer_cache :
      forall e m ca s E g m' ca' E' g' cs lr,
        mk_env_bexp_cache m ca s E g e = (m', ca', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        (* QFBV.well_formed_bexp e te -> *)
        Cache.well_formed ca -> newer_than_cache g ca ->
        newer_than_cache g' ca'.
Proof.
Admitted.
