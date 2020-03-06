From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
From newBBCache Require Import SimpTable SimpCache CompTable CompCache.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition init_vm := SSAVM.empty word.
Definition init_gen := (var_tt + 1)%positive.
Definition init_env : env := fun _ => true.
Definition init_ccache : compcache := 
  {| ht := {| et := ExpMap.empty (cnf * word);
              bt := BexpMap.empty (cnf * literal) |};
     ct := {| et := ExpMap.empty (cnf * word);
              bt := BexpMap.empty (cnf * literal) |} |}.
Definition init_cache : cache := 
  {| SimpCache.ht := {| CompTable.et := ExpMap.empty (cnf * word);
              CompTable.bt := BexpMap.empty (cnf * literal) |};
     SimpCache.ct := {| SimpTable.et := ExpMap.empty word;
              SimpTable.bt := BexpMap.empty literal |} |}.

Lemma init_newer_than_vm :
  newer_than_vm init_gen init_vm.
Proof.
  done.
Qed.

Lemma init_newer_than_tt :
  newer_than_lit init_gen lit_tt.
Proof.
  done.
Qed.

Lemma init_tt :
  interp_lit init_env lit_tt.
Proof.
  done.
Qed.

Lemma init_consistent :
  forall s, consistent init_vm init_env s.
Proof.
  move=> s x. rewrite /consistent1 /init_vm. rewrite SSAVM.Lemmas.empty_o. done.
Qed.

Lemma init_vm_adhere : 
  forall te, AdhereConform.adhere init_vm te .
Proof.
  done.
Qed.

Lemma init_ccache_well_formed :
  CompCache.well_formed init_ccache.
Proof.
  done.
Qed.

Lemma init_newer_than_cache :
  newer_than_cache init_gen init_ccache.
Proof.
  done.
Qed.

Lemma init_interp_cache :
  CompCache.interp_cache init_env init_ccache.
Proof.
  done.
Qed.

Lemma init_correct :
  forall m, correct m init_ccache.
Proof.
  done.
Qed.

Lemma init_bound_cache :
  CompCache.bound init_ccache init_vm.
Proof.
  done.
Qed.

Lemma init_interp_cache_ct :
  forall E, interp_cache_ct E init_ccache.
Proof.
  done.
Qed.

Lemma init_compatible : 
  compatible init_cache init_ccache.
Proof. 
  done. 
Qed.
