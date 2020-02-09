From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport 
     AdhereConform BitBlasting.
From BBCache Require Import Cache BitBlastingCacheDef BitBlastingCacheNewer 
     BitBlastingCachePreserve BitBlastingCacheCorrect BitBlastingCacheMkEnv 
     BitBlastingCacheConsistent BitBlastingCacheSat BitBlastingCacheAdhere
     BitBlastingCacheBound.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== mk_env_cache ===== *)

Lemma init_vm_adhere : 
  forall te, AdhereConform.adhere init_vm te .
Proof.
  done.
Qed.

Definition init_cache : cache := 
  {| het := ExpMap.empty (cnf * word);
     hbt := BexpMap.empty (cnf * literal);
     cet := ExpMap.empty word;
     cbt := BexpMap.empty literal |}.

Lemma init_well_formed_cache :
  Cache.well_formed init_cache.
Proof.
  done.
Qed.

Lemma init_newer_than_cache :
  newer_than_cache init_gen init_cache.
Proof.
  done.
Qed.

Lemma init_regular :
  Cache.regular init_env init_cache.
Proof.
  done.
Qed.

Lemma init_correct :
  forall E s, correct E s init_cache.
Proof.
  done.
Qed.

Lemma init_bound_cache :
  Cache.bound init_cache init_vm.
Proof.
  done.
Qed.

Definition mk_env_cache (s : SSAStore.t) (e : QFBV.bexp) : env :=
  let '(m', ca', E', g, cs, lr) := 
      mk_env_bexp_cache init_vm init_cache s init_env init_gen e in
  E'.

Lemma mk_env_cache_consistent :
  forall s e te m ca g cs lr,
    bit_blast_bexp_cache te init_vm init_cache init_gen e = (m, ca, g, cs, lr) ->
    AdhereConform.conform_bexp e s te ->
    QFBV.well_formed_bexp e te ->
    consistent m (mk_env_cache s e) s.
Proof.
  move=> s e te m ca g cs lr Hbb Hcf Hwf. rewrite /mk_env_cache.
  case Henv: (mk_env_bexp_cache init_vm init_cache s init_env init_gen e) 
  => [[[[[m' ca'] E'] g'] cs'] lr'].
  move: (mk_env_bexp_cache_is_bit_blast_bexp_cache Hcf Hwf Henv). 
  rewrite Hbb. case=> Hm Hca Hg Hcs Hlr.
  rewrite Hm. apply: (mk_env_bexp_cache_consistent Henv init_newer_than_vm).
  exact: init_consistent.
Qed.

Lemma mk_env_cache_tt :
  forall s e, interp_lit (mk_env_cache s e) lit_tt.
Proof.
  move=> s e. rewrite /mk_env_cache.
  case Henv: (mk_env_bexp_cache init_vm init_cache s init_env init_gen e) 
  => [[[[[m' ca'] E'] g'] cs'] lr'].
  rewrite (env_preserve_lit (mk_env_bexp_cache_preserve Henv) init_newer_than_tt).
  exact: init_tt.
Qed. 

Lemma mk_env_cache_sat :
  forall s e te m ca g cs lr,
    bit_blast_bexp_cache te init_vm init_cache init_gen e = (m, ca, g, cs, lr) ->
    AdhereConform.conform_bexp e s te ->
    QFBV.well_formed_bexp e te ->
    interp_cnf (mk_env_cache s e) cs.
Proof.
  move=> s e te m ca g cs lr Hbb Hcf Hwf. 
  move: (mk_env_cache_tt s e). rewrite /mk_env_cache.
  case Henv: (mk_env_bexp_cache init_vm init_cache s init_env init_gen e) 
  => [[[[[m' ca'] E'] g'] cs'] lr'].
  move: (mk_env_bexp_cache_is_bit_blast_bexp_cache Hcf Hwf Henv).
  rewrite Hbb; case=> _ _ _ -> _ Htt.
  exact: (mk_env_bexp_cache_sat Henv init_newer_than_vm init_newer_than_tt 
                                init_well_formed_cache init_newer_than_cache init_regular).
Qed.


(* ===== mk_state ===== *)





(* ===== Soundness and completeness ===== *)

Theorem bit_blast_cache_sound :
  forall (e : QFBV.bexp) te m' ca' g' cs lr,
    bit_blast_bexp_cache te init_vm init_cache init_gen e = (m', ca', g', cs, lr) ->
    QFBV.well_formed_bexp e te ->
    ~ (sat (add_prelude ([::neg_lit lr]::cs))) ->
    (forall s,
        AdhereConform.conform_bexp e s te ->
        QFBV.eval_bexp e s) .
Proof.
  move=> e te m' ca' g' cs lr Hblast Hwf Hsat s Hcf.
  move: (unsat_implies_valid Hsat) => {Hsat} Hsat.
  move: (Hsat (mk_env_cache s e)) => {Hsat} Hsat.
Check mk_env_cache_sat.
  move: (mk_env_cache_sat Hblast Hcf Hwf) => Hcs. move: (mk_env_cache_tt s e) => Htt.
  have Hprelude: interp_cnf (mk_env_cache s e) (add_prelude cs)
    by rewrite add_prelude_expand Hcs Htt.
  Check bit_blast_bexp_cache_correct.
  move: (bit_blast_bexp_cache_correct 
           Hblast Hcf 
           (mk_env_cache_consistent Hblast Hcf Hwf)
           Hprelude Hwf
           init_well_formed_cache 
           (init_correct (mk_env_cache s e) s)).
  rewrite /enc_bit. move=> /eqP <-.
  rewrite Hprelude /= in Hsat. exact: Hsat.
Qed.

Theorem bit_blast_cache_complete :
  forall (e : QFBV.bexp) te m' ca' g' cs lr,
    bit_blast_bexp_cache te init_vm init_cache init_gen e = (m', ca', g', cs, lr) ->
    QFBV.well_formed_bexp e te ->
    (forall s, AdhereConform.conform_bexp e s te ->
               QFBV.eval_bexp e s)
    ->
    ~ (sat (add_prelude ([::neg_lit lr]::cs))).
Proof.
  move=> e te m' ca' g' cs lr Hblast Hwf He.
  move=> [E Hcs].
  rewrite add_prelude_cons in Hcs. move/andP: Hcs => [Hlr Hcs].
  rewrite add_prelude_expand in Hlr. move/andP: Hlr => [Htt Hlr].
  rewrite /= interp_lit_neg_lit in Hlr.
  move : (bit_blast_bexp_cache_adhere (init_vm_adhere te) Hblast) => Hadm' .
  move : (bit_blast_bexp_cache_bound Hblast init_well_formed_cache init_bound_cache)
  => Hbound .
  move : (mk_state_conform_bexp E Hbound Hadm') => Hcf .
  move : (He (mk_state E m') Hcf) => {He} He .
  move: (bit_blast_bexp_cache_correct Hblast Hcf (mk_state_consistent E m') 
                                      Hcs Hwf init_well_formed_cache
                                      (init_correct E (mk_state E m'))).
  rewrite /enc_bit => /eqP H. rewrite -H in He.
  rewrite He in Hlr. exact: not_false_is_true.
Qed.

