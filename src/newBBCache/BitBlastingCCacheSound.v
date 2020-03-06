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
     BitBlastingCCacheMkEnv BitBlastingCCacheConsistent BitBlastingCCacheSat.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ===== mk_env_ccache ===== *)


Definition mk_env_ccache (s : SSAStore.t) (e : QFBV.bexp) : env :=
  let '(m, c, E, g, cs, l) := 
      mk_env_bexp_ccache init_vm init_ccache s init_env init_gen e in
  E.

Lemma mk_env_ccache_consistent :
  forall s e te m c g cs l,
    bit_blast_bexp_ccache te init_vm init_ccache init_gen e = (m, c, g, cs, l) ->
    AdhereConform.conform_bexp e s te ->
    QFBV.well_formed_bexp e te ->
    consistent m (mk_env_ccache s e) s.
Proof.
  move=> s e te m c g cs l Hbb Hcf Hwf. rewrite /mk_env_ccache.
  case Henv: (mk_env_bexp_ccache init_vm init_ccache s init_env init_gen e) 
  => [[[[[m' c'] E'] g'] cs'] l'].
  move: (mk_env_bexp_ccache_is_bit_blast_bexp_ccache Hcf Hwf Henv). 
  rewrite Hbb. case=> -> _ _ _ _.
  apply: (mk_env_bexp_ccache_consistent Henv init_newer_than_vm).
  exact: init_consistent.
Qed.

Lemma mk_env_ccache_tt :
  forall s e, interp_lit (mk_env_ccache s e) lit_tt.
Proof.
  move=> s e. rewrite /mk_env_ccache.
  case Henv: (mk_env_bexp_ccache init_vm init_ccache s init_env init_gen e) 
  => [[[[[m c] E] g] cs] l].
  rewrite (env_preserve_lit (mk_env_bexp_ccache_preserve Henv) init_newer_than_tt).
  exact: init_tt.
Qed. 

Lemma mk_env_ccache_sat :
  forall s e te m c g cs l,
    bit_blast_bexp_ccache te init_vm init_ccache init_gen e = (m, c, g, cs, l) ->
    AdhereConform.conform_bexp e s te ->
    QFBV.well_formed_bexp e te ->
    interp_cnf (mk_env_ccache s e) cs.
Proof.
  move=> s e te m c g cs l Hbb Hcf Hwf. 
  move: (mk_env_ccache_tt s e). rewrite /mk_env_ccache.
  case Henv: (mk_env_bexp_ccache init_vm init_ccache s init_env init_gen e) 
  => [[[[[m' c'] E'] g'] cs'] l'].
  move: (mk_env_bexp_ccache_is_bit_blast_bexp_ccache Hcf Hwf Henv).
  rewrite Hbb; case=> _ _ _ -> _ Htt.
  exact: (mk_env_bexp_ccache_sat Henv init_newer_than_vm init_newer_than_tt 
                                 init_ccache_well_formed init_newer_than_cache 
                                 init_interp_cache).
Qed.




Lemma valid_implies_unsat :
  forall premises goal,
    (forall E, ~~ interp_cnf E (add_prelude premises) || interp_lit E goal) ->
    ~ (sat (add_prelude ([::neg_lit goal]::premises))).
Proof.
  move=> premises goal H1 [E H2]. move: (H1 E) => {H1} H1.
  rewrite add_prelude_cons in H2. move/andP: H2 => [H2 H3].
  move/orP: H1. case => H1.
  - move/negP: H1. apply. exact: H3.
  - rewrite add_prelude_expand in H2. move/andP: H2 => [_ H2].
    rewrite /= interp_lit_neg_lit in H2. move/negP: H2; apply.
    rewrite H1 // .
Qed.

Lemma unsat_implies_valid :
  forall premises goal,
    ~ (sat (add_prelude ([::neg_lit goal]::premises))) ->
    (forall E, ~~ interp_cnf E (add_prelude premises) || interp_lit E goal).
Proof.
  move=> premises goal H E. case Hgoal: (interp_lit E goal).
  - by rewrite orbT.
  - rewrite orbF. apply/negP => H2. apply: H. exists E.
    rewrite add_prelude_cons H2 /= .
    rewrite add_prelude_expand /=  interp_lit_neg_lit.
    rewrite Hgoal /= . move : (add_prelude_tt H2) => Htt .
    rewrite /interp_lit /lit_tt in Htt .
    rewrite Htt // .
Qed.


Theorem bit_blast_ccache_sound :
  forall (e : QFBV.bexp) te m c g cs lr,
    bit_blast_bexp_ccache te init_vm init_ccache init_gen e = (m, c, g, cs, lr) ->
    QFBV.well_formed_bexp e te ->
    ~ (sat (add_prelude ([::neg_lit lr]::cs))) ->
    (forall s, AdhereConform.conform_bexp e s te ->
               QFBV.eval_bexp e s) .
Proof.
  move=> e te m c g cs lr Hblast Hwf Hsat s Hcf.
  move: (unsat_implies_valid Hsat) => {Hsat} Hsat.
  move: (Hsat (mk_env_ccache s e)) => {Hsat} Hsat.
  move: (mk_env_ccache_sat Hblast Hcf Hwf) => Hcs. 
  move: (mk_env_ccache_tt s e) => Htt.
  have Hprelude: interp_cnf (mk_env_ccache s e) (add_prelude cs)
    by rewrite add_prelude_expand Hcs Htt.
  Check bit_blast_bexp_ccache_correct.
  move: (bit_blast_bexp_ccache_correct 
           Hblast Hcf (mk_env_ccache_consistent Hblast Hcf Hwf)
           Hwf init_ccache_well_formed Hprelude 
           (init_interp_cache_ct (mk_env_ccache s e))
           (init_correct init_vm)).
  rewrite /enc_bit. move=> /eqP <-.
  rewrite Hprelude /= in Hsat. exact: Hsat.
Qed.
