From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport AdhereConform.
From BBCache Require Import CompCache BitBlastingCCacheCorrect
     BitBlastingCCacheDefGeneral BitBlastingCCache.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ===== generalized mk_env ===== *)

Definition mk_env (s : SSAStore.t) (es : seq QFBV.bexp) : env :=
  let '(m, c, E, g, cs, l) := mk_env_bexps_ccache s es in
  E.

Lemma mk_env_consistent :
  forall es s te m c g cs l,
    bit_blast_bexps_ccache te es = (m, c, g, cs, l) ->
    AdhereConform.conform_bexps es s te ->
    well_formed_bexps es te ->
    consistent m (mk_env s es) s.
Proof.
  move=> es s te m c g cs l Hbb Hcf Hwf.
  rewrite /mk_env.
  case Hmk: (mk_env_bexps_ccache s es) => [[[[[m' c'] E'] g'] cs'] l'].
  rewrite (mk_env_bexps_ccache_is_bit_blast_bexps_ccache Hmk Hcf Hwf) in Hbb.
  case: Hbb => <- _ _ _ _.
  exact: (mk_env_bexps_ccache_consistent Hmk).
Qed.

Lemma mk_env_tt :
  forall es s, interp_lit (mk_env s es) lit_tt.
Proof.
  move=> es s. rewrite /mk_env.
  case Hmkes : (mk_env_bexps_ccache s es) => [[[[[m c] E] g] cs] l].  
  exact: (mk_env_bexps_ccache_tt Hmkes).
Qed.

Lemma mk_env_sat :
  forall es s te m c g cs l,
    bit_blast_bexps_ccache te es = (m, c, g, cs, l) ->
    AdhereConform.conform_bexps es s te ->
    well_formed_bexps es te ->
    interp_cnf (mk_env s es) cs.
Proof.
  move=> es s te m c g cs l Hbb Hcf Hwf.
  rewrite /mk_env.
  case Hmk: (mk_env_bexps_ccache s es) => [[[[[m' c'] E'] g'] cs'] l'].
  rewrite (mk_env_bexps_ccache_is_bit_blast_bexps_ccache Hmk Hcf Hwf) in Hbb.
  case: Hbb => _ _ _ <- _.
  exact: (mk_env_bexps_ccache_sat Hmk).
Qed.


(* ===== mk_state ===== *)
(* Function mk_state is the same as the one of basic case in BitBlastingCCache.v *)

Lemma mk_state_conform_bexps :
  forall es te E m',
    bound_bexps es m' ->
    AdhereConform.adhere m' te ->
    AdhereConform.conform_bexps es (mk_state E m') te .
Proof .
  elim.
  - move=> te E m' /=. done.
  - move=> e es IHes te E m' /= /andP [Hbde Hbdes] Had.
    move: (IHes te E m' Hbdes Had) => Hcfes.
    move: (mk_state_conform_bexp E Hbde Had) => Hcfe.
    by rewrite Hcfe Hcfes. 
Qed.


(* ===== Soundness and completeness ===== *)

Theorem bit_blast_ccache_sound_general :
  forall (e : QFBV.bexp) (es : seq QFBV.bexp) te m c g cs lr,
    bit_blast_bexps_ccache te (e::es) = (m, c, g, cs, lr) ->
    well_formed_bexps (e::es) te ->
    ~ (sat (add_prelude ([::neg_lit lr]::cs))) 
    ->
    (forall s, AdhereConform.conform_bexps (e::es) s te ->
               QFBV.eval_bexp e s) .
Proof.
  move=> e es te m' c' g' cs' lr' Hbb Hwf Hsat s Hcf.
  move: (unsat_implies_valid Hsat) => {Hsat} Hsat.
  move: (Hsat (mk_env s (e::es))) => {Hsat} Hsat.
  move: (mk_env_sat Hbb Hcf Hwf) => Hcs. 
  move: (mk_env_tt (e::es) s) => Htt.
  have Hprelude: interp_cnf (mk_env s (e::es)) (add_prelude cs')
    by rewrite add_prelude_expand Hcs Htt.
  rewrite Hprelude /= in Hsat. 
  move: (mk_env_consistent Hbb Hcf Hwf) => Hcon.
  move: Hbb => /=.
  case Hbbes: (bit_blast_bexps_ccache te es) => [[[[m c] g] cs] lr].
  move: Hwf Hcf => /= /andP [Hwfe Hwfes] /andP [Hcfe Hcfes] Hbbe. 
  move: (bit_blast_bexps_ccache_correct_cache Hbbes Hwfes) => Hcr.
  move: (correct_reset_ct Hcr) => {Hcr} Hcr.
  move: (interp_cache_ct_reset_ct (mk_env s (e::es)) c) => Hic.
  move: (well_formed_reset_ct c) => Hwfc.
  move: (bit_blast_bexp_ccache_correct Hbbe Hcfe Hcon Hwfe Hwfc Hprelude Hic Hcr).
  rewrite /enc_bit. move=> /eqP <-.
  exact: Hsat.
Qed.


Theorem bit_blast_ccache_complete_general :
  forall (e : QFBV.bexp) (es: seq QFBV.bexp) te m c g cs lr,
    bit_blast_bexps_ccache te (e::es) = (m, c, g, cs, lr) ->
    well_formed_bexps (e::es) te ->
    (forall s, AdhereConform.conform_bexps (e::es) s te ->
               QFBV.eval_bexp e s)
    ->
    ~ (sat (add_prelude ([::neg_lit lr]::cs))).
Proof.
  move=> e es te m' c' g' cs' lr' Hbb Hwf He.
  move=> [E Hcs].
  rewrite add_prelude_cons in Hcs. move/andP: Hcs => [Hlr Hcs].
  rewrite add_prelude_expand in Hlr. move/andP: Hlr => [Htt Hlr].
  rewrite /= interp_lit_neg_lit in Hlr.
  move : (bit_blast_bexps_ccache_adhere Hbb) => Hadm' .
  move : (bit_blast_bexps_ccache_bound Hbb) => Hbound .
  move : (mk_state_conform_bexps E Hbound Hadm') => Hcf .
  move : (He (mk_state E m') Hcf) => {He} He .
  move: Hbb => /=.
  case Hbbes: (bit_blast_bexps_ccache te es) => [[[[m c] g] cs] lr].
  move: Hwf Hcf => /= /andP [Hwfe Hwfes] /andP [Hcfe Hcfes] Hbbe. 
  move: (bit_blast_bexps_ccache_correct_cache Hbbes Hwfes) => Hcr.
  move: (correct_reset_ct Hcr) => {Hcr} Hcr.
  move: (bit_blast_bexp_ccache_correct Hbbe Hcfe (mk_state_consistent E m') 
                                       Hwfe (well_formed_reset_ct c)
                                       Hcs (interp_cache_ct_reset_ct E c) Hcr).
  rewrite /enc_bit => /eqP H. rewrite -H in He.
  rewrite He in Hlr. exact: not_false_is_true.
Qed.
