From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport 
     AdhereConform BitBlasting.
From BBCache Require Import Cache BitBlastingCacheDef BitBlastingCacheNewer 
     BitBlastingCachePreserve BitBlastingCacheCorrect BitBlastingCacheMkEnv 
     BitBlastingCacheConsistent BitBlastingCacheSat BitBlastingCacheAdhere
     BitBlastingCacheBound BitBlastingCache.

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

Fixpoint bit_blast_bexps_cache te (es : seq QFBV.bexp) :=
  match es with 
  | [::] => (init_vm, init_cache, init_gen, add_prelude [::], lit_tt)
  | e :: es' => 
    let '(m, ca, g, cs, lr) := bit_blast_bexps_cache te es' in
    bit_blast_bexp_cache te m (reset_ct ca) g e
  end.

Fixpoint mk_env_bexps_cache (s : SSAStore.t) (es : seq QFBV.bexp) :=
  match es with 
  | [::] => (init_vm, init_cache, init_env, init_gen, add_prelude [::], lit_tt)
  | e :: es' => 
    let '(m, ca, E, g, cs, lr) := mk_env_bexps_cache s es' in
    mk_env_bexp_cache m (reset_ct ca) s E g e
  end.

Fixpoint well_formed_bexps (bs : seq QFBV.bexp) te : bool :=
  match bs with
  | [::] => true
  | b :: bs' => QFBV.well_formed_bexp b te && well_formed_bexps bs' te
  end.

Lemma mk_env_bexps_cache_newer_than_tt :
  forall es s m ca E g cs lr, 
    mk_env_bexps_cache s es = (m, ca, E, g, cs, lr) ->
    newer_than_lit g lit_tt.
Proof.
  elim.
  - move=> s m ca E g cs lr /=. case=> _ _ _ <- _ _. done.
  - move=> e tl IHtl s m' ca' E' g' cs' lr'. 
    rewrite /mk_env_bexps_cache -/mk_env_bexps_cache.
    case Hmktl : (mk_env_bexps_cache s tl) => [[[[[m ca] E] g] cs] lr].
    move=> Hmke.
    move: (IHtl _ _ _ _ _ _ _ Hmktl) => Hgtt.
    move: (mk_env_bexp_cache_newer_gen Hmke) => Hgg'.
    exact: (newer_than_lit_le_newer Hgtt Hgg').
Qed.

Lemma mk_env_bexps_cache_newer_than_vm :
  forall es s m ca E g cs lr, 
    mk_env_bexps_cache s es = (m, ca, E, g, cs, lr) ->
    newer_than_vm g m.
Proof.
  elim.
  - move=> s m ca E g cs lr /=. case=> <- _ _ <- _ _. done.
  - move=> e tl IHtl s m' ca' E' g' cs' lr'. 
    rewrite /mk_env_bexps_cache -/mk_env_bexps_cache.
    case Hmktl : (mk_env_bexps_cache s tl) => [[[[[m ca] E] g] cs] lr].
    move=> Hmke.
    move: (IHtl _ _ _ _ _ _ _ Hmktl) => Hgm.
    exact: (mk_env_bexp_cache_newer_vm Hmke Hgm).
Qed.

Lemma mk_env_bexps_cache_tt :
  forall es s m ca E g cs lr, 
    mk_env_bexps_cache s es = (m, ca, E, g, cs, lr) ->
    interp_lit E lit_tt.
Proof.
  elim.
  - move=> s m ca E g cs lr /=. case=> _ _ <- _ _ _. done.
  - move=> e tl IHtl s m' ca' E' g' cs' lr'. 
    rewrite /mk_env_bexps_cache -/mk_env_bexps_cache.
    case Hmktl : (mk_env_bexps_cache s tl) => [[[[[m ca] E] g] cs] lr].
    move=> Hmke.
    move: (mk_env_bexps_cache_newer_than_tt Hmktl) => Hgtt.
    rewrite (env_preserve_lit (mk_env_bexp_cache_preserve Hmke) Hgtt).
    exact: (IHtl _ _ _ _ _ _ _ Hmktl).
Qed.


(*
Inductive bit_blast_bexps_cache_res te : 
  vm -> cache -> generator -> cnf -> literal -> seq QFBV.bexp -> Prop :=
(* | bbI : forall e m ca g cs lr,  *)
(*     bit_blast_bexp_cache te init_vm init_cache init_gen e = (m, ca, g, cs, lr)  *)
(*     -> QFBV.well_formed_bexp e te *)
(*     -> bit_blast_bexps_cache_res te m ca g cs lr [::e] *)
| bbI : bit_blast_bexps_cache_res te init_vm init_cache init_gen [::] lit_tt [::]
| bbS : forall m ca g cs lr es e m' ca' g' cs' lr',
    bit_blast_bexps_cache_res te m ca g cs lr es
    -> bit_blast_bexp_cache te m (reset_ct ca) g e = (m', ca', g', cs', lr') 
    -> QFBV.well_formed_bexp e te
    -> bit_blast_bexps_cache_res te m' ca' g' cs' lr' (e::es).
*)


(* Lemma bit_blast_bexps_cache_res_well_formed : *)
(*   forall es te m ca g cs lr, *)
(*     bit_blast_bexps_cache_res te m ca g cs lr es -> *)
(*     well_formed_bexps es te. *)
(* Proof. *)
(*   move=> es te m ca g cs lr Hbbes. *)
(*   induction Hbbes as [| m ca g cs lr es e m' ca' g' cs' lr' Hbbes IH Hbbe Hwfe].  *)
(*   - done. *)
(*   - by rewrite /= Hwfe IH. *)
(* Qed. *)

Lemma mk_env_bexps_cache_is_bit_blast_bexps_cache :
  forall es s te m ca E g cs lr,
    mk_env_bexps_cache s es = (m, ca, E, g, cs, lr) ->
    AdhereConform.conform_bexps es s te ->
    well_formed_bexps es te ->
    bit_blast_bexps_cache te es = (m, ca, g, cs, lr).
Proof.
  elim.
  - move=> s te m ca E g cs lr /=. 
    case=> <- <- _ <- <- <- _ _. done.
  - move=> e es IHes s te m ca E g cs lr /=.
    case Hmkes: (mk_env_bexps_cache s es) => [[[[[mes caes] Ees] ges] cses] lres].
    move=> Hmke /andP [Hcfe Hcfes] /andP [Hwfe Hwfes].
    move: (IHes _ te _ _ _ _ _ _ Hmkes Hcfes Hwfes) => Hbbes.
    rewrite Hbbes.
    exact: (mk_env_bexp_cache_is_bit_blast_bexp_cache Hcfe Hwfe Hmke).
Qed.    

Lemma mk_env_bexps_cache_consistent :
  forall es s m ca E g cs lr,
    mk_env_bexps_cache s es = (m, ca, E, g, cs, lr) ->
    consistent m E s.
Proof.
  elim.
  - move=> s m ca E g cs lr /=. case=> <- _ <- _ _ _. done.
  - move=> e tl IHtl s m' ca' E' g' cs' lr'. 
    rewrite /mk_env_bexps_cache -/mk_env_bexps_cache.
    case Hmktl : (mk_env_bexps_cache s tl) => [[[[[m ca] E] g] cs] lr].
    move=> Hmke.
    move: (IHtl _ _ _ _ _ _ _ Hmktl) => HcmEs.
    move: (mk_env_bexps_cache_newer_than_vm Hmktl) => Hgm.
    exact: (mk_env_bexp_cache_consistent Hmke Hgm HcmEs). 
Qed.



Lemma mk_env_bexps_cache_well_formed :
  forall es s m ca E g cs lr,
    mk_env_bexps_cache s es = (m, ca, E, g, cs, lr) ->
    Cache.well_formed ca.
Proof.
Admitted.

Lemma mk_env_bexps_cache_newer_than_cache :
  forall es s m ca E g cs lr,
    mk_env_bexps_cache s es = (m, ca, E, g, cs, lr) ->
    newer_than_cache g ca.
Proof.
Admitted.

Lemma mk_env_bexps_cache_regular :
  forall es s m ca E g cs lr,
    mk_env_bexps_cache s es = (m, ca, E, g, cs, lr) ->
    Cache.regular E ca.
Proof.
Admitted.

Lemma mk_env_bexps_cache_sat :
  forall es s m ca E g cs lr,
    mk_env_bexps_cache s es = (m, ca, E, g, cs, lr) ->
    interp_cnf E cs.
Proof.
  case.
  - move=> s m ca E g cs lr /=. case=> _ _ <- _ <- _. done.
  - move=> e tl s m' ca' E' g' cs' lr'. 
    rewrite /mk_env_bexps_cache -/mk_env_bexps_cache.
    case Hmktl : (mk_env_bexps_cache s tl) => [[[[[m ca] E] g] cs] lr].
    move=> Hmke.
    move: (mk_env_bexps_cache_newer_than_vm Hmktl) => Hgm.
    move: (mk_env_bexps_cache_newer_than_tt Hmktl) => Hgtt.
    (* move: (mk_env_bexps_cache_well_formed Hmktl) => Hwfca. *)
    move: (reset_ct_well_formed ca) => Hwfrca.
    move: (mk_env_bexps_cache_newer_than_cache Hmktl).
    rewrite Cache.newer_than_cache_reset_ct => Hgrca.
    move: (mk_env_bexps_cache_regular Hmktl).
    rewrite Cache.regular_reset_ct => HrErca.
    exact: (mk_env_bexp_cache_sat Hmke Hgm Hgtt Hwfrca Hgrca HrErca).
Qed.

Lemma mk_env_bexps_cache_correct :
  forall es s m ca E g cs lr te,
    mk_env_bexps_cache s es = (m, ca, E, g, cs, lr) ->
    AdhereConform.conform_bexps es s te ->
    well_formed_bexps es te ->
    Cache.correct E s ca.
Proof.
  elim.
  - move=> s m ca E g cs lr te /=. case=> _ <- <- _ _ _ _ _. done.
  - move=> e tl IHtl s m' ca' E' g' cs' lr' te Hmk Hcf Hwf. 
    move: (mk_env_bexps_cache_consistent Hmk) => HconmpEps.
    move: (mk_env_bexps_cache_sat Hmk) => HiEpcsp.
    move: (mk_env_bexps_cache_tt Hmk) => Htt.
    have Hpre: interp_cnf E' (add_prelude cs')
      by rewrite add_prelude_expand HiEpcsp Htt.
    move: Hcf Hwf Hmk => /= /andP [Hcfe Hcftl] /andP [Hwfe Hwftl] {Htt HiEpcsp}.
    case Hmktl : (mk_env_bexps_cache s tl) => [[[[[m ca] E] g] cs] lr].
    move=> Hmke.
    move: (mk_env_bexp_cache_is_bit_blast_bexp_cache Hcfe Hwfe Hmke) => Hbbe.
    move: (IHtl _ _ _ _ _ _ _ _ Hmktl Hcftl Hwftl) => HcEsca.
    move: (mk_env_bexp_cache_preserve Hmke) => HpEEpg.
    move: (mk_env_bexps_cache_newer_than_cache Hmktl) => Hgca.
    move: HcEsca. 
    rewrite -(env_preserve_correct s HpEEpg Hgca) => {HpEEpg Hgca} HcEpsca.
    move: (bit_blast_bexp_cache_correct_cache Hbbe Hcfe HconmpEps Hpre Hwfe 
                                              (reset_ct_well_formed ca) HcEpsca).
    by move=> [_ H].
Qed.


(* ===== generalized mk_env ===== *)

Definition mk_envs_cache (s : SSAStore.t) (es : seq QFBV.bexp) : env :=
  let '(m, ca, E, g, cs, lr) := mk_env_bexps_cache s es in
  E.


Lemma mk_envs_cache_tt :
  forall es s, interp_lit (mk_envs_cache s es) lit_tt.
Proof.
  move=> es s. rewrite /mk_envs_cache.
  case Hmkes : (mk_env_bexps_cache s es) => [[[[[m ca] E] g] cs] lr].  
  exact: (mk_env_bexps_cache_tt Hmkes).
Qed.


Lemma mk_envs_cache_consistent :
  forall es s te m ca g cs lr,
    bit_blast_bexps_cache te es = (m, ca, g, cs, lr) ->
    AdhereConform.conform_bexps es s te ->
    well_formed_bexps es te ->
    consistent m (mk_envs_cache s es) s.
Proof.
  move=> es s te m ca g cs lr Hbb Hcf Hwf.
  rewrite /mk_envs_cache.
  case Hmk: (mk_env_bexps_cache s es) => [[[[[m' ca'] E'] g'] cs'] lr'].
  rewrite (mk_env_bexps_cache_is_bit_blast_bexps_cache Hmk Hcf Hwf) in Hbb.
  case: Hbb => <- _ _ _ _.
  exact: (mk_env_bexps_cache_consistent Hmk).
Qed.


Lemma mk_envs_cache_sat :
  forall es s te m ca g cs lr,
    bit_blast_bexps_cache te es = (m, ca, g, cs, lr) ->
    AdhereConform.conform_bexps es s te ->
    well_formed_bexps es te ->
    interp_cnf (mk_envs_cache s es) cs.
Proof.
  move=> es s te m ca g cs lr Hbb Hcf Hwf.
  rewrite /mk_envs_cache.
  case Hmk: (mk_env_bexps_cache s es) => [[[[[m' ca'] E'] g'] cs'] lr'].
  rewrite (mk_env_bexps_cache_is_bit_blast_bexps_cache Hmk Hcf Hwf) in Hbb.
  case: Hbb => _ _ _ <- _.
  exact: (mk_env_bexps_cache_sat Hmk).
Qed.

Lemma mk_envs_cache_correct :
  forall es e s te m ca g cs lr,
    bit_blast_bexps_cache te es = (m, ca, g, cs, lr) ->
    AdhereConform.conform_bexps es s te ->
    well_formed_bexps es te ->
    Cache.correct (mk_envs_cache s (e::es)) s ca.
Proof.
  move=> es e s te m ca g cs lr Hbbes Hcf Hwf.
  rewrite /mk_envs_cache /=.
  case Hmkes: (mk_env_bexps_cache s es) => [[[[[m' ca'] E'] g'] cs'] lr'].
  rewrite (mk_env_bexps_cache_is_bit_blast_bexps_cache Hmkes Hcf Hwf) in Hbbes.
  case: Hbbes => _ <- _ _ _.
  case Hmke: (mk_env_bexp_cache m' (reset_ct ca') s E' g' e)
  => [[[[[me cae] Ee] ge] cse] lre].
  move: (mk_env_bexps_cache_correct Hmkes Hcf Hwf) => HcEp.
  move: (mk_env_bexps_cache_newer_than_cache Hmkes) => Hgpcap.
  move: (mk_env_bexp_cache_preserve Hmke) => HpEpEe.
  rewrite (env_preserve_correct s HpEpEe Hgpcap).
  exact: HcEp.
Qed.


(*
Lemma mk_envs_cache_correct :
  forall es s te m ca g cs lr,
    bit_blast_bexps_cache te es = (m, ca, g, cs, lr) ->
    AdhereConform.conform_bexps es s te ->
    well_formed_bexps es te ->
    Cache.correct (mk_envs_cache s es) s ca.
Proof.
  elim.
  - move=> s te m ca g cs lr /=. case=> _ <- _ _ _ _ _. done.
  - move=> e tl IHtl s te m' ca' g' cs' lr' /=. 
    (* move: (mk_envs_cache_consistent Hbb Hcf Hwf) => Hcon. *)
    (* move: (mk_envs_cache_sat Hbb Hcf Hwf) => Hics'. *)
    move=> Hbb /= /andP [Hcfe Hcftl] /andP [Hwfe Hwftl]. move: Hbb.
    rewrite /mk_envs_cache -/mk_envs_cache /=.
    case Hmktl : (mk_env_bexps_cache s tl) => [[[[[m ca] E] g] cs] lr].
    move: (mk_env_bexps_cache_is_bit_blast_bexps_cache Hmktl Hcftl Hwftl) => Hbbtl.
    rewrite Hbbtl. 
    case Hmke : (mk_env_bexp_cache m (reset_ct ca) s E g e) 
    => [[[[[me cae] Ee] ge] cse] lre].
    move: (mk_env_bexp_cache_is_bit_blast_bexp_cache Hcfe Hwfe Hmke) => Hbbe.
    rewrite Hbbe. case=> _ <- _ _ _.
    move: (mk_env_bexps_cache_consistent Hmktl) => HcmEs.
    move: (mk_env_bexps_cache_newer_than_vm Hmktl) => Hgm.
    move: (mk_env_bexp_cache_consistent Hmke Hgm HcmEs) => HcmeEes.
   Check bit_blast_bexp_cache_correct_cache.
    
move: (IHtl _ _ _ _ _ _ _ Hmktl) => HcEsca.
    Check bit_blast_bexp_cache_correct_cache.
    move:  bit_blast_bexp_cache_correct_cache.
    move: (mk_env_bexps_cache_newer_than_vm Hmktl) => Hgm.
    exact: (mk_env_bexp_cache_consistent Hmke Hgm HcmEs). 
*)


(* ===== Soundness and completeness ===== *)

Theorem bit_blast_cache_general_sound :
  forall (e : QFBV.bexp) (es : seq QFBV.bexp) te m ca g cs lr,
    bit_blast_bexps_cache te (e::es) = (m, ca, g, cs, lr) ->
    well_formed_bexps (e::es) te ->
    ~ (sat (add_prelude ([::neg_lit lr]::cs))) ->
    (forall s,
        AdhereConform.conform_bexps (e::es) s te ->
        QFBV.eval_bexp e s) .
Proof.
  move=> e es te m' ca' g' cs' lr' Hbb Hwf Hsat s Hcf.
  move: (unsat_implies_valid Hsat) => {Hsat} Hsat.
  move: (Hsat (mk_envs_cache s (e::es))) => {Hsat} Hsat.
  move: (mk_envs_cache_sat Hbb Hcf Hwf) => Hcs. 
  move: (mk_envs_cache_tt (e::es) s) => Htt.
  have Hprelude: interp_cnf (mk_envs_cache s (e::es)) (add_prelude cs')
    by rewrite add_prelude_expand Hcs Htt.
  rewrite Hprelude /= in Hsat. 
  move: (mk_envs_cache_consistent Hbb Hcf Hwf) => Hconmp.
  move: Hbb => /=.
  case Hbbes: (bit_blast_bexps_cache te es) => [[[[m ca] g] cs] lr].
  move: Hwf Hcf => /= /andP [Hwfe Hwfes] /andP [Hcfe Hcfes] Hbbe. 
  move: (mk_envs_cache_correct e Hbbes Hcfes Hwfes) => Hcr.
  move: (bit_blast_bexp_cache_correct Hbbe Hcfe Hconmp Hprelude Hwfe
                                      (reset_ct_well_formed ca) Hcr).
  rewrite /enc_bit. move=> /eqP <-.
  exact: Hsat.
Qed.



(* Definition correct_ct (E : env) (s : SSAStore.t) (c : cache) := *)
(*   (forall e ls, ExpMap.find e (cet c) = Some ls -> enc_bits E ls (QFBV.eval_exp e s)) *)
(*   /\ forall e l, BexpMap.find e (cbt c) = Some l -> enc_bit E l (QFBV.eval_bexp e s). *)


(*
Lemma bb_correct_test :
  forall (e : QFBV.bexp) te m ca g m' ca' g' cs lr,
    bit_blast_bexp_cache te m ca g e = (m', ca', g', cs, lr) ->
    (* AdhereConform.conform_bexp e s te -> *)
    QFBV.well_formed_bexp e te ->
    Cache.well_formed ca -> strong_correct m ca ->    
    enc_correct_bexp m' e cs lr.
Proof.
Admitted.

Theorem bit_blast_cache_general_complete :
  forall (e : QFBV.bexp) (es: seq QFBV.bexp) te m ca g cs lr,
    bit_blast_bexps_cache te (e::es) = (m, ca, g, cs, lr) ->
    well_formed_bexps (e::es) te ->
    (forall s, AdhereConform.conform_bexps (e::es) s te ->
               QFBV.eval_bexp e s)
    ->
    ~ (sat (add_prelude ([::neg_lit lr]::cs))).
Proof.
  move=> e es te m' ca' g' cs' lr' Hbb Hwf He.
  move=> [E Hcs].
  rewrite add_prelude_cons in Hcs. move/andP: Hcs => [Hlr Hcs].
  rewrite add_prelude_expand in Hlr. move/andP: Hlr => [Htt Hlr].
  rewrite /= interp_lit_neg_lit Bool.orb_false_r Bool.andb_true_r in Hlr. 
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
*)
