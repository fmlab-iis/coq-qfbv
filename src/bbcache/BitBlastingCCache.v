From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport AdhereConform.
From BBCache Require Import CompCache BitBlastingCCacheDef BitBlastingInit
     BitBlastingCCachePreserve BitBlastingCCacheCorrect BitBlastingCCacheAdhere 
     BitBlastingCCacheBound BitBlastingCCacheMkEnv BitBlastingCCacheConsistent 
     BitBlastingCCacheSat.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ===== mk_env ===== *)

Definition mk_env (s : SSAStore.t) (e : QFBV.bexp) : env :=
  let '(m, c, E, g, cs, l) := 
      mk_env_bexp_ccache init_vm init_ccache s init_env init_gen e in
  E.

Lemma mk_env_consistent :
  forall s e te m c g cs l,
    bit_blast_bexp_ccache te init_vm init_ccache init_gen e = (m, c, g, cs, l) ->
    AdhereConform.conform_bexp e s te ->
    QFBV.well_formed_bexp e te ->
    consistent m (mk_env s e) s.
Proof.
  move=> s e te m c g cs l Hbb Hcf Hwf. rewrite /mk_env.
  case Henv: (mk_env_bexp_ccache init_vm init_ccache s init_env init_gen e) 
  => [[[[[m' c'] E'] g'] cs'] l'].
  move: (mk_env_bexp_ccache_is_bit_blast_bexp_ccache Hcf Hwf Henv). 
  rewrite Hbb. case=> -> _ _ _ _.
  apply: (mk_env_bexp_ccache_consistent Henv init_newer_than_vm).
  exact: init_consistent.
Qed.

Lemma mk_env_tt :
  forall s e, interp_lit (mk_env s e) lit_tt.
Proof.
  move=> s e. rewrite /mk_env.
  case Henv: (mk_env_bexp_ccache init_vm init_ccache s init_env init_gen e) 
  => [[[[[m c] E] g] cs] l].
  rewrite (env_preserve_lit (mk_env_bexp_ccache_preserve Henv) init_newer_than_tt).
  exact: init_tt.
Qed. 

Lemma mk_env_sat :
  forall s e te m c g cs l,
    bit_blast_bexp_ccache te init_vm init_ccache init_gen e = (m, c, g, cs, l) ->
    AdhereConform.conform_bexp e s te ->
    QFBV.well_formed_bexp e te ->
    interp_cnf (mk_env s e) cs.
Proof.
  move=> s e te m c g cs l Hbb Hcf Hwf. 
  move: (mk_env_tt s e). rewrite /mk_env.
  case Henv: (mk_env_bexp_ccache init_vm init_ccache s init_env init_gen e) 
  => [[[[[m' c'] E'] g'] cs'] l'].
  move: (mk_env_bexp_ccache_is_bit_blast_bexp_ccache Hcf Hwf Henv).
  rewrite Hbb; case=> _ _ _ -> _ Htt.
  exact: (mk_env_bexp_ccache_sat Henv init_newer_than_vm init_newer_than_tt 
                                 init_ccache_well_formed init_newer_than_cache 
                                 init_interp_cache).
Qed.


(* ===== mk_state ===== *)

Fixpoint lits_as_bits E (ls : word) : bits :=
  match ls with
  | [::] => [::]
  | hd::tl => joinlsb (interp_lit E hd) (lits_as_bits E tl)
  end .

Lemma enc_bits_lits_as_bits :
  forall E (ls : word),
    enc_bits E ls (lits_as_bits E ls).
Proof.
  move => E .
  elim .
  - done.
  - move => l ls IH .
    rewrite /= enc_bits_cons IH /= /enc_bit eqxx // .
Qed.

(* TypEnv.deftyp is Tuint 0. *)
Definition init_state : SSAStore.t := fun _ => from_nat 0 0.

Definition mk_state (E : env) (m : vm) : SSAStore.t :=
  (SSAVM.fold (fun v ls s => SSAStore.upd v (lits_as_bits E ls) s) m init_state).

Lemma mk_state_find :
  forall E m x ls,
    SSAVM.find x m = Some ls ->
    SSAStore.acc x (mk_state E m) = lits_as_bits E ls.
Proof.
  move=> E m.
  apply: (@SSAVM.Lemmas.OP.P.fold_rec
            word (SSAStore.t)
            (fun m s =>
               forall x ls,
                 SSAVM.find x m = Some ls ->
                 SSAStore.acc x s = lits_as_bits E ls)
            (fun v ls s => SSAStore.upd v (lits_as_bits E ls) s)
            init_state
            m).
  - move=> m0 Hempty x ls Hfind. 
    rewrite (SSAVM.Lemmas.Empty_find _ Hempty) in Hfind.
    discriminate.
  - move=> x lsx s m' m'' Hmapsto_xm Hin_xm' Hadd IH. move=> y lsy Hfind_y.
    case Hyx: (y == x).
    + rewrite (SSAStore.acc_upd_eq Hyx). move: (Hadd y).
      rewrite Hfind_y (SSAVM.Lemmas.find_add_eq Hyx). case=> ->. reflexivity.
    + move/idP/negP: Hyx => Hyx. rewrite (SSAStore.acc_upd_neq  Hyx).
      apply: IH. move: (Hadd y). rewrite Hfind_y. move/negP: Hyx => Hyx.
      rewrite (SSAVM.Lemmas.find_add_neq Hyx). by move=> ->; reflexivity.
Qed.

Lemma mk_state_consistent :
  forall E m, consistent m E (mk_state E m).
Proof.
  move=> E m x. rewrite /consistent1. case Hfind: (SSAVM.find x m); last by trivial.
  rewrite (mk_state_find _ Hfind). exact: enc_bits_lits_as_bits.
Qed.

Lemma mk_state_conform_bexp :
  forall e te E m',
    AdhereConform.bound_bexp e m' ->
    AdhereConform.adhere m' te ->
    AdhereConform.conform_bexp e (mk_state E m') te .
Proof .
  move=> e te E m' Hbnd Had.
  move: (mk_state_consistent E m') => Hcon.
  exact: (consistent_conform_bexp Hbnd Had Hcon).
Qed.


(* ===== Soundness and completeness ===== *)

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
    ~ (sat (add_prelude ([::neg_lit lr]::cs))) 
    ->
    (forall s, AdhereConform.conform_bexp e s te ->
               QFBV.eval_bexp e s) .
Proof.
  move=> e te m c g cs lr Hblast Hwf Hsat s Hcf.
  move: (unsat_implies_valid Hsat) => {Hsat} Hsat.
  move: (Hsat (mk_env s e)) => {Hsat} Hsat.
  move: (mk_env_sat Hblast Hcf Hwf) => Hcs. 
  move: (mk_env_tt s e) => Htt.
  have Hprelude: interp_cnf (mk_env s e) (add_prelude cs)
    by rewrite add_prelude_expand Hcs Htt.
  move: (bit_blast_bexp_ccache_correct Hblast Hcf (mk_env_consistent Hblast Hcf Hwf)
                                       Hwf init_ccache_well_formed Hprelude 
                                       (init_interp_cache_ct (mk_env s e))
                                       (init_correct init_vm)).
  rewrite /enc_bit. move=> /eqP <-.
  rewrite Hprelude /= in Hsat. exact: Hsat.
Qed.


Theorem bit_blast_ccache_complete :
  forall (e : QFBV.bexp) te m' c' g' cs lr,
    bit_blast_bexp_ccache te init_vm init_ccache init_gen e = (m', c', g', cs, lr) ->
    QFBV.well_formed_bexp e te ->
    (forall s, AdhereConform.conform_bexp e s te ->
               QFBV.eval_bexp e s)
    ->
    ~ (sat (add_prelude ([::neg_lit lr]::cs))).
Proof.
  move=> e te m' c' g' cs lr Hblast Hwf He.
  move=> [E Hcs].
  rewrite add_prelude_cons in Hcs. move/andP: Hcs => [Hlr Hcs].
  rewrite add_prelude_expand in Hlr. move/andP: Hlr => [Htt Hlr].
  rewrite /= interp_lit_neg_lit in Hlr.
  move : (bit_blast_bexp_ccache_adhere (init_vm_adhere te) Hblast) => Hadm' .
  move : (bit_blast_bexp_ccache_bound Hblast init_ccache_well_formed 
                                      init_bound_cache) => Hbound .
  move : (mk_state_conform_bexp E Hbound Hadm') => Hcf .
  move : (He (mk_state E m') Hcf) => {He} He .
  move: (bit_blast_bexp_ccache_correct Hblast Hcf (mk_state_consistent E m') 
                                       Hwf init_ccache_well_formed Hcs 
                                       (init_interp_cache_ct E)
                                       (init_correct init_vm)).
  rewrite /enc_bit => /eqP H. rewrite -H in He.
  rewrite He in Hlr. exact: not_false_is_true.
Qed.

Definition bexp_to_cnf_ccache te m c g e :=
  let '(m', c', g', cs, lr) := bit_blast_bexp_ccache te m c g e in
  (m', c', g', add_prelude ([::neg_lit lr]::cs)).
