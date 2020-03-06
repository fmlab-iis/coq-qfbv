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
     BitBlastingInit BitBlastingCCacheAdhere BitBlastingCCacheBound.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


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
  - move=> m0 Hempty x ls Hfind. rewrite (SSAVM.Lemmas.Empty_find _ Hempty) in Hfind.
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


Lemma size_lits_as_bits E ls :
  size ls = size (lits_as_bits E ls) .
Proof .
  elim ls; first done .
  move => a l IH .
  rewrite /= IH // .
Qed .

Lemma mk_state_conform_exp :
  forall e te E m',
    AdhereConform.bound_exp e m' ->
    AdhereConform.adhere m' te ->
    AdhereConform.conform_exp e (mk_state E m') te
with
mk_state_conform_bexp :
  forall e te E m',
    AdhereConform.bound_bexp e m' ->
    AdhereConform.adhere m' te ->
    AdhereConform.conform_bexp e (mk_state E m') te .
Proof .
  (* mk_state_conform_exp *)
  elim; rewrite /= .
  - move => v te E m' Hmem Had .
    elim : (Had _ Hmem) => ls [Hfind Hsize] .
    rewrite (eqP Hsize) (mk_state_find _ Hfind) -size_lits_as_bits // .
  - done .
  - elim => /= [e IHe te E m' Hbound Had |
                e IHe te E m' Hbound Had |
                i j e IHe te E m' Hbound Had |
                n e IHe te E m' Hbound Had |
                n e IHe te E m' Hbound Had |
                n e IHe te E m' Hbound Had |
                n e IHe te E m' Hbound Had];
              exact : (IHe _ _ _ Hbound Had) .
  - elim => /= e0 IH0 e1 IH1 te E m' /andP [Hbound0 Hbound1] Had;
      rewrite (IH0 _ _ _ Hbound0 Had) (IH1 _ _ _ Hbound1 Had) // .
  - move => c e0 IH0 e1 IH1 te E m' /andP [/andP [Hboundc Hbound0] Hbound1] Had .
    rewrite (mk_state_conform_bexp c _ _ _ Hboundc Had)
            (IH0 _ _ _ Hbound0 Had) (IH1 _ _ _ Hbound1 Had) // .
  (* mk_state_conform_bexp *)
  elim; rewrite /= .
  - done .
  - done .
  - elim => e0 e1 te E m' /andP [Hbound0 Hbound1] Had;
      rewrite (mk_state_conform_exp e0 _ _ _ Hbound0 Had)
              (mk_state_conform_exp e1 _ _ _ Hbound1 Had) // .
  - move => b IHb te E m'; apply : IHb .
  - move => b0 IH0 b1 IH1 te E m' /andP [Hbound0 Hbound1] Had;
      rewrite (IH0 _ _ _ Hbound0 Had) (IH1 _ _ _ Hbound1 Had) // .
  - move => b0 IH0 b1 IH1 te E m' /andP [Hbound0 Hbound1] Had;
      rewrite (IH0 _ _ _ Hbound0 Had) (IH1 _ _ _ Hbound1 Had) // .
Qed .



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
  move : (bit_blast_bexp_ccache_bound Hblast init_ccache_well_formed init_bound_cache)
  => Hbound .
  move : (mk_state_conform_bexp E Hbound Hadm') => Hcf .
  move : (He (mk_state E m') Hcf) => {He} He .
(* Check bit_blast_bexp_ccache_correct. *)
  move: (bit_blast_bexp_ccache_correct Hblast Hcf (mk_state_consistent E m') 
                                       Hwf init_ccache_well_formed Hcs 
                                       (init_interp_cache_ct E)
                                       (init_correct init_vm)).
  rewrite /enc_bit => /eqP H. rewrite -H in He.
  rewrite He in Hlr. exact: not_false_is_true.
Qed.



