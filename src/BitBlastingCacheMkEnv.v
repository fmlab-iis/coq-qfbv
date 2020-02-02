From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF Cache BBExport 
     AdhereConform BitBlastingCacheDef .

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* = mk_env_exp_cache_is_bit_blast_exp_cache and mk_env_bexp_cache_is_bit_blast_bexp_cache = *)

Lemma mk_env_exp_cache_is_bit_blast_exp_cache_nocache_var :
  forall (t : SSAVarOrder.t) (te : SSATE.env) (m : SSAVM.t word) 
         (ca : cache) (E : env) (g : generator) (s : SSAStore.t) 
         (m' : vm) (ca' : cache) (E' : env) (g' : generator) 
         (cs : cnf) (lrs : word),
    conform_exp (QFBV.Evar t) s te ->
    QFBV.well_formed_exp (QFBV.Evar t) te ->
    find_cet (QFBV.Evar t) ca = None ->
    find_het (QFBV.Evar t) ca = None ->
    mk_env_exp_cache m ca s E g (QFBV.Evar t) = (m', ca', E', g', cs, lrs) ->
    bit_blast_exp_cache te m ca g (QFBV.Evar t) = (m', ca', g', cs, lrs).
Proof.
  rewrite /= => t te m ca E g s m' ca' E' g' cs lrs Hsize _ Hfcet Hfhet.
  rewrite Hfcet Hfhet /=.
  case : (SSAVM.find t m) .
  - move => a; case => <- <- _ <- <- <- // .
  - dcase (mk_env_var E g (SSAStore.acc t s) t) => [[[[E'0 g'0] cs0] rs] Hmkr] .
    dcase (bit_blast_var te g t) => [[[g'1 cs1] rs0] Hbst] .
    case => <- <- _ <- <- <- .
    rewrite (mk_env_var_is_bit_blast_var (Logic.eq_sym (eqP Hsize)) Hmkr) in Hbst .
    move : Hbst; case => <- <- <- // .
Qed.

Lemma mk_env_exp_cache_is_bit_blast_exp_cache_nocache_const :
  forall (b : bits) (te : SSATE.env) (m : SSAVM.t word) 
         (ca : cache) (E : env) (g : generator) (s : SSAStore.t) 
         (m' : vm) (ca' : cache) (E' : env) (g' : generator) 
         (cs : cnf) (lrs : word),
    conform_exp (QFBV.Econst b) s te ->
    QFBV.well_formed_exp (QFBV.Econst b) te ->
    find_cet (QFBV.Econst b) ca = None ->
    find_het (QFBV.Econst b) ca = None ->
    mk_env_exp_cache m ca s E g (QFBV.Econst b) = (m', ca', E', g', cs, lrs) ->
    bit_blast_exp_cache te m ca g (QFBV.Econst b) = (m', ca', g', cs, lrs).
Proof.
  rewrite /=; move => b te m ca E g s m' ca' E' g' cs lrs Hcf _ Hfcet Hfhet.
  rewrite Hfcet Hfhet /=.
  case => <- <- _ <- <- <- // .
Qed.

Lemma mk_env_exp_cache_is_bit_blast_exp_cache_nocache_and :
  forall e1 : QFBV.exp,
    (forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
            (E : env) (g : generator) (s : SSAStore.t) (m' : vm) 
            (ca' : cache) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp_cache m ca s E g e1 = (m', ca', E', g', cs, lrs) ->
        bit_blast_exp_cache te m ca g e1 = (m', ca', g', cs, lrs)) ->
    forall e2 : QFBV.exp,
      (forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
              (E : env) (g : generator) (s : SSAStore.t) (m' : vm) 
              (ca' : cache) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp_cache m ca s E g e2 = (m', ca', E', g', cs, lrs) ->
          bit_blast_exp_cache te m ca g e2 = (m', ca', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
             (E : env) (g : generator) (s : SSAStore.t) (m' : vm) 
             (ca' : cache) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
        conform_exp (QFBV.Ebinop QFBV.Band e1 e2) s te ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Band e1 e2) te ->
        find_cet (QFBV.Ebinop QFBV.Band e1 e2) ca = None ->
        find_het (QFBV.Ebinop QFBV.Band e1 e2) ca = None ->
        mk_env_exp_cache m ca s E g (QFBV.Ebinop QFBV.Band e1 e2) =
        (m', ca', E', g', cs, lrs) ->
        bit_blast_exp_cache te m ca g (QFBV.Ebinop QFBV.Band e1 e2) =
        (m', ca', g', cs, lrs).
Proof.
  move=> e1 IH1 e2 IH2 te m ca E g s m' ca' E' g' cs lrs /andP [Hcf1 Hcf2] /= 
            /andP [/andP [Hwf1 Hwf2] Hsize] Hfcet Hfhet.
  rewrite Hfcet Hfhet /=.
  case Hmke1 : (mk_env_exp_cache m ca s E g e1) => [[[[[m1 ca1] E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp_cache m1 ca1 s E1 g1 e2) => [[[[[m2 ca2] E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ <- <- <-.
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1)
          (IH2 _ _ _ _ _ _ _ _ _ _ _ _ Hcf2 Hwf2 Hmke2) .
  by rewrite (mk_env_and_is_bit_blast_and Hmkr).
Qed.

Lemma mk_env_bexp_cache_is_bit_blast_bexp_cache_nocache_conj :
  forall b1 : QFBV.bexp,
    (forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
            (s : SSAStore.t) (E : env) (g : generator) (m' : vm) 
            (ca' : cache) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        conform_bexp b1 s te ->
        QFBV.well_formed_bexp b1 te ->
        mk_env_bexp_cache m ca s E g b1 = (m', ca', E', g', cs, lr) ->
        bit_blast_bexp_cache te m ca g b1 = (m', ca', g', cs, lr)) ->
    forall b2 : QFBV.bexp,
      (forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
              (s : SSAStore.t) (E : env) (g : generator) (m' : vm) 
              (ca' : cache) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          conform_bexp b2 s te ->
          QFBV.well_formed_bexp b2 te ->
          mk_env_bexp_cache m ca s E g b2 = (m', ca', E', g', cs, lr) ->
          bit_blast_bexp_cache te m ca g b2 = (m', ca', g', cs, lr)) ->
      forall (te : SSATE.env) (m : SSAVM.t word) (ca : cache) 
             (E : SSAStore.t) (g : env) (s : generator) (m' : vm) 
             (ca' : cache) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        conform_bexp (QFBV.Bconj b1 b2) E te ->
        QFBV.well_formed_bexp (QFBV.Bconj b1 b2) te ->
        find_cbt (QFBV.Bconj b1 b2) ca = None ->
        find_hbt (QFBV.Bconj b1 b2) ca = None ->
        mk_env_bexp_cache m ca E g s (QFBV.Bconj b1 b2) = (m', ca', E', g', cs, lr) ->
        bit_blast_bexp_cache te m ca s (QFBV.Bconj b1 b2) = (m', ca', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m ca s E g m' ca' E' g' cs lrs /= 
            /andP [Hcf0 Hcf1] /andP [Hwf0 Hwf1] Hfcbt Hfhbt.
  rewrite Hfcbt Hfhbt /=.
  case Hmke0 : (mk_env_bexp_cache m ca s E g e0) => [[[[[m1 ca1] E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_bexp_cache m1 ca1 s E1 g1 e1) => [[[[[m2 ca2] E2] g2] cs2] ls2].
  case=> <- <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1) //.
Qed.


Corollary mk_env_exp_cache_is_bit_blast_exp_cache :
  forall (e : QFBV.exp) te m ca E g s m' ca' E' g' cs lrs,
    AdhereConform.conform_exp e s te ->
    QFBV.well_formed_exp e te ->
    mk_env_exp_cache m ca s E g e = (m', ca', E', g', cs, lrs) ->
    bit_blast_exp_cache te m ca g e = (m', ca', g', cs, lrs)
  with
    mk_env_bexp_cache_is_bit_blast_bexp_cache :
      forall e te m ca s E g m' ca' E' g' cs lr,
        AdhereConform.conform_bexp e s te ->
        QFBV.well_formed_bexp e te ->
        mk_env_bexp_cache m ca s E g e = (m', ca', E', g', cs, lr) ->
        bit_blast_bexp_cache te m ca g e = (m', ca', g', cs, lr).
Proof.
  (* mk_env_exp_cache_is_bit_blast_exp_cache *)
  move=> e te m ca E g s m' ca' E' g' cs lrs Hcf Hwf.
  case Hfcet: (find_cet e ca) => [ls|]. 
  - rewrite mk_env_exp_cache_equation bit_blast_exp_cache_equation Hfcet /=.
    case=> <- <- _ <- <- <-. done. 
  - case Hfhet: (find_het e ca) => [[csh lsh]|].
    + rewrite mk_env_exp_cache_equation bit_blast_exp_cache_equation Hfcet Hfhet /=. 
      case=> <- <- _ <- <- <-. done. 
    + move: e te m ca E g s m' ca' E' g' cs lrs Hcf Hwf Hfcet Hfhet.
      case.
      * move => v; apply : mk_env_exp_cache_is_bit_blast_exp_cache_nocache_var .
      * move => b; apply : mk_env_exp_cache_is_bit_blast_exp_cache_nocache_const .
      * elim .
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_not . *)
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_neg . *)
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_extract . *)
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_high . *)
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_low . *)
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_zeroextend . *)
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_signextend . *)
      * elim .
        -- move=> e1 e2. 
           apply: mk_env_exp_cache_is_bit_blast_exp_cache_nocache_and;
             by apply: mk_env_exp_cache_is_bit_blast_exp_cache.
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_or . *)
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_xor . *)
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_add . *)
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_sub . *)
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_mul . *)
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_mod . *)
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_srem . *)
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_smod . *)
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_shl . *)
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_lshr . *)
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_ashr . *)
        -- admit. (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_concat . *)
      * admit. (* move => b e1 e2. *)
        (* move : b (mk_env_bexp_cache_is_bit_blast_bexp_cache b)  *)
        (*          e1 (mk_env_exp_cache_is_bit_blast_exp_cache e1) *)
        (*          e2 (mk_env_exp_cache_is_bit_blast_exp_cache e2) . *)
        (* apply : mk_env_exp_cache_is_bit_blast_exp_cache_ite . *)
  (* mk_env_bexp_cache_is_bit_blast_bexp_cache *)
  move=> e te m ca E g s m' ca' E' g' cs lr Hcf Hwf.
  case Hfcbt: (find_cbt e ca) => [l|]. 
  - rewrite mk_env_bexp_cache_equation bit_blast_bexp_cache_equation Hfcbt /=.
    case=> <- <- _ <- <- <-. done. 
  - case Hfhbt: (find_hbt e ca) => [[csh lh]|].
    + rewrite mk_env_bexp_cache_equation bit_blast_bexp_cache_equation Hfcbt Hfhbt /=. 
      case=> <- <- _ <- <- <-. done. 
    + move: e te m ca E g s m' ca' E' g' cs lr Hcf Hwf Hfcbt Hfhbt.
      case.
      * admit. (* : mk_env_bexp_cache_is_bit_blast_bexp_cache_false. *)
      * admit. (* : mk_env_bexp_cache_is_bit_blast_bexp_cache_true. *)
      * elim => e1 e2;
        move : e1 (mk_env_exp_cache_is_bit_blast_exp_cache e1)
               e2 (mk_env_exp_cache_is_bit_blast_exp_cache e2) .
        -- admit.  (* mk_env_bexp_cache_is_bit_blast_bexp_cache_eq . *)
        -- admit.  (* mk_env_bexp_cache_is_bit_blast_bexp_cache_ult . *)
        -- admit.   (* mk_env_bexp_cache_is_bit_blast_bexp_cache_ule . *)
        -- admit.  (* mk_env_bexp_cache_is_bit_blast_bexp_cache_ugt . *)
        -- admit.  (* mk_env_bexp_cache_is_bit_blast_bexp_cache_uge . *)
        -- admit. (* apply : mk_env_bexp_cache_is_bit_blast_bexp_cache_slt . *)
        -- admit. (* apply : mk_env_bexp_cache_is_bit_blast_bexp_cache_sle . *)
        -- admit. (* apply : mk_env_bexp_cache_is_bit_blast_bexp_cache_sgt . *)
        -- admit. (* apply : mk_env_bexp_cache_is_bit_blast_bexp_cache_sge . *)
        -- admit. (* apply : mk_env_bexp_cache_is_bit_blast_bexp_cache_uaddo . *)
        -- admit. (* apply : mk_env_bexp_cache_is_bit_blast_bexp_cache_usubo . *)
        -- admit. (* apply : mk_env_bexp_cache_is_bit_blast_bexp_cache_umulo . *)
        -- admit. (* apply : mk_env_bexp_cache_is_bit_blast_bexp_cache_saddo . *)
        -- admit. (* apply : mk_env_bexp_cache_is_bit_blast_bexp_cache_ssubo . *)
        -- admit. (* apply : mk_env_bexp_cache_is_bit_blast_bexp_cache_smulo . *)
      * admit.  (* : mk_env_bexp_cache_is_bit_blast_bexp_cache_lneg . *)
      * move=> b1 b2; 
        move : b1 (mk_env_bexp_cache_is_bit_blast_bexp_cache b1)
               b2 (mk_env_bexp_cache_is_bit_blast_bexp_cache b2) .
        exact: mk_env_bexp_cache_is_bit_blast_bexp_cache_nocache_conj.
      * admit.  (* : mk_env_bexp_cache_is_bit_blast_bexp_cache_disj . *)
(* Qed. *)
Admitted.
