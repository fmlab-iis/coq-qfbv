
From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Var Types SsrOrder Nats ZAriths Store FSets Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBCommon.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Conform .

  Fixpoint conform_exp (e : QFBV.exp) (s : SSAStore.t) (te : SSATE.env) : bool :=
    match e with
    | QFBV.Evar v => SSATE.vsize v te == size (SSAStore.acc v s)
    | QFBV.Econst _ => true
    | QFBV.Eunop op e => conform_exp e s te
    | QFBV.Ebinop op e1 e2 => conform_exp e1 s te && conform_exp e2 s te
    | QFBV.Eite b e1 e2 =>
      conform_bexp b s te && conform_exp e1 s te && conform_exp e2 s te
    end
  with
  conform_bexp (b : QFBV.bexp) (s : SSAStore.t) (te : SSATE.env) : bool :=
    match b with
    | QFBV.Bfalse
    | QFBV.Btrue => true
    | QFBV.Bbinop _ e1 e2 => conform_exp e1 s te && conform_exp e2 s te
    | QFBV.Blneg b => conform_bexp b s te
    | QFBV.Bconj b1 b2
    | QFBV.Bdisj b1 b2 => conform_bexp b1 s te && conform_bexp b2 s te
    end.

  (*
  Lemma conform_exp_upd x ty v s te :
    sizeof_typ ty = size v ->
    conform_exp (QFBV.Evar v) s te -> conform_exp (QFBV.Evar v) (SSAStore.upd x v s) (SSATE.add x ty te) .
  Proof.
    move=> Hs Hcon y. case Hyx: (y == x).
    - by rewrite (TypEnv.vsize_add_eq Hyx) (Store.acc_upd_eq Hyx).
    - move/idP/negP: Hyx => Hyx. rewrite (TypEnv.mem_add_neq Hyx) => Hmem.
      rewrite (Store.acc_upd_neq Hyx) (TypEnv.vsize_add_neq Hyx). exact: (Hcon _ Hmem).
  Qed.
   *)
  Lemma eval_conform_exp_size e te s :
    QFBV.well_formed_exp e te -> conform_exp e s te -> size (QFBV.eval_exp e s) = QFBV.exp_size e te.
  Proof .
    (* QFBV.exp *)
    elim e; rewrite /= .
    - move => v _ Hsize; rewrite (eqP Hsize) // .
    - done .
    - elim; rewrite /= .
      + move => e0 IH Hwf Hcf .
        rewrite -(IH Hwf Hcf) /invB size_map // .
      + move => e0 IH Hwf Hcf .
        rewrite -(IH Hwf Hcf) /negB /invB size_succB size_map // .
      + move => i j e0 _ _ _; rewrite size_extract // .
      + move => n e0 _ _ _; rewrite size_high // .
      + move => n e0 _ _ _; rewrite size_low // .
      + move => n e0 IH Hwf Hcf .
        rewrite -(IH Hwf Hcf) /zext size_cat size_zeros // .
      + move => n e0 IH Hwf Hcf .
        rewrite -(IH Hwf Hcf) /sext size_cat size_copy // .
      + move => n e0 IH Hwf Hcf .
        rewrite -(IH Hwf Hcf) size_repeat // .
      + move => n e0 IH Hwf Hcf .
        rewrite -(IH Hwf Hcf) size_rolB // .
      + move => n e0 IH Hwf Hcf .
        rewrite -(IH Hwf Hcf) size_rorB // .
    - elim; rewrite /=;
       move => e0 IH0 e1 IH1
                  /andP [/andP [/andP [Hwf0 Hwf1] Hszgt0] Hsize]
                  /andP [Hcf0 Hcf1] .
      + rewrite /andB size_lift (IH0 Hwf0 Hcf0) (IH1 Hwf1 Hcf1) (eqP Hsize) .
        reflexivity.
      + rewrite /orB size_lift (IH0 Hwf0 Hcf0) (IH1 Hwf1 Hcf1) (eqP Hsize) .
        reflexivity.
      + rewrite /xorB size_lift (IH0 Hwf0 Hcf0) (IH1 Hwf1 Hcf1) (eqP Hsize) .
        reflexivity.
      + rewrite size_addB (IH0 Hwf0 Hcf0) (IH1 Hwf1 Hcf1) (eqP Hsize) .
        reflexivity.
      + rewrite size_subB (IH0 Hwf0 Hcf0) (IH1 Hwf1 Hcf1) (eqP Hsize) .
        reflexivity.
      + rewrite size_mulB (IH0 Hwf0 Hcf0) . reflexivity.
      + rewrite size_udivB (IH0 Hwf0 Hcf0). reflexivity.
      + rewrite size_uremB (IH0 Hwf0 Hcf0). reflexivity.
      + rewrite size_sdivB (IH0 Hwf0 Hcf0). reflexivity.
      + rewrite size_sremB (IH0 Hwf0 Hcf0). reflexivity.
      + rewrite size_smodB_ss.
        * rewrite (IH0 Hwf0 Hcf0). reflexivity.
        * rewrite (IH0 Hwf0 Hcf0) (IH1 Hwf1 Hcf1). exact: (eqP Hsize).
      + rewrite size_shlB (IH0 Hwf0 Hcf0) . reflexivity.
      + rewrite size_shrB (IH0 Hwf0 Hcf0) . reflexivity.
      + rewrite size_sarB (IH0 Hwf0 Hcf0) . reflexivity.
      + rewrite size_cat (IH0 Hwf0 Hcf0) (IH1 Hwf1 Hcf1) addnC // .
    - move => b e0 IH0 e1 IH1
                /andP [/andP [/andP [Hwfb Hwf0] Hwf1] Hsize]
                /andP [/andP [Hcfb Hcf0] Hcf1] .
      case (QFBV.eval_bexp b s) .
      * rewrite -(eqP Hsize) (IH0 Hwf0 Hcf0) maxnn. reflexivity.
      * rewrite (eqP Hsize) (IH1 Hwf1 Hcf1) maxnn. reflexivity.
  Qed .


  Fixpoint conform_bexps (bs : seq QFBV.bexp) s te : bool :=
    match bs with
    | [::] => true
    | b :: bs' => conform_bexp b s te && conform_bexps bs' s te
    end.


  Lemma conform_exp_mem E e s v :
    conform_exp e s E ->
    SSAVS.mem v (QFBV.vars_exp e) ->
    size (SSAStore.acc v s) = SSATE.vsize v E
  with conform_bexp_mem E e s v :
    conform_bexp e s E ->
    SSAVS.mem v (QFBV.vars_bexp e) ->
    size (SSAStore.acc v s) = SSATE.vsize v E.
  Proof.
    (* conform_exp_mem *)
    case: e => //=.
    - move=> x /eqP Hs Hmem. move: (SSAVS.Lemmas.mem_singleton1 Hmem) => Heq.
      rewrite (eqP Heq) Hs. reflexivity.
    - move=> _ e Hco Hmem. exact: (conform_exp_mem _ _ _ _ Hco Hmem).
    - move=> _ e1 e2 /andP [Hco1 Hco2]. rewrite SSAVS.Lemmas.mem_union.
      case/orP=> Hmem.
      + exact: (conform_exp_mem _ _ _ _ Hco1 Hmem).
      + exact: (conform_exp_mem _ _ _ _ Hco2 Hmem).
    - move=> b e1 e2 /andP [/andP [Hco_b Hco1] Hco2].
      rewrite !SSAVS.Lemmas.mem_union. (case/orP; last case/orP) => Hmem.
      + exact: (conform_bexp_mem _ _ _ _ Hco_b Hmem).
      + exact: (conform_exp_mem _ _ _ _ Hco1 Hmem).
      + exact: (conform_exp_mem _ _ _ _ Hco2 Hmem).
    (* conform_bexp_mem *)
    case: e => //=.
    - move=> _ e1 e2 /andP [Hco1 Hco2]. rewrite SSAVS.Lemmas.mem_union.
      case/orP=> Hmem.
      + exact: (conform_exp_mem _ _ _ _ Hco1 Hmem).
      + exact: (conform_exp_mem _ _ _ _ Hco2 Hmem).
    - move=> e Hco Hmem. exact: (conform_bexp_mem _ _ _ _ Hco Hmem).
    - move=> e1 e2 /andP [Hco1 Hco2]. rewrite SSAVS.Lemmas.mem_union.
      case/orP=> Hmem.
      + exact: (conform_bexp_mem _ _ _ _ Hco1 Hmem).
      + exact: (conform_bexp_mem _ _ _ _ Hco2 Hmem).
    - move=> e1 e2 /andP [Hco1 Hco2]. rewrite SSAVS.Lemmas.mem_union.
      case/orP=> Hmem.
      + exact: (conform_bexp_mem _ _ _ _ Hco1 Hmem).
      + exact: (conform_bexp_mem _ _ _ _ Hco2 Hmem).
  Qed.

End Conform .

Section Adhere .

  Definition adhere (m : vm) (te : SSATE.env) : Prop :=
    forall v, SSAVM.mem v m -> exists ls, SSAVM.find v m = Some ls /\
                                          SSATE.vsize v te == size ls .
  
End Adhere .

Section Bound .
  Fixpoint bound_exp e (vm : vm) : bool :=
    match e with
    | QFBV.Evar v => SSAVM.mem v vm
    | QFBV.Econst _ => true
    | QFBV.Eunop op e => bound_exp e vm
    | QFBV.Ebinop op e1 e2 => bound_exp e1 vm && bound_exp e2 vm
    | QFBV.Eite b e1 e2 =>
      bound_bexp b vm && bound_exp e1 vm && bound_exp e2 vm
    end
  with
  bound_bexp b vm : bool :=
    match b with
    | QFBV.Bfalse
    | QFBV.Btrue => true
    | QFBV.Bbinop _ e1 e2 => bound_exp e1 vm && bound_exp e2 vm
    | QFBV.Blneg b => bound_bexp b vm
    | QFBV.Bconj b1 b2
    | QFBV.Bdisj b1 b2 => bound_bexp b1 vm && bound_bexp b2 vm
    end.

  Lemma vm_preserve_bound_exp :
    forall e vm vm', bound_exp e vm -> vm_preserve vm vm' -> bound_exp e vm'
  with
  vm_preserve_bound_bexp :
    forall e vm vm', bound_bexp e vm -> vm_preserve vm vm' -> bound_bexp e vm' .
  Proof .
    (* vm_preserve_bound_exp *)
    elim; rewrite /= .
    - move => v vm vm' Hmem Hpsrv .
      elim : (SSAVM.Lemmas.mem_find_some Hmem) => ls Hfind .
      move : (Hpsrv v ls Hfind) .
      exact : SSAVM.Lemmas.find_some_mem .
    - done .
    - move => unop e IHe vm vm' He Hpsrv .
      exact : (IHe _ _ He Hpsrv) .
    - move => binop e0 IH0 e1 IH1 vm vm' /andP [He0 He1] Hpsrv .
      rewrite (IH0 _ _ He0 Hpsrv) (IH1 _ _ He1 Hpsrv) // .
    - move => c e0 IH0 e1 IH1 vm vm' /andP [/andP [Hc He0] He1] Hpsrv .
      rewrite (vm_preserve_bound_bexp c _ _ Hc Hpsrv)
              (IH0 _ _ He0 Hpsrv) (IH1 _ _ He1 Hpsrv) // .
    (* vm_preserve_bound_bexp *)
    elim; rewrite /= .
    - done .
    - done .
    - move => binop e0 e1 vm vm' /andP [He0 He1] Hpsrv .
      rewrite (vm_preserve_bound_exp e0 _ _ He0 Hpsrv)
              (vm_preserve_bound_exp e1 _ _ He1 Hpsrv) // .
    - move => b IHb; exact : IHb .
    - move => b0 IH0 b1 IH1 vm vm' /andP [Hb0 Hb1] Hpsrv .
      rewrite (IH0 _ _ Hb0 Hpsrv) (IH1 _ _ Hb1 Hpsrv) // .
    - move => b0 IH0 b1 IH1 vm vm' /andP [Hb0 Hb1] Hpsrv .
      rewrite (IH0 _ _ Hb0 Hpsrv) (IH1 _ _ Hb1 Hpsrv) // .
  Qed .

  Lemma consistent_conform_exp :
    forall e m te E s, bound_exp e m -> adhere m te ->
                       consistent m E s -> conform_exp e s te
  with
  consistent_conform_bexp :
    forall e m te E s, bound_bexp e m -> adhere m te ->
                       consistent m E s -> conform_bexp e s te.
  Proof .
    (* consistent_conform_exp *)
    elim; rewrite /= .
    - move => v m te E s Hmem Had Hcon.
      elim : (Had _ Hmem) => ls [Hfind Hsize] .
      rewrite (eqP Hsize). 
      move: (Hcon v). rewrite /consistent1 Hfind => Henc. 
      apply /eqP. exact: (enc_bits_size Henc).
    - done .
    - done .
    - elim => /= e0 IH0 e1 IH1 m te E s /andP [Hbnd0 Hbnd1] Had Hcon;
      rewrite (IH0 _ _ _ _ Hbnd0 Had Hcon) (IH1 _ _ _ _ Hbnd1 Had Hcon) // .
    - move => c e0 IH0 e1 IH1 m te E s 
                /andP [/andP [Hbndc Hbnd0] Hbnd1] Had Hcon.
      rewrite (consistent_conform_bexp c _ _ _ _ Hbndc Had Hcon)
              (IH0 _ _ _ _ Hbnd0 Had Hcon) (IH1 _ _ _ _ Hbnd1 Had Hcon) // .
    (* consistent_conform_bexp *)
    elim; rewrite /= .
    - done .
    - done .
    - elim => e0 e1 m te E s /andP [Hbnd0 Hbnd1] Had Hcon;
      rewrite (consistent_conform_exp e0 _ _ _ _ Hbnd0 Had Hcon)
              (consistent_conform_exp e1 _ _ _ _ Hbnd1 Had Hcon) // .
    - done . 
    - move => b0 IH0 b1 IH1 m te E s /andP [Hbnd0 Hbnd1] Had Hcon;
      rewrite (IH0 _ _ _ _ Hbnd0 Had Hcon) (IH1 _ _ _ _ Hbnd1 Had Hcon) // .
    - move => b0 IH0 b1 IH1 m te E s /andP [Hbnd0 Hbnd1] Had Hcon;
      rewrite (IH0 _ _ _ _ Hbnd0 Had Hcon) (IH1 _ _ _ _ Hbnd1 Had Hcon) // .
  Qed .

  Fixpoint bound_bexps (bs : seq QFBV.bexp) vm : bool :=
    match bs with
    | [::] => true
    | b :: bs' => bound_bexp b vm && bound_bexps bs' vm
    end.

  Lemma vm_preserve_bound_bexps :
    forall es m m', vm_preserve m m' -> bound_bexps es m -> bound_bexps es m'.
  Proof.
    elim.
    - move=> m m' Hpre. done.
    - move=> e es IHes m m' Hpre /= /andP [Hbdem Hbdesm].
      move: (vm_preserve_bound_bexp Hbdem Hpre) => Hbdem'.
      move: (IHes _ _ Hpre Hbdesm) => Hbdesm'.
        by rewrite Hbdem' Hbdesm'.
  Qed.
  
End Bound .
