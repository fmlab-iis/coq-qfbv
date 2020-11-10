From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits SMTLIB.
From ssrlib Require Import Var Types SsrOrder Nats ZAriths Store FSets Tactics Seqs.
From BitBlasting Require Import Typ TypEnv State QFBV AdhereConform.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* QFBV semantics w.r.t. SMTLIB *)

Definition eunop_denote_smtlib (o : QFBV.eunop) : bits -> bits :=
  match o with
  | QFBV.Unot => SMTLIB.bvnot
  | QFBV.Uneg => SMTLIB.bvneg
  | QFBV.Uextr i j => SMTLIB.extract i j
  | QFBV.Uhigh n => high n
  | QFBV.Ulow n => low n
  | QFBV.Uzext n => SMTLIB.zero_extend n
  | QFBV.Usext n => SMTLIB.sign_extend n
  | QFBV.Urepeat n => SMTLIB.repeat n
  | QFBV.Urotl n => SMTLIB.rotate_left n
  | QFBV.Urotr n => SMTLIB.rotate_right n
  end.

Definition ebinop_denote_smtlib (o : QFBV.ebinop) : bits -> bits -> bits :=
  match o with
  | QFBV.Band => SMTLIB.bvand
  | QFBV.Bor => SMTLIB.bvor
  | QFBV.Bxor => SMTLIB.bvxor
  | QFBV.Badd => SMTLIB.bvadd
  | QFBV.Bsub => SMTLIB.bvsub
  | QFBV.Bmul => SMTLIB.bvmul
  | QFBV.Bdiv => SMTLIB.bvudiv
  | QFBV.Bmod => SMTLIB.bvurem
  | QFBV.Bsdiv => SMTLIB.bvsdiv
  | QFBV.Bsrem => SMTLIB.bvsrem
  | QFBV.Bsmod => SMTLIB.bvsmod
  | QFBV.Bshl => SMTLIB.bvshl
  | QFBV.Blshr => SMTLIB.bvlshr
  | QFBV.Bashr => SMTLIB.bvashr
  | QFBV.Bconcat => SMTLIB.concat
  | QFBV.Bcomp => SMTLIB.bvcomp
  end.

Definition bbinop_denote_smtlib (o : QFBV.bbinop) : bits -> bits -> bool :=
  match o with
  | QFBV.Beq => eq_op
  | QFBV.Bult => SMTLIB.bvult
  | QFBV.Bule => SMTLIB.bvule
  | QFBV.Bugt => SMTLIB.bvugt
  | QFBV.Buge => SMTLIB.bvuge
  | QFBV.Bslt => SMTLIB.bvslt
  | QFBV.Bsle => SMTLIB.bvsle
  | QFBV.Bsgt => SMTLIB.bvsgt
  | QFBV.Bsge => SMTLIB.bvsge
  | QFBV.Buaddo => carry_addB
  | QFBV.Busubo => borrow_subB
  | QFBV.Bumulo => Umulo
  | QFBV.Bsaddo => Saddo
  | QFBV.Bssubo => Ssubo
  | QFBV.Bsmulo => Smulo
  end.

Fixpoint smtlib_eval_exp (e : QFBV.exp) (s : SSAStore.t) : bits :=
  match e with
  | QFBV.Evar v => SSAStore.acc v s
  | QFBV.Econst n => n
  | QFBV.Eunop op e => (eunop_denote_smtlib op) (smtlib_eval_exp e s)
  | QFBV.Ebinop op e1 e2 => (ebinop_denote_smtlib op) (smtlib_eval_exp e1 s) 
                                                      (smtlib_eval_exp e2 s)
  | QFBV.Eite b e1 e2 => if smtlib_eval_bexp b s then smtlib_eval_exp e1 s 
                         else smtlib_eval_exp e2 s
  end
  with
  smtlib_eval_bexp (e : QFBV.bexp) s : bool :=
    match e with
    | QFBV.Bfalse => false
    | QFBV.Btrue => true
    | QFBV.Bbinop op e1 e2 => (bbinop_denote_smtlib op) (smtlib_eval_exp e1 s) 
                                                        (smtlib_eval_exp e2 s)
    | QFBV.Blneg e => ~~ (smtlib_eval_bexp e s)
    | QFBV.Bconj e1 e2 => (smtlib_eval_bexp e1 s) && (smtlib_eval_bexp e2 s)
    | QFBV.Bdisj e1 e2 => (smtlib_eval_bexp e1 s) || (smtlib_eval_bexp e2 s)
    end.


(* Theorems showing that two ways defining QFBV semantics
   (i.e. the one w.r.t. SMTLIB and the one in QFBV.v)
   are equivalent. *)

Lemma qfbv_exp_semantics_equivalence_var : 
  forall (t : SSAVarOrder.t) (te : SSATE.env),
    QFBV.well_formed_exp (QFBV.Evar t) te ->
    forall s : SSAStore.t,
      conform_exp (QFBV.Evar t) s te ->
      QFBV.eval_exp (QFBV.Evar t) s = smtlib_eval_exp (QFBV.Evar t) s .
Proof. reflexivity. Qed.

Lemma qfbv_exp_semantics_equivalence_const :
  forall (b : bits) (te : SSATE.env),
    QFBV.well_formed_exp (QFBV.Econst b) te ->
    forall s : SSAStore.t,
      conform_exp (QFBV.Econst b) s te ->
      QFBV.eval_exp (QFBV.Econst b) s = smtlib_eval_exp (QFBV.Econst b) s .
Proof. reflexivity. Qed.

Lemma qfbv_exp_semantics_equivalence_unop : 
  forall (op : QFBV.eunop) (e : QFBV.exp),
    (forall te : SSATE.env,
        QFBV.well_formed_exp e te ->
        forall s : SSAStore.t,
          conform_exp e s te -> QFBV.eval_exp e s = smtlib_eval_exp e s) ->
    forall te : SSATE.env,
      QFBV.well_formed_exp (QFBV.Eunop op e) te ->
      forall s : SSAStore.t,
        conform_exp (QFBV.Eunop op e) s te ->
        QFBV.eval_exp (QFBV.Eunop op e) s = smtlib_eval_exp (QFBV.Eunop op e) s .
Proof.
  move=> op e IH te /= Hwf s Hcf.
  rewrite -(IH te Hwf s Hcf). 
  case op => [ | | i j | n | n | n | n | n | n | n ] /=;
    [ rewrite smtlib_bvnot_invB |
      rewrite smtlib_bvneg_negB |
      rewrite smtlib_extract_extract |
      idtac (* Uhigh *) |
      idtac (* Ulow *) |
      rewrite smtlib_zero_extend_zext |
      rewrite smtlib_sign_extend_sext |
      rewrite smtlib_repeat_repeat |
      rewrite smtlib_rotate_left_rolB |
      rewrite smtlib_rotate_right_rorB ]; done.
Qed.

Lemma qfbv_exp_semantics_equivalence_binop : 
  forall (op : QFBV.ebinop) (e1 : QFBV.exp),
    (forall te : SSATE.env,
        QFBV.well_formed_exp e1 te ->
        forall s : SSAStore.t,
          conform_exp e1 s te -> QFBV.eval_exp e1 s = smtlib_eval_exp e1 s) ->
    forall e2 : QFBV.exp,
      (forall te : SSATE.env,
          QFBV.well_formed_exp e2 te ->
          forall s : SSAStore.t,
            conform_exp e2 s te -> QFBV.eval_exp e2 s = smtlib_eval_exp e2 s) ->
      forall te : SSATE.env,
        QFBV.well_formed_exp (QFBV.Ebinop op e1 e2) te ->
        forall s : SSAStore.t,
          conform_exp (QFBV.Ebinop op e1 e2) s te ->
          QFBV.eval_exp (QFBV.Ebinop op e1 e2) s = 
          smtlib_eval_exp (QFBV.Ebinop op e1 e2) s .
Proof.
  move=> op e1 IH1 e2 IH2 te /=. 
  move=> /andP [/andP [/andP [Hwf1 Hwf2] Hsz0] Hsz] s /andP [Hcf1 Hcf2].
  rewrite -(IH1 te Hwf1 s Hcf1) -(IH2 te Hwf2 s Hcf2).
  rewrite -(eval_conform_exp_size Hwf1 Hcf1) 
          -(eval_conform_exp_size Hwf2 Hcf2) in Hsz Hsz0.
  move: Hsz. case op => /= /eqP Hsz; 
    [ rewrite smtlib_bvand_andB |
      rewrite smtlib_bvor_orB |
      rewrite smtlib_bvxor_xorB |
      rewrite smtlib_bvadd_addB |
      rewrite smtlib_bvsub_subB |
      rewrite smtlib_bvmul_mulB |
      rewrite smtlib_bvudiv_udivB' |
      rewrite smtlib_bvurem_uremB |
      rewrite smtlib_bvsdiv_sdivB |
      rewrite smtlib_bvsrem_sremB |
      rewrite smtlib_bvsmod_smodB |
      rewrite smtlib_bvshl_shlB |
      rewrite smtlib_bvlshr_shrB |
      rewrite smtlib_bvashr_sarB |
      rewrite smtlib_concat_cat |
      rewrite smtlib_bvcomp_eqop ]; done.
Qed.

Lemma qfbv_exp_semantics_equivalence_ite : 
  forall b : QFBV.bexp,
    (forall te : SSATE.env,
        QFBV.well_formed_bexp b te ->
        forall s : SSAStore.t,
          conform_bexp b s te -> QFBV.eval_bexp b s = smtlib_eval_bexp b s) ->
    forall e1 : QFBV.exp,
      (forall te : SSATE.env,
          QFBV.well_formed_exp e1 te ->
          forall s : SSAStore.t,
            conform_exp e1 s te -> QFBV.eval_exp e1 s = smtlib_eval_exp e1 s) ->
      forall e2 : QFBV.exp,
        (forall te : SSATE.env,
            QFBV.well_formed_exp e2 te ->
            forall s : SSAStore.t,
              conform_exp e2 s te -> QFBV.eval_exp e2 s = smtlib_eval_exp e2 s) ->
        forall te : SSATE.env,
          QFBV.well_formed_exp (QFBV.Eite b e1 e2) te ->
          forall s : SSAStore.t,
            conform_exp (QFBV.Eite b e1 e2) s te ->
            QFBV.eval_exp (QFBV.Eite b e1 e2) s = 
            smtlib_eval_exp (QFBV.Eite b e1 e2) s .
Proof.
  move=> b IHb e1 IH1 e2 IH2 te /=. 
  move=> /andP [/andP [/andP [Hwfb Hwf1] Hwf2] /eqP Hsz] 
          s /andP [/andP [Hcfb Hcf1] Hcf2].
  rewrite -(IHb te Hwfb s Hcfb) -(IH1 te Hwf1 s Hcf1) -(IH2 te Hwf2 s Hcf2).
  reflexivity.
Qed.

Lemma qfbv_bexp_semantics_equivalence_false :
  forall te : SSATE.env,
    QFBV.well_formed_bexp QFBV.Bfalse te ->
    forall s : SSAStore.t,
      conform_bexp QFBV.Bfalse s te ->
      QFBV.eval_bexp QFBV.Bfalse s = smtlib_eval_bexp QFBV.Bfalse s .
Proof. reflexivity. Qed.

Lemma qfbv_bexp_semantics_equivalence_true :
  forall te : SSATE.env,
    QFBV.well_formed_bexp QFBV.Btrue te ->
    forall s : SSAStore.t,
      conform_bexp QFBV.Btrue s te ->
      QFBV.eval_bexp QFBV.Btrue s = smtlib_eval_bexp QFBV.Btrue s .
Proof. reflexivity. Qed.

Lemma qfbv_bexp_semantics_equivalence_binop :
  forall (op : QFBV.bbinop) (e1 : QFBV.exp),
    (forall te : SSATE.env,
        QFBV.well_formed_exp e1 te ->
        forall s : SSAStore.t,
          conform_exp e1 s te -> QFBV.eval_exp e1 s = smtlib_eval_exp e1 s) ->
    forall e2 : QFBV.exp,
      (forall te : SSATE.env,
          QFBV.well_formed_exp e2 te ->
          forall s : SSAStore.t,
            conform_exp e2 s te -> QFBV.eval_exp e2 s = smtlib_eval_exp e2 s) ->
      forall te : SSATE.env,
        QFBV.well_formed_bexp (QFBV.Bbinop op e1 e2) te ->
        forall s : SSAStore.t,
          conform_bexp (QFBV.Bbinop op e1 e2) s te ->
          QFBV.eval_bexp (QFBV.Bbinop op e1 e2) s = 
          smtlib_eval_bexp (QFBV.Bbinop op e1 e2) s .
Proof.
  move=> op e1 IH1 e2 IH2 te /=. 
  move=> /andP [/andP [Hwf1 Hwf2] /eqP Hsz] s /andP [Hcf1 Hcf2].
  rewrite -(IH1 te Hwf1 s Hcf1) -(IH2 te Hwf2 s Hcf2).
  rewrite -(eval_conform_exp_size Hwf1 Hcf1) 
          -(eval_conform_exp_size Hwf2 Hcf2) in Hsz.
  case op => /=;
    [ idtac (* Beq *) |
      rewrite smtlib_bvult_ltB |
      rewrite smtlib_bvule_leB |
      rewrite smtlib_bvugt_gtB |
      rewrite smtlib_bvuge_geB |
      rewrite smtlib_bvslt_sltB |
      rewrite smtlib_bvsle_sleB |
      rewrite smtlib_bvsgt_sgtB |
      rewrite smtlib_bvsge_sgeB |
      idtac (* Buaddo *) |
      idtac (* Busubo *) |
      idtac (* Bumulo *) |
      idtac (* Bsaddo *) |
      idtac (* Bssubo *) |
      idtac (* Bsmulo *) ]; done.
Qed.

Lemma qfbv_bexp_semantics_equivalence_lneg :
  forall b : QFBV.bexp,
    (forall te : SSATE.env,
        QFBV.well_formed_bexp b te ->
        forall s : SSAStore.t,
          conform_bexp b s te -> QFBV.eval_bexp b s = smtlib_eval_bexp b s) ->
    forall te : SSATE.env,
      QFBV.well_formed_bexp (QFBV.Blneg b) te ->
      forall s : SSAStore.t,
        conform_bexp (QFBV.Blneg b) s te ->
        QFBV.eval_bexp (QFBV.Blneg b) s = smtlib_eval_bexp (QFBV.Blneg b) s .
Proof.
  move=> b IH te /= Hwf s Hcf.
  rewrite -(IH te Hwf s Hcf). reflexivity.
Qed.

Lemma qfbv_bexp_semantics_equivalence_conj :
  forall b1 : QFBV.bexp,
    (forall te : SSATE.env,
        QFBV.well_formed_bexp b1 te ->
        forall s : SSAStore.t,
          conform_bexp b1 s te -> QFBV.eval_bexp b1 s = smtlib_eval_bexp b1 s) ->
    forall b2 : QFBV.bexp,
      (forall te : SSATE.env,
          QFBV.well_formed_bexp b2 te ->
          forall s : SSAStore.t,
            conform_bexp b2 s te -> QFBV.eval_bexp b2 s = smtlib_eval_bexp b2 s) ->
      forall te : SSATE.env,
        QFBV.well_formed_bexp (QFBV.Bconj b1 b2) te ->
        forall s : SSAStore.t,
          conform_bexp (QFBV.Bconj b1 b2) s te ->
          QFBV.eval_bexp (QFBV.Bconj b1 b2) s = 
          smtlib_eval_bexp (QFBV.Bconj b1 b2) s .
Proof.
  move=> b1 IH1 b2 IH2 te /=. 
  move=> /andP [Hwf1 Hwf2] s /andP [Hcf1 Hcf2].
  rewrite -(IH1 te Hwf1 s Hcf1) -(IH2 te Hwf2 s Hcf2). reflexivity.
Qed.

Lemma qfbv_bexp_semantics_equivalence_disj :
  forall b1 : QFBV.bexp,
    (forall te : SSATE.env,
        QFBV.well_formed_bexp b1 te ->
        forall s : SSAStore.t,
          conform_bexp b1 s te -> QFBV.eval_bexp b1 s = smtlib_eval_bexp b1 s) ->
    forall b2 : QFBV.bexp,
      (forall te : SSATE.env,
          QFBV.well_formed_bexp b2 te ->
          forall s : SSAStore.t,
            conform_bexp b2 s te -> QFBV.eval_bexp b2 s = smtlib_eval_bexp b2 s) ->
      forall te : SSATE.env,
        QFBV.well_formed_bexp (QFBV.Bdisj b1 b2) te ->
        forall s : SSAStore.t,
          conform_bexp (QFBV.Bdisj b1 b2) s te ->
          QFBV.eval_bexp (QFBV.Bdisj b1 b2) s = 
          smtlib_eval_bexp (QFBV.Bdisj b1 b2) s .
Proof.
  move=> b1 IH1 b2 IH2 te /=. 
  move=> /andP [Hwf1 Hwf2] s /andP [Hcf1 Hcf2].
  rewrite -(IH1 te Hwf1 s Hcf1) -(IH2 te Hwf2 s Hcf2). reflexivity.
Qed.
                                                           
Theorem qfbv_exp_semantics_equivalence : 
  forall (e : QFBV.exp) te,
    QFBV.well_formed_exp e te ->
    (forall s, AdhereConform.conform_exp e s te ->
               QFBV.eval_exp e s = smtlib_eval_exp e s) 
  with 
    qfbv_bexp_semantics_equivalence : 
      forall (b : QFBV.bexp) te,
        QFBV.well_formed_bexp b te ->
        (forall s, AdhereConform.conform_bexp b s te ->
                   QFBV.eval_bexp b s = smtlib_eval_bexp b s) .
Proof.
  (* exp *)
  set IHe := qfbv_exp_semantics_equivalence.
  set IHb := qfbv_bexp_semantics_equivalence.
  case.
  - exact: qfbv_exp_semantics_equivalence_var.
  - exact: qfbv_exp_semantics_equivalence_const.
  - move=> op e. move: op e (IHe e).
    exact: qfbv_exp_semantics_equivalence_unop.
  - move=> op e1 e2. move: op e1 (IHe e1) e2 (IHe e2). 
    exact: qfbv_exp_semantics_equivalence_binop.
  - move=> b e1 e2. move: b (IHb b) e1 (IHe e1) e2 (IHe e2).
    exact: qfbv_exp_semantics_equivalence_ite.
  (* bexp *)
  set IHe := qfbv_exp_semantics_equivalence.
  set IHb := qfbv_bexp_semantics_equivalence.
  case.
  - exact: qfbv_bexp_semantics_equivalence_false.
  - exact: qfbv_bexp_semantics_equivalence_true.
  - move=> op e1 e2. move: op e1 (IHe e1) e2 (IHe e2).
    exact: qfbv_bexp_semantics_equivalence_binop.
  - move=> b. move: b (IHb b). 
    exact: qfbv_bexp_semantics_equivalence_lneg.
  - move=> b1 b2. move: b1 (IHb b1) b2 (IHb b2).
    exact: qfbv_bexp_semantics_equivalence_conj.
  - move=> b1 b2. move: b1 (IHb b1) b2 (IHb b2).
    exact: qfbv_bexp_semantics_equivalence_disj.
Qed.
