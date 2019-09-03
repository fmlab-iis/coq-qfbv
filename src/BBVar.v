
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNFSimple BBCommon.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_var ===== *)

Fixpoint bit_blast_var' (g : generator) w : generator * w.-tuple literal :=
  match w with
  | O => (g, [tuple])
  | S n => let (g', hd) := gen g in
           let (g'', tl) := bit_blast_var' g' n in
           (g'', cons_tuple hd tl)
  end.

Fixpoint mk_env_var' w E g : BITS w -> env * generator * w.-tuple literal :=
  if w is _.+1 then
    fun bv =>
      let (bv_tl, bv_hd) := eta_expand (splitlsb bv) in
      let (g', hd) := gen g in
      let E' := env_upd E (var_of_lit hd) bv_hd in
      let '(E'', g'', tl) := mk_env_var' E' g' bv_tl in
      (E'', g'', cons_tuple hd tl)
  else
    fun _ =>
      (E, g, [tuple]).

Definition bit_blast_var g (v : var) : generator * cnf * wordsize.-tuple literal :=
  let (g', vs) := bit_blast_var' g wordsize in
  (g', [::], vs).

Definition mk_env_var E g (bv : BITS wordsize) (v : var) : env * generator * cnf * wordsize.-tuple literal :=
  let '(E', g', vs) := mk_env_var' E g bv in
  (E', g', [::], vs).

Lemma bit_blast_var_cnf_empty :
  forall g v g' cs lrs,
    bit_blast_var g v = (g', cs, lrs) -> cs = [::].
Proof.
  move=> g v g' cs lrs. rewrite /bit_blast_var. dcase (bit_blast_var' g wordsize).
  move=> [g_v lrs_v] Hbb. case=> _ <- _. reflexivity.
Qed.

Lemma mk_env_var'_is_bit_blast_var' :
  forall w E g (bs : BITS w) E' g' lrs,
    mk_env_var' E g bs = (E', g', lrs) ->
    bit_blast_var' g w = (g', lrs).
Proof.
  elim.
  - move=> iE ig ibs oE og olrs /=. case => _ <- <-. reflexivity.
  - move=> w IH iE ig. case/tupleP => ibs_hd ibs_tl oE og olrs /=.
    rewrite theadE beheadCons.
    case Henv: (mk_env_var' (env_upd iE ig ibs_hd) (ig + 1)%positive ibs_tl) =>
    [[E_env g_env] lrs_env].
    case => _ <- <-. rewrite (IH _ _ _ _ _ _ Henv). reflexivity.
Qed.

Lemma mk_env_var_is_bit_blast_var :
  forall E g (bs : BITS wordsize) v E' g' cs lrs,
    mk_env_var E g bs v = (E', g', cs, lrs) ->
    bit_blast_var g v = (g', cs, lrs).
Proof.
  rewrite /mk_env_var /bit_blast_var; intros; dcase_hyps; subst.
  rewrite (mk_env_var'_is_bit_blast_var' H); reflexivity.
Qed.

Lemma mk_env_var_sat :
  forall E g (bs : BITS wordsize) v E' g' cs lrs,
    mk_env_var E g bs v = (E', g', cs, lrs) ->
    interp_cnf E' cs.
Proof.
  move=> E g bs v E' g' cs lrs. rewrite /mk_env_var.
  case H: (mk_env_var' E g bs) => [[oE og] olrs].
  case=> <- _ <- _. done.
Qed.

Lemma mk_env_var'_preserve :
  forall w E g (bs : BITS w) E' g' lrs,
    mk_env_var' E g bs = (E', g', lrs) ->
    env_preserve E E' g.
Proof.
  elim.
  - move=> E g bs E' g' lrs. case=> <- _ _. exact: env_preserve_refl.
  - move=> w IH E g. case/tupleP=> [bs_hd bs_tl]. move=> E' g'.
    case/tupleP=> [lrs_hd lrs_tl]. rewrite /mk_env_var' -/mk_env_var'.
    rewrite /gen /= !theadE !beheadCons.
    case H: (mk_env_var' (env_upd E g bs_hd) (g + 1)%positive bs_tl) =>
    [[oE og] ocs]. case=> <- _ Hhd Htl. move: (IH _ _ _ _ _ _ H) => Hpre.
    exact: (env_preserve_env_upd_succ Hpre).
Qed.

Lemma mk_env_var_preserve :
  forall E g (bs : BITS wordsize) v E' g' cs lrs,
    mk_env_var E g bs v = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> E g bs v E' g' cs lrs. rewrite /mk_env_var.
  case H: (mk_env_var' E g bs) => [[oE og] olrs].
  case=> <- _ _ _. exact: (mk_env_var'_preserve H).
Qed.

Lemma mk_env_var'_newer_gen :
  forall w E g (bs : BITS w) E' g' lrs,
    mk_env_var' E g bs = (E', g', lrs) ->
    (g <=? g')%positive.
Proof.
  elim.
  - move=> E g bs E' g' lrs /=. case=> _ <- _. exact: Pos.leb_refl.
  - move=> w IH E g. case/tupleP=> [bs_hd bs_tl]. move=> E' g'.
    case/tupleP=> [lrs_hd lrs_tl]. rewrite /= !theadE !beheadCons.
    case Henv: (mk_env_var' (env_upd E g bs_hd) (g + 1)%positive bs_tl)
    => [[E'' g''] tl]. case=> _ <- _ _. move: (IH _ _ _ _ _ _ Henv) => H.
    apply: (pos_leb_trans _ H). exact: pos_leb_add_diag_r.
Qed.

Lemma mk_env_var_newer_gen :
  forall E g (bs : BITS wordsize) v E' g' cs lrs,
    mk_env_var E g bs v = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> E g bs v E' g' cs lrs. rewrite /mk_env_var.
  case H: (mk_env_var' E g bs) => [[oE og] olrs]. case=> _ <- _ _.
  exact: (mk_env_var'_newer_gen H).
Qed.

Lemma mk_env_var'_newer_res :
  forall w E g (bs : BITS w) E' g' lrs,
    mk_env_var' E g bs = (E', g', lrs) ->
    newer_than_lits g' lrs.
Proof.
  elim.
  - move=> E g bs E' g' lrs /=. case=> _ <- <-. done.
  - move=> w IH E g. case/tupleP=> [bs_hd bs_tl]. move=> E' g'.
    case/tupleP=> [lrs_hd lrs_tl]. rewrite /= !theadE !beheadCons.
    case Henv: (mk_env_var' (env_upd E g bs_hd) (g + 1)%positive bs_tl)
    => [[E'' g''] tl]. case=> _ <- <- <-. rewrite (IH _ _ _ _ _ _ Henv) andbT.
    rewrite /newer_than_lit /newer_than_var /=.
    move: (mk_env_var'_newer_gen Henv) => H. apply: (pos_ltb_leb_trans _ H).
    exact: pos_ltb_add_diag_r.
Qed.

Lemma mk_env_var_newer_res :
  forall E g (bs : BITS wordsize) v E' g' cs lrs,
    mk_env_var E g bs v = (E', g', cs, lrs) ->
    newer_than_lits g' lrs.
Proof.
  move=> E g bs v E' g' cs lrs. rewrite /mk_env_var.
  case H: (mk_env_var' E g bs) => [[oE og] olrs]. case=> _ <- _ <-.
  exact: (mk_env_var'_newer_res H).
Qed.

Lemma mk_env_var_newer_cnf :
  forall E g (bs : BITS wordsize) v E' g' cs lrs,
    mk_env_var E g bs v = (E', g', cs, lrs) ->
    newer_than_cnf g' cs.
Proof.
  move=> E g bs v E' g' cs lrs /=. rewrite /mk_env_var.
  case Henv: (mk_env_var' E g bs)=> [[Ev gv] lrsv]. case=> _ <- <- _. done.
Qed.

Lemma mk_env_var'_enc :
  forall w E g (bs : BITS w) E' g' lrs,
    mk_env_var' E g bs = (E', g', lrs) ->
    enc_bits E' lrs bs.
Proof.
  elim.
  - done.
  - move=> w IH E g. case/tupleP=> [bs_hd bs_tl]. move=> E' g'.
    case/tupleP=> [ls_hd ls_tl]. rewrite /= !theadE !beheadCons.
    case Henv: (mk_env_var' (env_upd E g bs_hd) (g + 1)%positive bs_tl)
    => [[E'' g''] tl]. case=> <- _ <- Htl. move: (IH _ _ _ _ _ _ Henv) => Henc_tl.
    rewrite (enc_bits_tval_eq Htl Henc_tl) andbT.
    move: (mk_env_var'_preserve Henv) => Hpre. rewrite /enc_bit /=.
    rewrite (Hpre g (pos_ltb_add_diag_r g 1)). rewrite env_upd_eq. exact: eqxx.
Qed.

Lemma mk_env_var_enc :
  forall E g (bs : BITS wordsize) v E' g' cs lrs,
    mk_env_var E g bs v = (E', g', cs, lrs) ->
    enc_bits E' lrs bs.
Proof.
  move=> E g bs v E' g' cs lrs. rewrite /mk_env_var.
  case Henv: (mk_env_var' E g bs) => [[E_v g_v] lrs_v].
  case=> <- _ _ <-. exact: (mk_env_var'_enc Henv).
Qed.
