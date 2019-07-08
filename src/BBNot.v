
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon.
From ssrlib Require Import Var ZAriths Tuples Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_not ===== *)

Definition bit_blast_not1 (g: generator) (a:literal) : generator * cnf * literal :=
  let (g', r):= gen g in
  let cs := [::
        [:: r; a]; [:: neg_lit r; neg_lit a]
      ] in (g', cs , r).

Fixpoint bit_blast_not w (g:generator) : w.-tuple literal -> generator * cnf * w.-tuple literal :=
  if w is _.+1 then
  fun ls =>
    let (ls_tl, ls_hd) := eta_expand (splitlsb ls) in
    let '(g_hd, cs_hd, lrs_hd) := bit_blast_not1 g ls_hd in
    let '(g_tl, cs_tl, lrs_tl) := bit_blast_not g_hd ls_tl in
    (g_tl, cs_hd++cs_tl, cons_tuple lrs_hd lrs_tl)
  else
    fun _ =>
      (g, [::], [tuple]).

Definition mk_env_not1 E g a : env * generator * cnf * literal :=
  let (g', r) := gen g in
  let E' := env_upd E (var_of_lit r) (~~ (interp_lit E a)) in
  let cs := [:: [:: r; a]; [:: neg_lit r; neg_lit a]] in
  (E', g', cs, r).

Fixpoint mk_env_not w (E : env) (g : generator) : w.-tuple literal -> env * generator * cnf * w.-tuple literal :=
  if w is _.+1 then
    fun ls =>
      let (ls_tl, ls_hd) := eta_expand (splitlsb ls) in
      let '(E_hd, g_hd, cs_hd, lrs_hd) := mk_env_not1 E g ls_hd in
      let '(E_tl, g_tl, cs_tl, lrs_tl) := mk_env_not E_hd g_hd ls_tl in
      (E_tl, g_tl, cs_hd++cs_tl, cons_tuple lrs_hd lrs_tl)
  else
    fun _ =>
      (E, g, [::], [tuple]).

Lemma bit_blast_not1_correct :
  forall g b br E l g' cs lr,
    bit_blast_not1 g l = (g', cs, lr) ->
    enc_bit E l b ->
    interp_cnf E (add_prelude cs) ->
    br = ~~ b ->
    enc_bit E lr br.
Proof.
  move => g b br E l g' cs lr.
  rewrite /bit_blast_not1 /enc_bit. case=> [Hg' Hcs Hlr].
  rewrite -Hlr -{}Hcs /= => {Hg' Hlr g' cs}. rewrite !interp_lit_neg_lit.
  move=> /eqP ->. case  (E g) => /=.
  - move/andP=> [Htt Hb]. move=> ->; done.
  - move/andP=> [Htt /andP [Hb _]]. move=> ->. by rewrite Hb.
Qed.

Lemma bit_blast_not_correct :
  forall w g (bs : BITS w) E ls g' cs lrs,
    @bit_blast_not w g ls = (g', cs, lrs) ->
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (invB bs).
Proof.
  elim.
  - done.
  - move => n IH g. case/tupleP=> [ibs_hd ibs_tl].
    move => E. case/tupleP => [ils_hd ils_tl].
    move => og cs. case/tupleP => [ilrs_hd ilrs_tl].
    rewrite /bit_blast_not -/bit_blast_not (lock bit_blast_not1)
            (lock interp_cnf) /= !theadE !beheadCons -2!lock.
    case Hnot_hd: (bit_blast_not1 g ils_hd) => [[g_hd cs_hd] lrs_hd].
    case Hnot_tl: (bit_blast_not g_hd ils_tl) => [[g_tl cs_tl] lrs_tl].
    case => Hog <- Holrs_hd Holrs_tl => {cs}. move=> /andP [Henc_hd Henc_tl] Hcnf.
    rewrite /invB. rewrite liftUnOpCons /=. rewrite /= !theadE !beheadCons.
    rewrite add_prelude_append in Hcnf. move/andP: Hcnf => [Hcnf_hd Hcnf_tl].
    apply/andP; split.
    + rewrite -Holrs_hd.
      exact: (bit_blast_not1_correct Hnot_hd Henc_hd Hcnf_hd ).
    + apply: (IH g_hd ibs_tl E ils_tl
                 g_tl cs_tl ilrs_tl _ Henc_tl Hcnf_tl).
      * rewrite Hnot_tl. apply: injective_projections => /=; first by reflexivity.
        apply: val_inj. exact: Holrs_tl.
Qed.

Lemma mk_env_not1_is_bit_blast_not1 :
  forall E g l E' g' cs lr,
    mk_env_not1 E g l = (E', g', cs, lr) ->
    bit_blast_not1 g l = (g', cs, lr).
Proof.
  rewrite /mk_env_not1 /bit_blast_not1; intros;
    dite_hyps; dcase_hyps; subst; reflexivity.
Qed.

Lemma mk_env_not_is_bit_blast_not :
  forall w E g (ls : w.-tuple literal) E' g' cs lrs,
    mk_env_not E g ls = (E', g', cs, lrs) ->
    bit_blast_not g ls = (g', cs, lrs).
Proof.
  elim.
  - move=> E g ls E' g' cs lrs /=. case=> _ <- <- <- //=.
  - move=> n IHn E g.
    case/tupleP=> [ls_hd ls_tl].
    move=> E' g' cs; case/tupleP=> [lrs_hd lrs_tl].
    rewrite /mk_env_not -/mk_env_not /bit_blast_not -/bit_blast_not.
    rewrite (lock mk_env_not1) (lock bit_blast_not1) /= !theadE !beheadCons -!lock.
    case Hhd : (mk_env_not1 E g ls_hd) => [[[E_hd g_hd] cs_hd] lsr_hd].
    rewrite (mk_env_not1_is_bit_blast_not1 Hhd).
    case Htl : (mk_env_not E_hd g_hd ls_tl) => [[[E_tl g_tl] cs_tl] lsr_tl].
    rewrite (IHn _ _ _ _ _ _ _ Htl).
    case=> _ <- <- <- Hlsrtl. by rewrite -(tval_eq Hlsrtl).
Qed.

Lemma mk_env_not1_newer_gen :
  forall E g l E' g' cs lr,
    mk_env_not1 E g l = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  rewrite /mk_env_not1 => E g l E' g' cs lr /=.
  case=> _ <- _ _. exact: pos_leb_add_diag_r.
Qed.

Lemma mk_env_not_newer_gen :
  forall w E g (ls : w.-tuple literal) E' g' cs lrs,
    mk_env_not E g ls = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  elim.
  - move=> E g ls E' g' cs lrs. case=> _ <- _ _. exact: Pos.leb_refl.
  - move=> n IHn E g.
    case/tupleP => [ls_hd ls_tl].
    move=> E' g' cs /tupleP [lrs_hd lrs_tl].
    rewrite /mk_env_not -/mk_env_not.
    rewrite (lock mk_env_not1) /= !theadE !beheadCons -!lock.
    case Hhd : (mk_env_not1 E g ls_hd) => [[[E_hd g_hd] cs_hd] lsr_hd].
    case Htl : (mk_env_not E_hd g_hd ls_tl) => [[[E_tl g_tl] cs_tl] lsr_tl].
    case=> _ <- _ _ _. apply: pos_leb_trans.
    - exact: (mk_env_not1_newer_gen Hhd).
    - exact: (IHn _ _ _ _ _ _ _ Htl).
Qed.

Lemma mk_env_not1_newer_res :
  forall E g l E' g' cs lr,
    mk_env_not1 E g l = (E', g', cs, lr) ->
    newer_than_lit g l ->
    newer_than_lit g' lr.
Proof.
  rewrite /mk_env_not1 => E g l E' g' cs lr /=.
  case=> _ <- _ <-. move=> _; by apply newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_not_newer_res :
  forall w E g (ls : w.-tuple literal) E' g' cs lrs,
    mk_env_not E g ls = (E', g', cs, lrs) ->
    newer_than_lits g ls ->
    newer_than_lits g' lrs.
Proof.
  elim.
  - move=> E g ls E' g' cs lrs [] _ <- _ <- //=.
  - move=> n IHn E g.
    case/tupleP => [ls_hd ls_tl].
    move=> E' g' cs /tupleP [lrs_hd lrs_tl].
    rewrite /mk_env_not -/mk_env_not.
    rewrite (lock mk_env_not1) /= !theadE !beheadCons -!lock.
    case Hhd : (mk_env_not1 E g ls_hd) => [[[E_hd g_hd] cs_hd] lsr_hd].
    case Htl : (mk_env_not E_hd g_hd ls_tl) => [[[E_tl g_tl] cs_tl] lsr_tl].
    case=> _ <- _ <- <-.
    move/andP=> [Hglh Hglt].
    move : (mk_env_not1_newer_res Hhd Hglh) => Hghlrh.
    move : (mk_env_not_newer_gen Htl) => Hghgt.
    rewrite (newer_than_lit_le_newer Hghlrh Hghgt) /=.
    move : (mk_env_not1_newer_gen Hhd) => Hggh.
    apply (IHn _ _ _ _ _ _ _ Htl).
    exact: (newer_than_lits_le_newer Hglt Hggh).
Qed.

Lemma mk_env_not1_newer_cnf :
  forall E g l E' g' cs lr,
    mk_env_not1 E g l = (E', g', cs, lr) ->
    newer_than_lit g l ->
    newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_not1 => E g l E' g' cs lr /=.
  case=> _ <- <- _. move=> Hgl /=. rewrite !newer_than_lit_neg.
  rewrite (newer_than_lit_add_diag_r (Pos g)).
  rewrite (newer_than_lit_add_diag_r (Neg g)).
  by rewrite !newer_than_lit_add_r.
Qed.

Lemma mk_env_not_newer_cnf :
  forall w E g (ls : w.-tuple literal) E' g' cs lrs,
    mk_env_not E g ls = (E', g', cs, lrs) ->
    newer_than_lits g ls ->
    newer_than_cnf g' cs.
Proof.
  elim.
  - move=> E g ls E' g' cs lrs [] _ <- <- _ //=.
  - move=> n IHn E g.
    case/tupleP => [ls_hd ls_tl].
    move=> E' g' cs /tupleP [lrs_hd lrs_tl].
    rewrite /mk_env_not -/mk_env_not.
    rewrite (lock mk_env_not1) /= !theadE !beheadCons -!lock.
    case Hhd : (mk_env_not1 E g ls_hd) => [[[E_hd g_hd] cs_hd] lsr_hd].
    case Htl : (mk_env_not E_hd g_hd ls_tl) => [[[E_tl g_tl] cs_tl] lsr_tl].
    case=> _ <- <- _ _ /=.
    move/andP=> [Hglh Hglt].
    rewrite newer_than_cnf_append.
    move : (mk_env_not1_newer_cnf Hhd Hglh) => Hghch.
    move : (mk_env_not_newer_gen Htl) => Hghgt.
    rewrite (newer_than_cnf_le_newer Hghch Hghgt) /=.
    move : (mk_env_not1_newer_gen Hhd) => Hggh.
    apply (IHn _ _ _ _ _ _ _ Htl).
    exact: (newer_than_lits_le_newer Hglt Hggh).
Qed.

Lemma mk_env_not1_preserve :
  forall E g l E' g' cs lr,
    mk_env_not1 E g l = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  rewrite /mk_env_not1 => E g l E' g' cs lr /=.
  case=> <- _ _ _. by apply env_upd_eq_preserve.
Qed.

Lemma mk_env_not_preserve :
  forall w E g (ls : w.-tuple literal) E' g' cs lrs,
    mk_env_not E g ls = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  elim.
  - move=> E g ls E' g' cs lrs [] <- _ _ _ //=.
  - move=> n IHn E g.
    case/tupleP => [ls_hd ls_tl].
    move=> E' g' cs /tupleP [lrs_hd lrs_tl].
    rewrite /mk_env_not -/mk_env_not.
    rewrite (lock mk_env_not1) /= !theadE !beheadCons -!lock.
    case Hhd : (mk_env_not1 E g ls_hd) => [[[E_hd g_hd] cs_hd] lsr_hd].
    case Htl : (mk_env_not E_hd g_hd ls_tl) => [[[E_tl g_tl] cs_tl] lsr_tl].
    case=> <- _ _ _ _ /=.
    move: (mk_env_not1_preserve Hhd) => HpEEhg.
    move: (IHn _ _ _ _ _ _ _ Htl) => HpEhEtgh.
    move: (mk_env_not1_newer_gen Hhd) => Hggh.
    move: (env_preserve_le HpEhEtgh Hggh). by apply env_preserve_trans.
Qed.

Lemma mk_env_not1_sat :
  forall E g l E' g' cs lr,
    mk_env_not1 E g l = (E', g', cs, lr) ->
    newer_than_lit g l ->
    interp_cnf E' cs.
Proof.
  rewrite /mk_env_not1 => E g l E' g' cs lr /=.
  case=> <- _ <- _ Hgl.
  move: (newer_than_lit_neq Hgl) => Hngl.
  rewrite /= !env_upd_eq !interp_lit_neg_lit.
  rewrite (interp_lit_env_upd_neq _ _ Hngl).
  by case (interp_lit E l).
Qed.

Lemma mk_env_not_sat :
  forall w E g (ls : w.-tuple literal) E' g' cs lrs,
    mk_env_not E g ls = (E', g', cs, lrs) ->
    newer_than_lits g ls ->
    interp_cnf E' cs.
Proof.
  elim.
  - move=> E g ls E' g' cs lrs [] <- _ <- _ //=.
  - move=> n IHn E g.
    case/tupleP => [ls_hd ls_tl].
    move=> E' g' cs /tupleP [lrs_hd lrs_tl].
    rewrite /mk_env_not -/mk_env_not.
    rewrite (lock mk_env_not1) /= !theadE !beheadCons -!lock.
    case Hhd : (mk_env_not1 E g ls_hd) => [[[E_hd g_hd] cs_hd] lsr_hd].
    case Htl : (mk_env_not E_hd g_hd ls_tl) => [[[E_tl g_tl] cs_tl] lsr_tl].
    case=> <- _ <- _ _ /=.
    move/andP=> [Hglh Hglt].
    rewrite interp_cnf_append.
    (* interp_cnf E_tl cs_hd *)
    move: (mk_env_not1_sat Hhd Hglh) => HiEhch.
    move: (mk_env_not_preserve Htl) => HpEhEtgh.
    move: (mk_env_not1_newer_cnf Hhd Hglh) => Hghch.
    rewrite (env_preserve_cnf HpEhEtgh Hghch) HiEhch /=.
    (* interp_cnf E_tl cs_tl *)
    move: (mk_env_not1_newer_gen Hhd) => Hggh.
    apply (IHn _ _ _ _ _ _ _ Htl).
    exact: (newer_than_lits_le_newer Hglt Hggh).
Qed.
