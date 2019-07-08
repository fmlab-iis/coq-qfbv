
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon.
From ssrlib Require Import Var ZAriths Tuples Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_xor ===== *)

Definition bit_blast_xor1 (g: generator) (a1 a2: literal) : generator * cnf * literal :=
  let (g', r) := gen g in
  let cs := [:: [:: neg_lit r; a1; a2]; [:: neg_lit r; neg_lit a1; neg_lit a2];
               [:: r; neg_lit a1; a2]; [:: r; a1; neg_lit a2]] in
  (g', cs, r).

Definition mk_env_xor1 E g a1 a2 : env * generator * cnf * literal :=
  let (g', r) := gen g in
  let E' := env_upd E (var_of_lit r)
                    (xorb (interp_lit E a1) (interp_lit E a2)) in
  let cs := [:: [:: neg_lit r; a1; a2]; [:: neg_lit r; neg_lit a1; neg_lit a2];
               [:: r; neg_lit a1; a2]; [:: r; a1; neg_lit a2]] in
  (E', g', cs, r).

Fixpoint bit_blast_xor w (g: generator): w.-tuple literal -> w.-tuple literal -> generator * cnf * w.-tuple literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(g_hd, cs_hd, lrs_hd) := bit_blast_xor1 g ls1_hd ls2_hd in
      let '(g_tl, cs_tl, lrs_tl) := bit_blast_xor g_hd ls1_tl ls2_tl in
      (g_tl, cs_hd++cs_tl, cons_tuple lrs_hd lrs_tl)
  else
    fun _ _ =>
      (g, [::], [tuple]).

Fixpoint mk_env_xor w (E : env) (g : generator) : w.-tuple literal -> w.-tuple literal -> env * generator * cnf * w.-tuple literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(E_hd, g_hd, cs_hd, lrs_hd) := mk_env_xor1 E g ls1_hd ls2_hd in
      let '(E_tl, g_tl, cs_tl, lrs_tl) := mk_env_xor E_hd g_hd ls1_tl ls2_tl in
      (E_tl, g_tl, cs_hd++cs_tl, cons_tuple lrs_hd lrs_tl)
  else
    fun _ _ =>
      (E, g, [::], [tuple]).

Lemma bit_blast_xor1_correct :
  forall g b1 b2 br E l1 l2 g' cs lr,
    bit_blast_xor1 g l1 l2 = (g', cs, lr) ->
    enc_bit E l1 b1 -> enc_bit E l2 b2 ->
    interp_cnf E (add_prelude cs) ->
    xorb b1 b2 = br ->
    enc_bit E lr br.
Proof.
  move => g b1 b2 br E l1 l2 g' cs lr. rewrite /bit_blast_xor1 /enc_bit.
  case => _ <- <-. move=> /eqP <- /eqP <- /andP /= [Htt Hcs] <-.
  rewrite !interp_lit_neg_lit in Hcs. move: Hcs.
  by case: (E g); case: (interp_lit E l1); case: (interp_lit E l2).
Qed.

Lemma bit_blast_xor_correct :
  forall w g (bs1 bs2 : BITS w) E ls1 ls2 g' cs lrs,
    @bit_blast_xor w g ls1 ls2 = (g', cs, lrs) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (xorB bs1 bs2).
Proof.
  elim.
  - done.
  - move => n IH g. case/tupleP =>[ibs1_hd ibs1_tl]. case/tupleP =>[ibs2_hd ibs2_tl].
    move => E. case/tupleP =>[ils1_hd ils1_tl]. case/tupleP =>[ils2_hd ils2_tl].
    move => og cs. case/tupleP =>[ilrs1_hd ilrs1_tl].
    rewrite /bit_blast_xor -/bit_blast_xor (lock bit_blast_xor)
            (lock bit_blast_xor1) (lock interp_cnf)  /= !theadE !beheadCons -!lock.
    case Hxor_hd: (bit_blast_xor1 g ils1_hd ils2_hd) =>[[g_hd cs_hd] lrs_hd].
    case Hxor_tl: (bit_blast_xor g_hd ils1_tl ils2_tl) =>[[g_tl cs_tl] lrs_tl].
    case => Hog <- Holrs_hd Holrs_tl => {cs}.
    move => /andP [Henc1_hd Henc1_tl] /andP [Henc2_hd Hen2_tl] Hcnf.
    rewrite add_prelude_append in Hcnf. move/andP: Hcnf => [Hcnf_hd Hcnf_tl].
    rewrite /xorB. rewrite liftBinOpCons /=. rewrite /= !theadE !beheadCons.
    apply/andP; split.
    + rewrite -Holrs_hd.
      exact: (bit_blast_xor1_correct Hxor_hd Henc1_hd Henc2_hd Hcnf_hd).
    + apply: (IH g_hd ibs1_tl ibs2_tl E ils1_tl ils2_tl
                 g_tl cs_tl ilrs1_tl _ Henc1_tl Hen2_tl Hcnf_tl).
      rewrite Hxor_tl. apply: injective_projections => /=; first by reflexivity.
      apply: val_inj. exact: Holrs_tl.
Qed.

Lemma mk_env_xor1_is_bit_blast_xor1 :
  forall E g l1 l2 E' g' cs lr,
    mk_env_xor1 E g l1 l2 = (E', g', cs, lr) ->
    bit_blast_xor1 g l1 l2 = (g', cs, lr).
Proof.
  rewrite /mk_env_xor1 /bit_blast_xor1; intros;
    dite_hyps; dcase_hyps; subst; reflexivity.
Qed.

Lemma mk_env_xor_is_bit_blast_xor :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_xor E g ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_xor g ls1 ls2 = (g', cs, lrs).
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lrs /=. case=> _ <- <- <- //=.
  - move=> n IHn E g.
    case/tupleP=> [ls1_hd ls1_tl]; case/tupleP=> [ls2_hd ls2_tl].
    move=> E' g' cs; case/tupleP=> [lrs_hd lrs_tl].
    rewrite /mk_env_xor -/mk_env_xor /bit_blast_xor -/bit_blast_xor.
    rewrite (lock mk_env_xor1) (lock bit_blast_xor1) /= !theadE !beheadCons -!lock.
    case Hhd : (mk_env_xor1 E g ls1_hd ls2_hd) => [[[E_hd g_hd] cs_hd] lsr_hd].
    rewrite (mk_env_xor1_is_bit_blast_xor1 Hhd).
    case Htl : (mk_env_xor E_hd g_hd ls1_tl ls2_tl) => [[[E_tl g_tl] cs_tl] lsr_tl].
    rewrite (IHn _ _ _ _ _ _ _ _ Htl).
    case=> _ <- <- <- Hlsrtl. by rewrite -(tval_eq Hlsrtl).
Qed.

Lemma mk_env_xor1_newer_gen :
  forall E g l1 l2 E' g' cs lr,
    mk_env_xor1 E g l1 l2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  rewrite /mk_env_xor1 => E g l1 l2 E' g' cs lr /=.
  case=> _ <- _ _. exact: pos_leb_add_diag_r.
Qed.

Lemma mk_env_xor_newer_gen :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_xor E g ls1 ls2 = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lrs. case=> _ <- _ _. exact: Pos.leb_refl.
  - move=> n IHn E g.
    case/tupleP => [ls1_hd ls1_tl]; case/tupleP => [ls2_hd ls2_tl].
    move=> E' g' cs /tupleP [lrs_hd lrs_tl].
    rewrite /mk_env_xor -/mk_env_xor.
    rewrite (lock mk_env_xor1) /= !theadE !beheadCons -!lock.
    case Hhd : (mk_env_xor1 E g ls1_hd ls2_hd) => [[[E_hd g_hd] cs_hd] lsr_hd].
    case Htl : (mk_env_xor E_hd g_hd ls1_tl ls2_tl) => [[[E_tl g_tl] cs_tl] lsr_tl].
    case=> _ <- _ _ _. apply: pos_leb_trans.
    - exact: (mk_env_xor1_newer_gen Hhd).
    - exact: (IHn _ _ _ _ _ _ _ _ Htl).
Qed.

Lemma mk_env_xor1_newer_res :
  forall E g l1 l2 E' g' cs lr,
    mk_env_xor1 E g l1 l2 = (E', g', cs, lr) ->
    newer_than_lit g l1 ->
    newer_than_lit g l2 ->
    newer_than_lit g' lr.
Proof.
  rewrite /mk_env_xor1 => E g l1 l2 E' g' cs lr /=.
  case=> _ <- _ <-. move=> _ _; by apply newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_xor_newer_res :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_xor E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_lits g' lrs.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lrs [] _ <- _ <- //=.
  - move=> n IHn E g.
    case/tupleP => [ls1_hd ls1_tl]; case/tupleP => [ls2_hd ls2_tl].
    move=> E' g' cs /tupleP [lrs_hd lrs_tl].
    rewrite /mk_env_xor -/mk_env_xor.
    rewrite (lock mk_env_xor1) /= !theadE !beheadCons -!lock.
    case Hhd : (mk_env_xor1 E g ls1_hd ls2_hd) => [[[E_hd g_hd] cs_hd] lsr_hd].
    case Htl : (mk_env_xor E_hd g_hd ls1_tl ls2_tl) => [[[E_tl g_tl] cs_tl] lsr_tl].
    case=> _ <- _ <- <-.
    move/andP=> [Hgl1h Hgl1t] /andP [Hgl2h Hgl2t].
    move : (mk_env_xor1_newer_res Hhd Hgl1h Hgl2h) => Hghlrh.
    move : (mk_env_xor_newer_gen Htl) => Hghgt.
    rewrite (newer_than_lit_le_newer Hghlrh Hghgt) /=.
    move : (mk_env_xor1_newer_gen Hhd) => Hggh.
    apply (IHn _ _ _ _ _ _ _ _ Htl).
    + exact: (newer_than_lits_le_newer Hgl1t Hggh).
    + exact: (newer_than_lits_le_newer Hgl2t Hggh).
Qed.

Lemma mk_env_xor1_newer_cnf :
  forall E g l1 l2 E' g' cs lr,
    mk_env_xor1 E g l1 l2 = (E', g', cs, lr) ->
    newer_than_lit g l1 -> newer_than_lit g l2 ->
    newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_xor1 => E g l1 l2 E' g' cs lr /=.
  case=> _ <- <- _. move=> Hgl1 Hgl2 /=. rewrite !newer_than_lit_neg.
  rewrite (newer_than_lit_add_diag_r (Pos g)).
  rewrite (newer_than_lit_add_diag_r (Neg g)).
  by rewrite !newer_than_lit_add_r.
Qed.

Lemma mk_env_xor_newer_cnf :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_xor E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lrs [] _ <- <- _ //=.
  - move=> n IHn E g.
    case/tupleP => [ls1_hd ls1_tl]; case/tupleP => [ls2_hd ls2_tl].
    move=> E' g' cs /tupleP [lrs_hd lrs_tl].
    rewrite /mk_env_xor -/mk_env_xor.
    rewrite (lock mk_env_xor1) /= !theadE !beheadCons -!lock.
    case Hhd : (mk_env_xor1 E g ls1_hd ls2_hd) => [[[E_hd g_hd] cs_hd] lsr_hd].
    case Htl : (mk_env_xor E_hd g_hd ls1_tl ls2_tl) => [[[E_tl g_tl] cs_tl] lsr_tl].
    case=> _ <- <- _ _ /=.
    move/andP=> [Hgl1h Hgl1t] /andP [Hgl2h Hgl2t].
    rewrite newer_than_cnf_append.
    move : (mk_env_xor1_newer_cnf Hhd Hgl1h Hgl2h) => Hghch.
    move : (mk_env_xor_newer_gen Htl) => Hghgt.
    rewrite (newer_than_cnf_le_newer Hghch Hghgt) /=.
    move : (mk_env_xor1_newer_gen Hhd) => Hggh.
    apply (IHn _ _ _ _ _ _ _ _ Htl).
    + exact: (newer_than_lits_le_newer Hgl1t Hggh).
    + exact: (newer_than_lits_le_newer Hgl2t Hggh).
Qed.


Lemma mk_env_xor1_preserve :
  forall E g l1 l2 E' g' cs lr,
    mk_env_xor1 E g l1 l2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  rewrite /mk_env_xor1 => E g l1 l2 E' g' cs lr /=.
  case=> <- _ _ _. by apply env_upd_eq_preserve.
Qed.

Lemma mk_env_xor_preserve :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_xor E g ls1 ls2 = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lrs [] <- _ _ _ //=.
  - move=> n IHn E g.
    case/tupleP => [ls1_hd ls1_tl]; case/tupleP => [ls2_hd ls2_tl].
    move=> E' g' cs /tupleP [lrs_hd lrs_tl].
    rewrite /mk_env_xor -/mk_env_xor.
    rewrite (lock mk_env_xor1) /= !theadE !beheadCons -!lock.
    case Hhd : (mk_env_xor1 E g ls1_hd ls2_hd) => [[[E_hd g_hd] cs_hd] lsr_hd].
    case Htl : (mk_env_xor E_hd g_hd ls1_tl ls2_tl) => [[[E_tl g_tl] cs_tl] lsr_tl].
    case=> <- _ _ _ _ /=.
    move: (mk_env_xor1_preserve Hhd) => HpEEhg.
    move: (IHn _ _ _ _ _ _ _ _ Htl) => HpEhEtgh.
    move: (mk_env_xor1_newer_gen Hhd) => Hggh.
    move: (env_preserve_le HpEhEtgh Hggh). by apply env_preserve_trans.
Qed.

Lemma mk_env_xor1_sat :
  forall E g l1 l2 E' g' cs lr,
    mk_env_xor1 E g l1 l2 = (E', g', cs, lr) ->
    newer_than_lit g l1 -> newer_than_lit g l2 ->
    interp_cnf E' cs.
Proof.
  rewrite /mk_env_xor1 => E g l1 l2 E' g' cs lr /=.
  case=> <- _ <- _ Hgl1 Hgl2.
  move: (newer_than_lit_neq Hgl1) (newer_than_lit_neq Hgl2) => Hngl1 Hngl2.
  rewrite /= !env_upd_eq !interp_lit_neg_lit.
  rewrite (interp_lit_env_upd_neq _ _ Hngl1).
  rewrite (interp_lit_env_upd_neq _ _ Hngl2).
  by case (interp_lit E l1); case (interp_lit E l2).
Qed.

Lemma mk_env_xor_sat :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_xor E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lrs [] <- _ <- _ //=.
  - move=> n IHn E g.
    case/tupleP => [ls1_hd ls1_tl]; case/tupleP => [ls2_hd ls2_tl].
    move=> E' g' cs /tupleP [lrs_hd lrs_tl].
    rewrite /mk_env_xor -/mk_env_xor.
    rewrite (lock mk_env_xor1) /= !theadE !beheadCons -!lock.
    case Hhd : (mk_env_xor1 E g ls1_hd ls2_hd) => [[[E_hd g_hd] cs_hd] lsr_hd].
    case Htl : (mk_env_xor E_hd g_hd ls1_tl ls2_tl) => [[[E_tl g_tl] cs_tl] lsr_tl].
    case=> <- _ <- _ _ /=.
    move/andP=> [Hgl1h Hgl1t] /andP [Hgl2h Hgl2t].
    rewrite interp_cnf_append.
    (* interp_cnf E_tl cs_hd *)
    move: (mk_env_xor1_sat Hhd Hgl1h Hgl2h) => HiEhch.
    move: (mk_env_xor_preserve Htl) => HpEhEtgh.
    move: (mk_env_xor1_newer_cnf Hhd Hgl1h Hgl2h) => Hghch.
    rewrite (env_preserve_cnf HpEhEtgh Hghch) HiEhch /=.
    (* interp_cnf E_tl cs_tl *)
    move: (mk_env_xor1_newer_gen Hhd) => Hggh.
    apply (IHn _ _ _ _ _ _ _ _ Htl).
    + exact: (newer_than_lits_le_newer Hgl1t Hggh).
    + exact: (newer_than_lits_le_newer Hgl2t Hggh).
Qed.