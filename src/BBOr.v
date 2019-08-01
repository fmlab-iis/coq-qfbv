
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon.
From ssrlib Require Import Var ZAriths Tuples Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_or ===== *)

Definition bit_blast_or1 (g: generator) (a1 a2: literal) :generator * cnf * literal :=
  if (a1 == lit_tt) || (a2 == lit_tt) then (g, [::], lit_tt)
  else if (a1 == lit_ff) then (g, [::], a2)
       else if (a2 == lit_ff) then (g, [::], a1)
            else
              let (g', r) := gen g in
              (g', [:: [:: neg_lit r; a1; a2];
                      [:: r; neg_lit a1];
                      [:: r; neg_lit a2]], r).

Definition mk_env_or1 E g a1 a2 : env * generator * cnf * literal :=
  if (a1 == lit_tt) || (a2 == lit_tt) then (E, g, [::], lit_tt)
  else if a1 == lit_ff then (E, g, [::], a2)
       else if a2 == lit_ff then (E, g, [::], a1)
            else let (g', r) := gen g in
                 let E' := env_upd E (var_of_lit r)
                                   (interp_lit E a1 || interp_lit E a2) in
                 let cs := [:: [:: neg_lit r; a1; a2]; [:: r; neg_lit a1];
                              [:: r; neg_lit a2]] in
                 (E', g', cs, r).

Fixpoint bit_blast_or  w (g: generator): w.-tuple literal -> w.-tuple literal -> generator * cnf * w.-tuple literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(g_hd, cs_hd, lrs_hd) := bit_blast_or1 g ls1_hd ls2_hd in
      let '(g_tl, cs_tl, lrs_tl) := bit_blast_or g_hd ls1_tl ls2_tl in
      (g_tl, cs_hd++cs_tl, cons_tuple lrs_hd lrs_tl)
  else
    fun _ _ =>
      (g, [::], [tuple]).

Fixpoint mk_env_or w (E : env) (g : generator) : w.-tuple literal -> w.-tuple literal -> env * generator * cnf * w.-tuple literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(E_hd, g_hd, cs_hd, lrs_hd) := mk_env_or1 E g ls1_hd ls2_hd in
      let '(E_tl, g_tl, cs_tl, lrs_tl) := mk_env_or E_hd g_hd ls1_tl ls2_tl in
      (E_tl, g_tl, cs_hd++cs_tl, cons_tuple lrs_hd lrs_tl)
  else
    fun _ _ =>
      (E, g, [::], [tuple]).

Lemma bit_blast_or1_correct:
  forall g b1 b2 br E l1 l2 g' cs lr,
    bit_blast_or1 g l1 l2 = (g', cs, lr) ->
    enc_bit E l1 b1 -> enc_bit E l2 b2 ->
    interp_cnf E (add_prelude cs) ->
    orb b1 b2 = br ->
    enc_bit E lr br.
Proof.
  move => g b1 b2 br E l1 l2 g' cs lr. rewrite /bit_blast_or1 /enc_bit.
  case Htt: ((l1 == lit_tt) || (l2 == lit_tt)).
  - case=> _ <- <- /eqP <- /eqP <- /= Htt1 <-.
    move /orP: Htt; case => /eqP -> /=; by [rewrite Htt1 | rewrite Htt1 orbT].
  - case Hff1: (l1 == lit_ff); last case Hff2: (l2 == lit_ff) .
    + case=> _ <- <- /eqP <- /eqP <- /= Htt1 <-; by [rewrite (eqP Hff1) /= Htt1].
    + case=> _ <- <- /eqP <- /eqP <- /= Htt1 <-; by [rewrite (eqP Hff2) /= Htt1 orbF ] .
    + case=> _ <- <- /eqP <- /eqP <- /andP /= . case => [Htt1 Hcs] <- .
      rewrite !interp_lit_neg_lit in Hcs . move: Hcs .
      by case: (E g); case: (interp_lit E l1); case: (interp_lit E l2) .
Qed.

Lemma bit_blast_or_correct :
  forall w g (bs1 bs2 : BITS w) E ls1 ls2 g' cs lrs,
    @bit_blast_or w g ls1 ls2 = (g', cs, lrs) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (orB bs1 bs2).
Proof.
  elim.
  - done.
  - move => n IH g. case/tupleP =>[ibs1_hd ibs1_tl]. case/tupleP =>[ibs2_hd ibs2_tl].
    move => E. case/tupleP =>[ils1_hd ils1_tl]. case/tupleP =>[ils2_hd ils2_tl].
    move => og cs. case/tupleP =>[ilrs_hd ilrs_tl].
    rewrite /bit_blast_or -/bit_blast_or (lock bit_blast_or) (lock bit_blast_or1)
            (lock interp_cnf) /= !theadE !beheadCons -!lock.
    case Hor_hd: (bit_blast_or1 g ils1_hd ils2_hd) =>[ [g_hd cs_hd] lrs_hd].
    case Hor_tl: (bit_blast_or g_hd ils1_tl ils2_tl) =>[ [g_tl cs_tl] lrs_tl].
    case => Hog <- Holrs_hd Holrs_tl => {cs}.
    move => /andP [Henc1_hd Henc1_tl] /andP [Henc2_hd Hen2_tl] Hcnf.
    rewrite add_prelude_append in Hcnf. move/andP: Hcnf => [Hcnf_hd Hcnf_tl].
    rewrite /orB. rewrite liftBinOpCons /=. rewrite /= !theadE !beheadCons.
    apply/andP; split.
    + rewrite -Holrs_hd.
      exact: (bit_blast_or1_correct Hor_hd Henc1_hd Henc2_hd Hcnf_hd).
    + apply: (IH g_hd ibs1_tl ibs2_tl E ils1_tl ils2_tl
                  g_tl cs_tl ilrs_tl _ Henc1_tl Hen2_tl Hcnf_tl).
      rewrite Hor_tl. apply: injective_projections => /=; first by reflexivity.
      apply: val_inj. exact: Holrs_tl.
Qed.

Lemma mk_env_or1_is_bit_blast_or1 :
  forall E g l1 l2 E' g' cs lr,
    mk_env_or1 E g l1 l2 = (E', g', cs, lr) ->
    bit_blast_or1 g l1 l2 = (g', cs, lr).
Proof.
  rewrite /mk_env_or1 /bit_blast_or1; intros;
    dite_hyps; dcase_hyps; subst; reflexivity .
Qed .

Lemma mk_env_or_is_bit_blast_or :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_or E g ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_or g ls1 ls2 = (g', cs, lrs).
Proof.
  elim .
  - move=> E g ls1 ls2 E' g' cs lrs /=; case=> _ <- <- <-; reflexivity .
  - move=> w iH E g.
    case /tupleP => ls1_hd ls1_tl; case /tupleP => ls2_hd ls2_tl E' g' cs; case /tupleP => lrs_hd lrs_tl .
    rewrite /= !theadE !beheadCons /= .
    case Henv : (mk_env_or1 E g ls1_hd ls2_hd) => [[[E_hd g_hd] cs_hd] lrs_hd0] .
    move : (mk_env_or1_is_bit_blast_or1 Henv) -> .
    case Henv1 : (mk_env_or E_hd g_hd ls1_tl ls2_tl) => [[[E_tl g_tl] cs_tl] lrs_tl0] .
    move : (iH _ _ _ _ _ _ _ _ Henv1) -> .
    case => [_] <- <- <- Heq .
    rewrite (tval_eq Heq); reflexivity .
Qed .

Lemma mk_env_or1_newer_gen :
  forall E g E' g' l1 l2 cs lr,
    mk_env_or1 E g l1 l2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  move => E g E' g' l1 l2 cs lr . rewrite /mk_env_or1 .
  case Htt :((l1 == lit_tt) || (l2 == lit_tt)) .
  - case => _ <- _ _; exact: Pos.leb_refl .
  - case Ht1: (l1 == lit_ff); last case Ht2: (l2 == lit_ff) .
    + case => _ <- _ _; exact: Pos.leb_refl .
    + case => _ <- _ _; exact: Pos.leb_refl .
    + case => _ <- _ _ . apply /pos_leP . rewrite Pos.add_1_r .
      apply: Pos.lt_le_incl . exact: Pos.lt_succ_diag_r .
Qed.

Lemma mk_env_or_newer_gen :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_or E g ls1 ls2 = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lrs [] _ <- _ _ . exact: Pos.leb_refl.
  - intros_tuple. dcase_hyps; subst. move=> Hls.
    move: (H _ _ _ _ _ _ _ _ H2) => Hg1g. apply: (pos_leb_trans _ Hg1g).
    apply: (mk_env_or1_newer_gen H0).
Qed.

Lemma mk_env_or1_newer_res :
  forall E g E' g' l1 l2 cs lr,
    mk_env_or1 E g l1 l2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g l1 -> newer_than_lit g l2 ->
    newer_than_lit g' lr.
Proof.
  rewrite /mk_env_or1.
  move => E g E' g' l1 l2 cs lr H Hgtt Hgl1 Hgl2.
  move: H.
  case Htt: ((l1 == lit_tt) || (l2 == lit_tt)) .
  - case => _ <- _ <- . done .
  - case Ht1 : (l1 == lit_ff); last case Ht2: (l2 == lit_ff) .
    + case => _ <- _ <- . done .
    + case => _ <- _ <- . done .
    + move => [[_ g0'] _] . case => <- . rewrite -g0' .
      exact: (newer_than_var_add_diag_r) .
Qed .

Lemma mk_env_or_newer_res :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_or E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    newer_than_lits g' lrs.
Proof.
  elim .
  - move=> E g ls1 ls2 E' g' cs lrs H _ _ _. case: H => _ <- _ <- . done .
  - intros_tuple. dcase_hyps; subst. move=> Hls .
    rewrite -(tval_eq Hls).
    case :H2 => /andP [Hgls1 Hgls0] .
    case :H3 => /andP [Hgls2 Hgls3] .
    move: (mk_env_or1_newer_gen H0) => Hgg0 .
    move: (mk_env_or1_newer_res H0 H1 Hgls1 Hgls2) => {H0} Hg0lrs .
    move: (newer_than_lit_le_newer H1 Hgg0) => {Hgls1 Hgls2} Hg0tt .
    move: (newer_than_lits_le_newer Hgls0 Hgg0)
            (newer_than_lits_le_newer Hgls3 Hgg0) =>
    {Hgls0 Hgls3} Hg0ls0 Hg0ls3 .
    move: (H _ _ _ _ _ _ _ _ H5 Hg0tt Hg0ls0 Hg0ls3) =>
    {Hg0tt Hg0ls0 Hg0ls3} Hg'ls .
    rewrite Hg'ls andbT .
    move: (mk_env_or_newer_gen H5) => {H5} Hg0g' .
    apply: (newer_than_lit_le_newer _ Hg0g') . done .
Qed .

Lemma mk_env_or1_newer_cnf :
  forall E g l1 l2 E' g' cs lr,
    mk_env_or1 E g l1 l2 = (E', g', cs, lr) ->
    newer_than_lit g l1 -> newer_than_lit g l2 ->
    newer_than_cnf g' cs.
Proof.
  intros E g l1 l2 E' g' cs lr Henv Hgl1 Hgl2 .
  move: Henv . rewrite /mk_env_or1 /= .
  case Htt: ((l1 == lit_tt) || (l2 == lit_tt)) .
  - case => _ _ <- _ . done .
  - case Ht1 : (l1 == lit_ff); last case Ht2 : (l2 == lit_ff) .
    + case => _ _ <- _ . done .
    + case => _ _ <- _ . done .
    + case => _ <- <- _ {Htt Ht1 Ht2} /= .
      move: (newer_than_lit_le_newer Hgl1 (pos_leb_add_diag_r g 1)) => Hg1l1 .
      move: (newer_than_lit_le_newer Hgl2 (pos_leb_add_diag_r g 1)) => Hg1l2 .
      rewrite !newer_than_lit_neg Hg1l1 Hg1l2 .
      rewrite /newer_than_lit /var_of_lit /= .
      rewrite (newer_than_var_add_diag_r g 1) .
      done .
Qed .

Lemma mk_env_or_newer_cnf :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_or E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lrs [] _ <- <- _ Hnew_gls1 Hnew_gls2. done.
  - intros_tuple. dcase_hyps; subst. move=> _ /=.
    move /andP: H1 => [Hgls1 Hgls0] .
    move /andP: H2 => [Hgls2 Hgls3] .
    rewrite newer_than_cnf_append .
    (* newer_than_cnf g' cs1 *)
    move: (mk_env_or1_newer_gen H0) => Hgg0 .
    move: (newer_than_lits_le_newer Hgls0 Hgg0)
            (newer_than_lits_le_newer Hgls3 Hgg0)
    => Hg0ls0 Hg0ls3 .
    rewrite (H _ _ _ _ _ _ _ _ H4 Hg0ls0 Hg0ls3) andbT
            {Hgls0 Hgls3 Hg0ls0 Hg0ls3 H} .
    (* newer_than_cnf g' cs0 *)
    move: (mk_env_or_newer_gen H4) => Hg0g' .
    move: (mk_env_or1_newer_cnf H0 Hgls1 Hgls2) => Hg0cs0 .
    exact: (newer_than_cnf_le_newer Hg0cs0 Hg0g') .
Qed .

Lemma mk_env_or1_preserve :
  forall E g l1 l2 E' g' cs lr,
    mk_env_or1 E g l1 l2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  move=> E g l1 l2 E' g' cs lr.
  rewrite /mk_env_or1.
  case Htt: ((l1 == lit_tt) || (l2 == lit_tt)) .
  - case => <- _ _ _. done.
  - case Ht1: (l1 == lit_ff); last case Ht2: (l2 == lit_ff) .
      * case => <- _ _ _; exact: env_preserve_refl .
      * case => <- _ _ _; exact: env_preserve_refl .
      * case => <- _ _ _; exact: env_upd_eq_preserve .
Qed.

Lemma mk_env_or_preserve :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_or E g ls1 ls2 = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  elim .
  - move=> E g ls1 ls2 E' g' cs lrs /=. case=> <- _ _ _. exact: env_preserve_refl.
  - intros_tuple. dcase_hyps; intros; subst. move: (H _ _ _ _ _ _ _ _ H2) => Hpre.
    move: (mk_env_or1_newer_gen H0) => Hg0g' .
    move: (env_preserve_le Hpre Hg0g') => {Hpre} HE0E'g .
    apply: (env_preserve_trans _ HE0E'g) .
    move: H0; rewrite /mk_env_or1 .
    case Htt: ((ls1 == lit_tt) || (ls2 == lit_tt)) .
    + case => <- _ _ _; exact: env_preserve_refl .
    + case Ht1: (ls1 == lit_ff); last case Ht2: (ls2 == lit_ff) .
      * case => <- _ _ _; exact: env_preserve_refl .
      * case => <- _ _ _; exact: env_preserve_refl .
      * case => <- _ _ _; exact: env_upd_eq_preserve .
Qed .

Lemma mk_env_or1_sat :
  forall E g l1 l2 E' g' cs lr,
    mk_env_or1 E g l1 l2 = (E', g', cs, lr) ->
    newer_than_lit g l1 ->
    newer_than_lit g l2 ->
    interp_cnf E' cs.
Proof.
  move=> E g l1 l2 E' g' cs lr H Hgl1 Hgl2.
  move: H.
  rewrite /mk_env_or1.
  case Htt: ((l1 == lit_tt) || (l2 == lit_tt)) .
  - case => <- _ <- _. done.
  - case Ht1: (l1 == lit_ff); last case Ht2: (l2 == lit_ff) .
      * by case => <- _ <- _.
      * by case => <- _ <- _.
      * case => <- _ <- _.
        rewrite !interp_cnf_cons /interp_clause !interp_lit_neg_lit .
        rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hgl1)).
        rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hgl2)).
        by case: (interp_lit E l1); case: (interp_lit E l2);
        rewrite /interp_lit !env_upd_eq .
Qed.

Lemma mk_env_or_sat :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_or E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  elim .
  - move=> E g ls1 ls2 E' g' cs lrs. case=> <- _ <- _ _ _ . done.
  - intros_tuple. dcase_hyps; intros; subst. rewrite !interp_cnf_append .
    move /andP: H1 => [Hgls1 Hgls0] .
    move /andP: H2 => [Hgls2 Hgls3] .
    move: (mk_env_or1_newer_gen H0) => Hgg0 .
    move: (H _ _ _ _ _ _ _ _ H4 (newer_than_lits_le_newer Hgls0 Hgg0)
             (newer_than_lits_le_newer Hgls3 Hgg0))
    => {Hgls0 Hgls3} -> .
    move: (mk_env_or_preserve H4) => HE0E'g0 .
    move: (mk_env_or1_newer_cnf H0 Hgls1 Hgls2) => Hg0cs0 .
    rewrite (env_preserve_cnf HE0E'g0 Hg0cs0) .
    move: H0; rewrite /mk_env_or1 .
    case Htt: ((ls1 == lit_tt) || (ls2 == lit_tt)) .
    + case => _ _ <- _ . done .
    + case Ht1: (ls1 == lit_ff); last case Ht2: (ls2 == lit_ff) .
      * case => _ _ <- _ . done .
      * case => _ _ <- _ . done .
      * case => <- _ <- Hr .
        rewrite !interp_cnf_cons /interp_clause !interp_lit_neg_lit .
        rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hgls1)).
        rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hgls2)).
        by case: (interp_lit E ls1); case: (interp_lit E ls2);
        rewrite /interp_lit !env_upd_eq .
Qed .
