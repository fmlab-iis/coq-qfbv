
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From BitBlasting Require Import QFBVSimple CNF BBCommon.
From ssrlib Require Import Var ZAriths Bools Tuples Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_eq ===== *)

Fixpoint bit_blast_eq_eq w r : w.-tuple literal -> w.-tuple literal -> cnf :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let cs_hd := List.map (fun cs => neg_lit r::cs) (cnf_lit_eq ls1_hd ls2_hd) in
      let cs_tl := bit_blast_eq_eq r ls1_tl ls2_tl in
      cs_hd++cs_tl
  else
    fun _ _ =>
      [::].

Definition bit_blast_eq_choice w r (auxs : w.-tuple literal) : cnf :=
  [:: r::auxs].

Fixpoint bit_blast_eq_neq w g : w.-tuple literal -> w.-tuple literal -> generator * cnf * w.-tuple literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (g_hd, auxs_hd) := gen g in
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let cs_hd := [:: [:: neg_lit auxs_hd; ls1_hd; ls2_hd];
                      [:: neg_lit auxs_hd; neg_lit ls1_hd; neg_lit ls2_hd];
                      [:: auxs_hd; neg_lit ls1_hd; ls2_hd];
                      [:: auxs_hd; ls1_hd; neg_lit ls2_hd] ] in
      let '(g_tl, cs_tl, auxs_tl) := bit_blast_eq_neq g_hd ls1_tl ls2_tl in
      (g_tl, cs_hd++cs_tl, cons_tuple auxs_hd auxs_tl)
  else
    fun _ _ =>
      (g, [::], [tuple]).

Fixpoint mk_env_eq_neq w E g : w.-tuple literal -> w.-tuple literal -> env * generator * cnf * w.-tuple literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (g_hd, auxs_hd) := gen g in
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let E' := env_upd E (var_of_lit auxs_hd)
                        (xorb (interp_lit E ls1_hd) (interp_lit E ls2_hd)) in
      let cs_hd := [:: [:: neg_lit auxs_hd; ls1_hd; ls2_hd];
                      [:: neg_lit auxs_hd; neg_lit ls1_hd; neg_lit ls2_hd];
                      [:: auxs_hd; neg_lit ls1_hd; ls2_hd];
                      [:: auxs_hd; ls1_hd; neg_lit ls2_hd] ] in
      let '(E_tl, g_tl, cs_tl, auxs_tl) := mk_env_eq_neq E' g_hd ls1_tl ls2_tl in
      (E_tl, g_tl, cs_hd++cs_tl, cons_tuple auxs_hd auxs_tl)
  else
    fun _ _ =>
      (E, g, [::], [tuple]).

Definition bit_blast_eq w (g : generator) (ls1 ls2 : w.-tuple literal) : generator * cnf * literal :=
  let (g_r, r) := gen g in
  let '(g_aux, cs_neq, auxs) := bit_blast_eq_neq g_r ls1 ls2 in
  let cs_aux := bit_blast_eq_choice r auxs in
  let cs_eq := bit_blast_eq_eq r ls1 ls2 in
  (g_aux, cs_neq++cs_aux++cs_eq, r).

Definition mk_env_eq w E g (ls1 ls2 : w.-tuple literal) : env * generator * cnf * literal :=
  let (g_r, r) := gen g in
  let E' := env_upd E (var_of_lit r) (interp_lits E ls1 == interp_lits E ls2) in
  let '(E_aux, g_aux, cs_neq, auxs) := mk_env_eq_neq E' g_r ls1 ls2 in
  let cs_aux := bit_blast_eq_choice r auxs in
  let cs_eq := bit_blast_eq_eq r ls1 ls2 in
  (E_aux, g_aux, cs_neq++cs_aux++cs_eq, r).

Lemma bit_blast_eq_eq_correct :
  forall w (bs1 bs2 : BITS w) E ls1 ls2 lr,
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude (bit_blast_eq_eq lr ls1 ls2)) ->
    interp_lit E lr ->
    bs1 = bs2.
Proof.
  elim.
  - move=> /= bs1 bs2 E ls1 ls2 lr Henc1 Henc2 Hcnf Hr. exact: trivialBits.
  - move=> w IH. case/tupleP=> [ibs1_hd ibs1_tl]. case/tupleP=> [ibs2_hd ibs2_tl].
    move=> E. case/tupleP=> [ils1_hd ils1_tl]. case/tupleP=> [ils2_hd ils2_tl].
    move=> ilr. rewrite (lock interp_cnf) /= !beheadCons !theadCons -lock.
    move=> /andP [Henc1hd Henc1tl] /andP [Henc2hd Henc2tl]. move=> Hcnf Hilr.
    rewrite add_prelude_cons in Hcnf. move/andP: Hcnf => [Hcnf_hd1 Hcnf_tl].
    rewrite add_prelude_cons in Hcnf_tl. move/andP: Hcnf_tl => [Hcnf_hd2 Hcnf_tl].
    have Heqhd: ibs1_hd = ibs2_hd.
    {
      rewrite /add_prelude /= in Hcnf_hd1 Hcnf_hd2. split_andb.
      rewrite !interp_lit_neg_lit in H0 H2. rewrite Hilr /= in H0 H2.
      move: (expand_eq (interp_lit E ils1_hd) (interp_lit E ils2_hd)).
      rewrite H0 H2 /= => /eqP Heq. exact: (enc_bit_eq_bit Heq Henc1hd Henc2hd).
    }
    move: (IH _ _ _ _ _ _ Henc1tl Henc2tl Hcnf_tl Hilr) => Heqtl.
    rewrite Heqhd Heqtl. reflexivity.
Qed.

Lemma bit_blast_eq_neq_correct :
  forall w g (bs1 bs2 : BITS w) E g' ls1 ls2 cs lauxs,
    bit_blast_eq_neq g ls1 ls2 = (g', cs, lauxs) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    (exists laux : literal, laux \in lauxs /\ interp_lit E laux) ->
    bs1 <> bs2.
Proof.
  elim.
  - move=> /= _ bs1 bs2 E _ _ _ _ lr _ _ _ _ [aux [Hin _]] Hbs.
    rewrite tuple0 in_nil in Hin. apply: not_false_is_true. exact: Hin.
  - move=> w IH ig. case/tupleP=> [ibs1_hd ibs1_tl]. case/tupleP=> [ibs2_hd ibs2_tl].
    move=> E og. case/tupleP=> [ils1_hd ils1_tl]. case/tupleP=> [ils2_hd ils2_tl].
    move=> cs. case/tupleP=> [ilauxs_hd ilauxs_tl].
    rewrite (lock interp_cnf) /= !beheadCons !theadCons -lock.
    case Hblast: (bit_blast_eq_neq (ig+1)%positive ils1_tl ils2_tl) =>
    [[g_tl cs_tl] lauxs_tl]. move=> [] Hog Hcs Haux_hd Haux_tl.
    move=> /andP [Henc1hd Henc1tl] /andP [Henc2hd Henc2tl].
    move=> Hcnf [laux [Hin Haux]]. rewrite in_cons in Hin. case/orP: Hin.
    + move=> /eqP Hin. rewrite -Hcs in Hcnf. rewrite -/(neg_lit (Pos ig)) in Hcnf.
      rewrite Haux_hd -Hin in Hcnf. rewrite /add_prelude /= in Hcnf.
      rewrite !interp_lit_neg_lit in Hcnf. rewrite Haux /= in Hcnf. split_andb.
      move=> Heq. injection Heq => Heqtl Heqhd. move: H0 H1.
      move: (enc_bit_eq_lit Heqhd Henc1hd Henc2hd) => ->.
      by case: (interp_lit E ils2_hd).
    + move=> Hin.
      have Hexists: (exists laux : literal,
                        laux \in lauxs_tl /\ interp_lit E laux).
      {
        exists laux. split; last by exact: Haux. move: (val_inj Haux_tl) => ->.
        exact: Hin.
      }
      have Hcnftl: interp_cnf E (add_prelude cs_tl).
      {
        rewrite -Hcs in Hcnf. rewrite add_prelude_cons in Hcnf.
        move/andP: Hcnf => [Hcnf1 Hcnf]. rewrite add_prelude_cons in Hcnf.
        move/andP: Hcnf => [Hcnf2 Hcnf]. rewrite add_prelude_cons in Hcnf.
        move/andP: Hcnf => [Hcnf3 Hcnf]. rewrite add_prelude_cons in Hcnf.
        move/andP: Hcnf => [Hcnf4 Hcnf]. exact: Hcnf.
      }
      move: (IH _ _ _ _ _ _ _ _ _ Hblast Henc1tl Henc2tl Hcnftl Hexists) => Hne Heq.
      apply: Hne. injection Heq => Heqtl Heqhd. apply: val_inj. exact: Heqtl.
Qed.

Lemma bit_blast_eq_choice_correct :
  forall w E r (auxs : w.-tuple literal),
    interp_cnf E (add_prelude (bit_blast_eq_choice r auxs)) ->
    interp_lit E r \/ (exists aux : literal,
                              aux \in auxs /\ interp_lit E aux).
Proof.
  move=> w E r auxs. rewrite /bit_blast_eq_choice /add_prelude.
  rewrite interp_cnf_cons /= -/(interp_clause E (r::auxs)).
  rewrite interp_clause_cons. move/andP=> [_ H].
  case/orP: H => H.
  - by left.
  - right. exact: (interp_clause_in H).
Qed.

Lemma bit_blast_eq_correct :
  forall w g (bs1 bs2 : BITS w) E g' ls1 ls2 cs lr,
    bit_blast_eq g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (bs1 == bs2).
Proof.
  move=> w ig ibs1 ibs2 E og ils1 ils2 cs olr. rewrite /bit_blast_eq.
  rewrite /gen. case Hneq: (bit_blast_eq_neq (ig+1)%positive ils1 ils2) =>
                [[g_aux cs_neq] auxs]. set r := Pos ig.
  case=> _ <- <- Henc1 Henc2 Hcnf.
  rewrite add_prelude_append add_prelude_cons in Hcnf.
  move/andP: Hcnf=> [Hcnf_neq Hcnf]. move/andP: Hcnf=> [Hcnf_auxs Hcnf_eq].
  rewrite /enc_bit. case Hr: (interp_lit E r).
  - apply/eqP; symmetry. apply/eqP.
    exact: (bit_blast_eq_eq_correct Henc1 Henc2 Hcnf_eq Hr).
  - move: (bit_blast_eq_choice_correct Hcnf_auxs). rewrite Hr.
    case => H; first by elim H. apply/eqP; symmetry. apply/eqP.
    exact: (bit_blast_eq_neq_correct Hneq Henc1 Henc2 Hcnf_neq H).
Qed.

Lemma mk_env_eq_neq_is_bit_blast_eq_neq :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_eq_neq E g ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_eq_neq g ls1 ls2 = (g', cs, lrs).
Proof.
  elim.
  - rewrite /=; intros; dcase_hyps; subst; reflexivity.
  - intros_tuple; dcase_hyps; intros; subst.
    rewrite (H _ _ _ _ _ _ _ _ H0). rewrite (tval_eq H1). reflexivity.
Qed.

Lemma mk_env_eq_is_bit_blast_eq :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_eq E g ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_eq g ls1 ls2 = (g', cs, lrs).
Proof.
  rewrite /mk_env_eq /bit_blast_eq /=; intros; dcase_hyps; subst.
  rewrite (mk_env_eq_neq_is_bit_blast_eq_neq H). reflexivity.
Qed.

Lemma mk_env_eq_neq_newer_gen :
forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
  mk_env_eq_neq E g ls1 ls2 = (E', g', cs, lr) ->
  (g <=? g')%positive.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr /=. case=> _ <- _ _. exact: Pos.leb_refl.
  - move=> w IH E g. case/tupleP=> [ls1_hd ls1_tl]. case/tupleP=> [ls2_hd ls2_tl].
    move=> E' g' cs. case/tupleP=> [lr_hd lr_tl]. rewrite /= !theadE !beheadCons.
    case Henv: (mk_env_eq_neq
                  (env_upd E g (xorb (interp_lit E ls1_hd) (interp_lit E ls2_hd)))
                  (g + 1)%positive ls1_tl ls2_tl) => [[[E_tl g_tl] cs_tl] auxs_tl].
    case=> _ <- _ _ _. move: (IH _ _ _ _ _ _ _ _ Henv) => H.
    apply: (pos_leb_trans _ H). exact: pos_leb_add_diag_r.
Qed.

Lemma mk_env_eq_newer_gen :
forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
  mk_env_eq E g ls1 ls2 = (E', g', cs, lr) ->
  (g <=? g')%positive.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_eq /gen.
  case Hneq: (mk_env_eq_neq
                (env_upd E (var_of_lit (Pos g))
                         (interp_lits E ls1 == interp_lits E ls2))
                (g + 1)%positive ls1 ls2)=> [[[E_aux g_aux] cs_neq] auxs].
  case=> _ <- _ _. move: (mk_env_eq_neq_newer_gen Hneq) => H.
  apply: (pos_leb_trans _ H). exact: pos_leb_add_diag_r.
Qed.

Lemma mk_env_eq_neq_newer_res :
forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
  mk_env_eq_neq E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lits g' lr.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr /=. case=> _ <- _ <-. done.
  - move=> w IH E g. case/tupleP=> [ls1_hd ls1_tl]. case/tupleP=> [ls2_hd ls2_tl].
    move=> E' g' cs. case/tupleP=> [lr_hd lr_tl]. rewrite /= !theadE !beheadCons.
    case Henv: (mk_env_eq_neq
                  (env_upd E g (xorb (interp_lit E ls1_hd) (interp_lit E ls2_hd)))
                  (g + 1)%positive ls1_tl ls2_tl) => [[[E_tl g_tl] cs_tl] auxs_tl].
    case=> _ <- _ <- <-. rewrite (IH _ _ _ _ _ _ _ _ Henv) andbT.
    move: (mk_env_eq_neq_newer_gen Henv) => H.
    rewrite /newer_than_lit /newer_than_var /=.
    exact: (pos_ltb_leb_trans (pos_ltb_add_diag_r g 1) H).
Qed.

Lemma mk_env_eq_newer_res :
forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
  mk_env_eq E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g' lr.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_eq /gen.
  case Henv: (mk_env_eq_neq
                (env_upd E (var_of_lit (Pos g))
                         (interp_lits E ls1 == interp_lits E ls2))
                (g + 1)%positive ls1 ls2)=> [[[E_aux g_aux] cs_neq] auxs].
  case=> _ <- _ <-. move: (mk_env_eq_neq_newer_gen Henv) => H.
  apply: (newer_than_lit_le_newer _ H). exact: newer_than_lit_add_diag_r.
Qed.

Lemma bit_blast_eq_eq_newer_cnf :
forall w g g' (ls1 ls2 : w.-tuple literal),
  (g <? g')%positive ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' (bit_blast_eq_eq (Pos g) ls1 ls2).
Proof.
  elim.
  - move=> g g' ls1 ls2 H_gg' Hnew_gls1 Hnew_gls2 /=. done.
  - move=> w IH g g'. case/tupleP=> [ls1_hd ls1_tl]. case/tupleP=> [ls2_hd ls2_tl].
    rewrite /= !theadE !beheadCons. move=> Hgg' /andP [Hnew_gls1hd Hnew_gls1tl].
    move/andP=> [Hnew_gls2hd Hnew_gls2tl]. rewrite !newer_than_lit_neg.
    move: (pos_ltb_leb_incl Hgg') => Hgg'_le.
    rewrite (newer_than_lit_le_newer Hnew_gls1hd Hgg'_le).
    rewrite (newer_than_lit_le_newer Hnew_gls2hd Hgg'_le).
    rewrite (IH _ _ _ _ Hgg' Hnew_gls1tl Hnew_gls2tl).
    rewrite /newer_than_lit /newer_than_var /=. by rewrite Hgg'.
Qed.

Lemma mk_env_eq_neq_newer_cnf :
forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
  mk_env_eq_neq E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr /=. case=> _ <- <- _ Hnew_gls1 Hnew_gls2.
    done.
  - move=> w IH E g. case/tupleP=> [ls1_hd ls1_tl]. case/tupleP=> [ls2_hd ls2_tl].
    move=> E' g' cs. case/tupleP=> [lr_hd lr_tl]. rewrite /= !theadE !beheadCons.
    case Henv: (mk_env_eq_neq
                  (env_upd E g (xorb (interp_lit E ls1_hd) (interp_lit E ls2_hd)))
                  (g + 1)%positive ls1_tl ls2_tl) => [[[E_tl g_tl] cs_tl] auxs_tl].
    case=> _ <- <- _ _. move/andP=> [Hnew_gls1_hd Hnew_gls1_tl].
    move/andP=> [Hnew_gls2_hd Hnew_gls2_tl]. rewrite /=.
    move: (mk_env_eq_neq_newer_gen Henv) => H_gp1gtl.
    move: (pos_leb_add_diag_r g 1) => H_ggp1.
    move: (pos_leb_trans H_ggp1 H_gp1gtl) => H_ggtl.
    rewrite !newer_than_lit_neg.
    move: (newer_than_lit_le_newer Hnew_gls1_hd H_ggtl) => ->.
    move: (newer_than_lit_le_newer Hnew_gls2_hd H_ggtl) => ->.
    move: (IH _ _ _ _ _ _ _ _ Henv
              (newer_than_lits_le_newer Hnew_gls1_tl H_ggp1)
              (newer_than_lits_le_newer Hnew_gls2_tl H_ggp1)) => ->.
    rewrite /newer_than_lit /newer_than_var /=.
    rewrite (pos_ltb_leb_trans (pos_ltb_add_diag_r g 1) H_gp1gtl). done.
Qed.

Lemma mk_env_eq_newer_cnf :
forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
  mk_env_eq E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_eq /gen.
  case Hneq: (mk_env_eq_neq
                (env_upd E (var_of_lit (Pos g))
                         (interp_lits E ls1 == interp_lits E ls2))
                (g + 1)%positive ls1 ls2)=> [[[E_aux g_aux] cs_neq] auxs].
  case=> _ <- <- _. move=> Hnew_gls1 Hnew_gls2 /=.
  rewrite newer_than_cnf_append /=. move: (pos_leb_add_diag_r g 1) => Hggp1.
  move: (newer_than_lits_le_newer Hnew_gls1 Hggp1) => Hnew_gp1ls1.
  move: (newer_than_lits_le_newer Hnew_gls2 Hggp1) => Hnew_gp1ls2.
  move: (mk_env_eq_neq_newer_cnf Hneq Hnew_gp1ls1 Hnew_gp1ls2) => ->.
  move: (mk_env_eq_neq_newer_res Hneq) => ->.
  move: (mk_env_eq_neq_newer_gen Hneq) => H_gp1gaux.
  rewrite /newer_than_lit /newer_than_var /=.
  move: (pos_ltb_leb_trans (pos_ltb_add_diag_r g 1) H_gp1gaux)=> H_ggaux.
  rewrite H_ggaux. exact: (bit_blast_eq_eq_newer_cnf H_ggaux Hnew_gls1 Hnew_gls2).
Qed.

Lemma mk_env_eq_neq_preserve :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_eq_neq E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr /=. case=> <- _ _ _. exact: env_preserve_refl.
  - move=> w IH E g. case/tupleP=> [ls1_hd ls1_tl]. case/tupleP=> [ls2_hd ls2_tl].
    move=> E' g' cs. case/tupleP=> [lr_hd lr_tl]. rewrite /= !theadE !beheadCons.
    case Henv: (mk_env_eq_neq
                  (env_upd E g (xorb (interp_lit E ls1_hd) (interp_lit E ls2_hd)))
                  (g + 1)%positive ls1_tl ls2_tl) => [[[E_tl g_tl] cs_tl] auxs_tl].
    case=> <- _ _ _ _. move: (IH _ _ _ _ _ _ _ _ Henv) => Hpre.
    exact: (env_preserve_env_upd_succ Hpre).
Qed.

Lemma mk_env_eq_preserve :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_eq E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_eq /gen.
  case Hneq: (mk_env_eq_neq
                (env_upd E (var_of_lit (Pos g))
                         (interp_lits E ls1 == interp_lits E ls2))
                (g + 1)%positive ls1 ls2)=> [[[E_aux g_aux] cs_neq] auxs].
  case=> <- _ _ _. exact: (env_preserve_env_upd_succ (mk_env_eq_neq_preserve Hneq)).
Qed.

Lemma mk_env_eq_neq_sat :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_eq_neq E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lr /=. case=> <- _ <- _ Hnew_gls1 Hnew_gls2. done.
  - move=> w IH E g. case/tupleP=> [ls1_hd ls1_tl]. case/tupleP=> [ls2_hd ls2_tl].
    move=> E' g' cs. case/tupleP=> [lr_hd lr_tl]. rewrite /= !theadE !beheadCons.
    case Henv: (mk_env_eq_neq
                  (env_upd E g (xorb (interp_lit E ls1_hd) (interp_lit E ls2_hd)))
                  (g + 1)%positive ls1_tl ls2_tl) => [[[E_tl g_tl] cs_tl] auxs_tl].
    case=> <- Hg <- H1 H2. move=> /andP [Hnew_gls1hd Hnew_gls1tl].
    move=> /andP [Hnew_gls2hd Hnew_gls2tl]. rewrite !interp_cnf_cons.
    move: (pos_leb_add_diag_r g 1) => H_gg1.
    move: (newer_than_lit_le_newer Hnew_gls1hd H_gg1) => Hnew_g1ls1hd.
    move: (newer_than_lit_le_newer Hnew_gls2hd H_gg1) => Hnew_g1ls2hd.
    move: (newer_than_lits_le_newer Hnew_gls1tl H_gg1) => Hnew_g1ls1tl.
    move: (newer_than_lits_le_newer Hnew_gls2tl H_gg1) => Hnew_g1ls2tl.
    rewrite (IH _ _ _ _ _ _ _ _ Henv Hnew_g1ls1tl Hnew_g1ls2tl) /=.
    rewrite !interp_lit_neg_lit. move: (mk_env_eq_neq_preserve Henv) => Hpre.
    move: (env_preserve_lit Hpre (newer_than_lit_add_diag_r (Pos g) 1))=> /= H_etlg.
    rewrite env_upd_eq in H_etlg. rewrite H_etlg => {H_etlg}.
    move: (env_preserve_lit Hpre Hnew_g1ls1hd) (env_preserve_lit Hpre Hnew_g1ls2hd).
    rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hnew_gls1hd)).
    rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hnew_gls2hd)).
    move=> -> ->.
    by case: (interp_lit E ls1_hd); case: (interp_lit E ls2_hd).
Qed.

Lemma bit_blast_eq_eq_sat_eq :
  forall w (E : env) g (ls1 ls2 : w.-tuple literal),
  E g ->
  interp_lits E ls1 == interp_lits E ls2 ->
  interp_cnf E (bit_blast_eq_eq (Pos g) ls1 ls2).
Proof.
  elim.
  - move=> E g ls1 ls2 Heg Heq /=. done.
  - move=> w IH E g. case/tupleP=> [ls1_hd ls1_tl]. case/tupleP=> [ls2_hd ls2_tl].
    move=> Heg. rewrite 2!interp_lits_cons. move/eqP=> Heq.
    move: (splitTuple Heq) => {Heq} [/eqP Heq_hd /eqP Heq_tl].
    rewrite /bit_blast_eq_eq -/bit_blast_eq_eq.
    rewrite List.map_cons !interp_cnf_cons.
    replace (splitlsb [tuple of ls1_hd :: ls1_tl]).1 with ls1_tl;
      last by rewrite /= beheadCons; reflexivity.
    replace (splitlsb [tuple of ls2_hd :: ls2_tl]).1 with ls2_tl;
      last by rewrite /= beheadCons; reflexivity.
    rewrite (IH E _ _ _ Heg Heq_tl) /=.
    rewrite !theadE !interp_lit_neg_lit. rewrite (eqP Heq_hd) Heg /=.
    by case: (interp_lit E ls2_hd).
Qed.

Lemma bit_blast_eq_eq_sat_neq :
  forall w (E : env) g (ls1 ls2 : w.-tuple literal),
  ~~ (E g) ->
  interp_cnf E (bit_blast_eq_eq (Pos g) ls1 ls2).
Proof.
  elim.
  - move=> E g ls1 ls2 Heg /=. done.
  - move=> w IH E g. case/tupleP=> [ls1_hd ls1_tl]. case/tupleP=> [ls2_hd ls2_tl].
    move=> Heg. rewrite /bit_blast_eq_eq -/bit_blast_eq_eq.
    replace ((splitlsb [tuple of ls1_hd :: ls1_tl]).1) with ls1_tl;
      last by rewrite /= beheadCons.
    replace ((splitlsb [tuple of ls2_hd :: ls2_tl]).1) with ls2_tl;
      last by rewrite /= beheadCons.
    rewrite List.map_cons !interp_cnf_cons. rewrite (IH _ _ _ _ Heg) /=.
    by rewrite Heg.
Qed.

Lemma mk_env_eq_neq_sat_neq :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_eq_neq E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_lits E' ls1 != interp_lits E' ls2 ->
    interp_clause E' lrs.
Proof.
  elim.
  - move=> E g ls1 ls2 E' g' cs lrs /=. case=> <- _ _ <- Hnew_gls1 Hnew_gls2 Hne.
    apply: False_ind. apply: (negP Hne). rewrite tuple0. apply/eqP. symmetry.
    rewrite tuple0. reflexivity.
  - move=> w IH E g. case/tupleP=> [ls1_hd ls1_tl]. case/tupleP=> [ls2_hd ls2_tl].
    move=> E' g' cs. case/tupleP=> [lr_hd lr_tl].
    rewrite (lock interp_clause) /= !theadE !beheadCons -lock.
    case Henv: (mk_env_eq_neq
                  (env_upd E g (xorb (interp_lit E ls1_hd) (interp_lit E ls2_hd)))
                  (g + 1)%positive ls1_tl ls2_tl) => [[[E_tl g_tl] cs_tl] auxs_tl].
    case=> <- _ _ <- <-. move/andP=> [Hnew_gls1hd Hnew_gls1tl].
    move/andP=> [Hnew_gls2hd Hnew_gls2tl]. move=> Hne. rewrite interp_clause_cons.
    rewrite 2!interp_lits_cons in Hne. rewrite cons_tuple_neq_case in Hne.
    case/orP: Hne.
    + move=> Hne_hd. move: (mk_env_eq_neq_preserve Henv) => Hpre.
      move: (env_preserve_lit Hpre (newer_than_lit_add_diag_r (Pos g) 1)) => /=.
      rewrite env_upd_eq. move: (env_preserve_env_upd_succ Hpre) => {Hpre} Hpre.
      rewrite -(env_preserve_lit Hpre Hnew_gls1hd)
              -(env_preserve_lit Hpre Hnew_gls2hd).
      move: Hne_hd.
        by case: (E_tl g);
          case: (interp_lit E_tl ls1_hd); case: (interp_lit E_tl ls2_hd).
    + move=> Hne_tl. move: (pos_leb_add_diag_r g 1) => Hgg1.
      move: (newer_than_lits_le_newer Hnew_gls1tl Hgg1) => Hnew_g1ls1tl.
      move: (newer_than_lits_le_newer Hnew_gls2tl Hgg1) => Hnew_g1ls2tl.
      rewrite (IH _ _ _ _ _ _ _ _ Henv Hnew_g1ls1tl Hnew_g1ls2tl Hne_tl).
        by rewrite orbT.
Qed.

Lemma mk_env_eq_sat :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_eq E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_eq /gen.
  case Henv: (mk_env_eq_neq
                (env_upd E (var_of_lit (Pos g))
                         (interp_lits E ls1 == interp_lits E ls2))
                (g + 1)%positive ls1 ls2)=> [[[E_aux g_aux] cs_neq] auxs].
  case=> <- _ <- _ Hnew_gls1 Hnew_gls2.
  rewrite interp_cnf_append interp_cnf_cons interp_clause_cons.
  move: (pos_leb_add_diag_r g 1) => H_gg1.
  move: (newer_than_lits_le_newer Hnew_gls1 H_gg1) => Hnew_g1ls1.
  move: (newer_than_lits_le_newer Hnew_gls2 H_gg1) => Hnew_g1ls2.
  rewrite (mk_env_eq_neq_sat Henv Hnew_g1ls1 Hnew_g1ls2) andTb.
  move: (mk_env_eq_neq_preserve Henv) => Hpre.
  move: (env_preserve_lit Hpre (newer_than_lit_add_diag_r (Pos g) 1)) => /=.
  rewrite env_upd_eq. move: (env_preserve_env_upd_succ Hpre) => /= {Hpre} Hpre.
  rewrite -(env_preserve_lits Hpre Hnew_gls1) -(env_preserve_lits Hpre Hnew_gls2).
  case Heg: (E_aux g).
  - rewrite /=. move=> Heq. move: (Logic.eq_sym Heq) => {Heq} Heq.
    exact: (bit_blast_eq_eq_sat_eq Heg Heq).
  - rewrite /=. move=> Hne. move: (Logic.eq_sym Hne) => {Hne} Hne.
    move/idP/negP: Hne => Hne. move/idP/negP: Heg => Heg.
    rewrite (bit_blast_eq_eq_sat_neq _ _ Heg) andbT.
    exact: (mk_env_eq_neq_sat_neq Henv Hnew_g1ls1 Hnew_g1ls2 Hne).
Qed.
