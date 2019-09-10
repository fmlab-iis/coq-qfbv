From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From BitBlasting Require Import Var QFBV CNF BBCommon.
From ssrlib Require Import ZAriths Tactics Bools Seqs.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== bit_blast_eq ===== *)

Fixpoint bit_blast_eq_eq_zip r lsp : cnf :=
  match lsp with
  | [::] => [::]
  | (l1, l2)::tl =>
      let cs_hd := List.map (fun cs => neg_lit r::cs) (cnf_lit_eq l1 l2) in
      let cs_tl := bit_blast_eq_eq_zip r tl in
      catrev cs_hd cs_tl
  end.

Definition bit_blast_eq_choice r (auxs: word) : cnf :=
  [:: r::auxs].

Fixpoint bit_blast_eq_neq_zip g lsp : generator * cnf * word :=
  match lsp with
  | [::] => (g, [::], [::])
  | (l1, l2)::tl =>
      let (g_hd, auxs_hd) := gen g in
      let cs_hd := [:: [:: neg_lit auxs_hd; l1; l2];
                      [:: neg_lit auxs_hd; neg_lit l1; neg_lit l2];
                      [:: auxs_hd; neg_lit l1; l2];
                      [:: auxs_hd; l1; neg_lit l2] ] in
      let '(g_tl, cs_tl, auxs_tl) := bit_blast_eq_neq_zip g_hd tl in
      (g_tl, catrev cs_hd cs_tl, auxs_hd :: auxs_tl)
  end.

Fixpoint mk_env_eq_neq_zip E g lsp : env * generator * cnf * word :=
  match lsp with
  | [::] => (E, g, [::], [::])
  | (l1, l2)::tl =>
      let (g_hd, auxs_hd) := gen g in
      let E' := env_upd E (var_of_lit auxs_hd)
                        (xorb (interp_lit E l1) (interp_lit E l2)) in
      let cs_hd := [:: [:: neg_lit auxs_hd; l1; l2];
                      [:: neg_lit auxs_hd; neg_lit l1; neg_lit l2];
                      [:: auxs_hd; neg_lit l1; l2];
                      [:: auxs_hd; l1; neg_lit l2] ] in
      let '(E_tl, g_tl, cs_tl, auxs_tl) := mk_env_eq_neq_zip E' g_hd tl in
      (E_tl, g_tl, catrev cs_hd cs_tl, auxs_hd :: auxs_tl)
  end.

Definition bit_blast_eq_zip (g : generator) lsp : generator * cnf * literal :=
  let (g_r, r) := gen g in
  let '(g_aux, cs_neq, auxs) := bit_blast_eq_neq_zip g_r lsp in
  let cs_aux := bit_blast_eq_choice r auxs in
  let cs_eq := bit_blast_eq_eq_zip r lsp in
  (g_aux, catrev cs_neq (catrev cs_aux cs_eq), r).

Definition mk_env_eq_zip E g lsp : env * generator * cnf * literal :=
  let (g_r, r) := gen g in
  let E' := env_upd E (var_of_lit r) (interp_word E (unzip1 lsp) == interp_word E (unzip2 lsp)) in
  let '(E_aux, g_aux, cs_neq, auxs) := mk_env_eq_neq_zip E' g_r lsp in
  let cs_aux := bit_blast_eq_choice r auxs in
  let cs_eq := bit_blast_eq_eq_zip r lsp in
  (E_aux, g_aux, catrev cs_neq (catrev cs_aux cs_eq), r).

Definition bit_blast_eq g ls1 ls2 := bit_blast_eq_zip g (extzip_ff ls1 ls2).

Definition mk_env_eq E g ls1 ls2 := mk_env_eq_zip E g (extzip_ff ls1 ls2).

Lemma bit_blast_eq_eq_zip_correct E bsp lsp lr:
  enc_bits E (unzip1 lsp) (unzip1 bsp) ->
  enc_bits E (unzip2 lsp) (unzip2 bsp) ->
  interp_cnf E (add_prelude (bit_blast_eq_eq_zip lr lsp)) ->
  interp_lit E lr ->
  (unzip1 bsp) = (unzip2 bsp).
Proof.
  elim: lsp E bsp lr => [| [ls1_hd ls2_hd] lsp_tl IH] E bsp lr.
  - rewrite !enc_bits_nil_l unzip1_l_nil.
    by case/eqP => ->.
  - rewrite /=.
    case: bsp => [| [bsp_hd1 bsp_hd2] bsp_tl] //=.
    rewrite !enc_bits_cons. move=> /andP [Henc1hd Henc1tl] /andP [Henc2hd Henc2tl].
    move=> Hcnf Hlr.
    rewrite add_prelude_cons in Hcnf. move/andP: Hcnf => [Hcnf_hd1 Hcnf_tl].
    rewrite add_prelude_cons in Hcnf_tl. move/andP: Hcnf_tl => [Hcnf_hd2 Hcnf_tl].
    have Heqhd: bsp_hd1 = bsp_hd2.
    {
      rewrite 2!add_prelude_singleton in Hcnf_hd1 Hcnf_hd2.
      rewrite /= in Hcnf_hd1 Hcnf_hd2. split_andb_hyps.
      rewrite !interp_lit_neg_lit in H0 H2. rewrite Hlr /= !orbF in H0 H2.
      move: (expand_eq (interp_lit E ls1_hd) (interp_lit E ls2_hd)).
      rewrite H0 H2 /= => /eqP Heq. exact: (enc_bit_eq_bit Heq Henc1hd Henc2hd).
    }
    move: (IH _ _ _ Henc1tl Henc2tl Hcnf_tl Hlr) => Heqtl.
    rewrite Heqhd Heqtl. reflexivity.
Qed.

Lemma bit_blast_eq_neq_zip_correct E g bsp lsp g' cs lauxs:
  bit_blast_eq_neq_zip g lsp = (g', cs, lauxs) ->
  enc_bits E (unzip1 lsp) (unzip1 bsp) ->
  enc_bits E (unzip2 lsp) (unzip2 bsp) ->
  interp_cnf E (add_prelude cs) ->
  (exists laux : literal, laux \in lauxs /\ interp_lit E laux) ->
  (unzip1 bsp) <> (unzip2 bsp).
Proof.
  elim: lsp E g bsp g' cs lauxs  => [| [ls1_hd ls2_hd] lsp_tl IH] E g bsp g' cs lauxs /=.
  - case=> _ _ <- _ _ _ Hcontra.
    destruct Hcontra.
    rewrite in_nil in H. by destruct H.
  - dcase (bit_blast_eq_neq_zip (g + 1)%positive lsp_tl) => [[[g_tl cs_tl] auxs_tl] Hblast].
    case=> Hg Hcs Hlauxs.
    case: bsp => [| [bsp_hd1 bsp_hd2] bsp_tl] //=.
    rewrite !enc_bits_cons. move=> /andP [Henc1hd Henc1tl] /andP [Henc2hd Henc2tl].
    move=> Hcnf Hlr.
    move: Hlr => [laux [Hin Haux]].
    rewrite -Hlauxs in_cons in Hin.
    case/orP: Hin.
    + move=> /eqP Hin. rewrite -Hcs in Hcnf. rewrite -/(neg_lit (Pos g)) in Hcnf.
      rewrite  -Hin in Hcnf.
      rewrite add_prelude_expand /= in Hcnf.
      rewrite !interp_lit_neg_lit in Hcnf. rewrite Haux /= !orbF in Hcnf. split_andb_hyps.
      move=> Heq. injection Heq => Heqtl Heqhd. move: H0 H1.
      move: (enc_bit_eq_lit Heqhd Henc1hd Henc2hd) => ->.
      by case: (interp_lit E ls2_hd).
    + move=> Hin.
      have Hexists: (exists laux : literal,
                        laux \in auxs_tl /\ interp_lit E laux).
      {
        exists laux. split; last by exact: Haux.
        exact: Hin.
      }
      have Hcnftl: interp_cnf E (add_prelude cs_tl).
      {
        rewrite -Hcs in Hcnf.
        rewrite add_prelude_cons in Hcnf.
        move/andP: Hcnf => [Hcnf1 Hcnf]. rewrite add_prelude_cons in Hcnf.
        move/andP: Hcnf => [Hcnf2 Hcnf]. rewrite add_prelude_cons in Hcnf.
        move/andP: Hcnf => [Hcnf3 Hcnf]. rewrite add_prelude_cons in Hcnf.
        move/andP: Hcnf => [Hcnf4 Hcnf]. exact: Hcnf.
      }
      move: (IH _ _ _ _ _ _ Hblast Henc1tl Henc2tl Hcnftl Hexists) => Hne Heq.
      apply: Hne. injection Heq => Heqtl Heqhd. exact: Heqtl.
Qed.

Lemma bit_blast_eq_choice_correct E r auxs:
  interp_cnf E (add_prelude (bit_blast_eq_choice r auxs)) ->
  interp_lit E r \/ (exists aux : literal,
                       aux \in auxs /\ interp_lit E aux).
Proof.
  rewrite /bit_blast_eq_choice.
  rewrite add_prelude_expand.
  rewrite interp_cnf_cons /= -/(interp_clause E (r::auxs)).
  rewrite !andbT.
  move/andP=> [_ H].
  case/orP: H => H.
  - by left.
  - right.
    move: (interp_clause_mem H).
    destruct 1.
    exists x; done.
Qed.

Lemma bit_blast_eq_zip_correct E g bsp lsp g' cs lr:
    bit_blast_eq_zip g lsp = (g', cs, lr) ->
    enc_bits E (unzip1 lsp) (unzip1 bsp) ->
    enc_bits E (unzip2 lsp) (unzip2 bsp) ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (unzip1 bsp == unzip2 bsp).
Proof.
  rewrite /bit_blast_eq_zip.
  rewrite /gen. case Hneq: (bit_blast_eq_neq_zip (g+1)%positive lsp) =>
                [[g_aux cs_neq] auxs]. set r := Pos g.
  case=> _ <- <- Henc1 Henc2 Hcnf.
  rewrite add_prelude_catrev add_prelude_cons in Hcnf.
  move/andP: Hcnf=> [Hcnf_neq Hcnf]. move/andP: Hcnf=> [Hcnf_auxs Hcnf_eq].
  rewrite /enc_bit. case Hr: (interp_lit E r).
  - apply/eqP; symmetry. apply/eqP.
    exact: (bit_blast_eq_eq_zip_correct Henc1 Henc2 Hcnf_eq Hr).
  - move: (bit_blast_eq_choice_correct Hcnf_auxs). rewrite Hr.
    case => H; first by elim H. apply/eqP; symmetry. apply/eqP.
    exact: (bit_blast_eq_neq_zip_correct Hneq Henc1 Henc2 Hcnf_neq H).
Qed.

Lemma bit_blast_eq_correct g bs1 bs2 E ls1 ls2 g' cs lr :
  bit_blast_eq g ls1 ls2 = (g', cs, lr) ->
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 -> interp_cnf E (add_prelude cs) ->
  enc_bit E lr (bs1 == bs2).
Proof.
  rewrite /bit_blast_eq => Hbb Henc1 Henc2 Hcs.
  move: (enc_bits_size Henc1) (enc_bits_size Henc2) => Hs1 Hs2.
  move: (add_prelude_enc_bit_tt Hcs) => Henctt.
  move: (bit_blast_eq_zip_correct Hbb
                                    (enc_bits_unzip1_extzip Henctt Henc1 Henc2)
                                    (enc_bits_unzip2_extzip Henctt Henc1 Henc2) Hcs).
Abort.


(*
Lemma bit_blast_eq_correct :
  forall w g (bs1 bs2 : bits) E g' ls1 ls2 cs lr,
    size bs1 = w ->
    size bs2 = w ->
    bit_blast_eq g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (bs1 == bs2).
Proof.
  move=> w ig ibs1 ibs2 E og ils1 ils2 cs olr Hszb1 Hszb2.
  rewrite /bit_blast_eq.
  rewrite /gen. case Hneq: (bit_blast_eq_neq w (ig+1)%positive ils1 ils2) =>
                [[g_aux cs_neq] auxs]. set r := Pos ig.
  case=> _ <- <- Henc1 Henc2 Hcnf.
  rewrite add_prelude_catrev add_prelude_cons in Hcnf.
  move/andP: Hcnf=> [Hcnf_neq Hcnf]. move/andP: Hcnf=> [Hcnf_auxs Hcnf_eq].
  rewrite /enc_bit. case Hr: (interp_lit E r).
  - apply/eqP; symmetry. apply/eqP.
    exact: (bit_blast_eq_eq_correct Hszb1 Hszb2 Henc1 Henc2 Hcnf_eq Hr).
  - move: (bit_blast_eq_choice_correct Hcnf_auxs). rewrite Hr.
    case => H; first by elim H. apply/eqP; symmetry. apply/eqP.
    exact: (bit_blast_eq_neq_correct Hszb1 Hszb2 Hneq Henc1 Henc2 Hcnf_neq H).
Qed.

Lemma mk_env_eq_neq_is_bit_blast_eq_neq :
  forall w E g ls1 ls2 E' g' cs lrs,
    mk_env_eq_neq w E g ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_eq_neq w g ls1 ls2 = (g', cs, lrs).
Proof.
  elim.
  - rewrite /=; intros; dcase_hyps; subst; reflexivity.
  - move=> w IH E g ls1 ls2 E' g' cs lrs.
    rewrite /=.
    dcase (mk_env_eq_neq w
      (env_upd E g
         (xorb (interp_lit E (head lit_ff ls1))
            (interp_lit E (head lit_ff ls2)))) (g + 1)%positive
      (behead ls1) (behead ls2) ) => [[[[E_tl g_tl] cs_tl] auxs_tl] Henv_tl].
    rewrite (IH _ _ _ _ _ _ _ _ Henv_tl).
    by case=> _ <- <- <-.
Qed.

Lemma mk_env_eq_is_bit_blast_eq :
  forall w E g ls1 ls2  E' g' cs lrs,
    mk_env_eq w E g ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_eq w g ls1 ls2 = (g', cs, lrs).
Proof.
  rewrite /mk_env_eq /bit_blast_eq /=; intros; dcase_hyps; subst.
  move: H.
  dcase (mk_env_eq_neq w (env_upd E g (interp_word E ls1 == interp_word E ls2))
      (g + 1)%positive ls1 ls2 ) => [[[[E_aux g_aux] cs_neq] auxs] Henv].
  rewrite (mk_env_eq_neq_is_bit_blast_eq_neq Henv).
  by case=> _ <- <- <-.
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

Lemma splitlsb_cons w bs bs_hd bs_tl:
  size bs = w.+1 ->
  splitlsb bs = (bs_hd, bs_tl) ->
  bs = bs_hd :: bs_tl.
Proof.
  case: bs.
  - discriminate.
  - move=> a l Hsz Hsplit.
  rewrite /splitlsb /split_head in Hsplit.
  inversion Hsplit.
  done.
Qed.

Lemma splitlsl_cons w ls ls_hd ls_tl:
  size ls = w.+1 ->
  splitlsl ls = (ls_hd, ls_tl) ->
  ls = ls_hd :: ls_tl.
Proof.
  case: ls.
  - discriminate.
  - move=> a l Hsz Hsplit.
  rewrite /splitlsb /split_head in Hsplit.
  inversion Hsplit.
  done.
Qed.


Lemma size_splitlsl ls : size (snd (splitlsl ls)) = size ls - 1.
Proof.
  destruct ls => /=.
  - reflexivity.
  - rewrite subn1 -pred_Sn. reflexivity.
Qed.

Lemma bit_blast_eq_neq_size:
  forall w g g' ls1 ls2 cs lauxs,
    size ls1 = w ->
    size ls2 = w ->
    bit_blast_eq_neq w g ls1 ls2 = (g', cs, lauxs) ->
    size lauxs = w.
Proof.
  elim.
  - by rewrite /bit_blast_eq_neq; move=> _ _ _ _ _ _ _ _ [_ _ <-].
  - move=> w IH g g' ls1 ls2 cs lauxs Hsz1 Hsz2.
    case Hls1: (splitlsl ls1) => [ls1_hd ls1_tl].
    case Hls2: (splitlsl ls2) => [ls2_hd ls2_tl].
    rewrite /=.
    move: (size_splitlsl ls1).
    rewrite Hls1 Hsz1 subn1 /= => Hsz1tl.
    move: (size_splitlsl ls2).
    rewrite Hls2 Hsz2 subn1 /= => Hsz2tl.
    move: (splitlsl_cons Hsz1 Hls1) => Hls1_split.
    move: (splitlsl_cons Hsz2 Hls2) => Hls2_split.
    rewrite Hls1_split Hls2_split /=.
    dcase (bit_blast_eq_neq w (g + 1)%positive ls1_tl ls2_tl) => [[[g_tl cs_tl] aux_tl] Hblast].
    case=> _ _ <-.
    rewrite /=.
      by rewrite (IH _ _ _ _ _ _ Hsz1tl Hsz2tl Hblast).
Qed.
*)
