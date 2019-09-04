
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNFSimple BBCommonSimple.
From ssrlib Require Import Var ZAriths Tuples Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_full_adder ===== *)

Definition bit_blast_full_adder1 g a1 a2 cin :=
  let (g', r) := gen g in
  let (g'', cout) := gen g' in
  let sum_cs := [::
        [:: neg_lit r; a1; a2; cin];
          [:: neg_lit r; neg_lit a1; neg_lit a2; cin];
          [:: neg_lit r; neg_lit a1; a2; neg_lit cin];
          [:: neg_lit r; a1; neg_lit a2; neg_lit cin];
        [:: r; neg_lit a1; a2; cin];
          [:: r; a1; neg_lit a2; cin];
          [:: r; a1; a2; neg_lit cin];
          [:: r; neg_lit a1; neg_lit a2; neg_lit cin]
      ] in
  let cout_cs := [::
        [:: neg_lit cout; a1; a2];
          [:: neg_lit cout; a1; cin];
          [:: neg_lit cout; a2; cin];
        [:: cout; neg_lit a1; neg_lit a2];
          [:: cout; neg_lit a1; a2; neg_lit cin];
          [:: cout; a1; neg_lit a2; neg_lit cin]
      ] in
  (g'', sum_cs++cout_cs, cout, r).

Definition mk_env_full_adder1 E g a1 a2 cin :=
  let (g', r) := gen g in
  let (g'', cout) := gen g' in
  let sum_cs := [::
        [:: neg_lit r; a1; a2; cin];
          [:: neg_lit r; neg_lit a1; neg_lit a2; cin];
          [:: neg_lit r; neg_lit a1; a2; neg_lit cin];
          [:: neg_lit r; a1; neg_lit a2; neg_lit cin];
        [:: r; neg_lit a1; a2; cin];
          [:: r; a1; neg_lit a2; cin];
          [:: r; a1; a2; neg_lit cin];
          [:: r; neg_lit a1; neg_lit a2; neg_lit cin]
      ] in
  let cout_cs := [::
        [:: neg_lit cout; a1; a2];
          [:: neg_lit cout; a1; cin];
          [:: neg_lit cout; a2; cin];
        [:: cout; neg_lit a1; neg_lit a2];
          [:: cout; neg_lit a1; a2; neg_lit cin];
          [:: cout; a1; neg_lit a2; neg_lit cin]
      ] in
  let E' := env_upd E (var_of_lit r)
                    (xorb (xorb (interp_lit E a1) (interp_lit E a2))
                          (interp_lit E cin)) in
  let E'' := env_upd E' (var_of_lit cout)
                     (((interp_lit E a1) && (interp_lit E a2))
                      || ((xorb (interp_lit E a1) (interp_lit E a2))
                            && (interp_lit E cin))) in
  (E'', g'', sum_cs++cout_cs, cout, r).

Lemma bit_blast_full_adder1_correct1 :
  forall g b1 b2 bcin E l1 l2 lcin g' cs lcout lr,
    bit_blast_full_adder1 g l1 l2 lcin = (g', cs, lcout, lr) ->
    enc_bit E l1 b1 -> enc_bit E l2 b2 -> enc_bit E lcin bcin ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (xorb (xorb b1 b2) bcin) /\
    enc_bit E lcout ((b1 && b2) || ((xorb b1 b2) && bcin)).
Proof.
  rewrite /bit_blast_full_adder1 /=.
  move=> g b1 b2 bcin E l1 l2 lcin g' cs lcout lr.
  case => _ <- <- <-. move=> {g' cs lcout lr}.
  rewrite /enc_bit /=. rewrite !interp_lit_neg_lit.
  move=> /eqP -> /eqP -> /eqP -> H. split_andb. split.
  - move: H0 H1 H2 H3 H4 H5 H6 H7 {H8 H9 H10 H11 H12 H13}.
      by case: (E g); case: b1; case: b2; case: bcin.
  - move: {H0 H1 H2 H3 H4 H5 H6 H7} H8 H9 H10 H11 H12 H13.
      by case: (E (g + 1)%positive); case: b1; case: b2; case: bcin.
Qed.

Lemma bit_blast_full_adder1_correct2 :
  forall g b1 b2 bcin bcout br E l1 l2 lcin g' cs lcout lr,
    bit_blast_full_adder1 g l1 l2 lcin = (g', cs, lcout, lr) ->
    enc_bit E l1 b1 -> enc_bit E l2 b2 -> enc_bit E lcin bcin ->
    interp_cnf E (add_prelude cs) ->
    fullAdder bcin b1 b2 = (bcout, br) ->
    enc_bit E lr br /\
    enc_bit E lcout bcout.
Proof.
  rewrite /bit_blast_full_adder1 /=.
  move=> g b1 b2 bcin bcout br E l1 l2 lcin g' cs lcout lr.
  case => _ <- <- <-. move=> {g' cs lcout lr}.
  rewrite /enc_bit /=. repeat rewrite interp_lit_neg_lit.
  move=> /eqP -> /eqP -> /eqP -> H. split_andb. move=> Hadd. split.
  - move: Hadd H0 H1 H2 H3 H4 H5 H6 H7 {H8 H9 H10 H11 H12 H13}.
    rewrite /fullAdder.
      by case: (E g); case: b1; case: b2; case: bcin; case; move=> _ <- /=.
  - move: Hadd {H0 H1 H2 H3 H4 H5 H6 H7} H8 H9 H10 H11 H12 H13.
      by case: (E (g + 1)%positive); case: b1; case: b2; case: bcin;
        case; move=> <- _.
Qed.

Fixpoint bit_blast_full_adder (g : generator) w lcin : w.-tuple literal -> w.-tuple literal -> generator * cnf * literal * w.-tuple literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(g_hd, cs_hd, lcout_hd, lrs_hd) := bit_blast_full_adder1 g ls1_hd ls2_hd lcin in
      let '(g_tl, cs_tl, lcout_tl, lrs_tl) := bit_blast_full_adder g_hd lcout_hd ls1_tl ls2_tl in
      (g_tl, cs_hd++cs_tl, lcout_tl, cons_tuple lrs_hd lrs_tl)
  else
    fun _ _ =>
        (g, [::], lcin, [tuple]).

Fixpoint mk_env_full_adder w E (g: generator) (lcin : literal) : w.-tuple literal -> w.-tuple literal -> env * generator * cnf * literal * w.-tuple literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(E_hd, g_hd, cs_hd, lcout_hd, lrs_hd) := mk_env_full_adder1 E g ls1_hd ls2_hd lcin in
      let '(E_tl, g_tl, cs_tl, lcout_tl, lrs_tl) := mk_env_full_adder E_hd g_hd lcout_hd ls1_tl ls2_tl in
      (E_tl, g_tl, cs_hd++cs_tl, lcout_tl, cons_tuple lrs_hd lrs_tl)
  else
    fun _ _ =>
      (E, g, [::], lcin, [tuple]).

Lemma bit_blast_full_adder_correct :
  forall w g (bv1 bv2 : BITS w) bcin bcout brs E (ls1 ls2 : w.-tuple literal) lcin g' cs lcout lrs,
    bit_blast_full_adder g lcin ls1 ls2 = (g', cs, lcout, lrs) ->
    enc_bits E ls1 bv1 -> enc_bits E ls2 bv2 -> enc_bit E lcin bcin ->
    interp_cnf E (add_prelude cs) ->
    adcB bcin bv1 bv2 = (bcout, brs) ->
    enc_bits E lrs brs /\ enc_bit E lcout bcout.
Proof.
  elim.
  - move=> g bv1 bv2 bcin.
    move=> bout brs E ls1 ls2 lcin g' cs lcout lrs Hadd Henc1 Henc2 Hencin Hcs HadcB.
    split; first by done.
    rewrite /bit_blast_full_adder in Hadd.
    case: Hadd => _ _ <- _. Local Transparent adcB. rewrite /adcB /= in HadcB.
    case: HadcB => <- _. exact: Hencin.
  - (* prefix i for initial input, Prefix o for final output. *)
    move=> n IH ig.
    case/tupleP => ibv1_hd ibv1_tl. case/tupleP => ibv2_hd ibv2_tl.
    move=> ibcin obcout. case/tupleP => obrs_hd obrs_tl. move=> E.
    case/tupleP => ils1_hd ils1_tl. case/tupleP => ils2_hd ils2_tl.
    move=> ilcin og ocs olcout. case/tupleP => olrs_hd olrs_tl.
    (* unfold the bit-blasting steps *)
    rewrite /bit_blast_full_adder (lock bit_blast_full_adder1) (lock interp_cnf)
            /= -!lock. rewrite -/bit_blast_full_adder.
    rewrite !theadE !beheadCons.
    case Hbit_blast_hd: (bit_blast_full_adder1 ig ils1_hd ils2_hd ilcin) =>
      [[[g_hd cs_hd] lcout_hd] lrs_hd].
    case Hbit_blast_tl: (bit_blast_full_adder g_hd lcout_hd ils1_tl ils2_tl) =>
      [[[g_tl cs_tl] lcout_tl] lrs_tl].
    move=> [] Hog Hocs Holcout Holrs_hd Holrs_tl.
    (* == *)
    (* the results of bit-blasting tl are the final outputs *)
    move=> {Hog og}. rewrite -Hocs => {Hocs ocs}.
    rewrite -Holcout => {Holcout olcout}. rewrite -Holrs_hd => {Holrs_hd olrs_hd}.
    (* == *)
    move=> /andP [Henc1_hd Henc1_tl] /andP [Henc2_hd Henc2_tl] Hencin Hcnf.
    rewrite add_prelude_append in Hcnf. move/andP: Hcnf => [Hcnf_hd Hcnf_tl].
    (* unfold the adcB steps *)
    rewrite /adcB /= !theadE !beheadCons.
    case HadcB_hd: (fullAdder ibcin ibv1_hd ibv2_hd) => [bcout_hd brs_hd].
    pose adcb_tl_res := (adcBmain bcout_hd ibv1_tl ibv2_tl).
    rewrite theadE beheadCons /=.
    case Hsplitmsb: (spec.splitmsb adcb_tl_res) => [adcb_res_msb adcb_res].
    move=> [] Hadcb_msb Hbrs_hd Hadcb_res.
    (* == *)
    (* the results of adcBmain tl are the final outputs *)
    rewrite -Hadcb_msb => {Hadcb_msb obcout}. rewrite -Hbrs_hd => {Hbrs_hd obrs_hd}.
    (* == *)
    move: (bit_blast_full_adder1_correct2
             Hbit_blast_hd Henc1_hd Henc2_hd
             Hencin Hcnf_hd HadcB_hd) => [Henc_rs_hd Henc_cout_hd].
    move: (IH g_hd ibv1_tl ibv2_tl bcout_hd adcb_res_msb adcb_res E ils1_tl ils2_tl
              lcout_hd g_tl cs_tl lcout_tl lrs_tl Hbit_blast_tl
              Henc1_tl Henc2_tl Henc_cout_hd Hcnf_tl).
    have: adcB bcout_hd ibv1_tl ibv2_tl = (adcb_res_msb, adcb_res).
    {
      rewrite /adcB -Hsplitmsb. reflexivity.
    }
    Local Opaque adcB.
    move=> {IH} H IH. move: (IH H) => {IH H} [H1 H2]. split.
    + rewrite Henc_rs_hd. rewrite (enc_bits_val_eq H1 Holrs_tl Hadcb_res). done.
    + exact: H2.
Qed.

Corollary bit_blast_full_adder_correct1 :
  forall w g (bv1 bv2 : BITS w) bcin bcout brs E (ls1 ls2 : w.-tuple literal) lcin g' cs lcout lrs,
    bit_blast_full_adder g lcin ls1 ls2 = (g', cs, lcout, lrs) ->
    enc_bits E ls1 bv1 -> enc_bits E ls2 bv2 -> enc_bit E lcin bcin ->
    interp_cnf E (add_prelude cs) ->
    adcB bcin bv1 bv2 = (bcout, brs) ->
    enc_bits E lrs brs.
Proof.
  move=> w g bv1 bv2 bcin bcout brs E ls1 ls2 lcin g' cs lcout lrs.
  move=> Hblast Henc1 Henc2 Hencin Hcs Hbrs.
  move: (bit_blast_full_adder_correct Hblast Henc1 Henc2 Hencin Hcs Hbrs).
  move=> [H1 H2]; exact: H1.
Qed.

Corollary bit_blast_full_adder_correct2 :
  forall w g (bv1 bv2 : BITS w) bcin bcout brs E (ls1 ls2 : w.-tuple literal) lcin g' cs lcout lrs,
    bit_blast_full_adder g lcin ls1 ls2 = (g', cs, lcout, lrs) ->
    enc_bits E ls1 bv1 -> enc_bits E ls2 bv2 -> enc_bit E lcin bcin ->
    interp_cnf E (add_prelude cs) ->
    adcB bcin bv1 bv2 = (bcout, brs) ->
    enc_bit E lcout bcout.
Proof.
  move=> w g bv1 bv2 bcin bcout brs E ls1 ls2 lcin g' cs lcout lrs.
  move=> Hblast Henc1 Henc2 Hencin Hcs Hbrs.
  move: (bit_blast_full_adder_correct Hblast Henc1 Henc2 Hencin Hcs Hbrs).
  move=> [H1 H2]; exact: H2.
Qed.

Lemma mk_env_full_adder_is_bit_blast_full_adder :
  forall w E g lcin (ls1 ls2 : w.-tuple literal) E' g' cs lcout lrs,
    mk_env_full_adder E g lcin ls1 ls2 = (E', g', cs, lcout, lrs) ->
    bit_blast_full_adder g lcin ls1 ls2 = (g', cs, lcout, lrs).
Proof.
  elim.
  - rewrite /mk_env_full_adder/bit_blast_full_adder/= => E g lcin ls1 ls2 E' g' cs lcout lrs.
     by case => _ <- <- <- <-.
  - intros_tuple. dcase_hyps; subst. move => Hls.
    rewrite (H _ _ _ _ _ _ _ _ _ _ H0). by rewrite (tval_eq Hls).
Qed.

Lemma mk_env_full_adder1_newer_gen :
  forall E g cin l1 l2 E' g' cs cout lr,
    mk_env_full_adder1 E g cin l1 l2 = (E', g', cs, cout, lr) ->
    (g <=? g')%positive.
Proof.
  move => E g cin l1 l2 E' g' cs cout lr [] _ <- _ _ _.
  rewrite -Pos.add_assoc. exact: (pos_leb_add_diag_r g (1+1)).
Qed.

Lemma mk_env_full_adder_newer_gen :
  forall w E g lcin (ls1 ls2: w.-tuple literal) E' g' cs cout lrs,
    mk_env_full_adder E g lcin ls1 ls2 = (E', g', cs, cout, lrs) ->
    (g <=? g')%positive.
Proof.
  elim.
  - move => E g lcin ls1 ls2 E' g' cs cout lrs [] _ <- _ _ _.
    exact: Pos.leb_refl.
  - intros_tuple. dcase_hyps; subst. move => Hls.
    move : (H _ _ _ _ _ _ _ _ _ _ H0) => IHm.
    apply: (pos_leb_trans _ IHm). rewrite -Pos.add_assoc.
    exact: (pos_leb_add_diag_r g (1+1)).
Qed.

Lemma mk_env_full_adder_newer_res :
  forall w E g lcin (ls1 ls2: w.-tuple literal) E' g' cs cout lrs,
    mk_env_full_adder E g lcin ls1 ls2 = (E', g', cs, cout, lrs) ->
    newer_than_lits g' lrs.
Proof.
  elim.
  - move => E g lcin ls1 ls2 E' g' cs cout lrs [] _ <- _ _ <-.
    done.
  - intros_tuple. dcase_hyps; subst. move => Hls.
    move : (H _ _ _ _ _ _ _ _ _ _ H0) => IHm. rewrite -Hls.
    rewrite IHm andbT.
    move: (mk_env_full_adder_newer_gen H0) => Hg1g. apply: (newer_than_var_le_newer _ Hg1g).
    rewrite -Pos.add_assoc.
    exact: newer_than_var_add_diag_r.
Qed.

Lemma mk_env_full_adder_newer_cout :
  forall w E g lcin (ls1 ls2: w.-tuple literal) E' g' cs cout lrs,
    mk_env_full_adder E g lcin ls1 ls2 = (E', g', cs, cout, lrs) ->
    newer_than_lit g lcin ->
    newer_than_lit g' cout.
Proof.
  elim.
  - move => E g lcin ls1 ls2 E' g' cs cout lrs [] _ <- _ <- _.
    done.
  - intros_tuple. dcase_hyps; subst. move => Hlrs.
    rewrite (H _ _ _ _ _ _ _ _ _ _ H0). done.
    exact : newer_than_var_add_diag_r.
Qed.

Lemma mk_env_full_adder_newer_cnf :
  forall w E g lcin (ls1 ls2: w.-tuple literal) E' g' cs cout lrs,
    mk_env_full_adder E g lcin ls1 ls2 = (E', g', cs, cout, lrs) ->
    newer_than_lit g lcin ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  elim.
  - move => E g lcin ls1 ls2 E' g' cs cout lrs [] _ <- <- _ _ Hnewcin Hnewls1 Hnewls2.
    done.
  - intros_tuple. dcase_hyps; subst. move => Hls.
    rewrite /=!newer_than_lit_neg.
    move/andP: H2 => [Hnewls1 Hnewls0]; move/andP: H3 => [Hnewls2 Hnewls3].
    move: (mk_env_full_adder_newer_gen H0) => Hg11. rewrite -Pos.add_assoc in Hg11.
    move: (newer_than_lit_add_r (1+1) H1) => Hnewg11lcin.
    move: (newer_than_lit_add_r (1+1) Hnewls1) => Hnewg11ls1.
    move: (newer_than_lit_add_r (1+1) Hnewls2) => Hnewg11ls2.
    move: (newer_than_lits_add_r (1+1) Hnewls3) => Hnewg11ls3. rewrite Pos.add_assoc in Hnewg11ls3.
    move: (newer_than_lits_add_r (1+1) Hnewls0) => Hnewg11ls0. rewrite Pos.add_assoc in Hnewg11ls0.
    assert ((g + 1 <? g + 1 + 1)%positive) as Hg1g11 by exact: (pos_ltb_add_diag_r (g+1) 1).
    move : (H  _ _ _ _ _ _ _ _ _ _ H0 Hg1g11 Hnewg11ls0 Hnewg11ls3) => Hnew.
    move: (newer_than_lit_le_newer Hnewg11lcin Hg11) => ->.
    move: (newer_than_lit_le_newer Hnewg11ls1 Hg11) => ->.
    move: (newer_than_lit_le_newer Hnewg11ls2 Hg11) => ->.
    rewrite Hnew /newer_than_lit/newer_than_var/=.
    rewrite (pos_ltb_leb_trans (pos_ltb_add_diag_r g (1+1)) Hg11).
    rewrite Pos.add_assoc in Hg11.
    rewrite (pos_ltb_leb_trans (pos_ltb_add_diag_r (g+1) 1) Hg11).
    done.
Qed.

Lemma mk_env_full_adder1_preserve :
  forall E g cin l1 l2 E' g' cs cout lr,
    mk_env_full_adder1 E g cin l1 l2 = (E', g', cs, cout, lr) ->
    env_preserve E E' g.
Proof.
  move=> E g cin l1 l2 E' g' cs cout lr /=.
  case=> <- _ _ _ _.
  apply (@env_preserve_trans _ (env_upd E g
          (xorb (xorb (interp_lit E cin) (interp_lit E l1))
                (interp_lit E l2)))).
  - exact: env_upd_eq_preserve.
  - apply env_upd_newer_preserve; by apply newer_than_var_add_diag_r.
Qed.

Lemma mk_env_full_adder_preserve :
  forall w E g lcin (ls1 ls2 : w.-tuple literal) E' g' cs cout lrs,
    mk_env_full_adder E g lcin ls1 ls2 = (E', g', cs, cout, lrs) ->
    env_preserve E E' g.
Proof.
  elim.
  - move=> E g lcin ls1 ls2 E' g' cs cout lrs /=.
    case=> <- _ _ _ _. exact: env_preserve_refl.
  - intros_tuple. dcase_hyps; subst. move => Hls.
    move: (H _ _ _ _ _ _ _ _ _ _ H0) => Hpre.
    move :(env_preserve_env_upd_succ Hpre) => Hpre1.
    exact :(env_preserve_env_upd_succ Hpre1).
Qed.

Lemma mk_env_full_adder_sat :
  forall w E g lcin (ls1 ls2 : w.-tuple literal) E' g' cs cout lrs,
    mk_env_full_adder E g lcin ls1 ls2 = (E', g', cs, cout, lrs) ->
    newer_than_lit g lcin -> newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  elim.
  - move => E g lcin ls1 ls2 E' g' cs cout lrs [] <- -> <- _ _ Hlcin Hls1 Hls2.
    done.
  - intros_tuple. dcase_hyps; subst. rewrite !interp_cnf_cons. move => Hls.
    move/andP : H2 => [Hnewls1 Hnewls0]; move/andP : H3=> [Hnewls2 Hnewls3].
    move : (newer_than_lit_le_newer H1 (pos_leb_add_diag_r g (1+1))) => Hnewlcin. rewrite Pos.add_assoc in Hnewlcin.
    move : (newer_than_lit_le_newer H1 (pos_leb_add_diag_r g (1))) => Hnew1lcin.
    move : (newer_than_lits_le_newer Hnewls0 (pos_leb_add_diag_r (g) (1+1))) => Hnewg11ls0. rewrite Pos.add_assoc in Hnewg11ls0.
    move : (newer_than_lits_le_newer Hnewls3 (pos_leb_add_diag_r g (1+1))) => Hnewg11ls3. rewrite Pos.add_assoc in Hnewg11ls3.
    move : (newer_than_lit_le_newer Hnewls1 (pos_leb_add_diag_r g (1+1))) => Hnewg11ls1. rewrite Pos.add_assoc in Hnewg11ls1.
    move : (newer_than_lit_le_newer Hnewls1 (pos_leb_add_diag_r g (1))) => Hnewg1ls1.
    move : (newer_than_lit_le_newer Hnewls2 (pos_leb_add_diag_r g (1+1))) => Hnewg11ls2. rewrite Pos.add_assoc in Hnewg11ls2.
    move : (newer_than_lit_le_newer Hnewls2 (pos_leb_add_diag_r g (1))) => Hnewg1ls2.
    move : (pos_ltb_add_diag_r (g+1) 1) => Hg11.
    move: (H _ _ _ _ _ _ _ _ _ _ H0 Hg11 Hnewg11ls0 Hnewg11ls3) => Hcnfcs0.
    rewrite /= Hcnfcs0 !interp_lit_neg_lit andbT /=.
    move : (mk_env_full_adder_preserve H0) => Hpre1.
    move : (Hpre1 (g+1)%positive (newer_than_var_add_diag_r (g+1) 1)).
    rewrite !env_upd_eq.
    move : (Hpre1 g). rewrite -Pos.add_assoc.
    move => H2. move : (H2 (newer_than_var_add_diag_r (g) (1+1))).
    rewrite env_upd_neq. rewrite env_upd_eq.
    move : (env_preserve_lit Hpre1 Hnewg11ls2).
    rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hnewg1ls2)).
    rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hnewls2)).
    move : (env_preserve_lit Hpre1 Hnewg11ls1).
    rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hnewg1ls1)).
    rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hnewls1)).
    move : (env_preserve_lit Hpre1 Hnewlcin).
    rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hnew1lcin)).
    rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq H1)).
    move => -> -> -> -> ->.
    by case: (interp_lit E lcin); case: (interp_lit E ls1); case: (interp_lit E ls2).
    apply/eqP/not_eq_sym. move : (Pos.succ_discr g). rewrite Pplus_one_succ_r.
    done.
Qed.



(* ===== bit_blast_add ===== *)

Definition bit_blast_add w g ls1 ls2 : generator * cnf * w.-tuple literal :=
  let '(g', cs, cout, lrs) := bit_blast_full_adder g lit_ff ls1 ls2 in
  (g', cs, lrs).

Lemma bit_blast_add_correct :
  forall w g (bs1 bs2 : BITS w) E ls1 ls2 br g' cs lrs,
    bit_blast_add g ls1 ls2 = (g', cs, lrs) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    addB bs1 bs2 = br->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs br.
Proof.
  move=> n g bs1 bs2 E ls1 ls2 br g' cs lrs.
  rewrite /bit_blast_add. case HadcB: (adcB false bs1 bs2) => [obcout obrs].
  case Hblast: (bit_blast_full_adder g lit_ff ls1 ls2) => [[[og ocs] olcout] olrs].
  case=> _ <- <- => Henc1 Henc2 <- Hcs.
  apply: (bit_blast_full_adder_correct1 Hblast Henc1 Henc2 _ Hcs HadcB).
  exact: (add_prelude_enc_bit_ff Hcs).
Qed.

Definition mk_env_add w E (g: generator) ls1 ls2 : env * generator * cnf * w.-tuple literal :=
  let '(E', g', cs, cout, lrs) := mk_env_full_adder E g lit_ff ls1 ls2 in
  (E', g', cs, lrs).

Lemma mk_env_add_is_bit_blast_add :
  forall w E g  (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_add E g ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_add g ls1 ls2 = (g', cs, lrs).
Proof.
  move =>  w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_add/bit_blast_add.
  case Hmk: (mk_env_full_adder E g lit_ff ls1 ls2 ) => [[[[E'0 g'0] cs0] cout] lrs0].
  move : (mk_env_full_adder_is_bit_blast_full_adder Hmk) => Hbb.
  rewrite Hbb. move =>[] _ <- <- <-.
  done.
Qed.

Lemma mk_env_add_newer_gen :
  forall w E g  (ls1 ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_add E g ls1 ls2 = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move =>  w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_add.
  case Hmk: (mk_env_full_adder E g lit_ff ls1 ls2) => [[[[E'0 g'0] cs0] cout] lrs0]. move => [] _ <- _ _.
  apply (mk_env_full_adder_newer_gen Hmk).
Qed.

Lemma mk_env_add_newer_res :
  forall  w E g  (ls1 ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_add E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lits g' lrs.
Proof.
  move =>  w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_add.
  case Hmk: (mk_env_full_adder E g lit_ff ls1 ls2) => [[[[E'0 g'0] cs0] cout] lrs0]. move => [] _ <- _ <-.
  apply (mk_env_full_adder_newer_res Hmk).
Qed.

Lemma mk_env_add_newer_cnf:
  forall  w E g  (ls1 ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_add E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lit_ff ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  move =>  w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_add.
  case Hmk: (mk_env_full_adder E g lit_ff ls1 ls2) => [[[[E'0 g'0] cs0] cout] lrs0]. move => [] _ <- <- _.
  apply (mk_env_full_adder_newer_cnf Hmk).
Qed.

Lemma mk_env_add_preserve :
  forall  w E g  (ls1 ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_add E g ls1 ls2 = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move =>  w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_add.  case Hmk: (mk_env_full_adder E g lit_ff ls1 ls2) => [[[[E'0 g'0] cs0] cout] lrs0]. move => [] <- _ _ _.
  apply (mk_env_full_adder_preserve Hmk).
Qed.

Lemma mk_env_add_sat :
  forall  w E g  (ls1 ls2: w.-tuple literal) E' g' cs lrs,
    mk_env_add E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lit_ff -> newer_than_lits g ls1 ->  newer_than_lits g ls2 -> interp_cnf E' cs.
Proof.
  move =>  w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_add.  case Hmk: (mk_env_full_adder E g lit_ff ls1 ls2) => [[[[E'0 g'0] cs0] cout] lrs0]. move => [] <- _ <- _.
  apply (mk_env_full_adder_sat Hmk).
Qed.
