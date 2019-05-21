
(*
 * Require the following libraries:
 * - coq-bit from https://github.com/mht208/coq-bits
 * - ssrlib from https://github.com/mht208/coq-ssrlib.git
 *)

From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From BitBlasting Require Import QFBVSimple CNF.
From ssrlib Require Import Bools Var Store SsrOrdered ZAriths.
From Bits Require Export bits ssrextra.tuple.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Module Arch64 : Arch.
  Definition wordsize := 64.
  Lemma wordsize_positive : wordsize > 0.
  Proof.
    done.
  Qed.
End Arch64.
Module QFBV64 := QFBVSimple.Make VarOrder Arch64.
Notation wordsize := Arch64.wordsize.



Definition cnf_lit_not a := [[neg_lit a]].
Definition cnf_lit_xor a1 a2 := [[a1; a2]; [neg_lit a1; neg_lit a2]].
Definition cnf_lit_eq a1 a2 := [[neg_lit a1; a2]; [a1; neg_lit a2]].

Lemma cnf_lit_xor_correct :
  forall b1 b2 E l1 l2,
    enc_bit E l1 b1 -> enc_bit E l2 b2 ->
    interp_cnf E (cnf_lit_xor l1 l2) ->
    b1 != b2.
Proof.
  move=> b1 b2 E l1 l2. rewrite /enc_bit /cnf_lit_xor /=.
  rewrite !interp_literal_neg_lit.
  case: b1; case: b2; try reflexivity.
  - move=> /eqP -> /eqP ->. done.
  - move=> /eqP -> /eqP ->. done.
Qed.

Lemma cnf_lit_eq_correct :
  forall b1 b2 E l1 l2,
    enc_bit E l1 b1 -> enc_bit E l2 b2 ->
    interp_cnf E (cnf_lit_eq l1 l2) ->
    b1 = b2.
Proof.
  move=> b1 b2 E l1 l2. rewrite /enc_bit /cnf_lit_eq /=.
  rewrite !interp_literal_neg_lit.
  case: b1; case: b2; try reflexivity.
  - move=> /eqP -> /eqP ->. done.
  - move=> /eqP -> /eqP ->. done.
Qed.

Ltac split_andb :=
  repeat (match goal with
          | H : is_true (andb ?l ?r) |- _ => move/andP: H;
                                             let H1 := fresh in
                                             let H2 := fresh in
                                             move=> [H1 H2]
          end).

Definition generator := positive.

Definition gen (g : generator) : generator * literal := (g + 1, Pos g)%positive.

Definition newer_than_vm w g (m : VM.t (w.-tuple literal)) :=
  forall v rs, VM.find v m = Some rs -> newer_than_lits g rs.

Lemma newer_than_vm_add_diag_r :
  forall w x (m : VM.t (w.-tuple literal)) y,
    newer_than_vm x m -> newer_than_vm (x + y) m.
Proof.
  move=> w x m y Hnew v rs Hfind. move: (Hnew v rs Hfind).
  exact: newer_than_lits_add_diag_r.
Qed.

Lemma newer_than_vm_le_newer :
  forall w x (m : VM.t (w.-tuple literal)) y,
    newer_than_vm x m -> (x <=? y)%positive -> newer_than_vm y m.
Proof.
  move=> w x m y Hnew Hle v rs Hfind. move: (Hnew v rs Hfind) => {Hnew} Hnew.
  exact: (newer_than_lits_le_newer Hnew Hle).
Qed.

Definition consistent1 m E s v : Prop :=
    match VM.find v m with
    | None => True
    | Some rs => @enc_bits E wordsize rs (QFBV64.State.acc v s)
    end.
Definition consistent m E s := forall v, consistent1 m E s v.

Lemma consistent_env_upd_newer :
  forall m s E g g' b,
    newer_than_vm g m ->
    consistent m E s ->
    (g <=? g')%positive ->
    consistent m (env_upd E g' b) s.
Proof.
  move=> m s E g g' b Hnew Hcon Hle.
  move: (newer_than_vm_le_newer Hnew Hle) => Hnew'. move=> v.
  move: (Hnew' v) (Hcon v) => {Hnew Hnew' Hcon}.
  rewrite /consistent1. case: (VM.find v m); last by done.
  move=> rs Hnew Henc. move: (Hnew rs (Logic.eq_refl (Some rs))) => {Hnew} Hnew.
  rewrite (newer_than_lits_enc_bits_env_upd _ _ _ Hnew). exact: Henc.
Qed.



(* ===== bit_blast_var ===== *)

Fixpoint bit_blast_var' (g : generator) w : generator * w.-tuple literal :=
  match w with
  | O => (g, [tuple])
  | S n => let (g', hd) := gen g in
           let (g'', tl) := bit_blast_var' g' n in
           (g'', cons_tuple hd tl)
  end.

Definition bit_blast_var g (v : var) : generator * cnf * wordsize.-tuple literal :=
  let (g', vs) := bit_blast_var' g wordsize in
  (g, [], vs).

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

Definition mk_env_var E g (bv : BITS wordsize) (v : var) : env * generator * cnf * wordsize.-tuple literal :=
  let '(E', g', vs) := mk_env_var' E g bv in
  (E', g, [], vs).

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
  move=> E g bs v E' g' cs lrs. rewrite /mk_env_var /bit_blast_var.
  case Hmk_env: (mk_env_var' E g bs) => [[oE_env og_env] ovs_env].
  case=> _ <- <- <-. rewrite (mk_env_var'_is_bit_blast_var' Hmk_env).
  reflexivity.
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

Lemma mk_env_var'_env_preserve :
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

Lemma mk_env_var_env_preserve :
  forall E g (bs : BITS wordsize) v E' g' cs lrs,
    mk_env_var E g bs v = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> E g bs v E' g' cs lrs. rewrite /mk_env_var.
  case H: (mk_env_var' E g bs) => [[oE og] olrs].
  case=> <- _ _ _. exact: (mk_env_var'_env_preserve H).
Qed.

Lemma mk_env_var_newer :
  forall E g (bs : BITS wordsize) v E' g' cs lrs,
    mk_env_var E g bs v = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> E g bs v E' g' cs lrs. rewrite /mk_env_var.
  case H: (mk_env_var' E g bs) => [[oE og] olrs]. case=> _ <- _ _.
  exact: Pos.leb_refl.
Qed.



(* ===== bit_blast_const ===== *)

Definition bit_blast_const w g (n : BITS w) : generator * cnf * w.-tuple literal :=
  (g, [], map_tuple (fun b => if b then lit_tt else lit_ff) n).

Definition mk_env_const w E g (n : BITS w) : env * generator * cnf * w.-tuple literal :=
  (E, g, [], map_tuple (fun b => if b then lit_tt else lit_ff) n).

Lemma bit_blast_const_correct :
  forall w g (bv : BITS w) E g' cs ls,
    bit_blast_const g bv = (g', cs, ls) ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E ls bv.
Proof.
  rewrite /bit_blast_const /add_prelude. elim; first by done.
  move=> w IH g. case/tupleP => bv_hd bv_tl E g' cs.
  case/tupleP => ls_hd ls_tl. move=> [] Hg Hcs Hls_hd Hls_tl.
  rewrite -Hcs. move=> /= Hprelude. rewrite !theadE !beheadCons. apply/andP; split.
  - rewrite -{}Hls_hd /enc_bit. case: bv_hd => /=; by rewrite Hprelude.
  - apply: (IH _ _ E g' []); last by rewrite /interp_cnf /= Hprelude.
    rewrite -Hg. apply: injective_projections => /=; first by reflexivity.
    apply: val_inj; rewrite /=. exact: Hls_tl.
Qed.

Lemma mk_env_const_is_bit_blast_env :
  forall w E g (bv : BITS w) E' g' cs ls,
    mk_env_const E g bv = (E', g', cs, ls) ->
    bit_blast_const g bv = (g', cs, ls).
Proof.
  move=> w E g bv E' g' cs ls. rewrite /mk_env_const /bit_blast_const.
  case => _ <- <- <-. reflexivity.
Qed.

Lemma mk_env_cont_sat :
  forall w E g (bv : BITS w) E' g' cs lrs,
    mk_env_const E g bv = (E', g', cs, lrs) ->
    interp_cnf E' cs.
Proof.
  rewrite /mk_env_const=> w E g bv E' g' cs lrs.
  case=> <- _ <- _. done.
Qed.

Lemma mk_env_const_env_preserve :
  forall w E g (bv : BITS w) E' g' cs lrs,
    mk_env_const E g bv = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> w E g bv E' g' cs lrs. case=> <- _ _ _. exact: env_preserve_refl.
Qed.

Lemma mk_env_const_newer :
  forall w E g (bv : BITS w) E' g' cs lrs,
    mk_env_const E g bv = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> w E g bv E' g' cs lrs. case=> _ <- _ _. exact: Pos.leb_refl.
Qed.



(* bit_blast_not *)

Definition bit_blast_not1 (g: generator) (a:literal) : generator * cnf * literal :=
  let (g', r):= gen g in
  let cs := [
        [r; a]; [neg_lit r; neg_lit a]
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
      (g, [], [tuple]).

Parameter mk_env_not : forall w : nat, env -> generator -> BITS w -> w.-tuple literal -> env * generator * cnf * w.-tuple literal.

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
  rewrite -Hlr -{}Hcs /= => {Hg' Hlr g' cs}. rewrite !interp_literal_neg_lit.
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

Lemma mk_env_not_is_bit_blast_not :
  forall w E g (bs : BITS w) ls E' g' cs lrs,
    mk_env_not E g bs ls = (E', g', cs, lrs) ->
    bit_blast_not g ls = (g', cs, lrs).
Proof.
Admitted.



(* ===== bit_blast_and ===== *)

Definition bit_blast_and1 (g: generator) (a1 a2: literal) : generator * cnf * literal :=
  if (a1 == lit_ff) || (a2 == lit_ff) then (g, [], lit_ff)
  else if a1 == lit_tt then (g, [], a2)
       else if a2 == lit_tt then (g, [], a1)
            else let (g', r) := gen g in
                 let cs := [[neg_lit r; a1]; [neg_lit r; a2];
                              [r; neg_lit a1; neg_lit a2]] in
                 (g', cs, r).

Definition mk_env_and1 E g b1 b2 a1 a2 : env * generator * cnf * literal :=
  if (a1 == lit_ff) || (a2 == lit_ff) then (E, g, [], lit_ff)
  else if a1 == lit_tt then (E, g, [], a2)
       else if a2 == lit_tt then (E, g, [], a1)
            else let (g', r) := gen g in
                 let E' := env_upd E (var_of_lit r) (b1 && b2) in
                 let cs := [[neg_lit r; a1]; [neg_lit r; a2];
                              [r; neg_lit a1; neg_lit a2]] in
                 (E', g', cs, r).

Fixpoint bit_blast_and w (g: generator): w.-tuple literal -> w.-tuple literal -> generator * cnf * w.-tuple literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(g_hd, cs_hd, lrs_hd) := bit_blast_and1 g ls1_hd ls2_hd in
      let '(g_tl, cs_tl, lrs_tl) := bit_blast_and g_hd ls1_tl ls2_tl in
      (g_tl, cs_hd++cs_tl, cons_tuple lrs_hd lrs_tl)
  else
    fun _ _ =>
      (g, [], [tuple]).

Fixpoint mk_env_and w (E : env) (g : generator) : BITS w -> BITS w -> w.-tuple literal -> w.-tuple literal -> env * generator * cnf * w.-tuple literal :=
  if w is _.+1 then
    fun bs1 bs2 ls1 ls2 =>
      let (bs1_tl, bs1_hd) := eta_expand (splitlsb bs1) in
      let (bs2_tl, bs2_hd) := eta_expand (splitlsb bs2) in
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(E_hd, g_hd, cs_hd, lrs_hd) := mk_env_and1 E g bs1_hd bs2_hd ls1_hd ls2_hd in
      let '(E_tl, g_tl, cs_tl, lrs_tl) := mk_env_and E_hd g_hd bs1_tl bs2_tl ls1_tl ls2_tl in
      (E_tl, g_tl, cs_hd++cs_tl, cons_tuple lrs_hd lrs_tl)
  else
    fun _ _ _ _ =>
      (E, g, [], [tuple]).

Lemma bit_blast_and1_correct :
  forall g b1 b2 br E l1 l2 g' cs lr,
    bit_blast_and1 g l1 l2 = (g', cs, lr) ->
    enc_bit E l1 b1 -> enc_bit E l2 b2 ->
    interp_cnf E (add_prelude cs) ->
    andb b1 b2 = br ->
    enc_bit E lr br.
Proof.
  move => g b1 b2 br E l1 l2 g' cs lr. rewrite /bit_blast_and1 /enc_bit.
  case Hff: ((l1 == lit_ff) || (l2 == lit_ff)).
  - case => _ <- <- /eqP <- /eqP <- /= Htt <-.
    move/orP: Hff; case => /eqP -> /=; rewrite Htt.
    + done.
    + by rewrite andbF.
  - case Htt1: (l1 == lit_tt); last case Htt2: (l2 == lit_tt).
    + case=> _ <- <- /eqP <- /eqP <- /= Htt <-.
      rewrite (eqP Htt1) /= Htt. exact: eqxx.
    + case=> _ <- <- /eqP <- /eqP <- /= Htt <-.
      rewrite (eqP Htt2) /= Htt. by rewrite andbT.
    + case => _ <- <-. move=> /eqP <- /eqP <- /andP /= [Htt Hcs] <-.
      rewrite !interp_literal_neg_lit in Hcs. move: Hcs.
      by case: (E g); case: (interp_literal E l1); case: (interp_literal E l2).
Qed.

Lemma bit_blast_and_correct :
  forall w g (bs1 bs2 : BITS w) E ls1 ls2 g' cs lrs,
    @bit_blast_and w g ls1 ls2 = (g', cs, lrs) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (andB bs1 bs2).
Proof.
  elim.
  - done.
  - move => n IH g. case/tupleP =>[ibs1_hd ibs1_tl]. case/tupleP =>[ibs2_hd ibs2_tl].
    move => E. case/tupleP =>[ils1_hd ils1_tl]. case/tupleP =>[ils2_hd ils2_tl].
    move => og cs. case/tupleP =>[ilrs1_hd ilrs1_tl].
    rewrite /bit_blast_and -/bit_blast_and (lock bit_blast_and)
            (lock bit_blast_and1) (lock interp_cnf)  /= !theadE !beheadCons -!lock.
    case Hand_hd: (bit_blast_and1 g ils1_hd ils2_hd) =>[ [g_hd cs_hd] lrs_hd].
    case Hand_tl: (bit_blast_and g_hd ils1_tl ils2_tl) =>[ [g_tl cs_tl] lrs_tl].
    case => Hog <- Holrs_hd Holrs_tl => {cs}.
    move => /andP [Henc1_hd Henc1_tl] /andP [Henc2_hd Hen2_tl] Hcnf.
    rewrite add_prelude_append in Hcnf. move/andP: Hcnf => [Hcnf_hd Hcnf_tl].
    rewrite /andB. rewrite liftBinOpCons /=. rewrite /= !theadE !beheadCons.
    apply/andP; split.
    + rewrite -Holrs_hd.
      exact: (bit_blast_and1_correct Hand_hd Henc1_hd Henc2_hd Hcnf_hd).
    + apply: (IH g_hd ibs1_tl ibs2_tl E ils1_tl ils2_tl
                  g_tl cs_tl ilrs1_tl _ Henc1_tl Hen2_tl Hcnf_tl).
      rewrite Hand_tl. apply: injective_projections => /=; first by reflexivity.
      apply: val_inj. exact: Holrs_tl.
Qed.

Lemma mk_env_and1_is_bit_blast_and1 :
  forall E g (b1 b2 : bool) l1 l2 E' g' cs lr,
    mk_env_and1 E g b1 b2 l1 l2 = (E', g', cs, lr) ->
    bit_blast_and1 g l1 l2 = (g', cs, lr).
Proof.
  move=> iE ig ib1 ib2 il1 il2 oE og ocs olr.
  rewrite /mk_env_and1 /bit_blast_and1.
  case Hff: ((il1 == lit_ff) || (il2 == lit_ff)).
  - case=> _ <- <- <-. reflexivity.
  - case Htt1: (il1 == lit_tt); last case Htt2: (il2 == lit_tt).
    + case=> _ <- <- <-. reflexivity.
    + case=> _ <- <- <-. reflexivity.
    + case=> _ <- <- <-. rewrite /=. reflexivity.
Qed.

Lemma mk_env_and1_sat :
  forall E g (b1 b2 : bool) E' g' l1 l2 cs lr,
    mk_env_and1 E g b1 b2 l1 l2 = (E', g', cs, lr) ->
    enc_bit E l1 b1 -> enc_bit E l2 b2 ->
    newer_than_lit g l1 -> newer_than_lit g l2 ->
    interp_cnf E' cs.
Proof.
  move=> iE ig ib1 ib2 oE og il1 il2 ocs olr. rewrite /mk_env_and1.
  case Hff: ((il1 == lit_ff) || (il2 == lit_ff)).
  - case=> <- _ <- _. done.
  - case Htt1: (il1 == lit_tt); last case Htt2: (il2 == lit_tt).
    + case=> <- _ <- _. done.
    + case=> <- _ <- _. done.
    + case=> <- _ <- _. move=> Henc1 Henc2 Hg1 Hg2.
      rewrite /interp_cnf /interp_clause. rewrite !interp_literal_neg_lit.
      move: (newer_than_lit_neq Hg1) (newer_than_lit_neq Hg2) => Hil1 Hil2.
      rewrite (interp_literal_env_upd_neq iE _ Hil1)
              (interp_literal_env_upd_neq iE _ Hil2).
      rewrite (interp_literal_env_upd_eq_pos iE).
      rewrite (interp_literal_env_upd_eq_neg iE).
      rewrite /enc_bit in Henc1 Henc2.
      rewrite (eqP Henc1) (eqP Henc2) => {Henc1 Henc2}.
      by case: ib1; case: ib2.
Qed.

Lemma mk_env_and1_env_preserve :
  forall E g (b1 b2 : bool) E' g' l1 l2 cs lr,
    mk_env_and1 E g b1 b2 l1 l2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  move=> iE ig ib1 ib2 oE og il1 il2 ocs olr. rewrite /mk_env_and1.
  case Hff: ((il1 == lit_ff) || (il2 == lit_ff)).
  - case=> <- _ _ _. exact: env_preserve_refl.
  - case Htt1: (il1 == lit_tt); last case Htt2: (il2 == lit_tt).
    + case=> <- _ _ _. exact: env_preserve_refl.
    + case=> <- _ _ _. exact: env_preserve_refl.
    + case => <- _ _ _. exact: env_upd_eq_preserve.
Qed.

Lemma mk_env_and1_newer :
  forall E g (b1 b2 : bool) E' g' l1 l2 cs lr,
    mk_env_and1 E g b1 b2 l1 l2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  move=> iE ig ib1 ib2 oE og il1 il2 ocs olr. rewrite /mk_env_and1.
  case Hff: ((il1 == lit_ff) || (il2 == lit_ff)).
  - case=> _ <- _ _. exact: Pos.leb_refl.
  - case Htt1: (il1 == lit_tt); last case Htt2: (il2 == lit_tt).
    + case=> _ <- _ _. exact: Pos.leb_refl.
    + case=> _ <- _ _. exact: Pos.leb_refl.
    + case => _ <- _ _. apply/pos_leP. rewrite Pos.add_1_r. apply: Pos.lt_le_incl.
      exact: Pos.lt_succ_diag_r.
Qed.

Lemma mk_env_and1_enc :
  forall E g (b1 b2 : bool) E' g' l1 l2 cs lr,
    mk_env_and1 E g b1 b2 l1 l2 = (E', g', cs, lr) ->
    enc_bit E l1 b1 -> enc_bit E l2 b2 ->
    newer_than_lit g l1 -> newer_than_lit g l2 ->
    enc_bit E' l1 b1 /\ enc_bit E' l2 b2.
Proof.
  move=> iE ig ib1 ib2 oE og il1 il2 ocs olr Hand1 Henc1 Henc2 Hnew1 Hnew2.
  rewrite /enc_bit in Henc1 Henc2 *.
  rewrite (env_preserve_literal (mk_env_and1_env_preserve Hand1) Hnew1).
  rewrite (env_preserve_literal (mk_env_and1_env_preserve Hand1) Hnew2).
  by rewrite Henc1 Henc2.
Qed.

Lemma mk_env_and_is_bit_blast_and :
  forall w E g (bs1 bs2 : BITS w) ls1 ls2 E' g' cs lrs,
    mk_env_and E g bs1 bs2 ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_and g ls1 ls2 = (g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_and_sat :
  forall w E g (bs1 bs2 : BITS w) E' g' ls1 ls2 cs lrs,
    mk_env_and E g bs1 bs2 ls1 ls2 = (E', g', cs, lrs) ->
    enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 ->
    (newer_than_lits g ls1) -> (newer_than_lits g ls2) ->
    interp_cnf E' cs.
Proof.
Admitted.



(* bit_blast_or *)

Definition bit_blast_or1 (g: generator) (a1 a2: literal) :generator * cnf * literal :=
  let (g', r) := gen g in
  let cs :=
      if (a1 == lit_tt) || (a2 == lit_tt) then [[r]]
      else if (a1 == lit_ff) then
             [[neg_lit r; a2]; [r; neg_lit a2]]
           else if (a2 == lit_ff) then
                  [[neg_lit r; a1]; [r; neg_lit a1]]
                else [[neg_lit r; a1; a2]; [r; neg_lit a1]; [r; neg_lit a2]]
  in (g', cs, r).

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
      (g, [], [tuple]).

Parameter mk_env_or : forall w : nat, env -> BITS w -> BITS w -> generator -> w.-tuple literal -> w.-tuple literal -> env * generator * cnf * w.-tuple literal.

Lemma bit_blast_or1_correct:
  forall g b1 b2 br E l1 l2 g' cs lr,
    bit_blast_or1 g l1 l2 = (g', cs, lr) ->
    enc_bit E l1 b1 -> enc_bit E l2 b2 ->
    interp_cnf E (add_prelude cs) ->
    orb b1 b2 = br ->
    enc_bit E lr br.
Proof.
  move => g b1 b2 br E l1 l2 g' cs lr. rewrite /bit_blast_or1 /enc_bit.
  case => _ {g'}. case Htt1: (l1 == lit_tt).
  - rewrite /=. move=> <- <- /eqP <- /eqP <- /=. move=> /andP [Htt ->] H.
    rewrite (eqP Htt1) /= Htt orTb in H. by rewrite -H.
  - case Htt2: (l2 == lit_tt).
    + rewrite /=. move=> <- <- /eqP <- /eqP <- /=. move=> /andP [Htt ->] H.
      rewrite (eqP Htt2) /= Htt orbT in H. by rewrite -H.
    + rewrite /=. case Hff1: (l1 == lit_ff).
      * move=> <- <- /eqP <- /eqP <- /=.
        rewrite (eqP Hff1) /= !interp_literal_neg_lit.
        move/andP => [Htt Hcs] <-. rewrite Htt orFb. rewrite expand_eq.
        rewrite andbC. exact: Hcs.
      * case Hff2: (l2 == lit_ff).
        -- move=> <- <- /eqP <- /eqP <- /=.
           rewrite (eqP Hff2) /= !interp_literal_neg_lit.
           move/andP => [Htt Hcs] <-. rewrite Htt orbF. rewrite expand_eq.
           rewrite andbC. exact: Hcs.
        -- move=> <- <- /eqP <- /eqP <- /=.
           rewrite /= !interp_literal_neg_lit. move/andP => [Htt Hcs] <-.
           move: Hcs.
           by case: (E g); case: (interp_literal E l1); case: (interp_literal E l2).
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

Lemma mk_env_or_is_bit_blast_or :
  forall w E (bs1 bs2 : BITS w) g E' ls1 ls2 g_env g_bb cs_env cs_bb lrs_env lrs_bb,
    mk_env_or E bs1 bs2 g ls1 ls2 = (E', g_env, cs_env, lrs_env) ->
    bit_blast_or g ls1 ls2 = (g_bb, cs_bb, lrs_bb) ->
    g_env = g_bb /\ cs_env = cs_bb /\ lrs_env = lrs_bb.
Proof.
Admitted.



(* ===== bit_blast_full_adder ===== *)

Definition bit_blast_full_adder1 g a1 a2 cin :=
  let (g', r) := gen g in
  let (g'', cout) := gen g' in
  let sum_cs := [
        [neg_lit r; a1; a2; cin];
          [neg_lit r; neg_lit a1; neg_lit a2; cin];
          [neg_lit r; neg_lit a1; a2; neg_lit cin];
          [neg_lit r; a1; neg_lit a2; neg_lit cin];
        [r; neg_lit a1; a2; cin];
          [r; a1; neg_lit a2; cin];
          [r; a1; a2; neg_lit cin];
          [r; neg_lit a1; neg_lit a2; neg_lit cin]
      ] in
  let cout_cs := [
        [neg_lit cout; a1; a2];
          [neg_lit cout; a1; cin];
          [neg_lit cout; a2; cin];
        [cout; neg_lit a1; neg_lit a2];
          [cout; neg_lit a1; a2; neg_lit cin];
          [cout; a1; neg_lit a2; neg_lit cin]
      ] in
  (g'', sum_cs++cout_cs, cout, r).

Definition mk_env_full_adder1 E b1 b2 bcin g a1 a2 cin :=
  let (g', r) := gen g in
  let (g'', cout) := gen g' in
  let sum_cs := [
        [neg_lit r; a1; a2; cin];
          [neg_lit r; neg_lit a1; neg_lit a2; cin];
          [neg_lit r; neg_lit a1; a2; neg_lit cin];
          [neg_lit r; a1; neg_lit a2; neg_lit cin];
        [r; neg_lit a1; a2; cin];
          [r; a1; neg_lit a2; cin];
          [r; a1; a2; neg_lit cin];
          [r; neg_lit a1; neg_lit a2; neg_lit cin]
      ] in
  let cout_cs := [
        [neg_lit cout; a1; a2];
          [neg_lit cout; a1; cin];
          [neg_lit cout; a2; cin];
        [cout; neg_lit a1; neg_lit a2];
          [cout; neg_lit a1; a2; neg_lit cin];
          [cout; a1; neg_lit a2; neg_lit cin]
      ] in
  let E' := env_upd E (var_of_lit r) (xorb (xorb b1 b2) bcin) in
  let E'' := env_upd E' (var_of_lit cout) ((b1 && b2) || ((xorb b1 b2) && bcin)) in
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
  rewrite /enc_bit /=. rewrite !interp_literal_neg_lit.
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
  rewrite /enc_bit /=. repeat rewrite interp_literal_neg_lit.
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
        (g, [], lcin, [tuple]).

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



(* ===== bit_blast_ite ===== *)

Definition bit_blast_ite1 (g : generator) (c : literal) (a1 a2 : literal) : generator * cnf * literal :=
  let (g', r) := gen g in
  let cs := [
        [neg_lit r; neg_lit c; a1]; [neg_lit r; c; a2];
        [r; c; neg_lit a2]; [r; neg_lit c; neg_lit a1]; [r; neg_lit a1; neg_lit a2]
      ] in
  (g', cs, r).

Lemma bit_blast_ite1_correct :
  forall g bc b1 b2 br E lc l1 l2 g' cs lr,
    bit_blast_ite1 g lc l1 l2 = (g', cs, lr) ->
    enc_bit E lc bc -> enc_bit E l1 b1 -> enc_bit E l2 b2 ->
    interp_cnf E (add_prelude cs) ->
    (if bc then b1 else b2) = br ->
    enc_bit E lr br.
Proof.
  move=> g bc b1 b2 br E lc l1 l2 g' cs lr.
  rewrite /bit_blast_ite1 /enc_bit. case=> _ <- <- /eqP <- /eqP <- /eqP <-.
  rewrite /interp_cnf /= !interp_literal_neg_lit.
  move=> H <-. split_andb. move: H0 H1 H2 H3 H4.
  case: (interp_literal E lc) => /=.
  - move=> H1 _ _ H2 _. rewrite expand_eq. by rewrite H1 H2.
  - move=> _ H1 H2 _ _. rewrite expand_eq. by rewrite H1 H2.
Qed.

Fixpoint bit_blast_ite w (g : generator) (c : literal) : w.-tuple literal -> w.-tuple literal -> generator * cnf * w.-tuple literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(g_hd, cs_hd, lrs_hd) := bit_blast_ite1 g c ls1_hd ls2_hd in
      let '(g_tl, cs_tl, lrs_tl) := bit_blast_ite g_hd c ls1_tl ls2_tl in
      (g_tl, cs_hd++cs_tl, cons_tuple lrs_hd lrs_tl)
  else
    fun _ _ =>
      (g, [], [tuple]).

Lemma ite_cons_tuple :
  forall A w (bc : bool) hd1 (tl1 : w.-tuple A) hd2 (tl2 : w.-tuple A),
  (if bc then cons_tuple hd1 tl1 else cons_tuple hd2 tl2) =
  cons_tuple (if bc then hd1 else hd2) (if bc then tl1 else tl2).
Proof.
  move=> A w bc hd1 tl1 hd2 tl2. by case bc.
Qed.

Lemma ite_cons :
  forall A w (bc : bool) hd1 (tl1 : w.-tuple A) hd2 (tl2 : w.-tuple A),
  (if bc then [tuple of hd1::tl1] else [tuple of hd2::tl2]) =
  [tuple of (if bc then hd1 else hd2)::(if bc then tl1 else tl2)].
Proof.
  move=> A w bc hd1 tl1 hd2 tl2. by case bc.
Qed.

Lemma bit_blast_ite_correct :
  forall w g bc (bs1 bs2 : BITS w) brs E lc (ls1 ls2 : w.-tuple literal) g' cs lrs,
    bit_blast_ite g lc ls1 ls2 = (g', cs, lrs) ->
    enc_bit E lc bc -> enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    (if bc then bs1 else bs2) = brs ->
    enc_bits E lrs brs.
Proof.
  elim.
  - done.
  - move=> n IH g bc. case/tupleP => [ibs1_hd ibs1_tl].
    case/tupleP => [ibs2_hd ibs2_tl]. case/tupleP => [obrs_hd obrs_tl].
    move=> E lc. case/tupleP => [ils1_hd ils1_tl]. case/tupleP => [ils2_hd ils2_tl].
    move=> og cs. case/tupleP => [olrs_hd olrs_tl].
    rewrite /bit_blast_ite (lock bit_blast_ite1)
            (lock interp_cnf) /= !theadE !beheadCons -!lock -/bit_blast_ite.
    case Hite_hd: (bit_blast_ite1 g lc ils1_hd ils2_hd) => [[g_hd cs_hd] lrs_hd].
    case Hite_tl: (bit_blast_ite g_hd lc ils1_tl ils2_tl) => [[g_tl cs_tl] lrs_tl].
    case => Hog <- Holrs_hd Holrs_tl => {cs}.
    move=> Henc_c /andP [Henc_hd1 Henc_tl1] /andP [Henc_hd2 Henc_tl2] Hcnf.
    rewrite ite_cons. case => Hobrs_hd Hobrs_tl.
    rewrite add_prelude_append in Hcnf. move/andP: Hcnf => [Hcnf_hd Hcnf_tl].
    apply/andP; split.
    + rewrite -Holrs_hd.
      exact: (bit_blast_ite1_correct Hite_hd Henc_c Henc_hd1 Henc_hd2
                                     Hcnf_hd Hobrs_hd).
    + apply: (IH g_hd bc ibs1_tl ibs2_tl obrs_tl E lc ils1_tl ils2_tl
                 g_tl cs_tl olrs_tl _ Henc_c Henc_tl1 Henc_tl2 Hcnf_tl).
      * rewrite Hite_tl. apply: injective_projections => /=; first by reflexivity.
        apply: val_inj. exact: Holrs_tl.
      * apply: val_inj. exact: Hobrs_tl.
Qed.



(* ===== bit_blast_shl ===== *)

Definition bit_blast_shl_int1 w (g : generator) (ls : w.-tuple literal) : generator * cnf * w.-tuple literal :=
  (g, [], dropmsb (joinlsb (ls, lit_ff))).

Fixpoint bit_blast_shl_int w (g : generator) (ls : w.-tuple literal) (n : nat) : generator * cnf * w.-tuple literal :=
  match n with
  | O => (g, [], ls)
  | S m => let '(g_m, cs_m, ls_m) := bit_blast_shl_int g ls m in
           let '(g1, cs1, ls1) := bit_blast_shl_int1 g_m ls_m in
           (g1, cs_m++cs1, ls1)
  end.

Lemma bit_blast_shl_int1_correct :
  forall w g (bs : BITS w) E ls g' cs lrs,
    bit_blast_shl_int1 g ls = (g', cs, lrs) ->
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (shlB bs).
Proof.
  move=> w g bs E ls g' cs lrs. rewrite /bit_blast_shl_int1 /shlB.
  case => _ _ <- Henc_bs Hcs. apply: enc_bits_dropmsb.
  rewrite (enc_bits_joinlsb _) Henc_bs (add_prelude_enc_bit_ff Hcs). done.
Qed.

Lemma bit_blast_shl_int_correct :
  forall w g (bs : BITS w) n E ls g' cs lrs,
    bit_blast_shl_int g ls n = (g', cs, lrs) ->
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (shlBn bs n).
Proof.
  move=> w ig ibs. elim.
  - rewrite /= => E ils og cs olrs. case => _ <- <-. move=> H _; exact: H.
  - move=> n IH E ils og cs olrs.
    rewrite /bit_blast_shl_int (lock interp_cnf)
            (lock bit_blast_shl_int1) /= -!lock -/bit_blast_shl_int.
    case Hm: (bit_blast_shl_int ig ils) => [[g_m cs_m] ls_m].
    case H1: (bit_blast_shl_int1 g_m ls_m) => [[g1 cs1] ls1].
    case => Hog Hcs Holrs Henc_ibs Hcnf. rewrite <- Holrs.
    rewrite -Hcs add_prelude_append in Hcnf. move/andP: Hcnf => [Hcnf_m Hcnf1].
    apply: (bit_blast_shl_int1_correct H1 _ Hcnf1).
    exact: (IH E _ _ _ _ Hm Henc_ibs Hcnf_m).
Qed.

Fixpoint bit_blast_shl_rec w wn (g : generator) : w.-tuple literal -> wn.-tuple literal -> nat -> generator * cnf * w.-tuple literal :=
  if wn is _.+1 then
    fun ls ns i =>
      let (ns_tl, ns_hd) := eta_expand (splitlsb ns) in
      let '(g_tl, cs_tl, ls_tl) := bit_blast_shl_rec g ls ns_tl (2 * i) in
      let '(g_hd, cs_hd, ls_hd) := bit_blast_shl_int g_tl ls_tl i in
      if ns_hd == lit_tt then
        (g_hd, cs_tl++cs_hd, ls_hd)
      else if ns_hd == lit_ff then
             (g_tl, cs_tl, ls_tl)
           else
             let '(g_ite, cs_ite, ls_ite) := bit_blast_ite g ns_hd ls_hd ls_tl in
             (g_ite, cs_tl++cs_hd++cs_ite, ls_ite)
  else
    fun ls _ _ =>
      (g, [], ls).

Definition bit_blast_shl w (g : generator) (ls ns : w.-tuple literal) : generator * cnf * w.-tuple literal :=
  bit_blast_shl_rec g ls ns 1.

Lemma bit_blast_shl_rec_correct :
  forall w wn g (bs : BITS w) (ns: BITS wn) i E ls (lns : wn.-tuple literal) g' cs lrs,
    bit_blast_shl_rec g ls lns i = (g', cs, lrs) ->
    enc_bits E ls bs ->
    enc_bits E lns ns ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (shlBn bs (toNat ns * i)).
Proof.
  move=> w. elim.
  - move=> ig ibs ins i E ils ilns og cs olrs. case => _ <- <-.
    move=> Henc_bs Henc_ns Hcnf. rewrite toNatNil /=. exact: Henc_bs.
  - move=> wn IH ig ibs. case/tupleP => [ins_hd ins_tl]. move=> i E ls.
    case/tupleP => [ilns_hd ilns_tl] og cs olrs.
    rewrite (lock interp_cnf) /= !theadE !beheadCons -lock.
    rewrite toNatCons.
    case Htl: (bit_blast_shl_rec ig ls ilns_tl (2 * i)) => [[g_tl cs_tl] ls_tl].
    case Hhd: (bit_blast_shl_int g_tl ls_tl i) => [[g_hd cs_hd] ls_hd].
    case Htt: (ilns_hd == lit_tt).
    + move/eqP: Htt => Htt. rewrite Htt.
      case => Hog Hcs Holrs Henc_bs /andP [Henc_hd Henc_tl] Hcnf.
      rewrite -Holrs. rewrite (add_prelude_enc_bit_true _ Hcnf) in Henc_hd.
      rewrite Henc_hd. rewrite -Hcs add_prelude_append in Hcnf.
      move/andP: Hcnf => [Hcnf_tl Hcnf_hd].
      move: (IH _ _ _ _ _ _ _ _ _ _ Htl Henc_bs Henc_tl Hcnf_tl) => Henc_ls_tl.
      move: (bit_blast_shl_int_correct Hhd Henc_ls_tl Hcnf_hd).
      rewrite -shlBn_add /=. rewrite -muln2.
      replace ((1 + toNat ins_tl * 2) * i) with (toNat ins_tl * (2 * i) + i) by ring.
      by apply.
    + case Hff: (ilns_hd == lit_ff).
      * move/eqP: Hff => {Htt} Hff. rewrite Hff.
        case => Hog Hcs Holrs Henc_bs /andP [Henc_hd Henc_tl] Hcnf.
        rewrite -Holrs. rewrite (add_prelude_enc_bit_is_false _ Hcnf) in Henc_hd.
        rewrite (eqP Henc_hd) /=. rewrite -Hcs in Hcnf. rewrite add0n.
        move: (IH ig ibs ins_tl (2*i) E ls ilns_tl g_tl cs_tl ls_tl Htl
                  Henc_bs Henc_tl Hcnf). rewrite -mul2n.
        replace (toNat ins_tl * (2 * i)) with (2 * toNat ins_tl * i) by ring.
        by apply.
      * move=> {Htt Hff}.
        case Hite: (bit_blast_ite ig ilns_hd ls_hd ls_tl) => [[g_ite cs_ite] ls_ite].
        case => Hog Hcs Holrs Henc_bs /andP [Henc_hd Henc_tl] Hcnf.
        rewrite -Hcs 2!add_prelude_append in Hcnf. move/andP: Hcnf => [Hcnf_tl Hcnf].
        move/andP: Hcnf => [Hcnf_hd Hcnf_ite]. rewrite -Holrs.
        have Henc_ls_hd: (enc_bits E ls_hd (shlBn ibs ((1 + (toNat ins_tl).*2) * i))).
        {
          move: (IH _ _ _ _ _ _ _ _ _ _ Htl Henc_bs Henc_tl Hcnf_tl) => Henc_ls_tl.
          move: (bit_blast_shl_int_correct Hhd Henc_ls_tl Hcnf_hd).
          rewrite -shlBn_add /=. rewrite -muln2.
          replace ((1 + toNat ins_tl * 2) * i) with (toNat ins_tl * (2 * i) + i)
            by ring. by apply.
        }
        have Henc_ls_tl: (enc_bits E ls_tl (shlBn ibs (((toNat ins_tl).*2) * i))).
        {
          move: (IH ig ibs ins_tl (2*i) E ls ilns_tl g_tl cs_tl ls_tl Htl
                    Henc_bs Henc_tl Hcnf_tl). rewrite -mul2n.
          replace (toNat ins_tl * (2 * i)) with (2 * toNat ins_tl * i) by ring.
          by apply.
        }
        apply: (bit_blast_ite_correct Hite Henc_hd Henc_ls_hd Henc_ls_tl Hcnf_ite).
        move=> {Henc_hd}. case: ins_hd; reflexivity.
Qed.

Corollary bit_blast_shl_correct :
  forall w g (bs : BITS w) (ns : BITS w) E ls lns g' cs lrs,
    bit_blast_shl g ls lns = (g', cs, lrs) ->
    enc_bits E ls bs ->
    enc_bits E lns ns ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (shlBn bs (toNat ns)).
Proof.
  move=> w g bs ns E ls lns g' cs lrs Hshl Henc_bs Henc_ns Hcnf.
  rewrite -(muln1 (toNat ns)).
  exact: (bit_blast_shl_rec_correct Hshl Henc_bs Henc_ns Hcnf).
Qed.



(* ===== bit_blast_shr ===== *)

Definition bit_blast_shr_int1 w (g : generator) : w.-tuple literal -> generator * cnf * w.-tuple literal :=
  if w is _.+1 then
    fun ls =>
      (g, [], joinmsb (lit_ff, droplsb ls))
  else
    fun _ =>
      (g, [], [tuple]).

Fixpoint bit_blast_shr_int w (g : generator) (ls : w.-tuple literal) (n : nat) : generator * cnf * w.-tuple literal :=
  match n with
  | O => (g, [], ls)
  | S m => let '(g_m, cs_m, ls_m) := bit_blast_shr_int g ls m in
           let '(g1, cs1, ls1) := bit_blast_shr_int1 g_m ls_m in
           (g1, cs_m++cs1, ls1)
  end.

Lemma bit_blast_shr_int1_correct :
  forall w g (bs : BITS w) E ls g' cs lrs,
    bit_blast_shr_int1 g ls = (g', cs, lrs) ->
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (shrB bs).
Proof.
  elim.
  - done.
  - move => w IH g bs E ls g' cs lrs. rewrite /bit_blast_shr_int1 /shrB /enc_bit.
    case => Hog Hcs <- Henc_bs Hcnf. apply/andP; split.
    + apply: enc_bits_thead. rewrite /joinmsb0.
      rewrite enc_bits_joinmsb (add_prelude_enc_bit_ff Hcnf).
      exact: (enc_bits_droplsb Henc_bs).
    + rewrite /=. apply enc_bits_behead. rewrite /joinmsb0.
      rewrite enc_bits_joinmsb (add_prelude_enc_bit_ff Hcnf).
      exact: (enc_bits_droplsb Henc_bs).
Qed.

Lemma bit_blast_shr_int_correct :
  forall w g (bs : BITS w) n E ls g' cs lrs,
    bit_blast_shr_int g ls n = (g', cs, lrs) ->
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (shrBn bs n).
Proof.
  move => w ig ibs. elim.
  - rewrite /= => E ils og cs olrs. case => _ <- <-. done.
  - move => n IH E ils og cs olrs. rewrite (lock interp_cnf) /= -lock.
    case Hm: (bit_blast_shr_int ig ils) => [[g_m cs_m] ls_m].
    case H1: (bit_blast_shr_int1 g_m ls_m) => [[g1 cs1] ls1].
    case => Hog Hcs Holrs Henc_ibs Hcnf. rewrite <- Holrs.
    rewrite -Hcs add_prelude_append in Hcnf. move/andP: Hcnf => [Hcnf_m Hcnf1].
    apply: (bit_blast_shr_int1_correct H1 _ Hcnf1).
    exact: (IH E _ _ _ _ Hm Henc_ibs Hcnf_m).
Qed.



(* ===== bit_blast_sra ===== *)

Definition bit_blast_sra_int1 w (g : generator) (ls: (w.+1).-tuple literal) : generator * cnf * (w.+1).-tuple literal :=
  (g, [], joinmsb (msb_nonnil ls, droplsb ls)).

Fixpoint bit_blast_sra_int w (g : generator) (ls : (w.+1).-tuple literal) (n : nat) : generator * cnf * (w.+1).-tuple literal :=
  match n with
  | O => (g, [], ls)
  | S m => let '(g_m, cs_m, ls_m) := bit_blast_sra_int g ls m in
           let '(g1, cs1, ls1) := bit_blast_sra_int1 g_m ls_m in
           (g1, cs_m++cs1, ls1)
  end.



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
  elim; first by done. move=> n IH g bs1 bs2 E ls1 ls2 br g' cs lrs.
  rewrite /bit_blast_add. case HadcB: (adcB false bs1 bs2) => [obcout obrs].
  case Hblast: (bit_blast_full_adder g lit_ff ls1 ls2) => [[[og ocs] olcout] olrs].
  case=> _ <- <- => Henc1 Henc2 <- Hcs.
  apply: (bit_blast_full_adder_correct1 Hblast Henc1 Henc2 _ Hcs HadcB).
  exact: (add_prelude_enc_bit_ff Hcs).
Qed.



(* ===== bit_blast_mul ===== *)

Fixpoint bit_blast_mul_rec w wn (g:generator) : w.-tuple literal -> wn.-tuple literal -> nat -> generator * cnf * w.-tuple literal :=
  if wn is _.+1 then
    fun ls1 ls2 i =>
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(g_tl, cs_tl, lrs_tl) := bit_blast_mul_rec g ls1 ls2_tl (i+1) in
      let '(g_hd, cs_hd, lrs_hd) := bit_blast_shl_int g_tl ls1 i in
      if ls2_hd == lit_tt then
        let '(g_add, cs_add, lrs_add) := bit_blast_add g lrs_tl lrs_hd in
        (g_add, cs_tl++cs_hd++cs_add, lrs_add)
      else if ls2_hd == lit_ff then
             (g_tl, cs_tl, lrs_tl)
           else
             let '(g_and, cs_and, lrs_and) := bit_blast_and g (copy w ls2_hd) lrs_hd in
             let '(g_add, cs_add, lrs_add) := bit_blast_add g_and lrs_tl lrs_and in
             (g_add, cs_tl++cs_hd++cs_and++cs_add, lrs_add)
  else
    fun _ _ _ =>
      bit_blast_const g (@fromNat w 0).

Definition bit_blast_mul w (g: generator) (ls1 ls2:  w.-tuple literal) :generator * cnf * w.-tuple literal:=
  bit_blast_mul_rec g ls1 ls2 0.

Lemma andB_copy_case :
  forall w b (bs : BITS w),
    andB (copy w b) bs = if b then bs else (@fromNat w 0).
Proof.
  move=> w [] bs.
  - exact: and1B.
  - rewrite -/(zero w) -fromNat0. exact: and0B.
Qed.

Lemma andB_copy_mul :
  forall w b (bs : BITS w),
    andB (copy w b) bs = bs *# b.
Proof.
  move=> w b bs. rewrite andB_copy_case. case: b.
  - rewrite mulB1; reflexivity.
  - rewrite mulB0; reflexivity.
Qed.

Lemma bit_blast_mul_rec_correct :
  forall wn w g (bs1 : BITS w) (bs2 : BITS wn) i E (ls1:w.-tuple literal) (ls2 : wn.-tuple literal) g' cs lrs,
    bit_blast_mul_rec g ls1 ls2 i = (g', cs, lrs) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (mulB bs1 (# (toNat bs2 * (2^i)))).
Proof.
  elim.
  - move => wn ig ibs1 ibs2 i E ils1 ils2 og cs olrs.
    case=> _ <- <- Henc1 Henc2 Hcnf.
    apply: (bit_blast_const_correct (g:=ig) _ Hcnf).
    apply: injective_projections => /=; first by reflexivity.
    rewrite toNatNil /= mul0n mulB0. reflexivity.
  - move => wn IH w ig ibs1. case/tupleP => [ibs2_hd ibs2_tl] i E ls1.
    case/tupleP => [ils2_hd ils2_tl] og cs olrs.
    rewrite /bit_blast_mul_rec -/bit_blast_mul_rec
            (lock interp_cnf) (lock bit_blast_add) (lock bit_blast_and)
            (lock bit_blast_shl_int) (lock enc_bits) /= !theadE !beheadCons -!lock.
    case Htl: (bit_blast_mul_rec ig ls1 ils2_tl (i+1)) => [[g_tl cs_tl] ls_tl].
    case Hhd: (bit_blast_shl_int g_tl ls1 i) => [[g_hd cs_hd] lrs_hd].
    case Hadd1: (bit_blast_add ig ls_tl lrs_hd) => [[g_add cs_add] lrs_add].
    case Hand: (bit_blast_and ig (copy w ils2_hd) lrs_hd)=> [[g_and cs_and] lrs_and].
    case Hadd2: (bit_blast_add g_and ls_tl lrs_and) => [[g_add2 cs_add2] lrs_add2].
    case Htt: (ils2_hd == lit_tt); last case Hff: (ils2_hd == lit_ff).
    + rewrite (eqP Htt) => {Hadd2 lrs_add2 cs_add2 g_add2 Hand lrs_and cs_and g_and}.
      case=> Hog Hcs Holrs Henc1 Henc2 Hcnf. rewrite -Holrs => {Holrs olrs Hog og}.
      move: (enc_bits_thead Henc2) (enc_bits_behead Henc2) => {Henc2}.
      rewrite !theadE !beheadCons => Henc2_hd Henc2_tl.
      rewrite -Hcs 2!add_prelude_append in Hcnf.
      move/andP: Hcnf => [Hcnf_tl /andP [Hcnf_hd Hcnf_add]].
      rewrite (add_prelude_enc_bit_true _ Hcnf_tl) in Henc2_hd. rewrite Henc2_hd.
      rewrite toNatCons -muln2 /=.
      have ->: ((1+toNat ibs2_tl*2) * 2^i) = ((2^i) + (toNat ibs2_tl) * (2^(i+1))).
      {
        rewrite mulnDl mul1n -mulnA -expnS addn1. reflexivity.
      }
      move: (IH _ _ _ _  (i+1) _ _ _ _ _ _ Htl Henc1 Henc2_tl Hcnf_tl) => Henc_ls_tl.
      move : (bit_blast_shl_int_correct Hhd Henc1 Hcnf_hd) => Henc_shl.
      apply: (bit_blast_add_correct Hadd1 Henc_ls_tl Henc_shl _ Hcnf_add).
      rewrite /shlBn shlB_mul2exp mulB_addn addBC. reflexivity.
    + rewrite (eqP Hff) => {Hadd2 lrs_add2 cs_add2 g_add2 Hand lrs_and cs_and g_and
                                  Hadd1 lrs_add cs_add g_add Hhd lrs_hd cs_hd g_hd}.
      case => Hog Hcs Holrs Henc_bs1 Henc_bs2 Hcnf.
      rewrite -Holrs => {Holrs olrs Hog og}. rewrite -Hcs in Hcnf => {Hcs cs}.
      move: (enc_bits_thead Henc_bs2) (enc_bits_behead Henc_bs2) => {Henc_bs2}.
      rewrite !theadE !beheadCons => Henc2_hd Henc2_tl.
      rewrite (add_prelude_enc_bit_is_false _ Hcnf) in Henc2_hd.
      rewrite (eqP Henc2_hd).
      rewrite toNatCons /= add0n -muln2 -mulnA -expnS -(addn1 i).
      exact: (IH _ _ _ _ _ _ _ _ _ _ _ Htl Henc_bs1 Henc2_tl Hcnf).
    + case => {Hadd1 lrs_add cs_add g_add} Hog Hcs Horls Henc_bs1 Henc_bs2 Hcnf.
      rewrite -Horls => {Horls olrs Hog og}.
      rewrite -Hcs 3!add_prelude_append in Hcnf => {Hcs}.
      move/andP: Hcnf => [Hcnf_tl /andP [Hcnf_hd /andP [Hcnf_and Hcnf_add2]]].
      move: (enc_bits_thead Henc_bs2) (enc_bits_behead Henc_bs2) => {Henc_bs2}.
      rewrite !theadE !beheadCons => [Henc2_hd Henc2_tl]. rewrite toNatCons.
      rewrite -muln2 mulnDl -mulnA -expnS -(addn1 i).
      move: (IH _ _ _ _ (i+1) _ _ _ _ _ _ Htl Henc_bs1 Henc2_tl Hcnf_tl) =>
      Henc_ls_tl.
      move : (bit_blast_shl_int_correct Hhd Henc_bs1 Hcnf_hd) => Henc_lrs_hd.
      move: (enc_bit_copy w Henc2_hd) => Henc_copy.
      move : (bit_blast_and_correct Hand Henc_copy Henc_lrs_hd Hcnf_and) =>
      Henc_lrs_and.
      apply: (bit_blast_add_correct Hadd2 Henc_ls_tl Henc_lrs_and _ Hcnf_add2).
      rewrite /shlBn shlB_mul2exp. rewrite andB_copy_mul.
      rewrite -mulB_muln -mulB_addn.
      replace (toNat ibs2_tl * 2 ^ (i + 1) + 2 ^ i * ibs2_hd) with
          (ibs2_hd * 2 ^ i + toNat ibs2_tl * 2 ^ (i + 1)) by ring.
      reflexivity.
Qed.

Lemma bit_blast_mul_correct :
  forall w g (bs1 bs2 : BITS w) E ls1 ls2 g' cs lrs,
    bit_blast_mul g ls1 ls2 = (g', cs, lrs) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (mulB bs1 bs2).
Proof.
  move => w g bs1 bs2 E ls1 ls2 g' cs lrs Hmul Henc_bs1 Henc_bs2 Hcnf.
  rewrite -(toNatK bs2). replace (toNat bs2) with (toNat bs2 * (2^ 0)) by ring.
  exact: (bit_blast_mul_rec_correct Hmul Henc_bs1 Henc_bs2 Hcnf).
Qed.



(* ===== bit_blast_eq ===== *)

Fixpoint bit_blast_eq_eq w r : w.-tuple literal -> w.-tuple literal -> cnf :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let clauses_hd := List.map (fun clause => neg_lit r::clause) (cnf_lit_eq ls1_hd ls2_hd) in
      let clauses_tl := bit_blast_eq_eq r ls1_tl ls2_tl in
      clauses_hd++clauses_tl
  else
    fun _ _ =>
      [].

Definition bit_blast_eq_choice w r (auxs : w.-tuple literal) : cnf :=
  [r::auxs].

Fixpoint bit_blast_eq_neq w g : w.-tuple literal -> w.-tuple literal -> generator * cnf * w.-tuple literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (g_hd, auxs_hd) := gen g in
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let clauses_hd := [ [neg_lit auxs_hd; ls1_hd; ls2_hd];
                          [neg_lit auxs_hd; neg_lit ls1_hd; neg_lit ls2_hd];
                          [auxs_hd; neg_lit ls1_hd; ls2_hd];
                          [auxs_hd; ls1_hd; neg_lit ls2_hd] ] in
      let '(g_tl, clauses_tl, auxs_tl) := bit_blast_eq_neq g_hd ls1_tl ls2_tl in
      (g_tl, clauses_hd++clauses_tl, cons_tuple auxs_hd auxs_tl)
  else
    fun _ _ =>
      (g, [], [tuple]).

Fixpoint mk_env_eq_neq w E g : BITS w -> BITS w -> w.-tuple literal -> w.-tuple literal -> env * generator * cnf * w.-tuple literal :=
  if w is _.+1 then
    fun bs1 bs2 ls1 ls2 =>
      let (g_hd, auxs_hd) := gen g in
      let (bs1_tl, bs1_hd) := eta_expand (splitlsb bs1) in
      let (bs2_tl, bs2_hd) := eta_expand (splitlsb bs2) in
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let E' := env_upd E (var_of_lit auxs_hd) (xorb bs1_hd bs2_hd) in
      let clauses_hd := [ [neg_lit auxs_hd; ls1_hd; ls2_hd];
                          [neg_lit auxs_hd; neg_lit ls1_hd; neg_lit ls2_hd];
                          [auxs_hd; neg_lit ls1_hd; ls2_hd];
                          [auxs_hd; ls1_hd; neg_lit ls2_hd] ] in
      let '(E_tl, g_tl, clauses_tl, auxs_tl) :=
          mk_env_eq_neq E' g_hd bs1_tl bs2_tl ls1_tl ls2_tl in
      (E_tl, g_tl, clauses_hd++clauses_tl, cons_tuple auxs_hd auxs_tl)
  else
    fun _ _ _ _ =>
      (E, g, [], [tuple]).

Definition bit_blast_eq w (g : generator) (ls1 ls2 : w.-tuple literal) : generator * cnf * literal :=
  let (g_r, r) := gen g in
  let '(g_aux, clauses_neq, auxs) := bit_blast_eq_neq g_r ls1 ls2 in
  let clauses_aux := bit_blast_eq_choice r auxs in
  let clauses_eq := bit_blast_eq_eq r ls1 ls2 in
  (g_aux, clauses_neq++clauses_aux++clauses_eq, r).

Definition mk_env_eq w E g (bs1 bs2 : BITS w) (ls1 ls2 : w.-tuple literal) : env * generator * cnf * literal :=
  let (g_r, r) := gen g in
  let E' := env_upd E (var_of_lit r) (bs1 == bs2) in
  let '(E_aux, g_aux, clauses_neq, auxs) := mk_env_eq_neq E' g_r bs1 bs2 ls1 ls2 in
  let clauses_aux := bit_blast_eq_choice r auxs in
  let clauses_eq := bit_blast_eq_eq r ls1 ls2 in
  (E_aux, g_aux, clauses_neq++clauses_aux++clauses_eq, r).

Lemma bit_blast_eq_eq_correct :
  forall w (bs1 bs2 : BITS w) E ls1 ls2 lr,
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude (bit_blast_eq_eq lr ls1 ls2)) ->
    interp_literal E lr ->
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
      rewrite !interp_literal_neg_lit in H0 H2. rewrite Hilr /= in H0 H2.
      move: (expand_eq (interp_literal E ils1_hd) (interp_literal E ils2_hd)).
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
    (exists laux : literal, laux \in lauxs /\ interp_literal E laux) ->
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
      rewrite !interp_literal_neg_lit in Hcnf. rewrite Haux /= in Hcnf. split_andb.
      move=> Heq. injection Heq => Heqtl Heqhd. move: H0 H1.
      move: (enc_bit_eq_lit Heqhd Henc1hd Henc2hd) => ->.
      by case: (interp_literal E ils2_hd).
    + move=> Hin.
      have Hexists: (exists laux : literal,
                        laux \in lauxs_tl /\ interp_literal E laux).
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
    interp_literal E r \/ (exists aux : literal,
                              aux \in auxs /\ interp_literal E aux).
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
    interp_literal E lr = (bs1 == bs2).
Proof.
  move=> w ig ibs1 ibs2 E og ils1 ils2 cs olr. rewrite /bit_blast_eq.
  rewrite /gen. case Hneq: (bit_blast_eq_neq (ig+1)%positive ils1 ils2) =>
                [[g_aux cs_neq] auxs]. set r := Pos ig.
  case=> _ <- <- Henc1 Henc2 Hcnf.
  rewrite add_prelude_append add_prelude_cons in Hcnf.
  move/andP: Hcnf=> [Hcnf_neq Hcnf]. move/andP: Hcnf=> [Hcnf_auxs Hcnf_eq].
  case Hr: (interp_literal E r).
  - symmetry. apply/eqP.
    exact: (bit_blast_eq_eq_correct Henc1 Henc2 Hcnf_eq Hr).
  - move: (bit_blast_eq_choice_correct Hcnf_auxs). rewrite Hr.
    case => H; first by elim H. symmetry. apply/eqP.
    exact: (bit_blast_eq_neq_correct Hneq Henc1 Henc2 Hcnf_neq H).
Qed.

Lemma mk_env_eq_neq_is_bit_blast_eq_neq :
  forall w E g (bs1 bs2 : BITS w) ls1 ls2 E' g' cs lrs,
    mk_env_eq_neq E g bs1 bs2 ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_eq_neq g ls1 ls2 = (g', cs, lrs).
Proof.
  elim.
  - move=> E g bs1 bs2 ls1 ls2 E' g' cs lrs /=. case=> _ <- <- <-. reflexivity.
  - move=> w IH E g. case/tupleP=> [bs1_hd bs1_tl]. case/tupleP=> [bs2_hd bs2_tl].
    case/tupleP=> [ls1_hd ls1_tl]. case/tupleP=> [ls2_hd ls2_tl].
    move=> E' g' cs lrs /=. rewrite !theadE !beheadCons.
    case Henv: (mk_env_eq_neq (env_upd E g (xorb bs1_hd bs2_hd))
                              (g + 1)%positive bs1_tl bs2_tl ls1_tl ls2_tl)
    => [[[E_env g_env] cs_env] auxs_env]. case=> _ <- <- <-.
    rewrite (IH _ _ _ _ _ _ _ _ _ _ Henv). reflexivity.
Qed.

Lemma mk_env_eq_is_bit_blast_eq :
  forall w E g (bs1 bs2 : BITS w) ls1 ls2 E' g' cs lrs,
    mk_env_eq E g bs1 bs2 ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_eq g ls1 ls2 = (g', cs, lrs).
Proof.
  move=> w E g bs1 bs2 ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_eq /bit_blast_eq. rewrite /gen.
  case Henv: (mk_env_eq_neq (env_upd E (var_of_lit (Pos g)) (bs1 == bs2))
                            (g + 1)%positive bs1 bs2 ls1 ls2)
  => [[[E_env g_env] cs_env] auxs_env]. case=> _ <- <- <-.
  rewrite (mk_env_eq_neq_is_bit_blast_eq_neq Henv). reflexivity.
Qed.

Lemma mk_env_eq_neq_newer_vm :
forall w (m : VM.t (wordsize.-tuple literal)) E g (bs1 bs2 : BITS w) ls1 ls2 E' g' cs lrs,
  mk_env_eq_neq E g bs1 bs2 ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_vm g m -> newer_than_vm g' m.
Proof.
  elim.
  - move=> m E g bs1 bs2 ls1 ls2 E' g' cs lrs /=. case=> _ <- _ _. done.
  - move=> w IH m E g. case/tupleP=> [bs1_hd bs1_tl]. case/tupleP=> [bs2_hd bs2_tl].
    case/tupleP=> [ls1_hd ls1_tl]. case/tupleP=> [ls2_hd ls2_tl].
    move=> E' g' cs. case/tupleP=> [lrs_hd lrs_tl].
    rewrite /= !theadE !beheadCons.
    case Hneq: (mk_env_eq_neq (env_upd E g (xorb bs1_hd bs2_hd)) (g + 1)%positive
                              bs1_tl bs2_tl ls1_tl ls2_tl)
    => [[[E_tl g_tl] cs_tl] auxs_tl]. case=> _ <- _ _ _ Hnew.
    apply: (IH _ _ _ _ _ _ _ _ _ _ _ Hneq). exact: newer_than_vm_add_diag_r.
Qed.

Lemma mk_env_eq_newer_vm :
forall w (m : VM.t (wordsize.-tuple literal)) E g (bs1 bs2 : BITS w) ls1 ls2 E' g' cs lr,
  mk_env_eq E g bs1 bs2 ls1 ls2 = (E', g', cs, lr) ->
  newer_than_vm g m -> newer_than_vm g' m.
Proof.
  move=> w m E g bs1 bs2 ls1 ls2 E' g' cs lr. rewrite /mk_env_eq /gen.
  case Hneq: (mk_env_eq_neq (env_upd E (var_of_lit (Pos g)) (bs1 == bs2))
                            (g + 1)%positive bs1 bs2 ls1 ls2)
  => [[[E_aux g_aux] cs_aux] auxs]. case=> _ <- _ _ Hnew.
  apply: (mk_env_eq_neq_newer_vm Hneq). exact: newer_than_vm_add_diag_r.
Qed.

Lemma mk_env_eq_neq_consistent :
  forall w m s E g (bs1 bs2 : BITS w) ls1 ls2 E' g' cs lr,
    mk_env_eq_neq E g bs1 bs2 ls1 ls2 = (E', g', cs, lr) ->
    newer_than_vm g m ->
    consistent m E s ->
    consistent m E' s.
Proof.
  elim.
  - move=> m s E g bs1 bs2 ls1 ls2 E' g' cs lr /=.
    case=> <- _ _ _ _ Hcon. exact: Hcon.
  - move=> w IH m s E g. case/tupleP=> [bs1_hd bs1_tl].
    case/tupleP=> [bs2_hd bs2_tl]. case/tupleP=> [ls1_hd ls1_tl].
    case/tupleP=> [ls2_hd ls2_tl]. move=> E' g' cs lr /=.
    rewrite !theadE !beheadCons.
    case Hneq_tl: (mk_env_eq_neq (env_upd E g (xorb bs1_hd bs2_hd))
                                 (g + 1)%positive bs1_tl bs2_tl ls1_tl ls2_tl)
    => [[[E_tl g_tl] cs_tl] auxs_tl].
    case=> <- Hg' Hcs Hlr Hnew Hcon.
    move: (newer_than_vm_add_diag_r 1 Hnew) => Hnew_g1.
    move: (consistent_env_upd_newer (xorb bs1_hd bs2_hd) Hnew Hcon (Pos.leb_refl g))
    => Hupd_con. exact: (IH m s _ _ _ _ _ _ _ _ _ _ Hneq_tl Hnew_g1 Hupd_con).
Qed.

Lemma mk_env_eq_consistent :
  forall w m s E g (bs1 bs2 : BITS w) ls1 ls2 E' g' cs lr,
    mk_env_eq E g bs1 bs2 ls1 ls2 = (E', g', cs, lr) ->
    newer_than_vm g m ->
    consistent m E s ->
    consistent m E' s.
Proof.
  move=> w m s E g bs1 bs2 ls1 ls2 E' g' cs lr. rewrite /mk_env_eq /gen.
  case Hneq: (mk_env_eq_neq (env_upd E (var_of_lit (Pos g)) (bs1 == bs2))
                            (g + 1)%positive bs1 bs2 ls1 ls2)
  => [[[E_aux g_aux] cs_neq] auxs]. case=> <- Hg' Hcs Hlr Hnewer Hcon .
  apply: (mk_env_eq_neq_consistent Hneq (newer_than_vm_add_diag_r 1 Hnewer)).
  move=> v. move: (Hnewer v) (Hcon v) => {Hnewer Hcon}.
  rewrite /consistent1. case: (VM.find v m); last by done.
  move=> xrs Hnew Henc. move: (Hnew xrs (Logic.eq_refl (Some xrs)))=> {Hnew} Hnew /=.
  rewrite (newer_than_lits_enc_bits_env_upd _ _ _ Hnew). exact: Henc.
Qed.

Lemma mk_env_eq_preserve :
  forall w E g (bs1 bs2 : BITS w) ls1 ls2 E' g' cs lr,
    mk_env_eq E g bs1 bs2 ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_eq_neq_sat :
  forall w E g (bs1 bs2 : BITS w) ls1 ls2 E' g' cs lr,
    mk_env_eq_neq E g bs1 bs2 ls1 ls2 = (E', g', cs, lr) ->
    enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_eq_sat :
  forall w E g (bs1 bs2 : BITS w) ls1 ls2 E' g' cs lr,
    mk_env_eq E g bs1 bs2 ls1 ls2 = (E', g', cs, lr) ->
    enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
Admitted.



(* ===== bit_blast_ult ===== *)

Parameter bit_blast_ult : forall w : nat, generator -> w.-tuple literal -> w.-tuple literal -> generator * cnf * literal.

Lemma bit_blast_ult_correct :
  forall w g (bs1 bs2 : BITS w) E g' ls1 ls2 cs lr,
    bit_blast_ult g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    interp_literal E lr = (ltB bs1 bs2).
Proof.
Admitted.



(* ===== bit_blast_ule ===== *)

Parameter bit_blast_ule : forall w : nat, generator -> w.-tuple literal -> w.-tuple literal -> generator * cnf * literal.

Lemma bit_blast_ule_correct :
  forall w g (bs1 bs2 : BITS w) E g' ls1 ls2 cs lr,
    bit_blast_ule g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    interp_literal E lr = (leB bs1 bs2).
Proof.
Admitted.



(* ===== bit_blast_ugt ===== *)

Parameter bit_blast_ugt : forall w : nat, generator -> w.-tuple literal -> w.-tuple literal -> generator * cnf * literal.

Lemma bit_blast_ugt_correct :
  forall w g (bs1 bs2 : BITS w) E g' ls1 ls2 cs lr,
    bit_blast_ugt g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    interp_literal E lr = (ltB bs2 bs1).
Proof.
Admitted.



(* ===== bit_blast_uge ===== *)

Parameter bit_blast_uge : forall w : nat, generator -> w.-tuple literal -> w.-tuple literal -> generator * cnf * literal.

Lemma bit_blast_uge_correct :
  forall w g (bs1 bs2 : BITS w) E g' ls1 ls2 cs lr,
    bit_blast_uge g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    interp_literal E lr = (leB bs2 bs1).
Proof.
Admitted.



(* ===== bit_blast_slt ===== *)

Parameter bit_blast_slt : forall w : nat, generator -> w.+1.-tuple literal -> w.+1.-tuple literal -> generator * cnf * literal.

Lemma bit_blast_slt_correct :
  forall w g (bs1 bs2 : BITS (w.+1)) E g' ls1 ls2 cs lr,
    bit_blast_slt g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    interp_literal E lr <-> (toZ bs1 < toZ bs2)%Z.
Proof.
Admitted.



(* ===== bit_blast_sle ===== *)

Parameter bit_blast_sle : forall w : nat, generator -> w.+1.-tuple literal -> w.+1.-tuple literal -> generator * cnf * literal.

Lemma bit_blast_sle_correct :
  forall w g (bs1 bs2 : BITS w.+1) E g' ls1 ls2 cs lr,
    bit_blast_sle g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    interp_literal E lr <-> (toZ bs1 <= toZ bs2)%Z.
Proof.
Admitted.



(* ===== bit_blast_sgt ===== *)

Parameter bit_blast_sgt : forall w : nat, generator -> w.+1.-tuple literal -> w.+1.-tuple literal -> generator * cnf * literal.

Lemma bit_blast_sgt_correct :
  forall w g (bs1 bs2 : BITS w.+1) E g' ls1 ls2 cs lr,
    bit_blast_sgt g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    interp_literal E lr <-> (toZ bs1 > toZ bs1)%Z.
Proof.
Admitted.



(* ===== bit_blast_sge ===== *)

Parameter bit_blast_sge : forall w : nat, generator -> w.+1.-tuple literal -> w.+1.-tuple literal -> generator * cnf * literal.

Lemma bit_blast_sge_correct :
  forall w g (bs1 bs2 : BITS w.+1) E g' ls1 ls2 cs lr,
    bit_blast_sge g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    interp_literal E lr <-> (toZ bs1 >= toZ bs1)%Z.
Proof.
Admitted.



(* ===== bit_blast_conj ===== *)

Definition bit_blast_conj g (a1 a2 : literal) : generator * cnf * literal :=
  let (g', r) := gen g in
  let clauses := [[neg_lit r; a1]; [neg_lit r; a2]; [r; neg_lit a1; neg_lit a2]] in
  (g', clauses, r).

Definition mk_env_conj E g b1 b2 (a1 a2 : literal) : env * generator * cnf * literal :=
  let (g', r) := gen g in
  let E' := env_upd E (var_of_lit r) (b1 && b2) in
  let clauses := [[neg_lit r; a1]; [neg_lit r; a2]; [r; neg_lit a1; neg_lit a2]] in
  (E, g', clauses, r).

Lemma bit_blast_conj_correct :
  forall g (b1 b2 : bool) E g' (l1 l2 : literal) cs lr,
    bit_blast_conj g l1 l2 = (g', cs, lr) ->
    enc_bit E l1 b1 -> enc_bit E l2 b2 ->
    interp_cnf E (add_prelude cs) ->
    interp_literal E lr = (b1 && b2).
Proof.
Admitted.

Lemma mk_env_conj_is_bit_blast_conj :
  forall E g (b1 b2 : bool) (l1 l2 : literal) E' g' cs lr,
    mk_env_conj E g b1 b2 l1 l2 = (E', g', cs, lr) ->
    bit_blast_conj g l1 l2 = (g', cs, lr).
Proof.
Admitted.

Lemma mk_env_conj_consistent :
  forall m s E g (b1 b2 : bool) (l1 l2 : literal) E' g' cs lr,
    mk_env_conj E g b1 b2 l1 l2 = (E', g', cs, lr) ->
    consistent m E s -> consistent m E' s.
Proof.
Admitted.



(* ===== bit_blast_exp ===== *)

Definition vm := VM.t (wordsize.-tuple literal).

Definition bit_blast_exp w (m : vm) (g : generator) (e : QFBV64.exp w) : vm * generator * cnf * w.-tuple literal :=
  match e with
  | QFBV64.bvVar v =>
    match VM.find v m with
    | None => let '(g', cs, rs) := bit_blast_var g v in
              (VM.add v rs m, g', cs, rs)
    | Some rs => (m, g, [], rs)
    end
  | QFBV64.bvConst _ n => let '(g', cs, rs) := bit_blast_const g n in
                          (m, g', cs, rs)
  end.

Definition mk_env_exp w (m : vm) (s : QFBV64.State.t) (E : env) (g : generator) (e : QFBV64.exp w) : vm * env * generator * cnf * w.-tuple literal :=
  match e with
  | QFBV64.bvVar v =>
    match VM.find v m with
    | None => let '(E', g', cs, rs) := mk_env_var E g (QFBV64.State.acc v s) v in
              (VM.add v rs m, E', g', cs, rs)
    | Some rs => (m, E, g, [], rs)
    end
  | QFBV64.bvConst _ n => let '(E', g', cs, rs) := mk_env_const E g n in
                          (m, E', g', cs, rs)
  end.

Lemma bit_blast_exp_var_consistent :
  forall (v : var) (m : vm) (g : generator) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : wordsize.-tuple literal)
    (s : QFBV64.State.t),
    bit_blast_exp m g (QFBV64.bvVar v) = (m', g', cs, lrs) ->
    consistent m' E s -> consistent m E s.
Proof.
  move=> v im ig E om og ocs olrs s /=. case Hv: (VM.find v im).
  - case => <- _ _ _. by apply.
  - case Hblast: (bit_blast_var ig v) => [[gv csv] rsv].
    case => <- _ _ _. move=> Hcon x. case Hxv: (x == v).
    + rewrite /consistent1 (eqP Hxv) Hv. done.
    + move: (Hcon x). rewrite /consistent1. move/negP: Hxv => Hxv.
      rewrite (VM.Lemmas.find_add_neq _ _ Hxv). by apply.
Qed.

Lemma bit_blast_exp_const_consistent :
  forall (w : nat) (bv : BITS w) (m : vm) (g : generator)
         (E : env) (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal)
         (s : QFBV64.State.t),
    bit_blast_exp m g (QFBV64.bvConst w bv) = (m', g', cs, lrs) ->
    consistent m' E s -> consistent m E s.
Proof.
  move=> w bv im ig E om og ocs olrs s /=. case=> <- _ _ _. by apply.
Qed.

Corollary bit_blast_exp_consistent :
  forall w m g (e : QFBV64.exp w) E m' g' cs lrs s,
    bit_blast_exp m g e = (m', g', cs, lrs) ->
    consistent m' E s ->
    consistent m E s.
Proof.
  move=> w m g e. elim: e m g.
  - exact: bit_blast_exp_var_consistent.
  - exact: bit_blast_exp_const_consistent.
Qed.

Lemma bit_blast_exp_var :
  forall v m g s E m' g' cs lrs,
    bit_blast_exp m g (QFBV64.bvVar v) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvVar v) s).
Proof.
  move=> v im ig s E om og ocs olrs. move=> Hblast Hcon Hcnf.
  move: (Hcon v) Hblast => {Hcon} Hcon. rewrite /=. case Hfind: (VM.find v im).
  - case=> Hm Hg Hcs Hlrs. move: Hcon; rewrite /consistent1.
    rewrite -Hm Hfind Hlrs. by apply.
  - case Hblast: (bit_blast_var ig v) => [[vg vcs] vlrs].
    case=> [Hom Hog Hocs Holrs]. move: Hcon; rewrite /consistent1.
    rewrite -Hom. rewrite (VM.Lemmas.find_add_eq _ _ (eq_refl v)).
    rewrite Holrs; by apply.
Qed.

Lemma bit_blast_exp_const :
  forall w (bv : BITS w) m g s E m' g' cs lrs,
    bit_blast_exp m g (QFBV64.bvConst w bv) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvConst w bv) s).
Proof.
  move=> w bv im ig s E om og ocs olrs. case=> _ _ <- <- _ Hprelude.
  move: (add_prelude_tt Hprelude) => /= Htt {im ig s om og ocs olrs Hprelude}.
  elim: w bv; first by done. move=> w IH. case/tupleP => hd tl.
  rewrite /= mapCons !theadE !beheadCons. apply/andP; split.
  - rewrite /enc_bit. case: hd => /=; by rewrite Htt.
  - exact: IH.
Qed.

Corollary bit_blast_exp_correct :
  forall w m g (e : QFBV64.exp w) s E m' g' cs lrs,
    bit_blast_exp m g e = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp e s).
Proof.
  move=> w im ig e. elim: e im ig.
  - exact: bit_blast_exp_var.
  - exact: bit_blast_exp_const.
Qed.

Lemma mk_env_exp_is_bit_blast_exp_var :
  forall (t : VarOrder.t) (m : vm) (E : env) (g : generator)
         (s : QFBV64.State.t) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : wordsize.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvVar t) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvVar t) = (m', g', cs, lrs).
Proof.
  move=> v m E g s m' E' gl cs lrs. rewrite /=. case Hfind: (VM.find v m).
  - case=> <- _ <- <- <-. reflexivity.
  - case Henv: (mk_env_var E g (QFBV64.State.acc v s) v) =>
    [[[E_env g_env] cs_env] rs_env]. case=> <- _ <- <- <-.
    rewrite (mk_env_var_is_bit_blast_var Henv). reflexivity.
Qed.

Lemma mk_env_exp_is_bit_blast_exp_const :
  forall (w : nat) (b : BITS w) (m : vm) (E : env) (g : generator)
         (s : QFBV64.State.t) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConst w b) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvConst w b) = (m', g', cs, lrs).
Proof.
  move=> w b m E g s m' E' g' cs lrs. rewrite /mk_env_exp /bit_blast_exp.
  case=> <- _ <- <- <-. reflexivity.
Qed.

Lemma mk_env_exp_is_bit_blast_exp :
  forall w m E g (e : QFBV64.exp w) s m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    bit_blast_exp m g e = (m', g', cs, lrs).
Proof.
  move=> w m E g e. elim: e m E g.
  - exact: mk_env_exp_is_bit_blast_exp_var.
  - exact: mk_env_exp_is_bit_blast_exp_const.
Qed.

Lemma mk_env_exp_newer_vm :
  forall w m s E g (e : QFBV64.exp w) m' E' g' cs lrs,
  mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
  newer_than_vm g m ->
  newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf :
  forall w m s E g (e : QFBV64.exp w) m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res :
  forall w m s E g (e : QFBV64.exp w) m' E' g' cs lrs,
  mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
  newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen :
  forall w m s E g (e : QFBV64.exp w) m' E' g' cs lrs,
  mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
  (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_consistent :
  forall w m s E g (e : QFBV64.exp w) m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_enc :
  forall w m s E g (e : QFBV64.exp w) m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    enc_bits E' lrs (QFBV64.eval_exp e s).
Proof.
Admitted.

Lemma mk_env_exp_preserve :
  forall w m s E g (e : QFBV64.exp w) m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_sat :
  forall w m s E g (e : QFBV64.exp w) m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    interp_cnf E' cs.
Proof.
Admitted.



(* ===== bit_blast_bexp ===== *)

Fixpoint bit_blast_bexp (m : vm) (g : generator) (e : QFBV64.bexp) : vm * generator * cnf * literal :=
  match e with
  | QFBV64.bvFalse => (m, g, [], lit_ff)
  | QFBV64.bvTrue => (m, g, [], lit_tt)
  | QFBV64.bvEq _ e1 e2 =>
    let '(m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let '(g', cs, r) := bit_blast_eq g2 ls1 ls2 in
    (m2, g', cs1++cs2++cs, r)
  | QFBV64.bvConj e1 e2 =>
    let '(m1, g1, cs1, l1) := bit_blast_bexp m g e1 in
    let '(m2, g2, cs2, l2) := bit_blast_bexp m1 g1 e2 in
    let '(g', cs, r) := bit_blast_conj g2 l1 l2 in
    (m2, g', cs1++cs2++cs, r)
  end.

Fixpoint mk_env_bexp (m : vm) (s : QFBV64.State.t) (E : env) (g : generator) (e : QFBV64.bexp) : vm * env * generator * cnf * literal :=
  match e with
  | QFBV64.bvFalse => (m, E, g, [], lit_ff)
  | QFBV64.bvTrue => (m, E, g, [], lit_tt)
  | QFBV64.bvEq _ e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(E', g', cs, r) := mk_env_eq E2 g2 (QFBV64.eval_exp e1 s) (QFBV64.eval_exp e2 s) ls1 ls2 in
    (m2, E', g', cs1++cs2++cs, r)
  | QFBV64.bvConj e1 e2 =>
    let '(m1, E1, g1, cs1, l1) := mk_env_bexp m s E g e1 in
    let '(m2, E2, g2, cs2, l2) := mk_env_bexp m1 s E1 g1 e2 in
    let '(E', g', cs, r) := mk_env_conj E2 g2 (QFBV64.eval_bexp e1 s) (QFBV64.eval_bexp e2 s) l1 l2 in
    (m2, E', g', cs1++cs2++cs, r)
  end.

Lemma bit_blast_bexp_false_consistent :
  forall (m : vm) (g : generator) (E : env) (m' : vm) (g' : generator)
         (cs : cnf) (lrs : literal) (s : QFBV64.State.t),
    bit_blast_bexp m g QFBV64.bvFalse = (m', g', cs, lrs) ->
    consistent m' E s -> consistent m E s.
Proof.
  move=> im ig E om og cs lrs s [] <-. done.
Qed.

Lemma bit_blast_bexp_true_consistent :
  forall (m : vm) (g : generator) (E : env) (m' : vm) (g' : generator)
         (cs : cnf) (lrs : literal) (s : QFBV64.State.t),
    bit_blast_bexp m g QFBV64.bvTrue = (m', g', cs, lrs) ->
    consistent m' E s -> consistent m E s.
Proof.
  move=> im ig E om og cs lrs s [] <-. done.
Qed.

Lemma bit_blast_bexp_eq_consistent :
  forall (w : nat) (e1 e2 : QFBV64.exp w) (m : vm) (g : generator)
         (E : env) (m' : vm) (g' : generator) (cs : cnf) (lrs : literal)
         (s : QFBV64.State.t),
    bit_blast_bexp m g (QFBV64.bvEq w e1 e2) = (m', g', cs, lrs) ->
    consistent m' E s -> consistent m E s.
Proof.
  move=> w e1 e2 im ig E om og ocs olrs s. rewrite /bit_blast_bexp.
  case Hblast1: (bit_blast_exp im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblasteq: (bit_blast_eq g2 rs1 rs2) => [[geq cseq] req].
  case=> Hom Hog Hocs Holrs. rewrite -Hom => {Hom om} Hcon2.
  apply: (bit_blast_exp_consistent Hblast1).
  apply: (bit_blast_exp_consistent Hblast2).
  exact: Hcon2.
Qed.

Lemma bit_blast_bexp_conj_consistent :
  forall b : QFBV64.bexp,
    (forall (m : vm) (g : generator) (E : env) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : literal) (s : QFBV64.State.t),
        bit_blast_bexp m g b = (m', g', cs, lrs) -> consistent m' E s -> consistent m E s) ->
    forall b0 : QFBV64.bexp,
      (forall (m : vm) (g : generator) (E : env) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : literal) (s : QFBV64.State.t),
          bit_blast_bexp m g b0 = (m', g', cs, lrs) ->
          consistent m' E s -> consistent m E s) ->
      forall (m : vm) (g : generator) (E : env) (m' : vm) (g' : generator)
             (cs : cnf) (lrs : literal) (s : QFBV64.State.t),
        bit_blast_bexp m g (QFBV64.bvConj b b0) = (m', g', cs, lrs) ->
        consistent m' E s -> consistent m E s.
Proof.
  move=> e1 IH1 e2 IH2 im ig E om og ocs olrs s. rewrite /=.
  case Hblast1: (bit_blast_bexp im ig e1) => [[[m1 g1] cs1] l1].
  case Hblast2: (bit_blast_bexp m1 g1 e2) => [[[m2 g2] cs2] l2].
  case=> Hom Hog Hocs Holrs. rewrite -Hom => Hcon2.
  apply: (IH1 _ _ _ _ _ _ _ _ Hblast1).
  apply: (IH2 _ _ _ _ _ _ _ _ Hblast2).
  exact: Hcon2.
Qed.

Lemma bit_blast_bexp_consistent :
  forall m g (e : QFBV64.bexp) E m' g' cs lrs s,
    bit_blast_bexp m g e = (m', g', cs, lrs) ->
    consistent m' E s ->
    consistent m E s.
Proof.
  move=> m g e. elim: e m g.
  - exact: bit_blast_bexp_false_consistent.
  - exact: bit_blast_bexp_true_consistent.
  - exact: bit_blast_bexp_eq_consistent.
  - exact: bit_blast_bexp_conj_consistent.
Qed.

Lemma bit_blast_bexp_false :
  forall (m : vm) (g : generator) (s : QFBV64.State.t)
         (E : env) (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g QFBV64.bvFalse = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    interp_literal E lr = QFBV64.eval_bexp QFBV64.bvFalse s.
Proof.
  move=> im ig s E om og ocs olr [] <- _ <- <- Hcon Htt /=.
  rewrite /= in Htt *. rewrite Htt. done.
Qed.

Lemma bit_blast_bexp_true :
  forall (m : vm) (g : generator) (s : QFBV64.State.t)
         (E : env) (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g QFBV64.bvTrue = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    interp_literal E lr = QFBV64.eval_bexp QFBV64.bvTrue s.
Proof.
  move=> im ig s E om og ocs olrs [] <- _ <- <- Hcon Htt.
  rewrite /= in Htt *. exact: Htt.
Qed.

Lemma bit_blast_bexp_eq :
  forall (w : nat) (e1 e2 : QFBV64.exp w) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env) (m' : vm) (g' : generator)
         (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvEq w e1 e2) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    interp_literal E lr = QFBV64.eval_bexp (QFBV64.bvEq w e1 e2) s.
Proof.
  move=> w e1 e2 im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) (lock interp_literal) /= -!lock.
  case Hblast1: (bit_blast_exp im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblasteq: (bit_blast_eq g2 rs1 rs2) => [[geq cseq] req].
  case => Hom Hog Hocs Holrs Hcon Hcs. rewrite -Hocs in Hcs => {Hocs ocs}.
  rewrite Hog in Hblasteq => {Hog geq}. rewrite Hom in Hblast2 => {Hom m2}.
  rewrite Holrs in Hblasteq => {Holrs req}.
  rewrite 2!add_prelude_append in Hcs. move/andP: Hcs => [Hcs1 Hcs].
  move/andP: Hcs => [Hcs2 Hcseq].
  move: (bit_blast_exp_correct
           Hblast1 (bit_blast_exp_consistent Hblast2 Hcon) Hcs1) => Henc1.
  move: (bit_blast_exp_correct Hblast2 Hcon Hcs2) => Henc2.
  exact: (bit_blast_eq_correct Hblasteq Henc1 Henc2 Hcseq).
Qed.

Lemma bit_blast_bexp_conj :
  forall b : QFBV64.bexp,
    (forall (m : vm) (g : generator) (s : QFBV64.State.t)
            (E : env) (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp m g b = (m', g', cs, lr) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) -> interp_literal E lr = QFBV64.eval_bexp b s) ->
    forall b0 : QFBV64.bexp,
      (forall (m : vm) (g : generator) (s : QFBV64.State.t)
              (E : env) (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
          bit_blast_bexp m g b0 = (m', g', cs, lr) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) -> interp_literal E lr = QFBV64.eval_bexp b0 s) ->
      forall (m : vm) (g : generator) (s : QFBV64.State.t)
             (E : env) (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp m g (QFBV64.bvConj b b0) = (m', g', cs, lr) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        interp_literal E lr = QFBV64.eval_bexp (QFBV64.bvConj b b0) s.
Proof.
  move=> e1 IH1 e2 IH2 im ig s E om og ocs olr.
  rewrite (lock interp_cnf) /bit_blast_bexp -/bit_blast_bexp /= -lock.
  case Hblast1: (bit_blast_bexp im ig e1) => [[[m1 g1] cs1] r1].
  case Hblast2: (bit_blast_bexp m1 g1 e2) => [[[m2 g2] cs2] r2].
  case => Hom Hog Hocs Holr Hcon Hcnf. rewrite -Hocs in Hcnf => {ocs Hocs}.
  rewrite -Hom in Hcon => {Hom om}.
  rewrite 2!add_prelude_append in Hcnf. move/andP: Hcnf => [Hcs1 Hcnf].
  move/andP: Hcnf => [Hcs2 Hcnf].
  have Heq: interp_literal E olr = (interp_literal E r1 && interp_literal E r2).
  {
    rewrite -Holr. move: Hcnf; rewrite /=. rewrite !interp_literal_neg_lit.
    move: (add_prelude_tt Hcs1) => /= -> /=.
    by case: (E g2); case: (interp_literal E r1); case: (interp_literal E r2).
  }
  rewrite Heq.
  have H: (forall P1 P2 Q1 Q2,
              ((P1 = Q1) /\ (P2 = Q2)) -> ((P1 && P2) = (Q1 && Q2)))
    by move=> P1 P2 Q1 Q2 [H1 H2]; rewrite H1 H2. apply: H. split.
  - exact: (IH1 _ _ _ _ _ _ _ _
                Hblast1 (bit_blast_bexp_consistent Hblast2 Hcon) Hcs1).
  - exact: (IH2 _ _ _ _ _ _ _ _ Hblast2 Hcon Hcs2).
Qed.

Corollary bit_blast_bexp_correct :
  forall m g (e : QFBV64.bexp) s E m' g' cs lr,
    bit_blast_bexp m g e = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    interp_literal E lr = QFBV64.eval_bexp e s.
Proof.
  move=> m g e. elim: e m g.
  - exact: bit_blast_bexp_false.
  - exact: bit_blast_bexp_true.
  - exact: bit_blast_bexp_eq.
  - exact: bit_blast_bexp_conj.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) ->
    bit_blast_bexp m g QFBV64.bvFalse = (m', g', cs, lr).
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> <- _ <- <- <-. reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) ->
    bit_blast_bexp m g QFBV64.bvTrue = (m', g', cs, lr).
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> <- _ <- <- <-. reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_eq :
  forall (w : nat) (e1 e2 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvEq w e1 e2) = (m', E', g', cs, lr) ->
    bit_blast_bexp m g (QFBV64.bvEq w e1 e2) = (m', g', cs, lr).
Proof.
  move=> w e1 e2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 (QFBV64.eval_exp e1 s) (QFBV64.eval_exp e2 s) ls1 ls2)
  => [[[E_eq g_eq] cs_eq] r_eq]. case=> <- _ <- <- <-.
  rewrite (mk_env_exp_is_bit_blast_exp Henv1).
  rewrite (mk_env_exp_is_bit_blast_exp Henv2).
  rewrite (mk_env_eq_is_bit_blast_eq Heq). reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_conj :
  forall b : QFBV64.bexp,
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        bit_blast_bexp m g b = (m', g', cs, lr)) ->
    forall b0 : QFBV64.bexp,
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          bit_blast_bexp m g b0 = (m', g', cs, lr)) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvConj b b0) = (m', g', cs, lr).
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /=.
  case Henv1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] l1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] l2].
  case=> <- _ <- <- <-. rewrite (IH1 _ _ _ _ _ _  _ _ _ Henv1).
  rewrite (IH2 _ _ _ _ _ _  _ _ _ Henv2). reflexivity.
Qed.

Corollary mk_env_bexp_is_bit_blast_bexp :
  forall m s E g e m' E' g' cs lr,
    mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
    bit_blast_bexp m g e = (m', g', cs, lr).
Proof.
  move=> m s E g e. elim: e m s E g.
  - exact: mk_env_bexp_is_bit_blast_bexp_false.
  - exact: mk_env_bexp_is_bit_blast_bexp_true.
  - exact: mk_env_bexp_is_bit_blast_bexp_eq.
  - exact: mk_env_bexp_is_bit_blast_bexp_conj.
Qed.

Lemma mk_env_bexp_newer_vm_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> m s E g m' E' g' cs lr. case=> <- _ <- _ _. done.
Qed.

Lemma mk_env_bexp_newer_vm_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> m s E g m' E' g' cs lr. case=> <- _ <- _ _. done.
Qed.

Lemma mk_env_bexp_newer_vm_eq :
  forall (w : nat) (e1 e2 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvEq w e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 e2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 (QFBV64.eval_exp e1 s) (QFBV64.eval_exp e2 s) ls1 ls2)
  => [[[oE og] ocs] olr]. case=> <- _ <- _ _ Hnew.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  exact: (mk_env_eq_newer_vm Heq Hnew2).
Qed.

Lemma mk_env_bexp_newer_vm_conj :
  forall b : QFBV64.bexp,
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall b0 : QFBV64.bexp,
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /=.
  case Henv1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case=> <- _ <- _ _ Hnew. apply: newer_than_vm_add_diag_r.
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2). apply: (IH1 _ _ _ _ _ _ _ _ _ Henv1).
  exact: Hnew.
Qed.

Corollary mk_env_bexp_newer_vm :
  forall m s E g e m' E' g' cs lr,
    mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> m s E g e. elim: e m s E g.
  - exact: mk_env_bexp_newer_vm_false.
  - exact: mk_env_bexp_newer_vm_true.
  - exact: mk_env_bexp_newer_vm_eq.
  - exact: mk_env_bexp_newer_vm_conj.
Qed.

Corollary mk_env_bexp_newer_cnf :
  forall m s E g e m' E' g' cs lr,
    mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_cnf g' cs.
Proof.
Admitted.

Corollary mk_env_bexp_newer_res :
  forall m s E g e m' E' g' cs lr,
    mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
    newer_than_lit g' lr.
Proof.
Admitted.

Corollary mk_env_bexp_newer_gen :
  forall m s E g e m' E' g' cs lr,
    mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_bexp_consistent_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) ->
    newer_than_vm g m ->
    consistent m E s -> consistent m' E' s.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> <- <- _ _ _. move=> _ H; exact: H.
Qed.

Lemma mk_env_bexp_consistent_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) ->
    newer_than_vm g m ->
    consistent m E s -> consistent m' E' s.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> <- <- _ _ _. move=> _ H; exact: H.
Qed.

Lemma mk_env_bexp_consistent_eq :
  forall (w : nat) (e1 e2 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvEq w e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m ->
    consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 e2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 (QFBV64.eval_exp e1 s) (QFBV64.eval_exp e2 s) ls1 ls2)
  => [[[oE og] ocs] or]. case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (mk_env_eq_consistent Heq Hnew2).
  apply: (mk_env_exp_consistent Henv2 Hnew1).
  exact: (mk_env_exp_consistent Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_conj :
  forall b : QFBV64.bexp,
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        consistent m E s -> consistent m' E' s) ->
    forall b0 : QFBV64.bexp,
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m ->
          consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case Hconj: (mk_env_conj E2 g2 (QFBV64.eval_bexp e1 s) (QFBV64.eval_bexp e2 s)
                           lr1 lr2)=> [[[oE og] ocs] olr].
  case=> <- <- _ _ _ Hnew Hcon.
  apply: (mk_env_conj_consistent Hconj).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 (mk_env_bexp_newer_vm Henv1 Hnew)).
  apply: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew). exact: Hcon.
Qed.

Corollary mk_env_bexp_consistent :
  forall m s E g e m' E' g' cs lr,
    mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
    newer_than_vm g m ->
    consistent m E s ->
    consistent m' E' s.
Proof.
  move=> m s E g e. elim: e m s E g.
  - exact: mk_env_bexp_consistent_false.
  - exact: mk_env_bexp_consistent_true.
  - exact: mk_env_bexp_consistent_eq.
  - exact: mk_env_bexp_consistent_conj.
Qed.

Corollary mk_env_bexp_enc :
  forall m s E g e m' E' g' cs lr,
    mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
    enc_bit E' lr (QFBV64.eval_bexp e s).
Proof.
Admitted.

Corollary mk_env_bexp_preserve :
  forall m s E g e m' E' g' cs lr,
    mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_bexp_sat_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) ->
    enc_bit E' lr (QFBV64.eval_bexp QFBV64.bvFalse s) ->
    newer_than_vm g m ->
    interp_cnf E' cs.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ <- _ <- _ _ Hnew. done.
Qed.

Lemma mk_env_bexp_sat_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) ->
    enc_bit E' lr (QFBV64.eval_bexp QFBV64.bvTrue s) ->
    newer_than_vm g m ->
    interp_cnf E' cs.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ <- _ <- _ _ Hnew. done.
Qed.

Lemma mk_env_bexp_sat_eq :
  forall (w : nat) (e1 e2 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvEq w e1 e2) = (m', E', g', cs, lr) ->
    enc_bit E' lr (QFBV64.eval_bexp (QFBV64.bvEq w e1 e2) s) ->
    newer_than_vm g m ->
    interp_cnf E' cs.
Proof.
  move=> w e1 e2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 (QFBV64.eval_exp e1 s) (QFBV64.eval_exp e2 s) ls1 ls2)
  => [[[oE og] ocs] olr]. case=> _ <- _ <- _ _ Hnew.
  rewrite 2!interp_cnf_append. move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew_g1m1.
  move: (mk_env_exp_sat Henv1) => Hcnf_E1cs1.
  move: (mk_env_exp_sat Henv2) => Hcnf_E2cs2.
  move: (mk_env_exp_newer_cnf Henv1 Hnew) => Hnew_g1cs1.
  move: (mk_env_exp_newer_cnf Henv2 Hnew_g1m1) => Hnew_g2cs2.
  move: (mk_env_exp_newer_gen Henv2) => H_g1leg2.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1leg2) => Hnew_g2cs1.
  move: (mk_env_exp_newer_res Henv1) => Hnew_g1ls1.
  move: (mk_env_exp_newer_res Henv2) => Hnew_g2ls2.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1leg2) => Hnew_g2ls1.
  move: (mk_env_eq_preserve Heq) => Hpre_E2oEg2.
  move: (mk_env_exp_preserve Henv2) => Hpre_E1E2g1.
  move: (mk_env_exp_enc Henv1) => Henc_E1ls1.
  move: (env_preserve_enc_bits Hpre_E1E2g1 Hnew_g1ls1 Henc_E1ls1) => Henc_E2ls1.
  move: (mk_env_exp_enc Henv2) => Henc_E2ls2.
  (* interp_cnf oE ocs *)
  rewrite (mk_env_eq_sat Heq Henc_E2ls1 Henc_E2ls2 Hnew_g2ls1 Hnew_g2ls2).
  (* interp_cnf oE cs2 *)
  rewrite (env_preserve_cnf Hpre_E2oEg2 Hnew_g2cs2).
  rewrite Hcnf_E2cs2.
  (* interp_cnf oE cs1 *)
  rewrite (env_preserve_cnf Hpre_E2oEg2 Hnew_g2cs1).
  rewrite (env_preserve_cnf Hpre_E1E2g1 Hnew_g1cs1).
  rewrite Hcnf_E1cs1.
  done.
Qed.

Lemma mk_env_bexp_sat_conj :
  forall b : QFBV64.bexp,
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        enc_bit E' lr (QFBV64.eval_bexp b s) -> newer_than_vm g m -> interp_cnf E' cs) ->
    forall b0 : QFBV64.bexp,
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          enc_bit E' lr (QFBV64.eval_bexp b0 s) -> newer_than_vm g m -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
        enc_bit E' lr (QFBV64.eval_bexp (QFBV64.bvConj b b0) s) ->
        newer_than_vm g m -> interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /=.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case=> _ <- _ <- Hlr Henc Hnew. rewrite 2!interp_cnf_append.
  move: (mk_env_bexp_preserve Henv2) => Hpre_E1E2g1.
  move: (mk_env_bexp_newer_gen Henv2) => H_g1leg2.
  move: (mk_env_bexp_newer_cnf Henv1 Hnew) => Hnew_g1cs1.
  move: (mk_env_bexp_newer_vm Henv1 Hnew) => Hnew_g1m1.
  move: (mk_env_bexp_newer_res Henv1) => Hnew_g1lr1.
  move: (mk_env_bexp_enc Henv1) => Henc_E1lr1.
  move: (mk_env_bexp_enc Henv2) => Henc_E2lr2.
  (* interp_cnf E2 cs1 *)
  rewrite (env_preserve_cnf Hpre_E1E2g1 Hnew_g1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Henv1 Henc_E1lr1 Hnew).
  (* interp_cnf E2 cs2 *)
  rewrite (IH2 _ _ _ _ _ _ _ _ _ Henv2 Henc_E2lr2 Hnew_g1m1).
  (* *)
  rewrite /=. rewrite !interp_literal_neg_lit.
  rewrite /enc_bit -Hlr /= in Henc. rewrite (eqP Henc).
  move: (env_preserve_enc_bit Hpre_E1E2g1 Hnew_g1lr1 Henc_E1lr1) => Henc_E2lr1.
  rewrite (eqP Henc_E2lr1) (eqP Henc_E2lr2) /=.
  set b1 := QFBV64.eval_bexp e1 s.
  set b2 := QFBV64.eval_bexp e2 s.
  by case: b1; case: b2.
Qed.

Corollary mk_env_bexp_sat :
  forall m s E g e m' E' g' cs lr,
    mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
    newer_than_vm g m ->
    interp_cnf E' cs.
Proof.
  move=> m s E g e m' E' g' cs lr Henv. move: (mk_env_bexp_enc Henv).
  elim: e m s E g m' E' g' cs lr Henv.
  - exact: mk_env_bexp_sat_false.
  - exact: mk_env_bexp_sat_true.
  - exact: mk_env_bexp_sat_eq.
  - exact: mk_env_bexp_sat_conj.
Qed.

Lemma mk_env_bexp_tt :
  forall m s E g e m' E' g' cs lr,
    mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
    interp_literal E' lit_tt.
Proof.
Admitted.

Definition init_vm := VM.empty (wordsize.-tuple literal).
Definition init_gen := var_tt.
Definition init_env : env := fun _ => true.

Lemma init_newer_than_vm :
  newer_than_vm init_gen init_vm.
Proof.
  done.
Qed.

Definition mk_env (s : QFBV64.State.t) (e : QFBV64.bexp) : env :=
  let '(m', E', g, cs, lr) := mk_env_bexp init_vm s init_env init_gen e in
  E'.

Lemma init_consistent :
  forall s, consistent init_vm init_env s.
Proof.
  move=> s x. rewrite /consistent1 /init_vm. rewrite VM.Lemmas.empty_o. done.
Qed.

Lemma mk_env_consistent :
  forall s e m g cs lr,
    bit_blast_bexp init_vm init_gen e = (m, g, cs, lr) ->
    consistent m (mk_env s e) s.
Proof.
  move=> s e m g cs lr Hbb. rewrite /mk_env.
  set m' := mk_env_bexp init_vm s init_env init_gen e.
  have: mk_env_bexp init_vm s init_env init_gen e = m' by reflexivity. move: m'.
  case=> [[[[m' E'] g'] cs'] lr'] Henv.
  move: (mk_env_bexp_is_bit_blast_bexp Henv). rewrite Hbb. case=> Hm Hg Hcs Hlr.
  rewrite Hm. apply: (mk_env_bexp_consistent Henv init_newer_than_vm).
  exact: init_consistent.
Qed.

Lemma mk_env_tt :
  forall s e, interp_literal (mk_env s e) lit_tt.
Proof.
  move=> s e. rewrite /mk_env.
  set m' := mk_env_bexp init_vm s init_env init_gen e.
  have: mk_env_bexp init_vm s init_env init_gen e = m' by reflexivity. move: m'.
  case=> [[[[m' E'] g'] cs'] lr'] Henv. exact: (mk_env_bexp_tt Henv).
Qed.

Lemma mk_env_sat :
  forall s e m g cs lr,
    bit_blast_bexp init_vm init_gen e = (m, g, cs, lr) ->
    interp_cnf (mk_env s e) cs.
Proof.
  move=> s e m g cs lr Hbb. rewrite /mk_env.
  set m' := mk_env_bexp init_vm s init_env init_gen e.
  have: mk_env_bexp init_vm s init_env init_gen e = m' by reflexivity. move: m'.
  case=> [[[[m' E'] g'] cs'] lr'] Henv. move: (mk_env_bexp_is_bit_blast_bexp Henv).
  rewrite Hbb; case=> _ _ -> _. exact: (mk_env_bexp_sat Henv init_newer_than_vm).
Qed.

Definition mk_state (E : env) (m : vm) : QFBV64.State.t.
Proof.
Admitted.

Lemma mk_state_consistent :
  forall E m, consistent m E (mk_state E m).
Proof.
Admitted.

Lemma valid_implies_unsat :
  forall premises goal,
    (forall E, ~~ interp_cnf E (add_prelude premises) || interp_literal E goal) ->
    ~ (sat (add_prelude ([neg_lit goal]::premises))).
Proof.
  move=> premises goal H1 [E H2]. move: (H1 E) => {H1} H1.
  rewrite add_prelude_cons in H2. move/andP: H2 => [H2 H3].
  move/orP: H1. case => H1.
  - move/negP: H1. apply. exact: H3.
  - rewrite add_prelude_expand in H2. move/andP: H2 => [_ H2].
    rewrite /= interp_literal_neg_lit in H2. move/negP: H2; apply.
    exact: H1.
Qed.

Lemma unsat_implies_valid :
  forall premises goal,
    ~ (sat (add_prelude ([neg_lit goal]::premises))) ->
    (forall E, ~~ interp_cnf E (add_prelude premises) || interp_literal E goal).
Proof.
  move=> premises goal H E. case Hgoal: (interp_literal E goal).
  - by rewrite orbT.
  - rewrite orbF. apply/negP => H2. apply: H. exists E.
    rewrite add_prelude_cons H2 andbT.
    rewrite add_prelude_expand /=  interp_literal_neg_lit.
    rewrite Hgoal andbT. exact: (add_prelude_tt H2).
Qed.

Lemma bit_blast_sound :
  forall (e : QFBV64.bexp) m' g' cs lr,
    bit_blast_bexp init_vm init_gen e = (m', g', cs, lr) ->
    ~ (sat (add_prelude ([neg_lit lr]::cs))) ->
    QFBV64.valid e.
Proof.
  move=> e m' g' cs lr Hblast Hsat s.
  move: (unsat_implies_valid Hsat) => {Hsat} Hsat.
  move: (Hsat (mk_env s e)) => {Hsat} Hsat.
  move: (mk_env_sat s Hblast) => Hcs. move: (mk_env_tt s e) => Htt.
  have Hprelude: interp_cnf (mk_env s e) (add_prelude cs)
    by rewrite add_prelude_expand Hcs Htt.
  rewrite -(bit_blast_bexp_correct Hblast (mk_env_consistent s Hblast) Hprelude).
  rewrite Hprelude /= in Hsat. exact: Hsat.
Qed.

Lemma bit_blast_complete :
  forall (e : QFBV64.bexp) m' g' cs lr,
    bit_blast_bexp init_vm init_gen e = (m', g', cs, lr) ->
    QFBV64.valid e ->
    ~ (sat (add_prelude ([neg_lit lr]::cs))).
Proof.
  move=> e m' g' cs lr Hblast He.
  move=> [E Hcs]. move: (He (mk_state E m')) => {He} He.
  rewrite add_prelude_cons in Hcs. move/andP: Hcs => [Hlr Hcs].
  rewrite add_prelude_expand in Hlr. move/andP: Hlr => [Htt Hlr].
  rewrite /= interp_literal_neg_lit in Hlr.
  rewrite -(bit_blast_bexp_correct Hblast (mk_state_consistent E m') Hcs) in He.
  rewrite He in Hlr. exact: not_false_is_true.
Qed.
