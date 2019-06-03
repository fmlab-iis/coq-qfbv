
(*
 * Require the following libraries:
 * - coq-bit from https://github.com/mht208/coq-bits
 * - ssrlib from https://github.com/mht208/coq-ssrlib.git
 *)

From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From BitBlasting Require Import QFBVSimple CNF.
From ssrlib Require Import Bools Var Store SsrOrdered ZAriths Tuples.
From Bits Require Export bits.

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
  rewrite !interp_lit_neg_lit.
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
  rewrite !interp_lit_neg_lit.
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

Definition vm := VM.t (wordsize.-tuple literal).

Definition newer_than_vm g (m : vm) :=
  forall v rs, VM.find v m = Some rs -> newer_than_lits g rs.

Lemma newer_than_vm_add_r :
  forall x (m : vm) y,
    newer_than_vm x m -> newer_than_vm (x + y) m.
Proof.
  move=> x m y Hnew v rs Hfind. move: (Hnew v rs Hfind).
  exact: newer_than_lits_add_r.
Qed.

Lemma newer_than_vm_le_newer :
  forall x (m : vm) y,
    newer_than_vm x m -> (x <=? y)%positive -> newer_than_vm y m.
Proof.
  move=> x m y Hnew Hle v rs Hfind. move: (Hnew v rs Hfind) => {Hnew} Hnew.
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

Lemma env_preserve_consistent :
  forall m E E' g s,
    newer_than_vm g m ->
    env_preserve E E' g ->
    consistent m E s ->
    consistent m E' s.
Proof.
  move=> m E E' g s Hnew_gm Hpre Hcon. move=> x; rewrite /consistent1.
  case Hfind: (VM.find x m); last by done. move: (Hnew_gm x _ Hfind) => Hnew_glsx.
  move: (Hcon x); rewrite /consistent1. rewrite Hfind.
  exact: (env_preserve_enc_bits Hpre Hnew_glsx).
Qed.

Definition vm_preserve (m m' : vm) : Prop :=
  forall v ls, VM.find v m = Some ls -> VM.find v m' = Some ls.

Lemma vm_preserve_consistent :
  forall m m' s E,
    vm_preserve m m' -> consistent m' E s -> consistent m E s.
Proof.
  move=> m m' s E Hpre Hcon v. rewrite /consistent1. case Hfind: (VM.find v m).
  - move: (Hpre _ _ Hfind) => Hfind'. move: (Hcon v). rewrite /consistent1.
    rewrite  Hfind'. by apply.
  - done.
Qed.

Lemma vm_preserve_refl : forall m, vm_preserve m m.
Proof.
  move=> m. done.
Qed.

Lemma vm_preserve_trans :
  forall m1 m2 m3, vm_preserve m1 m2 -> vm_preserve m2 m3 -> vm_preserve m1 m3.
Proof.
  move=> m1 m2 m3 H12 H23 v ls Hfind1. move: (H12 _ _ Hfind1) => Hfind2.
  exact: (H23 _ _ Hfind2).
Qed.

Lemma vm_preserve_add_diag :
  forall m v ls,
    VM.find v m = None ->
    vm_preserve m (VM.add v ls m).
Proof.
  move=> m v ls Hfind x xls Hfindx. case Hxv: (x == v).
  - rewrite (eqP Hxv) Hfind in Hfindx. discriminate.
  - move/negP: Hxv => Hxv. rewrite (VM.Lemmas.find_add_neq _ _ Hxv). assumption.
Qed.



(* ===== Tactics ===== *)

Ltac dcase t := move: (refl_equal t); generalize t at -1.

Ltac fresh_name t :=
  match t with
  | vm => fresh "m"
  | env => fresh "E"
  | generator => fresh "g"
  | cnf => fresh "cs"
  | _.-tuple literal => fresh "ls"
  | literal => fresh "l"
  | _ => fresh
  end.

Ltac dcase_hyps :=
  match goal with
  | H : context f [let '_ := ?r in _] |- _ =>
    move: H;
    let H1 := fresh in
    let H2 := fresh in
    lazymatch type of r with
    | prod (prod (prod (prod ?t1 ?t2) ?t3) ?t4) ?t5 =>
      let t1 := fresh_name t1 in
      let t2 := fresh_name t2 in
      let t3 := fresh_name t3 in
      let t4 := fresh_name t4 in
      let t5 := fresh_name t5 in
      dcase r; move=> [[[[t1 t2] t3] t4] t5] H1 H2; dcase_hyps
    | prod (prod (prod ?t1 ?t2) ?t3) ?t4 =>
      let t1 := fresh_name t1 in
      let t2 := fresh_name t2 in
      let t3 := fresh_name t3 in
      let t4 := fresh_name t4 in
      dcase r; move=> [[[t1 t2] t3] t4] H1 H2; dcase_hyps
    | prod (prod ?t1 ?t2) ?t3 =>
      let t1 := fresh_name t1 in
      let t2 := fresh_name t2 in
      let t3 := fresh_name t3 in
      dcase r; move=> [[t1 t2] t3] H1 H2; dcase_hyps
    | prod ?t1 ?t2 =>
      let t1 := fresh_name t1 in
      let t2 := fresh_name t2 in
      dcase r; move=> [t1 t2] H1 H2; dcase_hyps
    end
  | H : context f [if ?c then _ else _] |- _ =>
    move: H;
    let H1 := fresh in
    let H2 := fresh in
    dcase c=> H1 H2; dcase_hyps
  | H : (_, _, _, _, _) = (_, _, _, _, _) |- _ =>
    case: H;
    let H1 := fresh in
    let H2 := fresh in
    let H3 := fresh in
    let H4 := fresh in
    let H5 := fresh in
    move=> H1 H2 H3 H4 H5; dcase_hyps
  | H : (_, _, _, _) = (_, _, _, _) |- _ =>
    case: H;
    let H1 := fresh in
    let H2 := fresh in
    let H3 := fresh in
    let H4 := fresh in
    move=> H1 H2 H3 H4; dcase_hyps
  | H : (_, _, _) = (_, _, _) |- _ =>
    case: H;
    let H1 := fresh in
    let H2 := fresh in
    let H3 := fresh in
    move=> H1 H2 H3; dcase_hyps
  | H : (_, _) = (_, _) |- _ =>
    case: H;
    let H1 := fresh in
    let H2 := fresh in
    move=> H1 H2; dcase_hyps
  | H : context f [match ?t with | None => _ | Some _ => _ end] |- _ =>
    move: H;
    let H1 := fresh in
    let H2 := fresh in
    dcase t; case => H1 H2; dcase_hyps
  | H : context f [match ?t with | Some _ => _ | None => _ end] |- _ =>
    move: H;
    let H1 := fresh in
    let H2 := fresh in
    dcase t; case => H1 H2; dcase_hyps
  | |- _ => idtac
  end.

Ltac dcase_goal :=
  match goal with
  | |- context f [let '_ := ?r in _] =>
    let H := fresh in
    lazymatch type of r with
    | prod (prod (prod (prod ?t1 ?t2) ?t3) ?t4) ?t5 =>
      let t1 := fresh_name t1 in
      let t2 := fresh_name t2 in
      let t3 := fresh_name t3 in
      let t4 := fresh_name t4 in
      let t5 := fresh_name t5 in
      dcase r; move=> [[[[t1 t2] t3] t4] t5] H; dcase_goal
    | prod (prod (prod ?t1 ?t2) ?t3) ?t4 =>
      let t1 := fresh_name t1 in
      let t2 := fresh_name t2 in
      let t3 := fresh_name t3 in
      let t4 := fresh_name t4 in
      dcase r; move=> [[[t1 t2] t3] t4] H; dcase_goal
    | prod (prod ?t1 ?t2) ?t3 =>
      let t1 := fresh_name t1 in
      let t2 := fresh_name t2 in
      let t3 := fresh_name t3 in
      dcase r; move=> [[t1 t2] t3] H; dcase_goal
    | prod ?t1 ?t2 =>
      let t1 := fresh_name t1 in
      let t2 := fresh_name t2 in
      dcase r; move=> [t1 t2] H; dcase_goal
    end
  | |- (_, _, _, _, _) = (_, _, _, _, _) =>
    let H1 := fresh in
    let H2 := fresh in
    let H3 := fresh in
    let H4 := fresh in
    let H5 := fresh in
    case=> H1 H2 H3 H4 H5; dcase_goal
  | |- (_, _, _, _) = (_, _, _, _) =>
    let H1 := fresh in
    let H2 := fresh in
    let H3 := fresh in
    let H4 := fresh in
    case=> H1 H2 H3 H4; dcase_goal
  | |- (_, _, _) = (_, _, _) =>
    let H1 := fresh in
    let H2 := fresh in
    let H3 := fresh in
    case=> H1 H2 H3; dcase_goal
  | |- (_, _) = (_, _) =>
    let H1 := fresh in
    let H2 := fresh in
    case=> H1 H2; dcase_goal
  | |- _ => idtac
  end.

Ltac dite_hyps :=
  match goal with
  | H : context f [if ?c then _ else _] |- _ =>
    move: H;
    let H1 := fresh in
    let H2 := fresh in
    dcase c; case=> H1 H2; dite_hyps
  | |- _ => idtac
  end.

Ltac intros_tuple :=
  lazymatch goal with
  | |- forall x : ((_.+1).-tuple _), _ =>
    let hd := fresh x in
    let tl := fresh x in
    case/tupleP=> [hd tl] /=; try rewrite !theadE !beheadCons; intros_tuple
  | |- forall x : _, _ => intro; intros_tuple
  | |- _ => idtac
  end.



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
  (g', [], vs).

Definition mk_env_var E g (bv : BITS wordsize) (v : var) : env * generator * cnf * wordsize.-tuple literal :=
  let '(E', g', vs) := mk_env_var' E g bv in
  (E', g', [], vs).

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
  case Henv: (mk_env_var' E g bs)=> [[E_v g_v] lrs_v].
  case=> <- _ _ <-. exact: (mk_env_var'_enc Henv).
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
  rewrite /mk_env_const /bit_blast_const; intros; dcase_hyps; subst; reflexivity.
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

Lemma mk_env_const_newer_gen :
  forall w E g (bv : BITS w) E' g' cs lrs,
    mk_env_const E g bv = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> w E g bv E' g' cs lrs. case=> _ <- _ _. exact: Pos.leb_refl.
Qed.

Lemma mk_env_const_newer_res :
  forall w E g (bs : BITS w) E' g' cs lrs,
    mk_env_const E g bs = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g' lrs.
Proof.
  move=> w E g bs E' g' cs lrs /=. case=> _ <- _ <- Hnew_gtt {E E' g' cs lrs}.
  elim: w bs.
  - move=> bs /=. rewrite tuple0. done.
  - move=> w IH. case/tupleP=> [bs_hd bs_tl] /=. rewrite (IH _) andbT. case: bs_hd.
    + exact: Hnew_gtt.
    + exact: Hnew_gtt.
Qed.



(* ===== bit_blast_not ===== *)

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

Parameter mk_env_not : forall w : nat, env -> generator -> w.-tuple literal -> env * generator * cnf * w.-tuple literal.

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

Lemma mk_env_not_is_bit_blast_not :
  forall w E g (ls : w.-tuple literal) E' g' cs lrs,
    mk_env_not E g ls = (E', g', cs, lrs) ->
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

Definition mk_env_and1 E g a1 a2 : env * generator * cnf * literal :=
  if (a1 == lit_ff) || (a2 == lit_ff) then (E, g, [], lit_ff)
  else if a1 == lit_tt then (E, g, [], a2)
       else if a2 == lit_tt then (E, g, [], a1)
            else let (g', r) := gen g in
                 let E' := env_upd E (var_of_lit r)
                                   (interp_lit E a1 && interp_lit E a2) in
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

Fixpoint mk_env_and w (E : env) (g : generator) : w.-tuple literal -> w.-tuple literal -> env * generator * cnf * w.-tuple literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(E_hd, g_hd, cs_hd, lrs_hd) := mk_env_and1 E g ls1_hd ls2_hd in
      let '(E_tl, g_tl, cs_tl, lrs_tl) := mk_env_and E_hd g_hd ls1_tl ls2_tl in
      (E_tl, g_tl, cs_hd++cs_tl, cons_tuple lrs_hd lrs_tl)
  else
    fun _ _ =>
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
      rewrite !interp_lit_neg_lit in Hcs. move: Hcs.
      by case: (E g); case: (interp_lit E l1); case: (interp_lit E l2).
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
  forall E g l1 l2 E' g' cs lr,
    mk_env_and1 E g l1 l2 = (E', g', cs, lr) ->
    bit_blast_and1 g l1 l2 = (g', cs, lr).
Proof.
  rewrite /mk_env_and1 /bit_blast_and1; intros;
    dite_hyps; dcase_hyps; subst; reflexivity.
Qed.

(*
Lemma mk_env_and1_sat :
  forall E g E' g' l1 l2 cs lr,
    mk_env_and1 E g l1 l2 = (E', g', cs, lr) ->
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
      rewrite /interp_cnf /interp_clause. rewrite !interp_lit_neg_lit.
      move: (newer_than_lit_neq Hg1) (newer_than_lit_neq Hg2) => Hil1 Hil2.
      rewrite (interp_lit_env_upd_neq iE _ Hil1)
              (interp_lit_env_upd_neq iE _ Hil2).
      rewrite (interp_lit_env_upd_eq_pos iE).
      rewrite (interp_lit_env_upd_eq_neg iE).
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
  rewrite (env_preserve_lit (mk_env_and1_env_preserve Hand1) Hnew1).
  rewrite (env_preserve_lit (mk_env_and1_env_preserve Hand1) Hnew2).
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
*)



(* ===== bit_blast_or ===== *)

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

Parameter mk_env_or : forall w : nat, env -> generator -> w.-tuple literal -> w.-tuple literal -> env * generator * cnf * w.-tuple literal.

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
        rewrite (eqP Hff1) /= !interp_lit_neg_lit.
        move/andP => [Htt Hcs] <-. rewrite Htt orFb. rewrite expand_eq.
        rewrite andbC. exact: Hcs.
      * case Hff2: (l2 == lit_ff).
        -- move=> <- <- /eqP <- /eqP <- /=.
           rewrite (eqP Hff2) /= !interp_lit_neg_lit.
           move/andP => [Htt Hcs] <-. rewrite Htt orbF. rewrite expand_eq.
           rewrite andbC. exact: Hcs.
        -- move=> <- <- /eqP <- /eqP <- /=.
           rewrite /= !interp_lit_neg_lit. move/andP => [Htt Hcs] <-.
           move: Hcs.
           by case: (E g); case: (interp_lit E l1); case: (interp_lit E l2).
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
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_or E g ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_or g ls1 ls2 = (g', cs, lrs).
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

Definition mk_env_full_adder1 E g a1 a2 cin :=
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

Definition mk_env_ite1 E (g : generator) (c : literal) (a1 a2 : literal) : env * generator * cnf * literal :=
  let (g', r) := gen g in
  let E' := env_upd E (var_of_lit r)
                    (if interp_lit E c then interp_lit E a1 else interp_lit E a2)
                    in
  let cs := [
        [neg_lit r; neg_lit c; a1]; [neg_lit r; c; a2];
        [r; c; neg_lit a2]; [r; neg_lit c; neg_lit a1]; [r; neg_lit a1; neg_lit a2]
      ] in
  (E', g', cs, r).

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

Fixpoint mk_env_ite w E (g : generator) (c : literal) : w.-tuple literal -> w.-tuple literal -> env * generator * cnf * w.-tuple literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let '(E_hd, g_hd, cs_hd, lrs_hd) := mk_env_ite1 E g c ls1_hd ls2_hd in
      let '(E_tl, g_tl, cs_tl, lrs_tl) := mk_env_ite E_hd g_hd c ls1_tl ls2_tl in
      (E_tl, g_tl, cs_hd++cs_tl, cons_tuple lrs_hd lrs_tl)
  else
    fun _ _ =>
      (E, g, [], [tuple]).

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
  rewrite /interp_cnf /= !interp_lit_neg_lit.
  move=> H <-. split_andb. move: H0 H1 H2 H3 H4.
  case: (interp_lit E lc) => /=.
  - move=> H1 _ _ H2 _. rewrite expand_eq. by rewrite H1 H2.
  - move=> _ H1 H2 _ _. rewrite expand_eq. by rewrite H1 H2.
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

Lemma mk_env_ite_is_bit_blast_ite :
  forall w E g lc (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_ite E g lc ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_ite g lc ls1 ls2 = (g', cs, lrs).
Proof.
  elim.
  - rewrite /mk_env_ite /bit_blast_ite => E g lc ls1 ls2 E' g' cs lrs [] _ <- <- <-.
    reflexivity.
  - intros_tuple. dcase_hyps; subst. move=> Hls Henv.
    rewrite (H _ _ _ _ _ _ _ _ _ Henv). rewrite (tval_eq Hls). reflexivity.
Qed.

Lemma mk_env_ite_newer_gen :
  forall w E g lc (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_ite E g lc ls1 ls2 = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  elim.
  - move=> E g lc ls1 ls2 E' g' cs lrs [] _ <- _ _. exact: Pos.leb_refl.
  - intros_tuple. dcase_hyps; subst. move=> Hls Henv.
    move: (H _ _ _ _ _ _ _ _ _ Henv) => Hg1g. apply: (pos_leb_trans _ Hg1g).
    exact: (pos_leb_add_diag_r g 1).
Qed.

Lemma mk_env_ite_newer_res :
  forall w E g lc (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_ite E g lc ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lits g' lrs.
Proof.
  elim.
  - move=> E g lc ls1 ls2 E' g' cs lrs [] _ <- _ <-. done.
  - intros_tuple. dcase_hyps; subst. move=> Hls Henv. rewrite -(tval_eq Hls).
    move: (H _ _ _ _ _ _ _ _ _ Henv) => Hnew. rewrite {}Hnew andbT.
    move: (mk_env_ite_newer_gen Henv) => Hg1g. apply: (newer_than_var_le_newer _ Hg1g).
    exact: newer_than_var_add_diag_r.
Qed.

Lemma mk_env_ite_newer_cnf :
  forall w E g lc (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_ite E g lc ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lc ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  elim.
  - move=> E g lc ls1 ls2 E' g' cs lrs [] _ <- <- _ Hnew_glc Hnew_gls1 Hnew_gls2.
    done.
  - intros_tuple. dcase_hyps; subst. move=> _ Henv /=.
    rewrite !newer_than_lit_neg.
    move/andP: H2 => [Hnew_gls1 Hnew_gls0]. move/andP: H3 => [Hnew_gls2 Hnew_gls3].
    move: (mk_env_ite_newer_gen Henv) => Hg1g'.
    move: (newer_than_lit_add_r 1 H1) => Hnew_g1lc.
    move: (newer_than_lit_add_r 1 Hnew_gls1) => Hnew_g1ls1.
    move: (newer_than_lit_add_r 1 Hnew_gls2) => Hnew_g1ls2.
    move: (newer_than_lits_add_r 1 Hnew_gls0) => Hnew_g1ls0.
    move: (newer_than_lits_add_r 1 Hnew_gls3) => Hnew_g1ls3.
    move: (H _ _ _ _ _ _ _ _ _ Henv Hnew_g1lc Hnew_g1ls0 Hnew_g1ls3) => ->.
    move: (newer_than_lit_le_newer Hnew_g1lc Hg1g') => ->.
    move: (newer_than_lit_le_newer Hnew_g1ls1 Hg1g') => ->.
    move: (newer_than_lit_le_newer Hnew_g1ls2 Hg1g') => ->.
    rewrite /newer_than_lit /newer_than_var /=.
    rewrite (pos_ltb_leb_trans (pos_ltb_add_diag_r g 1) Hg1g'). done.
Qed.

Lemma mk_env_ite_preserve :
  forall w E g lc (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_ite E g lc ls1 ls2 = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  elim.
  - move=> E g lc ls1 ls2 E' g' cs lrs /=. case=> <- _ _ _. exact: env_preserve_refl.
  - intros_tuple. dcase_hyps; intros; subst. move: (H _ _ _ _ _ _ _ _ _ H7) => Hpre.
    exact: (env_preserve_env_upd_succ Hpre).
Qed.

Lemma mk_env_ite_sat :
  forall w E g lc (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_ite E g lc ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lc -> newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  elim.
  - move=> E g lc ls1 ls2 E' g' cs lrs. case=> <- _ <- _ Hnew_lc Hnew_ls1 Hnew_ls2.
    done.
  - intros_tuple. dcase_hyps; intros; subst. rewrite !interp_cnf_cons.
    move/andP: H2 => [Hnew_gls1 Hnew_gls0]. move/andP: H3 => [Hnew_gls2 Hnew_gls3].
    move: (newer_than_lit_le_newer H1 (pos_leb_add_diag_r g 1)) => Hnew_g1lc.
    move: (newer_than_lits_le_newer Hnew_gls0 (pos_leb_add_diag_r g 1)) => Hnew_g1ls0.
    move: (newer_than_lits_le_newer Hnew_gls3 (pos_leb_add_diag_r g 1)) => Hnew_g1ls3.
    rewrite (H _ _ _ _ _ _ _ _ _ H10 Hnew_g1lc Hnew_g1ls0 Hnew_g1ls3) /=.
    rewrite !interp_lit_neg_lit. move: (mk_env_ite_preserve H10) => Hpre.
    move: (newer_than_lit_le_newer Hnew_gls1 (pos_leb_add_diag_r g 1)) => Hnew_g1ls1.
    move: (newer_than_lit_le_newer Hnew_gls2 (pos_leb_add_diag_r g 1)) => Hnew_g1ls2.
    move: (Hpre g (newer_than_var_add_diag_r g 1)). rewrite env_upd_eq.
    move: (env_preserve_lit Hpre Hnew_g1ls1).
    rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hnew_gls1)).
    move: (env_preserve_lit Hpre Hnew_g1ls2).
    rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hnew_gls2)).
    move: (env_preserve_lit Hpre Hnew_g1lc).
    rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq H1)).
    move=> -> -> -> ->.
    by case: (interp_lit E lc); case: (interp_lit E ls1); case: (interp_lit E ls2).
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
      let cs_hd := List.map (fun cs => neg_lit r::cs) (cnf_lit_eq ls1_hd ls2_hd) in
      let cs_tl := bit_blast_eq_eq r ls1_tl ls2_tl in
      cs_hd++cs_tl
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
      let cs_hd := [ [neg_lit auxs_hd; ls1_hd; ls2_hd];
                     [neg_lit auxs_hd; neg_lit ls1_hd; neg_lit ls2_hd];
                     [auxs_hd; neg_lit ls1_hd; ls2_hd];
                     [auxs_hd; ls1_hd; neg_lit ls2_hd] ] in
      let '(g_tl, cs_tl, auxs_tl) := bit_blast_eq_neq g_hd ls1_tl ls2_tl in
      (g_tl, cs_hd++cs_tl, cons_tuple auxs_hd auxs_tl)
  else
    fun _ _ =>
      (g, [], [tuple]).

Fixpoint mk_env_eq_neq w E g : w.-tuple literal -> w.-tuple literal -> env * generator * cnf * w.-tuple literal :=
  if w is _.+1 then
    fun ls1 ls2 =>
      let (g_hd, auxs_hd) := gen g in
      let (ls1_tl, ls1_hd) := eta_expand (splitlsb ls1) in
      let (ls2_tl, ls2_hd) := eta_expand (splitlsb ls2) in
      let E' := env_upd E (var_of_lit auxs_hd)
                        (xorb (interp_lit E ls1_hd) (interp_lit E ls2_hd)) in
      let cs_hd := [ [neg_lit auxs_hd; ls1_hd; ls2_hd];
                     [neg_lit auxs_hd; neg_lit ls1_hd; neg_lit ls2_hd];
                     [auxs_hd; neg_lit ls1_hd; ls2_hd];
                     [auxs_hd; ls1_hd; neg_lit ls2_hd] ] in
      let '(E_tl, g_tl, cs_tl, auxs_tl) := mk_env_eq_neq E' g_hd ls1_tl ls2_tl in
      (E_tl, g_tl, cs_hd++cs_tl, cons_tuple auxs_hd auxs_tl)
  else
    fun _ _ =>
      (E, g, [], [tuple]).

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



(* ===== bit_blast_ult ===== *)

(*Parameter bit_blast_ult : forall w : nat, generator -> w.-tuple literal -> w.-tuple literal -> generator * cnf * literal.*)

Definition bit_blast_ult w (g: generator) (ls1 ls2: w.-tuple literal): generator * cnf * literal :=
  let (g', r) := gen g in
  let (g'', wahr) := gen g' in
  let cs1 := [[wahr]] in
  let '(g_not, cs2, r_nls2) := bit_blast_not g ls2 in
  let '(g_fa, cs3, cout, r_fa) := bit_blast_full_adder g_not wahr ls1 r_nls2 in
  let cs4 := [[r; cout]; [neg_lit r; neg_lit cout]] in
  (g_fa, cs1++cs2++cs3++cs4, r).

Lemma adcB_ltB_leB :
  forall n (ibs1 ibs2: BITS n),
    if ~~(adcB true ibs1 (invB ibs2)).1 then ltB ibs1 ibs2 else leB ibs2 ibs1.
Proof.
  move => n ibs1 ibs2.
  replace (~~ (adcB true ibs1 (invB ibs2)).1) with
      (sbbB false ibs1 ibs2).1 by done.
  apply sbbB_ltB_leB.
Qed.

Lemma bit_blast_ult_correct :
  forall w g (bs1 bs2 : BITS w) E g' ls1 ls2 cs lr,
    bit_blast_ult g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    interp_lit E lr = (ltB bs1 bs2).
Proof.
  move => w ig ibs1 ibs2 E og ils1 ils2 cs olr.
  rewrite /bit_blast_ult.
  case Hnot : (bit_blast_not ig ils2) => [[g_not cs_not] r_not].
  case Hg1 : (gen ig) => [g' r].
  case Hg2 : (gen g') => [g'' wahr].
  case Hfadd : (bit_blast_full_adder g_not wahr ils1 r_not) =>
  [[[g_fadd cs_fadd] c_out] r_fadd].
  case => _ <- <-.
  rewrite add_prelude_cons add_prelude_append add_prelude_singleton.
  rewrite add_prelude_append add_prelude_cons.
  repeat rewrite add_prelude_singleton.
  (*repeat rewrite interp_clause_cons. orbF ;simpl. *)
  rewrite interp_clause_cons orbF.
  repeat rewrite interp_clause_cons; repeat rewrite orbF.
  repeat rewrite interp_lit_neg_lit.
  move => Henc_ls1 Henc_ls2 Hcnf.
  split_andb.
  move : (bit_blast_not_correct Hnot Henc_ls2 H0) => Henc_not.
  case Hwahr : (interp_lit E wahr);
  move/eqP : H6 => Hwahrt; [|rewrite Hwahr in Hwahrt; discriminate].
  -
    assert (enc_bit E wahr true) by (rewrite /enc_bit Hwahr; done).
    assert ((adcB true ibs1 (invB ibs2)) = (~~ ltB ibs1 ibs2, (snd (adcB true ibs1 (invB ibs2))))).
    move : (adcB_ltB_leB ibs1 ibs2).
    case Hadcb : (adcB true ibs1 (invB ibs2)).1. 
    + simpl.
      move => Hltb.
      apply injective_projections. simpl.
      rewrite Hadcb  -leBNlt Hltb; reflexivity.
      reflexivity.
    + simpl.
      move => Hltb.
      apply injective_projections; try reflexivity; simpl.
      rewrite Hadcb Hltb; reflexivity.
    move : (bit_blast_full_adder_correct Hfadd Henc_ls1 Henc_not H6 H1 H7) => Hfa.
    move/andP : Hfa. move => Henc. split_andb.
    rewrite /enc_bit in H9.
    move/eqP :H9 => H9.
    apply Bool.negb_sym in H9.
    rewrite H9.
    case Hr :( interp_lit E r).
    +  rewrite Hr /= in H4; symmetry; apply H4.
    + rewrite Hr /= in H5;  apply Bool.negb_sym; simpl; apply H5.
Qed.



(* ===== bit_blast_disj ===== *)

Definition bit_blast_disj g (l1 l2: literal) : generator * cnf * literal :=
  let (g', r) := gen g in
  let cs := [[neg_lit r; l1; l2]; [r; neg_lit l1]; [r; neg_lit l2]]
  in (g', cs, r).

Lemma bit_blast_disj_correct :
  forall g b1 b2 E g' l1 l2 cs lr,
    bit_blast_disj g l1 l2 = (g', cs, lr) ->
    enc_bit E l1 b1 ->
    enc_bit E l2 b2 ->
    interp_cnf E (add_prelude cs) ->
    interp_lit E lr = (orb b1 b2).
Proof.
  move => g ib1 ib2 E g' il1 il2 cs olr.
  rewrite /bit_blast_disj.
  case.
  set r := Pos g.
  move => Hg <- <-.
  rewrite add_prelude_cons !add_prelude_singleton /=. 
  rewrite !interp_lit_neg_lit.
  move => Henc1 Henc2 Hcnf.
  move/andP: Hcnf => [Htt Hcnf].
  move/andP: Htt => [Htt Hcnf1].
  move/andP : Hcnf => [_ Hcnf2].
  move/andP : Hcnf2 => [Hcnfil1 Hcnfil2].
  case Heg: (E g).
  - rewrite Heg in Hcnf1; simpl in Hcnf1.
    case Hl1 : (interp_lit E il1).
    + rewrite /enc_bit in Henc1; rewrite Hl1 in Henc1.
      move/eqP : Henc1 => Henc1; rewrite -Henc1; symmetry; apply orTb.
    + rewrite Hl1 in Hcnf1; rewrite orFb in Hcnf1.
      rewrite /enc_bit in Henc2; rewrite Hcnf1 in Henc2.
      move/eqP : Henc2 => Henc2; rewrite -Henc2; symmetry; apply orbT.
  - rewrite Heg in Hcnfil1, Hcnfil2; simpl in Hcnfil1, Hcnfil2.
    move/eqP : Hcnfil1 => Hl1; move/eqP : Hl1 => Hl1; symmetry in Hl1; apply Bool.negb_sym in Hl1.
    move/eqP : Hcnfil2 => Hl2; move/eqP : Hl2 => Hl2; symmetry in Hl2; apply Bool.negb_sym in Hl2.
    rewrite /enc_bit in Henc1, Henc2; rewrite Hl1 in Henc1; rewrite Hl2 in Henc2.
    move/eqP : Henc1 => Henc1; rewrite -Henc1; symmetry; rewrite orFb.
    move/eqP : Henc2 => Henc2; done.
Qed.



(* ===== bit_blast_ule ===== *)

(*Parameter bit_blast_ule : forall w : nat, generator -> w.-tuple literal -> w.-tuple literal -> generator * cnf * literal.
 *)
Definition bit_blast_ule (w: nat) g (ls1 ls2: w.-tuple literal) : generator * cnf * literal :=
  let '(g_eq, cs_eq, r_eq) := bit_blast_eq g ls1 ls2 in
  let '(g_ult, cs_ult, r_ult) := bit_blast_ult g ls1 ls2 in
  let '(g_disj, cs_disj, r_disj) := bit_blast_disj g_ult r_eq r_ult in
  (g_disj, cs_eq++cs_ult++cs_disj, r_disj).

Lemma bit_blast_ule_correct :
  forall w g (bs1 bs2 : BITS w) E g' ls1 ls2 cs lr,
    bit_blast_ule g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    interp_lit E lr = (leB bs1 bs2).
Proof.
  move => w g ibs1 ibs2 E g' ils1 ils2 cs olr.
  rewrite /bit_blast_ule.
  case Heq : (bit_blast_eq g ils1 ils2) => [[g_eq cs_eq] r_eq].
  case Hult : (bit_blast_ult g ils1 ils2) => [[g_ult cs_ult] r_ult].
  case Hdisj : (bit_blast_disj g_ult r_eq r_ult) => [[g_disj cs_disj] r_disj].
  case => _ <- <- Henc1 Henc2.
  rewrite 2!add_prelude_append.
  move => Hcnf.
  move/andP : Hcnf => [Hcnf_eq Hcnf].
  move/andP : Hcnf => [Hcnf_ult Hcnf_disj].
  move : (bit_blast_eq_correct Heq Henc1 Henc2 Hcnf_eq) => Hreq.
  move : (bit_blast_ult_correct Hult Henc1 Henc2 Hcnf_ult) => Hrult.
  move/eqP : Hreq => Hreq.
  assert (enc_bit E r_eq (ibs1 == ibs2)) by (rewrite /enc_bit; by apply/eqP).
  assert (enc_bit E r_ult (ltB ibs1 ibs2)) by (rewrite /enc_bit Hrult; done).
  move : (bit_blast_disj_correct Hdisj H H0 Hcnf_disj) => Hrdisj.
  rewrite Hrdisj.
  rewrite /leB. apply Bool.orb_comm.
Qed.



(* ===== bit_blast_ugt ===== *)

(*Parameter bit_blast_ugt : forall w : nat, generator -> w.-tuple literal -> w.-tuple literal -> generator * cnf * literal.
 *)
Definition bit_blast_ugt w (g: generator) (ls1 ls2: w.-tuple literal) :generator * cnf * literal :=
  bit_blast_ult g ls2 ls1.

Lemma bit_blast_ugt_correct :
  forall w g (bs1 bs2 : BITS w) E g' ls1 ls2 cs lr,
    bit_blast_ugt g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    interp_lit E lr = (ltB bs2 bs1).
Proof.
  move => w g ibs1 ibs2 E g' ils1 ils2 cs olr.
  rewrite /bit_blast_ugt.
  move => Hult Henc1 Henc2 Hcnf.
  move : (bit_blast_ult_correct Hult Henc2 Henc1 Hcnf) => Hrult.
  symmetry; done.
Qed.



(* ===== bit_blast_uge ===== *)

(*Parameter bit_blast_uge : forall w : nat, generator -> w.-tuple literal -> w.-tuple literal -> generator * cnf * literal.
 *)
Definition bit_blast_uge w (g: generator) (ls1 ls2: w.-tuple literal) :generator * cnf * literal :=
  bit_blast_ule g ls2 ls1.

Lemma bit_blast_uge_correct :
  forall w g (bs1 bs2 : BITS w) E g' ls1 ls2 cs lr,
    bit_blast_uge g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    interp_lit E lr = (leB bs2 bs1).
Proof.
  move => w g ibs1 ibs2 E g' ils1 ils2 cs olr.
  rewrite /bit_blast_uge.
  move => Hule Henc1 Henc2 Hcnf.
  move : (bit_blast_ule_correct Hule Henc2 Henc1 Hcnf) => Hrule.
  done.
Qed.



(* ===== bit_blast_slt ===== *)

(*Parameter bit_blast_slt : forall w : nat, generator -> w.+1.-tuple literal -> w.+1.-tuple literal -> generator * cnf * literal.
 *)
Definition bit_blast_slt w g (ls1 ls2 : w.+1.-tuple literal) : generator * cnf * literal :=
  let (g', r) := gen g in
  let (g'', wahr) := gen g' in
  let cs1 := [[wahr]] in
  let (sign1, uls1) := eta_expand (splitmsb ls1) in
  let (sign2, uls2) := eta_expand (splitmsb ls2) in
  let '(g_not, cs_not, r_not) := bit_blast_not g ls2 in
  let '(g_fadd, cs_fadd, cout, r_fadd) := bit_blast_full_adder g_not wahr ls1 r_not in
  let cs4 := [[neg_lit r; cout; neg_lit sign1; sign2];
                [neg_lit r; cout; sign1; neg_lit sign2];
                [neg_lit r; neg_lit cout; sign1; sign2];
                [neg_lit r; neg_lit cout; neg_lit sign1; neg_lit sign2];
                [r; cout; sign1; sign2];
                [r; cout; neg_lit sign1; neg_lit sign2];
                [r; neg_lit cout; neg_lit sign1; sign2];
                [r; neg_lit cout; sign1; neg_lit sign2]] in
  (g_fadd, cs1++cs_not++cs_fadd++cs4, r).
(*<<<<<<< HEAD
*)  
Lemma toNegZCons n b  (p:BITS n) : toNegZ (consB b p) = if b then Zdouble (toNegZ p) else Zsucc (Zdouble (toNegZ p)).
Proof. done. Qed.

Lemma toPosZCons n b  (p:BITS n) : toPosZ (consB b p) = if b then Zsucc (Zdouble (toPosZ p)) else Zdouble (toPosZ p).
Proof. done. Qed.

Lemma splitmsb_ones :
  forall n, splitmsb (ones n.+1) = (true, ones n).
Proof.
  move => n.
  apply injective_projections.
  rewrite  splitmsb_msb msb_ones /=; reflexivity.
  simpl.
  induction n.
  rewrite /ones /copy /= nseqCons beheadCons; reflexivity.
  rewrite /ones /copy nseqCons tupleE/= beheadCons.
  replace (splitmsb (nseq_tuple n.+1 true)) with (eta_expand (splitmsb (nseq_tuple n.+1 true))).
  rewrite IHn /= theadE /= /joinlsb /=.
  rewrite /ones /copy /= nseqCons tupleE; reflexivity.
    by (symmetry; apply injective_projections).
Qed.

Lemma joinmsb_ones :
  forall n, joinmsb (true, ones n) =  ones n.+1. 
Proof.
  move => n.
  induction n.
  simpl. replace (joinlsb (nilB, true)) with (singleBit true) by done.
  rewrite /ones /copy nseqCons tuple0 tupleE; done.
  rewrite /ones /copy /= nseqCons beheadCons theadE.
  rewrite IHn.
  rewrite /joinlsb /= nseqCons tupleE; done.
Qed.
  
Lemma dropmsb_ones :
  forall n , dropmsb (ones n.+1) = (ones n).
Proof.
  move => n.
  rewrite /dropmsb.
  rewrite splitmsb_ones /=; done.
Qed.  
  
Lemma toZ_zero: forall n, toZ (zero n.+1) = 0%Z.
Proof.
  move => n.
  induction n.
  - rewrite /toZ /= /toPosZ /=; done.
  - rewrite -fromNat0 in IHn. rewrite -fromNat0.
    rewrite /toZ splitmsb_fromNat /= div.div0n /=.
    rewrite /toZ splitmsb_fromNat /= div.div0n /= in IHn.
    replace (# (0)) with (consB false (@fromNat n 0)) by done.
    rewrite toPosZCons. rewrite IHn /=.
    done.
Qed.

Lemma toZ_ones : forall n, toZ (ones n.+1) = (-1)%Z.
Proof.
  move => n.
  induction n.
  - rewrite /toZ.
    replace (splitmsb (ones 1)) with (true, (splitmsb (ones 1)).2) by
        (apply injective_projections; [rewrite splitmsb_msb; reflexivity|simpl; reflexivity]).
    simpl; reflexivity.
  - rewrite /toZ.
    rewrite splitmsb_ones.
    rewrite Z.opp_succ -Z.sub_1_r.
    symmetry; apply Zplus_minus_eq; simpl.
    rewrite /ones /copy nseqCons toNegZCons.
    rewrite /toZ splitmsb_ones Z.opp_succ -Z.sub_1_r in IHn.
    rewrite -Z.add_opp_r -Z.opp_add_distr in IHn.
    apply Z.opp_inj_wd in IHn. rewrite Z.opp_involutive /= in IHn.
    apply Z.add_move_r in IHn; simpl in IHn.
    rewrite IHn.
    done.
Qed.

Lemma toPosZ_fromPosZ n m : @toPosZ n (fromPosZ m) = Zmod m (Z.of_nat (2^(n))).
Proof.
Admitted.
    
Lemma fromZK n : cancel (fromPosZ) (@toPosZ n).
Proof.
Admitted.

Lemma toPosZ_inj n : injective (@toPosZ n).
Proof.
Admitted.

Lemma toZ_joinmsb0 n: forall (p: BITS n),
    toZ (joinmsb (false, p)) = toPosZ p.
Proof.
  move => p.
  rewrite /toZ joinmsbK; reflexivity.
Qed.

Lemma toPosZ_joinmsb0 n: forall (p: BITS n),
    toPosZ (joinmsb (false, p)) = toPosZ p.
Proof.
  induction n.
  - move => p.
    rewrite (tuple0 p)/= /joinmsb /joinlsb /toPosZ/=; reflexivity.
  - case/tupleP => [p_hd p_tl].
    move : (IHn p_tl).
    case Hpd : p_hd.
    + replace (toPosZ [tuple of false :: p_tl]) with (toPosZ (consB false p_tl)) by done.
      rewrite /= !theadE !beheadCons/= /joinlsb/= !toPosZCons /=.
      move => IHm.
      rewrite IHm !Z.double_spec; reflexivity.
    + replace (toPosZ [tuple of false :: p_tl]) with (toPosZ (consB false p_tl)) by done.
      rewrite /= !theadE !beheadCons/= /joinlsb/= !toPosZCons /=.
      move => IHm.
      rewrite IHm; reflexivity.
Qed.

Lemma toZ_joinmsb1 n : forall (p: BITS n),
    toZ (joinmsb (true, p)) = (Zopp (Zsucc (toNegZ p)))%Z.
Proof.
  move => p.
  rewrite /toZ joinmsbK; reflexivity.
Qed.

Lemma toPosZ_joinmsb1 n : forall (p: BITS n),
    toPosZ (joinmsb (true, p)) = ((toPosZ p) + 2^(Z.of_nat n))%Z.
Proof.
  induction n.
  - move => p.
    rewrite (tuple0 p)/= /joinmsb /joinlsb /toPosZ/=; reflexivity.
  - case/tupleP => [p_hd p_tl].
    move : (IHn p_tl).
    case Hpd : p_hd.
    + replace (toPosZ [tuple of true :: p_tl]) with (toPosZ (consB true p_tl)) by done.
      rewrite /= !theadE !beheadCons/= /joinlsb/= !toPosZCons /=.
      move => IHm.
      rewrite IHm Z.pow_pos_fold Zpos_P_of_succ_nat !Z.double_spec Z.mul_add_distr_l.
      rewrite Z.pow_succ_r; try omega.
    + replace (toPosZ [tuple of false :: p_tl]) with (toPosZ (consB false p_tl)) by done.
      rewrite /= !theadE !beheadCons/= /joinlsb/= !toPosZCons /=.
      move => IHm.
      rewrite IHm Z.pow_pos_fold Zpos_P_of_succ_nat !Z.double_spec Z.mul_add_distr_l.
      rewrite Z.pow_succ_r; try omega.
Qed.

Lemma toNat_joinmsb1 n (p: BITS n) : toNat (joinmsb (true, p)) = toNat p + 2^n.
Proof. rewrite toNat_joinmsb /=. ring. Qed.

Lemma ltB_joinmsb1 n: forall (p q : BITS n),
    ltB (joinmsb (true,p)) (joinmsb (true, q)) = ltB p q.
Proof.
  move => p q.
  rewrite ltB_nat. rewrite !toNat_joinmsb1.
  replace (toNat p + 2 ^ n < toNat q + 2 ^ n) with (toNat p < toNat q).
  symmetry; apply ltB_nat.
  rewrite ltn_add2r.
  done.
Qed.

Lemma toPosZ_toNat n : forall (p: BITS n),
    toPosZ p = Z.of_nat (toNat p).
Proof.
  induction n.
  - move => p. rewrite (tuple0 p) /= /toPosZ /=; reflexivity.
  - case/tupleP => [p_hd p_tl].
    case p_hd.
    + replace [tuple of true :: p_tl] with (consB true p_tl) by done.
      rewrite toPosZCons toNatCons /=.
      rewrite Zpos_P_of_succ_nat.
      rewrite (IHn p_tl).
      apply Z.succ_inj_wd. rewrite Z.double_spec.
      rewrite -muln2 Nat2Z.inj_mul.
      ring.
    + replace [tuple of false :: p_tl] with (consB false p_tl) by done.
      rewrite toPosZCons toNatCons /=.
      rewrite (IHn p_tl).
      rewrite Z.double_spec.
      rewrite -muln2 Nat2Z.inj_add Nat2Z.inj_0 Nat2Z.inj_mul.
      ring.
Qed.

Lemma toNegZ_toNat n : forall (p: BITS n),
    toNegZ p = Z.of_nat ((2^n-1) - (toNat p)).
Proof.
  induction n.
  - move => p. rewrite (tuple0 p) /toNegZ /=; reflexivity.
  - case/tupleP => [p_hd p_tl].
    case p_hd.
    + replace [tuple of true :: p_tl] with (consB true p_tl) by done.
      rewrite toNegZCons toNatCons /= (IHn p_tl).
      rewrite Z.double_spec expnS.
      rewrite Nat2Z.inj_sub;
        [| move : (toNatBounded p_tl) => Hnb; apply lt_n_Sm_le; rewrite -addn1 subnK; move/ltP :Hnb => Hnb; [done|apply Nats.expn2_gt0]].
      rewrite Z.mul_sub_distr_l.
      replace (Z.of_nat (2 * 2 ^ n - 1 - (1 + (toNat p_tl).*2))) with
          (Z.of_nat (2 * 2 ^ n - 1) - Z.of_nat (1 + (toNat p_tl).*2))%Z by
          (rewrite -Nat2Z.inj_sub;
           [done|
            rewrite -muln2; apply/leP /Nats.ltn_leq_sub; apply/ltP; rewrite mulnC;
            apply Nat.mul_2_mono_l; apply/ltP /toNatBounded]).
      rewrite !Nat2Z.inj_add Z.sub_add_distr -muln2 !Nat2Z.inj_mul !Nat2Z.inj_sub .
      rewrite Nat2Z.inj_mul.
      assert (Z.of_nat 2 = 2%Z) as H2 by done; assert (Z.of_nat 1= 1%Z) as H1 by done.
      rewrite !H1 !H2 Z.mul_sub_distr_l Z.mul_1_r. ring.
      rewrite -expnS; apply/leP /Nats.expn2_gt0.
      apply/leP /Nats.expn2_gt0.
    + replace [tuple of false :: p_tl] with (consB false p_tl) by done.
      rewrite toNegZCons toNatCons /= (IHn p_tl) /= Z.double_spec add0n.
      rewrite !Nat2Z.inj_sub. rewrite -muln2 expnS !Nat2Z.inj_mul.
      assert (Z.of_nat 2 = 2%Z) as H2 by done;
      assert (Z.of_nat 1= 1%Z) as H1 by done.
      rewrite !H1 !H2 !Z.mul_sub_distr_l Z.mul_1_r -Z.add_1_r. ring.
      apply/leP /Nats.expn2_gt0.
      rewrite expnS -muln2 mulnC. apply/leP /Nats.ltn_leq_sub.
      apply/ltP /mult_lt_compat_l.
      apply/ltP /toNatBounded. omega. apply/leP /Nats.expn2_gt0.
      apply lt_n_Sm_le. rewrite -addn1 subnK. apply/ltP /toNatBounded. apply Nats.expn2_gt0.
Qed.
      
Lemma toPosZ_lt n : forall (p1 p2: BITS n),
    ltB p1 p2 -> ((toPosZ p1)< (toPosZ p2))%Z.
Proof.
  move => p1 p2.
  rewrite !toPosZ_toNat. rewrite ltB_nat.
  move => Hltb.
  apply inj_lt.
  apply/ltP.
  done.
Qed.
        
Lemma ltB_toZ_Pos :
  forall n (p1 p2 :BITS n.+1),
    ~~((splitmsb p1).1 || (splitmsb p2).1) -> ltB p1 p2 = Z.ltb (toZ p1) (toZ p2)%Z.
Proof.
  move => n.
  move => p1 p2 Hmsb.
  replace p1 with (joinmsb (splitmsb p1)) by apply splitmsbK.
  replace p2 with (joinmsb (splitmsb p2)) by apply splitmsbK.
  case Hmsb1 : ((splitmsb p1).1); rewrite Hmsb1 in Hmsb; try discriminate.
  rewrite orFb in Hmsb.
  move/eqP/eqP: Hmsb=> Hmsb2.
  apply Bool.negb_true_iff in Hmsb2.
  case Hspl1: (splitmsb p1) => [b1 ps1];
  case Hspl2: (splitmsb p2) => [b2 ps2].
  rewrite Hspl1 /= in Hmsb1; rewrite Hspl2 /= in Hmsb2.
  rewrite Hmsb1 Hmsb2.
  rewrite /toZ !joinmsbK ltB_joinmsb0 !toPosZ_toNat ltB_nat.
  case Hlt : (toNat ps1 < toNat ps2).
  - move/ltP : Hlt => Hlt.
    apply inj_lt in Hlt.
    rewrite /Z.ltb Hlt; reflexivity.
  - move/ltP in Hlt. apply not_lt in Hlt.
    apply inj_ge in Hlt.
    rewrite /Z.ge in Hlt. rewrite /Z.ltb. 
    case Hge : ((Z.of_nat (toNat ps1) ?= Z.of_nat (toNat ps2))%Z); try reflexivity.
    rewrite Hge in Hlt. destruct Hlt; reflexivity.
Qed.

Lemma ltB_toZ_Neg n :
  forall (p1 p2 : BITS n.+1),
    ((splitmsb p1).1 && (splitmsb p2).1) -> ltB p1 p2 = (Z.ltb (toZ p1) (toZ p2)%Z).
Proof.
  move => p1 p2 Hmsb.
  replace p1 with (joinmsb (splitmsb p1)) by apply splitmsbK.
  replace p2 with (joinmsb (splitmsb p2)) by apply splitmsbK.
  case Hmsb1 : ((splitmsb p1).1); rewrite Hmsb1 in Hmsb; try discriminate.
  rewrite andTb in Hmsb. move/eqP/eqP: Hmsb => Hmsb2.
  case Hspl1: (splitmsb p1) => [b1 ps1];
  case Hspl2: (splitmsb p2) => [b2 ps2].
  rewrite Hspl1 /= in Hmsb1; rewrite Hspl2 /= in Hmsb2.
  rewrite Hmsb1 Hmsb2.
  rewrite /toZ !joinmsbK ltB_joinmsb1 !toNegZ_toNat ltB_nat.
  (*rewrite ltnNge.*)
  case Hlt : ((toNat ps1 < toNat ps2)).
  - (*apply Bool.negb_true_iff in Hlt.*)
    move/ltP : Hlt => Hlt. 
    apply inj_lt in Hlt.
    symmetry.
    rewrite !Nat2Z.inj_sub; try (apply/ltP /Nats.expn2_gt0).
    apply Z.opp_lt_mono  in Hlt.
    apply Zplus_lt_compat_l with (p:=(Z.of_nat (2 ^ n) - Z.of_nat 1)%Z) in Hlt.
    apply Zsucc_lt_compat in Hlt.
    apply Z.opp_lt_mono in Hlt.
    apply Z.ltb_lt in Hlt. rewrite Hlt. reflexivity.
    apply/leP; rewrite -ltnS; replace ((2 ^ n - 1).+1) with ((2 ^ n - 1)+1) by (rewrite addn1; reflexivity);
    rewrite subnK.
    apply toNatBounded.
    apply Nats.expn2_gt0.
    apply/leP; rewrite -ltnS; replace ((2 ^ n - 1).+1) with ((2 ^ n - 1)+1) by (rewrite addn1; reflexivity);
    rewrite subnK.
    apply toNatBounded.
    apply Nats.expn2_gt0.
  - 
    rewrite ltnNge in Hlt.
    apply Bool.negb_false_iff in Hlt.
    move/leP : Hlt => Hlt. 
    apply inj_le in Hlt.
    symmetry.
    rewrite !Nat2Z.inj_sub;
      try (apply/ltP /Nats.expn2_gt0).
    apply Z.opp_le_mono in Hlt.
    apply Zplus_le_compat_l with (p:=(Z.of_nat (2 ^ n) - Z.of_nat 1)%Z) in Hlt.
    apply Zsucc_le_compat in Hlt.
    apply Z.opp_le_mono in Hlt.
    rewrite -Z.gtb_ltb.
    rewrite /Z.gtb. apply Z.leb_le in Hlt. rewrite /Z.leb in Hlt.
    case Hcomp: ((- Z.succ (Z.of_nat (2 ^ n) - Z.of_nat 1 + - Z.of_nat (toNat ps2))
                           ?= - Z.succ (Z.of_nat (2 ^ n) - Z.of_nat 1 + - Z.of_nat (toNat ps1)))%Z);
    try done.
    rewrite Hcomp in Hlt; discriminate.
    apply/leP; rewrite -ltnS; replace ((2 ^ n - 1).+1) with ((2 ^ n - 1)+1) by (rewrite addn1; reflexivity);
    rewrite subnK.
    apply toNatBounded.
    apply Nats.expn2_gt0.
    apply/leP; rewrite -ltnS; replace ((2 ^ n - 1).+1) with ((2 ^ n - 1)+1) by (rewrite addn1; reflexivity);
    rewrite subnK.
    apply toNatBounded.
    apply Nats.expn2_gt0.
Qed.

Lemma ltB_toZ n :
  forall (p1 p2 : BITS n.+1),
    ((splitmsb p1).1 = (splitmsb p2).1) -> ltB p1 p2 = (Z.ltb (toZ p1) (toZ p2)%Z).
Proof.
  move => p1 p2.
  case Hp1 : ((splitmsb p1).1); case Hp2: ((splitmsb p2).1);
    try discriminate.
  - move => _; apply ltB_toZ_Neg; rewrite Hp1 Hp2; done.
  - move => _; apply ltB_toZ_Pos; rewrite Hp1 Hp2; done.
Qed.
  
Lemma bit_blast_slt_correct :
  forall w g (bs1 bs2 : BITS (w.+1)) E g' ls1 ls2 cs lr,
    bit_blast_slt g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    interp_lit E lr <-> (toZ bs1 < toZ bs2)%Z.
Proof.
  move => w ig ibs1 ibs2 E g' ils1 ils2 cs olr.
  rewrite /bit_blast_slt.
  case Hnot : (bit_blast_not ig ils2) => [[g_not cs_not] r_not].
  case Hg1 : (gen ig) => [ig' r].
  case Hg2 : (gen ig') => [ig'' wahr].
  case Hfadd : (bit_blast_full_adder g_not wahr ils1 r_not) =>
  [[[g_fadd cs_fadd] c_out] r_fadd].
  case => _ <- <-.
  move => Henc1 Henc2.
  rewrite 2!interp_cnf_cons 2!interp_cnf_append.
  rewrite !interp_cnf_cons /=.
  rewrite !interp_lit_neg_lit /=.
  move => Hcnf.
  move/andP : Hcnf => [Htt Hcnf].
  move/andP : Hcnf => [Hwahr Hcnf].
  move/andP : Hcnf => [Hcnf_not Hcnf].
  move/andP : Hcnf => [Hcnf_fadd Hcnf].
  move/andP : Hcnf => [Hcnf1 Hcnf]; move/andP : Hcnf => [Hcnf2 Hcnf]; move/andP : Hcnf => [Hcnf3 Hcnf]; move/andP : Hcnf => [Hcnf4 Hcnf]; move/andP : Hcnf => [Hcnf5 Hcnf]; move/andP : Hcnf => [Hcnf6 Hcnf]; move/andP : Hcnf => [Hcnf7 Hcnf]; move/andP : Hcnf => [Hcnf8 _].
  assert (interp_lit E lit_tt) as Hintt by done.
  assert (interp_lit E lit_tt && interp_cnf E cs_not) as Hcnf_addnot by (rewrite Hintt Hcnf_not; done).
  rewrite -add_prelude_expand in Hcnf_addnot.
  move : (bit_blast_not_correct Hnot Henc2 Hcnf_addnot) => Hrnot.
  case Hcin : (interp_lit E wahr); [| rewrite Hcin in Hwahr; discriminate].
  assert (adcB true ibs1 (invB ibs2) = eta_expand (adcB true ibs1 (invB ibs2))) as Hadcb
    by apply surjective_pairing.
  assert (enc_bit E wahr true) as Henc_cin by (rewrite /enc_bit Hcin; done).
  assert (interp_lit E lit_tt && interp_cnf E cs_fadd) as Hcnf_addadd by (rewrite Hintt Hcnf_fadd; done).
  rewrite -add_prelude_expand in Hcnf_addadd.
  move : (bit_blast_full_adder_correct Hfadd Henc1 Hrnot Henc_cin Hcnf_addadd Hadcb) => Henc_add.
  move/andP : Henc_add => Henc_add.
  move/andP : Henc_add => [Henc_radd Henc_cout].
  case Hr : (interp_lit E r).
  assert ((sbbB false ibs1 ibs2).1 = ~~(adcB true ibs1 (invB ibs2)).1) as Hsbbb1 by done.
  - split; try done.
    move => _.
    rewrite Hr /= in Hcnf1 Hcnf2 Hcnf3 Hcnf4 Hcnf5 Hcnf6 Hcnf7 Hcnf8.
    rewrite /enc_bit in Henc_cout. move/eqP :Henc_cout=> Henc_cout.
    rewrite enc_bits_splitmsb in Henc1; rewrite enc_bits_splitmsb in Henc2.
    move/andP: Henc1 => [Henc1msb Henc1]; move/andP: Henc2 => [Henc2msb Henc2].
    rewrite /enc_bit in Henc1msb Henc2msb; move/eqP : Henc1msb => Henc1msb; move/eqP : Henc2msb => Henc2msb.
    rewrite Henc1msb Henc2msb in Hcnf1 Hcnf2 Hcnf3 Hcnf4.
    case Hs1 :((splitmsb ibs1).1); case Hs2 :((splitmsb ibs2).1).
    + rewrite Hs1 Hs2 /= in Hcnf1 Hcnf2 Hcnf3 Hcnf4. 
      rewrite -Z.ltb_lt. rewrite -ltB_toZ_Neg.

      move : (sbbB_ltB_leB ibs1 ibs2).
      case Hcsub : (carry_subB ibs1 ibs2).
      done.
      rewrite Hcsub in Hsbbb1.
      symmetry in Hsbbb1. apply Bool.negb_false_iff in Hsbbb1.
      rewrite Hsbbb1 in Henc_cout. rewrite Henc_cout in Hcnf4.
      discriminate.
      rewrite Hs1 Hs2. done.
    +
      rewrite Hs1 Hs2 /=in Hcnf1 Hcnf2 Hcnf3 Hcnf4.
      (*rewrite -Z.ltb_lt. rewrite -ltB_toZ_Neg.*)
      move : (sbbB_ltB_leB ibs1 ibs2).
      case Hcsub : (carry_subB ibs1 ibs2).
      rewrite Hcsub in Hsbbb1.
      symmetry in Hsbbb1. apply Bool.negb_true_iff in Hsbbb1.
      rewrite Hsbbb1 in Henc_cout.
      rewrite Henc_cout in Hcnf1. discriminate.
      rewrite Hcsub in Hsbbb1.
      symmetry in Hsbbb1. apply Bool.negb_false_iff in Hsbbb1.
      rewrite Hsbbb1 in Henc_cout.
      admit.
    +
      rewrite Hs1 Hs2 /=in Hcnf1 Hcnf2 Hcnf3 Hcnf4.
      move : (sbbB_ltB_leB ibs1 ibs2).
      case Hcsub : (carry_subB ibs1 ibs2).
      rewrite Hcsub in Hsbbb1.
      symmetry in Hsbbb1. apply Bool.negb_true_iff in Hsbbb1.
      rewrite Hsbbb1 in Henc_cout. rewrite Henc_cout in Hcnf2.
      discriminate.
      admit.
    +
      rewrite Hs1 Hs2 /=in Hcnf1 Hcnf2 Hcnf3 Hcnf4.
      move : (sbbB_ltB_leB ibs1 ibs2).
      rewrite -Z.ltb_lt. rewrite -ltB_toZ_Pos.
      case Hcsub : (carry_subB ibs1 ibs2).
      done.
      rewrite Hcsub in Hsbbb1.
      symmetry in Hsbbb1. apply Bool.negb_false_iff in Hsbbb1.
      rewrite Hsbbb1 in Henc_cout. rewrite Henc_cout in Hcnf3.
      discriminate.
      rewrite Hs1 Hs2. 
      done.
  -
    assert ((sbbB false ibs1 ibs2).1 = ~~(adcB true ibs1 (invB ibs2)).1) as Hsbbb1 by done.
      split.
      + discriminate.
      +
        rewrite -Z.ltb_lt .
        rewrite -ltB_toZ_Neg.
        move => Hzlt.
        rewrite Hr /= in Hcnf1 Hcnf2 Hcnf3 Hcnf4.
        rewrite Hr /= in Hcnf5 Hcnf6 Hcnf7 Hcnf8.
        rewrite /enc_bit in Henc_cout. move/eqP :Henc_cout=> Henc_cout.
        rewrite enc_bits_splitmsb in Henc1; rewrite enc_bits_splitmsb in Henc2.
        move/andP: Henc1 => [Henc1msb Henc1]; move/andP: Henc2 => [Henc2msb Henc2].
        rewrite /enc_bit in Henc1msb Henc2msb; move/eqP : Henc1msb => Henc1msb; move/eqP : Henc2msb => Henc2msb.
        move : (sbbB_ltB_leB ibs1 ibs2).
        rewrite Henc1msb Henc2msb in Hcnf5 Hcnf6 Hcnf7 Hcnf8.
        case Hs1 :((splitmsb ibs1).1); case Hs2 :((splitmsb ibs2).1).
        rewrite Hs1 Hs2 /= in Hcnf5 Hcnf6 Hcnf7 Hcnf8.
        case Hcsub : (carry_subB ibs1 ibs2).
      * 
        rewrite Hcsub in Hsbbb1.
        symmetry in Hsbbb1. apply Bool.negb_true_iff in Hsbbb1.
        rewrite Hsbbb1 in Henc_cout. rewrite Henc_cout in Hcnf6.
        discriminate.
      *
        rewrite  Hcsub in Hsbbb1.
        symmetry in Hsbbb1. apply Bool.negb_false_iff in Hsbbb1.
        rewrite Hsbbb1 in Henc_cout.
        admit.

        case Hcsub : (carry_subB ibs1 ibs2).
        
        
      case Hs2:((splitmsb ibs2).1).
      rewrite Hs2 /= in Hcnf1 Hcnf4.
      rewrite orbF in Hcnf4.
      rewrite Henc_cout /= in Hcnf4.
      move/eqP/eqP: Hcnf4 => Hcnf4.
      apply Bool.negb_true_iff in Hcnf4.
      rewrite Hcnf4 in Hsbbb1.
      move : (sbbB_ltB_leB ibs1 ibs2).
      Local Opaque ltB leB.
      rewrite Hsbbb1 /=.
      move => Hltb.
      Eval compute in (@toNegZ 4 (#2)).
      rewrite -ltB_joinmsb0 in Hltb.
      
      
(*
      rewrite /toZ.
      replace (splitmsb ibs1) with ((splitmsb ibs1).1, (splitmsb ibs1).2) by (symmetry; apply surjective_pairing).
      replace (splitmsb ibs2) with ((splitmsb ibs2).1, (splitmsb ibs2).2) by (symmetry; apply surjective_pairing).
      rewrite Hs1 Hs2 /=. rewrite 2!Z.opp_succ. apply -> Z.pred_lt_mono.
      apply -> Z.opp_lt_mono.



=======
  assert (interp_lit E lit_tt) by done.
  assert (interp_lit E lit_tt && interp_cnf E cs_not) by (rewrite H Hcnf_not; done).
  rewrite -add_prelude_expand in H0.
  move : (bit_blast_not_correct Hnot Henc2 H0) => Hrnot.
  case Hcin : (interp_lit E wahr); [| rewrite Hcin in Hwahr; discriminate].
  assert (adcB true ibs1 (invB ibs2) = eta_expand (adcB true ibs1 (invB ibs2)))
    by apply surjective_pairing.
  assert (enc_bit E wahr true) by (rewrite /enc_bit Hcin; done).
  assert (interp_lit E lit_tt && interp_cnf E cs_fadd) by (rewrite H Hcnf_fadd; done).
  rewrite -add_prelude_expand in H3.
  move : (bit_blast_full_adder_correct Hfadd Henc1 Hrnot H2 H3 H1) => Henc_add.
  move/andP : Henc_add => Henc_add.
  move/andP : Henc_add => [Henc_radd Henc_cout].
  case Hr : (interp_lit E r).
  split.
>>>>>>> d965e1310a210a3c8afe5a2a70b5ee3cab8d08ae
*)
Admitted.



(* ===== bit_blast_sle ===== *)

Parameter bit_blast_sle : forall w : nat, generator -> w.+1.-tuple literal -> w.+1.-tuple literal -> generator * cnf * literal.

Lemma bit_blast_sle_correct :
  forall w g (bs1 bs2 : BITS w.+1) E g' ls1 ls2 cs lr,
    bit_blast_sle g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    interp_lit E lr <-> (toZ bs1 <= toZ bs2)%Z.
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
    interp_lit E lr <-> (toZ bs1 > toZ bs1)%Z.
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
    interp_lit E lr <-> (toZ bs1 >= toZ bs1)%Z.
Proof.
Admitted.



(* ===== bit_blast_conj ===== *)

Definition bit_blast_conj g (a1 a2 : literal) : generator * cnf * literal :=
  let (g', r) := gen g in
  let cs := [[neg_lit r; a1]; [neg_lit r; a2]; [r; neg_lit a1; neg_lit a2]] in
  (g', cs, r).

Definition mk_env_conj E g (a1 a2 : literal) : env * generator * cnf * literal :=
  let (g', r) := gen g in
  let E' := env_upd E (var_of_lit r) (interp_lit E a1 && interp_lit E a2) in
  let cs := [[neg_lit r; a1]; [neg_lit r; a2]; [r; neg_lit a1; neg_lit a2]] in
  (E', g', cs, r).

Lemma bit_blast_conj_correct :
  forall g (b1 b2 : bool) E g' (l1 l2 : literal) cs lr,
    bit_blast_conj g l1 l2 = (g', cs, lr) ->
    enc_bit E l1 b1 -> enc_bit E l2 b2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (b1 && b2).
Proof.
  move=> g b1 b2 E g' l1 l2 cs lr. rewrite /bit_blast_conj.
  case=> _ <- <- Henc1 Henc2. rewrite /enc_bit /=. rewrite !interp_lit_neg_lit.
  rewrite (eqP Henc1) (eqP Henc2) => {Henc1 Henc2}. move/andP => [_ H].
  move: H. by case: (E g); case: b1; case: b2.
Qed.

Lemma mk_env_conj_is_bit_blast_conj :
  forall E g (l1 l2 : literal) E' g' cs lr,
    mk_env_conj E g l1 l2 = (E', g', cs, lr) ->
    bit_blast_conj g l1 l2 = (g', cs, lr).
Proof.
  rewrite /mk_env_conj /bit_blast_conj /=; intros; dcase_hyps; subst; reflexivity.
Qed.

Lemma mk_env_conj_newer_gen :
  forall E g (l1 l2 : literal) E' g' cs lr,
    mk_env_conj E g l1 l2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  move=> E g l1 l2 E' g' cs lr. case=> _ <- _ _. exact: pos_leb_add_diag_r.
Qed.

Lemma mk_env_conj_newer_res :
  forall E g (l1 l2 : literal) E' g' cs lr,
    mk_env_conj E g l1 l2 = (E', g', cs, lr) ->
    newer_than_lit g' lr.
Proof.
  move=> E g l1 l2 E' g' cs lr. case=> _ <- _ <-.
  exact: newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_conj_newer_cnf :
  forall E g (l1 l2 : literal) E' g' cs lr,
    mk_env_conj E g l1 l2 = (E', g', cs, lr) ->
    newer_than_lit g l1 -> newer_than_lit g l2 ->
    newer_than_cnf g' cs.
Proof.
  move=> E g l1 l2 E' g' cs lr. case=> _ <- <- _ Hnew_l1 Hnew_l2 /=.
  move: (newer_than_lit_add_r 1 Hnew_l1) => {Hnew_l1} Hnew_l1.
  move: (newer_than_lit_add_r 1 Hnew_l2) => {Hnew_l2} Hnew_l2.
  rewrite 2!newer_than_lit_neg Hnew_l1 Hnew_l2.
  replace (g + 1)%positive with (var_of_lit (Neg g) + 1)%positive at 1 2
    by reflexivity.
  rewrite newer_than_lit_add_diag_r.
  replace (g + 1)%positive with (var_of_lit (Pos g) + 1)%positive by reflexivity.
  rewrite newer_than_lit_add_diag_r. done.
Qed.

Lemma mk_env_conj_preserve :
  forall E g (l1 l2 : literal) E' g' cs lr,
    mk_env_conj E g l1 l2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  move=> E g l1 l2 E' g' cs lr. case=> <- _ _ _. exact: env_upd_eq_preserve.
Qed.

Lemma mk_env_conj_sat :
  forall E g (l1 l2 : literal) E' g' cs lr,
    mk_env_conj E g l1 l2 = (E', g', cs, lr) ->
    newer_than_lit g l1 -> newer_than_lit g l2 ->
    interp_cnf E' cs.
Proof.
  move=> E g l1 l2 E' g' cs lr. case=> <- _ <- Hlr /= Hnew1 Hnew2.
  rewrite !interp_lit_neg_lit. rewrite env_upd_eq.
  rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hnew1)).
  rewrite (interp_lit_env_upd_neq _ _ (newer_than_lit_neq Hnew2)).
  by case: (interp_lit E l1); case: (interp_lit E l2).
Qed.



(* ===== bit_blast_exp and bit_blast_bexp ===== *)

Fixpoint bit_blast_exp w (m : vm) (g : generator) (e : QFBV64.exp w) : vm * generator * cnf * w.-tuple literal :=
  match e with
  | QFBV64.bvVar v =>
    match VM.find v m with
    | None => let '(g', cs, rs) := bit_blast_var g v in
              (VM.add v rs m, g', cs, rs)
    | Some rs => (m, g, [], rs)
    end
  | QFBV64.bvConst w n => let '(g', cs, rs) := bit_blast_const g n in
                          (m, g', cs, rs)
  | QFBV64.bvNot w e => (m, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvAnd w e e2 => (m, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvOr w e1 e2 => (m, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvXor w e1 e2 => (m, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvNeg w e => (m, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvAdd w e1 e2 => (m, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvSub w e1 e2 => (m, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvMul w e1 e2 => (m, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvMod w e1 e2 => (m, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvSrem w e1 e2 => (m, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvSmod w e1 e2 => (m, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvShl w e1 e2 => (m, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvLshr w e1 e2 => (m, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvAshr w e1 e2 => (m, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvConcat w1 w2 e1 e2 => (m, g, [], copy (w2 + w1) lit_tt) (* TODO *)
  | QFBV64.bvExtract w i j e => (m, g, [], copy (i - j + 1) lit_tt) (* TODO *)
  | QFBV64.bvSlice w1 w2 w3 e => (m, g, [], copy w2 lit_tt) (* TODO *)
  | QFBV64.bvHigh wh wl e => (m, g, [], copy wh lit_tt) (* TODO *)
  | QFBV64.bvLow wh wl e => (m, g, [], copy wl lit_tt) (* TODO *)
  | QFBV64.bvZeroExtend w n e => (m, g, [], copy (w+n) lit_tt) (* TODO *)
  | QFBV64.bvSignExtend w n e => (m, g, [], copy (w.+1+n) lit_tt) (* TODO *)
  | QFBV64.bvIte w c e1 e2 =>
    let '(mc, gc, csc, lc) := bit_blast_bexp m g c in
    let '(m1, g1, cs1, ls1) := bit_blast_exp mc gc e1 in
    let '(m2, g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let '(gr, csr, lsr) := bit_blast_ite g2 lc ls1 ls2 in
    (m2, gr, csc++cs1++cs2++csr, lsr)
  end
with
bit_blast_bexp (m : vm) (g : generator) (e : QFBV64.bexp) : vm * generator * cnf * literal :=
  match e with
  | QFBV64.bvFalse => (m, g, [], lit_ff)
  | QFBV64.bvTrue => (m, g, [], lit_tt)
  | QFBV64.bvEq _ e1 e2 =>
    let '(m1, g1, cs1, ls1) := bit_blast_exp m g e1 in
    let '(m2, g2, cs2, ls2) := bit_blast_exp m1 g1 e2 in
    let '(g', cs, r) := bit_blast_eq g2 ls1 ls2 in
    (m2, g', cs1++cs2++cs, r)
  | QFBV64.bvUlt w e1 e2 => (m, g, [], lit_ff) (* TODO *)
  | QFBV64.bvUle w e1 e2 => (m, g, [], lit_ff) (* TODO *)
  | QFBV64.bvUgt w e1 e2 => (m, g, [], lit_ff) (* TODO *)
  | QFBV64.bvUge w e1 e2 => (m, g, [], lit_ff) (* TODO *)
  | QFBV64.bvSlt w e1 e2 => (m, g, [], lit_ff) (* TODO *)
  | QFBV64.bvSle w e1 e2 => (m, g, [], lit_ff) (* TODO *)
  | QFBV64.bvSgt w e1 e2 => (m, g, [], lit_ff) (* TODO *)
  | QFBV64.bvSge w e1 e2 => (m, g, [], lit_ff) (* TODO *)
  | QFBV64.bvUaddo w e1 e2 => (m, g, [], lit_ff) (* TODO *)
  | QFBV64.bvUsubo w e1 e2 => (m, g, [], lit_ff) (* TODO *)
  | QFBV64.bvUmulo w e1 e2 => (m, g, [], lit_ff) (* TODO *)
  | QFBV64.bvSaddo w e1 e2 => (m, g, [], lit_ff) (* TODO *)
  | QFBV64.bvSsubo w e1 e2 => (m, g, [], lit_ff) (* TODO *)
  | QFBV64.bvSmulo w e1 e2 => (m, g, [], lit_ff) (* TODO *)
  | QFBV64.bvLneg e => (m, g, [], lit_ff) (* TODO *)
  | QFBV64.bvConj e1 e2 =>
    let '(m1, g1, cs1, l1) := bit_blast_bexp m g e1 in
    let '(m2, g2, cs2, l2) := bit_blast_bexp m1 g1 e2 in
    let '(g', cs, r) := bit_blast_conj g2 l1 l2 in
    (m2, g', cs1++cs2++cs, r)
  | QFBV64.bvDisj e1 e2 => (m, g, [], lit_ff) (* TODO *)
  end.

Fixpoint mk_env_exp w (m : vm) (s : QFBV64.State.t) (E : env) (g : generator) (e : QFBV64.exp w) : vm * env * generator * cnf * w.-tuple literal :=
  match e with
  | QFBV64.bvVar v =>
    match VM.find v m with
    | None => let '(E', g', cs, rs) := mk_env_var E g (QFBV64.State.acc v s) v in
              (VM.add v rs m, E', g', cs, rs)
    | Some rs => (m, E, g, [], rs)
    end
  | QFBV64.bvConst _ n => let '(E', g', cs, rs) := mk_env_const E g n in
                          (m, E', g', cs, rs)
  | QFBV64.bvNot w e => (m, E, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvAnd w e e2 => (m, E, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvOr w e1 e2 => (m, E, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvXor w e1 e2 => (m, E, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvNeg w e => (m, E, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvAdd w e1 e2 => (m, E, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvSub w e1 e2 => (m, E, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvMul w e1 e2 => (m, E, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvMod w e1 e2 => (m, E, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvSrem w e1 e2 => (m, E, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvSmod w e1 e2 => (m, E, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvShl w e1 e2 => (m, E, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvLshr w e1 e2 => (m, E, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvAshr w e1 e2 => (m, E, g, [], copy w lit_tt) (* TODO *)
  | QFBV64.bvConcat w1 w2 e1 e2 => (m, E, g, [], copy (w2 + w1) lit_tt) (* TODO *)
  | QFBV64.bvExtract w i j e => (m, E, g, [], copy (i - j + 1) lit_tt) (* TODO *)
  | QFBV64.bvSlice w1 w2 w3 e => (m, E, g, [], copy w2 lit_tt) (* TODO *)
  | QFBV64.bvHigh wh wl e => (m, E, g, [], copy wh lit_tt) (* TODO *)
  | QFBV64.bvLow wh wl e => (m, E, g, [], copy wl lit_tt) (* TODO *)
  | QFBV64.bvZeroExtend w n e => (m, E, g, [], copy (w+n) lit_tt) (* TODO *)
  | QFBV64.bvSignExtend w n e => (m, E, g, [], copy (w.+1+n) lit_tt) (* TODO *)
  | QFBV64.bvIte w c e1 e2 =>
    let '(mc, Ec, gc, csc, lc) := mk_env_bexp m s E g c in
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp mc s Ec gc e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(Er, gr, csr, lsr) := mk_env_ite E2 g2 lc ls1 ls2 in
    (m2, Er, gr, csc++cs1++cs2++csr, lsr)
  end
with
mk_env_bexp (m : vm) (s : QFBV64.State.t) (E : env) (g : generator) (e : QFBV64.bexp) : vm * env * generator * cnf * literal :=
  match e with
  | QFBV64.bvFalse => (m, E, g, [], lit_ff)
  | QFBV64.bvTrue => (m, E, g, [], lit_tt)
  | QFBV64.bvEq _ e1 e2 =>
    let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
    let '(E', g', cs, r) := mk_env_eq E2 g2 ls1 ls2 in
    (m2, E', g', cs1++cs2++cs, r)
  | QFBV64.bvUlt w e1 e2 => (m, E, g, [], lit_ff) (* TODO *)
  | QFBV64.bvUle w e1 e2 => (m, E, g, [], lit_ff) (* TODO *)
  | QFBV64.bvUgt w e1 e2 => (m, E, g, [], lit_ff) (* TODO *)
  | QFBV64.bvUge w e1 e2 => (m, E, g, [], lit_ff) (* TODO *)
  | QFBV64.bvSlt w e1 e2 => (m, E, g, [], lit_ff) (* TODO *)
  | QFBV64.bvSle w e1 e2 => (m, E, g, [], lit_ff) (* TODO *)
  | QFBV64.bvSgt w e1 e2 => (m, E, g, [], lit_ff) (* TODO *)
  | QFBV64.bvSge w e1 e2 => (m, E, g, [], lit_ff) (* TODO *)
  | QFBV64.bvUaddo w e1 e2 => (m, E, g, [], lit_ff) (* TODO *)
  | QFBV64.bvUsubo w e1 e2 => (m, E, g, [], lit_ff) (* TODO *)
  | QFBV64.bvUmulo w e1 e2 => (m, E, g, [], lit_ff) (* TODO *)
  | QFBV64.bvSaddo w e1 e2 => (m, E, g, [], lit_ff) (* TODO *)
  | QFBV64.bvSsubo w e1 e2 => (m, E, g, [], lit_ff) (* TODO *)
  | QFBV64.bvSmulo w e1 e2 => (m, E, g, [], lit_ff) (* TODO *)
  | QFBV64.bvLneg e => (m, E, g, [], lit_ff) (* TODO *)
  | QFBV64.bvConj e1 e2 =>
    let '(m1, E1, g1, cs1, l1) := mk_env_bexp m s E g e1 in
    let '(m2, E2, g2, cs2, l2) := mk_env_bexp m1 s E1 g1 e2 in
    let '(E', g', cs, r) := mk_env_conj E2 g2 l1 l2 in
    (m2, E', g', cs1++cs2++cs, r)
  | QFBV64.bvDisj e1 e2 => (m, E, g, [], lit_ff) (* TODO *)
  end.

(* = bit_blast_exp_preserve and bit_blast_bexp_preserve = *)

Ltac bb_exp_bexp_vm_preserve :=
  lazymatch goal with
  | |- vm_preserve ?m ?m => exact: vm_preserve_refl
  | H1 : context f [bit_blast_exp _ _ ?e = (_, _, _, _) -> vm_preserve _ _],
         H2 : bit_blast_exp ?m1 _ ?e = (?m2, _, _, _)
    |- vm_preserve ?m1 ?m2 =>
    eapply H1; exact: H2
  | H1 : context f [bit_blast_bexp _ _ ?e = (_, _, _, _) -> vm_preserve _ _],
         H2 : bit_blast_bexp ?m1 _ ?e = (?m2, _, _, _)
    |- vm_preserve ?m1 ?m2 =>
    eapply H1; exact: H2
  | H1 : context f [bit_blast_exp _ _ ?e = (_, _, _, _) -> vm_preserve _ _],
         H2 : bit_blast_exp ?m1 _ ?e = (?m2, _, _, _)
    |- vm_preserve _ ?m2 =>
    apply: (@vm_preserve_trans _ m1);
    [bb_exp_bexp_vm_preserve | bb_exp_bexp_vm_preserve]
  | H1 : context f [bit_blast_bexp _ _ ?e = (_, _, _, _) -> vm_preserve _ _],
         H2 : bit_blast_bexp ?m1 _ ?e = (?m2, _, _, _)
    |- vm_preserve _ ?m2 =>
    apply: (@vm_preserve_trans _ m1);
    [bb_exp_bexp_vm_preserve | bb_exp_bexp_vm_preserve]
  | |- _ => idtac
  end.

(* Solve vm_preserve for those cases in bit_blast_exp and bit_blast_bexp
   that does not update vm. *)
Ltac auto_bit_blast_vm_preserve :=
  simpl; intros; dcase_hyps; subst; bb_exp_bexp_vm_preserve.

Lemma bit_blast_exp_preserve_var :
  forall (t : VarOrder.t) (m : vm) (g : generator) (m' : vm)
         (g' : generator) (cs : cnf) (lrs : wordsize.-tuple literal),
    bit_blast_exp m g (QFBV64.bvVar t) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  move=> v m g m' g' cs lrs /=. case Hfind: (VM.find v m).
  - case=> <- _ _ _. exact: vm_preserve_refl.
  - case Hv: (bit_blast_var g v)=> [[og ocs] olrs].
    case=> <- _ _ _. exact: vm_preserve_add_diag.
Qed.

Lemma bit_blast_exp_preserve_const :
  forall (w : nat) (b : BITS w) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
    bit_blast_exp m g (QFBV64.bvConst w b) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_not :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvNot w0 e) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_and :
  forall (w0 : nat) (e : QFBV64.exp w0) (e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvAnd w0 e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_or :
  forall (w0 : nat) (e : QFBV64.exp w0) (e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvOr w0 e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_xor :
  forall (w0 : nat) (e : QFBV64.exp w0) (e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvXor w0 e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_neg :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvNeg w0 e) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_add :
  forall (w0 : nat) (e : QFBV64.exp w0) (e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvAdd w0 e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_sub :
  forall (w0 : nat) (e : QFBV64.exp w0) (e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvSub w0 e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_mul :
  forall (w0 : nat) (e : QFBV64.exp w0) (e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvMul w0 e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_mod :
  forall (w0 : nat) (e : QFBV64.exp w0) (e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvMod w0 e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_srem :
  forall (w0 : nat) (e : QFBV64.exp w0) (e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvSrem w0 e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_smod :
  forall (w0 : nat) (e : QFBV64.exp w0) (e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvSmod w0 e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_shl :
  forall (w0 : nat) (e : QFBV64.exp w0) (e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvShl w0 e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_lshr :
  forall (w0 : nat) (e : QFBV64.exp w0) (e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvLshr w0 e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_ashr :
  forall (w0 : nat) (e : QFBV64.exp w0) (e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvAshr w0 e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_concat :
  forall (w1 w2 : nat) (e : QFBV64.exp w1) (e0 : QFBV64.exp w2)
         (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : (w2 + w1).-tuple literal),
    bit_blast_exp m g (QFBV64.bvConcat w1 w2 e e0) = (m', g', cs, lrs) ->
    vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_extract :
  forall (w0 i j : nat) (e : QFBV64.exp (j + (i - j + 1) + (w0 - i - 1)))
         (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : (i - j + 1).-tuple literal),
    bit_blast_exp m g (QFBV64.bvExtract w0 i j e) = (m', g', cs, lrs) ->
    vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_slice :
  forall (w1 w2 w3 : nat) (e : QFBV64.exp (w3 + w2 + w1)) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
    bit_blast_exp m g (QFBV64.bvSlice w1 w2 w3 e) = (m', g', cs, lrs) ->
    vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_high :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh)) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
    bit_blast_exp m g (QFBV64.bvHigh wh wl e) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_low :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh)) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : wl.-tuple literal),
    bit_blast_exp m g (QFBV64.bvLow wh wl e) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_zeroextend :
  forall (w0 n : nat) (e : QFBV64.exp w0) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : (w0 + n).-tuple literal),
    bit_blast_exp m g (QFBV64.bvZeroExtend w0 n e) = (m', g', cs, lrs) ->
    vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_signextend :
  forall (w0 n : nat) (e : QFBV64.exp w0.+1) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : (w0.+1 + n).-tuple literal),
    bit_blast_exp m g (QFBV64.bvSignExtend w0 n e) = (m', g', cs, lrs) ->
    vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_ite :
  forall (w : nat) (b : QFBV64.bexp),
    (forall (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp m g b = (m', g', cs, lr) -> vm_preserve m m') ->
    forall (e : QFBV64.exp w),
      (forall (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (e0 : QFBV64.exp w),
        (forall (m : vm) (g : generator)
                (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
            bit_blast_exp m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
        forall (m : vm) (g : generator)
               (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g (QFBV64.bvIte w b e e0) = (m', g', cs, lrs) ->
          vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_false :
  forall (m : vm) (g : generator) (m' : vm) (g' : generator)
         (cs : cnf) (lrs : literal),
    bit_blast_bexp m g QFBV64.bvFalse = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_true :
  forall (m : vm) (g : generator) (m' : vm) (g' : generator)
         (cs : cnf) (lrs : literal),
    bit_blast_bexp m g QFBV64.bvTrue = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_eq :
  forall (w : nat) (e1 : QFBV64.exp w)
         (IH1 : forall (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e1 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (e2 : QFBV64.exp w)
         (IH2 : forall (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e2 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvEq w e1 e2) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_ult :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvUlt w e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_bexp_preserve_ule :
 forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
        (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
   bit_blast_bexp m g (QFBV64.bvUle w e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_bexp_preserve_ugt :
 forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
        (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
   bit_blast_bexp m g (QFBV64.bvUgt w e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_bexp_preserve_uge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvUge w e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_bexp_preserve_slt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvSlt w e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_bexp_preserve_sle :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvSle w e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_bexp_preserve_sgt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvSgt w e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_bexp_preserve_sge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvSge w e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_bexp_preserve_uaddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvUaddo w e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_bexp_preserve_usubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvUsubo w e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_bexp_preserve_umulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvUmulo w e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_bexp_preserve_saddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvSaddo w e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_bexp_preserve_ssubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvSsubo w e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_bexp_preserve_smulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvSmulo w e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_bexp_preserve_lneg :
  forall (b : QFBV64.bexp) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvLneg b) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_bexp_preserve_conj :
  forall (b : QFBV64.bexp)
         (IH :
            forall (m : vm) (g : generator)
                   (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
              bit_blast_bexp m g b = (m', g', cs, lrs) ->
              vm_preserve m m')
         (b0 : QFBV64.bexp)
         (IH0 :
            forall (m : vm) (g : generator)
                   (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
              bit_blast_bexp m g b0 = (m', g', cs, lrs) ->
              vm_preserve m m')
         (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvConj b b0) = (m', g', cs, lrs) ->
    vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_disj :
  forall (b : QFBV64.bexp) (b0 : QFBV64.bexp) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp m g (QFBV64.bvDisj b b0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Corollary bit_blast_exp_preserve :
  forall w (e : QFBV64.exp w) m g m' g' cs lrs,
    bit_blast_exp m g e = (m', g', cs, lrs) ->
    vm_preserve m m'
  with
    bit_blast_bexp_preserve :
      forall (e : QFBV64.bexp) m g m' g' cs lrs,
        bit_blast_bexp m g e = (m', g', cs, lrs) ->
        vm_preserve m m'.
Proof.
  (* bit_blast_exp_preserve *)
  move=> w [] {w}.
  - exact: bit_blast_exp_preserve_var.
  - exact: bit_blast_exp_preserve_const.
  - exact: bit_blast_exp_preserve_not.
  - exact: bit_blast_exp_preserve_and.
  - exact: bit_blast_exp_preserve_or.
  - exact: bit_blast_exp_preserve_xor.
  - exact: bit_blast_exp_preserve_neg.
  - exact: bit_blast_exp_preserve_add.
  - exact: bit_blast_exp_preserve_sub.
  - exact: bit_blast_exp_preserve_mul.
  - exact: bit_blast_exp_preserve_mod.
  - exact: bit_blast_exp_preserve_srem.
  - exact: bit_blast_exp_preserve_smod.
  - exact: bit_blast_exp_preserve_shl.
  - exact: bit_blast_exp_preserve_lshr.
  - exact: bit_blast_exp_preserve_ashr.
  - exact: bit_blast_exp_preserve_concat.
  - exact: bit_blast_exp_preserve_extract.
  - exact: bit_blast_exp_preserve_slice.
  - exact: bit_blast_exp_preserve_high.
  - exact: bit_blast_exp_preserve_low.
  - exact: bit_blast_exp_preserve_zeroextend.
  - exact: bit_blast_exp_preserve_signextend.
  - move=> w c e1 e2.
    move: (bit_blast_bexp_preserve c) (bit_blast_exp_preserve _ e1)
                                      (bit_blast_exp_preserve _ e2) => IHc IH1 IH2.
    exact: (bit_blast_exp_preserve_ite IHc IH1 IH2).
  (* bit_blast_bexp_preserve *)
  move=> [].
  - exact: bit_blast_bexp_preserve_false.
  - exact: bit_blast_bexp_preserve_true.
  - move=> w e1 e2.
    move: (bit_blast_exp_preserve _ e1) (bit_blast_exp_preserve _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_eq IH1 IH2).
  - exact: bit_blast_bexp_preserve_ult.
  - exact: bit_blast_bexp_preserve_ule.
  - exact: bit_blast_bexp_preserve_ugt.
  - exact: bit_blast_bexp_preserve_uge.
  - exact: bit_blast_bexp_preserve_slt.
  - exact: bit_blast_bexp_preserve_sle.
  - exact: bit_blast_bexp_preserve_sgt.
  - exact: bit_blast_bexp_preserve_sge.
  - exact: bit_blast_bexp_preserve_uaddo.
  - exact: bit_blast_bexp_preserve_usubo.
  - exact: bit_blast_bexp_preserve_umulo.
  - exact: bit_blast_bexp_preserve_saddo.
  - exact: bit_blast_bexp_preserve_ssubo.
  - exact: bit_blast_bexp_preserve_smulo.
  - exact: bit_blast_bexp_preserve_lneg.
  - move=> e1 e2.
    move: (bit_blast_bexp_preserve e1) (bit_blast_bexp_preserve e2) => IH1 IH2.
    exact: (bit_blast_bexp_preserve_conj IH1 IH2).
  - exact: bit_blast_bexp_preserve_disj.
Qed.

(* = bit_blast_exp_correct and bit_blast_bexp_correct = *)

Lemma bit_blast_exp_var :
  forall (t : VarOrder.t) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : wordsize.-tuple literal),
    bit_blast_exp m g (QFBV64.bvVar t) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvVar t) s).
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
  forall (w0 : nat) (b : BITS w0) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvConst w0 b) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvConst w0 b) s).
Proof.
  move=> w bv im ig s E om og ocs olrs. case=> _ _ <- <- _ Hprelude.
  move: (add_prelude_tt Hprelude) => /= Htt {im ig s om og ocs olrs Hprelude}.
  elim: w bv; first by done. move=> w IH. case/tupleP => hd tl.
  rewrite /= mapCons !theadE !beheadCons. apply/andP; split.
  - rewrite /enc_bit. case: hd => /=; by rewrite Htt.
  - exact: IH.
Qed.

Lemma bit_blast_exp_not :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvNot w0 e) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvNot w0 e) s).
Proof.
Admitted.

Lemma bit_blast_exp_and :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvAnd w0 e e0) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvAnd w0 e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_or :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvOr w0 e e0) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvOr w0 e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_xor :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvXor w0 e e0) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvXor w0 e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_neg :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvNeg w0 e) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvNeg w0 e) s).
Proof.
Admitted.

Lemma bit_blast_exp_add :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvAdd w0 e e0) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvAdd w0 e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_sub :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (s : QFBV64.State.t)
         (E : env) (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvSub w0 e e0) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvSub w0 e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_mul :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (s : QFBV64.State.t)
         (E : env) (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvMul w0 e e0) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvMul w0 e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_mod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvMod w0 e e0) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvMod w0 e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_srem :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvSrem w0 e e0) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvSrem w0 e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_smod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvSmod w0 e e0) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvSmod w0 e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_shl :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvShl w0 e e0) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvShl w0 e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_lshr :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvLshr w0 e e0) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvLshr w0 e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_ashr :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    bit_blast_exp m g (QFBV64.bvAshr w0 e e0) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvAshr w0 e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_concat :
  forall (w1 w2 : nat) (e : QFBV64.exp w1) (e0 : QFBV64.exp w2)
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : (w2 + w1).-tuple literal),
    bit_blast_exp m g (QFBV64.bvConcat w1 w2 e e0) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvConcat w1 w2 e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_extract :
  forall (w0 i j : nat) (e : QFBV64.exp (j + (i - j + 1) + (w0 - i - 1)))
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : (i - j + 1).-tuple literal),
    bit_blast_exp m g (QFBV64.bvExtract w0 i j e) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvExtract w0 i j e) s).
Proof.
Admitted.

Lemma bit_blast_exp_slice :
  forall (w1 w2 w3 : nat) (e : QFBV64.exp (w3 + w2 + w1))
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator)
         (cs : cnf) (lrs : w2.-tuple literal),
    bit_blast_exp m g (QFBV64.bvSlice w1 w2 w3 e) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvSlice w1 w2 w3 e) s).
Proof.
Admitted.

Lemma bit_blast_exp_high :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh))
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
    bit_blast_exp m g (QFBV64.bvHigh wh wl e) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvHigh wh wl e) s).
Proof.
Admitted.

Lemma bit_blast_exp_low :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh))
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : wl.-tuple literal),
    bit_blast_exp m g (QFBV64.bvLow wh wl e) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvLow wh wl e) s).
Proof.
Admitted.

Lemma bit_blast_exp_zeroextend :
  forall (w0 n : nat) (e : QFBV64.exp w0)
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : (w0 + n).-tuple literal),
    bit_blast_exp m g (QFBV64.bvZeroExtend w0 n e) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvZeroExtend w0 n e) s).
Proof.
Admitted.

Lemma bit_blast_exp_signextend :
  forall (w0 n : nat) (e : QFBV64.exp w0.+1)
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : (w0.+1 + n).-tuple literal),
    bit_blast_exp m g (QFBV64.bvSignExtend w0 n e) = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvSignExtend w0 n e) s).
Proof.
Admitted.

Lemma bit_blast_exp_ite :
  forall (w : nat) (b : QFBV64.bexp),
    (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp m g b = (m', g', cs, lr) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bit E lr (QFBV64.eval_bexp b s)) ->
    forall (e : QFBV64.exp w),
      (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp e s)) ->
      forall (e0 : QFBV64.exp w),
        (forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
            bit_blast_exp m g e0 = (m', g', cs, lrs) ->
            consistent m' E s ->
            interp_cnf E (add_prelude cs) ->
            enc_bits E lrs (QFBV64.eval_exp e0 s)) ->
        forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
               (m' : vm) (g' : generator)
               (cs : cnf) (lrs : w.-tuple literal),
          bit_blast_exp m g (QFBV64.bvIte w b e e0) = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV64.eval_exp (QFBV64.bvIte w b e e0) s).
Proof.
  move=> w c IHc e1 IH1 e2 IH2 m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock. dcase_goal. case; intros; subst.
  rewrite !add_prelude_append in H8.
  move: H8 => /andP [Hcs0 /andP [Hcs1 /andP [Hcs2 Hcs3]]].
  move: (vm_preserve_consistent (bit_blast_exp_preserve H1) H7) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve H0) Hcon1) => Hcon0.
  move: (IHc _ _ _ _ _ _ _ _ H Hcon0 Hcs0) => Hencl.
  move: (IH1 _ _ _ _ _ _ _ _ H0 Hcon1 Hcs1) => Hencls.
  move: (IH2 _ _ _ _ _ _ _ _ H1 H7 Hcs2) => Hencls0.
  apply: (bit_blast_ite_correct H2 Hencl Hencls Hencls0 Hcs3). reflexivity.
Qed.

Lemma bit_blast_bexp_false :
  forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g QFBV64.bvFalse = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) -> enc_bit E lr (QFBV64.eval_bexp QFBV64.bvFalse s).
Proof.
  move=> im ig s E om og ocs olr [] <- _ <- <- Hcon Hcs /=.
  exact: (add_prelude_enc_bit_ff Hcs).
Qed.

Lemma bit_blast_bexp_true :
  forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g QFBV64.bvTrue = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) -> enc_bit E lr (QFBV64.eval_bexp QFBV64.bvTrue s).
Proof.
  move=> im ig s E om og ocs olr [] <- _ <- <- Hcon Hcs /=.
  exact: (add_prelude_enc_bit_tt Hcs).
Qed.

Lemma bit_blast_bexp_eq :
  forall (w : nat)
         (e : QFBV64.exp w)
         (IH : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e = (m', g', cs, lrs) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bits E lrs (QFBV64.eval_exp e s))
         (e0 : QFBV64.exp w)
         (IH0 : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
             bit_blast_exp m g e0 = (m', g', cs, lrs) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bits E lrs (QFBV64.eval_exp e0 s))
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvEq w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvEq w e e0) s).
Proof.
  move=> w e1 IH1 e2 IH2 im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblasteq: (bit_blast_eq g2 rs1 rs2) => [[geq cseq] req].
  case => Hom Hog Hocs Holrs Hcon Hcs. rewrite -Hocs in Hcs => {Hocs ocs}.
  rewrite Hog in Hblasteq => {Hog geq}. rewrite Hom in Hblast2 => {Hom m2}.
  rewrite Holrs in Hblasteq => {Holrs req}.
  rewrite 2!add_prelude_append in Hcs. move/andP: Hcs => [Hcs1 Hcs].
  move/andP: Hcs => [Hcs2 Hcseq].
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon'.
  move: (IH1 _ _ _ _ _ _ _ _ Hblast1 Hcon' Hcs1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ Hblast2 Hcon Hcs2) => Henc2.
  exact: (bit_blast_eq_correct Hblasteq Henc1 Henc2 Hcseq).
Qed.

Lemma bit_blast_bexp_ult :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvUlt w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvUlt w e e0) s).
Proof.
Admitted.

Lemma bit_blast_bexp_ule :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvUle w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvUle w e e0) s).
Proof.
Admitted.

Lemma bit_blast_bexp_ugt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvUgt w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvUgt w e e0) s).
Proof.
Admitted.

Lemma bit_blast_bexp_uge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvUge w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvUge w e e0) s).
Proof.
Admitted.

Lemma bit_blast_bexp_slt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvSlt w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvSlt w e e0) s).
Proof.
Admitted.

Lemma bit_blast_bexp_sle :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvSle w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvSle w e e0) s).
Proof.
Admitted.

Lemma bit_blast_bexp_sgt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvSgt w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvSgt w e e0) s).
Proof.
Admitted.

Lemma bit_blast_bexp_sge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvSge w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvSge w e e0) s).
Proof.
Admitted.

Lemma bit_blast_bexp_uaddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvUaddo w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvUaddo w e e0) s).
Proof.
Admitted.

Lemma bit_blast_bexp_usubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvUsubo w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvUsubo w e e0) s).
Proof.
Admitted.

Lemma bit_blast_bexp_umulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvUmulo w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvUmulo w e e0) s).
Proof.
Admitted.

Lemma bit_blast_bexp_saddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvSaddo w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvSaddo w e e0) s).
Proof.
Admitted.

Lemma bit_blast_bexp_ssubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvSsubo w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvSsubo w e e0) s).
Proof.
Admitted.

Lemma bit_blast_bexp_smulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvSmulo w e e0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvSmulo w e e0) s).
Proof.
Admitted.

Lemma bit_blast_bexp_lneg :
  forall (b : QFBV64.bexp) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvLneg b) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvLneg b) s).
Proof.
Admitted.

Lemma bit_blast_bexp_conj :
  forall (b : QFBV64.bexp)
         (IH : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
             bit_blast_bexp m g b = (m', g', cs, lr) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bit E lr (QFBV64.eval_bexp b s))
         (b0 : QFBV64.bexp)
         (IH0 : forall (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
             bit_blast_bexp m g b0 = (m', g', cs, lr) ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             enc_bit E lr (QFBV64.eval_bexp b0 s))
         (m : vm) (g : generator) (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvConj b b0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvConj b b0) s).
Proof.
  move=> e1 IH1 e2 IH2 m g s E m' g' cs lr.
  rewrite /bit_blast_bexp -/bit_blast_bexp.
  case Hblast1: (bit_blast_bexp m g e1) => [[[m1 g1] cs1] r1].
  case Hblast2: (bit_blast_bexp m1 g1 e2) => [[[m2 g2] cs2] r2].
  case Hconj: (bit_blast_conj g2 r1 r2) => [[og ocs] olr].
  case=> <- _ <- <- Hcon Hcs. rewrite !add_prelude_append in Hcs.
  move: Hcs => /andP [Hcs1 /andP [Hcs2 Hocs]]. rewrite /=.
  apply: (bit_blast_conj_correct Hconj _ _ Hocs).
  - move: (vm_preserve_consistent (bit_blast_bexp_preserve Hblast2) Hcon) => Hcon'.
    exact: (IH1 _ _ _ _ _ _ _ _ Hblast1 Hcon' Hcs1).
  - exact: (IH2 _ _ _ _ _ _ _ _ Hblast2 Hcon Hcs2).
Qed.

Lemma bit_blast_bexp_disj :
  forall (b b0 : QFBV64.bexp) (m : vm) (g : generator)
         (s : QFBV64.State.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp m g (QFBV64.bvDisj b b0) = (m', g', cs, lr) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (QFBV64.eval_bexp (QFBV64.bvDisj b b0) s).
Proof.
Admitted.

Corollary bit_blast_exp_correct :
  forall w (e : QFBV64.exp w) m g s E m' g' cs lrs,
    bit_blast_exp m g e = (m', g', cs, lrs) ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (QFBV64.eval_exp e s)
  with
    bit_blast_bexp_correct :
      forall (e : QFBV64.bexp) m g s E m' g' cs lr,
        bit_blast_bexp m g e = (m', g', cs, lr) ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        enc_bit E lr (QFBV64.eval_bexp e s).
Proof.
  (* bit_blast_exp_correct *)
  move=> w [] {w}.
  - exact: bit_blast_exp_var.
  - exact: bit_blast_exp_const.
  - exact: bit_blast_exp_not.
  - exact: bit_blast_exp_and.
  - exact: bit_blast_exp_or.
  - exact: bit_blast_exp_xor.
  - exact: bit_blast_exp_neg.
  - exact: bit_blast_exp_add.
  - exact: bit_blast_exp_sub.
  - exact: bit_blast_exp_mul.
  - exact: bit_blast_exp_mod.
  - exact: bit_blast_exp_srem.
  - exact: bit_blast_exp_smod.
  - exact: bit_blast_exp_shl.
  - exact: bit_blast_exp_lshr.
  - exact: bit_blast_exp_ashr.
  - exact: bit_blast_exp_concat.
  - exact: bit_blast_exp_extract.
  - exact: bit_blast_exp_slice.
  - exact: bit_blast_exp_high.
  - exact: bit_blast_exp_low.
  - exact: bit_blast_exp_zeroextend.
  - exact: bit_blast_exp_signextend.
  - move=> w c e1 e2.
    move: (bit_blast_bexp_correct c) (bit_blast_exp_correct _ e1)
                                     (bit_blast_exp_correct _ e2) => IHc IH1 IH2.
    exact: (bit_blast_exp_ite IHc IH1 IH2).
  (* bit_blast_bexp_correct *)
  move=> [].
  - exact: bit_blast_bexp_false.
  - exact: bit_blast_bexp_true.
  - move=> w e1 e2.
    move: (bit_blast_exp_correct _ e1) (bit_blast_exp_correct _ e2) => IH1 IH2.
    exact: (bit_blast_bexp_eq IH1 IH2).
  - exact: bit_blast_bexp_ult.
  - exact: bit_blast_bexp_ule.
  - exact: bit_blast_bexp_ugt.
  - exact: bit_blast_bexp_uge.
  - exact: bit_blast_bexp_slt.
  - exact: bit_blast_bexp_sle.
  - exact: bit_blast_bexp_sgt.
  - exact: bit_blast_bexp_sge.
  - exact: bit_blast_bexp_uaddo.
  - exact: bit_blast_bexp_usubo.
  - exact: bit_blast_bexp_umulo.
  - exact: bit_blast_bexp_saddo.
  - exact: bit_blast_bexp_ssubo.
  - exact: bit_blast_bexp_smulo.
  - exact: bit_blast_bexp_lneg.
  - move=> e1 e2.
    move: (bit_blast_bexp_correct e1) (bit_blast_bexp_correct e2) => IH1 IH2.
    exact: (bit_blast_bexp_conj IH1 IH2).
  - exact: bit_blast_bexp_disj.
Qed.

(* = mk_env_exp_is_bit_blast_exp and mk_env_bexp_is_bit_blast_bexp = *)

Lemma mk_env_exp_is_bit_blast_exp_var :
  forall (t : VarOrder.t) (m : vm) (E : env) (g : generator)
         (s : QFBV64.State.t) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : wordsize.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvVar t) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvVar t) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  - case; intros; subst; reflexivity.
  - rewrite (mk_env_var_is_bit_blast_var H). reflexivity.
Qed.

Lemma mk_env_exp_is_bit_blast_exp_const :
  forall (w0 : nat) (b : BITS w0) (m : vm) (E : env) (g : generator)
         (s : QFBV64.State.t) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConst w0 b) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvConst w0 b) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst; reflexivity.
Qed.

Lemma mk_env_exp_is_bit_blast_exp_not :
 forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (E : env)
   (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
   (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
 mk_env_exp m s E g (QFBV64.bvNot w0 e) = (m', E', g', cs, lrs) ->
 bit_blast_exp m g (QFBV64.bvNot w0 e) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_and :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAnd w0 e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvAnd w0 e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_or :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvOr w0 e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvOr w0 e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_xor :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvXor w0 e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvXor w0 e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_neg :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNeg w0 e) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvNeg w0 e) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_add :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAdd w0 e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvAdd w0 e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_sub :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSub w0 e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvSub w0 e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_mul :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMul w0 e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvMul w0 e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_mod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMod w0 e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvMod w0 e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_srem :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSrem w0 e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvSrem w0 e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_smod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSmod w0 e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvSmod w0 e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_shl :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvShl w0 e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvShl w0 e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_lshr :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvLshr w0 e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvLshr w0 e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_ashr :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAshr w0 e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvAshr w0 e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_concat :
  forall (w1 w2 : nat) (e : QFBV64.exp w1) (e0 : QFBV64.exp w2)
         (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : (w2 + w1).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConcat w1 w2 e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvConcat w1 w2 e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_extract :
  forall (w0 i j : nat) (e : QFBV64.exp (j + (i - j + 1) + (w0 - i - 1)))
         (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf)
         (lrs : (i - j + 1).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvExtract w0 i j e) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvExtract w0 i j e) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_slice :
  forall (w1 w2 w3 : nat) (e : QFBV64.exp (w3 + w2 + w1))
         (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvSlice w1 w2 w3 e) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_high :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh)) (m : vm)
         (E : env) (g : generator) (s : QFBV64.State.t) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvHigh wh wl e) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvHigh wh wl e) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_low :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh)) (m : vm)
         (E : env) (g : generator) (s : QFBV64.State.t) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : wl.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvLow wh wl e) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvLow wh wl e) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_zeroextend :
  forall (w0 n : nat) (e : QFBV64.exp w0) (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : (w0 + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvZeroExtend w0 n e) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvZeroExtend w0 n e) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_signextend :
  forall (w0 n : nat) (e : QFBV64.exp w0.+1) (m : vm) (E : env)
         (g : generator) (s : QFBV64.State.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : (w0.+1 + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSignExtend w0 n e) = (m', E', g', cs, lrs) ->
    bit_blast_exp m g (QFBV64.bvSignExtend w0 n e) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_ite :
  forall (w : nat) (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        bit_blast_bexp m g b = (m', g', cs, lr)) ->
  forall (e : QFBV64.exp w),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV64.exp w),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
    forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvIte w b e e0) = (m', E', g', cs, lrs) ->
      bit_blast_exp m g (QFBV64.bvIte w b e e0) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _ _ _ _ H2) (H0 _ _ _ _ _ _ _ _ _ H4) (H1 _ _ _ _ _ _ _ _ _ H3).
  rewrite (mk_env_ite_is_bit_blast_ite H5). reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) ->
    bit_blast_bexp m g QFBV64.bvFalse = (m', g', cs, lr).
Proof.
  rewrite /=; intros; dcase_hyps; subst; reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) ->
    bit_blast_bexp m g QFBV64.bvTrue = (m', g', cs, lr).
Proof.
  rewrite /=; intros; dcase_hyps; subst; reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_eq :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (E : env) (g : generator) (s : QFBV64.State.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e0 = (m', g', cs, lrs)) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvEq w e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvEq w e e0) = (m', g', cs, lr).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _ _ _ _ H1). rewrite (H0 _ _ _ _ _ _ _ _ _ H3).
  rewrite (mk_env_eq_is_bit_blast_eq H2). reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_ult :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUlt w e e0) = (m', E', g', cs, lr) ->
    bit_blast_bexp m g (QFBV64.bvUlt w e e0) = (m', g', cs, lr).
Proof.
Admitted.

Lemma mk_env_bexp_is_bit_blast_bexp_ule :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUle w e e0) = (m', E', g', cs, lr) ->
    bit_blast_bexp m g (QFBV64.bvUle w e e0) = (m', g', cs, lr).
Proof.
Admitted.

Lemma mk_env_bexp_is_bit_blast_bexp_ugt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUgt w e e0) = (m', E', g', cs, lr) ->
    bit_blast_bexp m g (QFBV64.bvUgt w e e0) = (m', g', cs, lr).
Proof.
Admitted.

Lemma mk_env_bexp_is_bit_blast_bexp_uge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUge w e e0) = (m', E', g', cs, lr) ->
    bit_blast_bexp m g (QFBV64.bvUge w e e0) = (m', g', cs, lr).
Proof.
Admitted.

Lemma mk_env_bexp_is_bit_blast_bexp_slt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSlt w e e0) = (m', E', g', cs, lr) ->
    bit_blast_bexp m g (QFBV64.bvSlt w e e0) = (m', g', cs, lr).
Proof.
Admitted.

Lemma mk_env_bexp_is_bit_blast_bexp_sle :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSle w e e0) = (m', E', g', cs, lr) ->
    bit_blast_bexp m g (QFBV64.bvSle w e e0) = (m', g', cs, lr).
Proof.
Admitted.

Lemma mk_env_bexp_is_bit_blast_bexp_sgt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSgt w e e0) = (m', E', g', cs, lr) ->
    bit_blast_bexp m g (QFBV64.bvSgt w e e0) = (m', g', cs, lr).
Proof.
Admitted.

Lemma mk_env_bexp_is_bit_blast_bexp_sge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSge w e e0) = (m', E', g', cs, lr) ->
    bit_blast_bexp m g (QFBV64.bvSge w e e0) = (m', g', cs, lr).
Proof.
Admitted.

Lemma mk_env_bexp_is_bit_blast_bexp_uaddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUaddo w e e0) = (m', E', g', cs, lr) ->
    bit_blast_bexp m g (QFBV64.bvUaddo w e e0) = (m', g', cs, lr).
Proof.
Admitted.

Lemma mk_env_bexp_is_bit_blast_bexp_usubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUsubo w e e0) = (m', E', g', cs, lr) ->
    bit_blast_bexp m g (QFBV64.bvUsubo w e e0) = (m', g', cs, lr).
Proof.
Admitted.

Lemma mk_env_bexp_is_bit_blast_bexp_umulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUmulo w e e0) = (m', E', g', cs, lr) ->
    bit_blast_bexp m g (QFBV64.bvUmulo w e e0) = (m', g', cs, lr).
Proof.
Admitted.

Lemma mk_env_bexp_is_bit_blast_bexp_saddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSaddo w e e0) = (m', E', g', cs, lr) ->
    bit_blast_bexp m g (QFBV64.bvSaddo w e e0) = (m', g', cs, lr).
Proof.
Admitted.

Lemma mk_env_bexp_is_bit_blast_bexp_ssubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSsubo w e e0) = (m', E', g', cs, lr) ->
    bit_blast_bexp m g (QFBV64.bvSsubo w e e0) = (m', g', cs, lr).
Proof.
Admitted.

Lemma mk_env_bexp_is_bit_blast_bexp_smulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSmulo w e e0) = (m', E', g', cs, lr) ->
    bit_blast_bexp m g (QFBV64.bvSmulo w e e0) = (m', g', cs, lr).
Proof.
Admitted.

Lemma mk_env_bexp_is_bit_blast_bexp_lneg :
  forall (b : QFBV64.bexp) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvLneg b) = (m', E', g', cs, lr) ->
    bit_blast_bexp m g (QFBV64.bvLneg b) = (m', g', cs, lr).
Proof.
Admitted.

Lemma mk_env_bexp_is_bit_blast_bexp_conj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        bit_blast_bexp m g b = (m', g', cs, lr)) ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          bit_blast_bexp m g b0 = (m', g', cs, lr)) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
        bit_blast_bexp m g (QFBV64.bvConj b b0) = (m', g', cs, lr).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  rewrite (H _ _ _ _ _ _  _ _ _ H1). rewrite (H0 _ _ _ _ _ _  _ _ _ H3). reflexivity.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_disj :
  forall (b b0 : QFBV64.bexp) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvDisj b b0) = (m', E', g', cs, lr) ->
    bit_blast_bexp m g (QFBV64.bvDisj b b0) = (m', g', cs, lr).
Proof.
Admitted.

Corollary mk_env_exp_is_bit_blast_exp :
  forall w (e : QFBV64.exp w) m E g s m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    bit_blast_exp m g e = (m', g', cs, lrs)
  with
    mk_env_bexp_is_bit_blast_bexp :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        bit_blast_bexp m g e = (m', g', cs, lr).
Proof.
  (* mk_env_exp_is_bit_blast_exp *)
  move=> w [] {w}.
  - exact: mk_env_exp_is_bit_blast_exp_var.
  - exact: mk_env_exp_is_bit_blast_exp_const.
  - exact: mk_env_exp_is_bit_blast_exp_not.
  - exact: mk_env_exp_is_bit_blast_exp_and.
  - exact: mk_env_exp_is_bit_blast_exp_or.
  - exact: mk_env_exp_is_bit_blast_exp_xor.
  - exact: mk_env_exp_is_bit_blast_exp_neg.
  - exact: mk_env_exp_is_bit_blast_exp_add.
  - exact: mk_env_exp_is_bit_blast_exp_sub.
  - exact: mk_env_exp_is_bit_blast_exp_mul.
  - exact: mk_env_exp_is_bit_blast_exp_mod.
  - exact: mk_env_exp_is_bit_blast_exp_srem.
  - exact: mk_env_exp_is_bit_blast_exp_smod.
  - exact: mk_env_exp_is_bit_blast_exp_shl.
  - exact: mk_env_exp_is_bit_blast_exp_lshr.
  - exact: mk_env_exp_is_bit_blast_exp_ashr.
  - exact: mk_env_exp_is_bit_blast_exp_concat.
  - exact: mk_env_exp_is_bit_blast_exp_extract.
  - exact: mk_env_exp_is_bit_blast_exp_slice.
  - exact: mk_env_exp_is_bit_blast_exp_high.
  - exact: mk_env_exp_is_bit_blast_exp_low.
  - exact: mk_env_exp_is_bit_blast_exp_zeroextend.
  - exact: mk_env_exp_is_bit_blast_exp_signextend.
  - move=> w c e1 e2.
    move: (mk_env_bexp_is_bit_blast_bexp c)
            (mk_env_exp_is_bit_blast_exp _ e1)
            (mk_env_exp_is_bit_blast_exp _ e2) => IHc IH1 IH2.
    exact: (mk_env_exp_is_bit_blast_exp_ite IHc IH1 IH2).
  (* mk_env_bexp_is_bit_blast_bexp *)
  case.
  - exact: mk_env_bexp_is_bit_blast_bexp_false.
  - exact: mk_env_bexp_is_bit_blast_bexp_true.
  - move=> w e1 e2.
    move: (mk_env_exp_is_bit_blast_exp _ e1) (mk_env_exp_is_bit_blast_exp _ e2)
    => IH1 IH2. exact: (mk_env_bexp_is_bit_blast_bexp_eq IH1 IH2).
  - exact: mk_env_bexp_is_bit_blast_bexp_ult.
  - exact: mk_env_bexp_is_bit_blast_bexp_ule.
  - exact: mk_env_bexp_is_bit_blast_bexp_ugt.
  - exact: mk_env_bexp_is_bit_blast_bexp_uge.
  - exact: mk_env_bexp_is_bit_blast_bexp_slt.
  - exact: mk_env_bexp_is_bit_blast_bexp_sle.
  - exact: mk_env_bexp_is_bit_blast_bexp_sgt.
  - exact: mk_env_bexp_is_bit_blast_bexp_sge.
  - exact: mk_env_bexp_is_bit_blast_bexp_uaddo.
  - exact: mk_env_bexp_is_bit_blast_bexp_usubo.
  - exact: mk_env_bexp_is_bit_blast_bexp_umulo.
  - exact: mk_env_bexp_is_bit_blast_bexp_saddo.
  - exact: mk_env_bexp_is_bit_blast_bexp_ssubo.
  - exact: mk_env_bexp_is_bit_blast_bexp_smulo.
  - exact: mk_env_bexp_is_bit_blast_bexp_lneg.
  - move=> e1 e2.
    move: (mk_env_bexp_is_bit_blast_bexp e1) (mk_env_bexp_is_bit_blast_bexp e2) =>
    IH1 IH2. exact: (mk_env_bexp_is_bit_blast_bexp_conj IH1 IH2).
  - exact: mk_env_bexp_is_bit_blast_bexp_disj.
Qed.

(* = mk_env_exp_newer_gen and mk_env_bexp_newer_gen = *)

Lemma mk_env_exp_newer_gen_var :
  forall (t : VarOrder.t) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : wordsize.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvVar t) = (m', E', g', cs, lrs) -> (g <=? g')%positive.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case: (VM.find v m).
  - move=> ls [] _ _ <- _ _. exact: Pos.leb_refl.
  - case Henv: (mk_env_var E g (QFBV64.State.acc v s) v) => [[[oE og] ocs] olrs].
    case=> _ _ <- _ _. exact: (mk_env_var_newer_gen Henv).
Qed.

Lemma mk_env_exp_newer_gen_const :
  forall (w0 : nat) (b : BITS w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConst w0 b) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> w bs m s E g m' E' g' cs lrs /=. case=> _ _ <- _ _. exact: Pos.leb_refl.
Qed.

Lemma mk_env_exp_newer_gen_not :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNot w0 e) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_and :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAnd w0 e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_or :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvOr w0 e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_xor :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvXor w0 e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_neg :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNeg w0 e) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_add :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAdd w0 e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_sub :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSub w0 e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_mul :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMul w0 e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_mod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMod w0 e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_srem :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSrem w0 e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_smod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSmod w0 e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_shl :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvShl w0 e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_lshr :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvLshr w0 e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_ashr :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAshr w0 e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_concat :
  forall (w1 w2 : nat) (e : QFBV64.exp w1) (e0 : QFBV64.exp w2)
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : (w2 + w1).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConcat w1 w2 e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_extract :
  forall (w0 i j : nat) (e : QFBV64.exp (j + (i - j + 1) + (w0 - i - 1)))
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf)
         (lrs : (i - j + 1).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvExtract w0 i j e) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_slice :
  forall (w1 w2 w3 : nat) (e : QFBV64.exp (w3 + w2 + w1))
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_high :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh)) (m : vm)
         (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvHigh wh wl e) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_low :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh)) (m : vm)
         (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : wl.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvLow wh wl e) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_zeroextend :
  forall (w0 n : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : (w0 + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvZeroExtend w0 n e) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_signextend :
  forall (w0 n : nat) (e : QFBV64.exp w0.+1) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : (w0.+1 + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSignExtend w0 n e) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_ite :
  forall (w : nat) (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
    forall (e : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (e0 : QFBV64.exp w),
        (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : w.-tuple literal),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
        forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g (QFBV64.bvIte w b e e0) = (m', E', g', cs, lrs) ->
          (g <=? g')%positive.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_ite_newer_gen H5) => Hg2g'. move: (H1 _ _ _ _ _ _ _ _ _ H3) => Hg1g2.
  move: (H0 _ _ _ _ _ _ _ _ _ H4) => Hg0g1. move: (H _ _ _ _ _ _ _ _ _ H2) => Hgg0.
  apply: (pos_leb_trans _ Hg2g'). apply: (pos_leb_trans _ Hg1g2).
  apply: (pos_leb_trans _ Hg0g1). exact: Hgg0.
Qed.

Lemma mk_env_bexp_newer_gen_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) -> (g <=? g')%positive.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- _ _. exact: Pos.leb_refl.
Qed.

Lemma mk_env_bexp_newer_gen_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) -> (g <=? g')%positive.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- _ _. exact: Pos.leb_refl.
Qed.

Lemma mk_env_bexp_newer_gen_eq :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvEq w e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- _ _. apply: (pos_leb_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (pos_leb_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  exact: (mk_env_eq_newer_gen Heq).
Qed.

Lemma mk_env_bexp_newer_gen_ult :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUlt w e e0) = (m', E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_bexp_newer_gen_ule :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUle w e e0) = (m', E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_bexp_newer_gen_ugt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUgt w e e0) = (m', E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_bexp_newer_gen_uge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUge w e e0) = (m', E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_bexp_newer_gen_slt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSlt w e e0) = (m', E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_bexp_newer_gen_sle :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSle w e e0) = (m', E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_bexp_newer_gen_sgt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSgt w e e0) = (m', E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_bexp_newer_gen_sge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSge w e e0) = (m', E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_bexp_newer_gen_uaddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUaddo w e e0) = (m', E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_bexp_newer_gen_usubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUsubo w e e0) = (m', E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_bexp_newer_gen_umulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUmulo w e e0) = (m', E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_bexp_newer_gen_saddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSaddo w e e0) = (m', E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_bexp_newer_gen_ssubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSsubo w e e0) = (m', E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_bexp_newer_gen_smulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSmulo w e e0) = (m', E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_bexp_newer_gen_lneg :
  forall (b : QFBV64.bexp) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvLneg b) = (m', E', g', cs, lr) -> (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_bexp_newer_gen_conj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case Hconj: (mk_env_conj E2 g2 lr1 lr2)=> [[[oE og] ocs] olr].
  case=> _ _ <- _ _. apply: (pos_leb_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (pos_leb_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  exact: (mk_env_conj_newer_gen Hconj).
Qed.

Lemma mk_env_bexp_newer_gen_disj :
  forall (b b0 : QFBV64.bexp) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvDisj b b0) = (m', E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
Admitted.

Corollary mk_env_exp_newer_gen :
  forall w (e : QFBV64.exp w) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    (g <=? g')%positive
  with
    mk_env_bexp_newer_gen :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  (* mk_env_exp_newer_gen *)
  move=> w [] {w}.
  - exact: mk_env_exp_newer_gen_var.
  - exact: mk_env_exp_newer_gen_const.
  - exact: mk_env_exp_newer_gen_not.
  - exact: mk_env_exp_newer_gen_and.
  - exact: mk_env_exp_newer_gen_or.
  - exact: mk_env_exp_newer_gen_xor.
  - exact: mk_env_exp_newer_gen_neg.
  - exact: mk_env_exp_newer_gen_add.
  - exact: mk_env_exp_newer_gen_sub.
  - exact: mk_env_exp_newer_gen_mul.
  - exact: mk_env_exp_newer_gen_mod.
  - exact: mk_env_exp_newer_gen_srem.
  - exact: mk_env_exp_newer_gen_smod.
  - exact: mk_env_exp_newer_gen_shl.
  - exact: mk_env_exp_newer_gen_lshr.
  - exact: mk_env_exp_newer_gen_ashr.
  - exact: mk_env_exp_newer_gen_concat.
  - exact: mk_env_exp_newer_gen_extract.
  - exact: mk_env_exp_newer_gen_slice.
  - exact: mk_env_exp_newer_gen_high.
  - exact: mk_env_exp_newer_gen_low.
  - exact: mk_env_exp_newer_gen_zeroextend.
  - exact: mk_env_exp_newer_gen_signextend.
  - move=> w c e1 e2.
    move: (mk_env_bexp_newer_gen c)
            (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IHc IH1 IH2.
    exact: (mk_env_exp_newer_gen_ite IHc IH1 IH2).
  (* mk_env_bexp_newer_gen *)
  case.
  - exact: mk_env_bexp_newer_gen_false.
  - exact: mk_env_bexp_newer_gen_true.
  - move=> w e1 e2.
    move: (mk_env_exp_newer_gen _ e1) (mk_env_exp_newer_gen _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_eq IH1 IH2).
  - exact: mk_env_bexp_newer_gen_ult.
  - exact: mk_env_bexp_newer_gen_ule.
  - exact: mk_env_bexp_newer_gen_ugt.
  - exact: mk_env_bexp_newer_gen_uge.
  - exact: mk_env_bexp_newer_gen_slt.
  - exact: mk_env_bexp_newer_gen_sle.
  - exact: mk_env_bexp_newer_gen_sgt.
  - exact: mk_env_bexp_newer_gen_sge.
  - exact: mk_env_bexp_newer_gen_uaddo.
  - exact: mk_env_bexp_newer_gen_usubo.
  - exact: mk_env_bexp_newer_gen_umulo.
  - exact: mk_env_bexp_newer_gen_saddo.
  - exact: mk_env_bexp_newer_gen_ssubo.
  - exact: mk_env_bexp_newer_gen_smulo.
  - exact: mk_env_bexp_newer_gen_lneg.
  - move=> e1 e2.
    move: (mk_env_bexp_newer_gen e1) (mk_env_bexp_newer_gen e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_gen_conj IH1 IH2).
  - exact: mk_env_bexp_newer_gen_disj.
Qed.

(* = mk_env_exp_newer_vm and mk_env_bexp_newer_vm = *)

Lemma mk_env_exp_newer_vm_var :
  forall (t : VarOrder.t) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : wordsize.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvVar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case Hfind: (VM.find v m).
  - case=> <- _ <- _ _ Hnew_gm. exact: Hnew_gm.
  - case Henv: (mk_env_var E g (QFBV64.State.acc v s) v) => [[[oE og] ocs] olrs].
    case=> <- _ <- _ _ Hnew_gm. move=> x lxs. case Hxv: (x == v).
    + rewrite (VM.Lemmas.find_add_eq m olrs Hxv). case=> <-.
      exact: (mk_env_var_newer_res Henv).
    + move/negP: Hxv => Hxv. rewrite (VM.Lemmas.find_add_neq m olrs Hxv) => Hfindx.
      move: (Hnew_gm x lxs Hfindx) => Hnew_og.
      apply: (newer_than_lits_le_newer Hnew_og). exact: (mk_env_var_newer_gen Henv).
Qed.

Lemma mk_env_exp_newer_vm_const :
  forall (w0 : nat) (b : BITS w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConst w0 b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w b m s E g m' E' g' cs lrs. case=> <- _ <- _ _. by apply.
Qed.

Lemma mk_env_exp_newer_vm_not :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNot w0 e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_and :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAnd w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_or :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvOr w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_xor :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvXor w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_neg :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNeg w0 e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_add :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAdd w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_sub :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSub w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_mul :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMul w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_mod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_srem :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSrem w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_smod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSmod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_shl :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvShl w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_lshr :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvLshr w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_ashr :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAshr w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_concat :
  forall (w1 w2 : nat) (e : QFBV64.exp w1) (e0 : QFBV64.exp w2)
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : (w2 + w1).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConcat w1 w2 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_extract :
  forall (w0 i j : nat) (e : QFBV64.exp (j + (i - j + 1) + (w0 - i - 1)))
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf)
         (lrs : (i - j + 1).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvExtract w0 i j e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_slice :
  forall (w1 w2 w3 : nat) (e : QFBV64.exp (w3 + w2 + w1))
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_high :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh)) (m : vm)
         (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvHigh wh wl e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_low :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh)) (m : vm)
         (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : wl.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvLow wh wl e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_zeroextend :
  forall (w0 n : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : (w0 + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvZeroExtend w0 n e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_signextend :
  forall (w0 n : nat) (e : QFBV64.exp w0.+1) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : (w0.+1 + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSignExtend w0 n e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_ite :
  forall (w : nat) (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (e0 : QFBV64.exp w),
        (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : w.-tuple literal),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
            newer_than_vm g m -> newer_than_vm g' m') ->
        forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g (QFBV64.bvIte w b e e0) = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  rewrite /=; intros; dcase_hyps; subst. move: (mk_env_ite_newer_gen H6) => Hg2g'.
  apply: (newer_than_vm_le_newer _ Hg2g').
  apply: (H1 _ _ _ _ _ _ _ _ _ H4). apply: (H0 _ _ _ _ _ _ _ _ _ H5).
  exact: (H _ _ _ _ _ _ _ _ _ H2).
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
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvEq w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> <- _ <- _ _ Hnew.
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew) => Hnew1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1) => Hnew2.
  apply: (newer_than_vm_le_newer Hnew2). exact: (mk_env_eq_newer_gen Heq).
Qed.

Lemma mk_env_bexp_newer_vm_ult :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUlt w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_bexp_newer_vm_ule :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUle w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_bexp_newer_vm_ugt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUgt w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_bexp_newer_vm_uge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUge w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_bexp_newer_vm_slt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSlt w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_bexp_newer_vm_sle :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSle w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_bexp_newer_vm_sgt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSgt w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_bexp_newer_vm_sge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSge w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_bexp_newer_vm_uaddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUaddo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_bexp_newer_vm_usubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUsubo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_bexp_newer_vm_umulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUmulo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_bexp_newer_vm_saddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSaddo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_bexp_newer_vm_ssubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSsubo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_bexp_newer_vm_smulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSmulo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_bexp_newer_vm_lneg :
  forall (b : QFBV64.bexp) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvLneg b) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_bexp_newer_vm_conj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /=.
  case Henv1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case=> <- _ <- _ _ Hnew. apply: newer_than_vm_add_r.
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2). apply: (IH1 _ _ _ _ _ _ _ _ _ Henv1).
  exact: Hnew.
Qed.

Lemma mk_env_bexp_newer_vm_disj :
  forall (b b0 : QFBV64.bexp) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvDisj b b0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Corollary mk_env_exp_newer_vm :
  forall w (e : QFBV64.exp w) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_vm g' m'
  with
    mk_env_bexp_newer_vm :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  (* mk_env_exp_newer_vm *)
  move=> w [] {w}.
  - exact: mk_env_exp_newer_vm_var.
  - exact: mk_env_exp_newer_vm_const.
  - exact: mk_env_exp_newer_vm_not.
  - exact: mk_env_exp_newer_vm_and.
  - exact: mk_env_exp_newer_vm_or.
  - exact: mk_env_exp_newer_vm_xor.
  - exact: mk_env_exp_newer_vm_neg.
  - exact: mk_env_exp_newer_vm_add.
  - exact: mk_env_exp_newer_vm_sub.
  - exact: mk_env_exp_newer_vm_mul.
  - exact: mk_env_exp_newer_vm_mod.
  - exact: mk_env_exp_newer_vm_srem.
  - exact: mk_env_exp_newer_vm_smod.
  - exact: mk_env_exp_newer_vm_shl.
  - exact: mk_env_exp_newer_vm_lshr.
  - exact: mk_env_exp_newer_vm_ashr.
  - exact: mk_env_exp_newer_vm_concat.
  - exact: mk_env_exp_newer_vm_extract.
  - exact: mk_env_exp_newer_vm_slice.
  - exact: mk_env_exp_newer_vm_high.
  - exact: mk_env_exp_newer_vm_low.
  - exact: mk_env_exp_newer_vm_zeroextend.
  - exact: mk_env_exp_newer_vm_signextend.
  - move=> w c e1 e2.
    move: (mk_env_bexp_newer_vm c)
            (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IHc IH1 IH2.
    exact: (mk_env_exp_newer_vm_ite IHc IH1 IH2).
  (* mk_env_bexp_newer_vm *)
  case.
  - exact: mk_env_bexp_newer_vm_false.
  - exact: mk_env_bexp_newer_vm_true.
  - move=> w e1 e2.
    move: (mk_env_exp_newer_vm _ e1) (mk_env_exp_newer_vm _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_eq IH1 IH2).
  - exact: mk_env_bexp_newer_vm_ult.
  - exact: mk_env_bexp_newer_vm_ule.
  - exact: mk_env_bexp_newer_vm_ugt.
  - exact: mk_env_bexp_newer_vm_uge.
  - exact: mk_env_bexp_newer_vm_slt.
  - exact: mk_env_bexp_newer_vm_sle.
  - exact: mk_env_bexp_newer_vm_sgt.
  - exact: mk_env_bexp_newer_vm_sge.
  - exact: mk_env_bexp_newer_vm_uaddo.
  - exact: mk_env_bexp_newer_vm_usubo.
  - exact: mk_env_bexp_newer_vm_umulo.
  - exact: mk_env_bexp_newer_vm_saddo.
  - exact: mk_env_bexp_newer_vm_ssubo.
  - exact: mk_env_bexp_newer_vm_smulo.
  - exact: mk_env_bexp_newer_vm_lneg.
  - move=> e1 e2.
    move: (mk_env_bexp_newer_vm e1) (mk_env_bexp_newer_vm e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_vm_conj IH1 IH2).
  - exact: mk_env_bexp_newer_vm_disj.
Qed.

(* = mk_env_exp_newer_res and mk_env_bexp_newer_res = *)

Lemma mk_env_exp_newer_res_var :
  forall (t : VarOrder.t) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : wordsize.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvVar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case Hfind: (VM.find v m).
  - case=> _ _ <- _ <- Hnew_gm Hnew_gtt. exact: (Hnew_gm v _ Hfind).
  - case Henv: (mk_env_var E g (QFBV64.State.acc v s) v)=> [[[Ev gv] csv] lrsv].
    case=> _ _ <- _ <- Hnew_gm Hnew_gtt. exact: (mk_env_var_newer_res Henv).
Qed.

Lemma mk_env_exp_newer_res_const :
  forall (w0 : nat) (b : BITS w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConst w0 b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> w bs m s E g m' E' g' cs lrs. rewrite /mk_env_exp.
  case Henv: (mk_env_const E g bs)=> [[[oE og] ocs] olrs].
  case=> _ _ <- _ <- Hnew_gm Hnew_tt. exact: (mk_env_const_newer_res Henv Hnew_tt).
Qed.

Lemma mk_env_exp_newer_res_not :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNot w0 e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_and :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAnd w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_or :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvOr w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_xor :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvXor w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_neg :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNeg w0 e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_add :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAdd w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_sub :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSub w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_mul :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMul w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_mod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_srem :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSrem w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_smod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSmod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_shl :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvShl w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_lshr :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvLshr w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_ashr :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAshr w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_concat :
  forall (w1 w2 : nat) (e : QFBV64.exp w1) (e0 : QFBV64.exp w2)
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : (w2 + w1).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConcat w1 w2 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_extract :
  forall (w0 i j : nat) (e : QFBV64.exp (j + (i - j + 1) + (w0 - i - 1)))
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf)
         (lrs : (i - j + 1).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvExtract w0 i j e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_slice :
  forall (w1 w2 w3 : nat) (e : QFBV64.exp (w3 + w2 + w1))
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_high :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh)) (m : vm)
         (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvHigh wh wl e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_low :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh)) (m : vm)
         (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : wl.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvLow wh wl e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_zeroextend :
  forall (w0 n : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : (w0 + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvZeroExtend w0 n e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_signextend :
  forall (w0 n : nat) (e : QFBV64.exp w0.+1) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : (w0.+1 + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSignExtend w0 n e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_ite :
  forall (w : nat) (b : QFBV64.bexp) (e e0 : QFBV64.exp w)
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvIte w b e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. exact: (mk_env_ite_newer_res H4).
Qed.

Lemma mk_env_bexp_newer_res_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- _ <- Hnew. exact: Hnew.
Qed.

Lemma mk_env_bexp_newer_res_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- _ <- Hnew. exact: Hnew.
Qed.

Lemma mk_env_bexp_newer_res_eq :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvEq w e e0) = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  exact: (mk_env_eq_newer_res H1).
Qed.

Lemma mk_env_bexp_newer_res_ult :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUlt w e e0) = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
Admitted.

Lemma mk_env_bexp_newer_res_ule :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUle w e e0) = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
Admitted.

Lemma mk_env_bexp_newer_res_ugt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUgt w e e0) = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
Admitted.

Lemma mk_env_bexp_newer_res_uge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUge w e e0) = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
Admitted.

Lemma mk_env_bexp_newer_res_slt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSlt w e e0) = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
Admitted.

Lemma mk_env_bexp_newer_res_sle :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSle w e e0) = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
Admitted.

Lemma mk_env_bexp_newer_res_sgt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSgt w e e0) = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
Admitted.

Lemma mk_env_bexp_newer_res_sge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSge w e e0) = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
Admitted.

Lemma mk_env_bexp_newer_res_uaddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUaddo w e e0) = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
Admitted.

Lemma mk_env_bexp_newer_res_usubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUsubo w e e0) = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
Admitted.

Lemma mk_env_bexp_newer_res_umulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUmulo w e e0) = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
Admitted.

Lemma mk_env_bexp_newer_res_saddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSaddo w e e0) = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
Admitted.

Lemma mk_env_bexp_newer_res_ssubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSsubo w e e0) = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
Admitted.

Lemma mk_env_bexp_newer_res_smulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSmulo w e e0) = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
Admitted.

Lemma mk_env_bexp_newer_res_lneg :
  forall (b : QFBV64.bexp) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvLneg b) = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
Admitted.

Lemma mk_env_bexp_newer_res_conj :
  forall (b b0 : QFBV64.bexp) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  exact: newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_bexp_newer_res_disj :
  forall (b b0 : QFBV64.bexp) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvDisj b b0) = (m', E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
Admitted.

Corollary mk_env_exp_newer_res :
  forall w (e : QFBV64.exp w) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs
  with
    mk_env_bexp_newer_res :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_lit g lit_tt ->
        newer_than_lit g' lr.
Proof.
  (* mk_env_exp_newer_res *)
  move=> w [].
  - exact: mk_env_exp_newer_res_var.
  - exact: mk_env_exp_newer_res_const.
  - exact: mk_env_exp_newer_res_not.
  - exact: mk_env_exp_newer_res_and.
  - exact: mk_env_exp_newer_res_or.
  - exact: mk_env_exp_newer_res_xor.
  - exact: mk_env_exp_newer_res_neg.
  - exact: mk_env_exp_newer_res_add.
  - exact: mk_env_exp_newer_res_sub.
  - exact: mk_env_exp_newer_res_mul.
  - exact: mk_env_exp_newer_res_mod.
  - exact: mk_env_exp_newer_res_srem.
  - exact: mk_env_exp_newer_res_smod.
  - exact: mk_env_exp_newer_res_shl.
  - exact: mk_env_exp_newer_res_lshr.
  - exact: mk_env_exp_newer_res_ashr.
  - exact: mk_env_exp_newer_res_concat.
  - exact: mk_env_exp_newer_res_extract.
  - exact: mk_env_exp_newer_res_slice.
  - exact: mk_env_exp_newer_res_high.
  - exact: mk_env_exp_newer_res_low.
  - exact: mk_env_exp_newer_res_zeroextend.
  - exact: mk_env_exp_newer_res_signextend.
  - exact: mk_env_exp_newer_res_ite.
  (* mk_env_bexp_newer_res *)
  case.
  - exact: mk_env_bexp_newer_res_false.
  - exact: mk_env_bexp_newer_res_true.
  - exact: mk_env_bexp_newer_res_eq.
  - exact: mk_env_bexp_newer_res_ult.
  - exact: mk_env_bexp_newer_res_ule.
  - exact: mk_env_bexp_newer_res_ugt.
  - exact: mk_env_bexp_newer_res_uge.
  - exact: mk_env_bexp_newer_res_slt.
  - exact: mk_env_bexp_newer_res_sle.
  - exact: mk_env_bexp_newer_res_sgt.
  - exact: mk_env_bexp_newer_res_sge.
  - exact: mk_env_bexp_newer_res_uaddo.
  - exact: mk_env_bexp_newer_res_usubo.
  - exact: mk_env_bexp_newer_res_umulo.
  - exact: mk_env_bexp_newer_res_saddo.
  - exact: mk_env_bexp_newer_res_ssubo.
  - exact: mk_env_bexp_newer_res_smulo.
  - exact: mk_env_bexp_newer_res_lneg.
  - exact: mk_env_bexp_newer_res_conj.
  - exact: mk_env_bexp_newer_res_disj.
Qed.

(* = mk_env_exp_newer_cnf and mk_env_bexp_newer_cnf = *)

Lemma mk_env_exp_newer_cnf_var :
  forall (t : VarOrder.t) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : wordsize.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvVar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case: (VM.find v m).
  - move=> lxs [] _ _ <- <- _ Hnew_gm Hnew_gtt. done.
  - case Henv: (mk_env_var E g (QFBV64.State.acc v s) v)=> [[[Ev gv] csv] lrsv].
    case=> _ _ <- <- _ Hnew_gm Hnew_gtt. exact: (mk_env_var_newer_cnf Henv).
Qed.

Lemma mk_env_exp_newer_cnf_const :
  forall (w0 : nat) (b : BITS w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConst w0 b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
  move=> w bs m s E g m' E' g' cs lrs /=. case=> _ _ <- <- _ Hnew_gm Hnew_gtt. done.
Qed.

Lemma mk_env_exp_newer_cnf_not :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNot w0 e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_and :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAnd w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_or :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvOr w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_xor :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvXor w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_neg :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNeg w0 e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_add :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAdd w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_sub :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSub w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_mul :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMul w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_mod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_srem :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSrem w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_smod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSmod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_shl :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvShl w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_lshr :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvLshr w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_ashr :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAshr w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_concat :
  forall (w1 w2 : nat) (e : QFBV64.exp w1) (e0 : QFBV64.exp w2)
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : (w2 + w1).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConcat w1 w2 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_extract :
  forall (w0 i j : nat) (e : QFBV64.exp (j + (i - j + 1) + (w0 - i - 1)))
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf)
         (lrs : (i - j + 1).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvExtract w0 i j e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_slice :
  forall (w1 w2 w3 : nat) (e : QFBV64.exp (w3 + w2 + w1))
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_high :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh)) (m : vm)
         (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvHigh wh wl e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_low :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh)) (m : vm)
         (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : wl.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvLow wh wl e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_zeroextend :
  forall (w0 n : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : (w0 + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvZeroExtend w0 n e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_signextend :
  forall (w0 n : nat) (e : QFBV64.exp w0.+1) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : (w0.+1 + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSignExtend w0 n e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_ite :
  forall (w : nat) (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
    forall (e : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
      forall (e0 : QFBV64.exp w),
        (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : w.-tuple literal),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
            newer_than_vm g m ->
            newer_than_lit g lit_tt ->
            newer_than_cnf g' cs) ->
        forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g (QFBV64.bvIte w b e e0) = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !newer_than_cnf_append.
  move: (mk_env_bexp_newer_gen H2) => Hgg0.
  move: (mk_env_exp_newer_gen H6) => Hg0g1.
  move: (mk_env_exp_newer_gen H5) => Hg1g2.
  move: (mk_env_ite_newer_gen H7) => Hg2g'.
  (* newer_than_cnf g' cs0 *)
  move: (H _ _ _ _ _ _ _ _ _ H2 H3 H4) => Hnew_g0cs0.
  move: (pos_leb_trans Hg0g1 Hg1g2) => Hg0g2.
  move: (pos_leb_trans Hg0g2 Hg2g') => Hg0g'.
  rewrite (newer_than_cnf_le_newer Hnew_g0cs0 Hg0g') /=.
  (* newer_than_cnf g' cs1 *)
  move: (mk_env_bexp_newer_vm H2 H3) => Hnew_g0m0.
  move: (newer_than_lit_le_newer H4 Hgg0) => Hg0tt.
  move: (H0 _ _ _ _ _ _ _ _ _ H6 Hnew_g0m0 Hg0tt) => Hnew_g1cs1.
  move: (pos_leb_trans Hg1g2 Hg2g') => Hg1g'.
  rewrite (newer_than_cnf_le_newer Hnew_g1cs1 Hg1g') /=.
  (* newer_than_cnf g' cs2 *)
  move: (mk_env_exp_newer_vm H6 Hnew_g0m0) => Hnew_g1m1.
  move: (newer_than_lit_le_newer Hg0tt Hg0g1) => Hg1tt.
  move: (H1 _ _ _ _ _ _ _ _ _ H5 Hnew_g1m1 Hg1tt) => Hnew_g2cs2.
  rewrite (newer_than_cnf_le_newer Hnew_g2cs2 Hg2g') /=.
  (* newer_than_cnf g' cs3 *)
  move: (mk_env_bexp_newer_res H2 H4) => Hnew_g0l.
  move: (newer_than_lit_le_newer Hnew_g0l Hg0g2) => {Hnew_g0l} Hnew_g2l.
  move: (mk_env_exp_newer_res H6 Hnew_g0m0 Hg0tt) => Hnew_g1ls.
  move: (newer_than_lits_le_newer Hnew_g1ls Hg1g2) => {Hnew_g1ls} Hnew_g2ls.
  move: (mk_env_exp_newer_res H5 Hnew_g1m1 Hg1tt) => Hnew_g2ls0.
  rewrite (mk_env_ite_newer_cnf H7 Hnew_g2l Hnew_g2ls Hnew_g2ls0).
  done.
Qed.

Lemma mk_env_bexp_newer_cnf_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- <- _ Hnew_gm Hnew_gtt. done.
Qed.

Lemma mk_env_bexp_newer_cnf_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- <- _ Hnew_gm Hnew_gtt. done.
Qed.

Lemma mk_env_bexp_newer_cnf_eq :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvEq w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt. rewrite !newer_than_cnf_append.
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => {Hnew_g1cs1} Hnew_g2cs1.
  move: (mk_env_eq_newer_gen Heq) => H_g2og.
  move: (newer_than_cnf_le_newer Hnew_g2cs1 H_g2og) => {Hnew_g2cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (mk_env_exp_newer_gen Henv1) => H_gg1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (newer_than_cnf_le_newer Hnew_g2cs2 H_g2og) => {Hnew_g2cs2} Hnew_ogcs2.
  rewrite Hnew_ogcs2 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_exp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1ls1.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1g2) => {Hnew_g1ls1} Hnew_g2ls1.
  move: (mk_env_exp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2ls2.
  exact: (mk_env_eq_newer_cnf Heq Hnew_g2ls1 Hnew_g2ls2).
Qed.

Lemma mk_env_bexp_newer_cnf_ult :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUlt w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_bexp_newer_cnf_ule :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUle w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_bexp_newer_cnf_ugt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUgt w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_bexp_newer_cnf_uge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUge w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_bexp_newer_cnf_slt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSlt w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_bexp_newer_cnf_sle :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSle w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_bexp_newer_cnf_sgt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSgt w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_bexp_newer_cnf_sge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSge w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_bexp_newer_cnf_uaddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUaddo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_bexp_newer_cnf_usubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUsubo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_bexp_newer_cnf_umulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUmulo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_bexp_newer_cnf_saddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSaddo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_bexp_newer_cnf_ssubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSsubo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_bexp_newer_cnf_smulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSmulo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_bexp_newer_cnf_lneg :
  forall (b : QFBV64.bexp) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvLneg b) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_bexp_newer_cnf_conj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case Hconj: (mk_env_conj E2 g2 lr1 lr2)=> [[[oE og] ocs] olr].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt. rewrite !newer_than_cnf_append.
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (mk_env_bexp_newer_gen Henv2) => H_g1g2.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => {Hnew_g1cs1} Hnew_g2cs1.
  move: (mk_env_conj_newer_gen Hconj) => H_g2og.
  move: (newer_than_cnf_le_newer Hnew_g2cs1 H_g2og) => {Hnew_g2cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og cs2 *)
  move: (mk_env_bexp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (mk_env_bexp_newer_gen Henv1) => H_gg1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (newer_than_cnf_le_newer Hnew_g2cs2 H_g2og) => {Hnew_g2cs2} Hnew_ogcs2.
  rewrite Hnew_ogcs2 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_bexp_newer_res Henv1 Hnew_gtt) => Hnew_g1lr1.
  move: (newer_than_lit_le_newer Hnew_g1lr1 H_g1g2) => {Hnew_g1lr1} Hnew_g2lr1.
  move: (mk_env_bexp_newer_res Henv2 Hnew_g1tt) => Hnew_g2lr2.
  exact: (mk_env_conj_newer_cnf Hconj Hnew_g2lr1 Hnew_g2lr2).
Qed.

Lemma mk_env_bexp_newer_cnf_disj :
  forall (b b0 : QFBV64.bexp) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvDisj b b0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_cnf g' cs.
Proof.
Admitted.

Corollary mk_env_exp_newer_cnf :
  forall w (e : QFBV64.exp w) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    newer_than_cnf g' cs
  with
    mk_env_bexp_newer_cnf :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_cnf g' cs.
Proof.
  (* mk_env_exp_newer_cnf *)
  move=> w [] {w}.
  - exact: mk_env_exp_newer_cnf_var.
  - exact: mk_env_exp_newer_cnf_const.
  - exact: mk_env_exp_newer_cnf_not.
  - exact: mk_env_exp_newer_cnf_and.
  - exact: mk_env_exp_newer_cnf_or.
  - exact: mk_env_exp_newer_cnf_xor.
  - exact: mk_env_exp_newer_cnf_neg.
  - exact: mk_env_exp_newer_cnf_add.
  - exact: mk_env_exp_newer_cnf_sub.
  - exact: mk_env_exp_newer_cnf_mul.
  - exact: mk_env_exp_newer_cnf_mod.
  - exact: mk_env_exp_newer_cnf_srem.
  - exact: mk_env_exp_newer_cnf_smod.
  - exact: mk_env_exp_newer_cnf_shl.
  - exact: mk_env_exp_newer_cnf_lshr.
  - exact: mk_env_exp_newer_cnf_ashr.
  - exact: mk_env_exp_newer_cnf_concat.
  - exact: mk_env_exp_newer_cnf_extract.
  - exact: mk_env_exp_newer_cnf_slice.
  - exact: mk_env_exp_newer_cnf_high.
  - exact: mk_env_exp_newer_cnf_low.
  - exact: mk_env_exp_newer_cnf_zeroextend.
  - exact: mk_env_exp_newer_cnf_signextend.
  - move=> w c e1 e2.
    move: (mk_env_bexp_newer_cnf c)
            (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IHc IH1 IH2.
    exact: (mk_env_exp_newer_cnf_ite IHc IH1 IH2).
  (* mk_env_bexp_newer_cnf *)
  case.
  - exact: mk_env_bexp_newer_cnf_false.
  - exact: mk_env_bexp_newer_cnf_true.
  - move=> w e1 e2.
    move: (mk_env_exp_newer_cnf _ e1) (mk_env_exp_newer_cnf _ e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_cnf_eq IH1 IH2).
  - exact: mk_env_bexp_newer_cnf_ult.
  - exact: mk_env_bexp_newer_cnf_ule.
  - exact: mk_env_bexp_newer_cnf_ugt.
  - exact: mk_env_bexp_newer_cnf_uge.
  - exact: mk_env_bexp_newer_cnf_slt.
  - exact: mk_env_bexp_newer_cnf_sle.
  - exact: mk_env_bexp_newer_cnf_sgt.
  - exact: mk_env_bexp_newer_cnf_sge.
  - exact: mk_env_bexp_newer_cnf_uaddo.
  - exact: mk_env_bexp_newer_cnf_usubo.
  - exact: mk_env_bexp_newer_cnf_umulo.
  - exact: mk_env_bexp_newer_cnf_saddo.
  - exact: mk_env_bexp_newer_cnf_ssubo.
  - exact: mk_env_bexp_newer_cnf_smulo.
  - exact: mk_env_bexp_newer_cnf_lneg.
  - move=> e1 e2.
    move: (mk_env_bexp_newer_cnf e1) (mk_env_bexp_newer_cnf e2) => IH1 IH2.
    exact: (mk_env_bexp_newer_cnf_conj IH1 IH2).
  - exact: mk_env_bexp_newer_cnf_disj.
Qed.

(* = mk_env_exp_consistent and mk_env_bexp_consistent = *)

Lemma mk_env_exp_consistent_var :
  forall (t : VarOrder.t) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : wordsize.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvVar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case Hfind: (VM.find v m).
  - case=> <- <- _ _ _ Hnew_gm Hcon. assumption.
  - case Henv: (mk_env_var E g (QFBV64.State.acc v s) v) => [[[E_v g_v] cs_v] lrs_v].
    case=> <- <- _ _ _ Hnew_gm Hcon. move=> x. rewrite /consistent1.
    case Hxv: (x == v).
    + rewrite (VM.Lemmas.find_add_eq _ _ Hxv). rewrite (eqP Hxv).
      exact: (mk_env_var_enc Henv).
    + move/negP: Hxv => Hxv. rewrite (VM.Lemmas.find_add_neq _ _ Hxv).
      move: (Hcon x). rewrite /consistent1.
      case Hfind_xm: (VM.find x m).
      * move=> Henc. move: (Hnew_gm x _ Hfind_xm) => Hnew.
        exact: (env_preserve_enc_bits (mk_env_var_preserve Henv) Hnew Henc).
      * done.
Qed.

Lemma mk_env_exp_consistent_const :
  forall (w0 : nat) (b : BITS w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConst w0 b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w bs m s E g m' E' g' cs lrs /=. case=> <- <- _ _ _ Hnew_gm Hcon.
  assumption.
Qed.

Lemma mk_env_exp_consistent_not :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNot w0 e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_and :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAnd w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_or :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvOr w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_xor :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvXor w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_neg :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNeg w0 e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_add :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAdd w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_sub :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSub w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_mul :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMul w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_mod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_srem :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSrem w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_smod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSmod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_shl :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvShl w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_lshr :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvLshr w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_ashr :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAshr w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_concat :
  forall (w1 w2 : nat) (e : QFBV64.exp w1) (e0 : QFBV64.exp w2)
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : (w2 + w1).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConcat w1 w2 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_extract :
  forall (w0 i j : nat) (e : QFBV64.exp (j + (i - j + 1) + (w0 - i - 1)))
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf)
         (lrs : (i - j + 1).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvExtract w0 i j e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_slice :
  forall (w1 w2 w3 : nat) (e : QFBV64.exp (w3 + w2 + w1))
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_high :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh)) (m : vm)
         (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvHigh wh wl e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_low :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh)) (m : vm)
         (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : wl.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvLow wh wl e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_zeroextend :
  forall (w0 n : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : (w0 + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvZeroExtend w0 n e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_signextend :
  forall (w0 n : nat) (e : QFBV64.exp w0.+1) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : (w0.+1 + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSignExtend w0 n e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_ite :
  forall (w : nat) (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (e0 : QFBV64.exp w),
        (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : w.-tuple literal),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
            newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
        forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g (QFBV64.bvIte w b e e0) = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  move: (mk_env_bexp_newer_vm H2 H3) => Hnew_g0m0.
  move: (mk_env_exp_newer_vm H6 Hnew_g0m0) => Hnew_g1m1.
  move: (mk_env_exp_newer_vm H5 Hnew_g1m1) => Hnew_g2m'.
  apply: (env_preserve_consistent Hnew_g2m' (mk_env_ite_preserve H7)).
  apply: (H1 _ _ _ _ _ _ _ _ _ H5 Hnew_g1m1).
  apply: (H0 _ _ _ _ _ _ _ _ _ H6 Hnew_g0m0).
  exact: (H _ _ _ _ _ _ _ _ _ H2 H3 H4).
Qed.

Lemma mk_env_bexp_consistent_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> <- <- _ _ _. move=> _ H; exact: H.
Qed.

Lemma mk_env_bexp_consistent_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> <- <- _ _ _. move=> _ H; exact: H.
Qed.

Lemma mk_env_bexp_consistent_eq :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvEq w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_eq_preserve Heq)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_ult :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUlt w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_bexp_consistent_ule :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUle w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_bexp_consistent_ugt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUgt w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_bexp_consistent_uge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUge w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_bexp_consistent_slt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSlt w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_bexp_consistent_sle :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSle w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_bexp_consistent_sgt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSgt w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_bexp_consistent_sge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSge w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_bexp_consistent_uaddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUaddo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_bexp_consistent_usubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUsubo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_bexp_consistent_umulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUmulo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_bexp_consistent_saddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSaddo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_bexp_consistent_ssubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSsubo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_bexp_consistent_smulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSmulo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_bexp_consistent_lneg :
  forall (b : QFBV64.bexp) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvLneg b) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_bexp_consistent_conj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case Hconj: (mk_env_conj E2 g2 lr1 lr2)=> [[[oE og] ocs] olr].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_bexp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_bexp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_conj_preserve Hconj)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  apply: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew). exact: Hcon.
Qed.

Lemma mk_env_bexp_consistent_disj :
  forall (b b0 : QFBV64.bexp) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvDisj b b0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Corollary mk_env_exp_consistent :
  forall w (e : QFBV64.exp w) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    consistent m E s -> consistent m' E' s
  with
    mk_env_bexp_consistent :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        consistent m E s ->
        consistent m' E' s.
Proof.
  (* mk_env_exp_consistent *)
  move=> w [] {w}.
  - exact: mk_env_exp_consistent_var.
  - exact: mk_env_exp_consistent_const.
  - exact: mk_env_exp_consistent_not.
  - exact: mk_env_exp_consistent_and.
  - exact: mk_env_exp_consistent_or.
  - exact: mk_env_exp_consistent_xor.
  - exact: mk_env_exp_consistent_neg.
  - exact: mk_env_exp_consistent_add.
  - exact: mk_env_exp_consistent_sub.
  - exact: mk_env_exp_consistent_mul.
  - exact: mk_env_exp_consistent_mod.
  - exact: mk_env_exp_consistent_srem.
  - exact: mk_env_exp_consistent_smod.
  - exact: mk_env_exp_consistent_shl.
  - exact: mk_env_exp_consistent_lshr.
  - exact: mk_env_exp_consistent_ashr.
  - exact: mk_env_exp_consistent_concat.
  - exact: mk_env_exp_consistent_extract.
  - exact: mk_env_exp_consistent_slice.
  - exact: mk_env_exp_consistent_high.
  - exact: mk_env_exp_consistent_low.
  - exact: mk_env_exp_consistent_zeroextend.
  - exact: mk_env_exp_consistent_signextend.
  - move=> w c e1 e2.
    move: (mk_env_bexp_consistent c)
            (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => IHc IH1 IH2.
    exact: (mk_env_exp_consistent_ite IHc IH1 IH2).
  (* mk_env_bexp_consistent *)
  case.
  - exact: mk_env_bexp_consistent_false.
  - exact: mk_env_bexp_consistent_true.
  - move=> w e1 e2.
    move: (mk_env_exp_consistent _ e1) (mk_env_exp_consistent _ e2) => IH1 IH2.
    exact: (mk_env_bexp_consistent_eq IH1 IH2).
  - exact: mk_env_bexp_consistent_ult.
  - exact: mk_env_bexp_consistent_ule.
  - exact: mk_env_bexp_consistent_ugt.
  - exact: mk_env_bexp_consistent_uge.
  - exact: mk_env_bexp_consistent_slt.
  - exact: mk_env_bexp_consistent_sle.
  - exact: mk_env_bexp_consistent_sgt.
  - exact: mk_env_bexp_consistent_sge.
  - exact: mk_env_bexp_consistent_uaddo.
  - exact: mk_env_bexp_consistent_usubo.
  - exact: mk_env_bexp_consistent_umulo.
  - exact: mk_env_bexp_consistent_saddo.
  - exact: mk_env_bexp_consistent_ssubo.
  - exact: mk_env_bexp_consistent_smulo.
  - exact: mk_env_bexp_consistent_lneg.
  - move=> e1 e2.
    move: (mk_env_bexp_consistent e1) (mk_env_bexp_consistent e2) => IH1 IH2.
    exact: (mk_env_bexp_consistent_conj IH1 IH2).
  - exact: mk_env_bexp_consistent_disj.
Qed.

(* = mk_env_exp_preserve and mk_env_bexp_preserve = *)

Lemma mk_env_exp_preserve_var :
  forall (t : VarOrder.t) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : wordsize.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvVar t) = (m', E', g', cs, lrs) -> env_preserve E E' g.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case Hfind: (VM.find v m).
  - case=> _ <- _ _ _. exact: env_preserve_refl.
  - case Henv: (mk_env_var E g (QFBV64.State.acc v s) v) => [[[E_v g_v] cs_v] lrs_v].
    case=> _ <- _ _ _. exact: (mk_env_var_preserve Henv).
Qed.

Lemma mk_env_exp_preserve_const :
  forall (w0 : nat) (b : BITS w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConst w0 b) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> w bs m s E g m' E' g' cs lrs /=. case=> _ <- _ _ _. exact: env_preserve_refl.
Qed.

Lemma mk_env_exp_preserve_not :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNot w0 e) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_and :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAnd w0 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_or :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvOr w0 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_xor :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvXor w0 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_neg :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNeg w0 e) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_add :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAdd w0 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_sub :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSub w0 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_mul :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMul w0 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_mod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMod w0 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_srem :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSrem w0 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_smod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSmod w0 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_shl :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvShl w0 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_lshr :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvLshr w0 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_ashr :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAshr w0 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_concat :
  forall (w1 w2 : nat) (e : QFBV64.exp w1) (e0 : QFBV64.exp w2)
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : (w2 + w1).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConcat w1 w2 e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_extract :
  forall (w0 i j : nat) (e : QFBV64.exp (j + (i - j + 1) + (w0 - i - 1)))
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf)
         (lrs : (i - j + 1).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvExtract w0 i j e) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_slice :
  forall (w1 w2 w3 : nat) (e : QFBV64.exp (w3 + w2 + w1))
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_high :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh)) (m : vm)
         (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvHigh wh wl e) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_low :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh)) (m : vm)
         (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : wl.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvLow wh wl e) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_zeroextend :
  forall (w0 n : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : (w0 + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvZeroExtend w0 n e) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_signextend :
  forall (w0 n : nat) (e : QFBV64.exp w0.+1) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : (w0.+1 + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSignExtend w0 n e) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_ite :
  forall (w : nat) (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        env_preserve E E' g) ->
    forall (e : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (e0 : QFBV64.exp w),
        (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : w.-tuple literal),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
        forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g (QFBV64.bvIte w b e e0) = (m', E', g', cs, lrs) ->
          env_preserve E E' g.
Proof.
  rewrite /=; intros; dcase_hyps; subst. move: (mk_env_ite_preserve H5) => Hpre_E2E'g2.
  move: (H1 _ _ _ _ _ _ _ _ _ H3) => Hpre_E1E2g1.
  move: (H0 _ _ _ _ _ _ _ _ _ H4) => Hpre_E0E1g0.
  move: (H _ _ _ _ _ _ _ _ _ H2) => Hpre_EE0g.
  move: (mk_env_bexp_newer_gen H2) => Hgg0. move: (mk_env_exp_newer_gen H4) => Hg0g1.
  move: (mk_env_exp_newer_gen H3) => Hg1g2. move: (pos_leb_trans Hgg0 Hg0g1) => Hgg1.
  move: (pos_leb_trans Hgg1 Hg1g2) => Hgg2.
  apply: (env_preserve_trans _ (env_preserve_le Hpre_E2E'g2 Hgg2)).
  apply: (env_preserve_trans _ (env_preserve_le Hpre_E1E2g1 Hgg1)).
  exact: (env_preserve_trans Hpre_EE0g (env_preserve_le Hpre_E0E1g0 Hgg0)).
Qed.

Lemma mk_env_bexp_preserve_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) -> env_preserve E E' g.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ <- _ _ _. exact: env_preserve_refl.
Qed.

Lemma mk_env_bexp_preserve_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) -> env_preserve E E' g.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ <- _ _ _. exact: env_preserve_refl.
Qed.

Lemma mk_env_bexp_preserve_eq :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvEq w e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv2)).
  exact: (mk_env_eq_preserve Heq).
Qed.

Lemma mk_env_bexp_preserve_ult :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUlt w e e0) = (m', E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_bexp_preserve_ule :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUle w e e0) = (m', E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_bexp_preserve_ugt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUgt w e e0) = (m', E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_bexp_preserve_uge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUge w e e0) = (m', E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_bexp_preserve_slt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSlt w e e0) = (m', E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_bexp_preserve_sle :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSle w e e0) = (m', E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_bexp_preserve_sgt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSgt w e e0) = (m', E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_bexp_preserve_sge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSge w e e0) = (m', E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_bexp_preserve_uaddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUaddo w e e0) = (m', E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_bexp_preserve_usubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUsubo w e e0) = (m', E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_bexp_preserve_umulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUmulo w e e0) = (m', E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_bexp_preserve_saddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSaddo w e e0) = (m', E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_bexp_preserve_ssubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSsubo w e e0) = (m', E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_bexp_preserve_smulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSmulo w e e0) = (m', E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_bexp_preserve_lneg :
  forall (b : QFBV64.bexp) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvLneg b) = (m', E', g', cs, lr) -> env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_bexp_preserve_conj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        env_preserve E E' g) ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          env_preserve E E' g) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case Hconj: (mk_env_conj E2 g2 lr1 lr2) => [[[oE og] ocs] olr].
  case => _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_bexp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_bexp_newer_gen Henv2)).
  exact: (mk_env_conj_preserve Hconj).
Qed.

Lemma mk_env_bexp_preserve_disj :
  forall (b b0 : QFBV64.bexp) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvDisj b b0) = (m', E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
Admitted.

Corollary mk_env_exp_preserve :
  forall w (e : QFBV64.exp w) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    env_preserve E E' g
  with
    mk_env_bexp_preserve :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  (* mk_env_exp_preserve *)
  move=> w [] {w}.
  - exact: mk_env_exp_preserve_var.
  - exact: mk_env_exp_preserve_const.
  - exact: mk_env_exp_preserve_not.
  - exact: mk_env_exp_preserve_and.
  - exact: mk_env_exp_preserve_or.
  - exact: mk_env_exp_preserve_xor.
  - exact: mk_env_exp_preserve_neg.
  - exact: mk_env_exp_preserve_add.
  - exact: mk_env_exp_preserve_sub.
  - exact: mk_env_exp_preserve_mul.
  - exact: mk_env_exp_preserve_mod.
  - exact: mk_env_exp_preserve_srem.
  - exact: mk_env_exp_preserve_smod.
  - exact: mk_env_exp_preserve_shl.
  - exact: mk_env_exp_preserve_lshr.
  - exact: mk_env_exp_preserve_ashr.
  - exact: mk_env_exp_preserve_concat.
  - exact: mk_env_exp_preserve_extract.
  - exact: mk_env_exp_preserve_slice.
  - exact: mk_env_exp_preserve_high.
  - exact: mk_env_exp_preserve_low.
  - exact: mk_env_exp_preserve_zeroextend.
  - exact: mk_env_exp_preserve_signextend.
  - move=> w c e1 e2.
    move: (mk_env_bexp_preserve c)
            (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IHc IH1 IH2.
    exact: (mk_env_exp_preserve_ite IHc IH1 IH2).
  (* mk_env_exp_preserve *)
  case.
  - exact: mk_env_bexp_preserve_false.
  - exact: mk_env_bexp_preserve_true.
  - move=> w e1 e2.
    move: (mk_env_exp_preserve _ e1) (mk_env_exp_preserve _ e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_eq IH1 IH2).
  - exact: mk_env_bexp_preserve_ult.
  - exact: mk_env_bexp_preserve_ule.
  - exact: mk_env_bexp_preserve_ugt.
  - exact: mk_env_bexp_preserve_uge.
  - exact: mk_env_bexp_preserve_slt.
  - exact: mk_env_bexp_preserve_sle.
  - exact: mk_env_bexp_preserve_sgt.
  - exact: mk_env_bexp_preserve_sge.
  - exact: mk_env_bexp_preserve_uaddo.
  - exact: mk_env_bexp_preserve_usubo.
  - exact: mk_env_bexp_preserve_umulo.
  - exact: mk_env_bexp_preserve_saddo.
  - exact: mk_env_bexp_preserve_ssubo.
  - exact: mk_env_bexp_preserve_smulo.
  - exact: mk_env_bexp_preserve_lneg.
  - move=> e1 e2.
    move: (mk_env_bexp_preserve e1) (mk_env_bexp_preserve e2) => IH1 IH2.
    exact: (mk_env_bexp_preserve_conj IH1 IH2).
  - exact: mk_env_bexp_preserve_disj.
Qed.

(* = mk_env_exp_sat and mk_env_bexp_sat = *)

Lemma mk_env_exp_sat_var :
  forall (t : VarOrder.t) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : wordsize.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvVar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case Hfind: (VM.find v m).
  - case=> _ <- _ <- _ Hnew_gm Hnew_gtt. done.
  - case Henv: (mk_env_var E g (QFBV64.State.acc v s) v) => [[[E_v g_v] cs_v] lrs_v].
    case=> _ <- _ <- _ Hnew_gm Hnew_gtt. exact: (mk_env_var_sat Henv).
Qed.

Lemma mk_env_exp_sat_const :
  forall (w0 : nat) (b : BITS w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConst w0 b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
  move=> w bs m s E g m' E' g' cs lrs /=. case=> _ <- _ <- _ Hnew_gm Hnew_gtt. done.
Qed.

Lemma mk_env_exp_sat_not :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNot w0 e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_and :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAnd w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_or :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvOr w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_xor :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvXor w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_neg :
  forall (w0 : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvNeg w0 e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_add :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAdd w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_sub :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSub w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_mul :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMul w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_mod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvMod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_srem :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSrem w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_smod :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSmod w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_shl :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvShl w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_lshr :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvLshr w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_ashr :
  forall (w0 : nat) (e e0 : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : w0.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvAshr w0 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_concat :
  forall (w1 w2 : nat) (e : QFBV64.exp w1) (e0 : QFBV64.exp w2)
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : (w2 + w1).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvConcat w1 w2 e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_extract :
  forall (w0 i j : nat) (e : QFBV64.exp (j + (i - j + 1) + (w0 - i - 1)))
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf)
         (lrs : (i - j + 1).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvExtract w0 i j e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_slice :
  forall (w1 w2 w3 : nat) (e : QFBV64.exp (w3 + w2 + w1))
         (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_high :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh)) (m : vm)
         (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : wh.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvHigh wh wl e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_low :
  forall (wh wl : nat) (e : QFBV64.exp (wl + wh)) (m : vm)
         (s : QFBV64.State.t) (E : env) (g : generator) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : wl.-tuple literal),
    mk_env_exp m s E g (QFBV64.bvLow wh wl e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_zeroextend :
  forall (w0 n : nat) (e : QFBV64.exp w0) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : (w0 + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvZeroExtend w0 n e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_signextend :
  forall (w0 n : nat) (e : QFBV64.exp w0.+1) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : (w0.+1 + n).-tuple literal),
    mk_env_exp m s E g (QFBV64.bvSignExtend w0 n e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_ite :
  forall (w : nat) (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
      forall (e0 : QFBV64.exp w),
        (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : w.-tuple literal),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
            newer_than_vm g m ->
            newer_than_lit g lit_tt ->
            interp_cnf E' cs) ->
        forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w.-tuple literal),
          mk_env_exp m s E g (QFBV64.bvIte w b e e0) = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !interp_cnf_append.
  move: (mk_env_bexp_newer_gen H2) => Hgg0.
  move: (mk_env_exp_newer_gen H6) => Hg0g1.
  move: (mk_env_exp_newer_gen H5) => Hg1g2.
  move: (mk_env_ite_newer_gen H7) => Hg2g'.
  move: (mk_env_bexp_newer_vm H2 H3) => Hg0m0.
  move: (mk_env_exp_newer_vm H6 Hg0m0) => Hg1m1.
  move: (mk_env_exp_newer_vm H5 Hg1m1) => Hg2m2.
  move: (newer_than_lit_le_newer H4 Hgg0) => Hg0tt.
  move: (newer_than_lit_le_newer Hg0tt Hg0g1) => Hg1tt.
  (* interp_cnf E' cs0 *)
  move: (mk_env_ite_preserve H7) => Hpre_E2E'g2.
  move: (env_preserve_le Hpre_E2E'g2 Hg1g2) => Hpre_E2E'g1.
  move: (mk_env_exp_preserve H5) => Hpre_E1E2g1.
  move: (env_preserve_trans Hpre_E1E2g1 Hpre_E2E'g1) => Hpre_E1E'g1.
  move: (mk_env_exp_preserve H6) => Hpre_E0E1g0.
  move: (env_preserve_le Hpre_E1E'g1 Hg0g1) => Hpre_E1E'g0.
  move: (env_preserve_trans Hpre_E0E1g0 Hpre_E1E'g0) => Hpre_E0E'g0.
  move: (mk_env_bexp_newer_cnf H2 H3 H4) => Hg0cs0.
  rewrite (@env_preserve_cnf E0 E' g0 cs0 Hpre_E0E'g0 Hg0cs0).
  rewrite (H _ _ _ _ _ _ _ _ _ H2 H3 H4) /=.
  (* interp_cnf E' cs1 *)
  move: (mk_env_exp_newer_cnf H6 Hg0m0 Hg0tt) => Hg1cs1.
  rewrite (@env_preserve_cnf E1 E' g1 cs1 Hpre_E1E'g1 Hg1cs1).
  rewrite (H0 _ _ _ _ _ _ _ _ _ H6 Hg0m0 Hg0tt) /=.
  (* interp_cnf E' cs2 *)
  move: (mk_env_exp_newer_cnf H5 Hg1m1 Hg1tt) => Hg2cs2.
  rewrite (@env_preserve_cnf E2 E' g2 cs2 Hpre_E2E'g2 Hg2cs2).
  rewrite (H1 _ _ _ _ _ _ _ _ _ H5 Hg1m1 Hg1tt) /=.
  (* interp_cnf E' cs3 *)
  move: (pos_leb_trans Hg0g1 Hg1g2) => Hg0g2.
  move: (mk_env_bexp_newer_res H2 H4) => Hg0l.
  move: (newer_than_lit_le_newer Hg0l Hg0g2) => Hg2l.
  move: (mk_env_exp_newer_res H6 Hg0m0 Hg0tt) => Hg1ls.
  move: (newer_than_lits_le_newer Hg1ls Hg1g2) => Hg2ls.
  move: (mk_env_exp_newer_res H5 Hg1m1 Hg1tt) => Hg2ls0.
  rewrite (mk_env_ite_sat H7 Hg2l Hg2ls Hg2ls0).
  done.
Qed.

Lemma mk_env_bexp_sat_false :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvFalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ <- _ <- _ Hnew_gm Hnew_gtt. done.
Qed.

Lemma mk_env_bexp_sat_true :
  forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV64.bvTrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ <- _ <- _ Hnew_gm Hnew_gtt. done.
Qed.

Lemma mk_env_bexp_sat_eq :
  forall (w : nat) (e : QFBV64.exp w),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : w.-tuple literal),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (e0 : QFBV64.exp w),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : w.-tuple literal),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvEq w e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> w e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 ls1 ls2) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hnew_gm Hnew_gtt. rewrite !interp_cnf_append.
  move: (mk_env_exp_preserve Henv2) => Hpre_E1E2g1.
  move: (mk_env_exp_newer_gen Henv1) => H_gg1.
  move: (mk_env_exp_newer_gen Henv2) => H_g1g2.
  move: (mk_env_exp_newer_cnf Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => Hnew_g2cs1.
  move: (mk_env_exp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (mk_env_exp_newer_cnf Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (mk_env_exp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1ls1.
  move: (mk_env_exp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2ls2.
  move: (newer_than_lits_le_newer Hnew_g1ls1 H_g1g2) =>
  {H_g1g2 Hnew_g1ls1} Hnew_g2ls1.
  (* interp_cnf oE cs1 *)
  rewrite (env_preserve_cnf (mk_env_eq_preserve Heq) Hnew_g2cs1).
  rewrite (env_preserve_cnf Hpre_E1E2g1 Hnew_g1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) andTb.
  (* interp_cnf oE cs2 *)
  rewrite (env_preserve_cnf (mk_env_eq_preserve Heq) Hnew_g2cs2).
  rewrite (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) andTb.
  (* interp_cnf oE ocs *)
  exact: (mk_env_eq_sat Heq Hnew_g2ls1 Hnew_g2ls2).
Qed.

Lemma mk_env_bexp_sat_ult :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUlt w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_bexp_sat_ule :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUle w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_bexp_sat_ugt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUgt w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_bexp_sat_uge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUge w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_bexp_sat_slt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSlt w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_bexp_sat_sle :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSle w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_bexp_sat_sgt :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSgt w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_bexp_sat_sge :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSge w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_bexp_sat_uaddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUaddo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_bexp_sat_usubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUsubo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_bexp_sat_umulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvUmulo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_bexp_sat_saddo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSaddo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_bexp_sat_ssubo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSsubo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_bexp_sat_smulo :
  forall (w : nat) (e e0 : QFBV64.exp w) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvSmulo w e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_bexp_sat_lneg :
  forall (b : QFBV64.bexp) (m : vm) (s : QFBV64.State.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvLneg b) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_bexp_sat_conj :
  forall (b : QFBV64.bexp),
    (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
    forall (b0 : QFBV64.bexp),
      (forall (m : vm) (s : QFBV64.State.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs) ->
      forall (m : vm) (s : QFBV64.State.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV64.bvConj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case Hconj: (mk_env_conj E2 g2 lr1 lr2) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hnew_gm Hnew_gtt. rewrite !interp_cnf_append.
  move: (mk_env_bexp_preserve Henv2) => Hpre_E1E2g1.
  move: (mk_env_bexp_newer_gen Henv1) => H_gg1.
  move: (mk_env_bexp_newer_gen Henv2) => H_g1g2.
  move: (mk_env_bexp_newer_cnf Henv1 Hnew_gm Hnew_gtt) => Hnew_g1cs1.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => Hnew_g2cs1.
  move: (mk_env_bexp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => {H_gg1} Hnew_g1tt.
  move: (mk_env_bexp_newer_cnf Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2cs2.
  move: (mk_env_bexp_newer_res Henv1 Hnew_gtt) => Hnew_g1lr1.
  move: (mk_env_bexp_newer_res Henv2 Hnew_g1tt) => Hnew_g2lr2.
  move: (newer_than_lit_le_newer Hnew_g1lr1 H_g1g2) => {H_g1g2 Hnew_g1lr1} Hnew_g2lr1.
  (* interp_cnf E2 cs1 *)
  rewrite (env_preserve_cnf (mk_env_conj_preserve Hconj) Hnew_g2cs1).
  rewrite (env_preserve_cnf Hpre_E1E2g1 Hnew_g1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt) andTb.
  (* interp_cnf E2 cs2 *)
  rewrite (env_preserve_cnf (mk_env_conj_preserve Hconj) Hnew_g2cs2).
  rewrite (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt) andTb.
  (* interp_cnf oE ocs *)
  exact: (mk_env_conj_sat Hconj Hnew_g2lr1 Hnew_g2lr2).
Qed.

Lemma mk_env_bexp_sat_disj :
  forall (b b0 : QFBV64.bexp) (m : vm) (s : QFBV64.State.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV64.bvDisj b b0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> interp_cnf E' cs.
Proof.
Admitted.

Corollary mk_env_exp_sat :
  forall w (e : QFBV64.exp w) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    interp_cnf E' cs
  with
    mk_env_bexp_sat :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        interp_cnf E' cs.
Proof.
  (* mk_env_exp_sat *)
  move=> w [] {w}.
  - exact: mk_env_exp_sat_var.
  - exact: mk_env_exp_sat_const.
  - exact: mk_env_exp_sat_not.
  - exact: mk_env_exp_sat_and.
  - exact: mk_env_exp_sat_or.
  - exact: mk_env_exp_sat_xor.
  - exact: mk_env_exp_sat_neg.
  - exact: mk_env_exp_sat_add.
  - exact: mk_env_exp_sat_sub.
  - exact: mk_env_exp_sat_mul.
  - exact: mk_env_exp_sat_mod.
  - exact: mk_env_exp_sat_srem.
  - exact: mk_env_exp_sat_smod.
  - exact: mk_env_exp_sat_shl.
  - exact: mk_env_exp_sat_lshr.
  - exact: mk_env_exp_sat_ashr.
  - exact: mk_env_exp_sat_concat.
  - exact: mk_env_exp_sat_extract.
  - exact: mk_env_exp_sat_slice.
  - exact: mk_env_exp_sat_high.
  - exact: mk_env_exp_sat_low.
  - exact: mk_env_exp_sat_zeroextend.
  - exact: mk_env_exp_sat_signextend.
  - move=> w c e1 e2.
    move: (mk_env_bexp_sat c)
            (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IHc IH1 IH2.
    exact: (mk_env_exp_sat_ite IHc IH1 IH2).
  (* mk_env_exp_sat *)
  case.
  - exact: mk_env_bexp_sat_false.
  - exact: mk_env_bexp_sat_true.
  - move=> w e1 e2.
    move: (mk_env_exp_sat _ e1) (mk_env_exp_sat _ e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_eq IH1 IH2).
  - exact: mk_env_bexp_sat_ult.
  - exact: mk_env_bexp_sat_ule.
  - exact: mk_env_bexp_sat_ugt.
  - exact: mk_env_bexp_sat_uge.
  - exact: mk_env_bexp_sat_slt.
  - exact: mk_env_bexp_sat_sle.
  - exact: mk_env_bexp_sat_sgt.
  - exact: mk_env_bexp_sat_sge.
  - exact: mk_env_bexp_sat_uaddo.
  - exact: mk_env_bexp_sat_usubo.
  - exact: mk_env_bexp_sat_umulo.
  - exact: mk_env_bexp_sat_saddo.
  - exact: mk_env_bexp_sat_ssubo.
  - exact: mk_env_bexp_sat_smulo.
  - exact: mk_env_bexp_sat_lneg.
  - move=> e1 e2.
    move: (mk_env_bexp_sat e1) (mk_env_bexp_sat e2) => IH1 IH2.
    exact: (mk_env_bexp_sat_conj IH1 IH2).
  - exact: mk_env_bexp_sat_disj.
Qed.



(* ===== mk_env ===== *)

Definition init_vm := VM.empty (wordsize.-tuple literal).
Definition init_gen := (var_tt + 1)%positive.
Definition init_env : env := fun _ => true.

Lemma init_newer_than_vm :
  newer_than_vm init_gen init_vm.
Proof.
  done.
Qed.

Lemma init_newer_than_tt :
  newer_than_lit init_gen lit_tt.
Proof.
  done.
Qed.

Lemma init_tt :
  interp_lit init_env lit_tt.
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
  case Henv: (mk_env_bexp init_vm s init_env init_gen e) => [[[[m' E'] g'] cs'] lr'].
  move: (mk_env_bexp_is_bit_blast_bexp Henv). rewrite Hbb. case=> Hm Hg Hcs Hlr.
  rewrite Hm. apply: (mk_env_bexp_consistent Henv init_newer_than_vm).
  exact: init_consistent.
Qed.

Lemma mk_env_tt :
  forall s e, interp_lit (mk_env s e) lit_tt.
Proof.
  move=> s e. rewrite /mk_env.
  set m' := mk_env_bexp init_vm s init_env init_gen e.
  have: mk_env_bexp init_vm s init_env init_gen e = m' by reflexivity. move: m'.
  case=> [[[[m' E'] g'] cs'] lr'] Henv.
  rewrite (env_preserve_lit (mk_env_bexp_preserve Henv) init_newer_than_tt).
  exact: init_tt.
Qed.

Lemma mk_env_sat :
  forall s e m g cs lr,
    bit_blast_bexp init_vm init_gen e = (m, g, cs, lr) ->
    interp_cnf (mk_env s e) cs.
Proof.
  move=> s e m g cs lr Hbb. move: (mk_env_tt s e). rewrite /mk_env.
  set m' := mk_env_bexp init_vm s init_env init_gen e.
  have: mk_env_bexp init_vm s init_env init_gen e = m' by reflexivity. move: m'.
  case=> [[[[m' E'] g'] cs'] lr'] Henv. move: (mk_env_bexp_is_bit_blast_bexp Henv).
  rewrite Hbb; case=> _ _ -> _ Htt.
  exact: (mk_env_bexp_sat Henv init_newer_than_vm init_newer_than_tt).
Qed.



(* ===== mk_state ===== *)

Fixpoint lits_as_bits w E : w.-tuple literal -> BITS w :=
  if w is _.+1 then
    fun ls =>
      let (ls_tl, ls_hd) := eta_expand (splitlsb ls) in
      joinlsb (lits_as_bits E ls_tl, interp_lit E ls_hd)
  else
    fun _ =>
      nilB.

Lemma enc_bits_lits_as_bits :
  forall w E (ls : w.-tuple literal),
    enc_bits E ls (lits_as_bits E ls).
Proof.
  elim.
  - done.
  - move=> w IH E. case/tupleP=> [ls_hd ls_tl]. rewrite /= !theadE !beheadCons /=.
    rewrite IH andbT. exact: eqxx.
Qed.

Definition init_state : QFBV64.State.t := fun _ => fromNat 0.

Definition mk_state (E : env) (m : vm) : QFBV64.State.t :=
  (VM.fold (fun v ls s => QFBV64.State.upd v (lits_as_bits E ls) s) m init_state).

Lemma mk_state_find :
  forall E m x ls,
    VM.find x m = Some ls ->
    QFBV64.State.acc x (mk_state E m) = lits_as_bits E ls.
Proof.
  move=> E m.
  apply: (@VM.Lemmas.OP.P.fold_rec
            (wordsize.-tuple literal) (QFBV64.State.t)
            (fun m s =>
               forall x ls,
                 VM.find x m = Some ls ->
                 QFBV64.State.acc x s = lits_as_bits E ls)
            (fun v ls s => QFBV64.State.upd v (lits_as_bits E ls) s)
            init_state
            m).
  - move=> m0 Hempty x ls Hfind. rewrite (VM.Lemmas.Empty_find _ Hempty) in Hfind.
    discriminate.
  - move=> x lsx s m' m'' Hmapsto_xm Hin_xm' Hadd IH. move=> y lsy Hfind_y.
    case Hyx: (y == x).
    + rewrite (QFBV64.State.acc_upd_eq _ _ Hyx). move: (Hadd y).
      rewrite Hfind_y (VM.Lemmas.find_add_eq _ _ Hyx). case=> ->. reflexivity.
    + move/idP/negP: Hyx => Hyx. rewrite (QFBV64.State.acc_upd_neq _ _ Hyx).
      apply: IH. move: (Hadd y). rewrite Hfind_y. move/negP: Hyx => Hyx.
      rewrite (VM.Lemmas.find_add_neq _ _ Hyx). by move=> ->; reflexivity.
Qed.

Lemma mk_state_consistent :
  forall E m, consistent m E (mk_state E m).
Proof.
  move=> E m x. rewrite /consistent1. case Hfind: (VM.find x m); last by trivial.
  rewrite (mk_state_find _ Hfind). exact: enc_bits_lits_as_bits.
Qed.



(* ===== Soundness and completeness ===== *)

Lemma valid_implies_unsat :
  forall premises goal,
    (forall E, ~~ interp_cnf E (add_prelude premises) || interp_lit E goal) ->
    ~ (sat (add_prelude ([neg_lit goal]::premises))).
Proof.
  move=> premises goal H1 [E H2]. move: (H1 E) => {H1} H1.
  rewrite add_prelude_cons in H2. move/andP: H2 => [H2 H3].
  move/orP: H1. case => H1.
  - move/negP: H1. apply. exact: H3.
  - rewrite add_prelude_expand in H2. move/andP: H2 => [_ H2].
    rewrite /= interp_lit_neg_lit in H2. move/negP: H2; apply.
    exact: H1.
Qed.

Lemma unsat_implies_valid :
  forall premises goal,
    ~ (sat (add_prelude ([neg_lit goal]::premises))) ->
    (forall E, ~~ interp_cnf E (add_prelude premises) || interp_lit E goal).
Proof.
  move=> premises goal H E. case Hgoal: (interp_lit E goal).
  - by rewrite orbT.
  - rewrite orbF. apply/negP => H2. apply: H. exists E.
    rewrite add_prelude_cons H2 andbT.
    rewrite add_prelude_expand /=  interp_lit_neg_lit.
    rewrite Hgoal andbT. exact: (add_prelude_tt H2).
Qed.

Theorem bit_blast_sound :
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
  move: ((bit_blast_bexp_correct Hblast (mk_env_consistent s Hblast) Hprelude)).
  rewrite /enc_bit. move=> /eqP <-.
  rewrite Hprelude /= in Hsat. exact: Hsat.
Qed.

Theorem bit_blast_complete :
  forall (e : QFBV64.bexp) m' g' cs lr,
    bit_blast_bexp init_vm init_gen e = (m', g', cs, lr) ->
    QFBV64.valid e ->
    ~ (sat (add_prelude ([neg_lit lr]::cs))).
Proof.
  move=> e m' g' cs lr Hblast He.
  move=> [E Hcs]. move: (He (mk_state E m')) => {He} He.
  rewrite add_prelude_cons in Hcs. move/andP: Hcs => [Hlr Hcs].
  rewrite add_prelude_expand in Hlr. move/andP: Hlr => [Htt Hlr].
  rewrite /= interp_lit_neg_lit in Hlr.
  move: (bit_blast_bexp_correct Hblast (mk_state_consistent E m') Hcs).
  rewrite /enc_bit => /eqP H. rewrite -H in He.
  rewrite He in Hlr. exact: not_false_is_true.
Qed.
