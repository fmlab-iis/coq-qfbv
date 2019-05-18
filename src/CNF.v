
(*
 * Require the following libraries:
 * - coq-bit from https://github.com/mht208/coq-bits
 * - ssrlib from https://github.com/mht208/coq-ssrlib.git
 *)

From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import Var SsrOrdered ZAriths.
From Bits Require Export bits ssrextra.tuple.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Definition var := positive.

Inductive literal : Set :=
| Pos of var
| Neg of var.

Definition eq_lit l1 l2 :=
  match l1, l2 with
  | Pos n1, Pos n2 => n1 == n2
  | Neg n1, Neg n2 => n1 == n2
  | _, _ => false
  end.

Lemma lit_eqP : forall l1 l2, reflect (l1 = l2) (eq_lit l1 l2).
Proof.
  move=> l1 l2. case H: (eq_lit l1 l2).
  - apply: ReflectT. move: H. elim: l1; elim: l2 => /=.
    + move=> v1 v2 H. move/eqP: H => ->. reflexivity.
    + discriminate.
    + discriminate.
    + move=> v1 v2 H. move/eqP: H => ->. reflexivity.
  - apply: ReflectF. move: H. elim: l1; elim: l2 => /=.
    + move=> v1 v2 H1 H2. case: H2 => H2. rewrite {}H2 in H1. rewrite eq_refl in H1.
      discriminate.
    + move=> v1 v2 _ H. by inversion H.
    + move=> v1 v2 _ H. by inversion H.
    + move=> v1 v2 H1 H2. case: H2 => H2. rewrite {}H2 in H1. rewrite eq_refl in H1.
      discriminate.
Qed.

Definition lit_eqMixin := EqMixin lit_eqP.
Canonical lit_eqType := Eval hnf in EqType literal lit_eqMixin.

Definition var_tt := 1%positive.
Definition lit_tt : literal := Pos var_tt.
Definition lit_ff : literal := Neg var_tt.
Definition var_of_lit l :=
  match l with
  | Pos v => v
  | Neg v => v
  end.

Definition neg_lit lit :=
  match lit with
  | Pos v => Neg v
  | Neg v => Pos v
  end.

Definition clause : Set := list literal.

Definition cnf : Set := list clause.

Definition env : Set := var -> bool.

Fixpoint lits_as_cnf (ls : list literal) :=
  match ls with
  | [] => []
  | hd::tl => [hd]::(lits_as_cnf tl)
  end.

Definition tuple_as_cnf w (ls : w.-tuple literal) :=
  lits_as_cnf (tval ls).

Definition interp_literal (E : env) (l : literal) : bool :=
  match l with
  | Pos v => E v
  | Neg v => negb (E v)
  end.

Fixpoint interp_clause (E : env) (c : clause) : bool :=
  match c with
  | [] => false
  | hd::[] => interp_literal E hd
  | hd::tl => interp_literal E hd || interp_clause E tl
  end.

Fixpoint interp_cnf (E : env) (f : cnf) : bool :=
  match f with
  | [] => true
  | hd::[] => interp_clause E hd
  | hd::tl => interp_clause E hd && interp_cnf E tl
  end.

Definition sat (f : cnf) := exists (E : env), interp_cnf E f.

Definition valid (f : cnf) := forall (E : env), interp_cnf E f.



(* interp_literal *)

Lemma interp_literal_neg_involutive :
  forall E a,
    interp_literal E (neg_lit (neg_lit a)) = interp_literal E a.
Proof.
  move=> E a. rewrite /interp_literal.
  case: a => /=; reflexivity.
Qed.

Lemma interp_literal_neg_lit :
  forall E a,
    interp_literal E (neg_lit a) = ~~ (interp_literal E a).
Proof.
  move=> E a. rewrite /interp_literal.
  case: a => /=; first by reflexivity.
  move=> x. rewrite Bool.negb_involutive. reflexivity.
Qed.

Lemma interp_literal_pos_lit :
  forall E a,
    interp_literal E a = ~~ (interp_literal E (neg_lit a)).
Proof.
  move=> E a. rewrite -interp_literal_neg_lit. rewrite -interp_literal_neg_involutive.
  reflexivity.
Qed.



(* interp_clause *)

Lemma interp_clause_cons :
  forall E l ls, interp_clause E (l::ls) = interp_literal E l || interp_clause E ls.
Proof.
  move=> E l ls. rewrite /interp_clause /= -/(interp_clause E ls). case: ls.
  - rewrite /= Bool.orb_false_r. reflexivity.
  - reflexivity.
Qed.

Lemma interp_clause_append :
  forall E ls1 ls2,
    interp_clause E (ls1++ls2) = interp_clause E ls1 || interp_clause E ls2.
Proof.
  move=> E. elim.
  - move=> ls2 /=. reflexivity.
  - move=> ls1_hd ls1_tl IH ls2. rewrite cat_cons 2!interp_clause_cons.
    case: (interp_literal E ls1_hd) => /=; first by reflexivity. exact: IH.
Qed.

Lemma interp_clause_in :
  forall E ls, interp_clause E ls -> exists l, l \in ls /\ interp_literal E l.
Proof.
  move=> E. elim.
  - move=> H; by elim H.
  - move=> hd tl IH. rewrite interp_clause_cons. case/orP => H.
    + exists hd. rewrite mem_head H. done.
    + move: (IH H) => [l [Hin Hinterp]]. exists l. split; last by assumption.
      rewrite in_cons Hin. rewrite Bool.orb_true_r. done.
Qed.



(* interp_cnf *)

Lemma interp_cnf_cons :
  forall E c cs, interp_cnf E (c::cs) = interp_clause E c && interp_cnf E cs.
Proof.
  move=> E c cs. rewrite /interp_cnf /= -/(interp_cnf E cs). case: cs.
  - rewrite /= Bool.andb_true_r. reflexivity.
  - reflexivity.
Qed.

Lemma interp_cnf_append :
  forall E cs1 cs2,
    interp_cnf E (cs1++cs2) = interp_cnf E cs1 && interp_cnf E cs2.
Proof.
  move=> E. elim.
  - move=> cs2 /=. reflexivity.
  - move=> cs1_hd cs1_tl IH cs2. rewrite cat_cons interp_cnf_cons.
    rewrite (@interp_cnf_cons E cs1_hd cs1_tl).
    rewrite IH. rewrite andbA. reflexivity.
Qed.



(* env_upd *)

Definition env_upd (E : env) (x : var) v := fun y => if x == y then v else E y.

Lemma env_upd_eq :
  forall E x v, (env_upd E x v) x = v.
Proof.
  rewrite /env_upd => E x y. rewrite eqxx. reflexivity.
Qed.

Lemma env_upd_neq :
  forall E x v y, x != y -> (env_upd E x v) y = E y.
Proof.
  rewrite /env_upd => E x v y Hne. rewrite (negPf Hne). reflexivity.
Qed.

Lemma interp_literal_env_upd_eq_pos :
  forall E x v, interp_literal (env_upd E x v) (Pos x) = v.
Proof.
  rewrite /interp_literal /env_upd => E x v. by rewrite (eqxx x).
Qed.

Lemma interp_literal_env_upd_eq_neg :
  forall E x v, interp_literal (env_upd E x v) (Neg x) = ~~ v.
Proof.
  rewrite /interp_literal /env_upd => E x v. by rewrite (eqxx x).
Qed.

Lemma interp_literal_env_upd_neq :
  forall E x v y,
    x != var_of_lit y -> interp_literal (env_upd E x v) y = interp_literal E y.
Proof.
  rewrite /interp_literal /env_upd => E x v y. case: y;
  move=> y /= Hne; rewrite (negPf Hne); reflexivity.
Qed.



(* add_prelude *)

Definition add_prelude cnf := [lit_tt]::cnf.

Lemma add_prelude_tt :
  forall E cs, interp_cnf E (add_prelude cs) -> interp_literal E lit_tt.
Proof.
  move=> E cs /=. case: cs.
  - by apply.
  - move=> cs_hd cs_tl. move/andP => [H _]. exact: H.
Qed.

Lemma add_prelude_ff :
  forall E cs, interp_cnf E (add_prelude cs) -> ~~ interp_literal E lit_ff.
Proof.
  move=> E cs /=. case: cs.
  - rewrite Bool.negb_involutive. by apply.
  - move=> cs_hd cs_tl. move/andP => [H _]. rewrite Bool.negb_involutive. exact: H.
Qed.

Lemma add_prelude_neg_ff :
  forall E cs, interp_cnf E (add_prelude cs) -> interp_literal E (neg_lit lit_ff).
Proof.
  move=> E cs H. rewrite interp_literal_neg_lit. by rewrite (add_prelude_ff H).
Qed.

Lemma add_prelude_empty :
  forall E, interp_cnf E (add_prelude []) = interp_literal E lit_tt.
Proof.
  reflexivity.
Qed.

Lemma add_prelude_singleton :
  forall E c, interp_cnf E (add_prelude [c]) = interp_literal E lit_tt && interp_clause E c.
Proof.
  reflexivity.
Qed.

Lemma add_prelude_cons :
  forall E c cs,
    interp_cnf E (add_prelude (c::cs)) =
    interp_cnf E (add_prelude [c]) && interp_cnf E (add_prelude cs).
Proof.
  move=> E c cs. rewrite /add_prelude /=. case: (E var_tt) => //=. case: cs.
  - rewrite Bool.andb_true_r. reflexivity.
  - move=> cs_hd cs_tl. reflexivity.
Qed.

Lemma add_prelude_expand :
  forall E cs, interp_cnf E (add_prelude cs) = interp_literal E lit_tt && interp_cnf E cs.
Proof.
  move=> E. elim.
  - rewrite /=. rewrite andbT. reflexivity.
  - move=> c cs IH. rewrite add_prelude_cons. rewrite (interp_cnf_cons E c cs).
    rewrite IH. rewrite add_prelude_singleton. by case: (interp_literal E lit_tt).
Qed.

Lemma add_prelude_idem :
  forall E cs,
    interp_cnf E (add_prelude (add_prelude cs)) = interp_cnf E (add_prelude cs).
Proof.
  move=> E cs /=. case: (E var_tt); first by reflexivity.
  by case: cs.
Qed.

Lemma add_prelude_append :
  forall E cs1 cs2,
    interp_cnf E (add_prelude (cs1++cs2)) =
    interp_cnf E (add_prelude cs1) && interp_cnf E (add_prelude cs2).
Proof.
  move=> E. elim.
  - move=> cs2. rewrite cat0s. rewrite add_prelude_empty.
    rewrite -{1}(add_prelude_idem). rewrite {1}/add_prelude. reflexivity.
  - move=> cs1_hd cs1_tl IH cs2. rewrite cat_cons {1}add_prelude_cons.
    rewrite (add_prelude_cons E cs1_hd cs1_tl).
    case: (interp_cnf E (add_prelude [cs1_hd])); last by done.
    rewrite 2!Bool.andb_true_l. exact: IH.
Qed.



(* lits_equiv *)

Fixpoint lits_equiv E ls1 ls2 :=
  match ls1, ls2 with
  | [], [] => true
  | hd1::tl1, hd2::tl2 =>
    (interp_literal E hd1 == interp_literal E hd2) && lits_equiv E tl1 tl2
  | _, _ => false
  end.



(* Relation between literals and bit-vectors. *)

Definition enc_bit E l b : bool := interp_literal E l == b.

Fixpoint enc_bits E w : w.-tuple literal -> BITS w -> bool :=
  if w is _.+1 then
    fun ls bv =>
      let (ls_tl, ls_hd) := eta_expand (splitlsb ls) in
      let (bv_tl, bv_hd) := eta_expand (splitlsb bv) in
      enc_bit E ls_hd bv_hd && enc_bits E ls_tl bv_tl
  else
    fun _ _ => true.

Lemma enc_bit_change_lit :
  forall E b l1 l2,
    interp_literal E l1 = interp_literal E l2 ->
    enc_bit E l1 b ->
    enc_bit E l2 b.
Proof.
  move=> E b l1 l2 H. rewrite /enc_bit H. by apply.
Qed.

Lemma enc_bit_eq_bit :
  forall E b1 b2 l1 l2,
    interp_literal E l1 = interp_literal E l2 ->
    enc_bit E l1 b1 -> enc_bit E l2 b2 ->
    b1 = b2.
Proof.
  move=> E b1 b2 l1 l2. rewrite /enc_bit. move=> -> /eqP -> /eqP. by apply.
Qed.

Lemma enc_bit_eq_lit :
  forall E b1 b2 l1 l2,
    b1 = b2 ->
    enc_bit E l1 b1 -> enc_bit E l2 b2 ->
    interp_literal E l1 = interp_literal E l2.
Proof.
  move=> E b1 b2 l1 l2. rewrite /enc_bit. move=> -> /eqP -> /eqP ->. reflexivity.
Qed.

Lemma add_prelude_enc_bit_tt :
  forall E cs, interp_cnf E (add_prelude cs) -> enc_bit E lit_tt true.
Proof.
  rewrite /enc_bit => E cs H. apply/eqP. exact: (add_prelude_tt H).
Qed.

Lemma add_prelude_enc_bit_true :
  forall E cs b,
    interp_cnf E (add_prelude cs) -> enc_bit E lit_tt b = b.
Proof.
  rewrite /enc_bit => E cs b Hcs. rewrite (add_prelude_tt Hcs). done.
Qed.

Lemma add_prelude_enc_bit_ff :
  forall E cs, interp_cnf E (add_prelude cs) -> enc_bit E lit_ff false.
Proof.
  rewrite /enc_bit => E cs H. move/negPf: (add_prelude_ff H). move/eqP. by apply.
Qed.

Lemma add_prelude_enc_bit_is_not_true :
  forall E cs b, interp_cnf E (add_prelude cs) -> enc_bit E lit_ff b = ~~ b.
Proof.
  rewrite /enc_bit => E cs b Hcs. rewrite (negPf (add_prelude_ff Hcs)). done.
Qed.

Lemma add_prelude_enc_bit_is_false :
  forall E cs b,
    interp_cnf E (add_prelude cs) -> (enc_bit E lit_ff b) = (b == false).
Proof.
  rewrite /enc_bit => E cs b Hcs. rewrite (negPf (add_prelude_ff Hcs)). done.
Qed.

Lemma enc_bits_cons :
  forall E w ls_hd (ls_tl : w.-tuple literal) bv_hd (bv_tl : BITS w),
    enc_bits E (cons_tuple ls_hd ls_tl) (cons_tuple bv_hd bv_tl) =
    (enc_bit E ls_hd bv_hd && enc_bits E ls_tl bv_tl).
Proof.
  move=> E w ls_hd ls_tl bv_hd bv_tl. rewrite /enc_bits -/enc_bits /=.
  rewrite !theadE !beheadCons. reflexivity.
Qed.

Lemma enc_bits_split :
  forall E w (ls : (w.+1).-tuple literal) (bv : BITS (w.+1)),
    enc_bits E ls bv =
    (enc_bit E (thead ls) (thead bv) &&
             enc_bits E (behead_tuple ls) (behead_tuple bv)).
Proof.
  reflexivity.
Qed.

Lemma enc_bits_change_lits :
  forall w E (bv : BITS w) (ls1 ls2 : w.-tuple literal),
    lits_equiv E ls1 ls2 ->
    enc_bits E ls1 bv ->
    enc_bits E ls2 bv.
Proof.
  elim.
  - done.
  - move=> w IH E. case/tupleP => [bv_hd bv_tl]. case/tupleP => [ls1_hd ls1_tl].
    case/tupleP => [ls2_hd ls2_tl]. rewrite /= !theadE !beheadCons.
    move=> /andP [Heq1 Heq2] /andP [Henc1_hd Henc1_tl].
    rewrite (enc_bit_change_lit (eqP Heq1) Henc1_hd) andTb.
    exact: (IH _ _ _ _ Heq2 Henc1_tl).
Qed.

Lemma enc_bits_thead :
  forall E w (ls : (w.+1).-tuple literal) (bv : BITS (w.+1)),
    enc_bits E ls bv ->
    enc_bit E (thead ls) (thead bv).
Proof.
  move=> E w ls bv. rewrite enc_bits_split. move/andP => [H1 H2]. exact: H1.
Qed.

Lemma enc_bits_behead :
  forall E w (ls : (w.+1).-tuple literal) (bv : BITS (w.+1)),
    enc_bits E ls bv ->
    enc_bits E (behead_tuple ls) (behead_tuple bv).
Proof.
  move=> E w ls bv. rewrite enc_bits_split. move/andP => [H1 H2]. exact: H2.
Qed.

Lemma enc_bits_tuple0 :
  forall E (ls : 0.-tuple literal) (bv : BITS 0),
    enc_bits E ls bv.
Proof.
  done.
Qed.

Lemma enc_bit_copy :
  forall E (l : literal) (b : bool) n,
    enc_bit E l b -> enc_bits E (copy n l) (copy n b).
Proof.
  move=> E l b. elim.
  - done.
  - move=> n IH Henc_hd. rewrite /copy 2!nseqCons /=.
    rewrite !theadE !beheadCons. rewrite Henc_hd (IH Henc_hd). done.
Qed.

Lemma enc_bits_val_eq :
  forall E w (ls1 ls2 : w.-tuple literal) (bv1 bv2 : BITS w),
    enc_bits E ls1 bv1 ->
    val ls1 = val ls2 ->
    val bv1 = val bv2 ->
    enc_bits E ls2 bv2.
Proof.
  move=> E. elim.
  - move=> ls1 ls2 bv1 bv2 Henc1 Heq1 Heq2. exact: enc_bits_tuple0.
  - move=> w IH. case/tupleP => ls1_hd ls1_tl. case/tupleP => ls2_hd ls2_tl.
    case/tupleP => bv1_hd bv1_tl. case/tupleP => bv2_hd bv2_tl.
    rewrite /= !theadE !beheadCons.
    move=> /andP [Henc_hd Henc_tl] [] Hlseq_hd Hlseq_tl [] Hbveq_hd Hbveq_tl.
    rewrite -Hlseq_hd -Hbveq_hd Henc_hd andTb.
    exact: (IH ls1_tl ls2_tl bv1_tl bv2_tl Henc_tl Hlseq_tl Hbveq_tl).
Qed.

Lemma enc_bits_splitlsb :
  forall w (bs : BITS (w.+1)) E (ls : (w.+1).-tuple literal),
    enc_bits E ls bs =
    enc_bit E (splitlsb ls).2 (spec.splitlsb bs).2 &&
            enc_bits E (splitlsb ls).1 (spec.splitlsb bs).1.
Proof.
  move=> w. case/tupleP => bs_hd bs_tl. move=> E. case/tupleP => ls_hd ls_tl.
  rewrite /spec.splitlsb /splitlsb /=. rewrite !theadE !beheadCons. reflexivity.
Qed.

Corollary enc_bits_splitlsb_lsb :
  forall w (bs : BITS (w.+1)) E (ls : (w.+1).-tuple literal),
    enc_bits E ls bs ->
    enc_bit E (splitlsb ls).2 (spec.splitlsb bs).2.
Proof.
  move=> w bs E ls. rewrite enc_bits_splitlsb. move/andP => [H1 H2]; assumption.
Qed.

Corollary enc_bits_splitlsb_res :
  forall w (bs : BITS (w.+1)) E (ls : (w.+1).-tuple literal),
    enc_bits E ls bs ->
    enc_bits E (splitlsb ls).1 (spec.splitlsb bs).1.
Proof.
  move=> w bs E ls. rewrite enc_bits_splitlsb. move/andP => [H1 H2]; assumption.
Qed.

Lemma enc_bits_joinlsb :
  forall w bs_hd (bs_tl : BITS w) E ls_hd (ls_tl : w.-tuple literal),
    enc_bits E (joinlsb (ls_tl, ls_hd)) (spec.joinlsb (bs_tl, bs_hd)) =
    (enc_bit E ls_hd bs_hd && enc_bits E ls_tl bs_tl).
Proof.
  move=> w bs_hd bs_tl E ls_hd ls_tl. rewrite /joinlsb /=.
  rewrite !theadE !beheadCons. reflexivity.
Qed.

Lemma enc_bits_droplsb :
  forall w (bs : BITS (w.+1)) E (ls : (w.+1).-tuple literal),
    enc_bits E ls bs ->
    enc_bits E (droplsb ls) (spec.droplsb bs).
Proof.
  move=> w bs E ls Henc. rewrite /droplsb /spec.droplsb.
  by apply: enc_bits_splitlsb_res.
Qed.

Lemma enc_bits_splitmsb :
  forall w (bs : BITS (w.+1)) E (ls : (w.+1).-tuple literal),
    enc_bits E ls bs =
    (enc_bit E (splitmsb ls).1 (spec.splitmsb bs).1 &&
             enc_bits E (splitmsb ls).2 (spec.splitmsb bs).2).
Proof.
  elim.
  - move=> bs E ls /=. reflexivity.
  - move=> w IH. case/tupleP => [bs_hd bs_tl]. move=> E.
    case/tupleP => [ls_hd ls_tl]. rewrite /=. rewrite !beheadCons !theadE.
    case Hlsplit: (splitmsb ls_tl) => [lc lr].
    case Hbsplit: (spec.splitmsb bs_tl) => [bc br].
    rewrite /joinlsb /=. rewrite !beheadCons !theadE. rewrite -enc_bits_split.
    move: (IH bs_tl E ls_tl). rewrite Hbsplit Hlsplit. move=> -> /=.
    case: (enc_bit E ls_hd bs_hd).
    + reflexivity.
    + rewrite 2!andFb andbF. reflexivity.
Qed.

Corollary enc_bits_splitmsb_msb :
  forall w (bs : BITS (w.+1)) E (ls : (w.+1).-tuple literal),
    enc_bits E ls bs ->
    enc_bit E (splitmsb ls).1 (spec.splitmsb bs).1.
Proof.
  move=> w bs E ls. rewrite enc_bits_splitmsb. move/andP => [H1 H2]; assumption.
Qed.

Corollary enc_bits_splitmsb_res :
  forall w (bs : BITS (w.+1)) E (ls : (w.+1).-tuple literal),
    enc_bits E ls bs ->
    enc_bits E (splitmsb ls).2 (spec.splitmsb bs).2.
Proof.
  move=> w bs E ls. rewrite enc_bits_splitmsb. move/andP => [H1 H2]; assumption.
Qed.

Lemma enc_bits_joinmsb :
  forall w bs_hd (bs_tl : BITS w) E ls_hd (ls_tl : w.-tuple literal),
    enc_bits E (joinmsb (ls_hd, ls_tl)) (spec.joinmsb (bs_hd, bs_tl)) =
    (enc_bit E ls_hd bs_hd && enc_bits E ls_tl bs_tl).
Proof.
  elim.
  - done.
  - move=> w IH bs_hd1. case/tupleP => [bs_hd2 bs_tl] E ls_hd1.
    case/tupleP => [ls_hd2 ls_tl].
    rewrite (lock enc_bit) (lock enc_bits) /= -!lock.
    rewrite !beheadCons !theadCons.
    rewrite /joinlsb enc_bits_cons (lock enc_bits) /= -!lock.
    rewrite IH /=. rewrite !theadE !beheadCons.
    rewrite Bool.andb_assoc.
    rewrite (Bool.andb_comm (enc_bit E ls_hd2 bs_hd2) (enc_bit E ls_hd1 bs_hd1)).
    rewrite -Bool.andb_assoc.
    reflexivity.
Qed.

Lemma enc_bits_dropmsb :
  forall w (bs : BITS (w.+1)) E (ls : (w.+1).-tuple literal),
    enc_bits E ls bs ->
    enc_bits E (dropmsb ls) (spec.dropmsb bs).
Proof.
  move=> w bs E ls Henc. rewrite /dropmsb /spec.dropmsb.
  by apply: enc_bits_splitmsb_res.
Qed.

Lemma enc_bit_env_upd_updated :
  forall E b l x y,
    x != var_of_lit b ->
    enc_bit (env_upd E x y) b l = enc_bit E b l.
Proof.
  rewrite /enc_bit => E b l x y Hne. rewrite (interp_literal_env_upd_neq _ _ Hne).
  reflexivity.
Qed.

Lemma enc_bit_env_upd_original :
  forall E b l x y,
    x != var_of_lit b ->
    enc_bit (env_upd E x y) b l = enc_bit E b l.
Proof.
  rewrite /enc_bit => E b l x y Hne. rewrite (interp_literal_env_upd_neq _ _ Hne).
  reflexivity.
Qed.



(* newer_than_lit and newer_than_lits *)

Definition newer_than_var g v : bool := Pos.ltb v g.

Definition newer_than_lit g l : bool := newer_than_var g (var_of_lit l).

Definition newer_than_lits g ls : bool := List.forallb (newer_than_lit g) ls.

Definition newer_than_cnf g cs : bool := List.forallb (newer_than_lits g) cs.

Lemma newer_than_var_irrefl :
  forall x, ~~ newer_than_var x x.
Proof.
  move=> x. apply/negP => Hnew. rewrite /newer_than_var Pos.ltb_irrefl in Hnew.
  exact: not_false_is_true.
Qed.

Lemma newer_than_var_trans :
  forall x y z, newer_than_var x y -> newer_than_var y z -> newer_than_var x z.
Proof.
  move=> x y z Hxy Hyz. apply/pos_ltP. move/pos_ltP: Hxy=> Hxy.
  move/pos_ltP: Hyz=> Hyz. exact: (Pos.lt_trans _ _ _ Hyz Hxy).
Qed.

Lemma newer_than_var_le_newer :
  forall x y z, newer_than_var x y -> (x <=? z)%positive -> newer_than_var z y.
Proof.
  move=> x y z /pos_ltP Hyx /pos_leP Hxz. apply/pos_ltP.
  exact: (Pos.lt_le_trans _ _ _ Hyx Hxz).
Qed.

Lemma newer_than_var_lt_newer :
  forall x y z, newer_than_var x y -> (x <? z)%positive -> newer_than_var z y.
Proof.
  move=> x y z /pos_ltP Hyx /pos_ltP Hxz. apply/pos_ltP.
  exact: (Pos.lt_trans _ _ _ Hyx Hxz).
Qed.

Lemma newer_than_var_neq :
  forall g l,
    newer_than_var g l ->
    g != l.
Proof.
  move=> g l Hg. apply/negP. rewrite /= => H. rewrite (eqP H) in Hg.
  rewrite /newer_than_var in Hg. rewrite Pos.ltb_irrefl in Hg. by elim Hg.
Qed.

Lemma newer_than_var_add_diag_r :
  forall x y z, newer_than_var x y -> newer_than_var (x + z) y.
Proof.
  rewrite /newer_than_var=> x y z Hnew. apply/pos_ltP.
  move/pos_ltP: Hnew=> Hnew. exact: pos_lt_add_r.
Qed.

Lemma newer_than_lit_irrefl :
  forall x, ~~ newer_than_lit (var_of_lit x) x.
Proof.
  move=> x. exact: newer_than_var_irrefl.
Qed.

Lemma newer_than_lit_trans :
  forall x y z,
    newer_than_lit (var_of_lit x) y -> newer_than_lit (var_of_lit y) z ->
    newer_than_var (var_of_lit x) (var_of_lit z).
Proof.
  move=> x y H Hxy Hyz. exact: (newer_than_var_trans Hxy Hyz).
Qed.

Lemma newer_than_lit_neq :
  forall g l,
    newer_than_lit g l ->
    g != var_of_lit l.
Proof.
  move=> g l Hg. apply: newer_than_var_neq. exact: Hg.
Qed.

Lemma newer_than_lit_add_diag_r :
  forall x y z, newer_than_lit x y -> newer_than_lit (x + z) y.
Proof.
  rewrite /newer_than_lit=> x y z Hnew. exact: newer_than_var_add_diag_r.
Qed.

Lemma newer_than_lit_le_newer :
  forall x y z, newer_than_lit x y -> (x <=? z)%positive -> newer_than_lit z y.
Proof.
  move=> x y z /pos_ltP Hyx /pos_leP Hxz. apply/pos_ltP.
  exact: (Pos.lt_le_trans _ _ _ Hyx Hxz).
Qed.

Lemma newer_than_lit_lt_newer :
  forall x y z, newer_than_lit x y -> (x <? z)%positive -> newer_than_lit z y.
Proof.
  move=> x y z /pos_ltP Hyx /pos_ltP Hxz. apply/pos_ltP.
  exact: (Pos.lt_trans _ _ _ Hyx Hxz).
Qed.

Lemma newer_than_lit_enc_bit_env_upd :
  forall E x v l b,
    newer_than_lit x l ->
    enc_bit (env_upd E x v) l b = enc_bit E l b.
Proof.
  move=> E x v l b Hnew. rewrite /enc_bit.
  move: (newer_than_lit_neq Hnew) => Hneq.
  rewrite (interp_literal_env_upd_neq _ _ Hneq). reflexivity.
Qed.

Lemma newer_than_lits_cons :
  forall g l ls,
    newer_than_lits g (l::ls) = newer_than_lit g l && newer_than_lits g ls.
Proof.
  reflexivity.
Qed.

Lemma newer_than_lits_append :
  forall g ls1 ls2,
    newer_than_lits g (ls1++ls2) = newer_than_lits g ls1 && newer_than_lits g ls2.
Proof.
  move=> g; elim.
  - reflexivity.
  - move=> l ls1 IH ls2. rewrite /=. rewrite (IH ls2). rewrite andbA. reflexivity.
Qed.

Lemma newer_than_lits_neq :
  forall g ls l,
    l \in ls ->
    newer_than_lits g ls ->
     g != (var_of_lit l).
Proof.
  move=> g. elim.
  - done.
  - move=> hd tl IH l Hmem. rewrite newer_than_lits_cons.
    move/andP=> [Hnew_hd Hnew_tl]. rewrite in_cons in Hmem. case/orP: Hmem.
    + move=> /eqP ->. exact: (newer_than_lit_neq Hnew_hd).
    + move=> Hmem. exact: (IH _ Hmem Hnew_tl).
Qed.

Lemma newer_than_lits_add_diag_r :
  forall x ls y, newer_than_lits x ls -> newer_than_lits (x + y) ls.
Proof.
  move=> x ls. elim: ls x.
  - done.
  - move=> ls_hd ls_tl IH x y. rewrite 2!newer_than_lits_cons.
    move/andP=> [Hnewer_hd Hnewer_tl]. rewrite (IH _ _ Hnewer_tl) andbT.
    exact: newer_than_lit_add_diag_r.
Qed.

Lemma newer_than_lits_le_newer :
  forall x ls y, newer_than_lits x ls -> (x <=? y)%positive -> newer_than_lits y ls.
Proof.
  move=> x ls. elim: ls x.
  - done.
  - move=> hd tl IH x y. rewrite 2!newer_than_lits_cons.
    move/andP=> [Hnew_hd Hnew_tl] Hle. rewrite (newer_than_lit_le_newer Hnew_hd Hle).
    rewrite (IH _ _ Hnew_tl Hle). done.
Qed.

Lemma newer_than_lits_lt_newer :
  forall x ls y, newer_than_lits x ls -> (x <? y)%positive -> newer_than_lits y ls.
Proof.
  move=> x ls. elim: ls x.
  - done.
  - move=> hd tl IH x y. rewrite 2!newer_than_lits_cons.
    move/andP=> [Hnew_hd Hnew_tl] Hle. rewrite (newer_than_lit_lt_newer Hnew_hd Hle).
    rewrite (IH _ _ Hnew_tl Hle). done.
Qed.

Lemma newer_than_lits_enc_bits_env_upd :
  forall w E x b (ls : w.-tuple literal) bs,
    newer_than_lits x ls ->
    enc_bits (env_upd E x b) ls bs = enc_bits E ls bs.
Proof.
  elim.
  - done.
  - move=> w IH E x b. case/tupleP=> [ls_hd ls_tl]. case/tupleP=> [bs_hd bs_tl].
    rewrite /= !theadE !beheadCons. move/andP=> [Hnew_hd Hnew_tl].
    rewrite (newer_than_lit_enc_bit_env_upd _ _ _ Hnew_hd).
    rewrite (IH _ _ _ _ _ Hnew_tl). reflexivity.
Qed.

Lemma newer_than_cnf_cons :
  forall g c cs,
    newer_than_cnf g (c::cs) = newer_than_lits g c && newer_than_cnf g cs.
Proof.
  reflexivity.
Qed.

Lemma newer_than_cnf_append :
  forall g cs1 cs2,
    newer_than_cnf g (cs1++cs2) = newer_than_cnf g cs1 && newer_than_cnf g cs2.
Proof.
  move=> g; elim.
  - reflexivity.
  - move=> c cs1 IH cs2. rewrite /=. rewrite (IH cs2). rewrite andbA. reflexivity.
Qed.

Lemma newer_than_cnf_add_diag_r :
  forall x cs y, newer_than_cnf x cs -> newer_than_cnf (x + y) cs.
Proof.
  move=> x cs. elim: cs x.
  - done.
  - move=> cs_hd cs_tl IH x y. rewrite 2!newer_than_cnf_cons.
    move/andP=> [Hnewer_hd Hnewer_tl]. rewrite (IH _ _ Hnewer_tl) andbT.
    exact: newer_than_lits_add_diag_r.
Qed.

Lemma interp_literal_env_upd_newer :
  forall E x v y,
    newer_than_lit x y -> interp_literal (env_upd E x v) y = interp_literal E y.
Proof.
  move=> E x v y Hnewer. apply: interp_literal_env_upd_neq.
  exact: (newer_than_lit_neq Hnewer).
Qed.

Lemma interp_clause_env_upd_newer :
  forall E x v (c : clause),
    newer_than_lits x c ->
    interp_clause (env_upd E x v) c = interp_clause E c.
Proof.
  move=> E x v. elim.
  - reflexivity.
  - move=> l c IH Hnew. rewrite /= in Hnew. move/andP: Hnew=> [Hnew1 Hnew2].
    rewrite 2!interp_clause_cons. rewrite (interp_literal_env_upd_newer _ _ Hnew1).
    rewrite (IH Hnew2). reflexivity.
Qed.

Lemma interp_cnf_env_upd_newer :
  forall E x v (cs : cnf),
    newer_than_cnf x cs ->
    interp_cnf (env_upd E x v) cs = interp_cnf E cs.
Proof.
  move=> E x v. elim.
  - reflexivity.
  - move=> c cs IH Hnew. rewrite /= in Hnew. move/andP: Hnew=> [Hnew1 Hnew2].
    rewrite 2!(interp_cnf_cons _ c cs).
    rewrite (interp_clause_env_upd_newer _ _ Hnew1) (IH Hnew2).
    reflexivity.
Qed.



(* env_preserve *)

Definition env_preserve (E E' : env) g :=
  forall v : var,
    newer_than_var g v ->
    E' v = E v.

Lemma env_preserve_refl : forall E g, env_preserve E E g.
Proof.
  done.
Qed.

Lemma env_preserve_sym :
  forall E1 E2 g, env_preserve E1 E2 g -> env_preserve E2 E1 g.
Proof.
  move=> E1 E2 g H l Hnew. rewrite (H _ Hnew). reflexivity.
Qed.

Lemma env_preserve_trans :
  forall E1 E2 E3 g,
    env_preserve E1 E2 g -> env_preserve E2 E3 g -> env_preserve E1 E3 g.
Proof.
  move=> E1 E2 E3 g H12 H23 l Hnew. rewrite (H23 _ Hnew) (H12 _ Hnew). reflexivity.
Qed.

Lemma env_preserve_literal :
  forall E E' g l,
    env_preserve E E' g ->
    newer_than_lit g l ->
    interp_literal E' l = interp_literal E l.
Proof.
  move=> E E' g l Hpre Hnew. rewrite /interp_literal. case: l Hnew.
  - move=> v Hnew. exact: (Hpre _ Hnew).
  - move=> v Hnew. rewrite (Hpre _ Hnew) /=. reflexivity.
Qed.

Lemma env_preserve_clause :
  forall E E' g c,
    env_preserve E E' g ->
    newer_than_lits g c ->
    interp_clause E' c = interp_clause E c.
Proof.
  move=> E E' g. elim.
  - done.
  - move=> l c IH Hpre Hnew. rewrite 2!interp_clause_cons.
    rewrite newer_than_lits_cons in Hnew. move/andP: Hnew => [Hnew_l Hnew_c].
    rewrite (env_preserve_literal Hpre Hnew_l) (IH Hpre Hnew_c).
    reflexivity.
Qed.

Lemma env_preserve_cnf :
  forall E E' g cs,
    env_preserve E E' g ->
    newer_than_cnf g cs ->
    interp_cnf E' cs = interp_cnf E cs.
Proof.
  move=> E E' g. elim.
  - done.
  - move=> c cs IH Hpre Hnew. rewrite 2!interp_cnf_cons.
    rewrite newer_than_cnf_cons in Hnew. move/andP: Hnew => [Hnew_l Hnew_c].
    rewrite (env_preserve_clause Hpre Hnew_l) (IH Hpre Hnew_c).
    reflexivity.
Qed.

Lemma env_upd_eq_preserve :
  forall E x v,
    env_preserve E (env_upd E x v) x.
Proof.
  move=> E x v l Hnew. rewrite env_upd_neq; first by reflexivity.
  exact: (newer_than_var_neq Hnew).
Qed.

Lemma env_upd_newer_preserve :
  forall E x v y,
    newer_than_var x y ->
    env_preserve E (env_upd E x v) y.
Proof.
  move=> E x v y Hnew_xy l Hnew_yl. apply: env_upd_neq.
  move: (newer_than_var_trans Hnew_xy Hnew_yl) => Hnew.
  exact: (newer_than_var_neq Hnew).
Qed.

Lemma env_preserve_env_upd_succ :
  forall E E' x v,
    env_preserve (env_upd E x v) E' (x + 1) -> env_preserve E E' x.
Proof.
  move=> E E' x v H y Hnew. move: (H y (newer_than_var_add_diag_r 1 Hnew)).
  move=> ->. rewrite env_upd_neq; first by reflexivity.
  exact: newer_than_var_neq.
Qed.
