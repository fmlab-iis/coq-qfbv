
(*
 * Require the following libraries:
 * - coq-bit from https://github.com/mht208/coq-nbits
 * - ssrlib from https://github.com/mht208/coq-ssrlib.git
 *)

From Coq Require Import ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import SsrOrdered ZAriths Seqs Lists Bools FSets.
From nbits Require Export NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Definition bvar := positive.

Inductive literal : Set :=
| Pos of bvar
| Neg of bvar.

Definition eq_lit l1 l2 :=
  match l1, l2 with
  | Pos n1, Pos n2 => n1 == n2
  | Neg n1, Neg n2 => n1 == n2
  | _, _ => false
  end.

Lemma lit_eqP l1 l2 : reflect (l1 = l2) (eq_lit l1 l2).
Proof.
  case H: (eq_lit l1 l2).
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

(* A word is a sequence of literals that represent a bit-vector.
   The LSB is at the head of the literal sequence. *)
Definition word : Set := seq literal.

Definition clause : Set := seq literal.

Definition cnf : Set := seq clause.

Definition env : Set := bvar -> bool.

Definition splitlsl (ls : word) := split_head lit_ff ls.
Definition splitmsl (ls : word) := split_last lit_ff ls.
Definition droplsl (ls : word) : word := (splitlsl ls).2.
Definition dropmsl (ls : word) : word := (splitmsl ls).1.
Definition joinlsl := @cons.
Definition joinmsl := @rcons.
Definition lsl (ls : word) : literal := (splitlsl ls).1.
Definition msl (ls : word) : literal := (splitmsl ls).2.

Fixpoint word_as_cnf (ls : word) :=
  match ls with
  | [::] => [::]
  | hd::tl => [::hd]::(word_as_cnf tl)
  end.

Definition interp_lit (E : env) (l : literal) : bool :=
  match l with
  | Pos v => E v
  | Neg v => negb (E v)
  end.

Definition interp_word (E : env) (ls : word) : bits :=
  map (fun l => interp_lit E l) ls.

Fixpoint interp_clause (E : env) (c : clause) : bool :=
  match c with
  | [::] => false
  | [::hd] => interp_lit E hd
  | hd::tl => interp_lit E hd || interp_clause E tl
  end.

Fixpoint interp_cnf (E : env) (f : cnf) : bool :=
  match f with
  | [::] => true
  | [::hd] => interp_clause E hd
  | hd::tl => interp_clause E hd && interp_cnf E tl
  end.

Definition sat (f : cnf) := exists (E : env), interp_cnf E f.

Definition valid (f : cnf) := forall (E : env), interp_cnf E f.



(* interp_lit *)

Lemma interp_lit_neg_involutive E a :
  interp_lit E (neg_lit (neg_lit a)) = interp_lit E a.
Proof. rewrite /interp_lit. case: a => /=; reflexivity. Qed.

Lemma interp_lit_neg_lit E a : interp_lit E (neg_lit a) = ~~ (interp_lit E a).
Proof.
  rewrite /interp_lit. case: a => /=; first by reflexivity.
  move=> x. rewrite Bool.negb_involutive. reflexivity.
Qed.

Lemma interp_lit_pos_lit E a : interp_lit E a = ~~ (interp_lit E (neg_lit a)).
Proof.
  rewrite -interp_lit_neg_lit. rewrite -interp_lit_neg_involutive. reflexivity.
Qed.



(* interp_word *)

Lemma interp_word_cons E l (ls : word) :
  interp_word E (l::ls) = (interp_lit E l)::(interp_word E ls).
Proof. rewrite /interp_word. rewrite map_cons. reflexivity. Qed.

Lemma interp_word_split E (ls : word) :
  0 < size ls ->
  interp_word E ls = (interp_lit E (lsl ls))::(interp_word E (droplsl ls)).
Proof. by case: ls => [|ls_hd ls_tl] //=. Qed.



(* interp_clause *)

Lemma interp_clause_cons E l ls :
  interp_clause E (l::ls) = interp_lit E l || interp_clause E ls.
Proof.
  rewrite /interp_clause /= -/(interp_clause E ls). case: ls => //=.
  rewrite orbF. reflexivity.
Qed.

Lemma interp_clause_append E ls1 ls2 :
  interp_clause E (ls1++ls2) = interp_clause E ls1 || interp_clause E ls2.
Proof.
  elim: ls1 ls2 => [| ls1_hd ls1_tl IH] ls2 //. rewrite cat_cons 2!interp_clause_cons.
  rewrite (IH ls2). rewrite Bool.orb_assoc. reflexivity.
Qed.

Lemma interp_clause_in E ls :
  interp_clause E ls -> exists l, l \in ls /\ interp_lit E l.
Proof.
  elim: ls => [| hd tl IH] //. rewrite interp_clause_cons. case/orP => H.
  - exists hd. rewrite mem_head H. done.
  - move: (IH H) => [l [Hin Hinterp]]. exists l. split; last by assumption.
    rewrite in_cons Hin. rewrite orbT. reflexivity.
Qed.

Lemma interp_clause_mem E c :
  interp_clause E c -> exists l : literal, (l \in c) && interp_lit E l.
Proof.
  elim: c => [| hd tl IH] //. rewrite interp_clause_cons. case/orP => H.
  - exists hd. by rewrite mem_head H.
  - move: (IH H)=> {H} [l /andP [H1 H2]]. exists l.
      by rewrite in_cons H1 H2 andbT orbT.
Qed.



(* interp_cnf *)

Lemma interp_cnf_cons E c cs :
  interp_cnf E (c::cs) = interp_clause E c && interp_cnf E cs.
Proof.
  rewrite /interp_cnf /= -/(interp_cnf E cs). case: cs => //=.
  rewrite andbT. reflexivity.
Qed.

Lemma interp_cnf_append E cs1 cs2 :
  interp_cnf E (cs1++cs2) = interp_cnf E cs1 && interp_cnf E cs2.
Proof.
  elim: cs1 cs2 => [| cs1_hd cs1_tl IH] cs2 //. rewrite cat_cons interp_cnf_cons.
  rewrite (@interp_cnf_cons E cs1_hd cs1_tl). rewrite IH. rewrite andbA. reflexivity.
Qed.

Lemma interp_cnf_mem E c cs : interp_cnf E cs -> c \in cs -> interp_clause E c.
Proof.
  elim: cs => [|hd tl IH] //. rewrite interp_cnf_cons => /andP [H1 H2].
  rewrite in_cons. case/orP => H.
  - rewrite (eqP H). exact: H1.
  - exact: (IH H2 H).
Qed.



(* env_upd *)

Definition env_upd (E : env) (x : bvar) v := fun y => if x == y then v else E y.

Lemma env_upd_eq E x v : (env_upd E x v) x = v.
Proof. rewrite /env_upd. rewrite eqxx. reflexivity. Qed.

Lemma env_upd_neq E x v y : x != y -> (env_upd E x v) y = E y.
Proof. rewrite /env_upd => Hne. rewrite (negPf Hne). reflexivity. Qed.

Lemma interp_lit_env_upd_eq_pos E x v : interp_lit (env_upd E x v) (Pos x) = v.
Proof. by rewrite /interp_lit /env_upd eqxx. Qed.

Lemma interp_lit_env_upd_eq_neg E x v : interp_lit (env_upd E x v) (Neg x) = ~~ v.
Proof. by rewrite /interp_lit /env_upd eqxx. Qed.

Lemma interp_lit_env_upd_neq E x v y :
  x != var_of_lit y -> interp_lit (env_upd E x v) y = interp_lit E y.
Proof.
  rewrite /interp_lit /env_upd. case: y;
  move=> y /= Hne; rewrite (negPf Hne); reflexivity.
Qed.



(* add_prelude *)

Definition add_prelude cnf := [::lit_tt]::cnf.

Lemma add_prelude_tt E cs : interp_cnf E (add_prelude cs) -> interp_lit E lit_tt.
Proof. case: cs => [| hd tl] //= H. move/andP: H => [H _]. exact: H. Qed.

Lemma add_prelude_ff E cs : interp_cnf E (add_prelude cs) -> ~~ interp_lit E lit_ff.
Proof. rewrite interp_cnf_cons /=. move/andP => [H _]. apply/negPn. exact: H. Qed.

Lemma add_prelude_neg_ff E cs :
  interp_cnf E (add_prelude cs) -> interp_lit E (neg_lit lit_ff).
Proof. move=> H. rewrite interp_lit_neg_lit. by rewrite (add_prelude_ff H). Qed.

Lemma add_prelude_empty E : interp_cnf E (add_prelude [::]) = interp_lit E lit_tt.
Proof. reflexivity. Qed.

Lemma add_prelude_singleton E c :
  interp_cnf E (add_prelude [::c]) = interp_lit E lit_tt && interp_clause E c.
Proof. reflexivity. Qed.

Lemma add_prelude_cons E c cs :
  interp_cnf E (add_prelude (c::cs)) =
  interp_cnf E (add_prelude [::c]) && interp_cnf E (add_prelude cs).
Proof.
  rewrite /add_prelude /=. case: (E var_tt) => //=. case: cs => [| hd tl] //=.
  by rewrite andbT.
Qed.

Lemma add_prelude_expand E cs :
  interp_cnf E (add_prelude cs) = interp_lit E lit_tt && interp_cnf E cs.
Proof. elim: cs => [| c cs IH] //=. by rewrite andbT. Qed.

Lemma add_prelude_idem E cs :
  interp_cnf E (add_prelude (add_prelude cs)) = interp_cnf E (add_prelude cs).
Proof. rewrite /=. case: (E var_tt) => //=. by case: cs. Qed.

Lemma add_prelude_append E cs1 cs2 :
  interp_cnf E (add_prelude (cs1++cs2)) =
  interp_cnf E (add_prelude cs1) && interp_cnf E (add_prelude cs2).
Proof.
  elim: cs1 cs2 => [| cs1_hd cs1_tl IH] cs2.
  - rewrite cat0s add_prelude_empty. rewrite -add_prelude_expand add_prelude_idem.
    reflexivity.
  - rewrite cat_cons {1}add_prelude_cons.
    rewrite IH Bool.andb_assoc -add_prelude_cons. reflexivity.
Qed.



(* word_equiv *)

Fixpoint word_equiv E (ls1 ls2 : word) :=
  match ls1, ls2 with
  | [::], [::] => true
  | hd1::tl1, hd2::tl2 =>
    (interp_lit E hd1 == interp_lit E hd2) && word_equiv E tl1 tl2
  | _, _ => false
  end.

Lemma word_equiv_interp_eq E (ls1 ls2 : word) :
  word_equiv E ls1 ls2 = (interp_word E ls1 == interp_word E ls2).
Proof.
  elim: ls1 ls2 => [| hd1 tl1 IH] [| hd2 tl2] //=. rewrite eqseq_cons IH. reflexivity.
Qed.

Lemma word_equiv_size E ls1 ls2 : word_equiv E ls1 ls2 -> size ls1 = size ls2.
Proof.
  elim: ls1 ls2 => [| hd1 tl1 IH] [| hd2 tl2] //=. move/andP => [_ H].
  rewrite (IH _ H). reflexivity.
Qed.

Lemma word_equiv_cons E l1 ls1 l2 ls2 :
  word_equiv E (l1::ls1) (l2::ls2) =
  (interp_lit E l1 == interp_lit E l2) && word_equiv E ls1 ls2.
Proof. reflexivity. Qed.



(* Relation between literals and bit-vectors. *)

Definition enc_bit E l b : bool := interp_lit E l == b.

Definition enc_bits E (ls : word) (bs : bits) : bool := interp_word E ls == bs.

Lemma enc_bit_change_lit E b l1 l2 :
  interp_lit E l1 = interp_lit E l2 -> enc_bit E l1 b = enc_bit E l2 b.
Proof. move=> H. by rewrite /enc_bit H. Qed.

Lemma enc_bit_not E b l : enc_bit E l b = enc_bit E (neg_lit l) (~~ b).
Proof. rewrite /enc_bit interp_lit_neg_lit neg_eq. reflexivity. Qed.

Lemma enc_bit_eq_bit E b1 b2 l1 l2 :
  interp_lit E l1 = interp_lit E l2 -> enc_bit E l1 b1 -> enc_bit E l2 b2 -> b1 = b2.
Proof. rewrite /enc_bit. move=> -> /eqP -> /eqP. by apply. Qed.

Lemma enc_bit_eq_lit E b1 b2 l1 l2 :
  b1 = b2 -> enc_bit E l1 b1 -> enc_bit E l2 b2 -> interp_lit E l1 = interp_lit E l2.
Proof. rewrite /enc_bit. move=> -> /eqP -> /eqP ->. reflexivity. Qed.

Lemma add_prelude_enc_bit_tt E cs :
  interp_cnf E (add_prelude cs) -> enc_bit E lit_tt true.
Proof. rewrite /enc_bit => H. apply/eqP. exact: (add_prelude_tt H). Qed.

Lemma add_prelude_enc_bit_true E cs b :
  interp_cnf E (add_prelude cs) -> enc_bit E lit_tt b = b.
Proof. rewrite /enc_bit => H. by rewrite (add_prelude_tt H). Qed.

Lemma add_prelude_enc_bit_ff E cs :
  interp_cnf E (add_prelude cs) -> enc_bit E lit_ff false.
Proof. rewrite /enc_bit => H. apply/eqP/negPn. exact: (add_prelude_tt H). Qed.

Lemma add_prelude_enc_bit_is_not_true E cs b :
  interp_cnf E (add_prelude cs) -> enc_bit E lit_ff b = ~~ b.
Proof. rewrite /enc_bit => H. by rewrite (negPf (add_prelude_ff H)). Qed.

Lemma add_prelude_enc_bit_is_false E cs b :
  interp_cnf E (add_prelude cs) -> (enc_bit E lit_ff b) = (b == false).
Proof. move=> H. rewrite (add_prelude_enc_bit_is_not_true _ H). by case: b. Qed.

Lemma enc_bits_nil E : enc_bits E [::] [::].
Proof. reflexivity. Qed.

Lemma enc_bits_nil_l E bs : enc_bits E [::] bs = (bs == [::]).
Proof. rewrite eq_sym. reflexivity. Qed.

Lemma enc_bits_nil_r E ls : enc_bits E ls [::] = (ls == [::]).
Proof. by case: ls. Qed.

Lemma enc_bits_cons E ls_hd (ls_tl : word) bs_hd (bs_tl : bits) :
  enc_bits E (cons ls_hd ls_tl) (cons bs_hd bs_tl) =
  (enc_bit E ls_hd bs_hd && enc_bits E ls_tl bs_tl).
Proof. rewrite /enc_bit /enc_bits /=. rewrite eqseq_cons. reflexivity. Qed.

Lemma enc_bits_split E (ls : word) (bs : bits) :
  interp_lit E lit_tt ->
  enc_bits E ls bs ->
  (enc_bit E (lsl ls) (lsb bs) && enc_bits E (droplsl ls) (droplsb bs)).
Proof.
  case: ls => [|ls_hd ls_tl]; case: bs => [|bs_hd bs_tl] //=.
  rewrite /enc_bits /enc_bit /lsb /droplsb /=. by move=> ->.
Qed.

Lemma enc_bits_split_ss E (ls : word) (bs : bits) :
  interp_lit E lit_tt ->
  size ls = size bs ->
  enc_bits E ls bs =
  (enc_bit E (lsl ls) (lsb bs) && enc_bits E (droplsl ls) (droplsb bs)).
Proof.
  case: ls => [|ls_hd ls_tl]; case: bs => [|bs_hd bs_tl] //=.
  rewrite /enc_bits /enc_bit /lsb /droplsb /=. by move=> ->.
Qed.

Lemma enc_bits_split_nonempty E (ls : word) (bs : bits) :
  0 < size ls -> 0 < size bs ->
  enc_bits E ls bs =
  (enc_bit E (lsl ls) (lsb bs) && enc_bits E (droplsl ls) (droplsb bs)).
Proof. by case: ls => [|ls_hd ls_tl]; case: bs => [|bs_hd bs_tl] //=. Qed.

Lemma enc_bits_change_word E (bs : bits) (ls1 ls2 : word) :
  word_equiv E ls1 ls2 -> enc_bits E ls1 bs = enc_bits E ls2 bs.
Proof.
  elim: bs ls1 ls2 => [| bs_hd bs_tl IH] ls1 ls2 /=.
  - rewrite !enc_bits_nil_r. move=> H; move: (word_equiv_size H) => {H}.
    by case: ls1; case: ls2.
  - case: ls1 => [|hd1 tl1]; case: ls2 => [| hd2 tl2] //=.
    move/andP => [Hhd Htl]. rewrite !enc_bits_cons (IH _ _ Htl).
    rewrite (enc_bit_change_lit _ (eqP Hhd)). reflexivity.
Qed.

Lemma enc_bits_size E ls bs : enc_bits E ls bs -> size ls = size bs.
Proof.
  elim: ls bs => [| ls_hd ls_tl IH] [| bs_hd bs_tl] //=.
  rewrite enc_bits_cons => /andP [Hhd Htl]. rewrite (IH _ Htl). reflexivity.
Qed.

Lemma enc_bits_lsl E (ls : word) (bs : bits) :
  interp_lit E lit_tt ->
  enc_bits E ls bs -> enc_bit E (lsl ls) (lsb bs).
Proof. move=> Htt Henc. move: (enc_bits_split Htt Henc). by case/andP. Qed.

Lemma enc_bits_droplsl E (ls : word) (bs : bits) :
  enc_bits E ls bs -> enc_bits E (droplsl ls) (droplsb bs).
Proof.
  case: ls => [|ls_hd ls_tl]; case: bs => [|bs_hd bs_tl] //=.
  rewrite enc_bits_cons /droplsb /=. by move/andP => [_ H].
Qed.

Lemma enc_bit_copy E (l : literal) (b : bool) n :
    enc_bit E l b -> enc_bits E (copy n l) (copy n b).
Proof. move=> H. elim: n => [| n IHn] //=. by rewrite enc_bits_cons H IHn. Qed.

Lemma enc_bits_splitlsb E (ls : word) (bs : bits) :
  interp_lit E lit_tt ->
  enc_bits E ls bs ->
  enc_bit E (splitlsl ls).1 (splitlsb bs).1 &&
          enc_bits E (splitlsl ls).2 (splitlsb bs).2.
Proof. move=> Htt Henc. exact: (enc_bits_split Htt Henc). Qed.

Lemma enc_bits_splitlsb_ss E (ls : word) (bs : bits) :
  interp_lit E lit_tt ->
  size ls = size bs ->
  enc_bits E ls bs =
  enc_bit E (splitlsl ls).1 (splitlsb bs).1 &&
          enc_bits E (splitlsl ls).2 (splitlsb bs).2.
Proof. move=> Htt Hs. exact: (enc_bits_split_ss Htt Hs). Qed.

Lemma enc_bits_splitlsb_nonempty E (ls : word) (bs : bits) :
  0 < size ls -> 0 < size bs ->
  enc_bits E ls bs =
  (enc_bit E (splitlsl ls).1 (splitlsb bs).1 &&
           enc_bits E (splitlsl ls).2 (splitlsb bs).2).
Proof. move=> Hs1 Hs2. exact: (enc_bits_split_nonempty E Hs1 Hs2). Qed.

Lemma enc_bits_joinlsb E ls_hd (ls_tl : word) bs_hd (bs_tl : bits) :
  enc_bits E (joinlsl ls_hd ls_tl) (joinlsb bs_hd bs_tl) =
  (enc_bit E ls_hd bs_hd && enc_bits E ls_tl bs_tl).
Proof. exact: enc_bits_cons. Qed.

Lemma enc_bits_droplsb E (ls : word) (bs : bits) :
  interp_lit E lit_tt -> enc_bits E ls bs -> enc_bits E (droplsl ls) (droplsb bs).
Proof. move=> Htt Henc. by case/andP: (enc_bits_splitlsb Htt Henc). Qed.

Lemma enc_bits_droplsb_nonempty E (ls : word) (bs : bits) :
  0 < size ls -> 0 < size bs ->
  enc_bits E ls bs -> enc_bits E (droplsl ls) (droplsb bs).
Proof.
  move=> Hs1 Hs2. rewrite (enc_bits_splitlsb_nonempty E Hs1 Hs2).
  by move/andP => [_ H].
Qed.

Lemma enc_bits_splitmsb E (ls : word) (bs : bits) :
  interp_lit E lit_tt ->
  enc_bits E ls bs ->
  enc_bits E (splitmsl ls).1 (splitmsb bs).1 &&
           enc_bit E (splitmsl ls).2 (splitmsb bs).2.
Proof.
  elim: ls bs => [| ls_hd ls_tl IH] [| bs_hd bs_tl] //=.
  - rewrite /enc_bits /enc_bit /=. by move=> ->.
  - rewrite enc_bits_cons => Htt /andP [Hhd Htl]. move: (IH _ Htt Htl).
    rewrite /splitmsl /splitmsb /=. move: (enc_bits_size Htl) => {Htl IH}.
    case: ls_tl; case: bs_tl => //=.
    move=> b_hd b_tl l_hd l_tl Hs /andP [H1 H2]. by rewrite enc_bits_cons Hhd H1 H2.
Qed.

Lemma enc_bits_splitmsb_ss E (ls : word) (bs : bits) :
  interp_lit E lit_tt ->
  size ls = size bs ->
  enc_bits E ls bs =
  enc_bits E (splitmsl ls).1 (splitmsb bs).1 &&
           enc_bit E (splitmsl ls).2 (splitmsb bs).2.
Proof.
  elim: ls bs => [| ls_hd ls_tl IH] [| bs_hd bs_tl] //=.
  - rewrite /enc_bits /enc_bit /=. by move=> ->.
  - rewrite enc_bits_cons => Htt Hs. move: (eq_add_S _ _ Hs) => {Hs} Hs.
    rewrite (IH _ Htt Hs) => {IH}. rewrite /splitmsl /splitmsb /=. move: Hs.
    case: ls_tl; case: bs_tl => //=.
    + rewrite {2}/enc_bit /=. rewrite Htt andbT. reflexivity.
    + move=> b_hd b_tl l_hd l_tl Hs. rewrite enc_bits_cons.
      rewrite Bool.andb_assoc (Bool.andb_comm (enc_bit E ls_hd bs_hd))
              -Bool.andb_assoc. reflexivity.
Qed.

Lemma enc_bits_splitmsb_nonempty E (ls : word) (bs : bits) :
  0 < size ls -> 0 < size bs ->
  enc_bits E ls bs =
  enc_bits E (splitmsl ls).1 (splitmsb bs).1 &&
           enc_bit E (splitmsl ls).2 (splitmsb bs).2.
Proof.
  elim: ls bs => [| ls_hd ls_tl IH] [| bs_hd bs_tl] //=. move: IH.
  case: ls_tl bs_tl => [|ls_tlhd ls_tltl] [|bs_tlhd bs_tltl] /=.
  - move=> _ _ _. rewrite /enc_bits /enc_bit /=.
    by rewrite singleton_eq.
  - move=> IH _ _. rewrite /enc_bit /enc_bits /=. apply/negP => /eqP H. discriminate.
  - move=> IH _ _. rewrite /enc_bit /enc_bits /=. apply/negP => /eqP H. discriminate.
  - move=> IH _ _. have H1: 0 < (size ls_tltl).+1 by done.
    have H2: 0 < (size (bs_tlhd::bs_tltl)) by done.
    move: (IH _ H1 H2) => {IH H1 H2} /=. rewrite !enc_bits_cons. move=> ->.
    rewrite Bool.andb_assoc (Bool.andb_comm (enc_bit E ls_hd bs_hd))
            -Bool.andb_assoc. reflexivity.
Qed.

Lemma enc_bits_rcons E ls l bs b :
  enc_bits E (rcons ls l) (rcons bs b) = enc_bits E ls bs && enc_bit E l b.
Proof.
  rewrite enc_bits_splitmsb_nonempty.
  - rewrite /splitmsl /=. rewrite !belastd_rcons !lastd_rcons. reflexivity.
  - by rewrite size_rcons.
  - by rewrite size_rcons.
Qed.

Lemma enc_bits_joinmsb E ls l bs b :
  enc_bits E (joinmsl ls l) (joinmsb bs b) = enc_bits E ls bs && enc_bit E l b.
Proof. exact: enc_bits_rcons. Qed.

Lemma enc_bits_dropmsb E (ls : word) (bs : bits) :
  interp_lit E lit_tt -> enc_bits E ls bs -> enc_bits E (dropmsl ls) (dropmsb bs).
Proof.
  move=> Htt Henc. rewrite /dropmsl /dropmsb.
    by case/andP: (enc_bits_splitmsb Htt Henc).
Qed.

Lemma enc_bits_concat E ls0 bs0 ls1 bs1 :
  enc_bits E ls0 bs0 -> enc_bits E ls1 bs1 ->
  enc_bits E (cat ls0 ls1) (bs0 ++# bs1)%bits.
Proof.
  elim: ls0 bs0 => [| ls0_hd ls0_tl IH] [| bs0_hd bs0_tl] //=.
  rewrite !enc_bits_cons => /andP [H0_hd H0_tl] H1. by rewrite H0_hd (IH _ H0_tl H1).
Qed.

Lemma enc_bits_rev E ls bs : enc_bits E ls bs -> enc_bits E (rev ls) (rev bs).
Proof.
  elim: ls bs => [| ls_hd ls_tl IH] [| bs_hd bs_tl] //=.
  rewrite enc_bits_cons => /andP [Hhd Htl]. rewrite !rev_cons enc_bits_rcons.
  by rewrite (IH _ Htl) Hhd.
Qed.

Lemma enc_bit_env_upd_eq_pos E x b : enc_bit (env_upd E x b) (Pos x) b.
Proof. rewrite /enc_bit /=. by rewrite env_upd_eq. Qed.

Lemma enc_bit_env_upd_eq_neg E x b : enc_bit (env_upd E x b) (Neg x) (~~b).
Proof. rewrite /enc_bit /=. by rewrite env_upd_eq. Qed.

Lemma enc_bit_env_upd_neq E l b x y :
  x != var_of_lit l ->
  enc_bit (env_upd E x y) l b = enc_bit E l b.
Proof.
  rewrite /enc_bit => Hne. rewrite (interp_lit_env_upd_neq _ _ Hne). reflexivity.
Qed.

Lemma interp_word_enc_bits E (ls1 ls2 : word) bs :
  interp_word E ls1 = interp_word E ls2 ->
  enc_bits E ls1 bs = enc_bits E ls2 bs.
Proof.
  move=> Heq. apply: enc_bits_change_word. rewrite word_equiv_interp_eq.
  apply/eqP. assumption.
Qed.



(* newer_than_lit and newer_than_lits *)

Definition newer_than_var g v : bool := Pos.ltb v g.

Definition newer_than_lit g l : bool := newer_than_var g (var_of_lit l).

Definition newer_than_lits g ls : bool := all (newer_than_lit g) ls.

Definition newer_than_cnf g cs : bool := all (newer_than_lits g) cs.

Lemma newer_than_lit_tt_ff g : newer_than_lit g lit_tt = newer_than_lit g lit_ff.
Proof. by rewrite /newer_than_lit /=. Qed.

Lemma newer_than_var_irrefl x : ~~ newer_than_var x x.
Proof.
  apply/negP => Hnew. rewrite /newer_than_var Pos.ltb_irrefl in Hnew.
  exact: not_false_is_true.
Qed.

Lemma newer_than_var_trans x y z :
  newer_than_var x y -> newer_than_var y z -> newer_than_var x z.
Proof.
  move=> Hxy Hyz. apply/pos_ltP. move/pos_ltP: Hxy=> Hxy.
  move/pos_ltP: Hyz=> Hyz. exact: (Pos.lt_trans _ _ _ Hyz Hxy).
Qed.

Lemma newer_than_var_le_newer x y z :
  newer_than_var x y -> (x <=? z)%positive -> newer_than_var z y.
Proof.
  move=> /pos_ltP Hyx /pos_leP Hxz. apply/pos_ltP.
  exact: (Pos.lt_le_trans _ _ _ Hyx Hxz).
Qed.

Lemma newer_than_var_lt_newer x y z :
  newer_than_var x y -> (x <? z)%positive -> newer_than_var z y.
Proof.
  move=> /pos_ltP Hyx /pos_ltP Hxz. apply/pos_ltP.
  exact: (Pos.lt_trans _ _ _ Hyx Hxz).
Qed.

Lemma newer_than_var_neq g l :
  newer_than_var g l -> g != l.
Proof.
  move=> Hg. apply/negP. rewrite /= => H. rewrite (eqP H) in Hg.
  rewrite /newer_than_var in Hg. rewrite Pos.ltb_irrefl in Hg. by elim Hg.
Qed.

Lemma newer_than_var_add_diag_r x y : newer_than_var (x + y) x.
Proof. rewrite /newer_than_var. exact: pos_ltb_add_diag_r. Qed.

Lemma newer_than_var_add_r x y z : newer_than_var x y -> newer_than_var (x + z) y.
Proof.
  rewrite /newer_than_var=> Hnew. apply/pos_ltP. move/pos_ltP: Hnew=> Hnew.
  exact: pos_lt_add_r.
Qed.

Lemma newer_than_lit_irrefl x : ~~ newer_than_lit (var_of_lit x) x.
Proof. exact: newer_than_var_irrefl. Qed.

Lemma newer_than_lit_trans x y z :
  newer_than_lit (var_of_lit x) y -> newer_than_lit (var_of_lit y) z ->
  newer_than_var (var_of_lit x) (var_of_lit z).
Proof. move=> Hxy Hyz. exact: (newer_than_var_trans Hxy Hyz). Qed.

Lemma newer_than_lit_neq g l : newer_than_lit g l -> g != var_of_lit l.
Proof. move=> Hg. apply: newer_than_var_neq. exact: Hg. Qed.

Lemma newer_than_lit_neg g l : newer_than_lit g (neg_lit l) = newer_than_lit g l.
Proof. case: l => l; reflexivity. Qed.

Lemma newer_than_lit_add_diag_r x y : newer_than_lit (var_of_lit x + y) x.
Proof. rewrite /newer_than_lit /newer_than_var. exact: pos_ltb_add_diag_r. Qed.

Lemma newer_than_lit_add_r x y z : newer_than_lit x y -> newer_than_lit (x + z) y.
Proof. rewrite /newer_than_lit=> Hnew. exact: newer_than_var_add_r. Qed.

Lemma newer_than_lit_le_newer x y z :
  newer_than_lit x y -> (x <=? z)%positive -> newer_than_lit z y.
Proof.
  move=> /pos_ltP Hyx /pos_leP Hxz. apply/pos_ltP.
  exact: (Pos.lt_le_trans _ _ _ Hyx Hxz).
Qed.

Lemma newer_than_lit_lt_newer x y z :
  newer_than_lit x y -> (x <? z)%positive -> newer_than_lit z y.
Proof.
  move=> /pos_ltP Hyx /pos_ltP Hxz. apply/pos_ltP.
  exact: (Pos.lt_trans _ _ _ Hyx Hxz).
Qed.

Lemma newer_than_lit_enc_bit_env_upd E x v l b :
  newer_than_lit x l ->
  enc_bit (env_upd E x v) l b = enc_bit E l b.
Proof.
  move=> Hnew. rewrite /enc_bit. move: (newer_than_lit_neq Hnew) => Hneq.
  rewrite (interp_lit_env_upd_neq _ _ Hneq). reflexivity.
Qed.

Lemma newer_than_lits_cons g l ls :
  newer_than_lits g (l::ls) = newer_than_lit g l && newer_than_lits g ls.
Proof. reflexivity. Qed.

Lemma newer_than_lits_append g ls1 ls2 :
  newer_than_lits g (ls1++ls2) = newer_than_lits g ls1 && newer_than_lits g ls2.
Proof.
  elim: ls1 ls2 => [| hd1 tl1 IH1] ls2 //=. rewrite (IH1 ls2). rewrite andbA.
  reflexivity.
Qed.

Lemma newer_than_lits_neq g ls l :
  l \in ls -> newer_than_lits g ls -> g != (var_of_lit l).
Proof.
  elim: ls l => [| hd tl IH] l //=. move=> Hmem. move/andP=> [Hnew_hd Hnew_tl].
  rewrite in_cons in Hmem. case/orP: Hmem.
  + move=> /eqP ->. exact: (newer_than_lit_neq Hnew_hd).
  + move=> Hmem. exact: (IH _ Hmem Hnew_tl).
Qed.

Lemma newer_than_lits_add_r x ls y :
  newer_than_lits x ls -> newer_than_lits (x + y) ls.
Proof.
  elim: ls x y => [| hd tl IH] x y //=. move/andP=> [Hnewer_hd Hnewer_tl].
  rewrite (IH _ _ Hnewer_tl) andbT. exact: newer_than_lit_add_r.
Qed.

Lemma newer_than_lits_le_newer x ls y :
  newer_than_lits x ls -> (x <=? y)%positive -> newer_than_lits y ls.
Proof.
  elim: ls x y => [| hd tl IH] x y //=. move/andP=> [Hnew_hd Hnew_tl] Hle.
  rewrite (newer_than_lit_le_newer Hnew_hd Hle). rewrite (IH _ _ Hnew_tl Hle). done.
Qed.

Lemma newer_than_lits_lt_newer x ls y :
  newer_than_lits x ls -> (x <? y)%positive -> newer_than_lits y ls.
Proof.
  elim: ls x y => [| hd tl IH] x y //=. move/andP=> [Hnew_hd Hnew_tl] Hle.
  rewrite (newer_than_lit_lt_newer Hnew_hd Hle). rewrite (IH _ _ Hnew_tl Hle). done.
Qed.

Lemma newer_than_lits_nseq g n l :
  newer_than_lit g l -> newer_than_lits g (nseq n l).
Proof. elim: n => [| n IH] //=. move=> H. by rewrite H (IH H). Qed.

Lemma newer_than_lits_copy g n l :
  newer_than_lit g l -> newer_than_lits g (copy n l).
Proof. exact: (newer_than_lits_nseq). Qed.

Lemma newer_than_lits_splitlsl g (lits : seq literal) :
  newer_than_lit g lit_tt ->
  newer_than_lits g lits ->
  newer_than_lit g (splitlsl lits).1 && newer_than_lits g (splitlsl lits).2.
Proof.
  case: lits => [| hd tl IH] //=. move=> Htt _. by rewrite -newer_than_lit_tt_ff Htt.
Qed.

Lemma newer_than_lits_splitlsl_nonempty g (lits : seq literal) :
  0 < size lits ->
  newer_than_lits g lits ->
  newer_than_lit g (splitlsl lits).1 && newer_than_lits g (splitlsl lits).2.
Proof. by case: lits => [| hd tl IH] //=. Qed.

Lemma newer_than_lits_lsl g (ls : seq literal) :
  newer_than_lit g lit_tt -> newer_than_lits g ls -> newer_than_lit g (lsl ls).
Proof.
  move=> Htt H. move: (newer_than_lits_splitlsl Htt H).
  by rewrite /lsl => /andP [-> _].
Qed.

Lemma newer_than_lits_lsl_nonempty g (ls : seq literal) :
  0 < size ls -> newer_than_lits g ls -> newer_than_lit g (lsl ls).
Proof.
  move=> Hs H. move: (newer_than_lits_splitlsl_nonempty Hs H).
  by rewrite /lsl => /andP [-> _].
Qed.

Lemma newer_than_lits_droplsl g (ls : seq literal) :
  newer_than_lits g ls -> newer_than_lits g (droplsl ls).
Proof.
  case: ls => [| hd tl] //=. rewrite /droplsl => /andP [_ H] /=. assumption.
Qed.

Lemma newer_than_lits_joinlsl g l ls :
  newer_than_lit g l -> newer_than_lits g ls -> newer_than_lits g (joinlsl l ls).
Proof. move=> H1 H2 /=. by rewrite H1 H2. Qed.

Lemma newer_than_lits_splitmsl g (ls : seq literal) :
  newer_than_lit g lit_tt ->
  newer_than_lits g ls ->
  newer_than_lits g (splitmsl ls).1 && newer_than_lit g (splitmsl ls).2.
Proof.
  elim: ls => [| hd tl IH] //=. move=> Htt /andP [Hhd Htl].
  move: (IH Htt Htl) => {IH}. rewrite /splitmsl /split_last /=.
  case: tl Htl => //=. move=> tl_hd tl_tl /andP [Htl_hd Htl_tl]
    /andP [Htl_belast Htl_last]. by rewrite Hhd Htl_belast Htl_last.
Qed.

Lemma newer_than_lits_splitmsl_nonempty g (ls : seq literal) :
  0 < size ls ->
  newer_than_lits g ls ->
  newer_than_lits g (splitmsl ls).1 && newer_than_lit g (splitmsl ls).2.
Proof.
  elim: ls => [| hd [| tl_hd tl_tl] IH] //=.
  - by move=> _ /andP [-> _].
  - move=> _ /andP [Hhd Htl]. rewrite /= in IH. have Hs: 0 < (size tl_tl).+1 by done.
    move: (IH Hs Htl) => {IH Hs}. move/andP => [Htl_belast Htl_last].
    by rewrite Hhd Htl_belast Htl_last.
Qed.

Lemma newer_than_lits_msl g (ls : seq literal) :
  newer_than_lit g lit_tt -> newer_than_lits g ls -> newer_than_lit g (msl ls).
Proof.
  move=> Htt H. move: (newer_than_lits_splitmsl Htt H).
  by rewrite /msl => /andP [_ ->].
Qed.

Lemma newer_than_lits_msl_nonempty g (ls : seq literal) :
  0 < size ls -> newer_than_lits g ls -> newer_than_lit g (msl ls).
Proof.
  move=> Hs H. move: (newer_than_lits_splitmsl_nonempty Hs H).
  by rewrite /msl => /andP [_ ->].
Qed.

Lemma newer_than_lits_dropmsl g (ls : seq literal) :
  newer_than_lits g ls -> newer_than_lits g (dropmsl ls).
Proof.
  elim: ls => [| hd tl IH] //=. move/andP=> [Hhd Htl]. move: (IH Htl) => {IH}.
  case: tl Htl => //=. move=> tl_hd tl_tl /andP [Htl_hd Htl_tl] Hdropmsl.
  rewrite /dropmsl /= in Hdropmsl. by rewrite Hhd Hdropmsl.
Qed.

Lemma newer_than_lits_joinmsl g ls l :
  newer_than_lits g ls -> newer_than_lit g l -> newer_than_lits g (joinmsl ls l).
Proof.
  elim: ls => [| hd tl IH] /=.
  - by move=> _ ->.
  - move/andP=> [Hhd Htl] Hl. by rewrite Hhd (IH Htl Hl).
Qed.

Lemma newer_than_lits_rev g ls :
  newer_than_lits g ls -> newer_than_lits g (rev ls).
Proof.
  elim: ls => [| hd tl IH] //=. rewrite rev_cons.
  move/andP=> [Hhd Htl]. apply: (newer_than_lits_joinmsl (IH Htl) Hhd).
Qed.

Lemma newer_than_lits_enc_bits_env_upd  E x b (ls : seq literal) bs :
  newer_than_lits x ls ->
  enc_bits (env_upd E x b) ls bs = enc_bits E ls bs.
Proof.
  elim: ls bs => [| lt_hd ls_tl IH] [| bs_hd bs_tl] //=. move/andP=> [Hhd Htl].
  rewrite !enc_bits_cons. rewrite (newer_than_lit_enc_bit_env_upd _ _ _ Hhd).
  rewrite (IH _ Htl). reflexivity.
Qed.

Lemma newer_than_cnf_cons g c cs :
  newer_than_cnf g (c::cs) = newer_than_lits g c && newer_than_cnf g cs.
Proof. reflexivity. Qed.

Lemma newer_than_cnf_append g cs1 cs2 :
  newer_than_cnf g (cs1++cs2) = newer_than_cnf g cs1 && newer_than_cnf g cs2.
Proof. elim: cs1 cs2 => [| hd tl IH] cs2 //=. by rewrite (IH cs2) andbA. Qed.

Lemma newer_than_cnf_add_r x cs y : newer_than_cnf x cs -> newer_than_cnf (x + y) cs.
Proof.
  elim: cs x => [| hd tl IH] x //=. move/andP=> [Hhd Htl].
  by rewrite (newer_than_lits_add_r _ Hhd) (IH _ Htl).
Qed.

Lemma newer_than_cnf_le_newer x cs y :
  newer_than_cnf x cs -> (x <=? y)%positive -> newer_than_cnf y cs.
Proof.
  elim: cs x => [| hd tl IH] x //=. move/andP=> [Hhd Htl] Hle.
  by rewrite (newer_than_lits_le_newer Hhd Hle) (IH _ Htl Hle).
Qed.

Lemma newer_than_cnf_lt_newer x cs y :
  newer_than_cnf x cs -> (x <? y)%positive -> newer_than_cnf y cs.
Proof.
  elim: cs x => [| hd tl IH] x //=. move/andP=> [Hhd Htl] Hlt.
  by rewrite (newer_than_lits_lt_newer Hhd Hlt) (IH _ Htl Hlt).
Qed.

Lemma interp_lit_env_upd_newer E x v y :
  newer_than_lit x y -> interp_lit (env_upd E x v) y = interp_lit E y.
Proof. move=> H. exact: (interp_lit_env_upd_neq _ _ (newer_than_lit_neq H)). Qed.

Lemma interp_clause_env_upd_newer E x v (c : clause) :
  newer_than_lits x c ->
  interp_clause (env_upd E x v) c = interp_clause E c.
Proof.
  elim: c => [| hd tl IH] //=. move/andP=> [Hhd Htl].
  rewrite (interp_lit_env_upd_newer _ _ Hhd) (IH Htl). reflexivity.
Qed.

Lemma interp_word_env_upd_newer E x v (c : word) :
  newer_than_lits x c ->
  interp_word (env_upd E x v) c = interp_word E c.
Proof.
  elim: c => [| hd tl IH] //=. move/andP=> [Hhd Htl].
  rewrite (interp_lit_env_upd_newer _ _ Hhd) (IH Htl). reflexivity.
Qed.

Lemma interp_cnf_env_upd_newer E x v (cs : cnf) :
  newer_than_cnf x cs ->
  interp_cnf (env_upd E x v) cs = interp_cnf E cs.
Proof.
  elim: cs => [| hd tl IH] //=. move/andP=> [Hhd Htl].
  rewrite (interp_clause_env_upd_newer _ _ Hhd) (IH Htl). reflexivity.
Qed.



(* env_preserve *)

Definition env_preserve (E E' : env) g :=
  forall v : bvar,
    newer_than_var g v ->
    E' v = E v.

Lemma env_preserve_refl E g : env_preserve E E g.
Proof. done. Qed.

Lemma env_preserve_sym E1 E2 g : env_preserve E1 E2 g -> env_preserve E2 E1 g.
Proof. move=> H l Hnew. by rewrite (H _ Hnew). Qed.

Lemma env_preserve_trans E1 E2 E3 g :
  env_preserve E1 E2 g -> env_preserve E2 E3 g -> env_preserve E1 E3 g.
Proof. move=> H12 H23 l Hnew. by rewrite (H23 _ Hnew) (H12 _ Hnew). Qed.

Lemma env_preserve_lit E E' g l :
  env_preserve E E' g -> newer_than_lit g l -> interp_lit E' l = interp_lit E l.
Proof.
  move=> Hpre Hnew. rewrite /interp_lit. case: l Hnew.
  - move=> v Hnew. exact: (Hpre _ Hnew).
  - move=> v Hnew. rewrite (Hpre _ Hnew) /=. reflexivity.
Qed.

Lemma env_preserve_word E E' g (ls : seq literal) :
  env_preserve E E' g -> newer_than_lits g ls -> interp_word E' ls = interp_word E ls.
Proof.
  elim: ls => [| hd tl IH] //=. move=> Hpre /andP [Hhd Htl].
  by rewrite (env_preserve_lit Hpre Hhd) (IH Hpre Htl).
Qed.

Lemma env_preserve_clause E E' g c :
  env_preserve E E' g -> newer_than_lits g c ->
  interp_clause E' c = interp_clause E c.
Proof.
  elim: c => [| hd tl IH] //=. move=> Hpre /andP [Hhd Htl].
  by rewrite (env_preserve_lit Hpre Hhd) (IH Hpre Htl).
Qed.

Lemma env_preserve_cnf E E' g cs :
  env_preserve E E' g -> newer_than_cnf g cs ->
  interp_cnf E' cs = interp_cnf E cs.
Proof.
  elim: cs => [| hd tl IH] //=. move=> Hpre /andP [Hhd Htl].
  by rewrite (env_preserve_clause Hpre Hhd) (IH Hpre Htl).
Qed.

Lemma env_upd_eq_preserve E x v : env_preserve E (env_upd E x v) x.
Proof.
  move=> l Hnew. rewrite env_upd_neq; first by reflexivity.
  exact: (newer_than_var_neq Hnew).
Qed.

Lemma env_upd_newer_preserve E x v y :
  newer_than_var x y -> env_preserve E (env_upd E x v) y.
Proof.
  move=> Hnew_xy l Hnew_yl. apply: env_upd_neq.
  exact: (newer_than_var_neq (newer_than_var_trans Hnew_xy Hnew_yl)).
Qed.

Lemma env_preserve_env_upd_succ E E' x v :
  env_preserve (env_upd E x v) E' (x + 1) -> env_preserve E E' x.
Proof.
  move=> H y Hnew. move: (H y (newer_than_var_add_r 1 Hnew)).
  move=> ->. rewrite env_upd_neq; first by reflexivity. exact: newer_than_var_neq.
Qed.

Lemma env_preserve_enc_bit E E' g b l :
  env_preserve E E' g -> newer_than_lit g l ->
  enc_bit E l b -> enc_bit E' l b.
Proof.
  move=> Hpre Hnew. rewrite /enc_bit => Henc.
  rewrite (env_preserve_lit Hpre Hnew). exact: Henc.
Qed.

Lemma env_preserve_enc_bits E E' g bs ls :
  env_preserve E E' g -> newer_than_lits g ls ->
  enc_bits E ls bs -> enc_bits E' ls bs.
Proof.
  elim: ls bs => [| ls_hd ls_tl IH] [| bs_hd bs_tl] //=.
  move=> Hpre /andP [Hhd Htl]. rewrite !enc_bits_cons => /andP [Henc_hd Henc_tl].
  by rewrite (env_preserve_enc_bit Hpre Hhd Henc_hd) (IH _ Hpre Htl Henc_tl).
Qed.

Lemma env_preserve_le E E' g g' :
  env_preserve E E' g -> (g' <=? g)%positive -> env_preserve E E' g'.
Proof.
  move=> Hpre Hle v Hnew. exact: (Hpre v (newer_than_var_le_newer Hnew Hle)).
Qed.



(* Duplicates removal *)

Definition z_of_lit (x : literal) : Z :=
  match x with
  | Pos n => Zpos n
  | Neg n => Zneg n
  end.

Lemma z_of_lit_inj x y : z_of_lit x = z_of_lit y -> x = y.
Proof. case: x => x; case: y => y //=; by case=> ->. Qed.

Definition lit_lt (x y : literal) : bool := (z_of_lit x <? z_of_lit y)%Z.

Lemma lit_lt_trans x y z : lit_lt x y -> lit_lt y z -> lit_lt x z.
Proof. exact: ZOrder.lt_trans. Qed.

Lemma lit_lt_not_eq x y : lit_lt x y -> x != y.
Proof.
  move=> Hlt. move: (ZOrder.lt_not_eq Hlt). move=> H1; apply/eqP => H2.
  apply: H1. rewrite H2. exact: eqxx.
Qed.

Module LiteralOrderedMinimal <: SsrOrderedTypeMinimal.
  Definition t := lit_eqType.
  Definition eq (x y : t) := x == y.
  Definition lt (x y : t) := lit_lt x y.
  Definition lt_trans := lit_lt_trans.
  Definition lt_not_eq := lit_lt_not_eq.
  Definition compare (x y : t) : Compare lt eq x y.
  Proof.
    case Heq: (x == y).
    - exact: (EQ Heq).
    - case Hlt: (lit_lt x y).
      + exact: (LT Hlt).
      + apply: GT. move: (proj1 (Z.ltb_ge (z_of_lit x) (z_of_lit y)) Hlt) => {Hlt} Hlt.
        have Hne: z_of_lit y <> z_of_lit x
          by move=> H; apply/eqP/idP: Heq; rewrite (z_of_lit_inj H) eqxx.
        apply/Z_ltP. apply: (proj2 (Z.le_neq _ _)). split; assumption.
  Defined.
End LiteralOrderedMinimal.
Module LiteralOrdered := MakeSsrOrderedType LiteralOrderedMinimal.
Module ClauseOrdered := SeqOrdered LiteralOrdered.
Module ClauseSet := FSets.MakeTreeSet ClauseOrdered.

Definition cnf_imp_each E (cs1 cs2 : cnf) :=
  forall c2,
    c2 \in cs2 ->
           exists c1, c1 \in cs1 /\ (interp_clause E c1 -> interp_clause E c2).

Lemma cnf_imp_each_cons E cs1 cs2_hd cs2_tl :
  cnf_imp_each E cs1 (cs2_hd::cs2_tl) <-> (cnf_imp_each E cs1 [::cs2_hd] /\
                                           cnf_imp_each E cs1 cs2_tl).
Proof.
  split; [move => H; split | move=> [H1 H2]].
  - move=> c Hin. rewrite mem_seq1 in Hin.
    have Hin': c \in cs2_hd :: cs2_tl by rewrite (eqP Hin) mem_head.
    exact: (H c Hin').
  - move=> c Hin. have Hin': c \in cs2_hd :: cs2_tl by rewrite in_cons Hin orbT.
    exact: (H c Hin').
  - move=> c Hin. rewrite in_cons in Hin. case/orP: Hin => Hin.
    + have Hin': c \in [::cs2_hd] by rewrite mem_seq1 (eqP Hin).
      exact: (H1 c Hin').
    + exact: (H2 c Hin).
Qed.

Lemma cnf_imp_each_interp E cs1 cs2 :
  cnf_imp_each E cs1 cs2 -> interp_cnf E cs1 -> interp_cnf E cs2.
Proof.
  elim: cs2 cs1 => [| hd2 tl2 IH] cs1 //=. move=> Himp Hcs1.
  move: (Himp hd2 (mem_head hd2 tl2)) => [l1 [H1 H2]].
  rewrite (H2 (interp_cnf_mem Hcs1 H1)) andTb.
  move/cnf_imp_each_cons: Himp => [Himp_hd Himp_tl]. rewrite (IH _ Himp_tl Hcs1).
  by case: tl2 IH Himp_tl.
Qed.

Definition cnf_contains (cs1 cs2 : cnf) := forall c2, c2 \in cs2 -> c2 \in cs1.

Lemma cnf_contains_imp_each E cs1 cs2 :
  cnf_contains cs1 cs2 -> cnf_imp_each E cs1 cs2.
Proof. move=> Hcon c2 Hin. exists c2; split => //=. exact: (Hcon _ Hin). Qed.

Lemma cnf_contains_interp E cs1 cs2 :
  cnf_contains cs1 cs2 -> interp_cnf E cs1 -> interp_cnf E cs2.
Proof. move=> Hcon. exact: (cnf_imp_each_interp (cnf_contains_imp_each E Hcon)). Qed.

Lemma cnf_contains_eqsat E cs1 cs2 :
  cnf_contains cs1 cs2 -> cnf_contains cs2 cs1 -> interp_cnf E cs1 = interp_cnf E cs2.
Proof.
  move=> H12 H21. move: (cnf_imp_each_interp (cnf_contains_imp_each E H12)).
  move: (cnf_imp_each_interp (cnf_contains_imp_each E H21)). case: (interp_cnf E cs1).
  - move=> _ H. by rewrite (H is_true_true).
  - move=> H _. symmetry. apply/negP. move=> Hcs2. by move: (H Hcs2).
Qed.

Definition cnf_remove_duplicate (cs : cnf) :=
  ClauseSet.elements (ClauseSet.Lemmas.OP.P.of_list cs).

Lemma cnf_remove_duplicate_contains1 cs : cnf_contains cs (cnf_remove_duplicate cs).
Proof.
  case: cs => [| hd tl] //=. move=> c Hin. rewrite /cnf_remove_duplicate in Hin.
  move: (ClauseSet.Lemmas.in_elements_mem Hin) => {Hin} Hin.
  exact: (ClauseSet.Lemmas.mem_of_list_in Hin).
Qed.

Lemma cnf_remove_duplicate_contains2 cs : cnf_contains (cnf_remove_duplicate cs) cs.
Proof.
  case: cs => [| hd tl] //=. move=> c Hin. rewrite /cnf_remove_duplicate.
  apply: ClauseSet.Lemmas.mem_in_elements.
  exact: (ClauseSet.Lemmas.in_mem_of_list Hin).
Qed.

Lemma cnf_remove_duplicate_eqsat E cs :
  interp_cnf E cs = interp_cnf E (cnf_remove_duplicate cs).
Proof.
  exact: (cnf_contains_eqsat E (@cnf_remove_duplicate_contains1 cs)
                                (@cnf_remove_duplicate_contains2 cs)).
Qed.



(* Convert CNF to DIMACS format *)

From Coq Require Import String DecimalString.
Open Scope string_scope.

Module PS := FSets.MakeTreeSet(PositiveOrder).

Definition newline : string :=
"
".

Definition vs_of_clause c :=
  foldl (fun vs l => PS.add (var_of_lit l) vs) PS.empty c.

Definition vs_of_cnf cs :=
  foldl (fun vs c => PS.union (vs_of_clause c) vs) PS.empty cs.

(* Do not use nat because the output CNF contains a huge number of variables. *)
Definition num_vars (cs : cnf) : N :=
  PS.fold (fun _ (n : N) => (n + 1)%num) (vs_of_cnf cs) 0%num.

Definition max_var_of_clause c :=
  foldl (fun m l => Pos.max m (var_of_lit l)) var_tt c.

Definition max_var_of_cnf cs :=
  foldl (fun m c => Pos.max m (max_var_of_clause c)) var_tt cs.

(* Do not use nat because the output CNF contains a huge number of clauses. *)
Definition num_clauses (cs : cnf) : N :=
  foldl (fun n _ => (n + 1)%num) 0%num cs.

Definition dimacs_header (cs : cnf) : string :=
  "p cnf " ++ NilEmpty.string_of_uint (N.to_uint (num_vars cs)) ++ " " ++ NilEmpty.string_of_uint (N.to_uint (num_clauses cs)).

Definition diamcs_var (v : bvar) : string :=
  NilEmpty.string_of_uint (Pos.to_uint v).

Definition diamcs_lit (l : literal) : string :=
  match l with
  | Pos v => diamcs_var v
  | Neg v => "-" ++ diamcs_var v
  end.

Definition diamcs_clause (c : clause) : string :=
  (foldl (fun left l => left ++ diamcs_lit l ++ " ") "" c) ++ " 0".

Definition dimacs_cnf (cs : cnf) : string :=
  foldl (fun left c => left ++ diamcs_clause c ++ newline) "" cs.

Definition dimacs_cnf_with_header (cs : cnf) : string :=
  dimacs_header cs ++ newline ++ dimacs_cnf cs.
