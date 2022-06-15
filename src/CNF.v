
(*
 * Require the following libraries:
 * - coq-bit from https://github.com/mht208/coq-nbits
 * - ssrlib from https://github.com/mht208/coq-ssrlib.git
 *)

From Coq Require Import ZArith OrderedType Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import SsrOrder ZAriths Seqs Lists Bools FSets.
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

Definition lit_of_bool b := if b then lit_tt else lit_ff.

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

Definition word_as_cnf (ls : word) := map (fun l => [::l]) ls.

Definition interp_lit (E : env) (l : literal) : bool :=
  match l with
  | Pos v => E v
  | Neg v => negb (E v)
  end.

Definition interp_word (E : env) (ls : word) : bits :=
  map (fun l => interp_lit E l) ls.

Definition interp_clause (E : env) (c : clause) : bool := has (interp_lit E) c.

Definition interp_cnf (E : env) (cs : cnf) : bool := all (interp_clause E) cs.

Definition sat (f : cnf) := exists (E : env), interp_cnf E f.

Definition valid (f : cnf) := forall (E : env), interp_cnf E f.



Lemma size_joinlsl T l (ls : seq T) :
  size (joinlsl l ls) = size ls + 1 .
Proof .
  rewrite /joinlsl /=. rewrite addn1. reflexivity.
Qed .

Lemma size_joinmsl T l (ls : seq T) :
  size (joinmsl ls l) = size ls + 1 .
Proof .
  destruct ls => /= .
  - reflexivity .
  - by rewrite /joinmsl /= size_rcons addn1 .
Qed .

Lemma size_droplsl ls :
  size (droplsl ls) = size ls - 1 .
Proof .
  elim : ls => [| l ls Hls] .
  - done .
  - by rewrite /droplsl /= subn1 .
Qed .

Lemma size_dropmsl ls :
  size (dropmsl ls) = size ls - 1 .
Proof .
  destruct ls => /= .
  - reflexivity .
  - by rewrite subn1 -pred_Sn size_belast .
Qed .

Lemma size_splitmsl ls : (size (splitmsl ls).1) = size ls -1.
Proof.
  intros. rewrite /splitmsl /split_last /=.
  elim ls => [|lshd lstl IH]; try done. rewrite /= size_belast subn1//.
Qed.


(* interp_lit *)

Lemma interp_lit_neg_involutive E a :
  interp_lit E (neg_lit (neg_lit a)) = interp_lit E a.
Proof. rewrite /interp_lit. case: a => /=; reflexivity. Qed.

Lemma interp_lit_neg_lit E a : interp_lit E (neg_lit a) = ~~ (interp_lit E a).
Proof.
  rewrite /interp_lit. case: a => /=; first by reflexivity.
  move=> x. rewrite negb_involutive. reflexivity.
Qed.

Lemma interp_lit_pos_lit E a : interp_lit E a = ~~ (interp_lit E (neg_lit a)).
Proof.
  rewrite -interp_lit_neg_lit. rewrite -interp_lit_neg_involutive. reflexivity.
Qed.



(* interp_word *)

Lemma interp_word_cons E l (ls : word) :
  interp_word E (l::ls) = (interp_lit E l)::(interp_word E ls).
Proof. rewrite /interp_word. rewrite map_cons. reflexivity. Qed.

Lemma interp_word_rcons E w x :
  interp_word E (rcons w x) = rcons (interp_word E w) (interp_lit E x).
Proof. elim: w x => [| y w IH] x //=. rewrite IH. reflexivity. Qed.

Lemma interp_word_cat E w1 w2 :
  interp_word E (w1 ++ w2) = interp_word E w1 ++ interp_word E w2.
Proof. elim: w1 w2 => [| x1 w1 IH] w2 //=. rewrite IH. reflexivity. Qed.

Lemma interp_word_split E (ls : word) :
  0 < size ls ->
  interp_word E ls = (interp_lit E (lsl ls))::(interp_word E (droplsl ls)).
Proof. by case: ls => [|ls_hd ls_tl] //=. Qed.



(* interp_clause *)

Lemma interp_clause_cons E l c :
  interp_clause E (l::c) = interp_lit E l || interp_clause E c.
Proof. reflexivity. Qed.

Lemma interp_clause_cat E c1 c2 :
  interp_clause E (c1++c2) = interp_clause E c1 || interp_clause E c2.
Proof. by rewrite /interp_clause has_cat. Qed.

Lemma interp_clause_mem E c :
  interp_clause E c -> exists2 l, (l \in c) & (interp_lit E l).
Proof. by move/hasP. Qed.

Lemma interp_clause_rcons_cons E l c :
  interp_clause E (rcons c l) = interp_clause E (l::c).
Proof. by rewrite /interp_clause has_rcons /=. Qed.

Lemma interp_clause_catrev_cat E c1 c2 :
  interp_clause E (catrev c1 c2) = interp_clause E (c1 ++ c2).
Proof. by rewrite /interp_clause has_catrev has_cat. Qed.

Lemma interp_clause_catrev E c1 c2 :
  interp_clause E (catrev c1 c2) = interp_clause E c1 || interp_clause E c2.
Proof. by rewrite interp_clause_catrev_cat interp_clause_cat. Qed.



(* interp_cnf *)

Lemma interp_cnf_cons E c cs :
  interp_cnf E (c::cs) = interp_clause E c && interp_cnf E cs.
Proof. reflexivity. Qed.

Lemma interp_cnf_cat E cs1 cs2 :
  interp_cnf E (cs1++cs2) = interp_cnf E cs1 && interp_cnf E cs2.
Proof. by rewrite /interp_cnf all_cat. Qed.

Lemma interp_cnf_mem E c cs : interp_cnf E cs -> c \in cs -> interp_clause E c.
Proof. rewrite /interp_cnf. move/allP => H Hin. exact: (H _ Hin). Qed.

Lemma interp_cnf_rcons_cons E cs c :
  interp_cnf E (rcons cs c) = interp_cnf E (c::cs).
Proof. by rewrite /interp_cnf all_rcons. Qed.

Lemma interp_cnf_rcons E cs c :
  interp_cnf E (rcons cs c) = interp_clause E c && interp_cnf E cs.
Proof. by rewrite interp_cnf_rcons_cons interp_cnf_cons. Qed.

Lemma interp_cnf_catrev_cat E cs1 cs2 :
  interp_cnf E (catrev cs1 cs2) = interp_cnf E (cs1 ++ cs2).
Proof. by rewrite /interp_cnf all_catrev all_cat. Qed.

Lemma interp_cnf_catrev E cs1 cs2 :
  interp_cnf E (catrev cs1 cs2) = interp_cnf E cs1 && interp_cnf E cs2.
Proof. by rewrite interp_cnf_catrev_cat interp_cnf_cat. Qed.



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

Definition add_prelude cs := [::lit_tt]::cs.

Lemma add_prelude_to (E : env) cs :
  E var_tt -> interp_cnf E cs -> interp_cnf E (add_prelude cs).
Proof. rewrite /add_prelude /= orbF. by move=> -> ->. Qed.

Lemma add_prelude_tt E cs : interp_cnf E (add_prelude cs) -> interp_lit E lit_tt.
Proof. rewrite /interp_cnf /=. rewrite orbF=> /andP [H _]; assumption. Qed.

Lemma add_prelude_ff E cs : interp_cnf E (add_prelude cs) -> ~~ interp_lit E lit_ff.
Proof. rewrite interp_cnf_cons /=. rewrite orbF=> /andP [H _]. by apply/negPn. Qed.

Lemma add_prelude_neg_ff E cs :
  interp_cnf E (add_prelude cs) -> interp_lit E (neg_lit lit_ff).
Proof. move=> H. rewrite interp_lit_neg_lit. by rewrite (add_prelude_ff H). Qed.

Lemma add_prelude_empty E : interp_cnf E (add_prelude [::]) = interp_lit E lit_tt.
Proof. by rewrite /= orbF andbT. Qed.

Lemma add_prelude_singleton E c :
  interp_cnf E (add_prelude [::c]) = interp_lit E lit_tt && interp_clause E c.
Proof. by rewrite /= orbF andbT. Qed.

Lemma add_prelude_cons E c cs :
  interp_cnf E (add_prelude (c::cs)) =
  interp_cnf E (add_prelude [::c]) && interp_cnf E (add_prelude cs).
Proof.
  rewrite /= orbF andbT. rewrite !andb_assoc. rewrite -(andb_assoc _ _ (E var_tt)).
  rewrite (andb_comm _ (E var_tt)) andb_assoc andb_diag. reflexivity.
Qed.

Lemma add_prelude_rcons E cs c :
  interp_cnf E (add_prelude (rcons cs c)) =
  interp_cnf E (add_prelude [::c]) && interp_cnf E (add_prelude cs).
Proof.
  rewrite /= orbF andbT. rewrite interp_cnf_rcons. rewrite !andb_assoc.
  rewrite -(andb_assoc _ _ (E var_tt)).
  rewrite (andb_comm _ (E var_tt)) andb_assoc andb_diag. reflexivity.
Qed.

Lemma add_prelude_expand E cs :
  interp_cnf E (add_prelude cs) = interp_lit E lit_tt && interp_cnf E cs.
Proof. by rewrite /interp_cnf /= orbF. Qed.

Lemma add_prelude_idem E cs :
  interp_cnf E (add_prelude (add_prelude cs)) = interp_cnf E (add_prelude cs).
Proof. by rewrite /interp_cnf /= orbF andb_assoc andb_diag. Qed.

Lemma add_prelude_cat E cs1 cs2 :
  interp_cnf E (add_prelude (cs1++cs2)) =
  interp_cnf E (add_prelude cs1) && interp_cnf E (add_prelude cs2).
Proof.
  rewrite /interp_cnf /= orbF all_cat !andb_assoc.
  rewrite -(andb_assoc _ _ (E var_tt)) (andb_comm _ (E var_tt)) andb_assoc andb_diag.
  reflexivity.
Qed.

Lemma add_prelude_catrev E cs1 cs2 :
  interp_cnf E (add_prelude (catrev cs1 cs2)) =
  interp_cnf E (add_prelude cs1) && interp_cnf E (add_prelude cs2).
Proof.
  rewrite {1}/add_prelude. rewrite interp_cnf_cons interp_cnf_catrev.
  rewrite -interp_cnf_cat -add_prelude_cat. reflexivity.
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

Lemma enc_bit_tt_ff E : enc_bit E lit_tt true = enc_bit E lit_ff false.
Proof. rewrite /enc_bit /=. by case: (E var_tt). Qed.

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

Lemma enc_bits_seq1 E l b : enc_bits E [:: l] [:: b] = enc_bit E l b.
Proof. rewrite /enc_bits /enc_bit /=. by case: b; case: (interp_lit E l). Qed.

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

Lemma enc_bits_copy E (l : literal) (b : bool) n :
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
      rewrite andb_assoc (andb_comm (enc_bit E ls_hd bs_hd)) -andb_assoc. reflexivity.
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
    rewrite andb_assoc (andb_comm (enc_bit E ls_hd bs_hd)) -andb_assoc. reflexivity.
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

Lemma enc_bits_cat E ls1 ls2 bs1 bs2 :
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 ->
  enc_bits E (ls1 ++ ls2) (bs1 ++ bs2)%bits.
Proof.
  elim: ls1 bs1 => [| ls1_hd ls1_tl IH] [| bs1_hd bs1_tl] //=.
  rewrite !enc_bits_cons => /andP [H1_hd H1_tl] H2. by rewrite H1_hd (IH _ H1_tl H2).
Qed.

Lemma enc_bits_catrev E ls1 ls2 bs1 bs2 :
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 ->
  enc_bits E (catrev ls1 ls2) (catrev bs1 bs2).
Proof.
  elim: ls1 ls2 bs1 bs2 => [| ls1_hd ls1_tl IH] ls2 [| bs1_hd bs1_tl] bs2 //=.
  rewrite enc_bits_cons => /andP [H1_hd H1_tl] H2.
  rewrite (IH _ _ _ H1_tl); first reflexivity.
  by rewrite enc_bits_cons H1_hd H2.
Qed.

Lemma enc_bit_lastd E (ls : word) (bs : bits) l b:
    enc_bit E l b ->
    enc_bits E ls bs ->
    enc_bit E (lastd l ls) (lastd b bs) .
Proof.
  elim: ls bs => [| ls_hd ls_tl IH] [| bs_hd bs_tl] //=.
  rewrite enc_bits_cons => H /andP [Hhd Htl].
  move: (IH _ H Htl).
  move: (enc_bits_size Htl) => {Htl IH}.
  case: ls_tl; case: bs_tl => //=.
Qed.

Lemma enc_bits_rev E ls bs : enc_bits E ls bs -> enc_bits E (rev ls) (rev bs).
Proof. move=> H. rewrite /rev. by apply: (enc_bits_catrev H). Qed.

Lemma enc_bit_lit_of_bool E b : enc_bit E (lit_of_bool b) b = enc_bit E lit_tt true.
Proof. case: b => //=. by rewrite enc_bit_tt_ff. Qed.

Lemma enc_bits_lit_of_bool E bs :
  enc_bit E lit_tt true -> enc_bits E (map lit_of_bool bs) bs.
Proof.
  move=> Htt. elim: bs => [| hd tl IH] //=. rewrite enc_bits_cons.
  by rewrite enc_bit_lit_of_bool Htt IH.
Qed.

Lemma enc_bits_map_lit_of_bool_nonempty E bs :
  0 < size bs -> enc_bits E (map lit_of_bool bs) bs = enc_bit E lit_tt true.
Proof.
  elim: bs => [| hd [| tl_hd tl_tl] IH] _ //=.
  - by rewrite enc_bits_seq1 enc_bit_lit_of_bool.
  - rewrite enc_bits_cons. rewrite IH; last by done.
    by rewrite enc_bit_lit_of_bool andb_diag.
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

Lemma newer_than_lit_lit_of_bool g b :
  newer_than_lit g (lit_of_bool b) = newer_than_lit g lit_tt.
Proof. by case: b. Qed.

Lemma newer_than_lits_cons g l ls :
  newer_than_lits g (l::ls) = newer_than_lit g l && newer_than_lits g ls.
Proof. reflexivity. Qed.

Lemma newer_than_lits_cat g ls1 ls2 :
  newer_than_lits g (ls1++ls2) = newer_than_lits g ls1 && newer_than_lits g ls2.
Proof.
  elim: ls1 ls2 => [| hd1 tl1 IH1] ls2 //=. rewrite (IH1 ls2). rewrite andbA.
  reflexivity.
Qed.

Lemma newer_than_lits_rcons g ls l :
  newer_than_lits g (rcons ls l) = newer_than_lits g ls && newer_than_lit g l.
Proof.
  elim: ls => [| hd tl IH] /=.
  - by rewrite andbT.
  - by rewrite IH andb_assoc.
Qed.

Lemma newer_than_lits_catrev g ls1 ls2 :
  newer_than_lits g (catrev ls1 ls2) = newer_than_lits g ls1 && newer_than_lits g ls2.
Proof.
  elim: ls1 ls2 => [| hd1 tl1 IH1] ls2 //=. rewrite IH1 newer_than_lits_cons.
  by rewrite andb_assoc (andb_comm _ (newer_than_lit g hd1)).
Qed.

Lemma newer_than_lits_lit_of_bool g bs :
  newer_than_lit g lit_tt -> newer_than_lits g (map lit_of_bool bs).
Proof.
  move=> H. elim: bs => [| hd tl IH] //=. by rewrite newer_than_lit_lit_of_bool H IH.
Qed.

Lemma newer_than_lits_lit_of_bool_nonempty g bs :
  0 < size bs ->
  newer_than_lits g (map lit_of_bool bs) = newer_than_lit g lit_tt.
Proof.
  elim: bs => [| hd [| tl_hd tl_tl] IH] _ //.
  - by rewrite /= newer_than_lit_lit_of_bool andbT.
  - rewrite newer_than_lits_cons IH; last by done.
      by rewrite newer_than_lit_lit_of_bool andb_diag.
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

Lemma newer_than_lits_copy g n l :
  newer_than_lit g l -> newer_than_lits g (copy n l).
Proof. elim: n => [| n IH] //=. move=> H. by rewrite H (IH H). Qed.

Lemma newer_than_lits_copy_nonempty g n l :
  0 < n -> newer_than_lits g (nseq n l) = newer_than_lit g l.
Proof.
  elim: n => [| n IH] _ //=. case: n IH => /=.
  - move=> _; by rewrite andbT.
  - move=> n IH. rewrite IH => //=. exact: andb_diag.
Qed.

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

Lemma newer_than_lit_lastd g (ls : word) l:
    newer_than_lit g l ->
    newer_than_lits g ls -> newer_than_lit g (lastd l ls) .
Proof.
  rewrite /lastd.
  elim: ls g l=> [| ls_hd ls_tl IH] g l //=.
  move=> Hgl /andP [Hhd Htl].
  move: (IH _ _ Hgl Htl).
  clear IH Htl.
  case: ls_tl; move=> //=.
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

Lemma newer_than_cnf_cat g cs1 cs2 :
  newer_than_cnf g (cs1++cs2) = newer_than_cnf g cs1 && newer_than_cnf g cs2.
Proof. elim: cs1 cs2 => [| hd tl IH] cs2 //=. by rewrite (IH cs2) andbA. Qed.

Lemma newer_than_cnf_rcons g cs c :
  newer_than_cnf g (rcons cs c) = newer_than_cnf g cs && newer_than_lits g c.
Proof.
  elim: cs => [| hd tl IH] /=.
  - by rewrite andbT.
  - by rewrite IH andb_assoc.
Qed.

Lemma newer_than_cnf_catrev g cs1 cs2 :
  newer_than_cnf g (catrev cs1 cs2) = newer_than_cnf g cs1 && newer_than_cnf g cs2.
Proof.
  elim: cs1 cs2 => [| hd1 tl1 IH1] ls2 //=. rewrite IH1 newer_than_cnf_cons.
  by rewrite andb_assoc (andb_comm _ (newer_than_lits g hd1)).
Qed.

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

Lemma newer_than_cnf_rev g cs :
  newer_than_cnf g (rev cs) = newer_than_cnf g cs.
Proof.
  elim: cs => [| c cs IH] //=. rewrite rev_cons. rewrite newer_than_cnf_rcons.
  rewrite IH andbC. reflexivity.
Qed.

Lemma newer_than_cnf_tflatten_cons g c cs :
  newer_than_cnf g (tflatten (c :: cs)) =
  newer_than_cnf g c && newer_than_cnf g (tflatten cs).
Proof.
  elim: cs c => [| hd tl IH] c //=.
  - rewrite /tflatten /=. rewrite catrevE cats0. rewrite newer_than_cnf_rev andbT. reflexivity.
  - rewrite tflatten_cons. rewrite newer_than_cnf_cat. rewrite newer_than_cnf_rev.
    rewrite andbC. reflexivity.
Qed.

Lemma newer_than_cnf_tflatten_catrev g cs1 cs2 :
  newer_than_cnf g (tflatten (catrev cs1 cs2)) =
  newer_than_cnf g (tflatten cs1) && newer_than_cnf g (tflatten cs2).
Proof.
  elim: cs1 cs2 => [| c1 cs1 IH] cs2 //=.
  rewrite IH. rewrite !newer_than_cnf_tflatten_cons.
  case: (newer_than_cnf g c1) => //=. by rewrite andbF.
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

Module LiteralOrderMinimal <: SsrOrderMinimal.
  Definition t := lit_eqType.
  Definition eqn (x y : t) := x == y.
  Definition ltn (x y : t) := lit_lt x y.
  Definition ltn_trans := lit_lt_trans.
  Definition ltn_not_eqn := lit_lt_not_eq.
  Definition compare (x y : t) : Compare ltn eqn x y.
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
End LiteralOrderMinimal.
Module LiteralOrder <: SsrOrder := MakeSsrOrder LiteralOrderMinimal.
Module ClauseOrder <: SsrOrder := SeqOrder LiteralOrder.
Module ClauseSet := FSets.MakeTreeSet ClauseOrder.

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



(* Variable reordering *)

From ssrlib Require Import FMaps Tactics.

Module PM := MakeTreeMap(PositiveOrder).

Section Reorder.

  Definition reorder_lit (m : PM.t positive) (g : positive) (l : literal) :=
    match l with
    | Pos v => match PM.find v m with
               | None => (PM.add v g m, (g + 1)%positive, Pos g)
               | Some v' => (m, g, Pos v')
               end
    | Neg v => match PM.find v m with
               | None => (PM.add v g m, (g + 1)%positive, Neg g)
               | Some v'=> (m, g, Neg v')
               end
    end.

  Fixpoint reorder_clause (m : PM.t positive) (g : positive) (c : clause) :=
    match c with
    | [::] => (m, g, [::])
    | hd::tl =>
      let '(m1, g1, hd') := reorder_lit m g hd in
      let '(m2, g2, tl') := reorder_clause m1 g1 tl in
      (m2, g2, hd'::tl')
    end.

  Fixpoint reorder_cnf_rec (m : PM.t positive) (g : positive) (cs : cnf) :=
    match cs with
    | [::] => (m, g, cs)
    | hd::tl =>
      let '(m1, g1, hd') := reorder_clause m g hd in
      let '(m2, g2, tl') := reorder_cnf_rec m1 g1 tl in
      (m2, g2, hd'::tl')
    end.

  Definition reorder_lit_full m rm g l :=
    match l with
    | Pos v => match PM.find v m with
               | None => (PM.add v g m, PM.add g v rm, (g + 1)%positive, Pos g)
               | Some v' => (m, rm, g, Pos v')
               end
    | Neg v => match PM.find v m with
               | None => (PM.add v g m, PM.add g v rm, (g + 1)%positive, Neg g)
               | Some v'=> (m, rm, g, Neg v')
               end
    end.

  Fixpoint reorder_clause_full m rm g c :=
    match c with
    | [::] => (m, rm, g, [::])
    | hd::tl =>
      let '(m1, rm1, g1, hd') := reorder_lit_full m rm g hd in
      let '(m2, rm2, g2, tl') := reorder_clause_full m1 rm1 g1 tl in
      (m2, rm2, g2, hd'::tl')
    end.

  Fixpoint reorder_cnf_rec_full m rm g cs :=
    match cs with
    | [::] => (m, rm, g, cs)
    | hd::tl =>
      let '(m1, rm1, g1, hd') := reorder_clause_full m rm g hd in
      let '(m2, rm2, g2, tl') := reorder_cnf_rec_full m1 rm1 g1 tl in
      (m2, rm2, g2, hd'::tl')
    end.

  Definition reorder_upd_env (E : env) m :=
    fun v => match PM.find v m with
             | None => E v
             | Some v' => E v'
             end.

  Definition newer_than_values (g : positive) (m : PM.t positive) :=
    forall v v', PM.find v m = Some v' -> (v' < g)%positive.

  Definition newer_than_keys (g : positive) (m : PM.t positive) :=
    forall v, PM.mem v m -> (v < g)%positive.

  Definition consistent_vm (m rm : PM.t positive) :=
    forall v v', PM.find v m = Some v' <->
                 PM.find v' rm = Some v.


  Lemma consistent_vm_newer_than m rm g :
    consistent_vm m rm ->
    newer_than_values g m <-> newer_than_keys g rm.
  Proof.
    move=> Hcon. split.
    - move=> Hnv v Hmemv. move: (PM.Lemmas.mem_find_some Hmemv) => [v' Hfv].
      move/Hcon : Hfv => Hfv'. exact: (Hnv _ _ Hfv').
    - move=> Hnk v v' Hfv. move/Hcon : Hfv => Hfv'.
      move: (PM.Lemmas.find_some_mem Hfv') => Hmem. exact: (Hnk _ Hmem).
  Qed.


  Lemma reorder_lit_full_newer_than_values m rm g l m' rm' g' l' :
    reorder_lit_full m rm g l = (m', rm', g', l') ->
    newer_than_values g m -> newer_than_values g' m'.
  Proof.
    rewrite /reorder_lit_full. case: l => v.
    - case Hfv: (PM.find v m).
      + case=> ? ? ? ?; subst. by apply.
      + case=> ? ? ? ?; subst. move=> Hnew. move=> u u' Hfu. case Huv: (u == v).
        * rewrite (PM.Lemmas.find_add_eq Huv) in Hfu. case: Hfu => ?; subst.
          exact: Pos.lt_add_r.
        * move/negP: Huv=> Huv. rewrite (PM.Lemmas.find_add_neq Huv) in Hfu.
          move: (Hnew _ _ Hfu) => Hlt. exact: (pos_lt_add_r _ Hlt).
    - case Hfv: (PM.find v m).
      + case=> ? ? ? ?; subst. by apply.
      + case=> ? ? ? ?; subst. move=> Hnew. move=> u u' Hfu. case Huv: (u == v).
        * rewrite (PM.Lemmas.find_add_eq Huv) in Hfu. case: Hfu => ?; subst.
          exact: Pos.lt_add_r.
        * move/negP: Huv=> Huv. rewrite (PM.Lemmas.find_add_neq Huv) in Hfu.
          move: (Hnew _ _ Hfu) => Hlt. exact: (pos_lt_add_r _ Hlt).
  Qed.

  Lemma reorder_clause_full_newer_than_values m rm g c m' rm' g' c' :
    reorder_clause_full m rm g c = (m', rm', g', c') ->
    newer_than_values g m -> newer_than_values g' m'.
  Proof.
    elim: c m rm g m' rm' g' c' => [| l c IH] m rm g m' rm' g' c' //=.
    - case=> ? ? ? ?; subst. by apply.
    - dcase (reorder_lit_full m rm g l) => [[[[m1 rm1] g1] l_ro] Hro_l].
      dcase (reorder_clause_full m1 rm1 g1 c) => [[[[m2 rm2] g2] c_ro] Hro_c].
      case=> ? ? ? ?; subst. move=> Hnew. apply: (IH _ _ _ _ _ _ _ Hro_c).
      exact: (reorder_lit_full_newer_than_values Hro_l Hnew).
  Qed.

  Lemma reorder_cnf_rec_full_newer_than_values m rm g c m' rm' g' c' :
    reorder_cnf_rec_full m rm g c = (m', rm', g', c') ->
    newer_than_values g m -> newer_than_values g' m'.
  Proof.
    elim: c m rm g m' rm' g' c' => [| l c IH] m rm g m' rm' g' c' //=.
    - case=> ? ? ? ?; subst. by apply.
    - dcase (reorder_clause_full m rm g l) => [[[[m1 rm1] g1] l_ro] Hro_l].
      dcase (reorder_cnf_rec_full m1 rm1 g1 c) => [[[[m2 rm2] g2] c_ro] Hro_c].
      case=> ? ? ? ?; subst. move=> Hnew. apply: (IH _ _ _ _ _ _ _ Hro_c).
      exact: (reorder_clause_full_newer_than_values Hro_l Hnew).
  Qed.


  Lemma reorder_lit_full_newer_than_keys m rm g l m' rm' g' l' :
    reorder_lit_full m rm g l = (m', rm', g', l') ->
    newer_than_keys g rm -> newer_than_keys g' rm'.
  Proof.
    rewrite /reorder_lit_full. case: l => v.
    - case Hfv: (PM.find v m).
      + case=> ? ? ? ?; subst. by apply.
      + case=> ? ? ? ?; subst. move=> Hnew. move=> u Hmemu.
        rewrite PM.Lemmas.add_b in Hmemu. case/orP: Hmemu => Hmemu.
        * rewrite /PM.Lemmas.eqb in Hmemu. move: Hmemu.
          case: (PM.M.E.eq_dec g u) => //=.
          move/eqP => -> _. exact: Pos.lt_add_r.
        * move: (Hnew _ Hmemu) => Hlt. exact: (pos_lt_add_r _ Hlt).
    - case Hfv: (PM.find v m).
      + case=> ? ? ? ?; subst. by apply.
      + case=> ? ? ? ?; subst. move=> Hnew. move=> u Hmemu.
        rewrite PM.Lemmas.add_b in Hmemu. case/orP: Hmemu => Hmemu.
        * rewrite /PM.Lemmas.eqb in Hmemu. move: Hmemu.
          case: (PM.M.E.eq_dec g u) => //=.
          move/eqP => -> _. exact: Pos.lt_add_r.
        * move: (Hnew _ Hmemu) => Hlt. exact: (pos_lt_add_r _ Hlt).
  Qed.

  Lemma reorder_clause_full_newer_than_keys m rm g c m' rm' g' c' :
    reorder_clause_full m rm g c = (m', rm', g', c') ->
    newer_than_keys g rm -> newer_than_keys g' rm'.
  Proof.
    elim: c m rm g m' rm' g' c' => [| l c IH] m rm g m' rm' g' c' //=.
    - case=> ? ? ? ?; subst. by apply.
    - dcase (reorder_lit_full m rm g l) => [[[[m1 rm1] g1] l_ro] Hro_l].
      dcase (reorder_clause_full m1 rm1 g1 c) => [[[[m2 rm2] g2] c_ro] Hro_c].
      case=> ? ? ? ?; subst. move=> Hnew. apply: (IH _ _ _ _ _ _ _ Hro_c).
      exact: (reorder_lit_full_newer_than_keys Hro_l Hnew).
  Qed.

  Lemma reorder_cnf_rec_full_newer_than_keys m rm g c m' rm' g' c' :
    reorder_cnf_rec_full m rm g c = (m', rm', g', c') ->
    newer_than_keys g rm -> newer_than_keys g' rm'.
  Proof.
    elim: c m rm g m' rm' g' c' => [| l c IH] m rm g m' rm' g' c' //=.
    - case=> ? ? ? ?; subst. by apply.
    - dcase (reorder_clause_full m rm g l) => [[[[m1 rm1] g1] l_ro] Hro_l].
      dcase (reorder_cnf_rec_full m1 rm1 g1 c) => [[[[m2 rm2] g2] c_ro] Hro_c].
      case=> ? ? ? ?; subst. move=> Hnew. apply: (IH _ _ _ _ _ _ _ Hro_c).
      exact: (reorder_clause_full_newer_than_keys Hro_l Hnew).
  Qed.


  Lemma reorder_lit_full_consistent m rm g l m' rm' g' l' :
    reorder_lit_full m rm g l = (m', rm', g', l') ->
    newer_than_values g m ->
    consistent_vm m rm -> consistent_vm m' rm'.
  Proof.
    rewrite /reorder_lit_full /consistent_vm. case l => v.
    - case Hfv: (PM.find v m).
      + case=> ? ? ? ?; subst. move=> Hnv. by apply.
      + case=> ? ? ? ?; subst. move=> Hnv H u u'. split.
        * case Huv: (u == v).
          -- rewrite (PM.Lemmas.find_add_eq Huv). case => ->.
             rewrite (PM.Lemmas.find_add_eq (eqxx u')). by rewrite (eqP Huv).
          -- move/negP: Huv => Hne. rewrite (PM.Lemmas.find_add_neq Hne).
             move=> Hfu. move: (Hnv _ _ Hfu) => Hlt.
             have Hne': ~ u' == g.
             { move=> Heq. rewrite (eqP Heq) in Hlt. exact: (Pos.lt_irrefl _ Hlt). }
             rewrite (PM.Lemmas.find_add_neq Hne'). apply/(H _ _). exact: Hfu.
        * case Hu'g: (u' == g).
          -- rewrite (PM.Lemmas.find_add_eq Hu'g). case=> ?; subst.
             rewrite (PM.Lemmas.find_add_eq (eqxx u)). by rewrite (eqP Hu'g).
          -- move/negP: Hu'g => Hne. rewrite (PM.Lemmas.find_add_neq Hne).
             move=> Hfu'. case Huv: (u == v).
             ++ move/(H _ _): Hfu' => Hfu. rewrite (eqP Huv) Hfv in Hfu.
                discriminate.
             ++ move/negP: Huv => Huv. rewrite (PM.Lemmas.find_add_neq Huv).
                apply/(H _ _). exact: Hfu'.
    - case Hfv: (PM.find v m).
      + case=> ? ? ? ?; subst. move=> Hnv. by apply.
      + case=> ? ? ? ?; subst. move=> Hnv H u u'. split.
        * case Huv: (u == v).
          -- rewrite (PM.Lemmas.find_add_eq Huv). case => ->.
             rewrite (PM.Lemmas.find_add_eq (eqxx u')). by rewrite (eqP Huv).
          -- move/negP: Huv => Hne. rewrite (PM.Lemmas.find_add_neq Hne).
             move=> Hfu. move: (Hnv _ _ Hfu) => Hlt.
             have Hne': ~ u' == g.
             { move=> Heq. rewrite (eqP Heq) in Hlt. exact: (Pos.lt_irrefl _ Hlt). }
             rewrite (PM.Lemmas.find_add_neq Hne'). apply/(H _ _). exact: Hfu.
        * case Hu'g: (u' == g).
          -- rewrite (PM.Lemmas.find_add_eq Hu'g). case=> ?; subst.
             rewrite (PM.Lemmas.find_add_eq (eqxx u)). by rewrite (eqP Hu'g).
          -- move/negP: Hu'g => Hne. rewrite (PM.Lemmas.find_add_neq Hne).
             move=> Hfu'. case Huv: (u == v).
             ++ move/(H _ _): Hfu' => Hfu. rewrite (eqP Huv) Hfv in Hfu.
                discriminate.
             ++ move/negP: Huv => Huv. rewrite (PM.Lemmas.find_add_neq Huv).
                apply/(H _ _). exact: Hfu'.
  Qed.

  Lemma reorder_clause_full_consistent m rm g c m' rm' g' c' :
    reorder_clause_full m rm g c = (m', rm', g', c') ->
    newer_than_values g m ->
    consistent_vm m rm -> consistent_vm m' rm'.
  Proof.
    elim: c m rm g m' rm' g' c' => [| l c IH] m rm g m' rm' g' c' //=.
    - case=> ? ? ? ?; subst. move=> _. by apply.
    - dcase (reorder_lit_full m rm g l) => [[[[m1 rm1] g1] l_ro] Hro_l].
      dcase (reorder_clause_full m1 rm1 g1 c) => [[[[m2 rm2] g2] c_ro] Hro_c].
      case=> ? ? ? ?; subst. move=> Hnv Hcon. apply: (IH _ _ _ _ _ _ _ Hro_c).
      + exact: (reorder_lit_full_newer_than_values Hro_l Hnv).
      + exact: (reorder_lit_full_consistent Hro_l Hnv Hcon).
  Qed.

  Lemma reorder_cnf_rec_full_consistent m rm g c m' rm' g' c' :
    reorder_cnf_rec_full m rm g c = (m', rm', g', c') ->
    newer_than_values g m ->
    consistent_vm m rm -> consistent_vm m' rm'.
  Proof.
    elim: c m rm g m' rm' g' c' => [| l c IH] m rm g m' rm' g' c' //=.
    - case=> ? ? ? ?; subst. move=> _. by apply.
    - dcase (reorder_clause_full m rm g l) => [[[[m1 rm1] g1] l_ro] Hro_l].
      dcase (reorder_cnf_rec_full m1 rm1 g1 c) => [[[[m2 rm2] g2] c_ro] Hro_c].
      case=> ? ? ? ?; subst. move=> Hnv Hcon. apply: (IH _ _ _ _ _ _ _ Hro_c).
      + exact: (reorder_clause_full_newer_than_values Hro_l Hnv).
      + exact: (reorder_clause_full_consistent Hro_l Hnv Hcon).
  Qed.


  Definition vm_preserve (m1 m2 : PM.t positive) :=
    PM.Lemmas.submap m1 m2.

  Lemma vm_preserve_mem m1 m2 v :
    vm_preserve m1 m2 -> PM.mem v m1 -> PM.mem v m2.
  Proof.
    move=> Hpre Hmem1. move: (PM.Lemmas.mem_find_some Hmem1) => [v' Hfv].
    move: (Hpre _ _ Hfv) => Hfv2. exact: (PM.Lemmas.find_some_mem Hfv2).
  Qed.

  Lemma newer_than_keys_vm_preserve m g v :
    newer_than_keys g m -> vm_preserve m (PM.add g v m).
  Proof.
    move=> Hnk x y Hfx. move: (PM.Lemmas.find_some_mem Hfx) => Hmem.
    move: (Hnk _ Hmem) => Hlt. have Hne: ~ x == g.
    { move=> Heq. rewrite (eqP Heq) in Hlt. exact: (Pos.lt_irrefl _ Hlt). }
    rewrite (PM.Lemmas.find_add_neq Hne). assumption.
  Qed.

  Lemma vm_preserve_interp_lit E m1 m2 l :
    vm_preserve m1 m2 -> PM.mem (var_of_lit l) m1 ->
    interp_lit (reorder_upd_env E m1) l = interp_lit (reorder_upd_env E m2) l.
  Proof.
    rewrite /interp_lit /reorder_upd_env. move=> Hpre Hmem.
    move: (PM.Lemmas.mem_find_some Hmem) => {Hmem} [v' Hfv].
    case: l Hfv => /= v Hfv.
    - rewrite Hfv. rewrite (Hpre v _ Hfv). reflexivity.
    - rewrite Hfv. rewrite (Hpre v _ Hfv). reflexivity.
  Qed.

  Lemma vm_preserve_interp_clause E m1 m2 c :
    vm_preserve m1 m2 ->
    (forall l : lit_eqType, l \in c -> PM.mem (var_of_lit l) m1) ->
    interp_clause (reorder_upd_env E m1) c = interp_clause (reorder_upd_env E m2) c.
  Proof.
    move=> Hpre. elim: c => [| l c IH] //=. move=> Hmem.
    have Hin: (l \in l :: c) by rewrite in_cons eqxx orTb.
    rewrite (vm_preserve_interp_lit E Hpre (Hmem l Hin)).
    have Hmemc: forall l0 : literal, l0 \in c -> PM.mem (var_of_lit l0) m1.
    { move=> x Hinx. apply: Hmem. by rewrite in_cons Hinx orbT. }
    rewrite (IH Hmemc). reflexivity.
  Qed.

  Lemma reorder_lit_full_preserve m rm g l m' rm' g' l' :
    reorder_lit_full m rm g l = (m', rm', g', l') ->
    vm_preserve m m'.
  Proof.
    rewrite /reorder_lit_full. case: l => v.
    - case Hfv: (PM.find v m).
      + case=> ? ? ? ?; subst. exact: PM.Lemmas.submap_refl.
      + case=> ? ? ? ?; subst. apply: (PM.Lemmas.submap_none_add _ _ Hfv).
        exact: PM.Lemmas.submap_refl.
    - case Hfv: (PM.find v m).
      + case=> ? ? ? ?; subst. exact: PM.Lemmas.submap_refl.
      + case=> ? ? ? ?; subst. apply: (PM.Lemmas.submap_none_add _ _ Hfv).
        exact: PM.Lemmas.submap_refl.
  Qed.

  Lemma reorder_clause_full_preserve m rm g c m' rm' g' c' :
    reorder_clause_full m rm g c = (m', rm', g', c') ->
    vm_preserve m m'.
  Proof.
    elim: c m rm g m' rm' g' c' => [| l c IH] m rm g m' rm' g' c' /=.
    - case=> ? ? ? ?; subst. exact: PM.Lemmas.submap_refl.
    - dcase (reorder_lit_full m rm g l) => [[[[m1 rm1] g1] l_ro] Hro_l].
      dcase (reorder_clause_full m1 rm1 g1 c) => [[[[m2 rm2] g2] c_ro] Hro_c].
      case=> ? ? ? ?; subst.
      apply: (PM.Lemmas.submap_trans _ (IH _ _ _ _ _ _ _ Hro_c)).
      exact: (reorder_lit_full_preserve Hro_l).
  Qed.

  Lemma reorder_cnf_rec_full_preserve m rm g c m' rm' g' c' :
    reorder_cnf_rec_full m rm g c = (m', rm', g', c') ->
    vm_preserve m m'.
  Proof.
    elim: c m rm g m' rm' g' c' => [| l c IH] m rm g m' rm' g' c' //=.
    - case=> ? ? ? ?; subst. exact: PM.Lemmas.submap_refl.
    - dcase (reorder_clause_full m rm g l) => [[[[m1 rm1] g1] l_ro] Hro_l].
      dcase (reorder_cnf_rec_full m1 rm1 g1 c) => [[[[m2 rm2] g2] c_ro] Hro_c].
      case=> ? ? ? ?; subst.
      apply: (PM.Lemmas.submap_trans _ (IH _ _ _ _ _ _ _ Hro_c)).
      exact: (reorder_clause_full_preserve Hro_l).
  Qed.

  Lemma reorder_lit_full_preserver m rm g l m' rm' g' l' :
    newer_than_keys g rm ->
    reorder_lit_full m rm g l = (m', rm', g', l') ->
    vm_preserve rm rm'.
  Proof.
    rewrite /reorder_lit_full. move=> Hnk. case: l => v.
    - case Hfv: (PM.find v m).
      + case=> ? ? ? ?; subst. exact: PM.Lemmas.submap_refl.
      + case=> ? ? ? ?; subst. exact: (newer_than_keys_vm_preserve _ Hnk).
    - case Hfv: (PM.find v m).
      + case=> ? ? ? ?; subst. exact: PM.Lemmas.submap_refl.
      + case=> ? ? ? ?; subst. exact: (newer_than_keys_vm_preserve _ Hnk).
  Qed.

  Lemma reorder_clause_full_preserver m rm g c m' rm' g' c' :
    newer_than_keys g rm ->
    reorder_clause_full m rm g c = (m', rm', g', c') ->
    vm_preserve rm rm'.
  Proof.
    elim: c m rm g m' rm' g' c' => [| l c IH] m rm g m' rm' g' c' /= Hnk.
    - case=> ? ? ? ?; subst. exact: PM.Lemmas.submap_refl.
    - dcase (reorder_lit_full m rm g l) => [[[[m1 rm1] g1] l_ro] Hro_l].
      dcase (reorder_clause_full m1 rm1 g1 c) => [[[[m2 rm2] g2] c_ro] Hro_c].
      case=> ? ? ? ?; subst.
      move: (reorder_lit_full_newer_than_keys Hro_l Hnk) => Hnk1.
      apply: (PM.Lemmas.submap_trans _ (IH m1 rm1 _ _ _ _ _ Hnk1 Hro_c)).
      exact: (reorder_lit_full_preserver Hnk Hro_l).
  Qed.

  Lemma reorder_cnf_rec_full_preserver m rm g c m' rm' g' c' :
    newer_than_keys g rm ->
    reorder_cnf_rec_full m rm g c = (m', rm', g', c') ->
    vm_preserve rm rm'.
  Proof.
    elim: c m rm g m' rm' g' c' => [| l c IH] m rm g m' rm' g' c' //= Hnk.
    - case=> ? ? ? ?; subst. exact: PM.Lemmas.submap_refl.
    - dcase (reorder_clause_full m rm g l) => [[[[m1 rm1] g1] l_ro] Hro_l].
      dcase (reorder_cnf_rec_full m1 rm1 g1 c) => [[[[m2 rm2] g2] c_ro] Hro_c].
      case=> ? ? ? ?; subst.
      move: (reorder_clause_full_newer_than_keys Hro_l Hnk) => Hnk1.
      apply: (PM.Lemmas.submap_trans _ (IH _ _ _ _ _ _ _ Hnk1 Hro_c)).
      exact: (reorder_clause_full_preserver Hnk Hro_l).
  Qed.


  Lemma reorder_lit_full_mem m rm g l m' rm' g' l' :
    reorder_lit_full m rm g l = (m', rm', g', l') ->
    PM.mem (var_of_lit l) m'.
  Proof.
    rewrite /reorder_lit_full /var_of_lit. case: l => v.
    - case Hfv: (PM.find v m).
      + case=> ? ? ? ?; subst. exact (PM.Lemmas.find_some_mem Hfv).
      + case=> ? ? ? ?; subst. exact: (PM.Lemmas.mem_add_eq (eqxx v)).
    - case Hfv: (PM.find v m).
      + case=> ? ? ? ?; subst. exact (PM.Lemmas.find_some_mem Hfv).
      + case=> ? ? ? ?; subst. exact: (PM.Lemmas.mem_add_eq (eqxx v)).
  Qed.

  Lemma reorder_clause_full_mem m rm g c m' rm' g' c' :
    reorder_clause_full m rm g c = (m', rm', g', c') ->
    forall l, l \in c -> PM.mem (var_of_lit l) m'.
  Proof.
    elim: c m rm g m' rm' g' c' => [| l c IH] m rm g m' rm' g' c' //=.
    dcase (reorder_lit_full m rm g l) => [[[[m1 rm1] g1] l_ro] Hro_l].
    dcase (reorder_clause_full m1 rm1 g1 c) => [[[[m2 rm2] g2] c_ro] Hro_c].
    case=> ? ? ? ?; subst. move=> l' Hin'. rewrite in_cons in Hin'. case/orP: Hin'.
    - move/eqP => ->. move: (reorder_lit_full_mem Hro_l) => Hmem1.
      move: (reorder_clause_full_preserve Hro_c) => Hpre.
      exact: (vm_preserve_mem Hpre Hmem1).
    - move=> Hin. exact: (IH _ _ _ _ _ _ _ Hro_c _ Hin).
  Qed.

  Lemma reorder_cn_full_mem m rm g cs m' rm' g' cs' :
    reorder_cnf_rec_full m rm g cs = (m', rm', g', cs') ->
    forall c l, c \in cs -> l \in c -> PM.mem (var_of_lit l) m'.
  Proof.
    elim: cs m rm g m' rm' g' cs' => [| c cs IH] m rm g m' rm' g' cs' //=.
    dcase (reorder_clause_full m rm g c) => [[[[m1 rm1] g1] c_ro] Hc_ro].
    dcase (reorder_cnf_rec_full m1 rm1 g1 cs) => [[[[m2 rm2] g2] cs_ro] Hcs_ro].
    case=> ? ? ? ?; subst. move=> c' l' Hc' Hl'.
    rewrite in_cons in Hc'. case/orP: Hc' => Hc'.
    - move/eqP: Hc' => Hc'. subst.
      move: (reorder_clause_full_mem Hc_ro Hl') => Hmem1.
      move: (reorder_cnf_rec_full_preserve Hcs_ro) => Hpre.
      exact: (vm_preserve_mem Hpre Hmem1).
    - exact: (IH _ _ _ _ _ _ _ Hcs_ro _ _ Hc' Hl').
  Qed.


  Lemma reorder_lit_full_memr m rm g l m' rm' g' l' :
    consistent_vm m rm ->
    reorder_lit_full m rm g l = (m', rm', g', l') ->
    PM.mem (var_of_lit l') rm'.
  Proof.
    rewrite /reorder_lit_full /var_of_lit. move=> Hcon. case: l => v.
    - case Hfv: (PM.find v m).
      + case=> ? ? ? ?; subst. move/Hcon: Hfv => Hfv.
        exact (PM.Lemmas.find_some_mem Hfv).
      + case=> ? ? ? ?; subst. exact: (PM.Lemmas.mem_add_eq (eqxx g)).
    - case Hfv: (PM.find v m).
      + case=> ? ? ? ?; subst. move/Hcon: Hfv => Hfv.
        exact (PM.Lemmas.find_some_mem Hfv).
      + case=> ? ? ? ?; subst. exact: (PM.Lemmas.mem_add_eq (eqxx g)).
  Qed.

  Lemma reorder_clause_full_memr m rm g c m' rm' g' c' :
    consistent_vm m rm -> newer_than_values g m ->
    reorder_clause_full m rm g c = (m', rm', g', c') ->
    forall l, l \in c' -> PM.mem (var_of_lit l) rm'.
  Proof.
    elim: c m rm g m' rm' g' c' => [| l c IH] m rm g m' rm' g' c' //= Hcon Hnv.
    - case=> ? ? ? ?; subst. discriminate.
    - dcase (reorder_lit_full m rm g l) => [[[[m1 rm1] g1] l_ro] Hro_l].
      dcase (reorder_clause_full m1 rm1 g1 c) => [[[[m2 rm2] g2] c_ro] Hro_c].
      case=> ? ? ? ?; subst. move=> l' Hin'. rewrite in_cons in Hin'. case/orP: Hin'.
      + move/eqP => ->. move: (reorder_lit_full_memr Hcon Hro_l) => Hmem1.
        move/(consistent_vm_newer_than _ Hcon): Hnv => Hnk.
        move: (reorder_lit_full_newer_than_keys Hro_l Hnk) => Hnk1.
        move: (reorder_clause_full_preserver Hnk1 Hro_c) => Hpre.
        exact: (vm_preserve_mem Hpre Hmem1).
      + move=> Hin.
        move: (reorder_lit_full_consistent Hro_l Hnv Hcon) => Hcon1.
        move: (reorder_lit_full_newer_than_values Hro_l Hnv) => Hnv1.
        exact: (IH _ _ _ _ _ _ _ Hcon1 Hnv1 Hro_c _ Hin).
  Qed.

  Lemma reorder_cn_full_memr m rm g cs m' rm' g' cs' :
    consistent_vm m rm -> newer_than_values g m ->
    reorder_cnf_rec_full m rm g cs = (m', rm', g', cs') ->
    forall c l, c \in cs' -> l \in c -> PM.mem (var_of_lit l) rm'.
  Proof.
    elim: cs m rm g m' rm' g' cs' => [| c cs IH] m rm g m' rm' g' cs' //= Hcon Hnv.
    - case=> ? ? ? ?; subst. discriminate.
    - dcase (reorder_clause_full m rm g c) => [[[[m1 rm1] g1] c_ro] Hc_ro].
      dcase (reorder_cnf_rec_full m1 rm1 g1 cs) => [[[[m2 rm2] g2] cs_ro] Hcs_ro].
      case=> ? ? ? ?; subst. move=> c' l' Hc' Hl'.
      rewrite in_cons in Hc'. case/orP: Hc' => Hc'.
      + move/eqP: Hc' => Hc'. subst.
        move: (reorder_clause_full_memr Hcon Hnv Hc_ro Hl') => Hmem1.
        move/(consistent_vm_newer_than _ Hcon): Hnv => Hnk.
        move: (reorder_clause_full_newer_than_keys Hc_ro Hnk) => Hnk1.
        move: (reorder_cnf_rec_full_preserver Hnk1 Hcs_ro) => Hpre.
        exact: (vm_preserve_mem Hpre Hmem1).
      + move: (reorder_clause_full_consistent Hc_ro Hnv Hcon) => Hcon1.
        move: (reorder_clause_full_newer_than_values Hc_ro Hnv) => Hnv1.
        exact: (IH _ _ _ _ _ _ _ Hcon1 Hnv1 Hcs_ro _ _ Hc' Hl').
  Qed.


  Lemma reorder_lit_full_update_sat E m rm g l m' rm' g' l' :
    reorder_lit_full m rm g l = (m', rm', g', l') ->
    interp_lit (reorder_upd_env E m') l = interp_lit E l'.
  Proof.
    rewrite /reorder_lit_full /interp_lit /reorder_upd_env.
    case: l => v /=.
    - case Hfind: (PM.find v m).
      + case=> ? ? ? ?; subst. rewrite Hfind. reflexivity.
      + case=> ? ? ? ?; subst. rewrite (PM.Lemmas.find_add_eq (eqxx v)). reflexivity.
    - case Hfind: (PM.find v m).
      + case=> ? ? ? ?; subst. rewrite Hfind. reflexivity.
      + case=> ? ? ? ?; subst. rewrite (PM.Lemmas.find_add_eq (eqxx v)). reflexivity.
  Qed.

  Lemma reorder_clause_full_update_sat E m rm g c m' rm' g' c' :
    reorder_clause_full m rm g c = (m', rm', g', c') ->
    interp_clause (reorder_upd_env E m') c = interp_clause E c'.
  Proof.
    elim: c m rm g m' rm' g' c' => [| l c IH] m rm g m' rm' g' c' //=.
    - case=> ? ? ? ?; subst. reflexivity.
    - dcase (reorder_lit_full m rm g l) => [[[[m1 rm1] g1] l_ro] Hro_l].
      dcase (reorder_clause_full m1 rm1 g1 c) => [[[[m2 rm2] g2] c_ro] Hro_c].
      case=> ? ? ? ?; subst. rewrite interp_clause_cons.
      move: (reorder_lit_full_mem Hro_l) => Hmem.
      move: (reorder_clause_full_preserve Hro_c) => Hpre.
      rewrite -(vm_preserve_interp_lit _ Hpre Hmem).
      rewrite (IH _ _ _ _ _ _ _ Hro_c).
      rewrite (reorder_lit_full_update_sat E Hro_l). reflexivity.
  Qed.

  Lemma reorder_cnf_rec_full_update_sat E m rm g cs m' rm' g' cs' :
    reorder_cnf_rec_full m rm g cs = (m', rm', g', cs') ->
    interp_cnf (reorder_upd_env E m') cs = interp_cnf E cs'.
  Proof.
    elim: cs m rm g m' rm' g' cs' => [| c cs IH] m rm g m' rm' g' cs' //=.
    - case=> ? ? ? ?; subst. reflexivity.
    - dcase (reorder_clause_full m rm g c) => [[[[m1 rm1] g1] c_ro] Hro_c].
      dcase (reorder_cnf_rec_full m1 rm1 g1 cs) => [[[[m2 rm2] g2] cs_ro] Hro_cs].
      case=> ? ? ? ?; subst. rewrite interp_cnf_cons.
      move: (reorder_clause_full_mem Hro_c) => Hmem.
      move: (reorder_cnf_rec_full_preserve Hro_cs) => Hpre.
      rewrite -(vm_preserve_interp_clause E Hpre Hmem).
      rewrite (reorder_clause_full_update_sat E Hro_c).
      rewrite (IH _ _ _ _ _ _ _ Hro_cs). reflexivity.
  Qed.


  Lemma reorder_lit_full_satr E m rm g l m' rm' g' l' :
    consistent_vm m rm ->
    reorder_lit_full m rm g l = (m', rm', g', l') ->
    interp_lit (reorder_upd_env E rm') l' = interp_lit E l.
  Proof.
    rewrite /reorder_lit_full /interp_lit /reorder_upd_env.
    move=> Hcon. case: l => v /=.
    - case Hfind: (PM.find v m).
      + case=> ? ? ? ?; subst. move/Hcon: Hfind => Hfind.
        rewrite Hfind. reflexivity.
      + case=> ? ? ? ?; subst. rewrite (PM.Lemmas.find_add_eq (eqxx g)).
        reflexivity.
    - case Hfind: (PM.find v m).
      + case=> ? ? ? ?; subst. move/Hcon: Hfind => Hfind.
        rewrite Hfind. reflexivity.
      + case=> ? ? ? ?; subst. rewrite (PM.Lemmas.find_add_eq (eqxx g)).
        reflexivity.
  Qed.

  Lemma reorder_clause_full_satr E m rm g c m' rm' g' c' :
    consistent_vm m rm -> newer_than_values g m ->
    reorder_clause_full m rm g c = (m', rm', g', c') ->
    interp_clause (reorder_upd_env E rm') c' = interp_clause E c.
  Proof.
    elim: c m rm g m' rm' g' c' => [| l c IH] m rm g m' rm' g' c' //= Hcon Hnv.
    - case=> ? ? ? ?; subst. reflexivity.
    - dcase (reorder_lit_full m rm g l) => [[[[m1 rm1] g1] l_ro] Hro_l].
      dcase (reorder_clause_full m1 rm1 g1 c) => [[[[m2 rm2] g2] c_ro] Hro_c].
      case=> ? ? ? ?; subst. rewrite interp_clause_cons.
      move: (reorder_lit_full_memr Hcon Hro_l) => Hmem.
      move: (reorder_lit_full_consistent Hro_l Hnv Hcon) => Hcon1.
      move: (reorder_lit_full_newer_than_values Hro_l Hnv) => Hnv1.
      move/(consistent_vm_newer_than _ Hcon1): (Hnv1) => Hnk1.
      move: (reorder_clause_full_preserver Hnk1 Hro_c) => Hpre.
      rewrite -(vm_preserve_interp_lit _ Hpre Hmem).
      rewrite (IH _ _ _ _ _ _ _ Hcon1 Hnv1 Hro_c).
      rewrite (reorder_lit_full_satr E Hcon Hro_l). reflexivity.
  Qed.

  Lemma reorder_cnf_rec_full_satr E m rm g cs m' rm' g' cs' :
    consistent_vm m rm -> newer_than_values g m ->
    reorder_cnf_rec_full m rm g cs = (m', rm', g', cs') ->
    interp_cnf (reorder_upd_env E rm') cs' = interp_cnf E cs.
  Proof.
    elim: cs m rm g m' rm' g' cs' => [| c cs IH] m rm g m' rm' g' cs' //= Hcon Hnv.
    - case=> ? ? ? ?; subst. reflexivity.
    - dcase (reorder_clause_full m rm g c) => [[[[m1 rm1] g1] c_ro] Hro_c].
      dcase (reorder_cnf_rec_full m1 rm1 g1 cs) => [[[[m2 rm2] g2] cs_ro] Hro_cs].
      case=> ? ? ? ?; subst. rewrite interp_cnf_cons.
      move: (reorder_clause_full_memr Hcon Hnv Hro_c) => Hmem.
      move: (reorder_clause_full_consistent Hro_c Hnv Hcon) => Hcon1.
      move: (reorder_clause_full_newer_than_values Hro_c Hnv) => Hnv1.
      move/(consistent_vm_newer_than _ Hcon1): (Hnv1) => Hnk1.
      move: (reorder_cnf_rec_full_preserver Hnk1 Hro_cs) => Hpre.
      rewrite -(vm_preserve_interp_clause _ Hpre Hmem).
      rewrite (IH _ _ _ _ _ _ _ Hcon1 Hnv1 Hro_cs).
      rewrite (reorder_clause_full_satr E Hcon Hnv Hro_c). reflexivity.
  Qed.


  Lemma reorder_cnf_rec_full_sound E' m rm g cs m' rm' g' cs' :
    reorder_cnf_rec_full m rm g cs = (m', rm', g', cs') ->
    interp_cnf E' cs' -> exists E, interp_cnf E cs.
  Proof.
    move=> Hro Hcnf. exists (reorder_upd_env E' m').
    rewrite (reorder_cnf_rec_full_update_sat E' Hro). assumption.
  Qed.

  Lemma reorder_cnf_rec_full_complete E m rm g cs m' rm' g' cs' :
    consistent_vm m rm -> newer_than_values g m ->
    reorder_cnf_rec_full m rm g cs = (m', rm', g', cs') ->
    interp_cnf E cs -> exists E', interp_cnf E' cs'.
  Proof.
    move=> Hcon Hnv Hro Hcnf. exists (reorder_upd_env E rm').
    rewrite (reorder_cnf_rec_full_satr E Hcon Hnv Hro). assumption.
  Qed.


  Lemma reorder_lit_full_partial m rm g l m' rm' g' l' :
    reorder_lit_full m rm g l = (m', rm', g', l') ->
    reorder_lit m g l = (m', g', l').
  Proof.
    rewrite /reorder_lit_full /reorder_lit. case: l => v //=.
    - case Hfv: (PM.find v m).
      + case=> ? ? ? ?; subst. reflexivity.
      + case=> ? ? ? ?; subst. reflexivity.
    - case Hfv: (PM.find v m).
      + case=> ? ? ? ?; subst. reflexivity.
      + case=> ? ? ? ?; subst. reflexivity.
  Qed.

  Lemma reorder_clause_full_partial m rm g c m' rm' g' c' :
    reorder_clause_full m rm g c = (m', rm', g', c') ->
    reorder_clause m g c = (m', g', c').
  Proof.
    elim: c m rm g m' rm' g' c' => [| l c IH] m rm g m' rm' g' c' //=.
    - case=> ? ? ? ?; subst. reflexivity.
    - dcase (reorder_lit_full m rm g l) => [[[[m1 rm1] g1] l_ro] Hro_l].
      dcase (reorder_clause_full m1 rm1 g1 c) => [[[[m2 rm2] g2] c_ro] Hro_c].
      case=> ? ? ? ?; subst.
      dcase (reorder_lit m g l) => [[[m1' g1'] l_ro'] Hro_l'].
      dcase (reorder_clause m1' g1' c) => [[[m2' g2'] c_ro'] Hro_c'].
      move: (reorder_lit_full_partial Hro_l) => Hro_l''.
      rewrite Hro_l' in Hro_l''. case: Hro_l'' => ? ? ?; subst.
      move: (IH _ _ _ _ _ _ _ Hro_c) => Hro_c''. rewrite Hro_c' in Hro_c''.
      case: Hro_c'' => ? ? ?; subst. reflexivity.
  Qed.

  Lemma reorder_cnf_rec_full_partial m rm g cs m' rm' g' cs' :
    reorder_cnf_rec_full m rm g cs = (m', rm', g', cs') ->
    reorder_cnf_rec m g cs = (m', g', cs').
  Proof.
    elim: cs m rm g m' rm' g' cs' => [| c cs IH] m rm g m' rm' g' cs' //=.
    - case=> ? ? ? ?; subst. reflexivity.
    - dcase (reorder_clause_full m rm g c) => [[[[m1 rm1] g1] c_ro] Hro_c].
      dcase (reorder_cnf_rec_full m1 rm1 g1 cs) => [[[[m2 rm2] g2] cs_ro] Hro_cs].
      case=> ? ? ? ?; subst.
      dcase (reorder_clause m g c) => [[[m1' g1'] c_ro'] Hro_c'].
      dcase (reorder_cnf_rec m1' g1' cs) => [[[m2' g2'] cs_ro'] Hro_cs'].
      move: (reorder_clause_full_partial Hro_c) => Hro_c''.
      rewrite Hro_c' in Hro_c''. case: Hro_c'' => ? ? ?; subst.
      move: (IH _ _ _ _ _ _ _ Hro_cs) => Hro_cs''. rewrite Hro_cs' in Hro_cs''.
      case: Hro_cs'' => ? ? ?; subst. reflexivity.
  Qed.

  Definition init_m := PM.empty positive.
  Definition init_g := 1%positive.

  Definition reorder_cnf cs :=
    let '(_, _, cs') := reorder_cnf_rec init_m init_g cs in
    cs'.

  Theorem reorder_cnf_sound E' cs :
    interp_cnf E' (reorder_cnf cs) -> exists E, interp_cnf E cs.
  Proof.
    rewrite /reorder_cnf.
    dcase (reorder_cnf_rec init_m init_g cs) => [[[m' g'] cs'] Hro].
    dcase (reorder_cnf_rec_full init_m init_m init_g cs) =>
    [[[[m'' rm''] g''] cs''] Hro'].
    rewrite (reorder_cnf_rec_full_partial Hro') in Hro. case: Hro => ? ? ?; subst.
    exact: (reorder_cnf_rec_full_sound Hro').
  Qed.

  Theorem reorder_cnf_complete E cs :
    interp_cnf E cs -> exists E', interp_cnf E' (reorder_cnf cs).
  Proof.
    rewrite /reorder_cnf.
    dcase (reorder_cnf_rec init_m init_g cs) => [[[m' g'] cs'] Hro].
    dcase (reorder_cnf_rec_full init_m init_m init_g cs) =>
    [[[[m'' rm''] g''] cs''] Hro'].
    rewrite (reorder_cnf_rec_full_partial Hro') in Hro. case: Hro => ? ? ?; subst.
    by apply: (reorder_cnf_rec_full_complete _ _ Hro').
  Qed.

  Corollary reorder_cnf_eqsat cs : sat cs <-> sat (reorder_cnf cs).
  Proof.
    split.
    - move=> [E Hs]. exact: (reorder_cnf_complete Hs).
    - move=> [E Hs]. exact: (reorder_cnf_sound Hs).
  Qed.


  Lemma interp_cnf_rev_eqsat E cs :
    interp_cnf E (rev cs) = interp_cnf E cs.
  Proof.
    elim: cs => [| c cs IH] //=. rewrite rev_cons. rewrite interp_cnf_rcons_cons.
    rewrite interp_cnf_cons. rewrite IH. reflexivity.
  Qed.

  Lemma rev_cnf_eqsat cs : sat cs <-> sat (rev cs).
  Proof.
    split.
    - move=> [E Hs]. exists E. rewrite interp_cnf_rev_eqsat. assumption.
    - move=> [E Hs]. exists E. rewrite -interp_cnf_rev_eqsat. assumption.
  Qed.

End Reorder.


Section EqSat.

  Definition clause_eqsat (cs1 cs2 : clause) : Prop :=
    forall E, interp_clause E cs1 = interp_clause E cs2.

  Definition clause_eqsat_refl cs : clause_eqsat cs cs.
  Proof. move=> E. reflexivity. Qed.

  Definition clause_eqsat_sym cs1 cs2 :
    clause_eqsat cs1 cs2 -> clause_eqsat cs2 cs1.
  Proof. move=> H12 E. rewrite (H12 E). reflexivity. Qed.

  Definition clause_eqsat_trans cs1 cs2 cs3 :
    clause_eqsat cs1 cs2 -> clause_eqsat cs2 cs3 -> clause_eqsat cs1 cs3.
  Proof. move=> H12 H23 E. rewrite (H12 E) (H23 E). reflexivity. Qed.

  Instance clause_eqsat_equivalence : Equivalence clause_eqsat :=
    { Equivalence_Reflexive := clause_eqsat_refl;
      Equivalence_Symmetric := clause_eqsat_sym;
      Equivalence_Transitive := clause_eqsat_trans }.


  Definition cnf_eqsat (cs1 cs2 : cnf) : Prop :=
    forall E, interp_cnf E cs1 = interp_cnf E cs2.

  Definition cnf_eqsat_refl cs : cnf_eqsat cs cs.
  Proof. move=> E. reflexivity. Qed.

  Definition cnf_eqsat_sym cs1 cs2 : cnf_eqsat cs1 cs2 -> cnf_eqsat cs2 cs1.
  Proof. move=> H12 E. rewrite (H12 E). reflexivity. Qed.

  Definition cnf_eqsat_trans cs1 cs2 cs3 :
    cnf_eqsat cs1 cs2 -> cnf_eqsat cs2 cs3 -> cnf_eqsat cs1 cs3.
  Proof. move=> H12 H23 E. rewrite (H12 E) (H23 E). reflexivity. Qed.

  Instance cnf_eqsat_equivalence : Equivalence cnf_eqsat :=
    { Equivalence_Reflexive := cnf_eqsat_refl;
      Equivalence_Symmetric := cnf_eqsat_sym;
      Equivalence_Transitive := cnf_eqsat_trans }.

  Lemma cnf_eqsat_sat es1 es2 :
    cnf_eqsat es1 es2 -> sat es1 <-> sat es2.
  Proof.
    move=> H; split; move=> [E Hsat].
    - exists E. rewrite -(H E). assumption.
    - exists E. rewrite (H E). assumption.
  Qed.

  Lemma cnf_eqsat_cons c1 cs1 c2 cs2 :
    clause_eqsat c1 c2 -> cnf_eqsat cs1 cs2 ->
    cnf_eqsat (c1::cs1) (c2::cs2).
  Proof. move=> Hc Hcs E /=. rewrite (Hc E) (Hcs E). reflexivity. Qed.

  Lemma cnf_eqsat_add_prelude_interp_cnf E cs1 cs2 :
    cnf_eqsat cs1 cs2 ->
    interp_cnf E (add_prelude cs1) = interp_cnf E (add_prelude cs2).
  Proof.
    move=> Heqs. rewrite !add_prelude_expand. rewrite (Heqs E). reflexivity.
  Qed.

  Lemma cnf_eqsat_add_prelude_sat cs1 cs2 :
    cnf_eqsat cs1 cs2 ->
    sat (add_prelude cs1) <-> sat (add_prelude cs2).
  Proof.
    move=> Heqs. split; move=> [E Hs]; exists E.
    - rewrite -(cnf_eqsat_add_prelude_interp_cnf _ Heqs). assumption.
    - rewrite (cnf_eqsat_add_prelude_interp_cnf _ Heqs). assumption.
  Qed.


  Lemma eq_mem_cnf_eqsat cs1 cs2 :
    cs1 =i cs2 -> cnf_eqsat cs1 cs2.
  Proof.
    move=> H E. rewrite /interp_cnf. case H2: (all (interp_clause E) cs2).
    - apply/allP => c Hin. move/allP: H2=> H2.
      rewrite H in Hin. exact: (H2 c Hin).
    - apply/negP=> H1. move/negP: H2; apply. apply/allP => c Hin. move/allP: H1=> H1.
      rewrite -H in Hin. exact: (H1 c Hin).
  Qed.

  Lemma cnf_eqsat_rev cs : cnf_eqsat (rev cs) cs.
  Proof. apply: eq_mem_cnf_eqsat. exact: mem_rev. Qed.

  Lemma interp_cnf_tflatten_cons E c cs :
    interp_cnf E (tflatten (c::cs)) = interp_cnf E c && interp_cnf E (tflatten cs).
  Proof.
    rewrite tflatten_cons. rewrite interp_cnf_cat. rewrite andbC.
    rewrite interp_cnf_rev_eqsat. reflexivity.
  Qed.

  Lemma interp_cnf_add_prelude_tflatten_cons E cs css :
    interp_cnf E (add_prelude (tflatten (cs :: css))) =
    interp_cnf E (add_prelude cs) && interp_cnf E (add_prelude (tflatten css)).
  Proof.
    rewrite !add_prelude_expand. rewrite interp_cnf_tflatten_cons.
      by case: (interp_lit E lit_tt) => //=.
  Qed.

  Lemma interp_cnf_tflatten_catrev E cs1 cs2 :
    interp_cnf E (tflatten (catrev cs1 cs2)) = interp_cnf E (tflatten cs1) &&
                                               interp_cnf E (tflatten cs2).
  Proof.
    elim: cs1 cs2 => [| c1 cs1 IH] cs2 //=.
    rewrite IH. rewrite !interp_cnf_tflatten_cons. case: (interp_cnf E c1) => //=.
    rewrite andbF. reflexivity.
  Qed.

  Lemma tflatten_singleton_eqsat cs :
    cnf_eqsat (tflatten [:: cs]) cs.
  Proof. rewrite /tflatten /=. rewrite -/(rev cs). exact: cnf_eqsat_rev. Qed.

  Lemma tflatten_catrev_eqsat ecs1 ecs2 cs1 cs2 :
    cnf_eqsat (tflatten ecs1) cs1 ->
    cnf_eqsat (tflatten ecs2) cs2 ->
    cnf_eqsat (tflatten (catrev ecs1 ecs2)) (catrev cs1 cs2).
  Proof.
    move=> H1 H2 E. rewrite interp_cnf_catrev. rewrite interp_cnf_tflatten_catrev.
    rewrite (H1 E) (H2 E). reflexivity.
  Qed.

  Lemma tflatten_cons_catrev_eqsat ec ecs c cs :
    cnf_eqsat ec c -> cnf_eqsat (tflatten ecs) cs ->
    cnf_eqsat (tflatten (ec :: ecs)) (catrev c cs).
  Proof.
    move=> Hc Hcs. move=> E. rewrite interp_cnf_tflatten_cons.
    rewrite interp_cnf_catrev. rewrite (Hc E) (Hcs E). reflexivity.
  Qed.

  Lemma interp_cnf_add_prelude E cs1 cs2 :
    interp_cnf E cs1 = interp_cnf E cs2 ->
    interp_cnf E (add_prelude cs1) = interp_cnf E (add_prelude cs2).
  Proof.
    move=> H. rewrite !add_prelude_expand. by case: (interp_lit E lit_tt) => //=.
  Qed.

  Lemma cnf_eqsat_add_prelude cs1 cs2 :
    cnf_eqsat cs1 cs2 -> cnf_eqsat (add_prelude cs1) (add_prelude cs2).
  Proof.
    move=> H E. apply: interp_cnf_add_prelude. rewrite (H E). reflexivity.
  Qed.

End EqSat.

Section EqNew.

  Definition lit_eqnew (l1 l2 : literal) : Prop :=
    forall g, newer_than_lit g l1 = newer_than_lit g l2.

  Definition lits_eqnew (c1 c2 : clause) : Prop :=
    forall g, newer_than_lits g c1 = newer_than_lits g c2.

  Definition cnf_eqnew (cs1 cs2 : cnf) : Prop :=
    forall g, newer_than_cnf g cs1 = newer_than_cnf g cs2.

  Lemma all_newer_than_lits_empty c : (forall g, newer_than_lits g c) -> c = [::].
  Proof.
    elim: c => [| l c IH] //=. case: l.
    - move=> v. move=> H. move: (H v) => /andP [H1 H2]. rewrite /newer_than_lit /= in H1.
      move: (newer_than_var_irrefl v). rewrite H1. discriminate.
    - move=> v. move=> H. move: (H v) => /andP [H1 H2]. rewrite /newer_than_lit /= in H1.
      move: (newer_than_var_irrefl v). rewrite H1. discriminate.
  Qed.

  Lemma cnf_eqnew_sym cs : cnf_eqnew cs cs.
  Proof. done. Qed.

  Lemma cnf_eqnew_comm cs1 cs2 : cnf_eqnew cs1 cs2 -> cnf_eqnew cs2 cs1.
  Proof. move=> Heq g. rewrite (Heq g). reflexivity. Qed.

  Lemma cnf_eqnew_rcons_cons c cs : cnf_eqnew (rcons cs c) (c::cs).
  Proof.
    move=> g. rewrite newer_than_cnf_rcons /=. rewrite andbC. reflexivity.
  Qed.

  Lemma cnf_eqnew_rev cs : cnf_eqnew (rev cs) cs.
  Proof. move=> g. rewrite newer_than_cnf_rev. reflexivity. Qed.

  Lemma tflatten_singleton_eqnew cs :
    cnf_eqnew (tflatten [:: cs]) cs.
  Proof.
    elim: cs => [| c cs IH] //=. rewrite tflatten_cons /=. exact: cnf_eqnew_rev.
  Qed.

  Lemma cnf_eqnew_catrev2 cs1 cs2 cs3 cs4 :
    cnf_eqnew (tflatten cs1) cs2 ->
    cnf_eqnew (tflatten cs3) cs4 ->
    cnf_eqnew (tflatten (catrev cs1 cs3)) (catrev cs2 cs4).
  Proof.
    move=> Hnew12 Hnew34 g. rewrite newer_than_cnf_tflatten_catrev.
    rewrite newer_than_cnf_catrev. rewrite (Hnew12 g) (Hnew34 g). reflexivity.
  Qed.

End EqNew.



Section EnvEqual.

  Definition env_equal (e1 e2 : env) : Prop :=
    forall v, e1 v = e2 v.

  Lemma env_equal_interp_lit e1 e2 l :
    env_equal e1 e2 -> interp_lit e1 l = interp_lit e2 l.
  Proof.
    move=> H. case: l => //=. move=> v. rewrite (H v). reflexivity.
  Qed.

  Lemma env_equal_interp_word e1 e2 w :
    env_equal e1 e2 -> interp_word e1 w = interp_word e2 w.
  Proof.
    elim: w => [| l w IH] H //=. rewrite (IH H). rewrite (env_equal_interp_lit l H).
    reflexivity.
  Qed.

  Lemma env_equal_interp_clause e1 e2 c :
    env_equal e1 e2 -> interp_clause e1 c = interp_clause e2 c.
  Proof.
    elim: c => [| l c IH] H //=. rewrite (IH H). rewrite (env_equal_interp_lit l H).
    reflexivity.
  Qed.

  Lemma env_equal_interp_cnf e1 e2 cs :
    env_equal e1 e2 -> interp_cnf e1 cs = interp_cnf e2 cs.
  Proof.
    elim: cs => [| c cs IH] H //=. rewrite (IH H) (env_equal_interp_clause c H).
    reflexivity.
  Qed.

  Lemma env_equal_upd e1 e2 x v :
    env_equal e1 e2 -> env_equal (env_upd e1 x v) (env_upd e2 x v).
  Proof.
    move=> H y. case Hxy: (x == y).
    - rewrite (eqP Hxy). rewrite !env_upd_eq. reflexivity.
    - move/idP/negP: Hxy => Hxy. rewrite !(env_upd_neq _ _ Hxy). exact: (H y).
  Qed.

  Lemma env_equal_refl e : env_equal e e.
  Proof. done. Qed.

  Lemma env_equal_sym e1 e2 : env_equal e1 e2 -> env_equal e2 e1.
  Proof. move=> H x. rewrite (H x). reflexivity. Qed.

  Lemma env_equal_trans e1 e2 e3 : env_equal e1 e2 -> env_equal e2 e3 -> env_equal e1 e3.
  Proof. move=> H12 H23 x. rewrite (H12 x) (H23 x). reflexivity. Qed.

  Instance env_equal_Reflexive : Reflexive (@env_equal) := @env_equal_refl.
  Instance env_equal_Symmetric : Symmetric (@env_equal) := @env_equal_sym.
  Instance env_equal_Transitive : Transitive (@env_equal) := @env_equal_trans.
  Instance env_equal_Equivalence : Equivalence (@env_equal) :=
    { Equivalence_Reflexive := env_equal_Reflexive;
      Equivalence_Symmetric := env_equal_Symmetric;
      Equivalence_Transitive := env_equal_Transitive }.

End EnvEqual.


Global Opaque add_prelude.
