
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNFSimple BBCommonSimple BBIteSimple.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_shl ===== *)

Definition bit_blast_shl_int1 w (g : generator) (ls : w.-tuple literal) : generator * cnf * w.-tuple literal :=
  (g, [::], dropmsb (joinlsb (ls, lit_ff))).

Fixpoint bit_blast_shl_int w (g : generator) (ls : w.-tuple literal) (n : nat) : generator * cnf * w.-tuple literal :=
  match n with
  | O => (g, [::], ls)
  | S m => let '(g_m, cs_m, ls_m) := bit_blast_shl_int g ls m in
           let '(g1, cs1, ls1) := bit_blast_shl_int1 g_m ls_m in
           (g1, cs_m++cs1, ls1)
  end.

Definition mk_env_shl_int1 w (E : env) (g : generator) (ls : w.-tuple literal) : env * generator * cnf * w.-tuple literal :=
  (E, g, [::], dropmsb (joinlsb (ls, lit_ff))) .

Fixpoint mk_env_shl_int w (E : env) (g : generator) (ls : w.-tuple literal) (n : nat) : env * generator * cnf * w.-tuple literal :=
  match n with
  | O => (E, g, [::], ls)
  | S m => let: (E_m, g_m, cs_m, ls_m) := mk_env_shl_int E g ls m in
           let: (E', g', cs, ls') := mk_env_shl_int1 E_m g_m ls_m in
           (E', g', cs_m ++ cs, ls')
  end .

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
             let '(g_ite, cs_ite, ls_ite) := bit_blast_ite g_hd ns_hd ls_hd ls_tl in
             (g_ite, cs_tl++cs_hd++cs_ite, ls_ite)
  else
    fun ls _ _ =>
      (g, [::], ls).

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
        case Hite: (bit_blast_ite g_hd ilns_hd ls_hd ls_tl) => [[g_ite cs_ite] ls_ite].
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


Lemma mk_env_shl_int1_is_bit_blast_shl_int1 :
  forall w E g (ls: w.-tuple literal) E' g' cs lrs,
    mk_env_shl_int1 E g ls = (E', g', cs, lrs) ->
    bit_blast_shl_int1 g ls = (g', cs, lrs).
Proof.
  move => w E g ls E' g' cs lrs .
  rewrite /mk_env_shl_int1 /bit_blast_shl_int1 .
  by case => _ <- <- <- .
Qed .

Lemma mk_env_shl_int_is_bit_blast_shl_int :
  forall w E g (ls: w.-tuple literal) i E' g' cs lrs,
    mk_env_shl_int E g ls i = (E', g', cs, lrs) ->
    bit_blast_shl_int g ls i = (g', cs, lrs).
Proof.
  move => w E g ls /= .
  elim .
  - move => E' g' cs lrs .
    rewrite /mk_env_shl_int /bit_blast_shl_int /= .
    by case => _ <- <- <- .
  - move => n IH E' g' cs lrs /= .
    case Henv : (mk_env_shl_int E g ls n) => [[[E_m g_m] cs_m] ls_m] .
    case => _ <- <- <- .
    by rewrite (IH _ _ _ _ Henv) .
Qed .

Fixpoint mk_env_shl_rec w wn (E : env) (g : generator) : w.-tuple literal -> wn.-tuple literal -> nat -> env * generator * cnf * w.-tuple literal :=
  if wn is _.+1 then
    fun ls ns i =>
      let (ns_tl, ns_hd) := eta_expand (splitlsb ns) in
      let '(E_tl, g_tl, cs_tl, ls_tl) := mk_env_shl_rec E g ls ns_tl (2 * i) in
      let '(E_hd, g_hd, cs_hd, ls_hd) := mk_env_shl_int E_tl g_tl ls_tl i in
      if ns_hd == lit_tt then
        (E_hd, g_hd, cs_tl++cs_hd, ls_hd)
      else if ns_hd == lit_ff then
             (E_tl, g_tl, cs_tl, ls_tl)
           else
             let '(E_ite, g_ite, cs_ite, ls_ite) := mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl in
             (E_ite, g_ite, cs_tl++cs_hd++cs_ite, ls_ite)
  else
    fun ls _ _ =>
      (E, g, [::], ls).

Definition mk_env_shl w (E : env) (g : generator) (ls ns : w.-tuple literal) : env * generator * cnf * w.-tuple literal :=
  mk_env_shl_rec E g ls ns 1.

Lemma mk_env_shl_rec_is_bit_blast_shl_rec :
  forall w wn E g (ls : w.-tuple literal) (ns : wn.-tuple literal)
         i E' g' cs lrs,
    mk_env_shl_rec E g ls ns i= (E', g', cs, lrs) ->
    bit_blast_shl_rec g ls ns i = (g', cs, lrs).
Proof.
  move => w . elim .
  - move => E g ls ns i E' g' cs lrs .
    rewrite /mk_env_shl_rec /bit_blast_shl_rec /= .
    by case => _ <- <- <- .
  - move => n IH E g ls . case/tupleP => [ns_hd ns_tl] .
    move => i E' g' cs lrs .
    case Henv_tl : (mk_env_shl_rec E g ls ns_tl (2 * i))
    => [[[E_tl g_tl] cs_tl] ls_tl] .
    case Henv_hd : (mk_env_shl_int E_tl g_tl ls_tl i)
    => [[[E_hd g_hd] cs_hd] ls_hd] .
    rewrite /= !theadCons !beheadCons .
    case Htt : (ns_hd == lit_tt) .
    + rewrite Henv_tl (IH _ _ _ _ _ _ _ _ _ Henv_tl) .
      rewrite Henv_hd (mk_env_shl_int_is_bit_blast_shl_int Henv_hd) /= .
      by case => _ <- <- <- .
    + case Hff : (ns_hd == lit_ff) .
      * rewrite Henv_tl (IH _ _ _ _ _ _ _ _ _ Henv_tl) .
        rewrite Henv_hd (mk_env_shl_int_is_bit_blast_shl_int Henv_hd) /= .
        by case => _ <- <- <- .
      * rewrite Henv_tl (IH _ _ _ _ _ _ _ _ _ Henv_tl) .
        rewrite Henv_hd (mk_env_shl_int_is_bit_blast_shl_int Henv_hd) /= .
        case Hite : (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl)
        => [[[E_ite g_ite] cs_ite] ls_ite] .
        rewrite (mk_env_ite_is_bit_blast_ite Hite) .
        by case => _ <- <- <- .
Qed .

Lemma mk_env_shl_is_bit_blast_shl :
  forall w E g (ls ns: w.-tuple literal) E' g' cs lrs,
    mk_env_shl E g ls ns = (E', g', cs, lrs) ->
    bit_blast_shl g ls ns = (g', cs, lrs).
Proof.
  move => w E g ls ns E' g' cs lrs .
  apply mk_env_shl_rec_is_bit_blast_shl_rec .
Qed .

Lemma mk_env_shl_int_newer_gen :
  forall w E g (ls : w.-tuple literal) i E' g' cs lrs,
    mk_env_shl_int E g ls i = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move => w E g ls .
  elim .
  - move => E' g' cs lrs .
    case => _ <- _ _ .
    exact: Pos.leb_refl .
  - move => n IH E' g' cs lrs .
    case Henv_tl : (mk_env_shl_int E g ls n)
    => [[[E_tl g_tl] cs_tl] lrs_t] .
    rewrite /= .
    rewrite Henv_tl .
    case => _ <- _ _ .
    apply: (IH _ _ _ _ Henv_tl) .
Qed .

Lemma mk_env_shl_rec_newer_gen :
  forall w wn E g (ls0 : w.-tuple literal) (ls1 : wn.-tuple literal)
         i E' g' cs lrs,
    mk_env_shl_rec E g ls0 ls1 i = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move => w .
  elim .
  - move => E g ls0 ls1 i E' g' cs lrs .
    case => _ <- _ _ .
    exact: Pos.leb_refl .
  - move => n IH E g ls0 /tupleP [ls1_hd ls1_tl] i E' g' cs lrs .
    case Henv_tl : (mk_env_shl_rec E g ls0 ls1_tl (2 * i))
    => [[[E_tl g_tl] cs_tl] lrs_tl] .
    move : (IH _ _ _ _ _ _ _ _ _ Henv_tl) => Hggtl .
    rewrite /= !theadCons !beheadCons Henv_tl .
    case Hshl_int : (mk_env_shl_int E_tl g_tl lrs_tl i)
    => [[[E_hd g_hd] cs_hd] ls_hd] .
    move: (mk_env_shl_int_newer_gen Hshl_int) => Hgtlghd .
    case Htt : (ls1_hd == lit_tt) .
    + case => _ <- _ _ .
      apply (pos_leb_trans Hggtl Hgtlghd) .
    + case Hff : (ls1_hd == lit_ff) .
      * by case => _ <- _ _ .
      * case Hite : (mk_env_ite E_hd g_hd ls1_hd ls_hd lrs_tl)
        => [[[E_ite g_ite] cs_ite] ls_ite] .
        case => _ <- _ _ .
        move: (mk_env_ite_newer_gen Hite) .
        move : (pos_leb_trans Hggtl Hgtlghd) .
        apply pos_leb_trans .
Qed .

Lemma mk_env_shl_newer_gen :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_shl E g ls1 ls2 = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move => w E g ls ns E' g' cs lrs .
  exact : mk_env_shl_rec_newer_gen .
Qed .

Lemma mk_env_shl_int_newer_res :
  forall w E g i E' g' (ls : w.-tuple literal) cs lrs,
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    mk_env_shl_int E g ls i = (E', g', cs, lrs) ->
    newer_than_lits g' lrs.
Proof .
  move => w E g .
  elim .
  - move => E' g' ls cs lrs Hgtt Hgls .
    by case => _ <- _ <- .
  - move => n IH E' g' ls cs lrs Hgtt Hgls .
    move Htl : (mk_env_shl_int E g ls n) => [[[E_tl g_tl] cs_tl] lrs_tl] .
    rewrite /= Htl .
    case => _ <- _ <- .
    rewrite /joinlsb /= /dropmsb .
    move: (IH _ _ _ _ _ Hgtt Hgls Htl) => Hg_tllrs_tl .
    move: Hgtt .
    rewrite -newer_than_lit_neg /= -/lit_ff => Hgff .
    move : (mk_env_shl_int_newer_gen Htl) => Hgg' .
    move : (newer_than_lit_le_newer Hgff Hgg') => Hg'ff .
    assert (newer_than_lits g_tl (cons_tuple lit_ff lrs_tl)) .
    + rewrite newer_than_lits_cons .
      apply /andP; split; auto .
    + case Hsplitcons : (splitmsb (cons_tuple lit_ff lrs_tl))
      => [msb others] .
      move : (newer_than_lits_splitmsb H Hsplitcons) .
      by move /andP => [Hmsb Hothers] .
Qed .

Lemma mk_env_shl_rec_newer_res :
  forall w wn E g i E' g' (ls : w.-tuple literal) (ns : wn.-tuple literal)
         cs lrs,
    newer_than_lit g lit_tt ->
    newer_than_lits g ls -> newer_than_lits g ns ->
    mk_env_shl_rec E g ls ns i = (E', g', cs, lrs) ->
    newer_than_lits g' lrs.
Proof .
  move => w .
  elim .
  - move => E g i E' g' ls ns cs lrs Hgtt Hgls Hgns .
    by case => _ <- _ <- .
  - move => n IH E g i E' g' ls /tupleP [ns_hd ns_tl] cs lrs Hgtt Hgls Hgns .
    rewrite /= !theadCons !beheadCons .
    case Henvtl : (mk_env_shl_rec E g ls ns_tl (2*i))
    => [[[E_tl g_tl] cs_tl] ls_tl] .
    case Henvhd : (mk_env_shl_int E_tl g_tl ls_tl i)
    => [[[E_hd g_hd] cs_hd] ls_hd] .
    move : (newer_than_lits_behead Hgns) .
    rewrite beheadCons => {Hgns} Hgns_tl .
    move : (IH _ _ _ _ _ _ _ _ _ Hgtt Hgls Hgns_tl Henvtl)
    => {Hgns_tl} Hgtllstl .
    case Htt : (ns_hd == lit_tt) .
    + case => _ <- _ <- .
      move : (mk_env_shl_rec_newer_gen Henvtl) => Hggtl .
      move : (newer_than_lit_le_newer Hgtt Hggtl) => Hgtltt .
      apply (mk_env_shl_int_newer_res Hgtltt Hgtllstl Henvhd) .
    + case Hff : (ns_hd == lit_ff) .
      * case => _ <- _ <- .
        done .
      * case Hite : (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl)
        => [[[E_ite g_ite] cs_ite] ls_ite] .
        case => _ <- _ <- .
        apply (mk_env_ite_newer_res Hite) .
Qed .

Lemma mk_env_shl_newer_res :
  forall w E g (ls : w.-tuple literal) (ns : w.-tuple literal)
         E' g' cs lrs,
    newer_than_lit g lit_tt ->
    newer_than_lits g ls -> newer_than_lits g ns ->
    mk_env_shl E g ls ns = (E', g', cs, lrs) ->
    newer_than_lits g' lrs.
Proof .
  move => w E g ls ns E' g' cs lrs .
  apply mk_env_shl_rec_newer_res .
Qed .

Lemma mk_env_shl_int_newer_cnf :
  forall w E g (ls : w.-tuple literal) i E' g' cs lr,
    mk_env_shl_int E g ls i = (E', g', cs, lr) ->
    newer_than_lits g ls ->
    newer_than_cnf g' cs.
Proof .
  move => w E g ls .
  elim .
  - move => E' g' cs lr .
    by case => _ <- <- _ _ .
  - move => n IH E' g' cs lr .
    rewrite /= .
    case Hn : (mk_env_shl_int E g ls n) => [[[E_m g_m] cs_m] ls_m] .
    case => _ <- <- _ Hgls .
    rewrite cats0 .
    by apply (IH _ _ _ _ Hn Hgls) .
Qed .

Lemma mk_env_shl_rec_newer_cnf :
  forall w wn E g (ls : w.-tuple literal) (ns : wn.-tuple literal) i
         E' g' cs lr,
    mk_env_shl_rec E g ls ns i = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls -> newer_than_lits g ns ->
    newer_than_cnf g' cs.
Proof .
  move => w .
  elim .
  - move => E g ls ns i E' g' cs lr .
    by case => _ <- <- _ _ _ .
  - move => n IH E g ls /tupleP [ns_hd ns_tl] i E' g' cs lr .
    rewrite /= !theadCons !beheadCons .
    case Htl : (mk_env_shl_rec E g ls ns_tl (2*i))
    => [[[E_tl g_tl] cs_tl] ls_tl] .
    case Hhd : (mk_env_shl_int E_tl g_tl ls_tl i)
    => [[[E_hd g_hd] cs_hd] ls_hd] .
    case Htt : (ns_hd == lit_tt) .
    + case => _ <- <- _ .
      move => Hgtt Hgls /andP [Hgnshd Hgnstl] .
      move : (IH _ _ _ _ _ _ _ _ _ Htl Hgtt Hgls Hgnstl) => Hgtlcstl .
      move : (mk_env_shl_rec_newer_res Hgtt Hgls Hgnstl Htl) => Hgtllstl .
      move : (mk_env_shl_int_newer_cnf Hhd Hgtllstl) => Hghdcshd .
      move : (mk_env_shl_int_newer_gen Hhd) => Hgtlghd .
      move : (newer_than_cnf_le_newer Hgtlcstl Hgtlghd)
      => Hghdcstl .
      rewrite newer_than_cnf_append .
      apply /andP; split; auto .
    + case Hff : (ns_hd == lit_ff) .
      * case => _ <- <- _ .
        move => Hgtt Hgls /andP [Hgnshd Hgnstl] .
        apply (IH _ _ _ _ _ _ _ _ _ Htl Hgtt Hgls Hgnstl) .
      * case Hite : (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl)
        => [[[E_ite g_ite] cs_ite] ls_ite] .
        case => _ <- <- _ Hgtt Hgls /andP [Hgnshd Hgnstl] .
        move : (IH _ _ _ _ _ _ _ _ _ Htl Hgtt Hgls Hgnstl) => Hgtlcstl .
        move : (mk_env_shl_rec_newer_res Hgtt Hgls Hgnstl Htl) => Hgtllstl .
        move : (mk_env_shl_rec_newer_gen Htl)
        => { Htt Hff Htl Hgls Hgnstl } Hggtl .
        move : (newer_than_lit_le_newer Hgtt Hggtl)
                 (newer_than_lit_le_newer Hgnshd Hggtl)
        => { Hgtt Hgnshd Hggtl E g } Hgtltt Hgtlnshd .
        move : (mk_env_shl_int_newer_cnf Hhd Hgtllstl) => Hghdcshd .
        move : (mk_env_shl_int_newer_res Hgtltt Hgtllstl Hhd) => Hghdlshd .
        move : (mk_env_shl_int_newer_gen Hhd)
        => { Hhd Hgtltt } Hgtlghd .
        move : (newer_than_lit_le_newer Hgtlnshd Hgtlghd)
                 (newer_than_lits_le_newer Hgtllstl Hgtlghd)
                 (newer_than_cnf_le_newer Hgtlcstl Hgtlghd)
        => { Hgtlghd Hgtlnshd Hgtllstl Hgtlcstl E_tl g_tl }
             Hghdnshd Hghdlstl Hghdcstl .
        move : (mk_env_ite_newer_cnf Hite Hghdnshd Hghdlshd Hghdlstl)
        => { Hghdnshd Hghdlshd Hghdlstl } Hgitecsite .
        move : (mk_env_ite_newer_gen Hite) => Hghdgite .
        move : (newer_than_cnf_le_newer Hghdcshd Hghdgite)
                 (newer_than_cnf_le_newer Hghdcstl Hghdgite)
        => { Hite Hghdcshd Hghdcstl Hghdgite E_hd g_hd }
             Hgitecshd Hgitecstl .
        rewrite !newer_than_cnf_append .
        apply /andP; split; first done .
        apply /andP; split; done .
Qed .

Lemma mk_env_shl_newer_cnf :
  forall w E g (ls ns : w.-tuple literal) E' g' cs lrs,
    mk_env_shl E g ls ns = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls -> newer_than_lits g ns ->
    newer_than_cnf g' cs.
Proof .
  rewrite /mk_env_shl .
  move => w E g ls ns E' g' cs lrs .
  exact : mk_env_shl_rec_newer_cnf .
Qed .

Lemma mk_env_shl_int_preserve :
  forall w E g (ls : w.-tuple literal) i E' g' cs lrs,
    mk_env_shl_int E g ls i = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof .
  move => w E g ls .
  elim .
  - move => E' g' cs lrs .
    case => <- -> _ _ .
    exact : env_preserve_refl .
  - move => n IH E' g' cs lrs .
    case Hn : (mk_env_shl_int E g ls n) => [[[En gn] csn] lrsn] .
    move : (IH _ _ _ _ Hn) => HEEn .
    rewrite /= Hn .
    by case => <- _ _ _ .
Qed .

Lemma mk_env_shl_rec_preserve :
  forall w wn E g (ls : w.-tuple literal) (ns : wn.-tuple literal) i
         E' g' cs lrs,
    mk_env_shl_rec E g ls ns i = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof .
  move => w .
  elim .
  - move => E g ls ns i E' g' cs lrs .
    case => -> _ _ _ .
    exact : env_preserve_refl .
  - move => n IH E g ls /tupleP [ns_hd ns_tl] i E' g' cs lrs .
    rewrite /= !theadCons !beheadCons .
    case Htl : (mk_env_shl_rec E g ls ns_tl (2*i))
    => [[[E_tl g_tl] cs_tl] ls_tl] .
    move : (IH _ _ _ _ _ _ _ _ _ Htl) => HEEtl .
    move : (mk_env_shl_rec_newer_gen Htl) => {Htl} Hggtl .
    case Hhd : (mk_env_shl_int E_tl g_tl ls_tl i)
      => [[[E_hd g_hd] cs_hd] ls_hd] .
    move : (mk_env_shl_int_preserve Hhd) => HEtlEhd .
    move : (env_preserve_le HEtlEhd Hggtl)
    => { HEtlEhd } HEtlEhd .
    case : (ns_hd == lit_tt) .
    + case => <- _ _ _ .
      by apply (env_preserve_trans HEEtl) .
    + case : (ns_hd == lit_ff) .
      * by case => <- .
      * move : (mk_env_shl_int_newer_gen Hhd) => Hghdgtl .
        case Hite : (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl)
        => [[[E_ite g_ite] cs_ite] ls_ite] .
        case => <- _ _ _ .
        move : (mk_env_ite_preserve Hite) => HEEite .
        move : (env_preserve_le HEEite Hghdgtl) => {HEEite} HEEite .
        move : (env_preserve_le HEEite Hggtl) => {HEEite} .
        apply env_preserve_trans .
        by apply (env_preserve_trans HEEtl) .
Qed .

Lemma mk_env_shl_preserve :
  forall w E g (ls ns : w.-tuple literal) E' g' cs lrs,
    mk_env_shl E g ls ns = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof .
  move => w E g ls ns E' g' cs lrs .
  rewrite /mk_env_shl. exact : mk_env_shl_rec_preserve .
Qed .

Lemma mk_env_shl_int_sat :
  forall w E g (ls : w.-tuple literal) i E' g' cs lrs,
    mk_env_shl_int E g ls i = (E', g', cs, lrs) ->
    newer_than_lits g ls ->
    interp_cnf E' cs.
Proof .
  move => w E g ls .
  elim .
  - move => E' g' cs lrs .
    by case => _ _ <- _ .
  - move => n IH E' g' cs lrs .
    case Hn : (mk_env_shl_int E g ls n) => [[[En gn] csn] lsn] .
    rewrite /= Hn .
    case => <- _ <- _ Hgls .
    move : (IH _ _ _ _ Hn Hgls) => Hcsn .
    by rewrite interp_cnf_append Hcsn .
Qed .

Lemma mk_env_shl_rec_sat :
  forall w wn E g (ls : w.-tuple literal) (ns : wn.-tuple literal) i
         E' g' cs lrs,
    mk_env_shl_rec E g ls ns i = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls -> newer_than_lits g ns ->
    interp_cnf E' cs.
Proof .
  move => w .
  elim .
  - move => E g ls ns i E' g' cs lrs .
    by case => _ _ <- _ _ _ .
  - move => n IH E g ls /tupleP [ns_hd ns_tl] i E' g' cs lrs .
    case Htl : (mk_env_shl_rec E g ls ns_tl (2 * i))
    => [[[E_tl g_tl] cs_tl] ls_tl] .
    case Hhd : (mk_env_shl_int E_tl g_tl ls_tl i)
    => [[[E_hd g_hd] cs_hd] ls_hd] .
    rewrite /= !theadCons !beheadCons Htl Hhd .
    case : (ns_hd == lit_tt) .
    + case => <- _ <- _ Hgtt Hgls /andP [Hgnshd Hgnstl] .
      move : (IH _ _ _ _ _ _ _ _ _ Htl Hgtt Hgls Hgnstl) => HEtlcstl .
      move : (mk_env_shl_rec_newer_res Hgtt Hgls Hgnstl Htl) => Hgtllstl .
      move : (mk_env_shl_int_sat Hhd Hgtllstl) => HEhdcshd .
      rewrite interp_cnf_append .
      apply /andP; split; last done .
      move : (mk_env_shl_int_preserve Hhd) => HEtlEhd .
      move : (mk_env_shl_rec_newer_cnf Htl Hgtt Hgls Hgnstl) => Hgtlcstl .
      by rewrite (env_preserve_cnf HEtlEhd Hgtlcstl) .
    + case : (ns_hd == lit_ff) .
      * case => <- _ <- _ Hgtt Hgls /andP [Hgnshd Hgnstl] .
        by apply (IH _ _ _ _ _ _ _ _ _ Htl Hgtt Hgls Hgnstl) .
      * case Hite : (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl)
        => [[[E_ite g_ite] cs_ite] ls_ite] .
        case => <- _ <- _ Hgtt Hgls /andP [Hgnshd Hgnstl] .
        move : (mk_env_shl_rec_newer_cnf Htl Hgtt Hgls Hgnstl) => Hgtlcstl .
        move : (mk_env_shl_int_preserve Hhd) => HEtlEhd .
        move : (IH _ _ _ _ _ _ _ _ _ Htl Hgtt Hgls Hgnstl) .
        rewrite -(env_preserve_cnf HEtlEhd Hgtlcstl)
        => {HEtlEhd} HEhdcstl .
        move : (mk_env_shl_int_newer_gen Hhd) => Hgtlghd .
        move : (newer_than_cnf_le_newer Hgtlcstl Hgtlghd)
        => {Hgtlcstl Hgtlghd} Hghdcstl .
        move : (mk_env_ite_preserve Hite) HEhdcstl => HEhdEite .
        rewrite -(env_preserve_cnf HEhdEite Hghdcstl) => Hitecstl .
        move : (mk_env_shl_rec_newer_res Hgtt Hgls Hgnstl Htl)
        => {Hgnstl} Hgtllstl .
        move : (mk_env_shl_rec_newer_gen Htl) => Hggtl .
        move : (newer_than_lit_le_newer Hgnshd Hggtl) => Hgtlnshd .
        move : (newer_than_lit_le_newer Hgtt Hggtl)
        => { Hgtt Hggtl Hgnshd Htl E } => Hgtltt .
        move : (mk_env_shl_int_newer_cnf Hhd Hgtllstl) => Hghdcshd .
        move : (mk_env_shl_int_sat Hhd Hgtllstl) .
        rewrite -(env_preserve_cnf HEhdEite Hghdcshd) => HEitecshd .
        move : (mk_env_shl_int_newer_res Hgtltt Hgtllstl Hhd) => Hghdlshd .
        move : (mk_env_shl_int_newer_gen Hhd) => Hgtlghd .
        move : (newer_than_lit_le_newer Hgtlnshd Hgtlghd) => Hghdnshd .
        move : (newer_than_lits_le_newer Hgtllstl Hgtlghd)
        => { Hgtlnshd Hgtllstl Hgtlghd } Hghdlstl .
        move : (mk_env_ite_sat Hite Hghdnshd Hghdlshd Hghdlstl)
        => { Hghdnshd Hghdlshd Hghdlstl } => HEitecsite .
        rewrite !interp_cnf_append .
        apply /andP; split; first done; apply /andP; split; done .
Qed .

Lemma mk_env_shl_sat :
  forall w E g (ls ns : w.-tuple literal) E' g' cs lrs,
    mk_env_shl E g ls ns = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls -> newer_than_lits g ns ->
    interp_cnf E' cs.
Proof .
  move => w E g ls ns E' g' cs lrs .
  rewrite /mk_env_shl; exact : mk_env_shl_rec_sat .
Qed .
