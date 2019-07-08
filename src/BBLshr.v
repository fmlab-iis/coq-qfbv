
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon BBIte.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_lshr ===== *)

Definition bit_blast_lshr_int1 w (g : generator) : w.-tuple literal -> generator * cnf * w.-tuple literal :=
  if w is _.+1
  then fun ls => (g, [::], joinmsb (lit_ff, droplsb ls))
  else fun _ => (g, [::], [tuple]) .

Fixpoint bit_blast_lshr_int w (g : generator) (ls : w.-tuple literal) (n : nat) : generator * cnf * w.-tuple literal :=
  match n with
  | O => (g, [::], ls)
  | S m => let '(g_m, cs_m, ls_m) := bit_blast_lshr_int g ls m in
           let '(g1, cs1, ls1) := bit_blast_lshr_int1 g_m ls_m in
           (g1, cs_m++cs1, ls1)
  end.

Definition mk_env_lshr_int1 w (E : env) (g : generator) : w.-tuple literal -> env * generator * cnf * w.-tuple literal :=
  if w is _.+1
  then fun ls => (E, g, [::], joinmsb (lit_ff, droplsb ls))
  else fun _  => (E, g, [::], [tuple]) .

Fixpoint mk_env_lshr_int w (E : env) (g : generator) (ls : w.-tuple literal) (n : nat) : env * generator * cnf * w.-tuple literal :=
  match n with
  | O => (E, g, [::], ls)
  | S m => let: (E_m, g_m, cs_m, ls_m) := mk_env_lshr_int E g ls m in
           let: (E', g', cs, ls') := mk_env_lshr_int1 E_m g_m ls_m in
           (E', g', cs_m ++ cs, ls')
  end .

Lemma bit_blast_lshr_int1_correct :
  forall w g (bs : BITS w) E ls g' cs lrs,
    bit_blast_lshr_int1 g ls = (g', cs, lrs) ->
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (shrB bs).
Proof.
  elim.
  - done.
  - move => w IH g bs E ls g' cs lrs. rewrite /bit_blast_lshr_int1 /shrB /enc_bit.
    case => Hog Hcs <- Henc_bs Hcnf. apply/andP; split.
    + apply: enc_bits_thead. rewrite /joinmsb0.
      rewrite enc_bits_joinmsb (add_prelude_enc_bit_ff Hcnf).
      exact: (enc_bits_droplsb Henc_bs).
    + rewrite /=. apply enc_bits_behead. rewrite /joinmsb0.
      rewrite enc_bits_joinmsb (add_prelude_enc_bit_ff Hcnf).
      exact: (enc_bits_droplsb Henc_bs).
Qed.


Lemma bit_blast_lshr_int_correct :
  forall w g (bs : BITS w) n E ls g' cs lrs,
    bit_blast_lshr_int g ls n = (g', cs, lrs) ->
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (shrBn bs n).
Proof.
  move => w ig ibs. elim.
  - rewrite /= => E ils og cs olrs. case => _ <- <-. done.
  - move => n IH E ils og cs olrs. rewrite (lock interp_cnf) /= -lock.
    case Hm: (bit_blast_lshr_int ig ils) => [[g_m cs_m] ls_m].
    case H1: (bit_blast_lshr_int1 g_m ls_m) => [[g1 cs1] ls1].
    case => Hog Hcs Holrs Henc_ibs Hcnf. rewrite <- Holrs.
    rewrite -Hcs add_prelude_append in Hcnf. move/andP: Hcnf => [Hcnf_m Hcnf1].
    apply: (bit_blast_lshr_int1_correct H1 _ Hcnf1).
    exact: (IH E _ _ _ _ Hm Henc_ibs Hcnf_m).
Qed.

Fixpoint bit_blast_lshr_rec w wn (g : generator) : w.-tuple literal -> wn.-tuple literal -> nat -> generator * cnf * w.-tuple literal :=
  if wn is _.+1 then
    fun ls ns i =>
      let (ns_tl, ns_hd) := eta_expand (splitlsb ns) in
      let '(g_tl, cs_tl, ls_tl) := bit_blast_lshr_rec g ls ns_tl (2 * i) in
      let '(g_hd, cs_hd, ls_hd) := bit_blast_lshr_int g_tl ls_tl i in
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

Definition bit_blast_lshr w (g : generator) (ls ns : w.-tuple literal) : generator * cnf * w.-tuple literal :=
  bit_blast_lshr_rec g ls ns 1.

Lemma bit_blast_lshr_rec_correct :
  forall w wn g (bs : BITS w) (ns: BITS wn) i E ls (lns : wn.-tuple literal) g' cs lrs,
    bit_blast_lshr_rec g ls lns i = (g', cs, lrs) ->
    enc_bits E ls bs ->
    enc_bits E lns ns ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (shrBn bs (toNat ns * i)).
Proof.
  move => w  .
  elim .
  - move => g bs ns i E ls lns g' cs lrs .
    case => _ <- <- Hlsbs _ _ .
    by rewrite tuple0 /= .
  - move => n IH g bs /tupleP [ns_hd ns_tl] i E ls
              /tupleP [lns_hd lns_tl] g' cs lrs .
    case Htl : (bit_blast_lshr_rec g ls lns_tl (2 * i))
    => [[g_tl cs_tl] ls_tl] .
    case Hhd : (bit_blast_lshr_int g_tl ls_tl i)
    => [[g_hd cs_hd] ls_hd] .
    rewrite (lock add_prelude) /= !beheadCons !theadCons Htl Hhd -lock .
    case Htt : (lns_hd == lit_tt) .
    + move /eqP : Htt => Htt . rewrite Htt .
      case => _ <- <- Hlsbs /andP [Hnshd Hnstl] .
      rewrite add_prelude_append .
      case /andP => [Hcstl Hcshd] .
      rewrite (add_prelude_enc_bit_true _ Hcstl) in Hnshd .
      rewrite Hnshd .
      move : (IH _ _ _ _ _ _ _ _ _ _ Htl Hlsbs Hnstl Hcstl)
      => Hshrlstl .
      move :(bit_blast_lshr_int_correct Hhd Hshrlstl Hcshd) => Hshrlshd .
      rewrite -shrBn_add in Hshrlshd .
      rewrite toNat_joinlsb /= .
      rewrite -muln2 .
      by replace ((1 + toNat ns_tl * 2) * i) with (toNat ns_tl * (2 * i) + i) by ring .
      case Hff : (lns_hd == lit_ff) .
      * move /eqP : Hff => Hff; rewrite Hff .
        case => _ <- <- Hlsbs /andP [Hnshd Hnstl] Hcstl .
        rewrite (add_prelude_enc_bit_is_false _ Hcstl) in Hnshd .
        rewrite (eqP Hnshd) {Hnshd} .
        move : (IH _ _ _ _ _ _ _ _ _ _ Htl Hlsbs Hnstl Hcstl) .
        rewrite toNat_joinlsb /= -muln2 .
        replace ((0 + toNat ns_tl * 2) * i) with (toNat ns_tl * (2 * i)) by ring .
        done .
      * case Hite : (bit_blast_ite g_hd lns_hd ls_hd ls_tl)
        => {Htt Hff} [[g_ite cs_ite] ls_ite] .
        case => _ <- <- Hlsbs /andP [Hnshd Hnstl] .
        rewrite !add_prelude_append; case /andP => [Hcstl Hcshdite] .
        case : Hcshdite => /andP [Hcshd Hcsite] .
        move : (IH _ _ _ _ _ _ _ _ _ _ Htl Hlsbs Hnstl Hcstl) => Hlstl .
        move : (bit_blast_lshr_int_correct Hhd Hlstl Hcshd) => Hlshd .
        rewrite -shrBn_add in Hlshd .
        rewrite toNat_joinlsb /= -mul2n .
        apply (bit_blast_ite_correct Hite Hnshd Hlshd Hlstl Hcsite) .
        case ns_hd; rewrite /= .
        {
          by replace ((1 + 2 * toNat ns_tl) * i) with
              (toNat ns_tl * (2 * i) + i) by ring .
        }
        {
          by replace ((0 + 2 * toNat ns_tl) * i) with
              (toNat ns_tl * (2 * i)) by ring .
        }
Qed .

Corollary bit_blast_lshr_correct :
  forall w g (bs : BITS w) (ns : BITS w) E ls lns g' cs lrs,
    bit_blast_lshr g ls lns = (g', cs, lrs) ->
    enc_bits E ls bs ->
    enc_bits E lns ns ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (shrBn bs (toNat ns)).
Proof.
  move=> w g bs ns E ls lns g' cs lrs Hshl Henc_bs Henc_ns Hcnf.
  rewrite -(muln1 (toNat ns)).
  exact: (bit_blast_lshr_rec_correct Hshl Henc_bs Henc_ns Hcnf).
Qed.

Lemma mk_env_lshr_int1_is_bit_blast_lshr_int1 :
  forall w E g (ls: w.-tuple literal) E' g' cs lrs,
    mk_env_lshr_int1 E g ls = (E', g', cs, lrs) ->
    bit_blast_lshr_int1 g ls = (g', cs, lrs).
Proof.
  rewrite /mk_env_lshr_int1 /bit_blast_lshr_int1 .
  case .
  - move => E g _ E' g' cs lrs; case => _ <- <- <-; trivial .
  - move => n E g ls E' g' cs lrs; case => _ <- <- <-; trivial .
Qed .

Lemma mk_env_lshr_int_is_bit_blast_lshr_int :
  forall w E g (ls: w.-tuple literal) i E' g' cs lrs,
    mk_env_lshr_int E g ls i = (E', g', cs, lrs) ->
    bit_blast_lshr_int g ls i = (g', cs, lrs).
Proof.
  move => w E g ls /= .
  elim .
  - move => E' g' cs lrs .
    by case => _ <- <- <- /= .
  - move => n IH E' g' cs lrs /= .
    case Henvn : (mk_env_lshr_int E g ls n) => [[[En gn] csn] lrsn] .
    case Henv1 : (mk_env_lshr_int1 En gn lrsn) => [[[E1 g1] cs1] ls1] .
    case => _ <- <- <- .
    rewrite (IH _ _ _ _ Henvn) .
    by rewrite (mk_env_lshr_int1_is_bit_blast_lshr_int1 Henv1) .
Qed .

Fixpoint mk_env_lshr_rec w wn (E : env) (g : generator) : w.-tuple literal -> wn.-tuple literal -> nat -> env * generator * cnf * w.-tuple literal :=
  if wn is _.+1 then
    fun ls ns i =>
      let (ns_tl, ns_hd) := eta_expand (splitlsb ns) in
      let '(E_tl, g_tl, cs_tl, ls_tl) := mk_env_lshr_rec E g ls ns_tl (2 * i) in
      let '(E_hd, g_hd, cs_hd, ls_hd) := mk_env_lshr_int E_tl g_tl ls_tl i in
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

Definition mk_env_lshr w (E : env) (g : generator) (ls ns : w.-tuple literal) : env * generator * cnf * w.-tuple literal :=
  mk_env_lshr_rec E g ls ns 1.

Lemma mk_env_lshr_rec_is_bit_blast_lshr_rec :
  forall w wn E g (ls : w.-tuple literal) (ns : wn.-tuple literal)
         i E' g' cs lrs,
    mk_env_lshr_rec E g ls ns i= (E', g', cs, lrs) ->
    bit_blast_lshr_rec g ls ns i = (g', cs, lrs).
Proof .
  move => w . elim .
  - move => E g ls ns i E' g' cs lrs .
    rewrite /mk_env_lshr_rec /bit_blast_lshr_rec /= .
    by case => _ <- <- <- .
  - move => n IH E g ls . case/tupleP => [ns_hd ns_tl] .
    move => i E' g' cs lrs .
    case Henv_tl : (mk_env_lshr_rec E g ls ns_tl (2 * i))
    => [[[E_tl g_tl] cs_tl] ls_tl] .
    case Henv_hd : (mk_env_lshr_int E_tl g_tl ls_tl i)
    => [[[E_hd g_hd] cs_hd] ls_hd] .
    rewrite /= !theadCons !beheadCons .
    case : (ns_hd == lit_tt) .
    + rewrite Henv_tl (IH _ _ _ _ _ _ _ _ _ Henv_tl) .
      rewrite Henv_hd (mk_env_lshr_int_is_bit_blast_lshr_int Henv_hd) /= .
      by case => _ <- <- <- .
    + case : (ns_hd == lit_ff) .
      * rewrite Henv_tl (IH _ _ _ _ _ _ _ _ _ Henv_tl) .
        rewrite Henv_hd (mk_env_lshr_int_is_bit_blast_lshr_int Henv_hd) /= .
        by case => _ <- <- <- .
      * rewrite Henv_tl (IH _ _ _ _ _ _ _ _ _ Henv_tl) .
        rewrite Henv_hd (mk_env_lshr_int_is_bit_blast_lshr_int Henv_hd) /= .
        case Hite : (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl)
        => [[[E_ite g_ite] cs_ite] ls_ite] .
        rewrite (mk_env_ite_is_bit_blast_ite Hite) .
        by case => _ <- <- <- .
Qed .

Lemma mk_env_lshr_is_bit_blast_lshr :
  forall w E g (ls ns: w.-tuple literal) E' g' cs lrs,
    mk_env_lshr E g ls ns = (E', g', cs, lrs) ->
    bit_blast_lshr g ls ns = (g', cs, lrs).
Proof.
  move => w E g ls ns E' g' cs lrs .
  apply mk_env_lshr_rec_is_bit_blast_lshr_rec .
Qed .

Lemma mk_env_lshr_int1_newer_gen :
  forall w E g (ls : w.-tuple literal) E' g' cs lrs,
    mk_env_lshr_int1 E g ls = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof .
  elim .
  - move => E g ls E' g' cs lrs .
    case => _ <- _ _; exact : Pos.leb_refl .
  - move => n IH E g ls E' g' cs lrs .
    case => /= _ <- _ _; exact : Pos.leb_refl .
Qed .

Lemma mk_env_lshr_int_newer_gen :
  forall w E g (ls : w.-tuple literal) i E' g' cs lrs,
    mk_env_lshr_int E g ls i = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move => w E g ls .
  elim .
  - move => E' g' cs lrs .
    case => _ <- _ _ .
    exact: Pos.leb_refl .
  - move => n IH E' g' cs lrs .
    case Henv_tl : (mk_env_lshr_int E g ls n)
    => [[[E_tl g_tl] cs_tl] lrs_tl] .
    rewrite /= Henv_tl .
    case Henv1 : (mk_env_lshr_int1 E_tl g_tl lrs_tl) =>
    [[[E1 g1] cs1] ls1] .
    case => _ <- _ _ .
    move : (IH _ _ _ _ Henv_tl) (mk_env_lshr_int1_newer_gen Henv1) .
    apply pos_leb_trans .
Qed .

Lemma mk_env_lshr_rec_newer_gen :
  forall w wn E g (ls0 : w.-tuple literal) (ls1 : wn.-tuple literal)
         i E' g' cs lrs,
    mk_env_lshr_rec E g ls0 ls1 i = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move => w .
  elim .
  - move => E g ls0 ls1 i E' g' cs lrs .
    case => _ <- _ _ .
    exact: Pos.leb_refl .
  - move => n IH E g ls0 /tupleP [ls1_hd ls1_tl] i E' g' cs lrs .
    case Henv_tl : (mk_env_lshr_rec E g ls0 ls1_tl (2 * i))
    => [[[E_tl g_tl] cs_tl] lrs_tl] .
    move : (IH _ _ _ _ _ _ _ _ _ Henv_tl) => Hggtl .
    rewrite /= !theadCons !beheadCons Henv_tl .
    case Hshl_int : (mk_env_lshr_int E_tl g_tl lrs_tl i)
    => [[[E_hd g_hd] cs_hd] ls_hd] .
    move: (mk_env_lshr_int_newer_gen Hshl_int) => Hgtlghd .
    case : (ls1_hd == lit_tt) .
    + case => _ <- _ _ .
      apply (pos_leb_trans Hggtl Hgtlghd) .
    + case : (ls1_hd == lit_ff) .
      * by case => _ <- _ _ .
      * case Hite : (mk_env_ite E_hd g_hd ls1_hd ls_hd lrs_tl)
        => [[[E_ite g_ite] cs_ite] ls_ite] .
        case => _ <- _ _ .
        move: (mk_env_ite_newer_gen Hite) .
        move : (pos_leb_trans Hggtl Hgtlghd) .
        apply pos_leb_trans .
Qed .

Lemma mk_env_lshr_newer_gen :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_lshr E g ls1 ls2 = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move => w E g ls ns E' g' cs lrs .
  exact : mk_env_lshr_rec_newer_gen .
Qed .

Lemma mk_env_lshr_int1_newer_res :
  forall w E g E' g' (ls : w.-tuple literal) cs lrs,
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    mk_env_lshr_int1 E g ls = (E', g', cs, lrs) ->
    newer_than_lits g' lrs.
Proof .
  elim .
  - move => E g E' g' ls cs lrs _ _ .
    by case => _ <- _ <- .
  - move => n IH E g E' g' /tupleP [ls_hd ls_tl] cs lrs Hgtt Hgls .
    case => _ <- _ <- .
    rewrite /droplsb /= !beheadCons .
    apply newer_than_lits_joinmsb .
    + by move : Hgtt; rewrite -newer_than_lit_neg .
    + rewrite newer_than_lits_cons in Hgls .
      case : Hgls => /andP [_ Hlstl] ; trivial .
Qed .

Lemma mk_env_lshr_int_newer_res :
  forall w E g i E' g' (ls : w.-tuple literal) cs lrs,
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    mk_env_lshr_int E g ls i = (E', g', cs, lrs) ->
    newer_than_lits g' lrs.
Proof .
  move => w E g .
  elim .
  - move => E' g' ls cs lrs Hgtt Hgls .
    by case => _ <- _ <- .
  - move => n IH E' g' ls cs lrs Hgtt Hgls .
    move Htl : (mk_env_lshr_int E g ls n) => [[[E_tl g_tl] cs_tl] lrs_tl] .
    rewrite /= Htl .
    move H1 : (mk_env_lshr_int1 E_tl g_tl lrs_tl) =>
    [[[E1 g1] cs1] lrs1] .
    case => _ <- _ <- .
    move : (IH _ _ _ _ _ Hgtt Hgls Htl) => Hgtllrstl .
    move : (mk_env_lshr_int_newer_gen Htl) => Hggtl .
    move : (newer_than_lit_le_newer Hgtt Hggtl) => Hgtltt .
    apply (mk_env_lshr_int1_newer_res Hgtltt Hgtllrstl H1) .
Qed .

Lemma mk_env_lshr_rec_newer_res :
  forall w wn E g i E' g' (ls : w.-tuple literal) (ns : wn.-tuple literal)
         cs lrs,
    newer_than_lit g lit_tt ->
    newer_than_lits g ls -> newer_than_lits g ns ->
    mk_env_lshr_rec E g ls ns i = (E', g', cs, lrs) ->
    newer_than_lits g' lrs.
Proof .
  move => w .
  elim .
  - move => E g i E' g' ls ns cs lrs Hgtt Hgls Hgns .
    by case => _ <- _ <- .
  - move => n IH E g i E' g' ls /tupleP [ns_hd ns_tl] cs lrs Hgtt Hgls Hgns .
    rewrite /= !theadCons !beheadCons .
    case Henvtl : (mk_env_lshr_rec E g ls ns_tl (2*i))
    => [[[E_tl g_tl] cs_tl] ls_tl] .
    case Henvhd : (mk_env_lshr_int E_tl g_tl ls_tl i)
    => [[[E_hd g_hd] cs_hd] ls_hd] .
    move : (newer_than_lits_behead Hgns) .
    rewrite beheadCons => {Hgns} Hgns_tl .
    move : (IH _ _ _ _ _ _ _ _ _ Hgtt Hgls Hgns_tl Henvtl)
    => {Hgns_tl} Hgtllstl .
    case : (ns_hd == lit_tt) .
    + case => _ <- _ <- .
      move : (mk_env_lshr_rec_newer_gen Henvtl) => Hggtl .
      move : (newer_than_lit_le_newer Hgtt Hggtl) => Hgtltt .
      apply (mk_env_lshr_int_newer_res Hgtltt Hgtllstl Henvhd) .
    + case : (ns_hd == lit_ff) .
      * case => _ <- _ <- .
        done .
      * case Hite : (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl)
        => [[[E_ite g_ite] cs_ite] ls_ite] .
        case => _ <- _ <- .
        apply (mk_env_ite_newer_res Hite) .
Qed .

Lemma mk_env_lshr_newer_res :
  forall w E g (ls : w.-tuple literal) (ns : w.-tuple literal)
         E' g' cs lrs,
    newer_than_lit g lit_tt ->
    newer_than_lits g ls -> newer_than_lits g ns ->
    mk_env_lshr E g ls ns = (E', g', cs, lrs) ->
    newer_than_lits g' lrs.
Proof .
  move => w E g ls ns E' g' cs lrs .
  apply mk_env_lshr_rec_newer_res .
Qed .

Lemma mk_env_lshr_int1_newer_cnf :
  forall w E g (ls : w.-tuple literal) E' g' cs lr,
    mk_env_lshr_int1 E g ls = (E', g', cs, lr) ->
    newer_than_lits g ls ->
    newer_than_cnf g' cs.
Proof .
  case .
  - move => E g ls E' g' cs lr .
    by case => _ <- <- _ _ .
  - move => n E g ls E' g' cs lr /= .
    by case => _ <- <- _ .
Qed .

Lemma mk_env_lshr_int_newer_cnf :
  forall w E g (ls : w.-tuple literal) i E' g' cs lr,
    mk_env_lshr_int E g ls i = (E', g', cs, lr) ->
    newer_than_lit g lit_tt -> newer_than_lits g ls ->
    newer_than_cnf g' cs.
Proof .
  move => w E g ls .
  elim .
  - move => E' g' cs lr .
    by case => _ <- <- _ _ _ .
  - move => n IH E' g' cs lr .
    rewrite /= .
    case Hn : (mk_env_lshr_int E g ls n) => [[[E_m g_m] cs_m] ls_m] .
    case H1 : (mk_env_lshr_int1 E_m g_m ls_m) => [[[E1 g1] cs1] ls1] .
    case => _ <- <- _ Hgtt Hgls .
    rewrite newer_than_cnf_append .
    move : (IH _ _ _ _ Hn Hgtt Hgls) => Hgmcsm .
    move : (mk_env_lshr_int1_newer_gen H1) => Hgmg1 .
    move : (newer_than_cnf_le_newer Hgmcsm Hgmg1) => {Hgmcsm} Hg1csm .
    apply /andP; split; first trivial .
    apply (mk_env_lshr_int1_newer_cnf H1).
    apply (mk_env_lshr_int_newer_res Hgtt Hgls Hn) .
Qed .

Lemma mk_env_lshr_rec_newer_cnf :
  forall w wn E g (ls : w.-tuple literal) (ns : wn.-tuple literal) i
         E' g' cs lr,
    mk_env_lshr_rec E g ls ns i = (E', g', cs, lr) ->
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
    case Htl : (mk_env_lshr_rec E g ls ns_tl (2*i))
    => [[[E_tl g_tl] cs_tl] ls_tl] .
    case Hhd : (mk_env_lshr_int E_tl g_tl ls_tl i)
    => [[[E_hd g_hd] cs_hd] ls_hd] .
    case : (ns_hd == lit_tt) .
    + case => _ <- <- _ .
      move => Hgtt Hgls /andP [Hgnshd Hgnstl] .
      move : (IH _ _ _ _ _ _ _ _ _ Htl Hgtt Hgls Hgnstl) => Hgtlcstl .
      move : (mk_env_lshr_rec_newer_res Hgtt Hgls Hgnstl Htl) => Hgtllstl .
      move : (mk_env_lshr_rec_newer_gen Htl) => Hggtl .
      move : (newer_than_lit_le_newer Hgtt Hggtl) => Hgtltt .
      move : (mk_env_lshr_int_newer_cnf Hhd Hgtltt Hgtllstl) => Hghdcshd .
      move : (mk_env_lshr_int_newer_gen Hhd) => Hgtlghd .
      move : (newer_than_cnf_le_newer Hgtlcstl Hgtlghd)
      => Hghdcstl .
      rewrite newer_than_cnf_append .
      apply /andP; split; auto .
    + case : (ns_hd == lit_ff) .
      * case => _ <- <- _ .
        move => Hgtt Hgls /andP [Hgnshd Hgnstl] .
        apply (IH _ _ _ _ _ _ _ _ _ Htl Hgtt Hgls Hgnstl) .
      * case Hite : (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl)
        => [[[E_ite g_ite] cs_ite] ls_ite] .
        case => _ <- <- _ Hgtt Hgls /andP [Hgnshd Hgnstl] .
        move : (IH _ _ _ _ _ _ _ _ _ Htl Hgtt Hgls Hgnstl) => Hgtlcstl .
        move : (mk_env_lshr_rec_newer_res Hgtt Hgls Hgnstl Htl) => Hgtllstl .
        move : (mk_env_lshr_rec_newer_gen Htl)
        => { Htl Hgls Hgnstl } Hggtl .
        move : (newer_than_lit_le_newer Hgtt Hggtl)
                 (newer_than_lit_le_newer Hgnshd Hggtl)
        => { Hgtt Hgnshd Hggtl E g } Hgtltt Hgtlnshd .
        move : (mk_env_lshr_int_newer_cnf Hhd Hgtltt Hgtllstl) => Hghdcshd .
        move : (mk_env_lshr_int_newer_res Hgtltt Hgtllstl Hhd) => Hghdlshd .
        move : (mk_env_lshr_int_newer_gen Hhd)
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

Lemma mk_env_lshr_newer_cnf :
  forall w E g (ls ns : w.-tuple literal) E' g' cs lrs,
    mk_env_lshr E g ls ns = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls -> newer_than_lits g ns ->
    newer_than_cnf g' cs.
Proof .
  rewrite /mk_env_lshr .
  move => w E g ls ns E' g' cs lrs .
  exact : mk_env_lshr_rec_newer_cnf .
Qed .

Lemma mk_env_lshr_int1_preserve :
  forall w E g (ls : w.-tuple literal) E' g' cs lrs,
    mk_env_lshr_int1 E g ls = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof .
  case .
  - move => E g ls E' g' cs lrs .
    by case => <- _ _ _ .
  - move => n E g ls E' g' cs lrs /= .
    by case => <- _ _ _ .
Qed .

Lemma mk_env_lshr_int_preserve :
  forall w E g (ls : w.-tuple literal) i E' g' cs lrs,
    mk_env_lshr_int E g ls i = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof .
  move => w E g ls .
  elim .
  - move => E' g' cs lrs .
    by case => <- -> _ _ .
  - move => n IH E' g' cs lrs .
    case Hn : (mk_env_lshr_int E g ls n) => [[[En gn] csn] lrsn] .
    move : (IH _ _ _ _ Hn) => HEEn .
    rewrite /= Hn .
    move H1 : (mk_env_lshr_int1 En gn lrsn) => [[[E1 g1] cs1] lrs1] .
    case => <- _ _ _ .
    move : (mk_env_lshr_int_newer_gen Hn) => Hggn .
    move : (mk_env_lshr_int1_preserve H1) => HEnE1 .
    move : HEEn (env_preserve_le HEnE1 Hggn) .
    apply env_preserve_trans .
Qed .

Lemma mk_env_lshr_rec_preserve :
  forall w wn E g (ls : w.-tuple literal) (ns : wn.-tuple literal) i
         E' g' cs lrs,
    mk_env_lshr_rec E g ls ns i = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof .
  move => w .
  elim .
  - move => E g ls ns i E' g' cs lrs .
    case => -> _ _ _ .
    exact : env_preserve_refl .
  - move => n IH E g ls /tupleP [ns_hd ns_tl] i E' g' cs lrs .
    rewrite /= !theadCons !beheadCons .
    case Htl : (mk_env_lshr_rec E g ls ns_tl (2*i))
    => [[[E_tl g_tl] cs_tl] ls_tl] .
    move : (IH _ _ _ _ _ _ _ _ _ Htl) => HEEtl .
    move : (mk_env_lshr_rec_newer_gen Htl) => {Htl} Hggtl .
    case Hhd : (mk_env_lshr_int E_tl g_tl ls_tl i)
      => [[[E_hd g_hd] cs_hd] ls_hd] .
    move : (mk_env_lshr_int_preserve Hhd) => HEtlEhd .
    move : (env_preserve_le HEtlEhd Hggtl)
    => { HEtlEhd } HEtlEhd .
    case : (ns_hd == lit_tt) .
    + case => <- _ _ _ .
      by apply (env_preserve_trans HEEtl) .
    + case : (ns_hd == lit_ff) .
      * by case => <- .
      * move : (mk_env_lshr_int_newer_gen Hhd) => Hghdgtl .
        case Hite : (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl)
        => [[[E_ite g_ite] cs_ite] ls_ite] .
        case => <- _ _ _ .
        move : (mk_env_ite_preserve Hite) => HEEite .
        move : (env_preserve_le HEEite Hghdgtl) => {HEEite} HEEite .
        move : (env_preserve_le HEEite Hggtl) => {HEEite} .
        apply env_preserve_trans .
        by apply (env_preserve_trans HEEtl) .
Qed .

Lemma mk_env_lshr_preserve :
  forall w E g (ls ns : w.-tuple literal) E' g' cs lrs,
    mk_env_lshr E g ls ns = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof .
  move => w E g ls ns E' g' cs lrs .
  rewrite /mk_env_lshr. exact : mk_env_lshr_rec_preserve .
Qed .

Lemma mk_env_lshr_int1_sat :
  forall w E g (ls : w.-tuple literal) E' g' cs lrs,
    mk_env_lshr_int1 E g ls = (E', g', cs, lrs) ->
    newer_than_lits g ls ->
    interp_cnf E' cs.
Proof .
  case .
  - move => E g ls E' g' cs lrs .
    by case => <- _ <- _ _ .
  - move => n E g ls E' g' cs lrs /= .
    by case => <- _ <- _ _ .
Qed .

Lemma mk_env_lshr_int_sat :
  forall w E g (ls : w.-tuple literal) i E' g' cs lrs,
    mk_env_lshr_int E g ls i = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt -> newer_than_lits g ls ->
    interp_cnf E' cs.
Proof .
  move => w E g ls .
  elim .
  - move => E' g' cs lrs .
    by case => _ _ <- _ _ .
  - move => n IH E' g' cs lrs .
    case Hn : (mk_env_lshr_int E g ls n) => [[[En gn] csn] lsn] .
    rewrite /= Hn .
    case H1 : (mk_env_lshr_int1 En gn lsn) => [[[E1 g1] cs1] ls1] .
    case => <- _ <- _ Hgtt Hgls .
    move : (IH _ _ _ _ Hn Hgtt Hgls) => Hcsn .
    move : (mk_env_lshr_int_newer_res Hgtt Hgls Hn) => Hgnlsn .
    move : (mk_env_lshr_int1_sat H1 Hgnlsn) => HE1cs1 .
    move : (mk_env_lshr_int1_preserve H1) => HEnE1 .
    move : (mk_env_lshr_int_newer_cnf Hn Hgtt Hgls) => Hgncsn .
    rewrite -(env_preserve_cnf HEnE1 Hgncsn) in Hcsn .
    rewrite interp_cnf_append .
    apply /andP; split; trivial .
Qed .

Lemma mk_env_lshr_rec_sat :
  forall w wn E g (ls : w.-tuple literal) (ns : wn.-tuple literal) i
         E' g' cs lrs,
    mk_env_lshr_rec E g ls ns i = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt -> 
    newer_than_lits g ls -> newer_than_lits g ns ->
    interp_cnf E' cs.
Proof .
  move => w .
  elim .
  - move => E g ls ns i E' g' cs lrs .
    by case => _ _ <- _ _ _ .
  - move => n IH E g ls /tupleP [ns_hd ns_tl] i E' g' cs lrs .
    case Htl : (mk_env_lshr_rec E g ls ns_tl (2 * i))
    => [[[E_tl g_tl] cs_tl] ls_tl] .
    case Hhd : (mk_env_lshr_int E_tl g_tl ls_tl i)
    => [[[E_hd g_hd] cs_hd] ls_hd] .
    rewrite /= !theadCons !beheadCons Htl Hhd .
    case : (ns_hd == lit_tt) .
    + case => <- _ <- _ Hgtt Hgls /andP [Hgnshd Hgnstl] .
      move : (IH _ _ _ _ _ _ _ _ _ Htl Hgtt Hgls Hgnstl) => HEtlcstl .
      move : (mk_env_lshr_rec_newer_res Hgtt Hgls Hgnstl Htl) => Hgtllstl .
      move : (mk_env_lshr_rec_newer_gen Htl) => Hggtl .
      move : (newer_than_lit_le_newer Hgtt Hggtl) => Hgtltt .
      move : (mk_env_lshr_int_sat Hhd Hgtltt Hgtllstl) => HEhdcshd .
      rewrite interp_cnf_append .
      apply /andP; split; last done .
      move : (mk_env_lshr_int_preserve Hhd) => HEtlEhd .
      move : (mk_env_lshr_rec_newer_cnf Htl Hgtt Hgls Hgnstl) => Hgtlcstl .
      by rewrite (env_preserve_cnf HEtlEhd Hgtlcstl) .
    + case : (ns_hd == lit_ff) .
      * case => <- _ <- _ Hgtt Hgls /andP [Hgnshd Hgnstl] .
        by apply (IH _ _ _ _ _ _ _ _ _ Htl Hgtt Hgls Hgnstl) .
      * case Hite : (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl)
        => [[[E_ite g_ite] cs_ite] ls_ite] .
        case => <- _ <- _ Hgtt Hgls /andP [Hgnshd Hgnstl] .
        move : (mk_env_lshr_rec_newer_cnf Htl Hgtt Hgls Hgnstl) => Hgtlcstl .
        move : (mk_env_lshr_int_preserve Hhd) => HEtlEhd .
        move : (IH _ _ _ _ _ _ _ _ _ Htl Hgtt Hgls Hgnstl) .
        rewrite -(env_preserve_cnf HEtlEhd Hgtlcstl)
        => {HEtlEhd} HEhdcstl .
        move : (mk_env_lshr_int_newer_gen Hhd) => Hgtlghd .
        move : (newer_than_cnf_le_newer Hgtlcstl Hgtlghd)
        => {Hgtlcstl Hgtlghd} Hghdcstl .
        move : (mk_env_ite_preserve Hite) HEhdcstl => HEhdEite .
        rewrite -(env_preserve_cnf HEhdEite Hghdcstl) => Hitecstl .
        move : (mk_env_lshr_rec_newer_res Hgtt Hgls Hgnstl Htl)
        => {Hgnstl} Hgtllstl .
        move : (mk_env_lshr_rec_newer_gen Htl) => Hggtl .
        move : (newer_than_lit_le_newer Hgnshd Hggtl) => Hgtlnshd .
        move : (newer_than_lit_le_newer Hgtt Hggtl)
        => { Hgtt Hggtl Hgnshd Htl E } => Hgtltt .
        move : (mk_env_lshr_int_newer_cnf Hhd Hgtltt Hgtllstl) => Hghdcshd .
        move : (mk_env_lshr_int_sat Hhd Hgtltt Hgtllstl) .
        rewrite -(env_preserve_cnf HEhdEite Hghdcshd) => HEitecshd .
        move : (mk_env_lshr_int_newer_res Hgtltt Hgtllstl Hhd) => Hghdlshd .
        move : (mk_env_lshr_int_newer_gen Hhd) => Hgtlghd .
        move : (newer_than_lit_le_newer Hgtlnshd Hgtlghd) => Hghdnshd .
        move : (newer_than_lits_le_newer Hgtllstl Hgtlghd)
        => { Hgtlnshd Hgtllstl Hgtlghd } Hghdlstl .
        move : (mk_env_ite_sat Hite Hghdnshd Hghdlshd Hghdlstl)
        => { Hghdnshd Hghdlshd Hghdlstl } => HEitecsite .
        rewrite !interp_cnf_append .
        apply /andP; split; first done; apply /andP; split; done .
Qed .

Lemma mk_env_lshr_sat :
  forall w E g (ls ns : w.-tuple literal) E' g' cs lrs,
    mk_env_lshr E g ls ns = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls -> newer_than_lits g ns ->
    interp_cnf E' cs.
Proof .
  move => w E g ls ns E' g' cs lrs .
  rewrite /mk_env_lshr; exact : mk_env_lshr_rec_sat .
Qed .
