
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon BBSle.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_sge ===== *)

(*Parameter bit_blast_sge : forall w : nat, generator -> w.+1.-tuple literal -> w.+1.-tuple literal -> generator * cnf * literal.
 *)
Definition bit_blast_sge w (g: generator) (ls1 ls2 : w.+1.-tuple literal) : generator * cnf * literal :=
  bit_blast_sle g ls2 ls1.

Lemma bit_blast_sge_correct_iff :
  forall w g (bs1 bs2 : BITS w.+1) E g' ls1 ls2 cs lr,
    bit_blast_sge g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    interp_lit E lr <-> (toZ bs1 >= toZ bs2)%Z.
Proof.
  move => w g ibs1 ibs2 E g' ils11 ils2 cs olr.
  rewrite /bit_blast_sge.
  move => Hsle Henc1 Henc2 Hcnf.
  move : (bit_blast_sle_correct_iff Hsle Henc2 Henc1 Hcnf) => Hrsle.
  rewrite Hrsle; omega.
Qed.

Lemma bit_blast_sge_correct :
  forall w g (bs1 bs2 : BITS (w.+1)) E g' ls1 ls2 cs lr,
    bit_blast_sge g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (Z.geb (toZ bs1) (toZ bs2)).
Proof.
  move=> w g bs1 bs2 E g' ls1 ls2 cs lr Hslt Hl1b1 Hl2b2 HiEcs.
  move : (bit_blast_sge_correct_iff Hslt Hl1b1 Hl2b2 HiEcs) => H.
  rewrite /enc_bit. apply iffBool. rewrite H Z.ge_le_iff Z.geb_leb -Z.leb_le.
  done.
Qed.

Definition mk_env_sge w (E : env) g (ls1 ls2 : w.+1.-tuple literal) : env * generator * cnf * literal :=
  mk_env_sle E g ls2 ls1.

Lemma mk_env_sge_is_bit_blast_sge :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_sge E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_sge g ls1 ls2 = (g', cs, lr).
Proof.
  move=> w E g ls1 ls2 E' g' cs lr.
  rewrite /mk_env_sge /bit_blast_sge. 
  exact: mk_env_sle_is_bit_blast_sle.
Qed.

Lemma mk_env_sge_newer_gen :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_sge E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_sge.
  exact: mk_env_sle_newer_gen.
Qed.

Lemma mk_env_sge_newer_res :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_sge E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g' lr.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_sge.
  exact: mk_env_sle_newer_res.
Qed.  

Lemma mk_env_sge_newer_cnf :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_sge E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_sge.
  move=> Hmksle Hgt Hgl1 Hgl2.
  exact (mk_env_sle_newer_cnf Hmksle Hgt Hgl2 Hgl1).
Qed.

Lemma mk_env_sge_preserve :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_sge E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_sge.
  exact: mk_env_sle_preserve.
Qed.

Lemma mk_env_sge_sat :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_sge E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_sge.
  move=> Hmksle Hgt Hgl1 Hgl2.
  exact: (mk_env_sle_sat Hmksle Hgt Hgl2 Hgl1).
Qed.
