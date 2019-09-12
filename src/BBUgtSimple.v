
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNFSimple BBCommonSimple BBUltSimple.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_ugt ===== *)

(*Parameter bit_blast_ugt : forall w : nat, generator -> w.-tuple literal -> w.-tuple literal -> generator * cnf * literal.
 *)
Definition bit_blast_ugt w (g: generator) (ls1 ls2: w.-tuple literal) :generator * cnf * literal :=
  bit_blast_ult g ls2 ls1.

Definition mk_env_ugt w E g (ls1 ls2: w.-tuple literal) : env * generator * cnf * literal :=
  mk_env_ult E g ls2 ls1.

Lemma bit_blast_ugt_correct :
  forall w g (bs1 bs2 : BITS w) E g' ls1 ls2 cs lr,
    bit_blast_ugt g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (ltB bs2 bs1).
Proof.
  move => w g ibs1 ibs2 E g' ils1 ils2 cs olr.
  rewrite /bit_blast_ugt.
  move => Hult Henc1 Henc2 Hcnf.
  move : (bit_blast_ult_correct Hult Henc2 Henc1 Hcnf) => Hrult.
  symmetry; done.
Qed.

Lemma mk_env_ugt_is_bit_blast_ugt :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_ugt E g ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_ugt g ls1 ls2 = (g', cs, lrs).
Proof.
  move=> w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_ugt /bit_blast_ugt.
  exact: mk_env_ult_is_bit_blast_ult.
Qed.

Lemma mk_env_ugt_newer_gen :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_ugt E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  move=> w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_ugt.
  exact: mk_env_ult_newer_gen.
Qed.

Lemma mk_env_ugt_newer_res :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_ugt E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lit g' lr.
Proof.
  move=> w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_ugt. move=> H Hnew_gtt.
  exact: (mk_env_ult_newer_res H Hnew_gtt).
Qed.

Lemma mk_env_ugt_newer_cnf :
forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
  mk_env_ugt E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_ugt.
  move=> H e0 e1 e2.
  exact: (mk_env_ult_newer_cnf H e0 e2 e1).
Qed.

Lemma mk_env_ugt_preserve :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_ugt E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  move=> w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_ugt.
  exact: mk_env_ult_preserve.
Qed.

Lemma mk_env_ugt_sat :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_ugt E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_ugt.
  move=> H e0 e1 e2.
  exact: (mk_env_ult_sat H e0 e2 e1).
Qed.
