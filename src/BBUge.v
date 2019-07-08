
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNF BBCommon BBUle.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_uge ===== *)

(*Parameter bit_blast_uge : forall w : nat, generator -> w.-tuple literal -> w.-tuple literal -> generator * cnf * literal.
 *)

Definition bit_blast_uge w (g: generator) (ls1 ls2: w.-tuple literal) :generator * cnf * literal :=
  bit_blast_ule g ls2 ls1.

Definition mk_env_uge w E g (ls1 ls2: w.-tuple literal) : env * generator * cnf * literal :=
  mk_env_ule E g ls2 ls1.

Lemma bit_blast_uge_correct :
  forall w g (bs1 bs2 : BITS w) E g' ls1 ls2 cs lr,
    bit_blast_uge g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (leB bs2 bs1).
Proof.
  move => w g ibs1 ibs2 E g' ils1 ils2 cs olr.
  rewrite /bit_blast_uge.
  move => Hule Henc1 Henc2 Hcnf.
  move : (bit_blast_ule_correct Hule Henc2 Henc1 Hcnf) => Hrule.
  symmetry; done.
Qed.

Lemma mk_env_uge_is_bit_blast_uge :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lrs,
    mk_env_uge E g ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_uge g ls1 ls2 = (g', cs, lrs).
Proof.
  move=> w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_uge /bit_blast_uge.
  exact: mk_env_ule_is_bit_blast_ule.
Qed.

Lemma mk_env_uge_newer_gen :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_uge E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  move=> w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_uge.
  exact: mk_env_ule_newer_gen.
Qed.

Lemma mk_env_uge_newer_res :
  forall w E g (ls1 ls2: w.-tuple literal) E' g' cs lr,
    mk_env_uge E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g' lr.
Proof.
  move=> w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_uge. move=> H.
  exact: (mk_env_ule_newer_res H).
Qed.

Lemma mk_env_uge_newer_cnf :
forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
  mk_env_uge E g ls1 ls2 = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_uge.
  move=> H e0 e1 e2.
  exact: (mk_env_ule_newer_cnf H e0 e2 e1).
Qed.

Lemma mk_env_uge_preserve :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_uge E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  move=> w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_uge.
  exact: mk_env_ule_preserve.
Qed.

Lemma mk_env_uge_sat :
  forall w E g (ls1 ls2 : w.-tuple literal) E' g' cs lr,
    mk_env_uge E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_uge.
  move=> H e0 e1 e2.
  exact: (mk_env_ule_sat H e0 e2 e1).
Qed.
