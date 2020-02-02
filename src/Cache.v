From Coq Require Import ZArith OrderedType Bool.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq tuple fintype choice.
From ssrlib Require Import FMaps Var.
From BitBlasting Require Import QFBV CNF State.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module ExpMap <: SsrFMap := FMaps.MakeTreeMap QFBV.ExpOrder.
Module BexpMap <: SsrFMap := FMaps.MakeTreeMap QFBV.BexpOrder.

Definition cexpm := ExpMap.t word.
Definition cbexpm := BexpMap.t literal.
Definition hexpm := ExpMap.t (cnf * word).
Definition hbexpm := BexpMap.t (cnf * literal).

Record cache :=
  { (* store all historical results *)
    het : hexpm;
    hbt : hbexpm;
    (* store the current results *)
    cet : cexpm;
    cbt : cbexpm }.

Definition well_formed (c : cache) : Prop := 
  (forall e ls, ExpMap.find e (cet c) = Some ls 
                -> exists cs, ExpMap.find e (het c) = Some (cs, ls))
  /\ forall e l, BexpMap.find e (cbt c) = Some l
                 -> exists cs, BexpMap.find e (hbt c) = Some (cs, l).

Definition find_het e c := ExpMap.find e (het c).
Definition find_hbt e c := BexpMap.find e (hbt c).
Definition find_cet e c := ExpMap.find e (cet c).
Definition find_cbt e c := BexpMap.find e (cbt c).

Definition add_het e cs ls c := 
  {| het := ExpMap.add e (cs, ls) (het c);
     hbt := hbt c;
     cet := cet c;
     cbt := cbt c |}.
Definition add_hbt e cs l c := 
  {| het := het c;
     hbt := BexpMap.add e (cs, l) (hbt c);
     cet := cet c;
     cbt := cbt c |}.
Definition add_cet e ls c := 
  {| het := het c;
     hbt := hbt c;
     cet := ExpMap.add e ls (cet c);
     cbt := cbt c |}.
Definition add_cbt e l c := 
  {| het := het c;
     hbt := hbt c;
     cet := cet c;
     cbt := BexpMap.add e l (cbt c) |}.

Definition regular (E : env) (c : cache) :=
  (forall e cs ls, ExpMap.find e (het c) = Some (cs, ls) -> interp_cnf E cs)
  /\ forall e cs l, BexpMap.find e (hbt c) = Some (cs, l) -> interp_cnf E cs.

Lemma regular_add_cet :
  forall E c e ls, regular E c <-> regular E (add_cet e ls c).
Proof.
  move=> E c e ls. by rewrite /regular. 
Qed.

Lemma regular_add_cbt :
  forall E c e l, regular E c <-> regular E (add_cbt e l c).
Proof.
  move=> E c e ls. by rewrite /regular. 
Qed.

Lemma regular_add_het :
  forall E c e cs ls, regular E c /\ interp_cnf E cs ->
                      regular E (add_het e cs ls c).
Proof.
  move=> E c e cs ls [[Hce Hcb] Hcs]. rewrite /regular /=. split; last done.
  move=> e0 cs0 ls0. case Heq : (e0 == e).
  - rewrite (ExpMap.Lemmas.find_add_eq Heq). case=> <- _; done.
  - move/negP: Heq => Heq. rewrite (ExpMap.Lemmas.find_add_neq Heq).
    exact: Hce.
Qed.

Lemma regular_add_hbt :
  forall E c e cs l, regular E c /\ interp_cnf E cs ->
                     regular E (add_hbt e cs l c).
Proof.
  move=> E c e cs l [[Hce Hcb] Hcs]. rewrite /regular /=. split; first done.
  move=> e0 cs0 l0. case Heq : (e0 == e).
  - rewrite (BexpMap.Lemmas.find_add_eq Heq). case=> <- _; done.
  - move/negP: Heq => Heq. rewrite (BexpMap.Lemmas.find_add_neq Heq).
    exact: Hcb.
Qed.

Definition correct_ct (E : env) (s : SSAStore.t) (c : cache) :=
  (forall e ls, ExpMap.find e (cet c) = Some ls -> enc_bits E ls (QFBV.eval_exp e s))
  /\ forall e l, BexpMap.find e (cbt c) = Some l -> enc_bit E l (QFBV.eval_bexp e s).

Definition correct_ht (E : env) (s : SSAStore.t) (c : cache) :=
  (forall e cs ls, ExpMap.find e (het c) = Some (cs, ls) 
                   -> enc_bits E ls (QFBV.eval_exp e s))
  /\ forall e cs l, BexpMap.find e (hbt c) = Some (cs, l) 
                    -> enc_bit E l (QFBV.eval_bexp e s).

Definition correct := correct_ht.

Lemma correct_well_formed_correct_ct :
  forall E s c, correct E s c -> well_formed c -> correct_ct E s c.
Proof.
Admitted.

Lemma correct_add_cet :
  forall E s c e ls, correct E s c <-> correct E s (add_cet e ls c).
Proof.
  move=> E s c e ls. by rewrite /correct. 
Qed.

Lemma correct_add_cbt :
  forall E s c e l, correct E s c <-> correct E s (add_cbt e l c).
Proof.
  move=> E c e ls. by rewrite /correct. 
Qed.

Lemma correct_add_het :
  forall E s c e cs ls, correct E s c /\ enc_bits E ls (QFBV.eval_exp e s) ->
                        correct E s (add_het e cs ls c).
Proof.
  move=> E s c e cs ls [[Hce Hcb] Hence]. rewrite /correct /=. split; last done.
  move=> e0 cs0 ls0. case Heq : (e0 == e).
  - rewrite (ExpMap.Lemmas.find_add_eq Heq). move/eqP: Heq => Heq.
    rewrite Heq. case=> _ <-; done.
  - move/negP: Heq => Heq. rewrite (ExpMap.Lemmas.find_add_neq Heq).
    exact: Hce.
Qed.

Lemma correct_add_hbt :
  forall E s c e cs l, correct E s c /\ enc_bit E l (QFBV.eval_bexp e s) ->
                       correct E s (add_hbt e cs l c).
Proof.
  move=> E s c e cs l [[Hce Hcb] Hence]. rewrite /correct /=. split; first done.
  move=> e0 cs0 l0. case Heq : (e0 == e).
  - rewrite (BexpMap.Lemmas.find_add_eq Heq). move/eqP: Heq => Heq.
    rewrite Heq. case=> _ <-; done.
  - move/negP: Heq => Heq. rewrite (BexpMap.Lemmas.find_add_neq Heq).
    exact: Hcb.
Qed.

Definition newer_than_ct g (c : cache) :=
  (forall e ls, ExpMap.find e (cet c) = Some ls -> newer_than_lits g ls)
  /\ forall e l, BexpMap.find e (cbt c) = Some l -> newer_than_lit g l.

Definition newer_than_ht g (c : cache) :=
  (forall e cs ls, ExpMap.find e (het c) = Some (cs, ls) 
                   -> newer_than_cnf g cs && newer_than_lits g ls)
  /\ forall e cs l, BexpMap.find e (hbt c) = Some (cs, l) 
                    -> newer_than_cnf g cs && newer_than_lit g l.

Definition newer_than_cache := newer_than_ht.

Lemma newer_than_cache_well_formed_newer_ct :
  forall g c, newer_than_cache g c -> well_formed c -> newer_than_ct g c.
Proof.
Admitted.

Lemma env_preserve_regular E E' g ca :
  env_preserve E E' g -> newer_than_cache g ca ->
  regular E' ca <-> regular E ca.
Proof.
  move=> Henv [Hge Hgb]. rewrite /regular. split.
  - apply env_preserve_sym in Henv. move=> [H1 H2]. 
    split; move=> e cs ls Hfind.
    + move: (Hge _ _ _ Hfind) => /andP [Hgcs _].
      rewrite (env_preserve_cnf Henv Hgcs). exact: (H1 _ _ _ Hfind).
    + move: (Hgb _ _ _ Hfind) => /andP [Hgcs _].
      rewrite (env_preserve_cnf Henv Hgcs). exact: (H2 _ _ _ Hfind).
  - move=> [H1 H2]. 
    split; move=> e cs ls Hfind.
    + move: (Hge _ _ _ Hfind) => /andP [Hgcs _].
      rewrite (env_preserve_cnf Henv Hgcs). exact: (H1 _ _ _ Hfind).
    + move: (Hgb _ _ _ Hfind) => /andP [Hgcs _].
      rewrite (env_preserve_cnf Henv Hgcs). exact: (H2 _ _ _ Hfind).
Qed.    


