
From Coq Require Import ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Var SsrOrder ZAriths Tactics.
From BitBlasting Require Import QFBV.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Section HashedQFBV.

  Import QFBV.

  Inductive hashed_exp : Type :=
  | HEvar : SSAVarOrder.t -> hashed_exp
  | HEconst : bits -> hashed_exp
  | HEunop : eunop -> hexp -> hashed_exp
  | HEbinop : ebinop -> hexp -> hexp -> hashed_exp
  | HEite : hbexp -> hexp -> hexp -> hashed_exp
  with
    hashed_bexp : Type :=
  | HBfalse : hashed_bexp
  | HBtrue : hashed_bexp
  | HBbinop : bbinop -> hexp -> hexp -> hashed_bexp
  | HBlneg : hbexp -> hashed_bexp
  | HBconj : hbexp -> hbexp -> hashed_bexp
  | HBdisj : hbexp -> hbexp -> hashed_bexp
  with hexp : Type :=
  | epair : hashed_exp -> Z -> hexp
  with hbexp : Type :=
  | bpair : hashed_bexp -> Z -> hbexp.

  Definition ehobj (e : hexp) : hashed_exp :=
    match e with
    | epair e h => e
    end.

  Definition ehval (e : hexp) : Z :=
    match e with
    | epair e h => h
    end.

  Definition bhobj (e : hbexp) : hashed_bexp :=
    match e with
    | bpair e h => e
    end.

  Definition bhval (e : hbexp) : Z :=
    match e with
    | bpair e h => h
    end.

  Fixpoint unhash_hashed_exp (e : hashed_exp) : exp :=
    match e with
    | HEvar v => Evar v
    | HEconst bs => Econst bs
    | HEunop op e => Eunop op (unhash_hexp e)
    | HEbinop op e1 e2 => Ebinop op (unhash_hexp e1) (unhash_hexp e2)
    | HEite b e1 e2 => Eite (unhash_hbexp b) (unhash_hexp e1) (unhash_hexp e2)
    end
  with
  unhash_hashed_bexp (e : hashed_bexp) : bexp :=
    match e with
    | HBfalse => Bfalse
    | HBtrue => Btrue
    | HBbinop op e1 e2 => Bbinop op (unhash_hexp e1) (unhash_hexp e2)
    | HBlneg e => Blneg (unhash_hbexp e)
    | HBconj e1 e2 => Bconj (unhash_hbexp e1) (unhash_hbexp e2)
    | HBdisj e1 e2 => Bdisj (unhash_hbexp e1) (unhash_hbexp e2)
    end
  with
  unhash_hexp (e : hexp) : exp :=
    match e with
    | epair e _ => unhash_hashed_exp e
    end
  with
  unhash_hbexp (e : hbexp) : bexp :=
    match e with
    | bpair e _ => unhash_hashed_bexp e
    end.

  Coercion unhash_hashed_exp : hashed_exp >-> exp.
  Coercion unhash_hashed_bexp : hashed_bexp >-> bexp.
  Coercion unhash_hexp : hexp >-> exp.
  Coercion unhash_hbexp : hbexp >-> bexp.


End HashedQFBV.


Section HashFunc.

  Import QFBV.

  Definition hash_f : Type := (exp -> Z) * (bexp -> Z).

  (* Naive hash functions that compute the sizes of expressions *)
  Fixpoint ehf (e : exp) : Z :=
    match e with
    | Evar _ | Econst _ => 1
    | Eunop _ e => ehf e + 1
    | Ebinop _ e1 e2 => ehf e1 + ehf e2 + 1
    | Eite b e1 e2 => bhf b + ehf e1 + ehf e2 + 1
    end
  with
  bhf (e : bexp) : Z :=
    match e with
    | Bfalse | Btrue => 1
    | Bbinop _ e1 e2 => ehf e1 + ehf e2 + 1
    | Blneg e => bhf e + 1
    | Bconj e1 e2 | Bdisj e1 e2 => bhf e1 + bhf e2 + 1
    end.

  Definition shf : hash_f := (ehf, bhf).

  Fixpoint well_formed_hashed_exp (e : hashed_exp) : bool :=
    match e with
    | HEvar _ | HEconst _ => true
    | HEunop _ e => well_formed_hexp e
    | HEbinop _ e1 e2 => well_formed_hexp e1 && well_formed_hexp e2
    | HEite b e1 e2 =>
      well_formed_hbexp b && well_formed_hexp e1 && well_formed_hexp e2
    end
  with
  well_formed_hashed_bexp (e : hashed_bexp) : bool :=
    match e with
    | HBfalse | HBtrue => true
    | HBbinop _ e1 e2 => well_formed_hexp e1 && well_formed_hexp e2
    | HBlneg e => well_formed_hbexp e
    | HBconj e1 e2 | HBdisj e1 e2 => well_formed_hbexp e1 && well_formed_hbexp e2
    end
  with
  well_formed_hexp (e : hexp) : bool :=
    match e with
    | epair e h => (h == shf.1 e) && well_formed_hashed_exp e
    end
  with
  well_formed_hbexp (e : hbexp) : bool :=
    match e with
    | bpair e h => (h == shf.2 e) && well_formed_hashed_bexp e
    end.

  Fixpoint hash_exp (e : exp) : hexp :=
    match e with
    | Evar v => epair (HEvar v) 1
    | Econst bs => epair (HEconst bs) 1
    | Eunop op e => let he := hash_exp e in
                    epair (HEunop op he) (ehval he + 1)
    | Ebinop op e1 e2 => let he1 := hash_exp e1 in
                         let he2 := hash_exp e2 in
                         epair (HEbinop op he1 he2) (ehval he1 + ehval he2 + 1)
    | Eite b e1 e2 => let hb := hash_bexp b in
                      let he1 := hash_exp e1 in
                      let he2 := hash_exp e2 in
                      epair (HEite hb he1 he2) (bhval hb + ehval he1 + ehval he2 + 1)
    end
  with
  hash_bexp (e : bexp) : hbexp :=
    match e with
    | Bfalse => bpair HBfalse 1
    | Btrue => bpair HBtrue 1
    | Bbinop op e1 e2 => let he1 := hash_exp e1 in
                         let he2 := hash_exp e2 in
                         bpair (HBbinop op he1 he2) (ehval he1 + ehval he2 + 1)
    | Blneg e => let he := hash_bexp e in
                 bpair (HBlneg he) (bhval he + 1)
    | Bconj e1 e2 => let he1 := hash_bexp e1 in
                     let he2 := hash_bexp e2 in
                     bpair (HBconj he1 he2) (bhval he1 + bhval he2 + 1)
    | Bdisj e1 e2 => let he1 := hash_bexp e1 in
                     let he2 := hash_bexp e2 in
                     bpair (HBdisj he1 he2) (bhval he1 + bhval he2 + 1)
    end.

  Definition make_hashed_exp (e : exp) : hashed_exp :=
    ehobj (hash_exp e).

  Definition make_hashed_bexp (e : bexp) : hashed_bexp :=
    bhobj (hash_bexp e).

  Lemma ehval_hash_exp e : ehval (hash_exp e) = ehf e
  with bhval_hash_bexp e : bhval (hash_bexp e) = bhf e.
  Proof.
    (* ehval_hash_exp *)
    - case: e => //=.
      + move=> _ e. move: (ehval_hash_exp e). rewrite /ehval /=.
        case: (hash_exp e). move=> _ h <-. reflexivity.
      + move=> _ e1 e2. move: (ehval_hash_exp e1) (ehval_hash_exp e2).
        rewrite /ehval. case: (hash_exp e1); case: (hash_exp e2).
        move=> _ h1 _ h2 <- <-. reflexivity.
      + move=> b e1 e2.
        move: (bhval_hash_bexp b) (ehval_hash_exp e1) (ehval_hash_exp e2).
        rewrite /ehval /bhval.
        case: (hash_bexp b); case: (hash_exp e1); case: (hash_exp e2).
        move=> _ h _ h1 _ h2 <- <- <-. reflexivity.
    (* bhval_hash_bexp *)
    - case: e => //=.
      + move=> _ e1 e2. move: (ehval_hash_exp e1) (ehval_hash_exp e2).
        rewrite /ehval. case: (hash_exp e1); case: (hash_exp e2).
        move=> _ h1 _ h2 <- <-. reflexivity.
      + move=> e. move: (bhval_hash_bexp e). rewrite /bhval /=.
        case: (hash_bexp e). move=> _ h <-. reflexivity.
      + move=> e1 e2. move: (bhval_hash_bexp e1) (bhval_hash_bexp e2).
        rewrite /bhval. case: (hash_bexp e1); case: (hash_bexp e2).
        move=> _ h1 _ h2 <- <-. reflexivity.
      + move=> e1 e2. move: (bhval_hash_bexp e1) (bhval_hash_bexp e2).
        rewrite /bhval. case: (hash_bexp e1); case: (hash_bexp e2).
        move=> _ h1 _ h2 <- <-. reflexivity.
  Qed.

  Lemma unhash_make_hashed_exp e : unhash_hashed_exp (make_hashed_exp e) = e
  with unhash_make_hashed_bexp e : unhash_hashed_bexp (make_hashed_bexp e) = e
  with unhash_hash_exp e : unhash_hexp (hash_exp e) = e
  with unhash_hash_bexp e : unhash_hbexp (hash_bexp e) = e.
  Proof.
    (* unhash_make_hashed_exp *)
    - case: e => //=.
      + move=> op e. rewrite unhash_hash_exp. reflexivity.
      + move=> op e1 e2. rewrite !unhash_hash_exp. reflexivity.
      + move=> b e1 e2. rewrite unhash_hash_bexp !unhash_hash_exp. reflexivity.
    (* unhash_make_hashed_bexp *)
    - case: e => //=.
      + move=> op e1 e2. rewrite !unhash_hash_exp. reflexivity.
      + move=> e. rewrite unhash_hash_bexp. reflexivity.
      + move=> e1 e2. rewrite !unhash_hash_bexp. reflexivity.
      + move=> e1 e2. rewrite !unhash_hash_bexp. reflexivity.
    (* unhash_hash_exp *)
    - case: e => //=.
      + move=> op e. rewrite unhash_hash_exp. reflexivity.
      + move=> op e1 e2. rewrite !unhash_hash_exp. reflexivity.
      + move=> b e1 e2. rewrite unhash_hash_bexp !unhash_hash_exp. reflexivity.
    (* unhash_hash_bexp *)
    - case: e => //=.
      + move=> op e1 e2. rewrite !unhash_hash_exp. reflexivity.
      + move=> e. rewrite unhash_hash_bexp. reflexivity.
      + move=> e1 e2. rewrite !unhash_hash_bexp. reflexivity.
      + move=> e1 e2. rewrite !unhash_hash_bexp. reflexivity.
  Qed.

  Lemma hash_unhash_hashed_exp e :
    well_formed_hashed_exp e ->
    make_hashed_exp (unhash_hashed_exp e) = e
  with hash_unhash_hashed_bexp e :
         well_formed_hashed_bexp e ->
         make_hashed_bexp (unhash_hashed_bexp e) = e
  with hash_unhash_hexp e :
         well_formed_hexp e ->
         hash_exp (unhash_hexp e) = e
  with hash_unhash_hbexp e :
         well_formed_hbexp e ->
         hash_bexp (unhash_hbexp e) = e.
  Proof.
    (* hash_unhash_hashed_exp *)
    - case: e => //=.
      + move=> op e. rewrite /make_hashed_exp /= => Hwf.
        rewrite (hash_unhash_hexp e Hwf). reflexivity.
      + move=> op e1 e2. rewrite /make_hashed_exp /= => /andP [Hwf1 Hwf2].
        rewrite (hash_unhash_hexp e1 Hwf1) (hash_unhash_hexp e2 Hwf2). reflexivity.
      + move=> b e1 e2. rewrite /make_hashed_exp /= => /andP [/andP [Hwfb Hwf1] Hwf2].
        rewrite (hash_unhash_hbexp b Hwfb)
                (hash_unhash_hexp e1 Hwf1) (hash_unhash_hexp e2 Hwf2).
        reflexivity.
    (* hash_unhash_hashed_bexp *)
    - case: e => //=.
      + move=> op e1 e2. rewrite /make_hashed_bexp /= => /andP [Hwf1 Hwf2].
        rewrite (hash_unhash_hexp e1 Hwf1) (hash_unhash_hexp e2 Hwf2). reflexivity.
      + move=> e. rewrite /make_hashed_bexp /= => Hwf.
        rewrite (hash_unhash_hbexp e Hwf). reflexivity.
      + move=> e1 e2. rewrite /make_hashed_bexp /= => /andP [Hwf1 Hwf2].
        rewrite (hash_unhash_hbexp e1 Hwf1) (hash_unhash_hbexp e2 Hwf2). reflexivity.
      + move=> e1 e2. rewrite /make_hashed_bexp /= => /andP [Hwf1 Hwf2].
        rewrite (hash_unhash_hbexp e1 Hwf1) (hash_unhash_hbexp e2 Hwf2). reflexivity.
    (* hash_unhash_hexp *)
    - case: e => e h /=. move=> /andP [/eqP ->] Hwf.
      rewrite -ehval_hash_exp. rewrite /ehval.
      rewrite /unhash_hexp -/unhash_hashed_exp.
      move: (hash_unhash_hashed_exp e Hwf). rewrite /make_hashed_exp /ehobj.
      case: (hash_exp (unhash_hashed_exp e)). move=> ? ? ->. reflexivity.
    (* hash_unhash_hbexp *)
    - case: e => e h /=. move=> /andP [/eqP ->] Hwf.
      rewrite -bhval_hash_bexp. rewrite /bhval.
      rewrite /unhash_hbexp -/unhash_hashed_bexp.
      move: (hash_unhash_hashed_bexp e Hwf). rewrite /make_hashed_bexp /bhobj.
      case: (hash_bexp (unhash_hashed_bexp e)). move=> ? ? ->. reflexivity.
  Qed.

  Lemma make_hashed_exp_well_formed e : well_formed_hashed_exp (make_hashed_exp e)
  with make_hashed_bexp_well_formed e : well_formed_hashed_bexp (make_hashed_bexp e)
  with hash_exp_well_formed e : well_formed_hexp (hash_exp e)
  with hash_bexp_well_formed e : well_formed_hbexp (hash_bexp e).
  Proof.
    (* make_hashed_exp_well_formed *)
    - case: e => //=.
      + move=> _ e1 e2. rewrite !hash_exp_well_formed. reflexivity.
      + move=> b e1 e2. rewrite hash_bexp_well_formed !hash_exp_well_formed.
        reflexivity.
    (* make_hashed_bexp_well_formed *)
    - case: e => //=.
      + move=> _ e1 e2. rewrite !hash_exp_well_formed. reflexivity.
      + move=> e1 e2. rewrite !hash_bexp_well_formed. reflexivity.
      + move=> e1 e2. rewrite !hash_bexp_well_formed. reflexivity.
    (* hash_exp_well_formed *)
    - case: e => //=.
      + move=> op e. rewrite unhash_hash_exp.
        rewrite ehval_hash_exp eqxx hash_exp_well_formed.
        reflexivity.
      + move=> op e1 e2. rewrite !unhash_hash_exp.
        rewrite !ehval_hash_exp !eqxx !hash_exp_well_formed. reflexivity.
      + move=> b e1 e2. rewrite unhash_hash_bexp !unhash_hash_exp.
        rewrite bhval_hash_bexp !ehval_hash_exp !eqxx.
        rewrite hash_bexp_well_formed !hash_exp_well_formed. reflexivity.
    (* hash_bexp_well_formed *)
    - case: e => //=.
      + move=> op e1 e2. rewrite !unhash_hash_exp.
        rewrite !ehval_hash_exp eqxx !hash_exp_well_formed. reflexivity.
      + move=> b. rewrite unhash_hash_bexp.
        rewrite bhval_hash_bexp eqxx hash_bexp_well_formed. reflexivity.
      + move=> e1 e2. rewrite !unhash_hash_bexp.
        rewrite !bhval_hash_bexp eqxx !hash_bexp_well_formed. reflexivity.
      + move=> e1 e2. rewrite !unhash_hash_bexp.
        rewrite !bhval_hash_bexp eqxx !hash_bexp_well_formed. reflexivity.
  Qed.


  Structure hexp_of : Type := HExp { heval :> hexp;
                                     _ : well_formed_hexp heval }.
  Structure hbexp_of : Type := HBexp { hbval :> hbexp;
                                       _ : well_formed_hbexp hbval }.
  Canonical hexp_subType := Eval hnf in [subType for heval].
  Canonical hbexp_subType := Eval hnf in [subType for hbval].

End HashFunc.


Notation wf_hexp := hexp_of.
Notation wf_hbexp := hbexp_of.


Section HashEqn.

  Import QFBV.

  Fixpoint hashed_exp_eqn (e1 e2 : hashed_exp) : bool :=
    match e1, e2 with
    | HEvar v1, HEvar v2 => v1 == v2
    | HEconst n1, HEconst n2 => n1 == n2
    | HEunop op1 e1, HEunop op2 e2 => (op1 == op2) && hexp_eqn e1 e2
    | HEbinop op1 e11 e12, HEbinop op2 e21 e22 =>
      (op1 == op2) && hexp_eqn e11 e21 && hexp_eqn e12 e22
    | HEite b1 e11 e12, HEite b2 e21 e22 =>
      hbexp_eqn b1 b2 && hexp_eqn e11 e21 && hexp_eqn e12 e22
    | _, _ => false
    end
  with
  hashed_bexp_eqn (e1 e2 : hashed_bexp) : bool :=
    match e1, e2 with
    | HBfalse, HBfalse => true
    | HBtrue, HBtrue => true
    | HBbinop op1 e11 e12, HBbinop op2 e21 e22 =>
      (op1 == op2) && hexp_eqn e11 e21 && hexp_eqn e12 e22
    | HBlneg e1, HBlneg e2 => hbexp_eqn e1 e2
    | HBconj e11 e12, HBconj e21 e22 => hbexp_eqn e11 e21 && hbexp_eqn e12 e22
    | HBdisj e11 e12, HBdisj e21 e22 => hbexp_eqn e11 e21 && hbexp_eqn e12 e22
    | _, _ => false
    end
  with
  hexp_eqn (e1 e2 : hexp): bool :=
    match e1, e2 with
    | epair f1 h1, epair f2 h2 =>
      if h1 != h2 then false
      else hashed_exp_eqn f1 f2
    end
  with
  hbexp_eqn (e1 e2 : hbexp) : bool :=
    match e1, e2 with
    | bpair e1 h1, bpair e2 h2 =>
      if h1 != h2 then false
      else hashed_bexp_eqn e1 e2
    end.

  Lemma hashed_exp_eqn_eq x y : hashed_exp_eqn x y -> x = y
  with hashed_bexp_eqn_eq x y : hashed_bexp_eqn x y -> x = y
  with hexp_eqn_eq x y : hexp_eqn x y -> x = y
  with hbexp_eqn_eq x y : hbexp_eqn x y -> x = y.
  Proof.
    (* hashed_exp_eqn_eq *)
    - elim: x y => //=.
      + move=> x [] => //=. move=> y. by move=> /eqP ->.
      + move=> x [] => //=. move=> y. by move=> /eqP ->.
      + move=> op1 x [] => //=. move=> op2 y. move=> /andP [/eqP -> Heq].
        rewrite (hexp_eqn_eq _ _ Heq). reflexivity.
      + move=> op1 x1 x2 [] => //=. move=> op2 y1 y2.
        move=> /andP [/andP [/eqP -> Heq1] Heq2].
        rewrite (hexp_eqn_eq _ _ Heq1) (hexp_eqn_eq _ _ Heq2). reflexivity.
      + move=> b1 x1 x2 [] => //=. move=> b2 y1 y2.
        move=> /andP [/andP [Heqb Heq1] Heq2].
        rewrite (hbexp_eqn_eq _ _ Heqb) (hexp_eqn_eq _ _ Heq1) (hexp_eqn_eq _ _ Heq2).
        reflexivity.
    (* hashed_bexp_eqn_eq *)
    - elim: x y => //=.
      + by case=> //=.
      + by case=> //=.
      + move=> op1 x1 x2 [] => //=. move=> op2 y1 y2.
        move=> /andP [/andP [/eqP -> Heq1] Heq2].
        rewrite (hexp_eqn_eq _ _ Heq1) (hexp_eqn_eq _ _ Heq2). reflexivity.
      + move=> x [] => //=. move=> y. move=> Heq.
        rewrite (hbexp_eqn_eq _ _ Heq). reflexivity.
      + move=> x1 x2 [] => //=. move=> y1 y2. move=> /andP [Heq1 Heq2].
        rewrite (hbexp_eqn_eq _ _ Heq1) (hbexp_eqn_eq _ _ Heq2). reflexivity.
      + move=> x1 x2 [] => //=. move=> y1 y2. move=> /andP [Heq1 Heq2].
        rewrite (hbexp_eqn_eq _ _ Heq1) (hbexp_eqn_eq _ _ Heq2). reflexivity.
    (* hexp_eqn_eq *)
    - case: x; case: y. move=> x hx y hy /=. case Hh: (hy == hx) => //=.
      rewrite (eqP Hh). move=> Heq. rewrite (hashed_exp_eqn_eq _ _ Heq). reflexivity.
    (* hbexp_eqn_eq *)
    - case: x; case: y. move=> x hx y hy /=. case Hh: (hy == hx) => //=.
      rewrite (eqP Hh). move=> Heq. rewrite (hashed_bexp_eqn_eq _ _ Heq). reflexivity.
  Qed.

  Lemma hashed_exp_eqn_refl x : hashed_exp_eqn x x
  with hashed_bexp_eqn_refl x : hashed_bexp_eqn x x
  with hexp_eqn_refl x : hexp_eqn x x
  with hbexp_eqn_refl x : hbexp_eqn x x.
  Proof.
    (* hashed_exp_eqn_refl *)
    - case: x => //=.
      + move=> op e. rewrite eqxx andTb. exact: hexp_eqn_refl.
      + move=> op e1 e2. rewrite eqxx !hexp_eqn_refl. reflexivity.
      + move=> b e1 e2. rewrite hbexp_eqn_refl !hexp_eqn_refl. reflexivity.
    - case: x => //=.
      + move=> op e1 e2. rewrite eqxx !hexp_eqn_refl. reflexivity.
      + move=> e1 e2. rewrite !hbexp_eqn_refl. reflexivity.
      + move=> e1 e2. rewrite !hbexp_eqn_refl. reflexivity.
    - case: x => //=.
      + move=> e h. rewrite eqxx /=. exact: hashed_exp_eqn_refl.
    - case: x => //=.
      + move=> e h. rewrite eqxx /=. exact: hashed_bexp_eqn_refl.
  Qed.

  Lemma hashed_exp_eqn_sym x y : hashed_exp_eqn x y -> hashed_exp_eqn y x.
  Proof.
    move=> H. rewrite (hashed_exp_eqn_eq H). exact: hashed_exp_eqn_refl.
  Qed.

  Lemma hashed_bexp_eqn_sym x y : hashed_bexp_eqn x y -> hashed_bexp_eqn y x.
  Proof.
    move=> H. rewrite (hashed_bexp_eqn_eq H). exact: hashed_bexp_eqn_refl.
  Qed.

  Lemma hexp_eqn_sym x y : hexp_eqn x y -> hexp_eqn y x.
  Proof.
    move=> H. rewrite (hexp_eqn_eq H). exact: hexp_eqn_refl.
  Qed.

  Lemma hbexp_eqn_sym x y : hbexp_eqn x y -> hbexp_eqn y x.
  Proof.
    move=> H. rewrite (hbexp_eqn_eq H). exact: hbexp_eqn_refl.
  Qed.

  Lemma hashed_exp_eqn_trans (x y z : hashed_exp) :
    hashed_exp_eqn x y -> hashed_exp_eqn y z -> hashed_exp_eqn x z.
  Proof.
    move=> Hx Hy. rewrite (hashed_exp_eqn_eq Hx) (hashed_exp_eqn_eq Hy).
    exact: hashed_exp_eqn_refl.
  Qed.

  Lemma hashed_bexp_eqn_trans (x y z : hashed_bexp) :
    hashed_bexp_eqn x y -> hashed_bexp_eqn y z -> hashed_bexp_eqn x z.
  Proof.
    move=> Hx Hy. rewrite (hashed_bexp_eqn_eq Hx) (hashed_bexp_eqn_eq Hy).
    exact: hashed_bexp_eqn_refl.
  Qed.

  Lemma hexp_eqn_trans (x y z : hexp) :
    hexp_eqn x y -> hexp_eqn y z -> hexp_eqn x z.
  Proof.
    move=> Hx Hy. rewrite (hexp_eqn_eq Hx) (hexp_eqn_eq Hy).
    exact: hexp_eqn_refl.
  Qed.

  Lemma hbexp_eqn_trans (x y z : hbexp) :
    hbexp_eqn x y -> hbexp_eqn y z -> hbexp_eqn x z.
  Proof.
    move=> Hx Hy. rewrite (hbexp_eqn_eq Hx) (hbexp_eqn_eq Hy).
    exact: hbexp_eqn_refl.
  Qed.

  Lemma hashed_exp_eqP x y : reflect (x = y) (hashed_exp_eqn x y).
  Proof.
    case H: (hashed_exp_eqn x y).
    - apply: ReflectT. exact: (hashed_exp_eqn_eq H).
    - apply: ReflectF. move=> Hxy. move/negP: H; apply. rewrite Hxy.
      exact: hashed_exp_eqn_refl.
  Qed.

  Lemma hashed_bexp_eqP x y : reflect (x = y) (hashed_bexp_eqn x y).
  Proof.
    case H: (hashed_bexp_eqn x y).
    - apply: ReflectT. exact: (hashed_bexp_eqn_eq H).
    - apply: ReflectF. move=> Hxy. move/negP: H; apply. rewrite Hxy.
      exact: hashed_bexp_eqn_refl.
  Qed.

  Lemma hexp_eqP x y : reflect (x = y) (hexp_eqn x y).
  Proof.
    case H: (hexp_eqn x y).
    - apply: ReflectT. exact: (hexp_eqn_eq H).
    - apply: ReflectF. move=> Hxy. move/negP: H; apply. rewrite Hxy.
      exact: hexp_eqn_refl.
  Qed.

  Lemma hbexp_eqP x y : reflect (x = y) (hbexp_eqn x y).
  Proof.
    case H: (hbexp_eqn x y).
    - apply: ReflectT. exact: (hbexp_eqn_eq H).
    - apply: ReflectF. move=> Hxy. move/negP: H; apply. rewrite Hxy.
      exact: hbexp_eqn_refl.
  Qed.

  Definition hashed_exp_eqMixin := EqMixin hashed_exp_eqP.
  Canonical hashed_exp_eqType := Eval hnf in EqType hashed_exp hashed_exp_eqMixin.

  Definition hashed_bexp_eqMixin := EqMixin hashed_bexp_eqP.
  Canonical hashed_bexp_eqType := Eval hnf in EqType hashed_bexp hashed_bexp_eqMixin.

  Definition hexp_eqMixin := EqMixin hexp_eqP.
  Canonical hexp_eqType := Eval hnf in EqType hexp hexp_eqMixin.

  Definition hbexp_eqMixin := EqMixin hbexp_eqP.
  Canonical hbexp_eqType := Eval hnf in EqType hbexp hbexp_eqMixin.


  Lemma make_hashed_exp_inj (e1 e2 : exp) :
    make_hashed_exp e1 = make_hashed_exp e2 -> e1 = e2.
  Proof.
    move=> H. have: (unhash_hashed_exp (make_hashed_exp e1) =
                     unhash_hashed_exp (make_hashed_exp e2)) by rewrite H.
    rewrite !unhash_make_hashed_exp. by apply.
  Qed.

  Lemma make_hashed_bexp_inj (e1 e2 : bexp) :
    make_hashed_bexp e1 = make_hashed_bexp e2 -> e1 = e2.
  Proof.
    move=> H. have: (unhash_hashed_bexp (make_hashed_bexp e1) =
                     unhash_hashed_bexp (make_hashed_bexp e2)) by rewrite H.
    rewrite !unhash_make_hashed_bexp. by apply.
  Qed.

  Lemma hash_exp_inj (e1 e2 : exp) : hash_exp e1 = hash_exp e2 -> e1 = e2.
  Proof.
    move=> H. have: (unhash_hexp (hash_exp e1) =
                     unhash_hexp (hash_exp e2)) by rewrite H.
    rewrite !unhash_hash_exp. by apply.
  Qed.

  Lemma hash_bexp_inj (e1 e2 : bexp) : hash_bexp e1 = hash_bexp e2 -> e1 = e2.
  Proof.
    move=> H. have: (unhash_hbexp (hash_bexp e1) =
                     unhash_hbexp (hash_bexp e2)) by rewrite H.
    rewrite !unhash_hash_bexp. by apply.
  Qed.

  Lemma unhash_hashed_exp_inj e1 e2 :
    well_formed_hashed_exp e1 -> well_formed_hashed_exp e2 ->
    unhash_hashed_exp e1 = unhash_hashed_exp e2 -> e1 = e2.
  Proof.
    move=> Hwf1 Hwf2 H. have: (make_hashed_exp e1 = make_hashed_exp e2) by rewrite H.
    rewrite (hash_unhash_hashed_exp Hwf1) (hash_unhash_hashed_exp Hwf2).
    by apply.
  Qed.

  Lemma unhash_hashed_bexp_inj e1 e2 :
    well_formed_hashed_bexp e1 -> well_formed_hashed_bexp e2 ->
    unhash_hashed_bexp e1 = unhash_hashed_bexp e2 -> e1 = e2.
  Proof.
    move=> Hwf1 Hwf2 H. have: (make_hashed_bexp e1 = make_hashed_bexp e2) by rewrite H.
    rewrite (hash_unhash_hashed_bexp Hwf1) (hash_unhash_hashed_bexp Hwf2).
    by apply.
  Qed.

  Lemma unhash_hexp_inj e1 e2 :
    well_formed_hexp e1 -> well_formed_hexp e2 ->
    unhash_hexp e1 = unhash_hexp e2 -> e1 = e2.
  Proof.
    move=> Hwf1 Hwf2 H. have: (hash_exp e1 = hash_exp e2) by rewrite H.
    rewrite (hash_unhash_hexp Hwf1) (hash_unhash_hexp Hwf2).
    by apply.
  Qed.

  Lemma unhash_hbexp_inj e1 e2 :
    well_formed_hbexp e1 -> well_formed_hbexp e2 ->
    unhash_hbexp e1 = unhash_hbexp e2 -> e1 = e2.
  Proof.
    move=> Hwf1 Hwf2 H. have: (hash_bexp e1 = hash_bexp e2) by rewrite H.
    rewrite (hash_unhash_hbexp Hwf1) (hash_unhash_hbexp Hwf2).
    by apply.
  Qed.

End HashEqn.


Section HashLtn.

  Import QFBV.

  Definition id_hashed_exp (e : hashed_exp) : nat :=
    match e with
    | HEvar _ => 0
    | HEconst _ => 1
    | HEunop _ _ => 2
    | HEbinop _ _ _ => 3
    | HEite _ _ _ => 4
    end.

  Definition id_hashed_bexp (e : hashed_bexp) : nat :=
    match e with
    | HBfalse => 0
    | HBtrue => 1
    | HBbinop _ _ _ => 2
    | HBlneg _ => 3
    | HBconj _ _ => 4
    | HBdisj _ _ => 5
    end.

  Fixpoint hashed_exp_ltn (e1 e2 : hashed_exp) {struct e1} : bool :=
    match e1, e2 with
    | HEvar v1, HEvar v2 => SSAVarOrder.ltn v1 v2
    | HEconst n1, HEconst n2 =>
      (size n1 < size n2)
      || ((size n1 == size n2) && (n1 <# n2)%bits)
    | HEunop o1 f1, HEunop o2 f2 =>
      (eunop_ltn o1 o2)
      || ((o1 == o2) && (hexp_ltn f1 f2))
    | HEbinop o1 f1 f2, HEbinop o2 f3 f4 =>
      (ebinop_ltn o1 o2)
      || ((o1 == o2) && (hexp_ltn f1 f3))
      || ((o1 == o2) && (f1 == f3) && (hexp_ltn f2 f4))
    | HEite c1 f1 f2, HEite c2 f3 f4 =>
      (hbexp_ltn c1 c2)
      || ((c1 == c2) && (hexp_ltn f1 f3))
      || ((c1 == c2) && (f1 == f3) && (hexp_ltn f2 f4))
    | _, _ => id_hashed_exp e1 < id_hashed_exp e2
    end
  with
  hashed_bexp_ltn (e1 e2 : hashed_bexp) {struct e1} : bool :=
    match e1, e2 with
    | HBbinop o1 f1 f2, HBbinop o2 f3 f4 =>
      bbinop_ltn o1 o2
      || ((o1 == o2) && (hexp_ltn f1 f3))
      || ((o1 == o2) && (f1 == f3) && (hexp_ltn f2 f4))
    | HBlneg f1, HBlneg f2 => hbexp_ltn f1 f2
    | HBconj f1 f2, HBconj f3 f4 =>
      (hbexp_ltn f1 f3)
      || ((f1 == f3) && (hbexp_ltn f2 f4))
    | HBdisj f1 f2, HBdisj f3 f4 =>
      (hbexp_ltn f1 f3)
      || ((f1 == f3) && (hbexp_ltn f2 f4))
    | _, _ => id_hashed_bexp e1 < id_hashed_bexp e2
    end
  with
  hexp_ltn (e1 e2 : hexp) {struct e1} : bool :=
    match e1, e2 with
    | epair f1 h1, epair f2 h2 =>
      (h1 <? h2)%Z
      || ((h1 == h2)%Z && hashed_exp_ltn f1 f2)
    end
  with
  hbexp_ltn (e1 e2 : hbexp) {struct e1} : bool :=
    match e1, e2 with
    | bpair f1 h1, bpair f2 h2 =>
      (h1 <? h2)%Z
      || ((h1 == h2)%Z && hashed_bexp_ltn f1 f2)
    end.

  Lemma hashed_exp_ltnn e : hashed_exp_ltn e e = false
  with hashed_bexp_ltnn e : hashed_bexp_ltn e e = false
  with hexp_ltnn e : hexp_ltn e e = false
  with hbexp_ltnn e : hbexp_ltn e e = false.
  Proof.
    (* hashed_exp_ltnn *)
    - case: e => //=.
      + move=> v. exact: SSAVarOrder.ltnn.
      + move=> bs. rewrite eqxx ltnn ltBnn. reflexivity.
      + move=> op e. rewrite eqxx eunop_ltnn (hexp_ltnn e). reflexivity.
      + move=> op e1 e2. rewrite !eqxx ebinop_ltnn (hexp_ltnn e1) (hexp_ltnn e2).
        reflexivity.
      + move=> b e1 e2. rewrite !eqxx (hbexp_ltnn b) (hexp_ltnn e1) (hexp_ltnn e2).
        reflexivity.
    (* hashed_bexp_ltnn *)
    - case: e => //=.
      + move=> op e1 e2. rewrite !eqxx bbinop_ltnn hexp_ltnn hexp_ltnn.
        reflexivity.
      + move=> e1 e2. rewrite eqxx hbexp_ltnn hbexp_ltnn. reflexivity.
      + move=> e1 e2. rewrite eqxx hbexp_ltnn hbexp_ltnn. reflexivity.
    (* hexp_ltnn *)
    - case: e => h e /=. rewrite Z.ltb_irrefl eqxx hashed_exp_ltnn. reflexivity.
    (* hbexp_ltnn *)
    - case: e => h e /=. rewrite Z.ltb_irrefl eqxx hashed_bexp_ltnn. reflexivity.
  Qed.

  Lemma hashed_exp_ltn_eqF e1 e2 : hashed_exp_ltn e1 e2 -> e1 == e2 = false.
  Proof.
    move=> Hlt; apply/eqP => Heq. rewrite Heq hashed_exp_ltnn in Hlt. discriminate.
  Qed.

  Lemma hashed_bexp_ltn_eqF e1 e2 : hashed_bexp_ltn e1 e2 -> e1 == e2 = false.
  Proof.
    move=> Hlt; apply/eqP => Heq. rewrite Heq hashed_bexp_ltnn in Hlt. discriminate.
  Qed.

  Lemma hexp_ltn_eqF e1 e2 : hexp_ltn e1 e2 -> e1 == e2 = false.
  Proof.
    move=> Hlt; apply/eqP => Heq. rewrite Heq hexp_ltnn in Hlt. discriminate.
  Qed.

  Lemma hbexp_ltn_eqF e1 e2 : hbexp_ltn e1 e2 -> e1 == e2 = false.
  Proof.
    move=> Hlt; apply/eqP => Heq. rewrite Heq hbexp_ltnn in Hlt. discriminate.
  Qed.

  Ltac t_auto_hook ::=
    match goal with
    | H1 : (is_true (?e1 < ?e2)),
      H2 : (is_true (?e2 < ?e3)) |- context [?e1 < ?e3] =>
      rewrite (ltn_trans H1 H2); clear H1 H2
    | H1 : (is_true (?e1 <? ?e2)%Z),
      H2 : (is_true (?e2 <? ?e3)%Z) |- context [(?e1 <? ?e3)%Z] =>
      rewrite (Z_ltb_trans H1 H2); clear H1 H2
    | H1 : (is_true (SSAVarOrder.ltn ?e1 ?e2)),
      H2 : (is_true (SSAVarOrder.ltn ?e2 ?e3)) |-
      context [(SSAVarOrder.ltn ?e1 ?e3)] =>
      rewrite (SSAVarOrder.ltn_trans H1 H2); clear H1 H2
    | H1 : (is_true (?e1 <# ?e2)%bits),
      H2 : (is_true (?e2 <# ?e3)%bits) |-
      context [(?e1 <# ?e3)%bits] =>
      rewrite (ltB_trans H1 H2); clear H1 H2
    | H1 : (is_true (eunop_ltn ?e1 ?e2)),
      H2 : (is_true (eunop_ltn ?e2 ?e3)) |-
      context [eunop_ltn ?e1 ?e3] =>
      rewrite (eunop_ltn_trans H1 H2); clear H1 H2
    | H1 : (is_true (ebinop_ltn ?e1 ?e2)),
      H2 : (is_true (ebinop_ltn ?e2 ?e3)) |-
      context [ebinop_ltn ?e1 ?e3] =>
      rewrite (ebinop_ltn_trans H1 H2); clear H1 H2
    | H1 : (is_true (bbinop_ltn ?e1 ?e2)),
      H2 : (is_true (bbinop_ltn ?e2 ?e3)) |-
      context [bbinop_ltn ?e1 ?e3] =>
      rewrite (bbinop_ltn_trans H1 H2); clear H1 H2
    | hexp_ltn_trans :
        (forall e1 e2 e3 : hexp,
            is_true (hexp_ltn e1 e2) -> is_true (hexp_ltn e2 e3) ->
            is_true (hexp_ltn e1 e3)),
        H1 : is_true (hexp_ltn ?e1 ?e2),
        H2 : is_true (hexp_ltn ?e2 ?e3) |-
      context [hexp_ltn ?e1 ?e3] =>
      rewrite (hexp_ltn_trans _ _ _ H1 H2); clear H1 H2
    | hbexp_ltn_trans :
        (forall e1 e2 e3 : hbexp,
            is_true (hbexp_ltn e1 e2) -> is_true (hbexp_ltn e2 e3) ->
            is_true (hbexp_ltn e1 e3)),
        H1 : is_true (hbexp_ltn ?e1 ?e2),
        H2 : is_true (hbexp_ltn ?e2 ?e3) |-
      context [hbexp_ltn ?e1 ?e3] =>
      rewrite (hbexp_ltn_trans _ _ _ H1 H2); clear H1 H2
    | hashed_exp_ltn_trans :
        (forall e1 e2 e3 : hashed_exp,
            is_true (hashed_exp_ltn e1 e2) -> is_true (hashed_exp_ltn e2 e3) ->
            is_true (hashed_exp_ltn e1 e3)),
        H1 : is_true (hashed_exp_ltn ?e1 ?e2),
        H2 : is_true (hashed_exp_ltn ?e2 ?e3) |-
      context [hashed_exp_ltn ?e1 ?e3] =>
      rewrite (hashed_exp_ltn_trans _ _ _ H1 H2); clear H1 H2
    | hashed_bexp_ltn_trans :
        (forall e1 e2 e3 : hashed_bexp,
            is_true (hashed_bexp_ltn e1 e2) -> is_true (hashed_bexp_ltn e2 e3) ->
            is_true (hashed_bexp_ltn e1 e3)),
        H1 : is_true (hashed_bexp_ltn ?e1 ?e2),
        H2 : is_true (hashed_bexp_ltn ?e2 ?e3) |-
      context [hashed_bexp_ltn ?e1 ?e3] =>
      rewrite (hashed_bexp_ltn_trans _ _ _ H1 H2); clear H1 H2
    end.

  Lemma hashed_exp_ltn_trans e1 e2 e3 :
    hashed_exp_ltn e1 e2 -> hashed_exp_ltn e2 e3 -> hashed_exp_ltn e1 e3
  with
  hashed_bexp_ltn_trans e1 e2 e3 :
    hashed_bexp_ltn e1 e2 -> hashed_bexp_ltn e2 e3 -> hashed_bexp_ltn e1 e3
  with
  hexp_ltn_trans e1 e2 e3 :
    hexp_ltn e1 e2 -> hexp_ltn e2 e3 -> hexp_ltn e1 e3
  with
  hbexp_ltn_trans e1 e2 e3 :
    hbexp_ltn e1 e2 -> hbexp_ltn e2 e3 -> hbexp_ltn e1 e3.
  Proof.
    (* hashed_exp_ltn_trans *)
    - case: e1.
      + move=> v1; case: e2; case: e3; try done. move=> /= *; by t_auto.
      + move=> b1; case: e2; case: e3; try done. move=> /= *; by t_auto.
      + move=> op1 ne1; case: e2; case: e3; try done. move=> /= *; by t_auto.
      + move=> op1 ne1 ne2; case: e2; case: e3; try done. move=> /= *; by t_auto.
      + move=> c1 ne1 ne2. case: e2; case: e3; try done. move=> /=*; by t_auto.
    (* hashed_bexp_ltn_trans *)
    - case: e1.
      + case: e2; case: e3; try done.
      + case: e2; case: e3; try done.
      + move=> op1 ne1 ne2; case: e2; case: e3; try done. move=> /= *; by t_auto.
      + move=> ne1. case: e2; case: e3; try done. move=> /= *; by t_auto.
      + move=> ne1 ne2. case: e2; case: e3; try done. move=> /= *; by t_auto.
      + move=> ne1 ne2. case: e2; case: e3; try done. move=> /= *; by t_auto.
    (* hexp_ltn_trans *)
    - case: e1 => h1 e1; case: e2 => h2 e2; case: e3 => h3 e3 /=. by t_auto.
    (* hbexp_ltn_trans *)
    - case: e1 => h1 e1; case: e2 => h2 e2; case: e3 => h3 e3 /=. by t_auto.
  Qed.

  Lemma hashed_exp_ltn_antisym e1 e2 :
    hashed_exp_ltn e1 e2 -> ~~ hashed_exp_ltn e2 e1.
  Proof.
    move=> H1. apply/negP=> H2. move: (hashed_exp_ltn_trans H1 H2).
    rewrite hashed_exp_ltnn. discriminate.
  Qed.

  Lemma hashed_bexp_ltn_antisym e1 e2 :
    hashed_bexp_ltn e1 e2 -> ~~ hashed_bexp_ltn e2 e1.
  Proof.
    move=> H1. apply/negP=> H2. move: (hashed_bexp_ltn_trans H1 H2).
    rewrite hashed_bexp_ltnn. discriminate.
  Qed.

  Lemma hexp_ltn_antisym e1 e2 :
    hexp_ltn e1 e2 -> ~~ hexp_ltn e2 e1.
  Proof.
    move=> H1. apply/negP=> H2. move: (hexp_ltn_trans H1 H2).
    rewrite hexp_ltnn. discriminate.
  Qed.

  Lemma hbexp_ltn_antisym e1 e2 :
    hbexp_ltn e1 e2 -> ~~ hbexp_ltn e2 e1.
  Proof.
    move=> H1. apply/negP=> H2. move: (hbexp_ltn_trans H1 H2).
    rewrite hbexp_ltnn. discriminate.
  Qed.

  Lemma hashed_exp_eqn_ltn_gtn e1 e2 :
    (e1 == e2) || (hashed_exp_ltn e1 e2) || (hashed_exp_ltn e2 e1)
  with
  hashed_bexp_eqn_ltn_gtn e1 e2 :
    (e1 == e2) || (hashed_bexp_ltn e1 e2) || (hashed_bexp_ltn e2 e1)
  with
  hexp_eqn_ltn_gtn e1 e2 :
    (e1 == e2) || (hexp_ltn e1 e2) || (hexp_ltn e2 e1)
  with
  hbexp_eqn_ltn_gtn e1 e2 :
    (e1 == e2) || (hbexp_ltn e1 e2) || (hbexp_ltn e2 e1).
  Proof.
    (* hashed_exp_eqn_ltn_gtn *)
    - case: e1.
      + move=> v1; case: e2 => /=; try eauto. move=> v2.
        case: (SSAVarOrder.compare v1 v2);
          rewrite /SSAVarOrder.lt /SSAVarOrder.eq=> H; by t_auto.
      + move=> b1; case: e2 => /=; try eauto. move=> b2.
        move: (Nats.eqn_ltn_gtn_cases (size b1) (size b2)).
        case/orP; [case/orP; [| by t_auto] | by t_auto]. move/eqP => H.
        move: (eqB_ltB_gtB_cases_ss H). by t_auto.
      + move=> op1 ne1. case: e2 => /=; try eauto. move=> op2 ne2.
        move: (eunop_eqn_ltn_gtn op1 op2) (hexp_eqn_ltn_gtn ne1 ne2).
          by t_auto.
      + move=> op1 ne1 ne2. case: e2 => /=; try eauto. move=> op2 ne3 ne4.
        move: (ebinop_eqn_ltn_gtn op1 op2) (hexp_eqn_ltn_gtn ne1 ne3)
                                           (hexp_eqn_ltn_gtn ne2 ne4).
          by t_auto.
      + move=> b1 ne1 ne2. case: e2 => /=; try eauto. move=> b2 ne3 ne4.
        move: (hbexp_eqn_ltn_gtn b1 b2) (hexp_eqn_ltn_gtn ne1 ne3)
                                        (hexp_eqn_ltn_gtn ne2 ne4).
          by t_auto.
    (* hashed_bexp_eqn_ltn_gtn *)
    - case: e1.
      + case: e2 => /=; reflexivity.
      + case: e2 => /=; reflexivity.
      + move=> op1 ne1 ne2. case: e2 => /=; try eauto. move=> op2 ne3 ne4.
        move: (bbinop_eqn_ltn_gtn op1 op2) (hexp_eqn_ltn_gtn ne1 ne3)
                                           (hexp_eqn_ltn_gtn ne2 ne4).
          by t_auto.
      + move=> ne1. case: e2 => /=; try eauto. move=> ne2.
        move: (hbexp_eqn_ltn_gtn ne1 ne2).
          by t_auto.
      + move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
        move: (hbexp_eqn_ltn_gtn ne1 ne3) (hbexp_eqn_ltn_gtn ne2 ne4).
          by t_auto.
      + move=> ne1 ne2. case: e2 => /=; try eauto. move=> ne3 ne4.
        move: (hbexp_eqn_ltn_gtn ne1 ne3) (hbexp_eqn_ltn_gtn ne2 ne4).
          by t_auto.
    (* hexp_eqn_ltn_gtn *)
    - case: e1 => e1 h1; case: e2 => e2 h2 /=.
      move: (Z_eqn_ltn_gtn_cases h1 h2) (hashed_exp_eqn_ltn_gtn e1 e2).
         by t_auto.
    (* hbexp_eqn_ltn_gtn *)
    - case: e1 => e1 h1; case: e2 => e2 h2 /=.
      move: (Z_eqn_ltn_gtn_cases h1 h2) (hashed_bexp_eqn_ltn_gtn e1 e2).
        by t_auto.
  Qed.

  Definition hashed_exp_compare e1 e2 : Compare hashed_exp_ltn eq_op e1 e2.
  Proof.
    case Heq: (e1 == e2).
    - apply: EQ. assumption.
    - case Hlt: (hashed_exp_ltn e1 e2).
      + apply: LT. assumption.
      + move: (hashed_exp_eqn_ltn_gtn e1 e2). rewrite Heq Hlt /=. move=> Hgt.
        apply: GT. assumption.
  Defined.

  Definition hashed_bexp_compare e1 e2 : Compare hashed_bexp_ltn eq_op e1 e2.
  Proof.
    case Heq: (e1 == e2).
    - apply: EQ. assumption.
    - case Hlt: (hashed_bexp_ltn e1 e2).
      + apply: LT. assumption.
      + move: (hashed_bexp_eqn_ltn_gtn e1 e2). rewrite Heq Hlt /=. move=> Hgt.
        apply: GT. assumption.
  Defined.

  Definition hexp_compare e1 e2 : Compare hexp_ltn eq_op e1 e2.
  Proof.
    case Heq: (e1 == e2).
    - apply: EQ. assumption.
    - case Hlt: (hexp_ltn e1 e2).
      + apply: LT. assumption.
      + move: (hexp_eqn_ltn_gtn e1 e2). rewrite Heq Hlt /=. move=> Hgt.
        apply: GT. assumption.
  Defined.

  Definition hbexp_compare e1 e2 : Compare hbexp_ltn eq_op e1 e2.
  Proof.
    case Heq: (e1 == e2).
    - apply: EQ. assumption.
    - case Hlt: (hbexp_ltn e1 e2).
      + apply: LT. assumption.
      + move: (hbexp_eqn_ltn_gtn e1 e2). rewrite Heq Hlt /=. move=> Hgt.
        apply: GT. assumption.
  Defined.

End HashLtn.


Module HexpOrderMinimal <: SsrOrderMinimal.

  Definition t : eqType := hexp_eqType.
  Definition eqn (e1 e2 : t) : bool := e1 == e2.
  Definition ltn (e1 e2 : t) : bool := hexp_ltn e1 e2.
  Definition ltn_trans (x y z : t) : ltn x y -> ltn y z -> ltn x z :=
    @hexp_ltn_trans x y z.
  Lemma ltn_not_eqn x y : ltn x y -> x != y.
  Proof. move=> H. rewrite (hexp_ltn_eqF H). reflexivity. Qed.
  Definition compare (x y : t) : Compare ltn eqn x y := hexp_compare x y.

End HexpOrderMinimal.

Module HbexpOrderMinimal <: SsrOrderMinimal.

  Definition t : eqType := hbexp_eqType.
  Definition eqn (e1 e2 : t) : bool := e1 == e2.
  Definition ltn (e1 e2 : t) : bool := hbexp_ltn e1 e2.
  Definition ltn_trans (x y z : t) : ltn x y -> ltn y z -> ltn x z :=
    @hbexp_ltn_trans x y z.
  Lemma ltn_not_eqn x y : ltn x y -> x != y.
  Proof. move=> H. rewrite (hbexp_ltn_eqF H). reflexivity. Qed.
  Definition compare (x y : t) : Compare ltn eqn x y := hbexp_compare x y.

End HbexpOrderMinimal.

Module HexpOrder <: SsrOrder := MakeSsrOrder HexpOrderMinimal.
Module HbexpOrder <: SsrOrder := MakeSsrOrder HbexpOrderMinimal.

