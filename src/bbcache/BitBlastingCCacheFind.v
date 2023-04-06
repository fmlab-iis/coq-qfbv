From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types EqOrder EqVar Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport AdhereConform.
From BBCache Require Import CompCache BitBlastingCCacheDef.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Ltac auto_prove_neq_by_len :=
  match goal with
  | Hlen : is_true (QFBV.len_exp ?e1 < QFBV.len_exp ?e2)
    |- ~ is_true (?e2 == ?e1) =>
    let Heq := fresh in
    move/eqP=> Heq; rewrite Heq /= ltnn in Hlen; done
  | Hlen : is_true (QFBV.len_bexp ?e1 < QFBV.len_bexp ?e2)
    |- ~ is_true (?e2 == ?e1) =>
    let Heq := fresh in
    move/eqP=> Heq; rewrite Heq /= ltnn in Hlen; done
  end.

Ltac auto_prove_lt :=
  match goal with 
  | H : is_true (?a.+1 < ?p)
    |- is_true (?a < ?p) =>
    by apply: (ltn_trans (ltnSn a))
  | H : is_true ((?a + ?b).+1 < ?p)
    |- is_true (?a < ?p) =>
    let Haux := fresh in
    (have Haux : a < (a + b).+1 by apply leq_addr); exact: (ltn_trans Haux H)
  | H : is_true ((?b + ?a).+1 < ?p)
    |- is_true (?a < ?p) =>
    let Haux := fresh in
    (have Haux : a < (b + a).+1 by apply leq_addl); exact: (ltn_trans Haux H)
  | H : is_true ((?a + ?b + ?c).+1 < ?p)
    |- is_true (?a < ?p) =>
    let Haux := fresh in
    (have Haux : a < (a + b + c).+1 by rewrite -addnA; exact: leq_addr); 
    exact: (ltn_trans Haux H)
  | H : is_true ((?b + ?a + ?c).+1 < ?p)
    |- is_true (?a < ?p) =>
    let Haux := fresh in
    (have Haux : a < (b + a + c).+1 by rewrite (addnC b) -addnA; exact: leq_addr); 
    exact: (ltn_trans Haux H)
  | |- is_true (?a < ?a.+1) => exact: leqnn
  | |- is_true (?a < (?a + _).+1) => exact: leq_addr
  | |- is_true (?a < (_ + ?a).+1) => exact: leq_addl
  | |- is_true (?a < (?a + _ + _).+1) => rewrite -addnA; exact: leq_addr
  | |- is_true (?a < (?b + ?a + _).+1) => rewrite (addnC b) -addnA; exact: leq_addr
  end.

Ltac auto_prove_len_lt :=
  match goal with 
  | H : is_true (QFBV.len_exp ?e0 < QFBV.len_exp ?e)
    |- is_true (QFBV.len_exp ?e1 < QFBV.len_exp ?e) =>
    match e0 with
    | context [e1] =>
    rewrite /= in H; by auto_prove_lt
    end
  | H : is_true (QFBV.len_exp ?e0 < QFBV.len_exp ?e)
    |- is_true (QFBV.len_bexp ?e1 < QFBV.len_exp ?e) =>
    match e0 with
    | context [e1] =>
    rewrite /= in H; by auto_prove_lt
    end
  | H : is_true (QFBV.len_bexp ?e0 < QFBV.len_exp ?e)
    |- is_true (QFBV.len_exp ?e1 < QFBV.len_exp ?e) =>
    match e0 with
    | context [e1] =>
    rewrite /= in H; by auto_prove_lt
    end
  | H : is_true (QFBV.len_bexp ?e0 < QFBV.len_exp ?e)
    |- is_true (QFBV.len_bexp ?e1 < QFBV.len_exp ?e) =>
    match e0 with
    | context [e1] =>
    rewrite /= in H; by auto_prove_lt
    end
  | H : is_true (QFBV.len_exp ?e0 < QFBV.len_bexp ?e)
    |- is_true (QFBV.len_exp ?e1 < QFBV.len_bexp ?e) =>
    match e0 with
    | context [e1] =>
    rewrite /= in H; by auto_prove_lt
    end
  | H : is_true (QFBV.len_exp ?e0 < QFBV.len_bexp ?e)
    |- is_true (QFBV.len_bexp ?e1 < QFBV.len_bexp ?e) =>
    match e0 with
    | context [e1] =>
    rewrite /= in H; by auto_prove_lt
    end
  | H : is_true (QFBV.len_bexp ?e0 < QFBV.len_bexp ?e)
    |- is_true (QFBV.len_exp ?e1 < QFBV.len_bexp ?e) =>
    match e0 with
    | context [e1] =>
    rewrite /= in H; by auto_prove_lt
    end
  | H : is_true (QFBV.len_bexp ?e0 < QFBV.len_bexp ?e)
    |- is_true (QFBV.len_bexp ?e1 < QFBV.len_bexp ?e) =>
    match e0 with
    | context [e1] =>
    rewrite /= in H; by auto_prove_lt
    end
  | |- is_true (QFBV.len_exp ?e0 < QFBV.len_exp ?e) =>
    match e with
    | context [e0] =>
    rewrite /=; by auto_prove_lt
    end
  | |- is_true (QFBV.len_bexp ?e0 < QFBV.len_bexp ?e) =>
    match e with
    | context [e0] =>
    rewrite /=; by auto_prove_lt
    end
  | |- is_true (QFBV.len_bexp ?e0 < QFBV.len_exp ?e) =>
    match e with
    | context [e0] =>
    rewrite /=; by auto_prove_lt
    end
  | |- is_true (QFBV.len_exp ?e0 < QFBV.len_bexp ?e) =>
    match e with
    | context [e0] =>
    rewrite /=; by auto_prove_lt
    end
  end.


(* = bit_blast_exp_ccache_find_cet and bit_blast_bexp_ccache_find_cet = *)

Lemma bit_blast_exp_ccache_find_cet :
  forall e0 e te m c g m' c' g' cs ls,
    QFBV.len_exp e0 < QFBV.len_exp e ->
    bit_blast_exp_ccache te m c g e0 = (m', c', g', cs, ls) ->
    find_cet e c' = find_cet e c
  with
    bit_blast_bexp_ccache_find_cet :  
      forall e0 e te m c g m' c' g' cs l,
        QFBV.len_bexp e0 < QFBV.len_exp e ->
        bit_blast_bexp_ccache te m c g e0 = (m', c', g', cs, l) ->
        find_cet e c' = find_cet e c.
Proof.  
  (* bit_blast_exp_ccache_find_cet *)
  set IHe := bit_blast_exp_ccache_find_cet.
  set IHb := bit_blast_bexp_ccache_find_cet.
  move=> e0 e te m c g m' c' g' cs ls.
  case Hfcet: (find_cet e0 c) => [[cs0 ls0] | ]. 
  - move=> _. rewrite bit_blast_exp_ccache_equation Hfcet /=.
    case=> _ <- _ _ _. done. 
  - move: Hfcet. case e0 => [v | bs | op e1 | op e1 e2 | b e1 e2] Hfcet Hlen.
    + rewrite /= Hfcet. 
      case Hfhet : (find_het (QFBV.Evar v) c) => [[csh lsh] | ].
      * case=> _ <- _ _ _; apply find_cet_add_cet_neq;
        by auto_prove_neq_by_len.
      * case Hfind: (SSAVM.find v m) => [rs | ]; 
          last case Hblast : (bit_blast_var te g v) => [[vg vcs] vls];
          case=> _ <- _ _ _; rewrite find_cet_add_cet_neq; 
          (try by auto_prove_neq_by_len); by apply find_cet_add_het.
    + rewrite /= Hfcet.
      case Hfhet : (find_het (QFBV.Econst bs) c) => [[csh lsh] | ];
        case=> _ <- _ _ _; rewrite find_cet_add_cet_neq; (try done);
        (try by auto_prove_neq_by_len); by apply find_cet_add_het.
    + rewrite /= Hfcet.
      case Hbb1: (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
      have He1e : QFBV.len_exp e1 < QFBV.len_exp e by auto_prove_len_lt.
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ He1e Hbb1) => Hc1c.
      rewrite -Hc1c.
      case Hfhet : (find_het (QFBV.Eunop op e1) c1) => [[csop lsop] | ];
        last case Hbbop : (bit_blast_eunop op g1 ls1) => [[gop csop] lsop];
        case=> _ <- _ _ _; rewrite find_cet_add_cet_neq; (try done);
        (try by auto_prove_neq_by_len); by apply find_cet_add_het.
    + rewrite /= Hfcet.
      case Hbb1: (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
      have He1e : QFBV.len_exp e1 < QFBV.len_exp e by auto_prove_len_lt.
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ He1e Hbb1) => Hc1c.
      case Hbb2: (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
      have He2e : QFBV.len_exp e2 < QFBV.len_exp e by auto_prove_len_lt.
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ He2e Hbb2) => Hc2c1.
      rewrite -Hc1c -Hc2c1.
      case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csop lsop] | ];
        last case Hbbop : (bit_blast_ebinop op g2 ls1 ls2) => [[gop csop] lsop];
        case=> _ <- _ _ _; rewrite find_cet_add_cet_neq; (try done);
        (try by auto_prove_neq_by_len); by apply find_cet_add_het.
    + rewrite /= Hfcet.
      case Hbbb: (bit_blast_bexp_ccache te m c g b) => [[[[mb cb] gb] csb] lb].
      have Hbe : QFBV.len_bexp b < QFBV.len_exp e by auto_prove_len_lt.
      move: (IHb _ _ _ _ _ _ _ _ _ _ _ Hbe Hbbb) => Hcbc.
      case Hbb1: (bit_blast_exp_ccache te mb cb gb e1) => [[[[m1 c1] g1] cs1] ls1].
      have He1e : QFBV.len_exp e1 < QFBV.len_exp e by auto_prove_len_lt.
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ He1e Hbb1) => Hc1cb.
      case Hbb2: (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
      have He2e : QFBV.len_exp e2 < QFBV.len_exp e by auto_prove_len_lt.
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ He2e Hbb2) => Hc2c1.
      rewrite -Hcbc -Hc1cb -Hc2c1.
      case Hfhet : (find_het (QFBV.Eite b e1 e2) c2) => [[csop lsop] | ];
        last case Hbbop : (bit_blast_ite g2 lb ls1 ls2) => [[gop csop] lsop];
        case=> _ <- _ _ _; rewrite find_cet_add_cet_neq; (try done);
        (try by auto_prove_neq_by_len); by apply find_cet_add_het.
  (* bit_blast_bexp_ccache_find_cet *)
  set IHe := bit_blast_exp_ccache_find_cet.
  set IHb := bit_blast_bexp_ccache_find_cet.
  move=> e0 e te m c g m' c' g' cs l.
  case Hfcbt: (find_cbt e0 c) => [[cs0 l0] | ]. 
  - move=> _. rewrite bit_blast_bexp_ccache_equation Hfcbt /=.
    case=> _ <- _ _ _. done. 
  - move: Hfcbt. case e0 => [ | | op e1 e2 | e1 | e1 e2 | e1 e2] Hfcbt Hlen.
    + rewrite /= Hfcbt. 
      case Hfhet : (find_hbt QFBV.Bfalse c) => [[csh lh] | ]; case=> _ <- _ _ _; 
        rewrite find_cet_add_cbt; (try rewrite find_cet_add_hbt); done.
    + rewrite /= Hfcbt.
      case Hfhet : (find_hbt QFBV.Btrue c) => [[csh lh] | ]; case=> _ <- _ _ _; 
        rewrite find_cet_add_cbt; (try rewrite find_cet_add_hbt); done.
    + rewrite /= Hfcbt.
      case Hbb1: (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
      have He1e : QFBV.len_exp e1 < QFBV.len_exp e by auto_prove_len_lt.
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ He1e Hbb1) => Hc1c.
      case Hbb2: (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
      have He2e : QFBV.len_exp e2 < QFBV.len_exp e by auto_prove_len_lt.
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ He2e Hbb2) => Hc2c1.
      rewrite -Hc1c -Hc2c1.
      case Hfhbt : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[csop lop] | ];
        last case Hbbop : (bit_blast_bbinop op g2 ls1 ls2) => [[gop csop] lsop];
        case=> _ <- _ _ _; rewrite find_cet_add_cbt; 
        (try rewrite find_cet_add_hbt); done.
    + rewrite /= Hfcbt.
      case Hbb1: (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
      have He1e : QFBV.len_bexp e1 < QFBV.len_exp e by auto_prove_len_lt.
      move: (IHb _ _ _ _ _ _ _ _ _ _ _ He1e Hbb1) => Hc1c.
      rewrite -Hc1c.
      case Hfhbt : (find_hbt (QFBV.Blneg e1) c1) => [[csop lop] | ]; 
        case=> _ <- _ _ _; rewrite find_cet_add_cbt; 
        (try rewrite find_cet_add_hbt); done.
    + rewrite /= Hfcbt.
      case Hbb1: (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
      have He1e : QFBV.len_bexp e1 < QFBV.len_exp e by auto_prove_len_lt.
      move: (IHb _ _ _ _ _ _ _ _ _ _ _ He1e Hbb1) => Hc1c.
      case Hbb2: (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
      have He2e : QFBV.len_bexp e2 < QFBV.len_exp e by auto_prove_len_lt.
      move: (IHb _ _ _ _ _ _ _ _ _ _ _ He2e Hbb2) => Hc2c1.
      rewrite -Hc1c -Hc2c1.
      case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csop lop] | ]; 
        case=> _ <- _ _ _; rewrite find_cet_add_cbt; 
        (try rewrite find_cet_add_hbt); done.
    + rewrite /= Hfcbt.
      case Hbb1: (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
      have He1e : QFBV.len_bexp e1 < QFBV.len_exp e by auto_prove_len_lt.
      move: (IHb _ _ _ _ _ _ _ _ _ _ _ He1e Hbb1) => Hc1c.
      case Hbb2: (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
      have He2e : QFBV.len_bexp e2 < QFBV.len_exp e by auto_prove_len_lt.
      move: (IHb _ _ _ _ _ _ _ _ _ _ _ He2e Hbb2) => Hc2c1.
      rewrite -Hc1c -Hc2c1.
      case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csop lop] | ]; 
        case=> _ <- _ _ _; rewrite find_cet_add_cbt; 
        (try rewrite find_cet_add_hbt); done.
Qed.


(* = bit_blast_exp_ccache_find_cbt and bit_blast_bexp_ccache_find_cbt = *)

Lemma bit_blast_exp_ccache_find_cbt :
  forall e0 e te m c g m' c' g' cs ls,
    QFBV.len_exp e0 < QFBV.len_bexp e ->
    bit_blast_exp_ccache te m c g e0 = (m', c', g', cs, ls) ->
    find_cbt e c' = find_cbt e c
  with
    bit_blast_bexp_ccache_find_cbt :  
      forall e0 e te m c g m' c' g' cs l,
        QFBV.len_bexp e0 < QFBV.len_bexp e ->
        bit_blast_bexp_ccache te m c g e0 = (m', c', g', cs, l) ->
        find_cbt e c' = find_cbt e c.
Proof.  
  (* bit_blast_exp_ccache_find_cbt *)
  set IHe := bit_blast_exp_ccache_find_cbt.
  set IHb := bit_blast_bexp_ccache_find_cbt.
  move=> e0 e te m c g m' c' g' cs ls.
  case Hfcet: (find_cet e0 c) => [[cs0 ls0] | ]. 
  - move=> _. rewrite bit_blast_exp_ccache_equation Hfcet /=.
    case=> _ <- _ _ _. done. 
  - move: Hfcet. case e0 => [v | bs | op e1 | op e1 e2 | b e1 e2] Hfcet Hlen.
    + rewrite /= Hfcet. 
      case Hfhet : (find_het (QFBV.Evar v) c) => [[csh lsh] | ].
      * case=> _ <- _ _ _; apply find_cbt_add_cet.
      * case Hfind: (SSAVM.find v m) => [rs | ]; 
          last case Hblast : (bit_blast_var te g v) => [[vg vcs] vls];
          case=> _ <- _ _ _; rewrite find_cbt_add_cet; by apply find_cbt_add_het.
    + rewrite /= Hfcet.
      case Hfhet : (find_het (QFBV.Econst bs) c) => [[csh lsh] | ];
        case=> _ <- _ _ _; rewrite find_cbt_add_cet; (try done);
        by apply find_cbt_add_het.
    + rewrite /= Hfcet.
      case Hbb1: (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
      have He1e : QFBV.len_exp e1 < QFBV.len_bexp e by auto_prove_len_lt.
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ He1e Hbb1) => Hc1c.
      rewrite -Hc1c.
      case Hfhet : (find_het (QFBV.Eunop op e1) c1) => [[csop lsop] | ];
        last case Hbbop : (bit_blast_eunop op g1 ls1) => [[gop csop] lsop];
        case=> _ <- _ _ _; rewrite find_cbt_add_cet; (try done);
        by apply find_cbt_add_het.
    + rewrite /= Hfcet.
      case Hbb1: (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
      have He1e : QFBV.len_exp e1 < QFBV.len_bexp e by auto_prove_len_lt.
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ He1e Hbb1) => Hc1c.
      case Hbb2: (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
      have He2e : QFBV.len_exp e2 < QFBV.len_bexp e by auto_prove_len_lt.
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ He2e Hbb2) => Hc2c1.
      rewrite -Hc1c -Hc2c1.
      case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csop lsop] | ];
        last case Hbbop : (bit_blast_ebinop op g2 ls1 ls2) => [[gop csop] lsop];
        case=> _ <- _ _ _; rewrite find_cbt_add_cet; (try done);
        by apply find_cbt_add_het.
    + rewrite /= Hfcet.
      case Hbbb: (bit_blast_bexp_ccache te m c g b) => [[[[mb cb] gb] csb] lb].
      have Hbe : QFBV.len_bexp b < QFBV.len_bexp e by auto_prove_len_lt.
      move: (IHb _ _ _ _ _ _ _ _ _ _ _ Hbe Hbbb) => Hcbc.
      case Hbb1: (bit_blast_exp_ccache te mb cb gb e1) => [[[[m1 c1] g1] cs1] ls1].
      have He1e : QFBV.len_exp e1 < QFBV.len_bexp e by auto_prove_len_lt.
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ He1e Hbb1) => Hc1cb.
      case Hbb2: (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
      have He2e : QFBV.len_exp e2 < QFBV.len_bexp e by auto_prove_len_lt.
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ He2e Hbb2) => Hc2c1.
      rewrite -Hcbc -Hc1cb -Hc2c1.
      case Hfhet : (find_het (QFBV.Eite b e1 e2) c2) => [[csop lsop] | ];
        last case Hbbop : (bit_blast_ite g2 lb ls1 ls2) => [[gop csop] lsop];
        case=> _ <- _ _ _; rewrite find_cbt_add_cet; (try done);
        by apply find_cbt_add_het.
  (* bit_blast_bexp_ccache_find_cbt *)
  set IHe := bit_blast_exp_ccache_find_cbt.
  set IHb := bit_blast_bexp_ccache_find_cbt.
  move=> e0 e te m c g m' c' g' cs l.
  case Hfcbt: (find_cbt e0 c) => [[cs0 l0] | ]. 
  - move=> _. rewrite bit_blast_bexp_ccache_equation Hfcbt /=.
    case=> _ <- _ _ _. done. 
  - move: Hfcbt. case e0 => [ | | op e1 e2 | e1 | e1 e2 | e1 e2] Hfcbt Hlen.
    + rewrite /= Hfcbt. 
      case Hfhet : (find_hbt QFBV.Bfalse c) => [[csh lh] | ]; case=> _ <- _ _ _; 
        rewrite find_cbt_add_cbt_neq; (try auto_prove_neq_by_len);
        (try rewrite find_cbt_add_hbt); done.
    + rewrite /= Hfcbt.
      case Hfhet : (find_hbt QFBV.Btrue c) => [[csh lh] | ]; case=> _ <- _ _ _; 
        rewrite find_cbt_add_cbt_neq; (try auto_prove_neq_by_len);
        (try rewrite find_cbt_add_hbt); done.
    + rewrite /= Hfcbt.
      case Hbb1: (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
      have He1e : QFBV.len_exp e1 < QFBV.len_bexp e by auto_prove_len_lt.
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ He1e Hbb1) => Hc1c.
      case Hbb2: (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
      have He2e : QFBV.len_exp e2 < QFBV.len_bexp e by auto_prove_len_lt.
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ He2e Hbb2) => Hc2c1.
      rewrite -Hc1c -Hc2c1.
      case Hfhbt : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[csop lop] | ];
        last case Hbbop : (bit_blast_bbinop op g2 ls1 ls2) => [[gop csop] lsop];
        case=> _ <- _ _ _; rewrite find_cbt_add_cbt_neq; 
        (try auto_prove_neq_by_len); (try rewrite find_cbt_add_hbt); done.
    + rewrite /= Hfcbt.
      case Hbb1: (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
      have He1e : QFBV.len_bexp e1 < QFBV.len_bexp e by auto_prove_len_lt.
      move: (IHb _ _ _ _ _ _ _ _ _ _ _ He1e Hbb1) => Hc1c.
      rewrite -Hc1c.
      case Hfhbt : (find_hbt (QFBV.Blneg e1) c1) => [[csop lop] | ]; 
        case=> _ <- _ _ _; rewrite find_cbt_add_cbt_neq; 
        (try auto_prove_neq_by_len); (try rewrite find_cbt_add_hbt); done.
    + rewrite /= Hfcbt.
      case Hbb1: (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
      have He1e : QFBV.len_bexp e1 < QFBV.len_bexp e by auto_prove_len_lt.
      move: (IHb _ _ _ _ _ _ _ _ _ _ _ He1e Hbb1) => Hc1c.
      case Hbb2: (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
      have He2e : QFBV.len_bexp e2 < QFBV.len_bexp e by auto_prove_len_lt.
      move: (IHb _ _ _ _ _ _ _ _ _ _ _ He2e Hbb2) => Hc2c1.
      rewrite -Hc1c -Hc2c1.
      case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csop lop] | ]; 
        case=> _ <- _ _ _; rewrite find_cbt_add_cbt_neq; 
        (try auto_prove_neq_by_len); (try rewrite find_cet_add_hbt); done.
    + rewrite /= Hfcbt.
      case Hbb1: (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
      have He1e : QFBV.len_bexp e1 < QFBV.len_bexp e by auto_prove_len_lt.
      move: (IHb _ _ _ _ _ _ _ _ _ _ _ He1e Hbb1) => Hc1c.
      case Hbb2: (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
      have He2e : QFBV.len_bexp e2 < QFBV.len_bexp e by auto_prove_len_lt.
      move: (IHb _ _ _ _ _ _ _ _ _ _ _ He2e Hbb2) => Hc2c1.
      rewrite -Hc1c -Hc2c1.
      case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csop lop] | ]; 
        case=> _ <- _ _ _; rewrite find_cbt_add_cbt_neq; 
        (try auto_prove_neq_by_len); (try rewrite find_cbt_add_hbt); done.
Qed.


(* = bit_blast_exp_ccache_in_cet and bit_blast_bexp_ccache_in_cbt = *)

Lemma bit_blast_exp_ccache_in_cet :
  forall e te m c g m' c' g' cs ls,
    bit_blast_exp_ccache te m c g e = (m', c', g', cs, ls) ->
    exists cse, find_cet e c' = Some (cse, ls)
  with
    bit_blast_bexp_ccache_in_cbt :  
      forall e te m c g m' c' g' cs l,
        bit_blast_bexp_ccache te m c g e = (m', c', g', cs, l) ->
        exists cse, find_cbt e c' = Some (cse, l).
Proof.
  (* exp *)
  move=> e te m c g m' c' g' cs ls.
  case Hfcet: (find_cet e c) => [[cse lse] | ]. 
  - rewrite bit_blast_exp_ccache_equation Hfcet /=.
    case=> _ <- _ _ <-. exists cse; done. 
  - move: Hfcet. case: e.
    + move=> v Hfcet. rewrite /= Hfcet.
      case Hfhet : (find_het (QFBV.Evar v) c) => [[cse lse] | ];
        last case Hfv : (SSAVM.find v m);
        last case Hv : (bit_blast_var te g v) => [[gv csv] lsv];
        case=> _ <- _ _ <-; [ exists cse | exists [::] | exists csv]; 
        exact: find_cet_add_cet_eq.
    + move=> bs Hfcet. rewrite /= Hfcet.
      case Hfhet : (find_het (QFBV.Econst bs) c) => [[cse lse] | ];
        case=> _ <- _ _ <-; [ exists cse | exists [::]]; exact: find_cet_add_cet_eq.
    + move=> op e1 Hfcet. rewrite /= Hfcet.
      case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
      case Hfhet : (find_het (QFBV.Eunop op e1) c1) => [[csop lsop] | ];
        last case Hop : (bit_blast_eunop op g1 ls1) => [[gop csop] lsop];
        case=> _ <- _ _ <-; exists csop; exact: find_cet_add_cet_eq.
    + move=> op e1 e2 Hfcet. rewrite /= Hfcet.
      case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
      case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].  
      case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csop lsop] | ];
        last case Hop : (bit_blast_ebinop op g2 ls1 ls2) => [[gop csop] lsop];
        case=> _ <- _ _ <-; exists csop; exact: find_cet_add_cet_eq.
    + move=> b e1 e2 Hfcet. rewrite /= Hfcet.
      case Hb : (bit_blast_bexp_ccache te m c g b) => [[[[mb cb] gb] csb] lb].
      case He1 : (bit_blast_exp_ccache te mb cb gb e1) => [[[[m1 c1] g1] cs1] ls1].
      case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].  
      case Hfhet : (find_het (QFBV.Eite b e1 e2) c2) => [[csop lsop] | ];
        last case Hop : (bit_blast_ite g2 lb ls1 ls2) => [[gop csop] lsop];
        case=> _ <- _ _ <-; exists csop; exact: find_cet_add_cet_eq.
  (* bexp *)
  move=> e te m c g m' c' g' cs l.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite bit_blast_bexp_ccache_equation Hfcbt /=.
    case=> _ <- _ _ <-. exists cse; done. 
  - move: Hfcbt. case: e.
    + move=> Hfcbt. rewrite /= Hfcbt.
      case Hfhbt : (find_hbt (QFBV.Bfalse) c) => [[cse le] | ];
        case=> _ <- _ _ <-; [ exists cse | exists [::]]; exact: find_cbt_add_cbt_eq.
    + move=> Hfcbt. rewrite /= Hfcbt.
      case Hfhbt : (find_hbt (QFBV.Btrue) c) => [[cse le] | ];
        case=> _ <- _ _ <-; [ exists cse | exists [::]]; exact: find_cbt_add_cbt_eq.
    + move=> op e1 e2 Hfcbt. rewrite /= Hfcbt.
      case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
      case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].  
      case Hfhet : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[csop lop] | ];
        last case Hop : (bit_blast_bbinop op g2 ls1 ls2) => [[gop csop] lop];
        case=> _ <- _ _ <-; exists csop; exact: find_cbt_add_cbt_eq.
    + move=> e1 Hfcbt. rewrite /bit_blast_bexp_ccache -/bit_blast_bexp_ccache Hfcbt.
      case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
      case Hfhbt : (find_hbt (QFBV.Blneg e1) c1) => [[csop lop] | ];
        last case Hop : (bit_blast_lneg g1 l1) => [[gop csop] lop];
        case=> _ <- _ _ <-; exists csop; exact: find_cbt_add_cbt_eq.
    + move=> e1 e2 Hfcbt. 
      rewrite /bit_blast_bexp_ccache -/bit_blast_bexp_ccache Hfcbt.
      case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
      case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
      case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csop lop] | ];
        last case Hop : (bit_blast_conj g2 l1 l2) => [[gop csop] lop];
        case=> _ <- _ _ <-; exists csop; exact: find_cbt_add_cbt_eq.
    + move=> e1 e2 Hfcbt. 
      rewrite /bit_blast_bexp_ccache -/bit_blast_bexp_ccache Hfcbt.
      case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
      case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
      case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csop lop] | ];
        last case Hop : (bit_blast_disj g2 l1 l2) => [[gop csop] lop];
        case=> _ <- _ _ <-; exists csop; exact: find_cbt_add_cbt_eq.
Qed.


(* = bit_blast_exp_ccache_in_het and bit_blast_bexp_ccache_in_hbt = *)

Lemma bit_blast_exp_ccache_in_het :
  forall e te m c g m' c' g' cs ls,
    bit_blast_exp_ccache te m c g e = (m', c', g', cs, ls) ->
    CompCache.well_formed c ->
    exists cse, find_het e c' = Some (cse, ls)
  with
    bit_blast_bexp_ccache_in_hbt :  
      forall e te m c g m' c' g' cs l,
        bit_blast_bexp_ccache te m c g e = (m', c', g', cs, l) ->
        CompCache.well_formed c ->
        exists cse, find_hbt e c' = Some (cse, l).
Proof.
  (* exp *)
  move=> e te m c g m' c' g' cs ls Hbb Hwfc. move: Hbb.
  case Hfcet: (find_cet e c) => [[cse lse] | ]. 
  - rewrite bit_blast_exp_ccache_equation Hfcet /=.
    case=> _ <- _ _ <-. exists cse; exact: (well_formed_find_cet Hwfc Hfcet). 
  - move: Hfcet. case: e.
    + move=> v Hfcet. rewrite /= Hfcet.
      case Hfhet : (find_het (QFBV.Evar v) c) => [[cse lse] | ];
        last case Hfv : (SSAVM.find v m);
        last case Hv : (bit_blast_var te g v) => [[gv csv] lsv];
        case=> _ <- _ _ <-; [ exists cse | exists [::] | exists csv]; 
        rewrite find_het_add_cet; try rewrite find_het_add_het_eq; done.
    + move=> bs Hfcet. rewrite /= Hfcet.
      case Hfhet : (find_het (QFBV.Econst bs) c) => [[csop lsop] | ];
        case=> _ <- _ _ <-; [ exists csop | exists [::]]; 
        rewrite find_het_add_cet; try rewrite find_het_add_het_eq; done.
    + move=> op e1 Hfcet. rewrite /= Hfcet.
      case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
      case Hfhet : (find_het (QFBV.Eunop op e1) c1) => [[csop lsop] | ];
        last case Hop : (bit_blast_eunop op g1 ls1) => [[gop csop] lsop];
        case=> _ <- _ _ <-; exists csop; 
        rewrite find_het_add_cet; try rewrite find_het_add_het_eq; done.
    + move=> op e1 e2 Hfcet. rewrite /= Hfcet.
      case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
      case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].  
      case Hfhet : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csop lsop] | ];
        last case Hop : (bit_blast_ebinop op g2 ls1 ls2) => [[gop csop] lsop];
        case=> _ <- _ _ <-; exists csop; 
        rewrite find_het_add_cet; try rewrite find_het_add_het_eq; done.
    + move=> b e1 e2 Hfcet. rewrite /= Hfcet.
      case Hb : (bit_blast_bexp_ccache te m c g b) => [[[[mb cb] gb] csb] lb].
      case He1 : (bit_blast_exp_ccache te mb cb gb e1) => [[[[m1 c1] g1] cs1] ls1].
      case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].  
      case Hfhet : (find_het (QFBV.Eite b e1 e2) c2) => [[csop lsop] | ];
        last case Hop : (bit_blast_ite g2 lb ls1 ls2) => [[gop csop] lsop];
        case=> _ <- _ _ <-; exists csop; 
        rewrite find_het_add_cet; try rewrite find_het_add_het_eq; done.
  (* bexp *)
  move=> e te m c g m' c' g' cs l Hbb Hwfc. move: Hbb.
  case Hfcbt: (find_cbt e c) => [[cse le] | ]. 
  - rewrite bit_blast_bexp_ccache_equation Hfcbt /=.
    case=> _ <- _ _ <-. exists cse; exact: (well_formed_find_cbt Hwfc Hfcbt). 
  - move: Hfcbt. case: e.
    + move=> Hfcbt. rewrite /= Hfcbt.
      case Hfhbt : (find_hbt (QFBV.Bfalse) c) => [[csop lop] | ];
        case=> _ <- _ _ <-; [ exists csop | exists [::]]; 
        rewrite find_hbt_add_cbt; try rewrite find_hbt_add_hbt_eq; done.
    + move=> Hfcbt. rewrite /= Hfcbt.
      case Hfhbt : (find_hbt (QFBV.Btrue) c) => [[csop lop] | ];
        case=> _ <- _ _ <-; [ exists csop | exists [::]]; 
        rewrite find_hbt_add_cbt; try rewrite find_hbt_add_hbt_eq; done.
    + move=> op e1 e2 Hfcbt. rewrite /= Hfcbt.
      case He1 : (bit_blast_exp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
      case He2 : (bit_blast_exp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].  
      case Hfhbt : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[csop lop] | ];
        last case Hop : (bit_blast_bbinop op g2 ls1 ls2) => [[gop csop] lop];
        case=> _ <- _ _ <-; exists csop; 
        rewrite find_hbt_add_cbt; try rewrite find_hbt_add_hbt_eq; done.
    + move=> e1 Hfcbt. 
      rewrite /bit_blast_bexp_ccache -/bit_blast_bexp_ccache Hfcbt.
      case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
      case Hfhbt : (find_hbt (QFBV.Blneg e1) c1) => [[csop lop] | ];
        last case Hop : (bit_blast_lneg g1 l1) => [[gop csop] lop];
        case=> _ <- _ _ <-; exists csop; 
        rewrite find_hbt_add_cbt; try rewrite find_hbt_add_hbt_eq; done.
    + move=> e1 e2 Hfcbt. 
      rewrite /bit_blast_bexp_ccache -/bit_blast_bexp_ccache Hfcbt.
      case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
      case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
      case Hfhbt : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csop lop] | ];
        last case Hop : (bit_blast_conj g2 l1 l2) => [[gop csop] lop];
        case=> _ <- _ _ <-; exists csop; 
        rewrite find_hbt_add_cbt; try rewrite find_hbt_add_hbt_eq; done.
    + move=> e1 e2 Hfcbt. 
      rewrite /bit_blast_bexp_ccache -/bit_blast_bexp_ccache Hfcbt.
      case He1 : (bit_blast_bexp_ccache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
      case He2 : (bit_blast_bexp_ccache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
      case Hfhbt : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csop lop] | ];
        last case Hop : (bit_blast_disj g2 l1 l2) => [[gop csop] lop];
        case=> _ <- _ _ <-; exists csop; 
        rewrite find_hbt_add_cbt; try rewrite find_hbt_add_hbt_eq; done.
Qed.
