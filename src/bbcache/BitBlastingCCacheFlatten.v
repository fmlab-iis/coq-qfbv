From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics Seqs.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
From BBCache Require Import BitBlastingInit CacheFlatten BitBlastingCCacheExport BitBlastingCacheExport.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ==== bit_blast_exp_fccache and bit_blast_bexp_fccache ==== *)

(* The bit-blasting with complete information is used for correctness. *)

From BBCache Require Import CCacheFlatten.

Fixpoint bit_blast_exp_fccache E m c g e : vm * ccache * generator * seq cnf * word :=
  (* = bit_blast_exp_nocet = *)
  let bit_blast_exp_nocet E m c g e : vm * ccache * generator * seq cnf * word * seq cnf :=
      match e with
      | QFBV.Evar v =>
        match find_het e c with
        | Some (cs, ls) => (m, c, g, cs, ls, cs)
        | None =>
          match SSAVM.find v m with
          | None => let '(g', cs, rs) := bit_blast_var E g v in
                    (SSAVM.add v rs m, add_het e [:: cs] rs c, g', [:: cs], rs, [:: cs])
          | Some rs => (m, add_het e [::] rs c, g, [::], rs, [::])
          end
        end
      | QFBV.Econst bs =>
        match find_het e c with
        | Some (cs, ls) => (m, c, g, cs, ls, cs)
        | None => let '(g', cs, rs) := bit_blast_const g bs in
                  (m, add_het e [:: cs] rs c, g', [:: cs], rs, [:: cs])
        end
      | QFBV.Eunop op e1 =>
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_fccache E m c g e1 in
        match find_het e c1 with
        | Some (csop, lsop) => (m1, c1, g1, catrev cs1 csop, lsop, csop)
        | None =>
          let '(gop, csop, lsop) := bit_blast_eunop op g1 ls1 in
          (m1, add_het e [:: csop] lsop c1, gop,
           catrev cs1 [:: csop], lsop, [:: csop])
        end
      | QFBV.Ebinop op e1 e2 =>
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_fccache E m c g e1 in
        let '(m2, c2, g2, cs2, ls2) := bit_blast_exp_fccache E m1 c1 g1 e2 in
        match find_het e c2 with
        | Some (csop, lsop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lsop, csop)
        | None =>
          let '(gop, csop, lsop) := bit_blast_ebinop op g2 ls1 ls2 in
          (m2, add_het e [:: csop] lsop c2, gop,
           catrev cs1 (catrev cs2 [:: csop]), lsop, [:: csop])
        end
      | QFBV.Eite b e1 e2 =>
        let '(mb, cb, gb, csb, lb) := bit_blast_bexp_fccache E m c g b in
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_fccache E mb cb gb e1 in
        let '(m2, c2, g2, cs2, ls2) := bit_blast_exp_fccache E m1 c1 g1 e2 in
        match find_het e c2 with
        | Some (csop, lsop) =>
          (m2, c2, g2, catrev csb (catrev cs1 (catrev cs2 csop)), lsop, csop)
        | None =>
          let '(gop, csop, lsop) := bit_blast_ite g2 lb ls1 ls2 in
          (m2, add_het e [:: csop] lsop c2, gop,
           catrev csb (catrev cs1 (catrev cs2 [:: csop])), lsop, [:: csop])
        end
      end
  (* = = *)
  in
  match find_cet e c with
  | Some (cs, ls) => (m, c, g, [::], ls)
  | None => let '(m', c', g', cs, lrs, csop) := bit_blast_exp_nocet E m c g e in
            (m', CCacheFlatten.add_cet e csop lrs c', g', cs, lrs)
  end
with
bit_blast_bexp_fccache E m c g e : vm * ccache * generator * seq cnf * literal :=
  (* = bit_blast_bexp_nocbt = *)
  let bit_blast_bexp_nocbt E m c g e : vm * ccache * generator * seq cnf * literal * seq cnf :=
      match e with
      | QFBV.Bfalse =>
        match find_hbt e c with
        | Some (cs, l) => (m, c, g, cs, l, cs)
        | None => (m, add_hbt e [::] lit_ff c, g, [::], lit_ff, [::])
        end
      | QFBV.Btrue =>
        match find_hbt e c with
        | Some (cs, l) => (m, c, g, cs, l, cs)
        | None => (m, add_hbt e [::] lit_tt c, g, [::], lit_tt, [::])
        end
      | QFBV.Bbinop op e1 e2 =>
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_fccache E m c g e1 in
        let '(m2, c2, g2, cs2, ls2) := bit_blast_exp_fccache E m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None =>
          let '(gop, csop, lop) := bit_blast_bbinop op g2 ls1 ls2 in
          (m2, add_hbt e [:: csop] lop c2, gop,
           catrev cs1 (catrev cs2 [:: csop]), lop, [:: csop])
        end
      | QFBV.Blneg e1 =>
        let '(m1, c1, g1, cs1, l1) := bit_blast_bexp_fccache E m c g e1 in
        match find_hbt e c1 with
        | Some (csop, lop) => (m1, c1, g1, catrev cs1 csop, lop, csop)
        | None => let '(gop, csop, lop) := bit_blast_lneg g1 l1 in
                  (m1, add_hbt e [:: csop] lop c1, gop,
                   catrev cs1 [:: csop], lop, [:: csop])
        end
      | QFBV.Bconj e1 e2 =>
        let '(m1, c1, g1, cs1, l1) := bit_blast_bexp_fccache E m c g e1 in
        let '(m2, c2, g2, cs2, l2) := bit_blast_bexp_fccache E m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None => let '(gop, csop, lop) := bit_blast_conj g2 l1 l2 in
                  (m2, add_hbt e [:: csop] lop c2, gop,
                   catrev cs1 (catrev cs2 [:: csop]), lop, [:: csop])
        end
      | QFBV.Bdisj e1 e2 =>
        let '(m1, c1, g1, cs1, l1) := bit_blast_bexp_fccache E m c g e1 in
        let '(m2, c2, g2, cs2, l2) := bit_blast_bexp_fccache E m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None => let '(gop, csop, lop) := bit_blast_disj g2 l1 l2 in
                  (m2, add_hbt e [:: csop] lop c2, gop,
                   catrev cs1 (catrev cs2 [:: csop]), lop, [:: csop])
        end
      end
  (* = = *)
  in
  match find_cbt e c with
  | Some (cs, l) => (m, c, g, [::], l)
  | None => let '(m', c', g', cs, lr, csop) := bit_blast_bexp_nocbt E m c g e in
            (m', CCacheFlatten.add_cbt e csop lr c', g', cs, lr)
  end.

Definition init_fccache : ccache := CCacheFlatten.empty.

Lemma init_fccache_compatible : ccache_compatible init_fccache init_ccache.
Proof. done. Qed.

Ltac dcase_bb_base :=
  match goal with
  | |- context f [bit_blast_var ?E ?g ?v] =>
    let g' := fresh in
    let cs := fresh in
    let lrs := fresh in
    let H := fresh in
    dcase (bit_blast_var E g v) => [[[g' cs] lrs] H]
  | |- context f [bit_blast_eunop ?op ?g ?lrs] =>
    let g' := fresh in
    let cs' := fresh in
    let lrs' := fresh in
    let H := fresh in
    dcase (bit_blast_eunop op g lrs) => [[[g' cs'] lrs'] H]
  | |- context f [bit_blast_ebinop ?op ?g ?lrs1 ?lrs2] =>
    let g' := fresh in
    let cs' := fresh in
    let lrs' := fresh in
    let H := fresh in
    dcase (bit_blast_ebinop op g lrs1 lrs2) => [[[g' cs'] lrs'] H]
  | |- context f [bit_blast_ite ?g ?lr ?ls1 ?ls2] =>
    let g' := fresh in
    let cs' := fresh in
    let lr' := fresh in
    let H := fresh in
    dcase (bit_blast_ite g lr ls1 ls2) => [[[g' cs'] lr'] H]
  | |- context f [bit_blast_bbinop ?op ?g ?lrs1 ?lrs2] =>
    let g' := fresh in
    let cs' := fresh in
    let lr' := fresh in
    let H := fresh in
    dcase (bit_blast_bbinop op g lrs1 lrs2) => [[[g' cs'] lr'] H]
  end.

Ltac dcase_bb_ccache :=
  match goal with
  | |- context f [find_cet ?e ?c] =>
    let Hfe_cet := fresh in
    let cs := fresh in
    let lrs := fresh in
    dcase (find_cet e c); case=> [[cs lrs]|] Hfe_cet
  | |- context f [find_cbt ?e ?c] =>
    let Hfe_cbt := fresh in
    let cs := fresh in
    let lr := fresh in
    dcase (find_cbt e c); case=> [[cs lr]|] Hfe_cbt
  | |- context f [find_het ?e ?c] =>
    let Hfe_het := fresh in
    let cs := fresh in
    let lrs := fresh in
    dcase (find_het e c); case=> [[cs lrs]|] Hfe_het
  | |- context f [find_hbt ?e ?c] =>
    let Hfe_hbt := fresh in
    let cs := fresh in
    let lr := fresh in
    dcase (find_hbt e c); case=> [[cs lr]|] Hfe_hbt
  (**)
  | |- context f [SSAVM.find ?v ?m] =>
    let lrs := fresh in
    case: (SSAVM.find v m) => [lrs|]
  | |- context f [bit_blast_exp_fccache ?E ?m ?ec ?g ?e] =>
    let m' := fresh in
    let ec' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lrs := fresh in
    let H := fresh in
    dcase (bit_blast_exp_fccache E m ec g e) =>
    [[[[[m' ec'] g'] cs] lrs] H]
  | |- context f [bit_blast_bexp_fccache ?E ?m ?ec ?g ?e] =>
    let m' := fresh in
    let ec' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lr := fresh in
    let H := fresh in
    dcase (bit_blast_bexp_fccache E m ec g e) =>
    [[[[[m' ec'] g'] cs] lr] H]
  | |- context f [bit_blast_exp_ccache ?E ?m ?c ?g ?e] =>
    let m' := fresh in
    let c' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lrs := fresh in
    let H := fresh in
    dcase (bit_blast_exp_ccache E m c g e) =>
    [[[[[m' c'] g'] cs] lrs] H]
  | |- context f [bit_blast_bexp_ccache ?E ?m ?c ?g ?e] =>
    let m' := fresh in
    let c' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lr := fresh in
    let H := fresh in
    dcase (bit_blast_bexp_ccache E m c g e) =>
    [[[[[m' c'] g'] cs] lr] H]
  (**)
  | |- _ => dcase_bb_base
  end.

Ltac simpl_ccache_compatible :=
  match goal with
  | |- ccache_compatible (add_cet ?e ?ecs ?lrs _) (CompCache.add_cet ?e ?cs ?lrs _) =>
    apply: ccache_compatible_add_cet
  | |- ccache_compatible (add_cbt ?e ?ecs ?lr _) (CompCache.add_cbt ?e ?cs ?lr _) =>
    apply: ccache_compatible_add_cbt
  | |- ccache_compatible (add_het ?e ?ecs ?lrs _) (CompCache.add_het ?e ?cs ?lrs _) =>
    apply: ccache_compatible_add_het
  | |- ccache_compatible (add_hbt ?e ?ecs ?lrs _) (CompCache.add_hbt ?e ?cs ?lrs _) =>
    apply: ccache_compatible_add_hbt
  | |- cnf_eqsat (tflatten [:: ?cs]) ?cs => exact: tflatten_singleton_eqsat
  | |- cnf_eqsat (tflatten (catrev _ _)) ?cs => apply: tflatten_catrev_eqsat
  | |- cnf_eqsat (tflatten [::]) [::] => done
  (**)
  | Hc : ccache_compatible ?ec ?c,
    H : find_cet ?e ?ec = None |- context f [CompCache.find_cet ?e ?c] =>
    move/(ccache_compatible_find_cet_none _ Hc): H => H; rewrite H
  | Hc : ccache_compatible ?ec ?c,
    H : find_cbt ?e ?ec = None |- context f [CompCache.find_cbt ?e ?c] =>
    move/(ccache_compatible_find_cbt_none _ Hc): H => H; rewrite H
  | Hc : ccache_compatible ?ec ?c,
    H : find_het ?e ?ec = None |- context f [CompCache.find_het ?e ?c] =>
    move/(ccache_compatible_find_het_none _ Hc): H => H; rewrite H
  | Hc : ccache_compatible ?ec ?c,
    H : find_hbt ?e ?ec = None |- context f [CompCache.find_hbt ?e ?c] =>
    move/(ccache_compatible_find_hbt_none _ Hc): H => H; rewrite H
  | Hc : ccache_compatible ?ec ?c,
    H : find_cet ?e ?ec = Some _ |- context f [CompCache.find_cet ?e ?c] =>
    let cs := fresh in
    let Hf_cet := fresh in
    let Heqs := fresh in
    let Heqn := fresh in
    move: (ccache_compatible_find_cet_some_exists1 Hc H) =>
    [cs [Hf_cet [Heqs Heqn]]]; rewrite Hf_cet
  | Hc : ccache_compatible ?ec ?c,
    H : find_cbt ?e ?ec = Some _ |- context f [CompCache.find_cbt ?e ?c] =>
    let cs := fresh in
    let Hf_cbt := fresh in
    let Heqs := fresh in
    let Heqn := fresh in
    move: (ccache_compatible_find_cbt_some_exists1 Hc H) =>
    [cs [Hf_cbt [Heqs Heqn]]]; rewrite Hf_cbt
  | Hc : ccache_compatible ?ec ?c,
    H : find_het ?e ?ec = Some _ |- context f [CompCache.find_het ?e ?c] =>
    let cs := fresh in
    let Hf_het := fresh in
    let Heqs := fresh in
    let Heqs := fresh in
    move: (ccache_compatible_find_het_some_exists1 Hc H) =>
    [cs [Hf_het [Heqs heqn]]]; rewrite Hf_het
  | Hc : ccache_compatible ?ec ?c,
    H : find_hbt ?e ?ec = Some _ |- context f [CompCache.find_hbt ?e ?c] =>
    let cs := fresh in
    let Hf_hbt := fresh in
    let Heqs := fresh in
    let Heqs := fresh in
    move: (ccache_compatible_find_hbt_some_exists1 Hc H) =>
    [cs [Hf_hbt [Heqs Heqn]]]; rewrite Hf_hbt
  end.

Ltac solve_eqnew :=
  match goal with
  | |- cnf_eqnew (tflatten [::]) [::] => done
  | |- cnf_eqnew (tflatten [:: ?cs]) ?cs => exact: tflatten_singleton_eqnew
  | H12 : cnf_eqnew (tflatten ?cs1) ?cs2
    |- cnf_eqnew (tflatten (catrev ?cs1 ?cs3)) (catrev ?cs2 ?cs4) =>
    apply: (cnf_eqnew_catrev2 H12)
  | H34 : cnf_eqnew (tflatten ?cs3) ?cs4
    |- cnf_eqnew (tflatten (catrev ?cs1 ?cs3)) (catrev ?cs2 ?cs4) =>
    apply: (cnf_eqnew_catrev2 _ H34)
  end.

Ltac myauto :=
  repeat
    match goal with
    | |- _ /\ _ => split
    | |- ?e = ?e => reflexivity
    | H : ?p |- ?p => assumption
    | |- (_, _, _, _, _) = (_, _, _, _, _) -> _ =>
      case=> ? ? ? ? ?; subst
    (* apply induction hypothesis *)
    | bit_blast_exp_fccache_valid :
        (forall (E : SSATE.env)
               (e : QFBV.exp) (im : vm)
               (iec : ccache) (ic : CompCache.compcache)
               (ig : generator) (em : vm)
               (ec : ccache) (eg : generator)
               (ecs : seq cnf) (elrs : word)
               (m : vm) (c : CompCache.compcache)
               (g : generator) (cs : cnf)
               (lrs : word),
            ccache_compatible iec ic ->
            bit_blast_exp_fccache E im iec ig e = (em, ec, eg, ecs, elrs) ->
            bit_blast_exp_ccache E im ic ig e =
            (m, c, g, cs, lrs) ->
            em = m /\
            ccache_compatible ec c /\
            eg = g /\ cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs /\ elrs = lrs),
      Hcc : ccache_compatible ?iec ?ic,
      Hbbe : bit_blast_exp_fccache ?E ?im ?iec ?ig ?e = _,
      Hbb : bit_blast_exp_ccache ?E ?im ?ic ?ig ?e = _ |- _ =>
      let Hm := fresh in
      let Hc := fresh in
      let Hg := fresh in
      let Hcs_eqs := fresh in
      let Hcs_eqn := fresh in
      let Hlrs:= fresh in
      move: (bit_blast_exp_fccache_valid
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcc Hbbe Hbb);
      move=> [Hm [Hc [Hg [Hcs_eqs [Hcs_eqn Hlrs]]]]]; subst; clear Hbbe Hbb
    | bit_blast_bexp_fccache_valid :
        (forall (E : SSATE.env)
                (e : QFBV.bexp) (im : vm)
                (iec : ccache) (ic : CompCache.compcache)
                (ig : generator) (em : vm)
                (ec : ccache) (eg : generator)
                (ecs : seq cnf) (elr : literal)
                (m : vm) (c : CompCache.compcache)
                (g : generator) (cs : cnf)
                (lr : literal),
            ccache_compatible iec ic ->
            bit_blast_bexp_fccache E im iec ig e = (em, ec, eg, ecs, elr) ->
            bit_blast_bexp_ccache E im ic ig e = (m, c, g, cs, lr) ->
            em = m /\
            ccache_compatible ec c /\
            eg = g /\ cnf_eqsat (tflatten ecs) cs /\ cnf_eqnew (tflatten ecs) cs /\ elr = lr),
      Hcc : ccache_compatible ?iec ?ic,
      Hbbe : bit_blast_bexp_fccache ?E ?im ?iec ?ig ?e = _,
      Hbb : bit_blast_bexp_ccache ?E ?im ?ic ?ig ?e = _ |- _ =>
      let Hm := fresh in
      let Hc := fresh in
      let Hg := fresh in
      let Hcs_eqs := fresh in
      let Hcs_eqn := fresh in
      let Hlr:= fresh in
      move: (bit_blast_bexp_fccache_valid
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcc Hbbe Hbb);
      move=> [Hm [Hc [Hg [Hcs_eqs [Hcs_eqn Hlr]]]]]; subst; clear Hbbe Hbb
    (**)
    | |- _ => simpl_ccache_compatible || dcase_bb_ccache || solve_eqnew
    end.

Lemma bit_blast_exp_fccache_valid
      E e im iec ic ig em ec eg ecs elrs m c g cs lrs :
  ccache_compatible iec ic ->
  bit_blast_exp_fccache E im iec ig e = (em, ec, eg, ecs, elrs) ->
  bit_blast_exp_ccache E im ic ig e = (m, c, g, cs, lrs) ->
  em = m
  /\ ccache_compatible ec c
  /\ eg = g
  /\ cnf_eqsat (tflatten ecs) cs
  /\ cnf_eqnew (tflatten ecs) cs
  /\ elrs = lrs
with
bit_blast_bexp_fccache_valid E e im iec ic ig em ec eg ecs elr m c g cs lr :
  ccache_compatible iec ic ->
  bit_blast_bexp_fccache E im iec ig e = (em, ec, eg, ecs, elr) ->
  bit_blast_bexp_ccache E im ic ig e = (m, c, g, cs, lr) ->
  em = m
  /\ ccache_compatible ec c
  /\ eg = g
  /\ cnf_eqsat (tflatten ecs) cs
  /\ cnf_eqnew (tflatten ecs) cs
  /\ elr = lr.
Proof.
  (* bit_blast_exp_fccache_valid *)
  move=> Hcc. case: e => /=.
  - move=> v. by myauto.
  - move=> bs. by myauto.
  - move=> op e. by myauto.
  - move=> op e1 e2. by myauto.
  - move=> e1 e2 e3. by myauto.
  (* bit_blast_bexp_fccache_valid *)
  move=> Hcc. case: e => /=.
  - by myauto.
  - by myauto.
  - move=> op e1 e2. by myauto.
  - move=> e. by myauto.
  - move=> e1 e2. by myauto.
  - move=> e1 e2. by myauto.
Qed.

Theorem bit_blast_bexp_fccache_sound E e m c g cs lr :
  bit_blast_bexp_fccache
    E init_vm init_fccache init_gen e = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexp e E ->
  ~ (sat (add_prelude ([::neg_lit lr]::(tflatten cs)))) ->
  (forall s, AdhereConform.conform_bexp e s E ->
             QFBV.eval_bexp e s).
Proof.
  move=> Hbbe Hwf Hsat.
  dcase (bit_blast_bexp_ccache E init_vm init_ccache init_gen e) =>
  [[[[[m' c'] g'] cs'] lr'] Hbb].
  move: (bit_blast_bexp_fccache_valid
           (init_fccache_compatible) Hbbe Hbb) => [Hm [Hcc [Hg [Heqs [Heqn Hlr]]]]]; subst.
  apply: (bit_blast_ccache_sound Hbb Hwf). move=> Hs. apply: Hsat.
  move: (cnf_eqsat_cons (clause_eqsat_refl [:: neg_lit lr']) Heqs) => Heqs'.
  apply/(cnf_eqsat_add_prelude_sat Heqs'). assumption.
Qed.

Theorem bit_blast_bexp_fccache_complete E e m c g cs lr :
  bit_blast_bexp_fccache E init_vm init_fccache init_gen e = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexp e E ->
  (forall s, AdhereConform.conform_bexp e s E ->
             QFBV.eval_bexp e s) ->
  ~ (sat (add_prelude ([::neg_lit lr]::(tflatten cs)))).
Proof.
  move=> Hbbe Hwf Hev.
  dcase (bit_blast_bexp_ccache E init_vm init_ccache init_gen e) =>
  [[[[[m' c'] g'] cs'] lr'] Hbb].
  move: (bit_blast_bexp_fccache_valid
           (init_fccache_compatible) Hbbe Hbb) => [Hm [Hcc [Hg [Heqs [Heqn Hlr]]]]]; subst.
  move=> Hs. move: (cnf_eqsat_cons (clause_eqsat_refl [:: neg_lit lr']) Heqs) => Heqs'.
  move/(cnf_eqsat_add_prelude_sat Heqs'): Hs => {Heqs'}.
  exact: (bit_blast_ccache_complete Hbb Hwf Hev).
Qed.

Theorem bit_blast_bexp_fccache_sat_sound E e m c g cs lr :
  bit_blast_bexp_fccache
    E init_vm init_fccache init_gen e = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexp e E ->
  (sat (add_prelude ([::lr]::(tflatten cs)))) ->
  (exists s, AdhereConform.conform_bexp e s E /\
             QFBV.eval_bexp e s).
Proof.
  move=> Hbbe Hwf Hsat.
  dcase (bit_blast_bexp_ccache E init_vm init_ccache init_gen e) =>
  [[[[[m' c'] g'] cs'] lr'] Hbb].
  move: (bit_blast_bexp_fccache_valid
           (init_fccache_compatible) Hbbe Hbb) => [Hm [Hcc [Hg [Heqs [Heqn Hlr]]]]]; subst.
  apply: (bit_blast_ccache_sat_sound Hbb Hwf).
  move: (cnf_eqsat_cons (clause_eqsat_refl [:: lr']) Heqs) => Heqs'.
  apply/(cnf_eqsat_add_prelude_sat Heqs'). assumption.
Qed.

Theorem bit_blast_bexp_fccache_sat_complete E e m c g cs lr :
  bit_blast_bexp_fccache E init_vm init_fccache init_gen e = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexp e E ->
  (exists s, AdhereConform.conform_bexp e s E /\
             QFBV.eval_bexp e s) ->
  (sat (add_prelude ([::lr]::(tflatten cs)))).
Proof.
  move=> Hbbe Hwf Hev.
  dcase (bit_blast_bexp_ccache E init_vm init_ccache init_gen e) =>
  [[[[[m' c'] g'] cs'] lr'] Hbb].
  move: (bit_blast_bexp_fccache_valid
           (init_fccache_compatible) Hbbe Hbb) => [Hm [Hcc [Hg [Heqs [Heqn Hlr]]]]]; subst.
  move: (cnf_eqsat_cons (clause_eqsat_refl [:: lr']) Heqs) => Heqs'.
  apply/(cnf_eqsat_add_prelude_sat Heqs').
  exact: (bit_blast_ccache_sat_complete Hbb Hwf Hev).
Qed.



(* ==== general case ==== *)

(* = bit-blasting multiple bexps = *)

Definition bit_blast_bexp_fccache_tflatten E m c g e :=
  let '(m', c', g', css', lr') := bit_blast_bexp_fccache E m c g e in
  (m', c', g', tflatten css', lr').

Fixpoint bit_blast_bexps_fccache E (es : seq QFBV.bexp) :=
  match es with
  | [::] => (init_vm, init_fccache, init_gen, add_prelude [::], lit_tt)
  | e :: es' =>
    let '(m, c, g, cs, lr) := bit_blast_bexps_fccache E es' in
    bit_blast_bexp_fccache_tflatten E m (CCacheFlatten.reset_ct c) g e
  end.

Lemma bit_blast_bexps_fccache_valid E es m c g cs lr m' c' g' cs' lr' :
  bit_blast_bexps_fccache E es = (m, c, g, cs, lr) ->
  bit_blast_bexps_ccache E es = (m', c', g', cs', lr') ->
  m = m' /\ ccache_compatible c c' /\ g = g' /\ cnf_eqsat cs cs' /\ cnf_eqnew cs cs' /\ lr = lr'.
Proof.
  elim: es m c g cs lr m' c' g' cs' lr' => [| e es IH] m c g cs lr m' c' g' cs' lr' /=.
  - move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
  - dcase (bit_blast_bexps_fccache E es) => [[[[[m1 c1] g1] cs1] lr1] Hbbe1].
    move=> Hbbe2.
    dcase (bit_blast_bexps_ccache E es) => [[[[[m1' c1'] g1'] cs1'] lr1'] Hbb1].
    move=> Hbb2. move: (IH _ _ _ _ _ _ _ _ _ _ Hbbe1 Hbb1).
    move=> [Hn [Hc [Hg [Heqs [Heqn Hlr]]]]]; subst.
    move: Hbbe2. rewrite /bit_blast_bexp_fccache_tflatten.
    dcase (bit_blast_bexp_fccache E m1' (reset_ct c1) g1' e) =>
    [[[[[m'' c''] g''] cs''] lrs''] Hbbe1']. case=> ? ? ? ? ?; subst.
    exact: (bit_blast_bexp_fccache_valid (ccache_compatible_reset_ct Hc)
                                           Hbbe1' Hbb2).
Qed.

Theorem bit_blast_bexps_fccache_sound e es E m c g cs lr :
  bit_blast_bexps_fccache E (e::es) = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexps (e::es) E ->
  ~ (sat (add_prelude ([::neg_lit lr]::cs))) ->
  (forall s, AdhereConform.conform_bexps (e::es) s E ->
             QFBV.eval_bexp e s).
Proof.
  move=> Hbbe Hwf Hsat.
  dcase (bit_blast_bexps_ccache E (e::es)) => [[[[[m' c'] g'] cs'] lr'] Hbb].
  move: (bit_blast_bexps_fccache_valid Hbbe Hbb).
  move=> [Hm [Hc [Hg [Heqs [Heqn Hlr]]]]]; subst.
  have Hsat': ~ sat (add_prelude ([:: neg_lit lr'] :: cs')).
  { move=> H. apply: Hsat.
    move: (cnf_eqsat_cons (clause_eqsat_refl [:: neg_lit lr']) Heqs) => Heqs'.
    apply/(cnf_eqsat_add_prelude_sat Heqs'). assumption. }
  exact: (bit_blast_ccache_sound_general Hbb Hwf Hsat').
Qed.

Theorem bit_blast_bexps_fccache_complete e es E m c g cs lr :
  bit_blast_bexps_fccache E (e::es) = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexps (e::es) E ->
  (forall s, AdhereConform.conform_bexps (e::es) s E ->
             QFBV.eval_bexp e s) ->
  ~ (sat (add_prelude ([::neg_lit lr]::cs))).
Proof.
  move=> Hbbe Hwf Hev Hsat.
  dcase (bit_blast_bexps_ccache E (e::es)) => [[[[[m' c'] g'] cs'] lr'] Hbb].
  move: (bit_blast_bexps_fccache_valid Hbbe Hbb).
  move=> [Hm [Hc [Hg [Heqs [Heqn Hlr]]]]]; subst.
  have Hsat': sat (add_prelude ([:: neg_lit lr'] :: cs')).
  { move: (cnf_eqsat_cons (clause_eqsat_refl [:: neg_lit lr']) Heqs) => Heqs'.
    apply/(cnf_eqsat_add_prelude_sat Heqs'). assumption. }
  move: Hsat'. exact: (bit_blast_ccache_complete_general Hbb Hwf Hev).
Qed.

Definition bexp_to_cnf_fccache E m c g e :=
  let '(m', c', g', cs, lr) := bit_blast_bexp_fccache_tflatten E m c g e in
  (m', c', g', add_prelude ([::neg_lit lr]::cs)).


(* ===== mk_env_exp_fccache and mk_env_bexp_fccache ===== *)

Fixpoint mk_env_exp_fccache E s m c g e : env * vm * ccache * generator * seq cnf * word :=
  (* = bit_blast_exp_nocet = *)
  let mk_env_exp_nocet E s m c g e : env * vm * ccache * generator * seq cnf * word * seq cnf :=
      match e with
      | QFBV.Evar v =>
        match find_het e c with
        | Some (cs, ls) => (E, m, c, g, cs, ls, cs)
        | None =>
          match SSAVM.find v m with
          | None => let '(E', g', cs, rs) := mk_env_var E g (SSAStore.acc v s) v in
                    (E', SSAVM.add v rs m, add_het e [:: cs] rs c, g', [:: cs], rs, [:: cs])
          | Some rs => (E, m, add_het e [::] rs c, g, [::], rs, [::])
          end
        end
      | QFBV.Econst bs =>
        match find_het e c with
        | Some (cs, ls) => (E, m, c, g, cs, ls, cs)
        | None => let '(E', g', cs, rs) := mk_env_const E g bs in
                  (E', m, add_het e [:: cs] rs c, g', [:: cs], rs, [:: cs])
        end
      | QFBV.Eunop op e1 =>
        let '(E1, m1, c1, g1, cs1, ls1) := mk_env_exp_fccache E s m c g e1 in
        match find_het e c1 with
        | Some (csop, lsop) => (E1, m1, c1, g1, catrev cs1 csop, lsop, csop)
        | None =>
          let '(Eop, gop, csop, lsop) := mk_env_eunop op E1 g1 ls1 in
          (Eop, m1, add_het e [:: csop] lsop c1, gop,
           catrev cs1 [:: csop], lsop, [:: csop])
        end
      | QFBV.Ebinop op e1 e2 =>
        let '(E1, m1, c1, g1, cs1, ls1) := mk_env_exp_fccache E s m c g e1 in
        let '(E2, m2, c2, g2, cs2, ls2) := mk_env_exp_fccache E1 s m1 c1 g1 e2 in
        match find_het e c2 with
        | Some (csop, lsop) => (E2, m2, c2, g2, catrev cs1 (catrev cs2 csop), lsop, csop)
        | None =>
          let '(Eop, gop, csop, lsop) := mk_env_ebinop op E2 g2 ls1 ls2 in
          (Eop, m2, add_het e [:: csop] lsop c2, gop,
           catrev cs1 (catrev cs2 [:: csop]), lsop, [:: csop])
        end
      | QFBV.Eite b e1 e2 =>
        let '(Eb, mb, cb, gb, csb, lb) := mk_env_bexp_fccache E s m c g b in
        let '(E1, m1, c1, g1, cs1, ls1) := mk_env_exp_fccache Eb s mb cb gb e1 in
        let '(E2, m2, c2, g2, cs2, ls2) := mk_env_exp_fccache E1 s m1 c1 g1 e2 in
        match find_het e c2 with
        | Some (csop, lsop) =>
          (E2, m2, c2, g2, catrev csb (catrev cs1 (catrev cs2 csop)), lsop, csop)
        | None =>
          let '(Eop, gop, csop, lsop) := mk_env_ite E2 g2 lb ls1 ls2 in
          (Eop, m2, add_het e [:: csop] lsop c2, gop,
           catrev csb (catrev cs1 (catrev cs2 [:: csop])), lsop, [:: csop])
        end
      end
  (* = = *)
  in
  match find_cet e c with
  | Some (cs, ls) => (E, m, c, g, [::], ls)
  | None => let '(E', m', c', g', cs, lrs, csop) := mk_env_exp_nocet E s m c g e in
            (E', m', CCacheFlatten.add_cet e csop lrs c', g', cs, lrs)
  end
with
mk_env_bexp_fccache E s m c g e : env * vm * ccache * generator * seq cnf * literal :=
  (* = bit_blast_bexp_nocbt = *)
  let mk_env_bexp_nocbt E s m c g e : env * vm * ccache * generator * seq cnf * literal * seq cnf :=
      match e with
      | QFBV.Bfalse =>
        match find_hbt e c with
        | Some (cs, l) => (E, m, c, g, cs, l, cs)
        | None => (E, m, add_hbt e [::] lit_ff c, g, [::], lit_ff, [::])
        end
      | QFBV.Btrue =>
        match find_hbt e c with
        | Some (cs, l) => (E, m, c, g, cs, l, cs)
        | None => (E, m, add_hbt e [::] lit_tt c, g, [::], lit_tt, [::])
        end
      | QFBV.Bbinop op e1 e2 =>
        let '(E1, m1, c1, g1, cs1, ls1) := mk_env_exp_fccache E s m c g e1 in
        let '(E2, m2, c2, g2, cs2, ls2) := mk_env_exp_fccache E1 s m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (E2, m2, c2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None =>
          let '(Eop, gop, csop, lop) := mk_env_bbinop op E2 g2 ls1 ls2 in
          (Eop, m2, add_hbt e [:: csop] lop c2, gop,
           catrev cs1 (catrev cs2 [:: csop]), lop, [:: csop])
        end
      | QFBV.Blneg e1 =>
        let '(E1, m1, c1, g1, cs1, l1) := mk_env_bexp_fccache E s m c g e1 in
        match find_hbt e c1 with
        | Some (csop, lop) => (E1, m1, c1, g1, catrev cs1 csop, lop, csop)
        | None => let '(Eop, gop, csop, lop) := mk_env_lneg E1 g1 l1 in
                  (Eop, m1, add_hbt e [:: csop] lop c1, gop,
                   catrev cs1 [:: csop], lop, [:: csop])
        end
      | QFBV.Bconj e1 e2 =>
        let '(E1, m1, c1, g1, cs1, l1) := mk_env_bexp_fccache E s m c g e1 in
        let '(E2, m2, c2, g2, cs2, l2) := mk_env_bexp_fccache E1 s m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (E2, m2, c2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None => let '(Eop, gop, csop, lop) := mk_env_conj E2 g2 l1 l2 in
                  (Eop, m2, add_hbt e [:: csop] lop c2, gop,
                   catrev cs1 (catrev cs2 [:: csop]), lop, [:: csop])
        end
      | QFBV.Bdisj e1 e2 =>
        let '(E1, m1, c1, g1, cs1, l1) := mk_env_bexp_fccache E s m c g e1 in
        let '(E2, m2, c2, g2, cs2, l2) := mk_env_bexp_fccache E1 s m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (E2, m2, c2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None => let '(Eop, gop, csop, lop) := mk_env_disj E2 g2 l1 l2 in
                  (Eop, m2, add_hbt e [:: csop] lop c2, gop,
                   catrev cs1 (catrev cs2 [:: csop]), lop, [:: csop])
        end
      end
  (* = = *)
  in
  match find_cbt e c with
  | Some (cs, l) => (E, m, c, g, [::], l)
  | None => let '(E', m', c', g', cs, lr, csop) := mk_env_bexp_nocbt E s m c g e in
            (E', m', CCacheFlatten.add_cbt e csop lr c', g', cs, lr)
  end.

Ltac dcase_mk_env_ccache :=
  match goal with
  (**)
  | |- context f [SSAVM.find ?v ?m] =>
    let lrs := fresh in
    case: (SSAVM.find v m) => [lrs|]
  | |- context f [mk_env_exp_fccache ?E ?s ?m ?ec ?g ?e] =>
    let E' := fresh in
    let m' := fresh in
    let ec' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lrs := fresh in
    let H := fresh in
    dcase (mk_env_exp_fccache E s m ec g e) =>
    [[[[[[E' m'] ec'] g'] cs] lrs] H]
  | |- context f [mk_env_bexp_fccache ?E ?s ?m ?ec ?g ?e] =>
    let E' := fresh in
    let m' := fresh in
    let ec' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lr := fresh in
    let H := fresh in
    dcase (mk_env_bexp_fccache E s m ec g e) =>
    [[[[[[E' m'] ec'] g'] cs] lr] H]
  | |- context f [mk_env_exp_ccache ?m ?c ?s ?E ?g ?e] =>
    let m' := fresh in
    let c' := fresh in
    let E' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lrs := fresh in
    let H := fresh in
    dcase (mk_env_exp_ccache m c s E g e) =>
    [[[[[[m' c'] E'] g'] cs] lrs] H]
  | |- context f [mk_env_bexp_ccache ?m ?c ?s ?E ?g ?e] =>
    let m' := fresh in
    let c' := fresh in
    let E' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lr := fresh in
    let H := fresh in
    dcase (mk_env_bexp_ccache m c s E g e) =>
    [[[[[[m' c'] E'] g'] cs] lr] H]
  (**)
  | |- context f [mk_env_var ?E ?g ?ls ?v] =>
    let E' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lrs := fresh in
    let H := fresh in
    dcase (mk_env_var E g ls v) => [[[[E' g'] cs] lrs] H]
  | |- context f [mk_env_eunop ?op ?E ?g ?lrs] =>
    let E' := fresh in
    let g' := fresh in
    let cs' := fresh in
    let lrs' := fresh in
    let H := fresh in
    dcase (mk_env_eunop op E g lrs) => [[[[E' g'] cs'] lrs'] H]
  | |- context f [mk_env_ebinop ?op ?E ?g ?lrs1 ?lrs2] =>
    let E' := fresh in
    let g' := fresh in
    let cs' := fresh in
    let lrs' := fresh in
    let H := fresh in
    dcase (mk_env_ebinop op E g lrs1 lrs2) => [[[[E' g'] cs'] lrs'] H]
  | |- context f [mk_env_ite ?E ?g ?lr ?ls1 ?ls2] =>
    let E' := fresh in
    let g' := fresh in
    let cs' := fresh in
    let lr' := fresh in
    let H := fresh in
    dcase (mk_env_ite E g lr ls1 ls2) => [[[[E' g'] cs'] lr'] H]
  | |- context f [mk_env_bbinop ?op ?E ?g ?lrs1 ?lrs2] =>
    let E' := fresh in
    let g' := fresh in
    let cs' := fresh in
    let lr' := fresh in
    let H := fresh in
    dcase (mk_env_bbinop op E g lrs1 lrs2) => [[[[E' g'] cs'] lr'] H]
  end.

Ltac myauto ::=
  repeat
    match goal with
    | |- _ /\ _ => split
    | |- ?e = ?e => reflexivity
    | H : ?p |- ?p => assumption
    | |- (_, _, _, _, _, _) = (_, _, _, _, _, _) -> _ =>
      case=> ? ? ? ? ? ?; subst
    | |- (_, _, _, _, _) = (_, _, _, _, _) -> _ =>
      case=> ? ? ? ? ?; subst
    | H1 : ?e = Some _, H2 : ?e = None |- _ =>
      rewrite H1 in H2; discriminate
    (**)
    | Hs : is_true (SSATE.vsize ?v ?TE == size ?bs),
           Henv : mk_env_var ?iE ?ig ?bs ?v = (?oE, ?og, ?ocs, ?olrs),
                  Hbb : bit_blast_var ?TE ?ig ?v = _ |- _ =>
      let Hbb' := fresh in
      rewrite eq_sym in Hs;
      (move: (mk_env_var_is_bit_blast_var (eqP Hs) Henv) => Hbb');
      rewrite Hbb in Hbb'; case: Hbb' => ? ? ?; subst
    | H1 : find_het ?e ?c = Some (?cs1, ?lrs1),
      H2 : find_het ?e ?c = Some (?cs2, ?lrs2) |- _ =>
      rewrite H1 in H2; case: H2 => ? ?; subst
    | H1 : find_hbt ?e ?c = Some (?cs1, ?lr1),
      H2 : find_hbt ?e ?c = Some (?cs2, ?lr2) |- _ =>
      rewrite H1 in H2; case: H2 => ? ?; subst
    | H1 : bit_blast_exp_fccache ?E ?m ?c ?g ?e = (?m1, ?c1, ?g1, ?cs1, ?lrs1),
      H2 : bit_blast_exp_fccache ?E ?m ?c ?g ?e = (?m2, ?c2, ?g2, ?cs2, ?lrs2) |- _ =>
      rewrite H1 in H2; case: H2 => ? ? ? ? ?; subst
    | H1 : bit_blast_bexp_fccache ?E ?m ?c ?g ?e = (?m1, ?c1, ?g1, ?cs1, ?lr1),
      H2 : bit_blast_bexp_fccache ?E ?m ?c ?g ?e = (?m2, ?c2, ?g2, ?cs2, ?lr2) |- _ =>
      rewrite H1 in H2; case: H2 => ? ? ? ? ?; subst
    | H1 : mk_env_eunop ?op ?E ?g ?ls = _,
      H2 : bit_blast_eunop ?op ?g ?ls = _ |- _ =>
      let H := fresh in
      (move: (mk_env_eunop_is_bit_blast_eunop H1) => H); rewrite H2 in H;
      case: H => ? ? ?; subst
    | H1 : mk_env_ebinop ?op ?E ?g ?ls1 ?ls2 = _,
      H2 : bit_blast_ebinop ?op ?g ?ls1 ?ls2 = _ |- _ =>
      let H := fresh in
      (move: (mk_env_ebinop_is_bit_blast_ebinop H1) => H); rewrite H2 in H;
      case: H => ? ? ?; subst
    | H1 : mk_env_bbinop ?op ?E ?g ?ls1 ?ls2 = _,
      H2 : bit_blast_bbinop ?op ?g ?ls1 ?ls2 = _ |- _ =>
      let H := fresh in
      (move: (mk_env_bbinop_is_bit_blast_bbinop H1) => H); rewrite H2 in H;
      case: H => ? ? ?; subst
    | H1 : mk_env_ite ?E ?g ?lc ?ls1 ?ls2 = _,
      H2 : bit_blast_ite ?g ?lc ?ls1 ?ls2 = _ |- _ =>
      let H := fresh in
      (move: (mk_env_ite_is_bit_blast_ite H1) => H); rewrite H2 in H;
      case: H => ? ? ?; subst
    (* apply induction hypothesis *)
    | mk_env_exp_fccache_is_bit_blast_exp_fccache :
        (forall (e : QFBV.exp)
                (s : SSAStore.t)
                (TE : SSATE.env)
                (iE : env) (im : vm)
                (ic : ccache) (ig : generator)
                (oE : env) (om : vm)
                (oc : ccache) (og : generator)
                (ocs : seq cnf)
                (olrs : word),
            is_true (AdhereConform.conform_exp e s TE) ->
            is_true (QFBV.well_formed_exp e TE) ->
            mk_env_exp_fccache iE s im ic ig e =
            (oE, om, oc, og, ocs, olrs) ->
            bit_blast_exp_fccache TE im ic ig e =
            (om, oc, og, ocs, olrs)),
        Hco : is_true (AdhereConform.conform_exp ?e ?s ?TE),
        Hwf : is_true (QFBV.well_formed_exp ?e ?TE),
        Henv : mk_env_exp_fccache ?iE ?s ?im ?ic ?ig ?e = _ |- _ =>
      let H := fresh "H" in
      (move: (mk_env_exp_fccache_is_bit_blast_exp_fccache _ _ _ _ _ _ _ _ _ _ _ _ _
                                                          Hco Hwf Henv) => H);
      clear Henv
    | mk_env_bexp_fccache_is_bit_blast_bexp_fccache :
        (forall (e : QFBV.bexp)
                (s : SSAStore.t)
                (TE : SSATE.env)
                (iE : env) (im : vm)
                (ic : ccache) (ig : generator)
                (oE : env) (om : vm)
                (oc : ccache) (og : generator)
                (ocs : seq cnf)
                (olr : literal),
            is_true (AdhereConform.conform_bexp e s TE) ->
            is_true (QFBV.well_formed_bexp e TE) ->
            mk_env_bexp_fccache iE s im ic ig e =
            (oE, om, oc, og, ocs, olr) ->
            bit_blast_bexp_fccache TE im ic ig e =
            (om, oc, og, ocs, olr)),
        Hco : is_true (AdhereConform.conform_bexp ?e ?s ?TE),
        Hwf : is_true (QFBV.well_formed_bexp ?e ?TE),
        Henv : mk_env_bexp_fccache ?iE ?s ?im ?ic ?ig ?e = _ |- _ =>
      let H := fresh "H" in
      (move: (mk_env_bexp_fccache_is_bit_blast_bexp_fccache _ _ _ _ _ _ _ _ _ _ _ _ _
                                                            Hco Hwf Henv) => H);
      clear Henv
    | |- _ => dcase_bb_ccache || dcase_mk_env_ccache
    end.

Lemma mk_env_exp_fccache_is_bit_blast_exp_fccache
      e s TE iE im ic ig oE om oc og ocs olrs :
  AdhereConform.conform_exp e s TE ->
  QFBV.well_formed_exp e TE ->
  mk_env_exp_fccache iE s im ic ig e = (oE, om, oc, og, ocs, olrs) ->
  bit_blast_exp_fccache TE im ic ig e = (om, oc, og, ocs, olrs)
with
mk_env_bexp_fccache_is_bit_blast_bexp_fccache
      e s TE iE im ic ig oE om oc og ocs olr :
  AdhereConform.conform_bexp e s TE ->
  QFBV.well_formed_bexp e TE ->
  mk_env_bexp_fccache iE s im ic ig e = (oE, om, oc, og, ocs, olr) ->
  bit_blast_bexp_fccache TE im ic ig e = (om, oc, og, ocs, olr).
Proof.
  (* mk_env_exp_fccache_is_bit_blast_exp_fccache *)
  case: e => //=.
  - move=> v Hs Hm. by myauto.
  - move=> bs _ _. by myauto.
  - move=> op e Hco Hwf. by myauto.
  - move=> op e1 e2 /andP [Hco1 Hco2] /andP [/andP [/andP [Hwf1 Hwf2] Hwfs1] Hwfs2].
    by myauto.
  - move=> e1 e2 e3 /andP [/andP [Hco1 Hco2] Hco3] /andP [/andP [/andP [Hwf1 Hwf2] Hwf3] Hwfs].
    by myauto.
  (* mk_env_bexp_fccache_is_bit_blast_bexp_fccache *)
  case: e => //=.
  - move=> _ _. by myauto.
  - move=> _ _. by myauto.
  - move=> op e1 e2 /andP [Hco1 Hco2] /andP [/andP [Hwf1 Hwf2] Hwfs]. by myauto.
  - move=> e Hco Hwf. by myauto.
  - move=> e1 e2 /andP [Hco1 Hco2] /andP [Hwf1 Hwf2]. by myauto.
  - move=> e1 e2 /andP [Hco1 Hco2] /andP [Hwf1 Hwf2]. by myauto.
Qed.

Ltac dcase_mk_env_compcache :=
  match goal with
  | |- context f [CompCache.find_cet ?e ?c] =>
    let Hfe_cet := fresh in
    let cs := fresh in
    let lrs := fresh in
    dcase (CompCache.find_cet e c); case=> [[cs lrs]|] Hfe_cet
  | |- context f [CompCache.find_cbt ?e ?c] =>
    let Hfe_cbt := fresh in
    let cs := fresh in
    let lr := fresh in
    dcase (CompCache.find_cbt e c); case=> [[cs lr]|] Hfe_cbt
  | |- context f [CompCache.find_het ?e ?c] =>
    let Hfe_het := fresh in
    let cs := fresh in
    let lrs := fresh in
    dcase (CompCache.find_het e c); case=> [[cs lrs]|] Hfe_het
  | |- context f [CompCache.find_hbt ?e ?c] =>
    let Hfe_hbt := fresh in
    let cs := fresh in
    let lr := fresh in
    dcase (CompCache.find_hbt e c); case=> [[cs lr]|] Hfe_hbt
  end.

Ltac simpl_ccache_compatible_find :=
  match goal with
  | Hcc : ccache_compatible ?fc ?c,
    Hff : find_cet ?e ?fc = Some (?fcs, ?flrs),
    Hf : CompCache.find_cet ?e ?c = Some (?cs, ?lrs) |- _ =>
    let Heqs := fresh in
    let Heqn := fresh in
    let Hlrs := fresh in
    (move: (ccache_compatible_find_cet_some Hcc Hff Hf) => [Heqs [Heqn Hlrs]]); subst;
    clear Hff; clear Hf
  | Hcc : ccache_compatible ?fc ?c,
    Hff : find_cbt ?e ?fc = Some (?fcs, ?flrs),
    Hf : CompCache.find_cbt ?e ?c = Some (?cs, ?lrs) |- _ =>
    let Heqs := fresh in
    let Heqn := fresh in
    let Hlrs := fresh in
    (move: (ccache_compatible_find_cbt_some Hcc Hff Hf) => [Heqs [Heqn Hlrs]]); subst;
    clear Hff; clear Hf
  | Hcc : ccache_compatible ?fc ?c,
    Hff : find_het ?e ?fc = Some (?fcs, ?flrs),
    Hf : CompCache.find_het ?e ?c = Some (?cs, ?lrs) |- _ =>
    let Heqs := fresh in
    let Heqn := fresh in
    let Hlrs := fresh in
    (move: (ccache_compatible_find_het_some Hcc Hff Hf) => [Heqs [Heqn Hlrs]]); subst;
    clear Hff; clear Hf
  | Hcc : ccache_compatible ?fc ?c,
    Hff : find_hbt ?e ?fc = Some (?fcs, ?flrs),
    Hf : CompCache.find_hbt ?e ?c = Some (?cs, ?lrs) |- _ =>
    let Heqs := fresh in
    let Heqn := fresh in
    let Hlrs := fresh in
    (move: (ccache_compatible_find_hbt_some Hcc Hff Hf) => [Heqs [Heqn Hlrs]]); subst;
    clear Hff; clear Hf
  (**)
  | Hcc : ccache_compatible ?fc ?c,
    Hff : find_cet ?e ?fc = Some _,
    Hf : CompCache.find_cet ?e ?c = None |- _ =>
    (move/(ccache_compatible_find_cet_none _ Hcc): Hf => Hf);
    rewrite Hff in Hf; discriminate
  | Hcc : ccache_compatible ?fc ?c,
    Hff : find_cbt ?e ?fc = Some _,
    Hf : CompCache.find_cbt ?e ?c = None |- _ =>
    (move/(ccache_compatible_find_cbt_none _ Hcc): Hf => Hf);
    rewrite Hff in Hf; discriminate
  | Hcc : ccache_compatible ?fc ?c,
    Hff : find_het ?e ?fc = Some _,
    Hf : CompCache.find_het ?e ?c = None |- _ =>
    (move/(ccache_compatible_find_het_none _ Hcc): Hf => Hf);
    rewrite Hff in Hf; discriminate
  | Hcc : ccache_compatible ?fc ?c,
    Hff : find_hbt ?e ?fc = Some _,
    Hf : CompCache.find_hbt ?e ?c = None |- _ =>
    (move/(ccache_compatible_find_hbt_none _ Hcc): Hf => Hf);
    rewrite Hff in Hf; discriminate
  (**)
  | Hcc : ccache_compatible ?fc ?c,
    Hff : find_cet ?e ?fc = None,
    Hf : CompCache.find_cet ?e ?c = Some _ |- _ =>
    (move/(ccache_compatible_find_cet_none _ Hcc): Hff => Hff);
    rewrite Hf in Hff; discriminate
  | Hcc : ccache_compatible ?fc ?c,
    Hff : find_cbt ?e ?fc = None,
    Hf : CompCache.find_cbt ?e ?c = Some _ |- _ =>
    (move/(ccache_compatible_find_cbt_none _ Hcc): Hff => Hff);
    rewrite Hf in Hff; discriminate
  | Hcc : ccache_compatible ?fc ?c,
    Hff : find_het ?e ?fc = None,
    Hf : CompCache.find_het ?e ?c = Some _ |- _ =>
    (move/(ccache_compatible_find_het_none _ Hcc): Hff => Hff);
    rewrite Hf in Hff; discriminate
  | Hcc : ccache_compatible ?fc ?c,
    Hff : find_hbt ?e ?fc = None,
    Hf : CompCache.find_hbt ?e ?c = Some _ |- _ =>
    (move/(ccache_compatible_find_hbt_none _ Hcc): Hff => Hff);
    rewrite Hf in Hff; discriminate
  end.

Ltac myauto ::=
  repeat
    match goal with
    | |- _ /\ _ => split
    | |- ?e = ?e => reflexivity
    | H : ?p |- ?p => assumption
    | |- (_, _, _, _, _, _) = (_, _, _, _, _, _) -> _ =>
      case=> ? ? ? ? ? ?; subst
    | |- (_, _, _, _, _) = (_, _, _, _, _) -> _ =>
      case=> ? ? ? ? ?; subst
    | H1 : ?e = Some _, H2 : ?e = None |- _ =>
      rewrite H1 in H2; discriminate
    (* apply induction hypothesis *)
    | mk_env_exp_fccache_valid :
        (forall (iE : env) (s : SSAStore.t) (e : QFBV.exp)
                (im : vm) (ifc : ccache) (ic : CompCache.compcache)
                (ig : generator) (ofE oE : env) (ofm : vm)
                (ofc : ccache) (ofg : generator) (ofcs : seq cnf)
                (oflrs : word) (om : vm) (oc : CompCache.compcache)
                (og : generator) (ocs : cnf) (olrs : word),
            ccache_compatible ifc ic ->
            mk_env_exp_fccache iE s im ifc ig e =
            (ofE, ofm, ofc, ofg, ofcs, oflrs) ->
            mk_env_exp_ccache im ic s iE ig e = (om, oc, oE, og, ocs, olrs) ->
            ofE = oE /\
            ofm = om /\
            ccache_compatible ofc oc /\
            ofg = og /\
            cnf_eqsat (tflatten ofcs) ocs /\
            cnf_eqnew (tflatten ofcs) ocs /\ oflrs = olrs),
      Hcc : ccache_compatible ?ifc ?ic,
      Hv1 : mk_env_exp_fccache ?iE ?s ?im ?ifc ?ig ?e = _,
      Hv2 : mk_env_exp_ccache ?im ?ic ?s ?iE ?ig ?e = _ |- _ =>
      let H1 := fresh in
      let H2 := fresh in
      let H3 := fresh in
      let H4 := fresh in
      let H5 := fresh in
      let H6 := fresh in
      let H7 := fresh in
      (move: (mk_env_exp_fccache_valid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                       Hcc Hv1 Hv2));
      (move=> [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]);
      subst; clear Hv1 Hv2
    | mk_env_bexp_fccache_valid :
        (forall (iE : env) (s : SSAStore.t) (e : QFBV.bexp)
                (im : vm) (ifc : ccache) (ic : CompCache.compcache)
                (ig : generator) (ofE oE : env) (ofm : vm)
                (ofc : ccache) (ofg : generator) (ofcs : seq cnf)
                (oflr : literal) (om : vm) (oc : CompCache.compcache)
                (og : generator) (ocs : cnf) (olr : literal),
            ccache_compatible ifc ic ->
            mk_env_bexp_fccache iE s im ifc ig e =
            (ofE, ofm, ofc, ofg, ofcs, oflr) ->
            mk_env_bexp_ccache im ic s iE ig e = (om, oc, oE, og, ocs, olr) ->
            ofE = oE /\
            ofm = om /\
            ccache_compatible ofc oc /\
            ofg = og /\
            cnf_eqsat (tflatten ofcs) ocs /\
            cnf_eqnew (tflatten ofcs) ocs /\ oflr = olr),
      Hcc : ccache_compatible ?ifc ?ic,
      Hv1 : mk_env_bexp_fccache ?iE ?s ?im ?ifc ?ig ?e = _,
      Hv2 : mk_env_bexp_ccache ?im ?ic ?s ?iE ?ig ?e = _ |- _ =>
      let H1 := fresh in
      let H2 := fresh in
      let H3 := fresh in
      let H4 := fresh in
      let H5 := fresh in
      let H6 := fresh in
      let H7 := fresh in
      (move: (mk_env_bexp_fccache_valid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                        Hcc Hv1 Hv2));
      (move=> [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]);
      subst; clear Hv1 Hv2
    (**)
    | Hv1 : mk_env_var ?iE ?g ?bs ?v = _,
      Hv2 : mk_env_var ?iE ?g ?bs ?v = _ |- _ =>
      let H1 := fresh in
      let H2 := fresh in
      let H3 := fresh in
      let H4 := fresh in
      (rewrite Hv1 in Hv2); (case: Hv2 => ? ? ? ?; subst)
    | Hv1 : mk_env_eunop ?op ?iE ?g ?ls = _,
      Hv2 : mk_env_eunop ?op ?iE ?g ?ls = _ |- _ =>
      let H1 := fresh in
      let H2 := fresh in
      let H3 := fresh in
      let H4 := fresh in
      (rewrite Hv1 in Hv2); (case: Hv2 => ? ? ? ?; subst)
    | Hv1 : mk_env_ebinop ?op ?iE ?g ?ls1 ?ls2 = _,
      Hv2 : mk_env_ebinop ?op ?iE ?g ?ls1 ?ls2 = _ |- _ =>
      let H1 := fresh in
      let H2 := fresh in
      let H3 := fresh in
      let H4 := fresh in
      (rewrite Hv1 in Hv2); (case: Hv2 => ? ? ? ?; subst)
    | Hv1 : mk_env_bbinop ?op ?iE ?g ?ls1 ?ls2 = _,
      Hv2 : mk_env_bbinop ?op ?iE ?g ?ls1 ?ls2 = _ |- _ =>
      let H1 := fresh in
      let H2 := fresh in
      let H3 := fresh in
      let H4 := fresh in
      (rewrite Hv1 in Hv2); (case: Hv2 => ? ? ? ?; subst)
    | Hv1 : mk_env_ite ?iE ?g ?l ?ls1 ?ls2 = _,
      Hv2 : mk_env_ite ?iE ?g ?l ?ls1 ?ls2 = _ |- _ =>
      let H1 := fresh in
      let H2 := fresh in
      let H3 := fresh in
      let H4 := fresh in
      (rewrite Hv1 in Hv2); (case: Hv2 => ? ? ? ?; subst)
    (**)
    | |- _ => dcase_bb_ccache || dcase_mk_env_compcache || dcase_mk_env_ccache
              || simpl_ccache_compatible || simpl_ccache_compatible_find || solve_eqnew
    end.

Lemma mk_env_exp_fccache_valid
      iE s e im ifc ic ig ofE oE ofm ofc ofg ofcs oflrs om oc og ocs olrs :
  ccache_compatible ifc ic ->
  mk_env_exp_fccache iE s im ifc ig e = (ofE, ofm, ofc, ofg, ofcs, oflrs) ->
  mk_env_exp_ccache im ic s iE ig e = (om, oc, oE, og, ocs, olrs) ->
  ofE = oE
  /\ ofm = om
  /\ ccache_compatible ofc oc
  /\ ofg = og
  /\ cnf_eqsat (tflatten ofcs) ocs
  /\ cnf_eqnew (tflatten ofcs) ocs
  /\ oflrs = olrs
with
mk_env_bexp_fccache_valid
  iE s e im ifc ic ig ofE oE ofm ofc ofg ofcs oflr om oc og ocs olr :
  ccache_compatible ifc ic ->
  mk_env_bexp_fccache iE s im ifc ig e = (ofE, ofm, ofc, ofg, ofcs, oflr) ->
  mk_env_bexp_ccache im ic s iE ig e = (om, oc, oE, og, ocs, olr) ->
  ofE = oE
  /\ ofm = om
  /\ ccache_compatible ofc oc
  /\ ofg = og
  /\ cnf_eqsat (tflatten ofcs) ocs
  /\ cnf_eqnew (tflatten ofcs) ocs
  /\ oflr = olr.
Proof.
  (* mk_env_exp_fccache_valid *)
  move=> Hcc. case: e => /=.
  - move=> v. by myauto.
  - move=> bs. by myauto.
  - move=> op e. by myauto.
  - move=> op e1 e2. by myauto.
  - move=> e1 e2 e3. by myauto.
  (* mk_env_bexp_fccache_valid *)
  move=> Hcc. case: e => /=.
  - by myauto.
  - by myauto.
  - move=> op e1 e2. by myauto.
  - move=> e. by myauto.
  - move=> e1 e2. by myauto.
  - move=> e1 e2. by myauto.
Qed.
