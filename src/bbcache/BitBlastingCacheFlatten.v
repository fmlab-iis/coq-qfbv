From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics Seqs.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
From BBCache Require Import BitBlastingInit CacheFlatten BitBlastingCCacheExport BitBlastingCacheExport.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ==== bit_blast_exp_fcache and bit_blast_bexp_fcache ==== *)

Fixpoint bit_blast_exp_fcache E m c g e : vm * cache * generator * seq cnf * word :=
  (* = bit_blast_exp_nocet = *)
  let bit_blast_exp_nocet E m c g e : vm * cache * generator * seq cnf * word :=
      match e with
      | QFBV.Evar v =>
        match find_het e c with
        | Some (cs, ls) => (m, c, g, cs, ls)
        | None => match SSAVM.find v m with
                  | None => let '(g', cs, rs) := bit_blast_var E g v in
                            (SSAVM.add v rs m, add_het e [:: cs] rs c, g', [:: cs], rs)
                  | Some rs => (m, add_het e [::] rs c, g, [::], rs)
                  end
        end
      | QFBV.Econst bs =>
        match find_het e c with
        | Some (cs, ls) => (m, c, g, cs, ls)
        | None => let '(g', cs, rs) := bit_blast_const g bs in
                  (m, add_het e [:: cs] rs c, g', [:: cs], rs)
        end
      | QFBV.Eunop op e1 =>
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_fcache E m c g e1 in
        match find_het e c1 with
        | Some (csop, lsop) => (m1, c1, g1, catrev cs1 csop, lsop)
        | None =>
          let '(gop, csop, lsop) := bit_blast_eunop op g1 ls1 in
          (m1, add_het e [:: csop] lsop c1, gop,
           catrev cs1 [:: csop], lsop)
        end
      | QFBV.Ebinop op e1 e2 =>
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_fcache E m c g e1 in
        let '(m2, c2, g2, cs2, ls2) := bit_blast_exp_fcache E m1 c1 g1 e2 in
        match find_het e c2 with
        | Some (csop, lsop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lsop)
        | None =>
          let '(gop, csop, lsop) := bit_blast_ebinop op g2 ls1 ls2 in
          (m2, add_het e [:: csop] lsop c2, gop,
           catrev cs1 (catrev cs2 [:: csop]), lsop)
        end
      | QFBV.Eite b e1 e2 =>
        let '(mb, cb, gb, csb, lb) := bit_blast_bexp_fcache E m c g b in
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_fcache E mb cb gb e1 in
        let '(m2, c2, g2, cs2, ls2) := bit_blast_exp_fcache E m1 c1 g1 e2 in
        match find_het e c2 with
        | Some (csop, lsop) =>
          (m2, c2, g2, catrev csb (catrev cs1 (catrev cs2 csop)), lsop)
        | None =>
          let '(gop, csop, lsop) := bit_blast_ite g2 lb ls1 ls2 in
          (m2, add_het e [:: csop] lsop c2, gop,
           catrev csb (catrev cs1 (catrev cs2 [:: csop])), lsop)
        end
      end
  (* = = *)
  in
  match find_cet e c with
  | Some ls => (m, c, g, [::], ls)
  | None => let '(m', c', g', cs, lrs) := bit_blast_exp_nocet E m c g e in
            (m', add_cet e lrs c', g', cs, lrs)
  end
with
bit_blast_bexp_fcache E m c g e : vm * cache * generator * seq cnf * literal :=
  (* = bit_blast_bexp_nocbt = *)
  let bit_blast_bexp_nocbt E m c g e : vm * cache * generator * seq cnf * literal :=
      match e with
      | QFBV.Bfalse =>
        match find_hbt e c with
        | Some (cs, l) => (m, c, g, cs, l)
        | None => (m, add_hbt e [::] lit_ff c, g, [::], lit_ff)
        end
      | QFBV.Btrue =>
        match find_hbt e c with
        | Some (cs, l) => (m, c, g, cs, l)
        | None => (m, add_hbt e [::] lit_tt c, g, [::], lit_tt)
        end
      | QFBV.Bbinop op e1 e2 =>
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_fcache E m c g e1 in
        let '(m2, c2, g2, cs2, ls2) := bit_blast_exp_fcache E m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lop)
        | None =>
          let '(gop, csop, lop) := bit_blast_bbinop op g2 ls1 ls2 in
          (m2, add_hbt e [:: csop] lop c2, gop,
           catrev cs1 (catrev cs2 [:: csop]), lop)
        end
      | QFBV.Blneg e1 =>
        let '(m1, c1, g1, cs1, l1) := bit_blast_bexp_fcache E m c g e1 in
        match find_hbt e c1 with
        | Some (csop, lop) => (m1, c1, g1, catrev cs1 csop, lop)
        | None => let '(gop, csop, lop) := bit_blast_lneg g1 l1 in
                  (m1, add_hbt e [:: csop] lop c1, gop,
                   catrev cs1 [:: csop], lop)
        end
      | QFBV.Bconj e1 e2 =>
        let '(m1, c1, g1, cs1, l1) := bit_blast_bexp_fcache E m c g e1 in
        let '(m2, c2, g2, cs2, l2) := bit_blast_bexp_fcache E m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lop)
        | None => let '(gop, csop, lop) := bit_blast_conj g2 l1 l2 in
                  (m2, add_hbt e [:: csop] lop c2, gop,
                   catrev cs1 (catrev cs2 [:: csop]), lop)
        end
      | QFBV.Bdisj e1 e2 =>
        let '(m1, c1, g1, cs1, l1) := bit_blast_bexp_fcache E m c g e1 in
        let '(m2, c2, g2, cs2, l2) := bit_blast_bexp_fcache E m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lop)
        | None => let '(gop, csop, lop) := bit_blast_disj g2 l1 l2 in
                  (m2, add_hbt e [:: csop] lop c2, gop,
                   catrev cs1 (catrev cs2 [:: csop]), lop)
        end
      end
  (* = = *)
  in
  match find_cbt e c with
  | Some l => (m, c, g, [::], l)
  | None => let '(m', c', g', cs, lr) := bit_blast_bexp_nocbt E m c g e in
            (m', add_cbt e lr c', g', cs, lr)
  end.



(* ==== basic case ==== *)

(* = bit-blasting only one bexp = *)

Definition init_fcache : cache := CacheFlatten.empty.

Lemma init_fcache_compatible : cache_compatible init_fcache init_cache.
Proof. done. Qed.

Ltac myauto :=
  repeat
    match goal with
    | |- _ /\ _ => split
    | |- ?e = ?e => reflexivity
    | |- cache_compatible (add_cet ?e ?lrs _) (Cache.add_cet ?e ?lrs _) =>
      apply: cache_compatible_add_cet
    | |- cache_compatible (add_cbt ?e ?lr _) (Cache.add_cbt ?e ?lr _) =>
      apply: cache_compatible_add_cbt
    | |- cache_compatible (add_het ?e ?ecs ?lrs _) (Cache.add_het ?e ?cs ?lrs _) =>
      apply: cache_compatible_add_het
    | |- cache_compatible (add_hbt ?e ?ecs ?lrs _) (Cache.add_hbt ?e ?cs ?lrs _) =>
      apply: cache_compatible_add_hbt
    | H : ?p |- ?p => assumption
    | |- cnf_eqsat (tflatten [:: ?cs]) ?cs => exact: tflatten_singleton_eqsat
    | |- cnf_eqsat (tflatten (catrev _ _)) ?cs => apply: tflatten_catrev_eqsat
    | |- cnf_eqsat (tflatten [::]) [::] => done
    | |- (_, _, _, _, _) = (_, _, _, _, _) -> _ =>
      case=> ? ? ? ? ?; subst
    (**)
    | Hc : cache_compatible ?ec ?c,
      H : find_cet ?e ?ec = _ |- context f [Cache.find_cet ?e ?c] =>
      rewrite (cache_compatible_find_cet _ Hc) in H; rewrite H
    | Hc : cache_compatible ?ec ?c,
      H : find_cbt ?e ?ec = _ |- context f [Cache.find_cbt ?e ?c] =>
      rewrite (cache_compatible_find_cbt _ Hc) in H; rewrite H
    | Hc : cache_compatible ?ec ?c,
      H : find_het ?e ?ec = None |- context f [Cache.find_het ?e ?c] =>
      move/(cache_compatible_find_het_none _ Hc): H => H; rewrite H
    | Hc : cache_compatible ?ec ?c,
      H : find_hbt ?e ?ec = None |- context f [Cache.find_hbt ?e ?c] =>
      move/(cache_compatible_find_hbt_none _ Hc): H => H; rewrite H
    | Hc : cache_compatible ?ec ?c,
      H : find_het ?e ?ec = Some _ |- context f [Cache.find_het ?e ?c] =>
      let cs := fresh in
      let Hf_het := fresh in
      let Heqs := fresh in
      move: (cache_compatible_find_het_some_exists1 Hc H) =>
      [cs [Hf_het Heqs]]; rewrite Hf_het
    | Hc : cache_compatible ?ec ?c,
      H : find_hbt ?e ?ec = Some _ |- context f [Cache.find_hbt ?e ?c] =>
      let cs := fresh in
      let Hf_hbt := fresh in
      let Heqs := fresh in
      move: (cache_compatible_find_hbt_some_exists1 Hc H) =>
      [cs [Hf_hbt Heqs]]; rewrite Hf_hbt
    | |- context f [find_cet ?e ?c] =>
      let Hfe_cet := fresh in
      let lrs := fresh in
      dcase (find_cet e c); case=> [lrs|] Hfe_cet
    | |- context f [find_cbt ?e ?c] =>
      let Hfe_cbt := fresh in
      let lr := fresh in
      dcase (find_cbt e c); case=> [lr|] Hfe_cbt
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
    | |- context f [bit_blast_exp_fcache ?E ?m ?ec ?g ?e] =>
      let m' := fresh in
      let ec' := fresh in
      let g' := fresh in
      let cs := fresh in
      let lrs := fresh in
      let H := fresh in
      dcase (bit_blast_exp_fcache E m ec g e) =>
      [[[[[m' ec'] g'] cs] lrs] H]
    | |- context f [bit_blast_bexp_fcache ?E ?m ?ec ?g ?e] =>
      let m' := fresh in
      let ec' := fresh in
      let g' := fresh in
      let cs := fresh in
      let lr := fresh in
      let H := fresh in
      dcase (bit_blast_bexp_fcache E m ec g e) =>
      [[[[[m' ec'] g'] cs] lr] H]
    | |- context f [bit_blast_exp_cache ?E ?m ?c ?g ?e] =>
      let m' := fresh in
      let c' := fresh in
      let g' := fresh in
      let cs := fresh in
      let lrs := fresh in
      let H := fresh in
      dcase (bit_blast_exp_cache E m c g e) =>
      [[[[[m' c'] g'] cs] lrs] H]
    | |- context f [bit_blast_bexp_cache ?E ?m ?c ?g ?e] =>
      let m' := fresh in
      let c' := fresh in
      let g' := fresh in
      let cs := fresh in
      let lr := fresh in
      let H := fresh in
      dcase (bit_blast_bexp_cache E m c g e) =>
      [[[[[m' c'] g'] cs] lr] H]
    | bit_blast_exp_fcache_valid :
        (forall (E : SSATE.env)
               (e : QFBV.exp) (im : vm)
               (iec : cache) (ic : Cache.cache)
               (ig : generator) (em : vm)
               (ec : cache) (eg : generator)
               (ecs : seq cnf) (elrs : word)
               (m : vm) (c : Cache.cache)
               (g : generator) (cs : cnf)
               (lrs : word),
            cache_compatible iec ic ->
            bit_blast_exp_fcache E im iec ig e = (em, ec, eg, ecs, elrs) ->
            bit_blast_exp_cache E im ic ig e =
            (m, c, g, cs, lrs) ->
            em = m /\
            cache_compatible ec c /\
            eg = g /\ cnf_eqsat (tflatten ecs) cs /\ elrs = lrs),
      Hcc : cache_compatible ?iec ?ic,
      Hbbe : bit_blast_exp_fcache ?E ?im ?iec ?ig ?e = _,
      Hbb : bit_blast_exp_cache ?E ?im ?ic ?ig ?e = _ |- _ =>
      let Hm := fresh in
      let Hc := fresh in
      let Hg := fresh in
      let Hcs := fresh in
      let Hlrs:= fresh in
      move: (bit_blast_exp_fcache_valid
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcc Hbbe Hbb);
      move=> [Hm [Hc [Hg [Hcs Hlrs]]]]; subst; clear Hbbe Hbb
    | bit_blast_bexp_fcache_valid :
        (forall (E : SSATE.env)
                (e : QFBV.bexp) (im : vm)
                (iec : cache) (ic : Cache.cache)
                (ig : generator) (em : vm)
                (ec : cache) (eg : generator)
                (ecs : seq cnf) (elr : literal)
                (m : vm) (c : Cache.cache)
                (g : generator) (cs : cnf)
                (lr : literal),
            cache_compatible iec ic ->
            bit_blast_bexp_fcache E im iec ig e = (em, ec, eg, ecs, elr) ->
            bit_blast_bexp_cache E im ic ig e = (m, c, g, cs, lr) ->
            em = m /\
            cache_compatible ec c /\
            eg = g /\ cnf_eqsat (tflatten ecs) cs /\ elr = lr),
      Hcc : cache_compatible ?iec ?ic,
      Hbbe : bit_blast_bexp_fcache ?E ?im ?iec ?ig ?e = _,
      Hbb : bit_blast_bexp_cache ?E ?im ?ic ?ig ?e = _ |- _ =>
      let Hm := fresh in
      let Hc := fresh in
      let Hg := fresh in
      let Hcs := fresh in
      let Hlr:= fresh in
      move: (bit_blast_bexp_fcache_valid
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcc Hbbe Hbb);
      move=> [Hm [Hc [Hg [Hcs Hlr]]]]; subst; clear Hbbe Hbb
    (**)
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

Lemma bit_blast_exp_fcache_valid
      E e im iec ic ig em ec eg ecs elrs m c g cs lrs :
  cache_compatible iec ic ->
  bit_blast_exp_fcache E im iec ig e = (em, ec, eg, ecs, elrs) ->
  bit_blast_exp_cache E im ic ig e = (m, c, g, cs, lrs) ->
  em = m
  /\ cache_compatible ec c
  /\ eg = g
  /\ cnf_eqsat (tflatten ecs) cs
  /\ elrs = lrs
with
bit_blast_bexp_fcache_valid E e im iec ic ig em ec eg ecs elr m c g cs lr :
  cache_compatible iec ic ->
  bit_blast_bexp_fcache E im iec ig e = (em, ec, eg, ecs, elr) ->
  bit_blast_bexp_cache E im ic ig e = (m, c, g, cs, lr) ->
  em = m
  /\ cache_compatible ec c
  /\ eg = g
  /\ cnf_eqsat (tflatten ecs) cs
  /\ elr = lr.
Proof.
  (* bit_blast_exp_fcache_valid *)
  move=> Hcc. case: e => /=.
  - move=> v. by myauto.
  - move=> bs. by myauto.
  - move=> op e. by myauto.
  - move=> op e1 e2. by myauto.
  - move=> e1 e2 e3. by myauto.
  (* bit_blast_bexp_fcache_valid *)
  move=> Hcc. case: e => /=.
  - by myauto.
  - by myauto.
  - move=> op e1 e2. by myauto.
  - move=> e. by myauto.
  - move=> e1 e2. by myauto.
  - move=> e1 e2. by myauto.
Qed.


Theorem bit_blast_bexp_fcache_sound E e m c g cs lr :
  bit_blast_bexp_fcache
    E init_vm init_fcache init_gen e = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexp e E ->
  ~ (sat (add_prelude ([::neg_lit lr]::(tflatten cs)))) ->
  (forall s, AdhereConform.conform_bexp e s E ->
             QFBV.eval_bexp e s).
Proof.
  move=> Hbbe Hwf Hsat.
  dcase (bit_blast_bexp_cache E init_vm init_cache init_gen e) =>
  [[[[[m' c'] g'] cs'] lr'] Hbb].
  move: (bit_blast_bexp_fcache_valid
           (init_fcache_compatible) Hbbe Hbb) => [Hm [Hcc [Hg [Heqs Hlr]]]]; subst.
  apply: (bit_blast_cache_sound Hbb Hwf). move=> Hs. apply: Hsat.
  move: (cnf_eqsat_cons (clause_eqsat_refl [:: neg_lit lr']) Heqs) => Heqs'.
  apply/(cnf_eqsat_add_prelude_sat Heqs'). assumption.
Qed.

Theorem bit_blast_bexp_fcache_complete E e m c g cs lr :
  bit_blast_bexp_fcache E init_vm init_fcache init_gen e = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexp e E ->
  (forall s, AdhereConform.conform_bexp e s E ->
             QFBV.eval_bexp e s) ->
  ~ (sat (add_prelude ([::neg_lit lr]::(tflatten cs)))).
Proof.
  move=> Hbbe Hwf Hev.
  dcase (bit_blast_bexp_cache E init_vm init_cache init_gen e) =>
  [[[[[m' c'] g'] cs'] lr'] Hbb].
  move: (bit_blast_bexp_fcache_valid
           (init_fcache_compatible) Hbbe Hbb) => [Hm [Hcc [Hg [Heqs Hlr]]]]; subst.
  move=> Hs. move: (cnf_eqsat_cons (clause_eqsat_refl [:: neg_lit lr']) Heqs) => Heqs'.
  move/(cnf_eqsat_add_prelude_sat Heqs'): Hs => {Heqs'}.
  exact: (bit_blast_cache_complete Hbb Hwf Hev).
Qed.


Theorem bit_blast_bexp_fcache_sat_sound E e m c g cs lr :
  bit_blast_bexp_fcache
    E init_vm init_fcache init_gen e = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexp e E ->
  (sat (add_prelude ([::lr]::(tflatten cs)))) ->
  (exists s, AdhereConform.conform_bexp e s E /\
             QFBV.eval_bexp e s).
Proof.
  move=> Hbbe Hwf Hsat.
  dcase (bit_blast_bexp_cache E init_vm init_cache init_gen e) =>
  [[[[[m' c'] g'] cs'] lr'] Hbb].
  move: (bit_blast_bexp_fcache_valid
           (init_fcache_compatible) Hbbe Hbb) => [Hm [Hcc [Hg [Heqs Hlr]]]]; subst.
  apply: (bit_blast_cache_sat_sound Hbb Hwf).
  move: (cnf_eqsat_cons (clause_eqsat_refl [:: lr']) Heqs) => Heqs'.
  apply/(cnf_eqsat_add_prelude_sat Heqs'). assumption.
Qed.

Theorem bit_blast_bexp_fcache_sat_complete E e m c g cs lr :
  bit_blast_bexp_fcache E init_vm init_fcache init_gen e = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexp e E ->
  (exists s, AdhereConform.conform_bexp e s E /\
             QFBV.eval_bexp e s) ->
  (sat (add_prelude ([::lr]::(tflatten cs)))).
Proof.
  move=> Hbbe Hwf Hev.
  dcase (bit_blast_bexp_cache E init_vm init_cache init_gen e) =>
  [[[[[m' c'] g'] cs'] lr'] Hbb].
  move: (bit_blast_bexp_fcache_valid
           (init_fcache_compatible) Hbbe Hbb) => [Hm [Hcc [Hg [Heqs Hlr]]]]; subst.
  move: (cnf_eqsat_cons (clause_eqsat_refl [:: lr']) Heqs) => Heqs'.
  apply/(cnf_eqsat_add_prelude_sat Heqs').
  exact: (bit_blast_cache_sat_complete Hbb Hwf Hev).
Qed.


(* ==== general case ==== *)

(* = bit-blasting multiple bexps = *)

Definition bit_blast_bexp_fcache_tflatten E m c g e :=
  let '(m', c', g', css', lr') := bit_blast_bexp_fcache E m c g e in
  (m', c', g', tflatten css', lr').

Fixpoint bit_blast_bexps_fcache E (es : seq QFBV.bexp) :=
  match es with
  | [::] => (init_vm, init_fcache, init_gen, add_prelude [::], lit_tt)
  | e :: es' =>
    let '(m, c, g, cs, lr) := bit_blast_bexps_fcache E es' in
    bit_blast_bexp_fcache_tflatten E m (CacheFlatten.reset_ct c) g e
  end.

Lemma bit_blast_bexps_fcache_valid E es m c g cs lr m' c' g' cs' lr' :
  bit_blast_bexps_fcache E es = (m, c, g, cs, lr) ->
  bit_blast_bexps_cache E es = (m', c', g', cs', lr') ->
  m = m' /\ cache_compatible c c' /\ g = g' /\ cnf_eqsat cs cs' /\ lr = lr'.
Proof.
  elim: es m c g cs lr m' c' g' cs' lr' => [| e es IH] m c g cs lr m' c' g' cs' lr' /=.
  - move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
  - dcase (bit_blast_bexps_fcache E es) => [[[[[m1 c1] g1] cs1] lr1] Hbbe1].
    move=> Hbbe2.
    dcase (bit_blast_bexps_cache E es) => [[[[[m1' c1'] g1'] cs1'] lr1'] Hbb1].
    move=> Hbb2. move: (IH _ _ _ _ _ _ _ _ _ _ Hbbe1 Hbb1).
    move=> [Hn [Hc [Hg [Heqs Hlr]]]]; subst.
    move: Hbbe2. rewrite /bit_blast_bexp_fcache_tflatten.
    dcase (bit_blast_bexp_fcache E m1' (reset_ct c1) g1' e) =>
    [[[[[m'' c''] g''] cs''] lrs''] Hbbe1']. case=> ? ? ? ? ?; subst.
    exact: (bit_blast_bexp_fcache_valid (cache_compatible_reset_ct Hc)
                                           Hbbe1' Hbb2).
Qed.



Theorem bit_blast_bexps_fcache_sound e es E m c g cs lr :
  bit_blast_bexps_fcache E (e::es) = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexps (e::es) E ->
  ~ (sat (add_prelude ([::neg_lit lr]::cs))) ->
  (forall s, AdhereConform.conform_bexps (e::es) s E ->
             QFBV.eval_bexp e s).
Proof.
  move=> Hbbe Hwf Hsat.
  dcase (bit_blast_bexps_cache E (e::es)) => [[[[[m' c'] g'] cs'] lr'] Hbb].
  move: (bit_blast_bexps_fcache_valid Hbbe Hbb).
  move=> [Hm [Hc [Hg [Heqs Hlr]]]]; subst.
  have Hsat': ~ sat (add_prelude ([:: neg_lit lr'] :: cs')).
  { move=> H. apply: Hsat.
    move: (cnf_eqsat_cons (clause_eqsat_refl [:: neg_lit lr']) Heqs) => Heqs'.
    apply/(cnf_eqsat_add_prelude_sat Heqs'). assumption. }
  exact: (bit_blast_cache_sound_general Hbb Hwf Hsat').
Qed.

Theorem bit_blast_bexps_fcache_complete e es E m c g cs lr :
  bit_blast_bexps_fcache E (e::es) = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexps (e::es) E ->
  (forall s, AdhereConform.conform_bexps (e::es) s E ->
             QFBV.eval_bexp e s) ->
  ~ (sat (add_prelude ([::neg_lit lr]::cs))).
Proof.
  move=> Hbbe Hwf Hev Hsat.
  dcase (bit_blast_bexps_cache E (e::es)) => [[[[[m' c'] g'] cs'] lr'] Hbb].
  move: (bit_blast_bexps_fcache_valid Hbbe Hbb).
  move=> [Hm [Hc [Hg [Heqs Hlr]]]]; subst.
  have Hsat': sat (add_prelude ([:: neg_lit lr'] :: cs')).
  { move: (cnf_eqsat_cons (clause_eqsat_refl [:: neg_lit lr']) Heqs) => Heqs'.
    apply/(cnf_eqsat_add_prelude_sat Heqs'). assumption. }
  move: Hsat'. exact: (bit_blast_cache_complete_general Hbb Hwf Hev).
Qed.

Definition bexp_to_cnf_fcache E m c g e :=
  let '(m', c', g', cs, lr) := bit_blast_bexp_fcache_tflatten E m c g e in
  (m', c', g', add_prelude ([::neg_lit lr]::cs)).
