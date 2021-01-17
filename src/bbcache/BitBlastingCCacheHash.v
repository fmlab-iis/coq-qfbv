From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics Seqs.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
From BitBlasting Require Import AdhereConform.
From BBCache Require Import BitBlastingInit.
From BBCache Require Import BitBlastingCCacheExport BitBlastingCacheExport.
From BBCache Require Import BitBlastingCCacheFlatten.
From BBCache Require Import CCacheFlatten CCacheHash QFBVHash.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma mk_state_preserve_eval_exp E m1 m2 e :
  bound_exp e m1 ->
  vm_preserve m1 m2 ->
  QFBV.eval_exp e (mk_state E m1) = QFBV.eval_exp e (mk_state E m2)
with
mk_state_preserve_eval_bexp E m1 m2 e :
  bound_bexp e m1 ->
  vm_preserve m1 m2 ->
  QFBV.eval_bexp e (mk_state E m1) = QFBV.eval_bexp e (mk_state E m2).
Proof.
  (* mk_state_preserve_eval_exp *)
  case: e => //=.
  - move=> s Hmem Hpre. move: (SSAVM.Lemmas.mem_find_some Hmem) => [ls Hfind1].
    move: (Hpre _ _ Hfind1) => Hfind2.
    rewrite (mk_state_find E Hfind1) (mk_state_find E Hfind2). reflexivity.
  - move=> op e Hbound1 Hpre.
    rewrite (mk_state_preserve_eval_exp _ _ _ _ Hbound1 Hpre). reflexivity.
  - move=> op e1 e2 /andP [Hbound1 Hbound2] Hpre.
    rewrite (mk_state_preserve_eval_exp _ _ _ _ Hbound1 Hpre)
            (mk_state_preserve_eval_exp _ _ _ _ Hbound2 Hpre). reflexivity.
  - move=> e1 e2 e3 /andP [/andP [Hbound1 Hbound2] Hbound3] Hpre.
    rewrite (mk_state_preserve_eval_bexp _ _ _ _ Hbound1 Hpre)
            (mk_state_preserve_eval_exp _ _ _ _ Hbound2 Hpre)
            (mk_state_preserve_eval_exp _ _ _ _ Hbound3 Hpre). reflexivity.
  (* mk_state_preserve_eval_bexp *)
  case: e => //=.
  - move=> op e1 e2 /andP [Hbound1 Hbound2] Hpre.
    rewrite (mk_state_preserve_eval_exp _ _ _ _ Hbound1 Hpre)
            (mk_state_preserve_eval_exp _ _ _ _ Hbound2 Hpre). reflexivity.
  - move=> e Hbound1 Hpre.
    rewrite (mk_state_preserve_eval_bexp _ _ _ _ Hbound1 Hpre). reflexivity.
  - move=> e1 e2 /andP [Hbound1 Hbound2] Hpre.
    rewrite (mk_state_preserve_eval_bexp _ _ _ _ Hbound1 Hpre)
            (mk_state_preserve_eval_bexp _ _ _ _ Hbound2 Hpre). reflexivity.
  - move=> e1 e2 /andP [Hbound1 Hbound2] Hpre.
    rewrite (mk_state_preserve_eval_bexp _ _ _ _ Hbound1 Hpre)
            (mk_state_preserve_eval_bexp _ _ _ _ Hbound2 Hpre). reflexivity.
Qed.

Lemma bit_blast_exp_ccache_interp_cache_ct
      TE E e im ic ig om oc og ocs olrs :
  bit_blast_exp_ccache TE im ic ig e = (om, oc, og, ocs, olrs) ->
  interp_cnf E ocs ->
  CompCache.interp_cache_ct E ic ->
  CompCache.interp_cache_ct E oc
with
bit_blast_bexp_ccache_interp_cache_ct
  TE E e im ic ig om oc og ocs olr :
  bit_blast_bexp_ccache TE im ic ig e = (om, oc, og, ocs, olr) ->
  interp_cnf E ocs ->
  CompCache.interp_cache_ct E ic ->
  CompCache.interp_cache_ct E oc.
Proof.
  (* bit_blast_exp_ccache_interp_cache_ct *)
  case: e => //=.
  - move=> v. case: (CompCache.find_cet (QFBV.Evar v) ic).
    + move=> [cs lrs]. case=> ? ? ? ? ?; subst. move=> _. by apply.
    + case: (CompCache.find_het (QFBV.Evar v) ic).
      * move=> [cs lrs]. case=> ? ? ? ? ?; subst. move=> Hcs Hic.
        exact: (CompCache.interp_cache_ct_add_cet _ _ Hic Hcs).
      * case: (SSAVM.find v im).
        -- move=> lrs. case=> ? ? ? ? ?; subst. move=> _ Hic.
           exact: (CompCache.interp_cache_ct_add_cet _ _ Hic).
        -- dcase (bit_blast_var TE ig v) => [[[g1 cs1] lrs1] Hbb1].
           case=> ? ? ? ? ?; subst. move=> Hcs Hic.
           exact: (CompCache.interp_cache_ct_add_cet _ _ Hic Hcs).
  - move=> bs. case: (CompCache.find_cet (QFBV.Econst bs) ic).
    + move=> [cs lrs]. case=> ? ? ? ? ?; subst. move=> _. by apply.
    + case: (CompCache.find_het (QFBV.Econst bs) ic).
      * move=> [cs lrs]. case=> ? ? ? ? ?; subst. move=> Hcs Hic.
        exact: (CompCache.interp_cache_ct_add_cet _ _ Hic Hcs).
      * case=> ? ? ? ? ?; subst. move=> _ Hic.
        exact: (CompCache.interp_cache_ct_add_cet _ _ Hic).
  - move=> op e. case: (CompCache.find_cet (QFBV.Eunop op e) ic).
    + move=> [cs lrs]. case=> ? ? ? ? ?; subst. move=> _. by apply.
    + dcase (bit_blast_exp_ccache TE im ic ig e) => [[[[[m1 c1] g1] cs1] lrs1] Hbb1].
      case: (CompCache.find_het (QFBV.Eunop op e) c1).
      * move=> [cs lrs]. case=> ? ? ? ? ?; subst. move=> Hcs Hic.
        rewrite interp_cnf_catrev in Hcs. move/andP: Hcs=> [Hcs1 Hcs].
        apply: (CompCache.interp_cache_ct_add_cet _ _ _ Hcs).
        exact: (bit_blast_exp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb1 Hcs1 Hic).
      * dcase (bit_blast_eunop op g1 lrs1) => [[[g2 cs2] lrs2] Hbb2].
        case=> ? ? ? ? ?; subst. move=> Hcs Hic.
        rewrite interp_cnf_catrev in Hcs. move/andP: Hcs => [Hcs1 Hcs2].
        apply: (CompCache.interp_cache_ct_add_cet _ _ _ Hcs2).
        apply (CompCache.interp_cache_ct_add_het).
        exact: (bit_blast_exp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb1 Hcs1 Hic).
  - move=> op e1 e2. case: (CompCache.find_cet (QFBV.Ebinop op e1 e2) ic).
    + move=> [cs lrs]. case=> ? ? ? ? ?; subst. move=> _. by apply.
    + dcase (bit_blast_exp_ccache TE im ic ig e1) => [[[[[m1 c1] g1] cs1] lrs1] Hbb1].
      dcase (bit_blast_exp_ccache TE m1 c1 g1 e2) => [[[[[m2 c2] g2] cs2] lrs2] Hbb2].
      case: (CompCache.find_het (QFBV.Ebinop op e1 e2) c2).
      * move=> [cs lrs]. case=> ? ? ? ? ?; subst. move=> Hcs Hic.
        rewrite !interp_cnf_catrev in Hcs. move/andP: Hcs => [Hcs1 /andP [Hcs2 Hcs]].
        apply: (CompCache.interp_cache_ct_add_cet _ _ _ Hcs).
        apply: (bit_blast_exp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb2 Hcs2).
        exact: (bit_blast_exp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb1 Hcs1 Hic).
      * dcase (bit_blast_ebinop op g2 lrs1 lrs2) => [[[g3 cs3] lrs3] Hbb3].
        case=> ? ? ? ? ?; subst. move=> Hcs Hic.
        rewrite !interp_cnf_catrev in Hcs. move/andP: Hcs => [Hcs1 /andP [Hcs2 Hcs3]].
        apply: (CompCache.interp_cache_ct_add_cet _ _ _ Hcs3).
        apply CompCache.interp_cache_ct_add_het.
        apply: (bit_blast_exp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb2 Hcs2).
        exact: (bit_blast_exp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb1 Hcs1 Hic).
  - move=> e1 e2 e3. case: (CompCache.find_cet (QFBV.Eite e1 e2 e3) ic).
    + move=> [cs lrs]. case=> ? ? ? ? ?; subst. move=> _. by apply.
    + dcase (bit_blast_bexp_ccache TE im ic ig e1) => [[[[[m1 c1] g1] cs1] lrs1] Hbb1].
      dcase (bit_blast_exp_ccache TE m1 c1 g1 e2) => [[[[[m2 c2] g2] cs2] lrs2] Hbb2].
      dcase (bit_blast_exp_ccache TE m2 c2 g2 e3) => [[[[[m3 c3] g3] cs3] lrs3] Hbb3].
      case: (CompCache.find_het (QFBV.Eite e1 e2 e3) c3).
      * move=> [cs lrs]. case=> ? ? ? ? ?; subst. move=> Hcs Hic.
        rewrite !interp_cnf_catrev in Hcs.
        move/andP: Hcs => [Hcs1 /andP [Hcs2 /andP [Hcs3 Hcs]]].
        apply: (CompCache.interp_cache_ct_add_cet _ _ _ Hcs).
        apply: (bit_blast_exp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb3 Hcs3).
        apply: (bit_blast_exp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb2 Hcs2).
        exact: (bit_blast_bexp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb1 Hcs1 Hic).
      * dcase (bit_blast_ite g3 lrs1 lrs2 lrs3) => [[[g4 cs4] lrs4] Hbb4].
        case=> ? ? ? ? ?; subst. move=> Hcs Hic.
        rewrite !interp_cnf_catrev in Hcs.
        move/andP: Hcs => [Hcs1 /andP [Hcs2 /andP [Hcs3 Hcs4]]].
        apply: (CompCache.interp_cache_ct_add_cet _ _ _ Hcs4).
        apply CompCache.interp_cache_ct_add_het.
        apply: (bit_blast_exp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb3 Hcs3).
        apply: (bit_blast_exp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb2 Hcs2).
        exact: (bit_blast_bexp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb1 Hcs1 Hic).
  (* bit_blast_bexp_ccache_interp_cache_ct *)
  case: e => //=.
  - case: (CompCache.find_cbt QFBV.Bfalse ic).
    + move=> [cs lr]. case=> ? ? ? ? ?; subst. done.
    + case: (CompCache.find_hbt QFBV.Bfalse ic).
      * move=> [cs lr]. case=> ? ? ? ? ?; subst. move=> Hocs Hic.
        exact: (CompCache.interp_cache_ct_add_cbt _ _ Hic Hocs).
      * case=> ? ? ? ? ?; subst. move=> _ Hic.
        apply: CompCache.interp_cache_ct_add_cbt; last by done.
        apply CompCache.interp_cache_ct_add_hbt. assumption.
  - case: (CompCache.find_cbt QFBV.Btrue ic).
    + move=> [cs lr]. case=> ? ? ? ? ?; subst. done.
    + case: (CompCache.find_hbt QFBV.Btrue ic).
      * move=> [cs lr]. case=> ? ? ? ? ?; subst. move=> Hocs Hic.
        exact: (CompCache.interp_cache_ct_add_cbt _ _ Hic Hocs).
      * case=> ? ? ? ? ?; subst. move=> _ Hic.
        apply: CompCache.interp_cache_ct_add_cbt; last by done.
        apply CompCache.interp_cache_ct_add_hbt. assumption.
  - move=> op e1 e2. case: (CompCache.find_cbt (QFBV.Bbinop op e1 e2) ic).
    + move=> [cs lr]. case=> ? ? ? ? ?; subst. done.
    + dcase (bit_blast_exp_ccache TE im ic ig e1) => [[[[[m1 c1] g1] cs1] ls1] Hbb1].
      dcase (bit_blast_exp_ccache TE m1 c1 g1 e2) => [[[[[m2 c2] g2] cs2] ls2] Hbb2].
      case: (CompCache.find_hbt (QFBV.Bbinop op e1 e2) c2).
      * move=> [cs lr]. case=> ? ? ? ? ?; subst. move=> Hcs Hic.
        rewrite !interp_cnf_catrev in Hcs. move/andP: Hcs => [Hcs1 /andP [Hcs2 Hcs]].
        apply: (CompCache.interp_cache_ct_add_cbt _ _ _ Hcs).
        apply: (bit_blast_exp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb2 Hcs2).
        exact: (bit_blast_exp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb1 Hcs1 Hic).
      * dcase (bit_blast_bbinop op g2 ls1 ls2) => [[[g3 cs3] ls3] Hbb3].
        case=> ? ? ? ? ?; subst. move=> Hcs Hic.
        rewrite !interp_cnf_catrev in Hcs. move/andP: Hcs => [Hcs1 /andP [Hcs2 Hcs3]].
        apply: (CompCache.interp_cache_ct_add_cbt _ _ _ Hcs3).
        apply CompCache.interp_cache_ct_add_hbt.
        apply: (bit_blast_exp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb2 Hcs2).
        exact: (bit_blast_exp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb1 Hcs1 Hic).
  - move=> e. case: (CompCache.find_cbt (QFBV.Blneg e) ic).
    + move=> [cs lr]. case=> ? ? ? ? ?; subst. done.
    + dcase (bit_blast_bexp_ccache TE im ic ig e) => [[[[[m1 c1] g1] cs1] ls1] Hbb1].
      case: (CompCache.find_hbt (QFBV.Blneg e) c1).
      * move=> [cs lr]. case=> ? ? ? ? ?; subst. move=> Hcs Hic.
        rewrite !interp_cnf_catrev in Hcs. move/andP: Hcs => [Hcs1 Hcs].
        apply: (CompCache.interp_cache_ct_add_cbt _ _ _ Hcs).
        exact: (bit_blast_bexp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb1 Hcs1 Hic).
      * case=> ? ? ? ? ?; subst. move=> Hcs Hic.
        rewrite !interp_cnf_catrev in Hcs. move/andP: Hcs => [Hcs1 Hcs].
        apply: (CompCache.interp_cache_ct_add_cbt _ _ _ Hcs).
        apply CompCache.interp_cache_ct_add_hbt.
        exact: (bit_blast_bexp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb1 Hcs1 Hic).
  - move=> e1 e2. case: (CompCache.find_cbt (QFBV.Bconj e1 e2) ic).
    + move=> [cs lr]. case=> ? ? ? ? ?; subst. done.
    + dcase (bit_blast_bexp_ccache TE im ic ig e1) => [[[[[m1 c1] g1] cs1] ls1] Hbb1].
      dcase (bit_blast_bexp_ccache TE m1 c1 g1 e2) => [[[[[m2 c2] g2] cs2] ls2] Hbb2].
      case: (CompCache.find_hbt (QFBV.Bconj e1 e2) c2).
      * move=> [cs lr]. case=> ? ? ? ? ?; subst. move=> Hcs Hic.
        rewrite !interp_cnf_catrev in Hcs. move/andP: Hcs => [Hcs1 /andP [Hcs2 Hcs]].
        apply: (CompCache.interp_cache_ct_add_cbt _ _ _ Hcs).
        apply: (bit_blast_bexp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb2 Hcs2).
        exact: (bit_blast_bexp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb1 Hcs1 Hic).
      * case=> ? ? ? ? ?; subst. move=> Hcs Hic.
        rewrite !interp_cnf_catrev in Hcs. move/andP: Hcs => [Hcs1 /andP [Hcs2 Hcs]].
        apply: (CompCache.interp_cache_ct_add_cbt _ _ _ Hcs).
        apply: (bit_blast_bexp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb2 Hcs2).
        exact: (bit_blast_bexp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb1 Hcs1 Hic).
  - move=> e1 e2. case: (CompCache.find_cbt (QFBV.Bdisj e1 e2) ic).
    + move=> [cs lr]. case=> ? ? ? ? ?; subst. done.
    + dcase (bit_blast_bexp_ccache TE im ic ig e1) => [[[[[m1 c1] g1] cs1] ls1] Hbb1].
      dcase (bit_blast_bexp_ccache TE m1 c1 g1 e2) => [[[[[m2 c2] g2] cs2] ls2] Hbb2].
      case: (CompCache.find_hbt (QFBV.Bdisj e1 e2) c2).
      * move=> [cs lr]. case=> ? ? ? ? ?; subst. move=> Hcs Hic.
        rewrite !interp_cnf_catrev in Hcs. move/andP: Hcs => [Hcs1 /andP [Hcs2 Hcs]].
        apply: (CompCache.interp_cache_ct_add_cbt _ _ _ Hcs).
        apply: (bit_blast_bexp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb2 Hcs2).
        exact: (bit_blast_bexp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb1 Hcs1 Hic).
      * case=> ? ? ? ? ?; subst. move=> Hcs Hic.
        rewrite !interp_cnf_catrev in Hcs. move/andP: Hcs => [Hcs1 /andP [Hcs2 Hcs]].
        apply: (CompCache.interp_cache_ct_add_cbt _ _ _ Hcs).
        apply: (bit_blast_bexp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb2 Hcs2).
        exact: (bit_blast_bexp_ccache_interp_cache_ct
                  _ _ _ _ _ _ _ _ _ _ _ Hbb1 Hcs1 Hic).
Qed.

(* ==== bit_blast_exp_hccache and bit_blast_bexp_hccache ==== *)


Fixpoint bit_blast_exp_hccache E m c g (e : hexp) : vm * ccache * generator * seq cnf * word :=
  (* = bit_blast_exp_nocet = *)
  let bit_blast_exp_nocet E m c g (e : hexp) : vm * ccache * generator * seq cnf * word * seq cnf :=
      match e with
      | epair (HEvar v) _ =>
        match find_het e c with
        | Some (cs, ls) => (m, c, g, cs, ls, cs)
        | None => match SSAVM.find v m with
                  | None => let '(g', cs, rs) := bit_blast_var E g v in
                            (SSAVM.add v rs m, add_het e [:: cs] rs c, g', [:: cs], rs, [:: cs])
                  | Some rs => (m, add_het e [::] rs c, g, [::], rs, [::])
                  end
        end
      | epair (HEconst bs) _ =>
        match find_het e c with
        | Some (cs, ls) => (m, c, g, cs, ls, cs)
        | None => let '(g', cs, rs) := bit_blast_const g bs in
                  (m, add_het e [:: cs] rs c, g', [:: cs], rs, [:: cs])
        end
      | epair (HEunop op e1) _ =>
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_hccache E m c g e1 in
        match find_het e c1 with
        | Some (csop, lsop) => (m1, c1, g1, catrev cs1 csop, lsop, csop)
        | None =>
          let '(gop, csop, lsop) := bit_blast_eunop op g1 ls1 in
          (m1, add_het e [:: csop] lsop c1, gop,
           catrev cs1 [:: csop], lsop, [:: csop])
        end
      | epair (HEbinop op e1 e2) _ =>
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_hccache E m c g e1 in
        let '(m2, c2, g2, cs2, ls2) := bit_blast_exp_hccache E m1 c1 g1 e2 in
        match find_het e c2 with
        | Some (csop, lsop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lsop, csop)
        | None =>
          let '(gop, csop, lsop) := bit_blast_ebinop op g2 ls1 ls2 in
          (m2, add_het e [:: csop] lsop c2, gop,
           catrev cs1 (catrev cs2 [:: csop]), lsop, [:: csop])
        end
      | epair (HEite b e1 e2) _ =>
        let '(mb, cb, gb, csb, lb) := bit_blast_bexp_hccache E m c g b in
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_hccache E mb cb gb e1 in
        let '(m2, c2, g2, cs2, ls2) := bit_blast_exp_hccache E m1 c1 g1 e2 in
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
            (m', CCacheHash.add_cet e csop lrs c', g', cs, lrs)
  end
with
bit_blast_bexp_hccache E m c g (e : hbexp) : vm * ccache * generator * seq cnf * literal :=
  (* = bit_blast_bexp_nocbt = *)
  let bit_blast_bexp_nocbt E m c g (e : hbexp) : vm * ccache * generator * seq cnf * literal * seq cnf :=
      match e with
      | bpair HBfalse _ =>
        match find_hbt e c with
        | Some (cs, l) => (m, c, g, cs, l, cs)
        | None => (m, add_hbt e [::] lit_ff c, g, [::], lit_ff, [::])
        end
      | bpair HBtrue _ =>
        match find_hbt e c with
        | Some (cs, l) => (m, c, g, cs, l, cs)
        | None => (m, add_hbt e [::] lit_tt c, g, [::], lit_tt, [::])
        end
      | bpair (HBbinop op e1 e2) _ =>
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_hccache E m c g e1 in
        let '(m2, c2, g2, cs2, ls2) := bit_blast_exp_hccache E m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None =>
          let '(gop, csop, lop) := bit_blast_bbinop op g2 ls1 ls2 in
          (m2, add_hbt e [:: csop] lop c2, gop,
           catrev cs1 (catrev cs2 [:: csop]), lop, [:: csop])
        end
      | bpair (HBlneg e1) _ =>
        let '(m1, c1, g1, cs1, l1) := bit_blast_bexp_hccache E m c g e1 in
        match find_hbt e c1 with
        | Some (csop, lop) => (m1, c1, g1, catrev cs1 csop, lop, csop)
        | None => let '(gop, csop, lop) := bit_blast_lneg g1 l1 in
                  (m1, add_hbt e [:: csop] lop c1, gop,
                   catrev cs1 [:: csop], lop, [:: csop])
        end
      | bpair (HBconj e1 e2) _ =>
        let '(m1, c1, g1, cs1, l1) := bit_blast_bexp_hccache E m c g e1 in
        let '(m2, c2, g2, cs2, l2) := bit_blast_bexp_hccache E m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None => let '(gop, csop, lop) := bit_blast_conj g2 l1 l2 in
                  (m2, add_hbt e [:: csop] lop c2, gop,
                   catrev cs1 (catrev cs2 [:: csop]), lop, [:: csop])
        end
      | bpair (HBdisj e1 e2) _ =>
        let '(m1, c1, g1, cs1, l1) := bit_blast_bexp_hccache E m c g e1 in
        let '(m2, c2, g2, cs2, l2) := bit_blast_bexp_hccache E m1 c1 g1 e2 in
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
            (m', CCacheHash.add_cbt e csop lr c', g', cs, lr)
  end.


(* ==== relation between bit_blast_exp_hccache and bit_blast_exp_fccache ==== *)

Section WellFormedCCache.

  Import QFBV.

  Definition well_formed_est (ht : SimpTableHash.simptable) : Prop :=
    forall (e : hexp) r, SimpTableHash.find_et e ht = Some r ->
                         well_formed_hexp e.

  Definition well_formed_bst (ht : SimpTableHash.simptable) : Prop :=
    forall (e : hbexp) r, SimpTableHash.find_bt e ht = Some r ->
                          well_formed_hbexp e.

  Definition well_formed_st (ht : SimpTableHash.simptable) : Prop :=
    well_formed_est ht /\ well_formed_bst ht.

  Definition well_formed_ect (ht : CompTableHash.comptable) : Prop :=
    forall (e : hexp) r, CompTableHash.find_et e ht = Some r ->
                         well_formed_hexp e.

  Definition well_formed_bct (ht : CompTableHash.comptable) : Prop :=
    forall (e : hbexp) r, CompTableHash.find_bt e ht = Some r ->
                          well_formed_hbexp e.

  Definition well_formed_ct (ht : CompTableHash.comptable) : Prop :=
    well_formed_ect ht /\ well_formed_bct ht.

  Definition well_formed_ccache (hc : CCacheHash.ccache) : Prop :=
    well_formed_ct (CCacheHash.ct hc) /\ well_formed_ct (CCacheHash.ht hc).

  Lemma well_formed_ccache_find_cet hc e r :
    well_formed_ccache hc -> CCacheHash.find_cet e hc = Some r ->
    well_formed_hexp e.
  Proof.
    move=> [[H1 H2] [H3 H4]] Hf. exact: (H1 _ _ Hf).
  Qed.

  Lemma well_formed_ccache_find_cbt hc e r :
    well_formed_ccache hc -> CCacheHash.find_cbt e hc = Some r ->
    well_formed_hbexp e.
  Proof.
    move=> [[H1 H2] [H3 H4]] Hf. exact: (H2 _ _ Hf).
  Qed.

  Lemma well_formed_ccache_find_het hc e r :
    well_formed_ccache hc -> CCacheHash.find_het e hc = Some r ->
    well_formed_hexp e.
  Proof.
    move=> [[H1 H2] [H3 H4]] Hf. exact: (H3 _ _ Hf).
  Qed.

  Lemma well_formed_ccache_find_hbt hc e r :
    well_formed_ccache hc -> CCacheHash.find_hbt e hc = Some r ->
    well_formed_hbexp e.
  Proof.
    move=> [[H1 H2] [H3 H4]] Hf. exact: (H4 _ _ Hf).
  Qed.

  Lemma well_formed_ccache_add_cet hc (e : hexp) cs ls :
    well_formed_ccache hc -> well_formed_hexp e ->
    well_formed_ccache (CCacheHash.add_cet e cs ls hc).
  Proof.
    move=> [[H1 H2] [H3 H4]] Hwfe. repeat split.
    - rewrite /add_cet /=. move=> f fls. case Hfe: (f == e).
      + rewrite (eqP Hfe). move=> _; assumption.
      + move/negP: Hfe=> Hfe. rewrite (CompTableHash.find_et_add_et_neq _ _ _ Hfe).
        exact: (H1 f).
    - rewrite /add_cet /=. move=> f fls. exact: (H2 f).
    - rewrite /add_cet /=. move=> f fls. exact: (H3 f).
    - rewrite /add_cet /=. move=> f fls. exact: (H4 f).
  Qed.

  Lemma well_formed_ccache_add_cbt hc (e : hbexp) cs ls :
    well_formed_ccache hc -> well_formed_hbexp e ->
    well_formed_ccache (CCacheHash.add_cbt e cs ls hc).
  Proof.
    move=> [[H1 H2] [H3 H4]] Hwfe. repeat split.
    - rewrite /add_cbt /=. move=> f fls. exact: (H1 f).
    - rewrite /add_cbt /=. move=> f fls. case Hfe: (f == e).
      + rewrite (eqP Hfe). move=> _; assumption.
      + move/negP: Hfe=> Hfe. rewrite (CompTableHash.find_bt_add_bt_neq _ _ _ Hfe).
        exact: (H2 f).
    - rewrite /add_cbt /=. move=> f fls. exact: (H3 f).
    - rewrite /add_cbt /=. move=> f fls. exact: (H4 f).
  Qed.

  Lemma well_formed_ccache_add_het hc (e : hexp) cs ls :
    well_formed_ccache hc -> well_formed_hexp e ->
    well_formed_ccache (CCacheHash.add_het e cs ls hc).
  Proof.
    move=> [[H1 H2] [H3 H4]] Hwfe. repeat split.
    - rewrite /add_het /=. move=> f fls. exact: (H1 f).
    - rewrite /add_het /=. move=> f fls. exact: (H2 f).
    - rewrite /add_het /=. move=> f fls. case Hfe: (f == e).
      + rewrite (eqP Hfe). move=> _; assumption.
      + move/negP: Hfe=> Hfe. rewrite (CompTableHash.find_et_add_et_neq _ _ _ Hfe).
        exact: (H3 f).
    - rewrite /add_het /=. move=> f fls. exact: (H4 f).
  Qed.

  Lemma well_formed_ccache_add_hbt hc (e : hbexp) cs ls :
    well_formed_ccache hc -> well_formed_hbexp e ->
    well_formed_ccache (CCacheHash.add_hbt e cs ls hc).
  Proof.
    move=> [[H1 H2] [H3 H4]] Hwfe. repeat split.
    - rewrite /add_hbt /=. move=> f fls. exact: (H1 f).
    - rewrite /add_hbt /=. move=> f fls. exact: (H2 f).
    - rewrite /add_hbt /=. move=> f fls. exact: (H3 f).
    - rewrite /add_hbt /=. move=> f fls. case Hfe: (f == e).
      + rewrite (eqP Hfe). move=> _; assumption.
      + move/negP: Hfe=> Hfe. rewrite (CompTableHash.find_bt_add_bt_neq _ _ _ Hfe).
        exact: (H4 f).
  Qed.

  Lemma well_formed_ccache_reset_ct c :
    well_formed_ccache c -> well_formed_ccache (reset_ct c).
  Proof.
    rewrite /reset_ct. move=>[[H1 H2] [H3 H4]]. by repeat split.
  Qed.

End WellFormedCCache.


Ltac t_auto_hook ::=
  match goal with
  | |- ?e = ?e => reflexivity
  | |- _ /\ _ => split
  | |- well_formed_ccache (add_cet (hash_exp _) _ _ _) =>
    apply: well_formed_ccache_add_cet
  | |- well_formed_ccache (add_cbt (hash_bexp _) _ _ _) =>
    apply: well_formed_ccache_add_cbt
  | |- well_formed_ccache (add_het (hash_exp _) _ _ _) =>
    apply: well_formed_ccache_add_het
  | |- well_formed_ccache (add_hbt (hash_bexp _) _ _ _) =>
    apply: well_formed_ccache_add_hbt
  | |- well_formed_ccache (add_cet ?he _ _ _) =>
    replace he with (hash_exp (unhash_hexp he))
      by (rewrite /=; try rewrite !unhash_hash_exp; try rewrite !unhash_hash_bexp;
          try rewrite !ehval_hash_exp; try rewrite !bhval_hash_bexp; reflexivity);
    apply: well_formed_ccache_add_cet
  | |- well_formed_ccache (add_cbt ?he _ _ _) =>
    replace he with (hash_bexp (unhash_hbexp he))
      by (rewrite /=; try rewrite !unhash_hash_exp; try rewrite !unhash_hash_bexp;
          try rewrite !ehval_hash_exp; try rewrite !bhval_hash_bexp; reflexivity);
    apply: well_formed_ccache_add_cbt
  | |- ccache_compatible (add_cet _ ?cs ?rs _) (CCacheFlatten.add_cet _ ?cs ?rs _) =>
    apply: ccache_compatible_add_cet
  | |- ccache_compatible (add_cbt _ ?cs ?rs _) (CCacheFlatten.add_cbt _ ?cs ?rs _) =>
    apply: ccache_compatible_add_cbt
  | |- ccache_compatible (add_het _ ?cs ?rs _) (CCacheFlatten.add_het _ ?cs ?rs _) =>
    apply: ccache_compatible_add_het
  | |- ccache_compatible (add_hbt _ ?cs ?rs _) (CCacheFlatten.add_hbt _ ?cs ?rs _) =>
    apply: ccache_compatible_add_hbt
  | |- context f [unhash_hexp (hash_exp ?e)] =>
    rewrite (unhash_hash_exp e) /=
  | |- context f [unhash_hbexp (hash_bexp ?e)] =>
    rewrite (unhash_hash_bexp e) /=
  | |- context f [ehval (hash_exp ?e)] =>
    rewrite (ehval_hash_exp e)
  | |- context f [bhval (hash_bexp ?e)] =>
    rewrite (bhval_hash_bexp e)
  | |- context f [well_formed_hexp (hash_exp ?e)] =>
    rewrite (hash_exp_well_formed e)
  | |- context f [well_formed_hbexp (hash_bexp ?e)] =>
    rewrite (hash_bexp_well_formed e)

  | |- context f [CCacheHash.add_cet (epair ?he ?hh) _ _ _] =>
    match goal with
    | |- context g [CCacheFlatten.add_cet ?e _ _ _] =>
      replace (epair he hh) with (hash_exp e)
    end
  | |- hash_exp _ = epair _ _ => rewrite /=
  end.

Lemma bit_blast_exp_hccache_well_formed_ccache
      E (e : QFBV.exp) m ihc g hm ohc hg hcs hlrs :
  well_formed_ccache ihc ->
  bit_blast_exp_hccache E m ihc g (hash_exp e) =  (hm, ohc, hg, hcs, hlrs) ->
  well_formed_ccache ohc
with bit_blast_bexp_hccache_well_formed_ccache
       E (e : QFBV.bexp) m ihc g hm ohc hg hcs hlr :
       well_formed_ccache ihc ->
       bit_blast_bexp_hccache E m ihc g (hash_bexp e) =  (hm, ohc, hg, hcs, hlr) ->
       well_formed_ccache ohc.
Proof.
  (* bit_blast_exp_hccache_fcache_well_formed_ccache *)
  - case: e => /=.
    + move=> v Hwf.
      replace (epair (HEvar v) 1) with (hash_exp (QFBV.Evar v)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Evar v)) ihc).
      * move=> [cs ls] [] ? ? ? ? ?; subst. assumption.
      * case: (find_het (hash_exp (QFBV.Evar v)) ihc).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. by t_auto.
        -- case Hvm: (SSAVM.find v m).
           ++ move=> [] ? ? ? ? ?; subst. by t_auto.
           ++ dcase (bit_blast_var E g v) => [[[g1 cs1] rs1] Hbbv].
              move=> [] ? ? ? ? ?; subst. by t_auto.
    + move=> bs Hf.
      replace (epair (HEconst bs) 1) with (hash_exp (QFBV.Econst bs)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Econst bs)) ihc).
      * move=> [cs ls] [] ? ? ? ? ?; subst. assumption.
      * case: (find_het (hash_exp (QFBV.Econst bs)) ihc).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. by t_auto.
    + move=> op e Hwf.
      replace (epair (HEunop op (hash_exp e)) (ehval (hash_exp e) + 1))
        with (hash_exp (QFBV.Eunop op e)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Eunop op e)) ihc).
      * move=> [cs ls] [] ? ? ? ? ?; subst. assumption.
      * dcase (bit_blast_exp_hccache E m ihc g (hash_exp e)) =>
        [[[[[hm1 hc1] hg1] hcs1] hls1] Hhbb].
        move: (bit_blast_exp_hccache_well_formed_ccache
                 _ _ _ _ _ _ _ _ _ _ Hwf Hhbb) => Hwf_hc1.
        case: (find_het (hash_exp (QFBV.Eunop op e)) hc1).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. by t_auto.
        -- dcase (bit_blast_eunop op hg1 hls1) => [[[g1 cs1] ls1] Hbb].
           move=> [] ? ? ? ? ?; subst. by t_auto.
    + move=> op e1 e2 Hwf.
      replace (epair (HEbinop op (hash_exp e1) (hash_exp e2))
                     (ehval (hash_exp e1) + ehval (hash_exp e2) + 1))
        with (hash_exp (QFBV.Ebinop op e1 e2)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Ebinop op e1 e2)) ihc).
      * move=> [cs ls] [] ? ? ? ? ?; subst. assumption.
      * dcase (bit_blast_exp_hccache E m ihc g (hash_exp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hls1] Hhbb1].
        dcase (bit_blast_exp_hccache E hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hls2] Hhbb2].
        move: (bit_blast_exp_hccache_well_formed_ccache
                 _ _ _ _ _ _ _ _ _ _ Hwf Hhbb1) => Hwf1.
        move: (bit_blast_exp_hccache_well_formed_ccache
                 _ _ _ _ _ _ _ _ _ _ Hwf1 Hhbb2) => Hwf2.
        case: (find_het (hash_exp (QFBV.Ebinop op e1 e2)) hc2).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. by t_auto.
        -- dcase (bit_blast_ebinop op hg2 hls1 hls2) => [[[gop csop] lsop] Hbbop].
           move=> [] ? ? ? ? ?; subst. by t_auto.
    + move=> e1 e2 e3 Hwf.
      replace (epair (HEite (hash_bexp e1) (hash_exp e2) (hash_exp e3))
                     (bhval (hash_bexp e1) +
                      ehval (hash_exp e2) + ehval (hash_exp e3) + 1)) with
          (hash_exp (QFBV.Eite e1 e2 e3)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Eite e1 e2 e3)) ihc).
      * move=> [cs ls] [] ? ? ? ? ?; subst. assumption.
      * dcase (bit_blast_bexp_hccache E m ihc g (hash_bexp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hls1] Hhbb1].
        dcase (bit_blast_exp_hccache E hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hls2] Hhbb2].
        dcase (bit_blast_exp_hccache E hm2 hc2 hg2 (hash_exp e3)) =>
        [[[[[hm3 hc3] hg3] hcs3] hls3] Hhbb3].
        move: (bit_blast_bexp_hccache_well_formed_ccache
                 _ _ _ _ _ _ _ _ _ _ Hwf Hhbb1) => Hwf1.
        move: (bit_blast_exp_hccache_well_formed_ccache
                 _ _ _ _ _ _ _ _ _ _ Hwf1 Hhbb2) => Hwf2.
        move: (bit_blast_exp_hccache_well_formed_ccache
                 _ _ _ _ _ _ _ _ _ _ Hwf2 Hhbb3) => Hwf3.
        case: (find_het (hash_exp (QFBV.Eite e1 e2 e3)) hc3).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. by t_auto.
        -- dcase (bit_blast_ite hg3 hls1 hls2 hls3) => [[[gop csop] lsop] Hbbop].
           move=> [] ? ? ? ? ?; subst. by t_auto.
  (* bit_blast_bexp_hccache_fcache_well_formed_ccache *)
  - case: e => /=.
    + move=> Hwf.
      replace (bpair HBfalse 1) with (hash_bexp QFBV.Bfalse) by reflexivity.
      case: (find_cbt (hash_bexp QFBV.Bfalse) ihc).
      * move=> [cs lr] [] ? ? ? ? ?; subst. assumption.
      * case: (find_hbt (hash_bexp QFBV.Bfalse) ihc).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. by t_auto.
    + move=> Hwf.
      replace (bpair HBtrue 1) with (hash_bexp QFBV.Btrue) by reflexivity.
      case: (find_cbt (hash_bexp QFBV.Btrue) ihc).
      * move=> [cs lr] [] ? ? ? ? ?; subst. assumption.
        case: (find_hbt (hash_bexp QFBV.Btrue) ihc).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. by t_auto.
    + move=> op e1 e2 Hwf.
      replace (bpair (HBbinop op (hash_exp e1) (hash_exp e2))
                     (ehval (hash_exp e1) + ehval (hash_exp e2) + 1)) with
          (hash_bexp (QFBV.Bbinop op e1 e2)) by reflexivity.
      case: (find_cbt (hash_bexp (QFBV.Bbinop op e1 e2)) ihc).
      * move=> [cs lr] [] ? ? ? ? ?; subst. assumption.
      * dcase (bit_blast_exp_hccache E m ihc g (hash_exp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_exp_hccache E hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
        move: (bit_blast_exp_hccache_well_formed_ccache
                 _ _ _ _ _ _ _ _ _ _ Hwf Hhbb1) => Hwf1.
        move: (bit_blast_exp_hccache_well_formed_ccache
                 _ _ _ _ _ _ _ _ _ _ Hwf1 Hhbb2) => Hwf2.
        case: (find_hbt (hash_bexp (QFBV.Bbinop op e1 e2)) hc2).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. by t_auto.
        -- dcase (bit_blast_bbinop op hg2 hlr1 hlr2) => [[[gop csop] lop] Hbbop].
           move=> [] ? ? ? ? ?; subst. by t_auto.
    + move=> e Hwf.
      replace (bpair (HBlneg (hash_bexp e)) (bhval (hash_bexp e) + 1)) with
          (hash_bexp (QFBV.Blneg e)) by reflexivity.
      case: (find_cbt (hash_bexp (QFBV.Blneg e)) ihc).
      * move=> [cs lr] [] ? ? ? ? ?; subst. assumption.
      * dcase (bit_blast_bexp_hccache E m ihc g (hash_bexp e)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        move: (bit_blast_bexp_hccache_well_formed_ccache
                 _ _ _ _ _ _ _ _ _ _ Hwf Hhbb1) => Hwf1.
        case: (find_hbt (hash_bexp (QFBV.Blneg e)) hc1).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. by t_auto.
    + move=> e1 e2 Hwf.
      replace (bpair (HBconj (hash_bexp e1) (hash_bexp e2))
                     (bhval (hash_bexp e1) + bhval (hash_bexp e2) + 1)) with
          (hash_bexp (QFBV.Bconj e1 e2)) by reflexivity.
      case: (find_cbt (hash_bexp (QFBV.Bconj e1 e2)) ihc).
      * move=> [cs lr] [] ? ? ? ? ?; subst. done.
      * dcase (bit_blast_bexp_hccache E m ihc g (hash_bexp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_bexp_hccache E hm1 hc1 hg1 (hash_bexp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
        move: (bit_blast_bexp_hccache_well_formed_ccache
                 _ _ _ _ _ _ _ _ _ _ Hwf Hhbb1) => Hwf1.
        move: (bit_blast_bexp_hccache_well_formed_ccache
                 _ _ _ _ _ _ _ _ _ _ Hwf1 Hhbb2) => Hwf2.
        case: (find_hbt (hash_bexp (QFBV.Bconj e1 e2)) hc2).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. by t_auto.
    + move=> e1 e2 Hwf.
      replace (bpair (HBdisj (hash_bexp e1) (hash_bexp e2))
                     (bhval (hash_bexp e1) + bhval (hash_bexp e2) + 1)) with
          (hash_bexp (QFBV.Bdisj e1 e2)) by reflexivity.
      case: (find_cbt (hash_bexp (QFBV.Bdisj e1 e2)) ihc).
      * move=> [cs lr] [] ? ? ? ? ?; subst. assumption.
      * dcase (bit_blast_bexp_hccache E m ihc g (hash_bexp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_bexp_hccache E hm1 hc1 hg1 (hash_bexp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
        move: (bit_blast_bexp_hccache_well_formed_ccache
                 _ _ _ _ _ _ _ _ _ _ Hwf Hhbb1) => Hwf1.
        move: (bit_blast_bexp_hccache_well_formed_ccache
                 _ _ _ _ _ _ _ _ _ _ Hwf1 Hhbb2) => Hwf2.
        case: (find_hbt (hash_bexp (QFBV.Bdisj e1 e2)) hc2).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. by t_auto.
Qed.

Ltac t_exists :=
  match goal with
  | H : ccache_compatible ?ohc ?ifc
    |- exists ofc : CCacheFlatten.ccache, ccache_compatible ?ohc ofc =>
    exists ifc
  | H : ccache_compatible ?ihc ?ifc
    |- exists ofc : CCacheFlatten.ccache,
      ccache_compatible (add_cet ?he ?hcs ?hlrs ?ihc) ofc =>
    exists (CCacheFlatten.add_cet (unhash_hexp he) hcs hlrs ifc)
  | H : ccache_compatible ?ihc ?ifc
    |- exists ofc : CCacheFlatten.ccache,
      ccache_compatible (add_cbt ?he ?hcs ?hlr ?ihc) ofc =>
    exists (CCacheFlatten.add_cbt (unhash_hbexp he) hcs hlr ifc)
  | H : ccache_compatible ?ihc ?ifc
    |- exists ofc : CCacheFlatten.ccache,
      ccache_compatible
        (add_cet ?he1 ?hcs1 ?hlrs1
                 (add_het ?he2 ?hcs2 ?hlrs2 ?ihc)) ofc =>
    exists (CCacheFlatten.add_cet
              (unhash_hexp he1) hcs1 hlrs1
              (CCacheFlatten.add_het (unhash_hexp he2) hcs2 hlrs2 ifc))
  | H : ccache_compatible ?ihc ?ifc
    |- exists ofc : CCacheFlatten.ccache,
      ccache_compatible
        (add_cbt ?he1 ?hcs1 ?hlr1
                 (add_hbt ?he2 ?hcs2 ?hlr2 ?ihc)) ofc =>
    exists (CCacheFlatten.add_cbt
              (unhash_hbexp he1) hcs1 hlr1
              (CCacheFlatten.add_hbt (unhash_hbexp he2) hcs2 hlr2 ifc))
  end; rewrite /=.

Lemma bit_blast_exp_hccache_ccache_compatible
      E (e : QFBV.exp) m ihc ifc g hm ohc hg hcs hlrs :
  ccache_compatible ihc ifc ->
  bit_blast_exp_hccache E m ihc g (hash_exp e) =  (hm, ohc, hg, hcs, hlrs) ->
  exists ofc, ccache_compatible ohc ofc
with bit_blast_bexp_hccache_ccache_compatible
       E (e : QFBV.bexp) m ihc ifc g hm ohc hg hcs hlr :
       ccache_compatible ihc ifc ->
       bit_blast_bexp_hccache E m ihc g (hash_bexp e) =  (hm, ohc, hg, hcs, hlr) ->
       exists ofc, ccache_compatible ohc ofc.
Proof.
  (* bit_blast_exp_hccache_fccache_ccache_compatible *)
  - case: e => /=.
    + move=> v Hcc.
      replace (epair (HEvar v) 1) with (hash_exp (QFBV.Evar v)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Evar v)) ihc).
      * move=> [cs ls] [] ? ? ? ? ?; subst. t_exists. assumption.
      * case: (find_het (hash_exp (QFBV.Evar v)) ihc).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- case Hvm: (SSAVM.find v m).
           ++ move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
           ++ dcase (bit_blast_var E g v) => [[[g1 cs1] rs1] Hbbv].
              move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
    + move=> bs Hcc.
      replace (epair (HEconst bs) 1) with (hash_exp (QFBV.Econst bs)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Econst bs)) ihc).
      * move=> [cs ls] [] ? ? ? ? ?; subst. t_exists. assumption.
      * case: (find_het (hash_exp (QFBV.Econst bs)) ihc).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
    + move=> op e Hcc.
      replace (epair (HEunop op (hash_exp e)) (ehval (hash_exp e) + 1))
        with (hash_exp (QFBV.Eunop op e)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Eunop op e)) ihc).
      * move=> [cs ls] [] ? ? ? ? ?; subst. t_exists. assumption.
      * dcase (bit_blast_exp_hccache E m ihc g (hash_exp e)) =>
        [[[[[hm1 hc1] hg1] hcs1] hls1] Hhbb].
        move: (bit_blast_exp_hccache_ccache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc Hhbb) => [fc1 Hcc1].
        case: (find_het (hash_exp (QFBV.Eunop op e)) hc1).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- dcase (bit_blast_eunop op hg1 hls1) => [[[g1 cs1] ls1] Hbb].
           move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
    + move=> op e1 e2 Hcc.
      replace (epair (HEbinop op (hash_exp e1) (hash_exp e2))
                     (ehval (hash_exp e1) + ehval (hash_exp e2) + 1))
        with (hash_exp (QFBV.Ebinop op e1 e2)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Ebinop op e1 e2)) ihc).
      * move=> [cs ls] [] ? ? ? ? ?; subst. t_exists. assumption.
      * dcase (bit_blast_exp_hccache E m ihc g (hash_exp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hls1] Hhbb1].
        dcase (bit_blast_exp_hccache E hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hls2] Hhbb2].
        move: (bit_blast_exp_hccache_ccache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc Hhbb1) => [fc1 Hcc1].
        move: (bit_blast_exp_hccache_ccache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc1 Hhbb2) => [fc2 Hcc2].
        case: (find_het (hash_exp (QFBV.Ebinop op e1 e2)) hc2).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- dcase (bit_blast_ebinop op hg2 hls1 hls2) => [[[gop csop] lsop] Hbbop].
           move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
    + move=> e1 e2 e3 Hcc.
      replace (epair (HEite (hash_bexp e1) (hash_exp e2) (hash_exp e3))
                     (bhval (hash_bexp e1) +
                      ehval (hash_exp e2) + ehval (hash_exp e3) + 1)) with
          (hash_exp (QFBV.Eite e1 e2 e3)) by reflexivity.
      case: (find_cet (hash_exp (QFBV.Eite e1 e2 e3)) ihc).
      * move=> [cs ls] [] ? ? ? ? ?; subst. t_exists. assumption.
      * dcase (bit_blast_bexp_hccache E m ihc g (hash_bexp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hls1] Hhbb1].
        dcase (bit_blast_exp_hccache E hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hls2] Hhbb2].
        dcase (bit_blast_exp_hccache E hm2 hc2 hg2 (hash_exp e3)) =>
        [[[[[hm3 hc3] hg3] hcs3] hls3] Hhbb3].
        move: (bit_blast_bexp_hccache_ccache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc Hhbb1) => [fc1 Hcc1].
        move: (bit_blast_exp_hccache_ccache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc1 Hhbb2) => [fc2 Hcc2].
        move: (bit_blast_exp_hccache_ccache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc2 Hhbb3) => [fc3 Hcc3].
        case: (find_het (hash_exp (QFBV.Eite e1 e2 e3)) hc3).
        -- move=> [cs ls] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- dcase (bit_blast_ite hg3 hls1 hls2 hls3) => [[[gop csop] lsop] Hbbop].
           move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
  (* bit_blast_bexp_hccache_fccache_ccache_compatible *)
  - case: e => /=.
    + move=> Hcc.
      replace (bpair HBfalse 1) with (hash_bexp QFBV.Bfalse) by reflexivity.
      case: (find_cbt (hash_bexp QFBV.Bfalse) ihc).
      * move=> [cs lr] [] ? ? ? ? ?; subst. t_exists. assumption.
      * case: (find_hbt (hash_bexp QFBV.Bfalse) ihc).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
    + move=> Hcc.
      replace (bpair HBtrue 1) with (hash_bexp QFBV.Btrue) by reflexivity.
      case: (find_cbt (hash_bexp QFBV.Btrue) ihc).
      * move=> [cs lr] [] ? ? ? ? ?; subst. t_exists. assumption.
      * case: (find_hbt (hash_bexp QFBV.Btrue) ihc).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
    + move=> op e1 e2 Hcc.
      replace (bpair (HBbinop op (hash_exp e1) (hash_exp e2))
                     (ehval (hash_exp e1) + ehval (hash_exp e2) + 1)) with
          (hash_bexp (QFBV.Bbinop op e1 e2)) by reflexivity.
      case: (find_cbt (hash_bexp (QFBV.Bbinop op e1 e2)) ihc).
      * move=> [cs lr] [] ? ? ? ? ?; subst. t_exists. assumption.
      * dcase (bit_blast_exp_hccache E m ihc g (hash_exp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_exp_hccache E hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
        move: (bit_blast_exp_hccache_ccache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc Hhbb1) => [fc1 Hcc1].
        move: (bit_blast_exp_hccache_ccache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc1 Hhbb2) => [fc2 Hcc2].
        case: (find_hbt (hash_bexp (QFBV.Bbinop op e1 e2)) hc2).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- dcase (bit_blast_bbinop op hg2 hlr1 hlr2) => [[[gop csop] lop] Hbbop].
           move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
    + move=> e Hcc.
      replace (bpair (HBlneg (hash_bexp e)) (bhval (hash_bexp e) + 1)) with
          (hash_bexp (QFBV.Blneg e)) by reflexivity.
      case: (find_cbt (hash_bexp (QFBV.Blneg e)) ihc).
      * move=> [cs lr] [] ? ? ? ? ?; subst. t_exists. assumption.
      * dcase (bit_blast_bexp_hccache E m ihc g (hash_bexp e)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        move: (bit_blast_bexp_hccache_ccache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc Hhbb1) => [fc1 Hcc1].
        case: (find_hbt (hash_bexp (QFBV.Blneg e)) hc1).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
    + move=> e1 e2 Hcc.
      replace (bpair (HBconj (hash_bexp e1) (hash_bexp e2))
                     (bhval (hash_bexp e1) + bhval (hash_bexp e2) + 1)) with
          (hash_bexp (QFBV.Bconj e1 e2)) by reflexivity.
      case: (find_cbt (hash_bexp (QFBV.Bconj e1 e2)) ihc).
      * move=> [cs lr] [] ? ? ? ? ?; subst. t_exists. assumption.
      * dcase (bit_blast_bexp_hccache E m ihc g (hash_bexp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_bexp_hccache E hm1 hc1 hg1 (hash_bexp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
        move: (bit_blast_bexp_hccache_ccache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc Hhbb1) => [fc1 Hcc1].
        move: (bit_blast_bexp_hccache_ccache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc1 Hhbb2) => [fc2 Hcc2].
        case: (find_hbt (hash_bexp (QFBV.Bconj e1 e2)) hc2).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
    + move=> e1 e2 Hcc.
      replace (bpair (HBdisj (hash_bexp e1) (hash_bexp e2))
                     (bhval (hash_bexp e1) + bhval (hash_bexp e2) + 1)) with
          (hash_bexp (QFBV.Bdisj e1 e2)) by reflexivity.
      case: (find_cbt (hash_bexp (QFBV.Bdisj e1 e2)) ihc).
      * move=> [cs lr] [] ? ? ? ? ?; subst. t_exists. assumption.
      * dcase (bit_blast_bexp_hccache E m ihc g (hash_bexp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_bexp_hccache E hm1 hc1 hg1 (hash_bexp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
        move: (bit_blast_bexp_hccache_ccache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc Hhbb1) => [fc1 Hcc1].
        move: (bit_blast_bexp_hccache_ccache_compatible
                 _ _ _ _ _ _ _ _ _ _ _ Hcc1 Hhbb2) => [fc2 Hcc2].
        case: (find_hbt (hash_bexp (QFBV.Bdisj e1 e2)) hc2).
        -- move=> [cs lr] [] ? ? ? ? ?; subst. t_exists. by t_auto.
        -- move=> [] ? ? ? ? ?; subst. t_exists. by t_auto.
Qed.

Lemma bit_blast_exp_hccache_fccache
      E (e : QFBV.exp) m ihc ifc g hm fm
      ohc ofc hg fg hcs fcs hlrs flrs :
  well_formed_ccache ihc ->
  ccache_compatible ihc ifc ->
  bit_blast_exp_hccache E m ihc g (hash_exp e) =  (hm, ohc, hg, hcs, hlrs) ->
  bit_blast_exp_fccache E m ifc g e =  (fm, ofc, fg, fcs, flrs) ->
  hm = fm
  /\ well_formed_ccache ohc
  /\ ccache_compatible ohc ofc
  /\ hg = fg
  /\ hcs = fcs
  /\ hlrs = flrs
with bit_blast_bexp_hccache_fccache
       E (e : QFBV.bexp) m ihc ifc g hm fm
       ohc ofc hg fg hcs fcs hlr flr :
       well_formed_ccache ihc ->
       ccache_compatible ihc ifc ->
       bit_blast_bexp_hccache E m ihc g (hash_bexp e) =  (hm, ohc, hg, hcs, hlr) ->
       bit_blast_bexp_fccache E m ifc g e =  (fm, ofc, fg, fcs, flr) ->
       hm = fm
       /\ well_formed_ccache ohc
       /\ ccache_compatible ohc ofc
       /\ hg = fg
       /\ hcs = fcs
       /\ hlr = flr.
Proof.
  (* bit_blast_exp_hccache_fccache *)
  - case: e => /=.
    + move=> v Hwf Hcc.
      replace (epair (HEvar v) 1) with (hash_exp (QFBV.Evar v)) by reflexivity.
      rewrite (ccache_compatible_find_cet _ Hcc).
      rewrite (ccache_compatible_find_het _ Hcc).
      case: (CCacheFlatten.find_cet (QFBV.Evar v) ifc).
      * move=> [cs ls] [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * case: (CCacheFlatten.find_het (QFBV.Evar v) ifc).
        -- move=> [cs ls] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- case Hvm: (SSAVM.find v m).
           ++ move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
                by t_auto.
           ++ dcase (bit_blast_var E g v) => [[[g1 cs1] rs1] Hbbv].
              move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
                by t_auto.
    + move=> bs Hf Hcc.
      replace (epair (HEconst bs) 1) with (hash_exp (QFBV.Econst bs)) by reflexivity.
      rewrite (ccache_compatible_find_cet _ Hcc).
      rewrite (ccache_compatible_find_het _ Hcc).
      case: (CCacheFlatten.find_cet (QFBV.Econst bs) ifc).
      * move=> [cs ls] [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * case: (CCacheFlatten.find_het (QFBV.Econst bs) ifc).
        -- move=> [cs ls] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
    + move=> op e Hwf Hcc.
      replace (epair (HEunop op (hash_exp e)) (ehval (hash_exp e) + 1))
        with (hash_exp (QFBV.Eunop op e)) by reflexivity.
      rewrite (ccache_compatible_find_cet _ Hcc).
      case: (CCacheFlatten.find_cet (QFBV.Eunop op e) ifc).
      * move=> [cs ls] [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * dcase (bit_blast_exp_hccache E m ihc g (hash_exp e)) =>
        [[[[[hm1 hc1] hg1] hcs1] hls1] Hhbb].
        dcase (bit_blast_exp_fccache E m ifc g e) =>
        [[[[[fm1 fc1] fg1] fcs1] fls1] Hfbb].
        move: (bit_blast_exp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf Hcc Hhbb Hfbb).
        move=> [? [Hwf1 [Hcc1 [? [? ?]]]]]; subst.
        rewrite (ccache_compatible_find_het _ Hcc1).
        case: (CCacheFlatten.find_het (QFBV.Eunop op e) fc1).
        -- move=> [cs ls] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- dcase (bit_blast_eunop op fg1 fls1) => [[[g1 cs1] ls1] Hbb].
           move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
    + move=> op e1 e2 Hwf Hcc.
      replace (epair (HEbinop op (hash_exp e1) (hash_exp e2))
                     (ehval (hash_exp e1) + ehval (hash_exp e2) + 1))
        with (hash_exp (QFBV.Ebinop op e1 e2)) by reflexivity.
      rewrite (ccache_compatible_find_cet _ Hcc).
      case: (CCacheFlatten.find_cet (QFBV.Ebinop op e1 e2) ifc).
      * move=> [cs ls] [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * dcase (bit_blast_exp_hccache E m ihc g (hash_exp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hls1] Hhbb1].
        dcase (bit_blast_exp_hccache E hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hls2] Hhbb2].
        dcase (bit_blast_exp_fccache E m ifc g e1) =>
        [[[[[fm1 fc1] fg1] fcs1] fls1] Hfbb1].
        dcase (bit_blast_exp_fccache E fm1 fc1 fg1 e2) =>
        [[[[[fm2 fc2] fg2] fcs2] fls2] Hfbb2].
        move: (bit_blast_exp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf Hcc Hhbb1 Hfbb1).
        move=> [? [Hwf1 [Hcc1 [? [? ?]]]]]; subst.
        move: (bit_blast_exp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf1 Hcc1 Hhbb2 Hfbb2).
        move=> [? [Hwf2 [Hcc2 [? [? ?]]]]]; subst.
        rewrite (ccache_compatible_find_het _ Hcc2).
        case: (CCacheFlatten.find_het (QFBV.Ebinop op e1 e2) fc2).
        -- move=> [cs ls] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- dcase (bit_blast_ebinop op fg2 fls1 fls2) => [[[gop csop] lsop] Hbbop].
           move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
    + move=> e1 e2 e3 Hwf Hcc.
      replace (epair (HEite (hash_bexp e1) (hash_exp e2) (hash_exp e3))
                     (bhval (hash_bexp e1) +
                      ehval (hash_exp e2) + ehval (hash_exp e3) + 1)) with
          (hash_exp (QFBV.Eite e1 e2 e3)) by reflexivity.
      rewrite (ccache_compatible_find_cet _ Hcc).
      case: (CCacheFlatten.find_cet (QFBV.Eite e1 e2 e3) ifc).
      * move=> [cs ls] [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * dcase (bit_blast_bexp_hccache E m ihc g (hash_bexp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hls1] Hhbb1].
        dcase (bit_blast_exp_hccache E hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hls2] Hhbb2].
        dcase (bit_blast_exp_hccache E hm2 hc2 hg2 (hash_exp e3)) =>
        [[[[[hm3 hc3] hg3] hcs3] hls3] Hhbb3].
        dcase (bit_blast_bexp_fccache E m ifc g e1) =>
        [[[[[fm1 fc1] fg1] fcs1] fls1] Hfbb1].
        dcase (bit_blast_exp_fccache E fm1 fc1 fg1 e2) =>
        [[[[[fm2 fc2] fg2] fcs2] fls2] Hfbb2].
        dcase (bit_blast_exp_fccache E fm2 fc2 fg2 e3) =>
        [[[[[fm3 fc3] fg3] fcs3] fls3] Hfbb3].
        move: (bit_blast_bexp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf Hcc Hhbb1 Hfbb1).
        move=> [? [Hwf1 [Hcc1 [? [? ?]]]]]; subst.
        move: (bit_blast_exp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf1 Hcc1 Hhbb2 Hfbb2).
        move=> [? [Hwf2 [Hcc2 [? [? ?]]]]]; subst.
        move: (bit_blast_exp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf2 Hcc2 Hhbb3 Hfbb3).
        move=> [? [Hwf3 [Hcc3 [? [? ?]]]]]; subst.
        rewrite (ccache_compatible_find_het _ Hcc3).
        case: (CCacheFlatten.find_het (QFBV.Eite e1 e2 e3) fc3).
        -- move=> [cs ls] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- dcase (bit_blast_ite fg3 fls1 fls2 fls3) => [[[gop csop] lsop] Hbbop].
           move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
  (* bit_blast_bexp_hccache_fccache *)
  - case: e => /=.
    + move=> Hwf Hcc.
      replace (bpair HBfalse 1) with (hash_bexp QFBV.Bfalse) by reflexivity.
      rewrite (ccache_compatible_find_cbt _ Hcc).
      case: (CCacheFlatten.find_cbt QFBV.Bfalse ifc).
      * move=> [cs lr] [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * rewrite (ccache_compatible_find_hbt _ Hcc).
        case: (CCacheFlatten.find_hbt QFBV.Bfalse ifc).
        -- move=> [cs lr] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
    + move=> Hwf Hcc.
      replace (bpair HBtrue 1) with (hash_bexp QFBV.Btrue) by reflexivity.
      rewrite (ccache_compatible_find_cbt _ Hcc).
      case: (CCacheFlatten.find_cbt QFBV.Btrue ifc).
      * move=> [cs lr] [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * rewrite (ccache_compatible_find_hbt _ Hcc).
        case: (CCacheFlatten.find_hbt QFBV.Btrue ifc).
        -- move=> [cs lr] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
    + move=> op e1 e2 Hwf Hcc.
      replace (bpair (HBbinop op (hash_exp e1) (hash_exp e2))
                     (ehval (hash_exp e1) + ehval (hash_exp e2) + 1)) with
          (hash_bexp (QFBV.Bbinop op e1 e2)) by reflexivity.
      rewrite (ccache_compatible_find_cbt _ Hcc).
      case: (CCacheFlatten.find_cbt (QFBV.Bbinop op e1 e2) ifc).
      * move=> [cs lr] [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * dcase (bit_blast_exp_hccache E m ihc g (hash_exp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_exp_hccache E hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
        dcase (bit_blast_exp_fccache E m ifc g e1) =>
        [[[[[fm1 fc1] fg1] fcs1] flr1] Hfbb1].
        dcase (bit_blast_exp_fccache E fm1 fc1 fg1 e2) =>
        [[[[[fm2 fc2] fg2] fcs2] flr2] Hfbb2].
        move: (bit_blast_exp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf Hcc Hhbb1 Hfbb1).
        move=> [? [Hwf1 [Hcc1 [? [? ?]]]]]; subst.
        move: (bit_blast_exp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf1 Hcc1 Hhbb2 Hfbb2).
        move=> [? [Hwf2 [Hcc2 [? [? ?]]]]]; subst.
        rewrite (ccache_compatible_find_hbt _ Hcc2).
        case: (CCacheFlatten.find_hbt (QFBV.Bbinop op e1 e2) fc2).
        -- move=> [cs lr] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- dcase (bit_blast_bbinop op fg2 flr1 flr2) => [[[gop csop] lop] Hbbop].
           move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
    + move=> e Hwf Hcc.
      replace (bpair (HBlneg (hash_bexp e)) (bhval (hash_bexp e) + 1)) with
          (hash_bexp (QFBV.Blneg e)) by reflexivity.
      rewrite (ccache_compatible_find_cbt _ Hcc).
      case: (CCacheFlatten.find_cbt (QFBV.Blneg e) ifc).
      * move=> [cs lr] [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * dcase (bit_blast_bexp_hccache E m ihc g (hash_bexp e)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_bexp_fccache E m ifc g e) =>
        [[[[[fm1 fc1] fg1] fcs1] flr1] Hfbb1].
        move: (bit_blast_bexp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                            Hwf Hcc Hhbb1 Hfbb1).
        move=> [? [Hwf1 [Hcc1 [? [? ?]]]]]; subst.
        rewrite (ccache_compatible_find_hbt _ Hcc1).
        case: (CCacheFlatten.find_hbt (QFBV.Blneg e) fc1).
        -- move=> [cs lr] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
    + move=> e1 e2 Hwf Hcc.
      replace (bpair (HBconj (hash_bexp e1) (hash_bexp e2))
                     (bhval (hash_bexp e1) + bhval (hash_bexp e2) + 1)) with
          (hash_bexp (QFBV.Bconj e1 e2)) by reflexivity.
      rewrite (ccache_compatible_find_cbt _ Hcc).
      case: (CCacheFlatten.find_cbt (QFBV.Bconj e1 e2) ifc).
      * move=> [cs lr] [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * dcase (bit_blast_bexp_hccache E m ihc g (hash_bexp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_bexp_hccache E hm1 hc1 hg1 (hash_bexp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
        dcase (bit_blast_bexp_fccache E m ifc g e1) =>
        [[[[[fm1 fc1] fg1] fcs1] flr1] Hfbb1].
        dcase (bit_blast_bexp_fccache E fm1 fc1 fg1 e2) =>
        [[[[[fm2 fc2] fg2] fcs2] flr2] Hfbb2].
        move: (bit_blast_bexp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                            Hwf Hcc Hhbb1 Hfbb1).
        move=> [? [Hwf1 [Hcc1 [? [? ?]]]]]; subst.
        move: (bit_blast_bexp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                            Hwf1 Hcc1 Hhbb2 Hfbb2).
        move=> [? [Hwf2 [Hcc2 [? [? ?]]]]]; subst.
        rewrite (ccache_compatible_find_hbt _ Hcc2).
        case: (CCacheFlatten.find_hbt (QFBV.Bconj e1 e2) fc2).
        -- move=> [cs lr] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
    + move=> e1 e2 Hwf Hcc.
      replace (bpair (HBdisj (hash_bexp e1) (hash_bexp e2))
                     (bhval (hash_bexp e1) + bhval (hash_bexp e2) + 1)) with
          (hash_bexp (QFBV.Bdisj e1 e2)) by reflexivity.
      rewrite (ccache_compatible_find_cbt _ Hcc).
      case: (CCacheFlatten.find_cbt (QFBV.Bdisj e1 e2) ifc).
      * move=> [cs lr] [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
      * dcase (bit_blast_bexp_hccache E m ihc g (hash_bexp e1)) =>
        [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
        dcase (bit_blast_bexp_hccache E hm1 hc1 hg1 (hash_bexp e2)) =>
        [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
        dcase (bit_blast_bexp_fccache E m ifc g e1) =>
        [[[[[fm1 fc1] fg1] fcs1] flr1] Hfbb1].
        dcase (bit_blast_bexp_fccache E fm1 fc1 fg1 e2) =>
        [[[[[fm2 fc2] fg2] fcs2] flr2] Hfbb2].
        move: (bit_blast_bexp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                            Hwf Hcc Hhbb1 Hfbb1).
        move=> [? [Hwf1 [Hcc1 [? [? ?]]]]]; subst.
        move: (bit_blast_bexp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                            Hwf1 Hcc1 Hhbb2 Hfbb2).
        move=> [? [Hwf2 [Hcc2 [? [? ?]]]]]; subst.
        rewrite (ccache_compatible_find_hbt _ Hcc2).
        case: (CCacheFlatten.find_hbt (QFBV.Bdisj e1 e2) fc2).
        -- move=> [cs lr] [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
        -- move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst.
             by t_auto.
Qed.


Lemma bit_blast_bexp_hccache_preserve
      TE e ihm ihc ihg ohm ohc ohg ohcs ohlr ifc icc :
  bit_blast_bexp_hccache TE ihm ihc ihg (hash_bexp e) =  (ohm, ohc, ohg, ohcs, ohlr) ->
  well_formed_ccache ihc ->
  ccache_compatible ihc ifc ->
  CCacheFlatten.ccache_compatible ifc icc ->
  vm_preserve ihm ohm.
Proof.
  move=> Hhbb Hwfihc Hccihc Hccifc.
  dcase (bit_blast_bexp_fccache TE ihm ifc ihg e) =>
  [[[[[ofm ofc] ofg] ofcs] oflr] Hfbb].
  move: (bit_blast_bexp_hccache_fccache Hwfihc Hccihc Hhbb Hfbb) =>
  [? [Hwfohc [Hccohc [? [? ?]]]]]; subst.
  dcase (bit_blast_bexp_ccache TE ihm icc ihg e) =>
  [[[[[om oc] og] ocs] olr] Hcbb].
  move: (bit_blast_bexp_fccache_valid Hccifc Hfbb Hcbb) =>
  [? [Hccofc [? [Heqs ?]]]]; subst.
  exact: (bit_blast_bexp_ccache_preserve Hcbb).
Qed.

Lemma bit_blast_bexp_hccache_bound
      TE e ihm ihc ihg ohm ohc ohg ohcs ohlr ifc icc :
  bit_blast_bexp_hccache TE ihm ihc ihg (hash_bexp e) =  (ohm, ohc, ohg, ohcs, ohlr) ->
  well_formed_ccache ihc ->
  ccache_compatible ihc ifc ->
  CCacheFlatten.ccache_compatible ifc icc ->
  CompCache.well_formed icc ->
  CompCache.bound icc ihm ->
  bound_bexp e ohm.
Proof.
  move=> Hhbb Hwfihc Hccihc Hccifc Hwficc Hboundicc.
  dcase (bit_blast_bexp_fccache TE ihm ifc ihg e) =>
  [[[[[ofm ofc] ofg] ofcs] oflr] Hfbb].
  move: (bit_blast_bexp_hccache_fccache Hwfihc Hccihc Hhbb Hfbb) =>
  [? [Hwfohc [Hccohc [? [? ?]]]]]; subst.
  dcase (bit_blast_bexp_ccache TE ihm icc ihg e) =>
  [[[[[ocm occ] ocg] occs] oclr] Hcbb].
  move: (bit_blast_bexp_fccache_valid Hccifc Hfbb Hcbb) =>
  [? [Hccofc [? [Heqs ?]]]]; subst.
  exact: (proj1 (bit_blast_bexp_ccache_bound_cache Hcbb Hwficc Hboundicc)).
Qed.

Lemma bit_blast_bexp_hccache_adhere
      TE e ihm ihc ihg ohm ohc ohg ohcs ohlr ifc icc :
  bit_blast_bexp_hccache TE ihm ihc ihg (hash_bexp e) =  (ohm, ohc, ohg, ohcs, ohlr) ->
  well_formed_ccache ihc ->
  ccache_compatible ihc ifc ->
  CCacheFlatten.ccache_compatible ifc icc ->
  adhere ihm TE ->
  adhere ohm TE.
Proof.
  move=> Hhbb Hwfihc Hccihc Hccifc Hadihm.
  dcase (bit_blast_bexp_fccache TE ihm ifc ihg e) =>
  [[[[[ofm ofc] ofg] ofcs] oflr] Hfbb].
  move: (bit_blast_bexp_hccache_fccache Hwfihc Hccihc Hhbb Hfbb) =>
  [? [Hwfohc [Hccohc [? [? ?]]]]]; subst.
  dcase (bit_blast_bexp_ccache TE ihm icc ihg e) =>
  [[[[[ocm occ] ocg] occs] oclr] Hcbb].
  move: (bit_blast_bexp_fccache_valid Hccifc Hfbb Hcbb) =>
  [? [Hccofc [? [Heqs ?]]]]; subst.
  exact: (bit_blast_bexp_ccache_adhere Hadihm Hcbb).
Qed.



(* ==== basic case ==== *)

(* = bit-blasting only one bexp = *)

Definition init_hccache : ccache := CCacheHash.empty.

Lemma init_hccache_well_formed : well_formed_ccache init_hccache.
Proof. done. Qed.

Lemma init_hccache_fccache_compatible : ccache_compatible init_hccache init_fccache.
Proof. done. Qed.

Theorem bit_blast_bexp_hccache_sound E (e : QFBV.bexp) m c g cs lr :
  bit_blast_bexp_hccache
    E init_vm init_hccache init_gen (hash_bexp e) = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexp e E ->
  ~ (sat (add_prelude ([::neg_lit lr]::(tflatten cs)))) ->
  (forall s, AdhereConform.conform_bexp e s E ->
             QFBV.eval_bexp e s).
Proof.
  move=> Hhbb Hwf Hsat.
  dcase (bit_blast_bexp_fccache E init_vm init_fccache init_gen e) =>
  [[[[[m' c'] g'] cs'] lr'] Hfbb].
  move: (bit_blast_bexp_hccache_fccache init_hccache_well_formed
                                      init_hccache_fccache_compatible
                                      Hhbb Hfbb).
  move=> [? [Hwf' [Hcc' [? [? ?]]]]]; subst.
  exact: (bit_blast_bexp_fccache_sound Hfbb Hwf Hsat).
Qed.

Theorem bit_blast_bexp_hccache_complete E (e : QFBV.bexp) m c g cs lr :
  bit_blast_bexp_hccache
    E init_vm init_hccache init_gen (hash_bexp e) = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexp e E ->
  (forall s, AdhereConform.conform_bexp e s E ->
             QFBV.eval_bexp e s) ->
  ~ (sat (add_prelude ([::neg_lit lr]::(tflatten cs)))).
Proof.
  move=> Hhbb Hwf Hev.
  dcase (bit_blast_bexp_fccache E init_vm init_fccache init_gen e) =>
  [[[[[m' c'] g'] cs'] lr'] Hfbb].
  move: (bit_blast_bexp_hccache_fccache init_hccache_well_formed
                                      init_hccache_fccache_compatible
                                      Hhbb Hfbb).
  move=> [? [Hwf' [Hcc' [? [? ?]]]]]; subst.
  exact: (bit_blast_bexp_fccache_complete Hfbb Hwf Hev).
Qed.

Theorem bit_blast_bexp_hccache_sat_sound E (e : QFBV.bexp) m c g cs lr :
  bit_blast_bexp_hccache
    E init_vm init_hccache init_gen (hash_bexp e) = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexp e E ->
  (sat (add_prelude ([:: lr]::(tflatten cs)))) ->
  (exists s, AdhereConform.conform_bexp e s E /\
             QFBV.eval_bexp e s).
Proof.
  move=> Hhbb Hwf Hsat.
  dcase (bit_blast_bexp_fccache E init_vm init_fccache init_gen e) =>
  [[[[[m' c'] g'] cs'] lr'] Hfbb].
  move: (bit_blast_bexp_hccache_fccache init_hccache_well_formed
                                      init_hccache_fccache_compatible
                                      Hhbb Hfbb).
  move=> [? [Hwf' [Hcc' [? [? ?]]]]]; subst.
  exact: (bit_blast_bexp_fccache_sat_sound Hfbb Hwf Hsat).
Qed.

Theorem bit_blast_bexp_hccache_sat_complete E (e : QFBV.bexp) m c g cs lr :
  bit_blast_bexp_hccache
    E init_vm init_hccache init_gen (hash_bexp e) = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexp e E ->
  (exists s, AdhereConform.conform_bexp e s E /\
             QFBV.eval_bexp e s) ->
  (sat (add_prelude ([:: lr]::(tflatten cs)))).
Proof.
  move=> Hhbb Hwf Hev.
  dcase (bit_blast_bexp_fccache E init_vm init_fccache init_gen e) =>
  [[[[[m' c'] g'] cs'] lr'] Hfbb].
  move: (bit_blast_bexp_hccache_fccache init_hccache_well_formed
                                      init_hccache_fccache_compatible
                                      Hhbb Hfbb).
  move=> [? [Hwf' [Hcc' [? [? ?]]]]]; subst.
  exact: (bit_blast_bexp_fccache_sat_complete Hfbb Hwf Hev).
Qed.

Corollary bit_blast_bexp_hccache_sat_sound_and_complete E (e : QFBV.bexp) m c g cs lr :
  bit_blast_bexp_hccache
    E init_vm init_hccache init_gen (hash_bexp e) = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexp e E ->
  ((exists s, AdhereConform.conform_bexp e s E /\ QFBV.eval_bexp e s)
   <->
   (exists (E : env), interp_cnf E (add_prelude ([:: lr]::(tflatten cs))))).
Proof.
  move=> Hbb Hwf. split.
  - exact: (bit_blast_bexp_hccache_sat_complete Hbb).
  - exact: (bit_blast_bexp_hccache_sat_sound Hbb).
Qed.


(* ==== general case ==== *)

(* = bit-blasting multiple bexps = *)

Definition bit_blast_bexp_hccache_tflatten E m c g e :=
  let '(m', c', g', css', lr') := bit_blast_bexp_hccache E m c g e in
  (m', c', g', tflatten css', lr').

Fixpoint bit_blast_hbexps_hccache E (es : seq hbexp) :=
  match es with
  | [::] => (init_vm, init_hccache, init_gen, add_prelude [::], lit_tt)
  | e :: es' =>
    let '(m, c, g, cs, lr) := bit_blast_hbexps_hccache E es' in
    bit_blast_bexp_hccache_tflatten E m (CCacheHash.reset_ct c) g e
  end.

Definition bit_blast_bexps_hccache E (es : seq QFBV.bexp) :=
  bit_blast_hbexps_hccache E (map hash_bexp es).

Lemma bit_blast_bexps_hccache_valid E es hm hc hg hcs hlr fm fc fg fcs flr :
  bit_blast_bexps_hccache E es = (hm, hc, hg, hcs, hlr) ->
  bit_blast_bexps_fccache E es = (fm, fc, fg, fcs, flr) ->
  hm = fm
  /\ well_formed_ccache hc
  /\ ccache_compatible hc fc
  /\ hg = fg
  /\ hcs = fcs
  /\ hlr = flr.
Proof.
  elim: es hm hc hg hcs hlr fm fc fg fcs flr => [| e es IH] hm hc hg hcs hlr fm fc fg fcs flr /=.
  - move=> [] ? ? ? ? ? [] ? ? ? ? ?; subst. done.
  - rewrite /bit_blast_bexps_hccache /=.
    dcase (bit_blast_hbexps_hccache E [seq hash_bexp i | i <- es]) =>
    [[[[[hm1 hc1] hg1] hcs1] hlr1] Hhbb1].
    rewrite Hhbb1. rewrite /bit_blast_bexp_hccache_tflatten.
    dcase (bit_blast_bexp_hccache E hm1 (reset_ct hc1) hg1 (hash_bexp e)) =>
    [[[[[hm2 hc2] hg2] hcs2] hlr2] Hhbb2].
    case=> ? ? ? ? ?; subst.
    dcase (bit_blast_bexps_fccache E es) => [[[[[fm1 fc1] fg1] fcs1] flr1] Hfbb1].
    rewrite /bit_blast_bexp_fccache_tflatten.
    dcase (bit_blast_bexp_fccache E fm1 (CCacheFlatten.reset_ct fc1) fg1 e) =>
    [[[[[fm2 fc2] fg2] fcs2] flr2] Hfbb2].
    case=> ? ? ? ? ?; subst.
    move: (IH _ _ _ _ _ _ _ _ _ _ Hhbb1 Hfbb1).
    move=> [Hm [Hwf1 [Hcc1 [Hg [Hcs Hlr]]]]]; subst.
    move: (bit_blast_bexp_hccache_fccache (well_formed_ccache_reset_ct Hwf1)
                                        (ccache_compatible_reset_ct Hcc1)
                                        Hhbb2 Hfbb2).
    move=> [? [Hwf2 [Hcc2 [? [? ?]]]]]; subst. by repeat split => //=.
Qed.

Theorem bit_blast_bexps_hccache_sound e es E m c g cs lr :
  bit_blast_bexps_hccache E (e::es) = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexps (e::es) E ->
  ~ (sat (add_prelude ([::neg_lit lr]::cs))) ->
  (forall s, AdhereConform.conform_bexps (e::es) s E ->
             QFBV.eval_bexp e s).
Proof.
  move=> Hhbb Hwf Hsat.
  dcase (bit_blast_bexps_fccache E (e::es)) => [[[[[m' c'] g'] cs'] lr'] Hfbb].
  move: (bit_blast_bexps_hccache_valid Hhbb Hfbb).
  move=> [Hm [Hwfc [Hcc [Hg [Hcs Hlr]]]]]; subst.
  exact: (bit_blast_bexps_fccache_sound Hfbb Hwf Hsat).
Qed.

Theorem bit_blast_bexps_hccache_complete e es E m c g cs lr :
  bit_blast_bexps_hccache E (e::es) = (m, c, g, cs, lr) ->
  QFBV.well_formed_bexps (e::es) E ->
  (forall s, AdhereConform.conform_bexps (e::es) s E ->
             QFBV.eval_bexp e s) ->
  ~ (sat (add_prelude ([::neg_lit lr]::cs))).
Proof.
  move=> Hhbb Hwf Hev Hsat.
  dcase (bit_blast_bexps_fccache E (e::es)) => [[[[[m' c'] g'] cs'] lr'] Hfbb].
  move: (bit_blast_bexps_hccache_valid Hhbb Hfbb).
  move=> [Hm [Hwfc [Hcc [Hg [Heqs Hlr]]]]]; subst.
  exact: (bit_blast_bexps_fccache_complete Hfbb Hwf Hev).
Qed.

Definition bexp_to_cnf_hccache E m c g e :=
  let '(m', c', g', cs, lr) := bit_blast_bexp_hccache_tflatten E m c g e in
  (m', c', g', add_prelude ([::neg_lit lr]::cs)).



(* Bit-blasting a sequence of QFBV bexps as a conjunction *)

Fixpoint bit_blast_hbexps_hccache_conjs_rec
         E m c g rcs rlrs es : vm * ccache * generator * seq cnf * cnf :=
  match es with
  | [::] => (m, c, g, rcs, rlrs)
  | hd::tl => let '(m', c', g', cs, lr) := bit_blast_bexp_hccache E m c g hd in
              bit_blast_hbexps_hccache_conjs_rec E m' c' g'
                                                (catrev cs rcs) ([:: lr]::rlrs) tl
  end.

Definition bit_blast_hbexps_hccache_conjs E m c g es :=
  bit_blast_hbexps_hccache_conjs_rec E m c g [::] [::] es.

Lemma bit_blast_hbexps_hccache_conjs_rec_empty E m c g rcs rlrs :
  bit_blast_hbexps_hccache_conjs_rec E m c g rcs rlrs [::] = (m, c, g, rcs, rlrs).
Proof. reflexivity. Qed.

Lemma bit_blast_hbexps_hccache_conjs_rec_singleton E m c g rcs rlrs e :
  bit_blast_hbexps_hccache_conjs_rec E m c g rcs rlrs [:: e] =
  let '(m', c', g', cs, lr) := bit_blast_bexp_hccache E m c g e in
  (m', c', g', (catrev cs rcs), [::lr]::rlrs).
Proof. reflexivity. Qed.

Lemma bit_blast_hbexps_hccache_conjs_rec_cons E m c g rcs rlrs e es :
  bit_blast_hbexps_hccache_conjs_rec E m c g rcs rlrs (e::es) =
  let '(m', c', g', cs, lr) := bit_blast_bexp_hccache E m c g e in
  bit_blast_hbexps_hccache_conjs_rec E m' c' g'
                                    (catrev cs rcs) ([::lr]::rlrs) es.
Proof. reflexivity. Qed.

Lemma bit_blast_hbexps_hccache_conjs_rec_rcons E m c g rcs rlrs es e :
  bit_blast_hbexps_hccache_conjs_rec E m c g rcs rlrs (rcons es e) =
  let '(m', c', g', cs, lrs) := bit_blast_hbexps_hccache_conjs_rec
                                  E m c g rcs rlrs es in
  bit_blast_hbexps_hccache_conjs_rec E m' c' g' cs lrs [:: e].
Proof.
  rewrite /=. elim: es m c g rcs rlrs e => [| hd tl IH] m c g rcs rlrs e //=.
  dcase (bit_blast_bexp_hccache E m c g hd) => [[[[[m1 c1] g1] cs1] lr1] Hbb_hd].
  rewrite -IH. reflexivity.
Qed.

Lemma bit_blast_hbexps_hccache_conjs_rec_cat E m c g rcs rlrs es1 es2 :
  bit_blast_hbexps_hccache_conjs_rec E m c g rcs rlrs (es1 ++ es2) =
  let '(m', c', g', cs1, lrs1) := bit_blast_hbexps_hccache_conjs_rec
                                    E m c g rcs rlrs es1 in
  bit_blast_hbexps_hccache_conjs_rec E m' c' g' cs1 lrs1 es2.
Proof.
  elim: es1 es2 m c g rcs rlrs => [| hd tl IH] es2 m c g rcs rlrs //=.
  dcase (bit_blast_bexp_hccache E m c g hd) => [[[[[m1 c1] g1] cs1] lr1] Hbb_hd].
  rewrite -IH. reflexivity.
Qed.

Lemma bit_blast_hbexps_hccache_conjs_rec_well_formed_ccache
      TE es m c g m' c' g' ics ilrs cs lrs :
  bit_blast_hbexps_hccache_conjs_rec
    TE m c g ics ilrs (mapr hash_bexp es) = (m', c', g', cs, lrs) ->
  well_formed_ccache c -> well_formed_ccache c'.
Proof.
  elim: es m c g m' c' g' ics ilrs cs lrs =>
  [| hd tl IH] im ic ig om oc og ics ilrs ocs olrs //=.
  - case=> ? ? ? ? ?; subst. by apply.
  - rewrite mapr_cons. rewrite bit_blast_hbexps_hccache_conjs_rec_rcons.
    dcase (bit_blast_hbexps_hccache_conjs_rec TE im ic ig ics ilrs (mapr hash_bexp tl))
    => [[[[[m1 c1] g1] cs1] lrs1] Hbb_tl].
    rewrite bit_blast_hbexps_hccache_conjs_rec_singleton.
    dcase (bit_blast_bexp_hccache TE m1 c1 g1 (hash_bexp hd)) =>
    [[[[[m2 c2] g2] cs2] lrs2] Hbb_hd]. case=> ? ? ? ? ?; subst.
    move=> Hwf_ic. move: (IH _ _ _ _ _ _ _ _ _ _ Hbb_tl Hwf_ic) => Hwf_c1.
    exact: (bit_blast_bexp_hccache_well_formed_ccache Hwf_c1 Hbb_hd).
Qed.

Lemma bit_blast_hbexps_hccache_conjs_rec_ccache_compatible
      TE es m c g m' c' g' ics ilrs cs lrs fc :
  bit_blast_hbexps_hccache_conjs_rec
    TE m c g ics ilrs (mapr hash_bexp es) = (m', c', g', cs, lrs) ->
  ccache_compatible c fc -> exists fc', ccache_compatible c' fc'.
Proof.
  elim: es m c g m' c' g' ics ilrs cs lrs fc =>
  [| hd tl IH] im ic ig om oc og ics ilrs ocs olrs fc //=.
  - case=> ? ? ? ? ?; subst. move=> Hcomp. exists fc. assumption.
  - rewrite mapr_cons. rewrite bit_blast_hbexps_hccache_conjs_rec_rcons.
    dcase (bit_blast_hbexps_hccache_conjs_rec TE im ic ig ics ilrs (mapr hash_bexp tl))
    => [[[[[m1 c1] g1] cs1] lrs1] Hbb_tl].
    rewrite bit_blast_hbexps_hccache_conjs_rec_singleton.
    dcase (bit_blast_bexp_hccache TE m1 c1 g1 (hash_bexp hd)) =>
    [[[[[m2 c2] g2] cs2] lrs2] Hbb_hd]. case=> ? ? ? ? ?; subst.
    move=> Hcomp. move: (IH _ _ _ _ _ _ _ _ _ _ _ Hbb_tl Hcomp) => [fc1 Hcomp_c1].
    exact: (bit_blast_bexp_hccache_ccache_compatible Hcomp_c1 Hbb_hd).
Qed.

Lemma bit_blast_hbexps_hccache_conjs_rec_ccache_compatible_chain
      TE es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc :
  bit_blast_hbexps_hccache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  well_formed_ccache ihc ->
  ccache_compatible ihc ifc ->
  CCacheFlatten.ccache_compatible ifc icc ->
  exists ofc, exists occ,
        ccache_compatible ohc ofc
        /\ CCacheFlatten.ccache_compatible ofc occ.
Proof.
  elim: es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc =>
  [| hd tl IH] ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc //=.
  - case=> ? ? ? ? ?; subst. move=> ? ? ?.
    exists ifc. exists icc. tauto.
  - rewrite mapr_cons. rewrite bit_blast_hbexps_hccache_conjs_rec_rcons.
    dcase (bit_blast_hbexps_hccache_conjs_rec
             TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp tl))
    => [[[[[hm1 hc1] hg1] hcs1] hlrs1] Hhbb_tl].
    rewrite bit_blast_hbexps_hccache_conjs_rec_singleton.
    dcase (bit_blast_bexp_hccache TE hm1 hc1 hg1 (hash_bexp hd)) =>
    [[[[[hm2 hc2] hg2] hcs2] hlrs2] Hhbb_hd]. case=> ? ? ? ? ?; subst.
    move=> Hwfihc Hccihc Hccifc.
    move: (IH _ _ _ _ _ _ _ _ _ _ _ _ Hhbb_tl Hwfihc Hccihc Hccifc)
    => [fc1 [cc1 [Hcchc1 Hccfc1]]].
    move: (bit_blast_hbexps_hccache_conjs_rec_well_formed_ccache Hhbb_tl Hwfihc)
    => Hwfhc1.
    dcase (bit_blast_bexp_fccache TE hm1 fc1 hg1 hd) =>
    [[[[[fm2 fc2] fg2] fcs2] flrs2] Hfbb_hd].
    move: (bit_blast_bexp_hccache_fccache Hwfhc1 Hcchc1 Hhbb_hd Hfbb_hd)
    => [? [Hwfohc [Hccohc [? [? ?]]]]]; subst.
    dcase (bit_blast_bexp_ccache TE hm1 cc1 hg1 hd) =>
    [[[[[cm2 cc2] cg2] ccs2] clrs2] Hcbb_hd]; subst.
    move: (bit_blast_bexp_fccache_valid Hccfc1 Hfbb_hd Hcbb_hd)
    => [? [Hccfc2 [? [? ?]]]]; subst.
    exists fc2. exists cc2. tauto.
Qed.

Lemma bit_blast_hbexps_hccache_conjs_rec_ccache_compatible_chain_wf_bound
      TE es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc :
  bit_blast_hbexps_hccache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  well_formed_ccache ihc ->
  ccache_compatible ihc ifc ->
  CCacheFlatten.ccache_compatible ifc icc ->
  CompCache.well_formed icc ->
  CompCache.bound icc ihm ->
  exists ofc, exists occ,
        ccache_compatible ohc ofc
        /\ CCacheFlatten.ccache_compatible ofc occ
        /\ CompCache.well_formed occ
        /\ CompCache.bound occ ohm.
Proof.
  elim: es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc =>
  [| hd tl IH] ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc //=.
  - case=> ? ? ? ? ?; subst. move=> ? ? ? ? ?.
    exists ifc. exists icc. tauto.
  - rewrite mapr_cons. rewrite bit_blast_hbexps_hccache_conjs_rec_rcons.
    dcase (bit_blast_hbexps_hccache_conjs_rec
             TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp tl))
    => [[[[[hm1 hc1] hg1] hcs1] hlrs1] Hhbb_tl].
    rewrite bit_blast_hbexps_hccache_conjs_rec_singleton.
    dcase (bit_blast_bexp_hccache TE hm1 hc1 hg1 (hash_bexp hd)) =>
    [[[[[hm2 hc2] hg2] hcs2] hlrs2] Hhbb_hd]. case=> ? ? ? ? ?; subst.
    move=> Hwfihc Hccihc Hccifc Hwficc Hboundicc.
    move: (IH _ _ _ _ _ _ _ _ _ _ _ _
              Hhbb_tl Hwfihc Hccihc Hccifc Hwficc Hboundicc)
    => [fc1 [cc1 [Hcchc1 [Hccfc1 [Hwfcc1 Hboundcc1]]]]].
    move: (bit_blast_hbexps_hccache_conjs_rec_well_formed_ccache Hhbb_tl Hwfihc)
    => Hwfhc1.
    dcase (bit_blast_bexp_fccache TE hm1 fc1 hg1 hd) =>
    [[[[[fm2 fc2] fg2] fcs2] flrs2] Hfbb_hd].
    move: (bit_blast_bexp_hccache_fccache Hwfhc1 Hcchc1 Hhbb_hd Hfbb_hd)
    => [? [Hwfohc [Hccohc [? [? ?]]]]]; subst.
    dcase (bit_blast_bexp_ccache TE hm1 cc1 hg1 hd) =>
    [[[[[cm2 cc2] cg2] ccs2] clrs2] Hcbb_hd]; subst.
    move: (bit_blast_bexp_fccache_valid Hccfc1 Hfbb_hd Hcbb_hd)
    => [? [Hccfc2 [? [? ?]]]]; subst.
    move: (bit_blast_bexp_ccache_bound_cache Hcbb_hd Hwfcc1 Hboundcc1) =>
    [Hbbexpcc2 Hboundcc2].
    move: (bit_blast_bexp_ccache_well_formed Hcbb_hd Hwfcc1) => Hwfcc2.
    exists fc2. exists cc2. tauto.
Qed.

Lemma bit_blast_hbexps_hccache_conjs_rec_preserve
      TE es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc :
  bit_blast_hbexps_hccache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  well_formed_ccache ihc ->
  ccache_compatible ihc ifc ->
  CCacheFlatten.ccache_compatible ifc icc ->
  vm_preserve ihm ohm.
Proof.
  elim: es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc =>
  [| hd tl IH] ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc //=.
  - case=> ? ? ? ? ?; subst. move=> _ _ _. exact: vm_preserve_refl.
  - rewrite mapr_cons. rewrite bit_blast_hbexps_hccache_conjs_rec_rcons.
    dcase (bit_blast_hbexps_hccache_conjs_rec TE ihm ihc ihg ihcs ihlrs
                                             (mapr hash_bexp tl))
    => [[[[[hm1 hc1] hg1] hcs1] hlrs1] Hhbb_tl].
    rewrite bit_blast_hbexps_hccache_conjs_rec_singleton.
    dcase (bit_blast_bexp_hccache TE hm1 hc1 hg1 (hash_bexp hd)) =>
    [[[[[hm2 hc2] hg2] hcs2] hlrs2] Hhbb_hd]. case=> ? ? ? ? ?; subst.
    move=> Hwfihc Hccihc Hccifc.
    move: (IH _ _ _ _ _ _ _ _ _ _ _ _ Hhbb_tl Hwfihc Hccihc Hccifc) => Hpre1.
    apply: (vm_preserve_trans Hpre1).

    move: (bit_blast_hbexps_hccache_conjs_rec_well_formed_ccache Hhbb_tl Hwfihc)
    => Hwfhc1.
    move: (bit_blast_hbexps_hccache_conjs_rec_ccache_compatible_chain
             Hhbb_tl Hwfihc Hccihc Hccifc)
    => [fc1 [cc1 [Hcchc1 Hccfc1]]].
    exact: (bit_blast_bexp_hccache_preserve Hhbb_hd Hwfhc1 Hcchc1 Hccfc1).
Qed.

Lemma bit_blast_hbexps_hccache_conjs_rec_ccache_compatible_full
      TE E es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc :
  bit_blast_hbexps_hccache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  QFBV.well_formed_bexps es TE ->
  well_formed_ccache ihc ->
  ccache_compatible ihc ifc ->
  CCacheFlatten.ccache_compatible ifc icc ->
  CompCache.well_formed icc ->
  CompCache.bound icc ihm ->
  interp_cnf E (tflatten ohcs) ->
  CompCache.interp_cache_ct E icc ->
  CompCache.correct ihm icc ->
  exists ofc, exists occ,
        ccache_compatible ohc ofc
        /\ CCacheFlatten.ccache_compatible ofc occ
        /\ CompCache.well_formed occ
        /\ CompCache.bound occ ohm
        /\ CompCache.interp_cache_ct E occ
        /\ CompCache.correct ohm occ.
Proof.
  elim: es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc =>
  [| hd tl IH] ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc //=.
  - case=> ? ? ? ? ?; subst. move=> ? ? ? ? ? ? ? ? ?.
    exists ifc. exists icc. tauto.
  - rewrite mapr_cons. rewrite bit_blast_hbexps_hccache_conjs_rec_rcons.
    dcase (bit_blast_hbexps_hccache_conjs_rec
             TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp tl))
    => [[[[[hm1 hc1] hg1] hcs1] hlrs1] Hhbb_tl].
    rewrite bit_blast_hbexps_hccache_conjs_rec_singleton.
    dcase (bit_blast_bexp_hccache TE hm1 hc1 hg1 (hash_bexp hd)) =>
    [[[[[hm2 hc2] hg2] hcs2] hlrs2] Hhbb_hd]. case=> ? ? ? ? ?; subst.
    move=> /andP [Hwf_hd Hwf_tl] Hwfihc Hccihc Hccifc Hwficc Hboundicc
            Hcs Hcticc Hcorrihm.
    rewrite interp_cnf_tflatten_catrev in Hcs. move/andP: Hcs => [Hhcs2 Hhcs1].

    move: (IH _ _ _ _ _ _ _ _ _ _ _ _
              Hhbb_tl Hwf_tl Hwfihc Hccihc Hccifc Hwficc Hboundicc
              Hhcs1 Hcticc Hcorrihm)
    => [fc1 [cc1
                   [Hcchc1 [Hccfc1 [Hwfcc1 [Hboundcc1 [Hctcc1 Hcorrcc1]]]]]]].
    move: (bit_blast_hbexps_hccache_conjs_rec_well_formed_ccache Hhbb_tl Hwfihc)
    => Hwfhc1.
    dcase (bit_blast_bexp_fccache TE hm1 fc1 hg1 hd) =>
    [[[[[fm2 fc2] fg2] fcs2] flrs2] Hfbb_hd].
    move: (bit_blast_bexp_hccache_fccache Hwfhc1 Hcchc1 Hhbb_hd Hfbb_hd)
    => [? [Hwfohc [Hccohc [? [? ?]]]]]; subst.
    dcase (bit_blast_bexp_ccache TE hm1 cc1 hg1 hd) =>
    [[[[[cm2 cc2] cg2] ccs2] clrs2] Hcbb_hd]; subst.
    move: (bit_blast_bexp_fccache_valid Hccfc1 Hfbb_hd Hcbb_hd)
    => [? [Hccfc2 [? [Heqs ?]]]]; subst.
    move: (bit_blast_bexp_ccache_bound_cache Hcbb_hd Hwfcc1 Hboundcc1) =>
    [Hbbexpcc2 Hboundcc2].
    move: (bit_blast_bexp_ccache_well_formed Hcbb_hd Hwfcc1) => Hwfcc2.
    rewrite (Heqs E) in Hhcs2.
    move: (bit_blast_bexp_ccache_interp_cache_ct Hcbb_hd Hhcs2 Hctcc1) => Hctcc2.
    move: (bit_blast_hbexps_hccache_conjs_rec_preserve
             Hhbb_tl Hwfihc Hccihc Hccifc) => Hpreihm.
    move: (bit_blast_bexp_ccache_correct_cache
             Hcbb_hd Hwf_hd Hwfcc1 Hcorrcc1) => Hcorrcc2.
    move: (CompCache.vm_preserve_correct Hpreihm Hcorrihm).
    exists fc2. exists cc2. tauto.
Qed.

Lemma bit_blast_hbexps_hccache_conjs_rec_bound
      TE es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc :
  bit_blast_hbexps_hccache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  well_formed_ccache ihc ->
  ccache_compatible ihc ifc ->
  CCacheFlatten.ccache_compatible ifc icc ->
  CompCache.well_formed icc ->
  CompCache.bound icc ihm ->
  bound_bexps es ohm.
Proof.
  elim: es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc =>
  [| hd tl IH] ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc //=.
  rewrite mapr_cons. rewrite bit_blast_hbexps_hccache_conjs_rec_rcons.
  dcase (bit_blast_hbexps_hccache_conjs_rec TE ihm ihc ihg ihcs ihlrs
                                           (mapr hash_bexp tl))
  => [[[[[hm1 hc1] hg1] hcs1] hlrs1] Hhbb_tl].
  rewrite bit_blast_hbexps_hccache_conjs_rec_singleton.
  dcase (bit_blast_bexp_hccache TE hm1 hc1 hg1 (hash_bexp hd)) =>
  [[[[[hm2 hc2] hg2] hcs2] hlrs2] Hhbb_hd]. case=> ? ? ? ? ?; subst.
  move=> Hwfihc Hccihc Hccifc Hwficc Hboundicc.
  move: (IH _ _ _ _ _ _ _ _ _ _ _ _
            Hhbb_tl Hwfihc Hccihc Hccifc Hwficc Hboundicc) => Hbbexpstlhm1.

  move: (bit_blast_hbexps_hccache_conjs_rec_well_formed_ccache Hhbb_tl Hwfihc)
  => Hwfhc1.
  move: (bit_blast_hbexps_hccache_conjs_rec_ccache_compatible_chain_wf_bound
           Hhbb_tl Hwfihc Hccihc Hccifc Hwficc Hboundicc)
  => [fc1 [cc1 [Hcchc1 [Hccfc1 [Hwfcc1 Hboundcc1]]]]].

  move: (bit_blast_bexp_hccache_preserve Hhbb_hd Hwfhc1 Hcchc1 Hccfc1) => Hprehm1.
  move: (vm_preserve_bound_bexps Hprehm1 Hbbexpstlhm1) => Hbbexpstlohm.
  rewrite Hbbexpstlohm andbT.

  exact: (bit_blast_bexp_hccache_bound Hhbb_hd Hwfhc1 Hcchc1 Hccfc1 Hwfcc1 Hboundcc1).
Qed.

Lemma bit_blast_hbexps_hccache_conjs_adhere
      TE es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc :
  bit_blast_hbexps_hccache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  well_formed_ccache ihc ->
  ccache_compatible ihc ifc ->
  CCacheFlatten.ccache_compatible ifc icc ->
  adhere ihm TE ->
  adhere ohm TE.
Proof.
  elim: es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc =>
  [| hd tl IH] ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc //=.
  - case=> ? ? ? ? ?; subst. move=> _ _ _ ?; assumption.
  - rewrite mapr_cons. rewrite bit_blast_hbexps_hccache_conjs_rec_rcons.
    dcase (bit_blast_hbexps_hccache_conjs_rec TE ihm ihc ihg ihcs ihlrs
                                             (mapr hash_bexp tl))
    => [[[[[hm1 hc1] hg1] hcs1] hlrs1] Hhbb_tl].
    rewrite bit_blast_hbexps_hccache_conjs_rec_singleton.
    dcase (bit_blast_bexp_hccache TE hm1 hc1 hg1 (hash_bexp hd)) =>
    [[[[[hm2 hc2] hg2] hcs2] hlrs2] Hhbb_hd]. case=> ? ? ? ? ?; subst.
    move=> Hwfihc Hccihc Hccifc Hadihm.
    move: (IH _ _ _ _ _ _ _ _ _ _ _ _ Hhbb_tl Hwfihc Hccihc Hccifc Hadihm) => Hadhm1.
    move: (bit_blast_hbexps_hccache_conjs_rec_well_formed_ccache Hhbb_tl Hwfihc)
    => Hwfhc1.
    move: (bit_blast_hbexps_hccache_conjs_rec_ccache_compatible_chain
             Hhbb_tl Hwfihc Hccihc Hccifc) => [fc1 [cc1 [Hcchc1 Hccfc1]]].
    exact: (bit_blast_bexp_hccache_adhere Hhbb_hd Hwfhc1 Hcchc1 Hccfc1 Hadhm1).
Qed.

Lemma bit_blast_hbexps_hccache_conjs_rec_conform
      TE E es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc :
  bit_blast_hbexps_hccache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  well_formed_ccache ihc ->
  ccache_compatible ihc ifc ->
  CCacheFlatten.ccache_compatible ifc icc ->
  CompCache.well_formed icc ->
  CompCache.bound icc ihm ->
  adhere ihm TE ->
  AdhereConform.conform_bexps es (mk_state E ohm) TE.
Proof.
  move=> Hhbb Hwfihc Hccihc Hccifc Hwficc Hboundicc Hadihm.
  apply: mk_state_conform_bexps.
  - exact: (bit_blast_hbexps_hccache_conjs_rec_bound Hhbb Hwfihc Hccihc Hccifc Hwficc Hboundicc).
  - exact: (bit_blast_hbexps_hccache_conjs_adhere Hhbb Hwfihc Hccihc Hccifc Hadihm).
Qed.

Lemma bit_blast_hbexps_hccache_conjs_conform TE E es ohm ohc ohg ohcs ohlrs :
  bit_blast_hbexps_hccache_conjs
    TE init_vm init_hccache init_gen (mapr hash_bexp es) =
  (ohm, ohc, ohg, ohcs, ohlrs) ->
  AdhereConform.conform_bexps es (mk_state E ohm) TE.
Proof.
  move=> Hbb.
  exact: (bit_blast_hbexps_hccache_conjs_rec_conform
            E Hbb init_hccache_well_formed init_hccache_fccache_compatible
            init_fccache_compatible init_ccache_well_formed
            init_bound_cache (init_vm_adhere TE)).
Qed.



Fixpoint mk_conjs_rec res es :=
  match es with
  | [::] => res
  | hd::tl => mk_conjs_rec (QFBV.Bconj res hd) tl
  end.

Definition mk_conjs es :=
  match es with
  | [::] => QFBV.Btrue
  | hd::tl => mk_conjs_rec hd tl
  end.

Lemma mk_conjs_rec_rcons res es e :
  mk_conjs_rec res (rcons es e) = QFBV.Bconj (mk_conjs_rec res es) e.
Proof.
  by elim: es res e => [| hd tl IH] res e //=.
Qed.

Lemma mk_conjs_rcons es e :
  mk_conjs (rcons es e) = if es == [::] then e
                          else QFBV.Bconj (mk_conjs es) e.
Proof.
  case: es e => [| hd tl] e //=. rewrite mk_conjs_rec_rcons.
  reflexivity.
Qed.

Lemma mk_conjs_rec_eval s res es :
  QFBV.eval_bexp (mk_conjs_rec res es) s = QFBV.eval_bexp res s
                                           && (QFBV.eval_bexp (mk_conjs es) s).
Proof.
  move: es res. apply: last_ind => //=.
  - move=> res. rewrite andbT. reflexivity.
  - move=> es e IH res. rewrite mk_conjs_rec_rcons /=.
    rewrite {}IH. case: (QFBV.eval_bexp res s) => //=.
    rewrite mk_conjs_rcons /=. by case: es.
Qed.

Lemma mk_conjs_eval_cons s e es :
  QFBV.eval_bexp (mk_conjs (e::es)) s = QFBV.eval_bexp e s
                                        && (QFBV.eval_bexp (mk_conjs es) s).
Proof.
  rewrite /=. rewrite mk_conjs_rec_eval. reflexivity.
Qed.

Lemma mk_conjs_eval es s :
  QFBV.eval_bexp (mk_conjs es) s <-> forall e, e \in es -> QFBV.eval_bexp e s.
Proof.
  elim: es => [| hd tl IH] //=. rewrite mk_conjs_rec_eval. split.
  - move/andP=> [Hhd Htl]. move=> e Hin. rewrite in_cons in Hin.
    case/orP: Hin => Hin.
    + rewrite (eqP Hin). assumption.
    + exact: ((proj1 IH) Htl e Hin).
  - move=> H. rewrite (H hd (mem_head hd tl)) /=.
    apply: (proj2 IH). move=> e Hin; apply: H. rewrite in_cons Hin orbT.
    reflexivity.
Qed.

Lemma bound_bexps_rcons es e m :
  bound_bexps (rcons es e) m = (bound_bexps es m) && (bound_bexp e m).
Proof.
  elim: es e => [| hd tl IH] e //=.
  - rewrite andbT. reflexivity.
  - rewrite IH. rewrite Bool.andb_assoc. reflexivity.
Qed.

Lemma mk_conjs_rec_bound res es m :
  bound_bexp res m ->
  bound_bexps es m ->
  bound_bexp (mk_conjs_rec res es) m.
Proof.
  move: es res. apply: last_ind => //=. move=> es e IH res Hbb_res.
  rewrite bound_bexps_rcons. move/andP=> [Hbb_es Hbb_e].
  rewrite mk_conjs_rec_rcons /=. by rewrite (IH _ Hbb_res Hbb_es) Hbb_e.
Qed.

Lemma mk_conjs_bound es m :
  bound_bexps es m ->
  bound_bexp (mk_conjs es) m.
Proof.
  case: es => //=. move=> e es /andP [Hbb_e Hbb_es].
  exact: (mk_conjs_rec_bound Hbb_e Hbb_es).
Qed.

Lemma mk_conjs_rec_conform e es s E :
  conform_bexp (mk_conjs_rec e es) s E =
  conform_bexp e s E && conform_bexp (mk_conjs es) s E.
Proof.
  move: es e. apply: last_ind => /=.
  - move=> e. rewrite andbT. reflexivity.
  - move=> es le IH e. rewrite mk_conjs_rec_rcons /=. rewrite {}IH.
    case: (conform_bexp e s E) => //=. rewrite mk_conjs_rcons. by case: es.
Qed.

Lemma mk_conjs_conform es s E :
  conform_bexp (mk_conjs es) s E = conform_bexps es s E.
Proof.
  elim: es => [| e es IH] //=. rewrite mk_conjs_rec_conform IH. reflexivity.
Qed.

Lemma mk_conjs_rec_well_formed TE e es :
  QFBV.well_formed_bexp (mk_conjs_rec e es) TE =
  QFBV.well_formed_bexp e TE && QFBV.well_formed_bexps es TE.
Proof.
  move: es. apply: last_ind => /=.
  - rewrite andbT. reflexivity.
  - move=> es le IH. rewrite mk_conjs_rec_rcons /=. rewrite IH.
    rewrite QFBV.well_formed_bexps_rcons. rewrite andbA. reflexivity.
Qed.

Lemma mk_conjs_well_formed TE es :
  QFBV.well_formed_bexp (mk_conjs es) TE = QFBV.well_formed_bexps es TE.
Proof.
  case: es => [| e es] //=. rewrite mk_conjs_rec_well_formed. reflexivity.
Qed.



Definition size1 {A : Type} (s : seq A) :=
  size s == 1.

Lemma size1_singleton {A : Type} (s : seq A) :
  size1 s -> exists x, s = [:: x].
Proof. case: s => [| x1 s] //=. case: s => //=. move=> _. by exists x1. Qed.

Lemma interp_cnf_interp_word E cs :
  interp_cnf E cs ->
  all size1 cs ->
  interp_word E (tflatten cs) = ones (size cs).
Proof.
  elim: cs => [| c cs IH] //=. move/andP=> [Hc Hcs]. move/andP=> [Hsc Hscs].
  rewrite tflatten_cons. move: (size1_singleton Hsc) => [x Heq]; subst.
  rewrite /rev /=. rewrite cats1. rewrite interp_word_rcons.
  rewrite ones_cons. rewrite -ones_rcons. rewrite /= orbF in Hc.
  rewrite Hc. rewrite (IH Hcs Hscs). reflexivity.
Qed.

Lemma enc_bits_eval_conjs E s ohlrs es:
  interp_cnf E ohlrs ->
  all size1 ohlrs ->
  enc_bits E (tflatten ohlrs) (mapr (fun e => QFBV.eval_bexp e s) es) ->
  QFBV.eval_bexp (mk_conjs es) s.
Proof.
  move=> Hcs Hs. rewrite /enc_bits. rewrite (interp_cnf_interp_word Hcs Hs).
  clear Hcs Hs. elim: es ohlrs => [| e es IH] ohlrs //=.
  rewrite mapr_cons. case: ohlrs => [| lr ohlrs] //=.
  - move/eqP=> H. have Heq: size ([::] : cnf) =
                            size (rcons
                                    (mapr
                                       (QFBV.eval_bexp^~ s) es) (QFBV.eval_bexp e s))
    by rewrite -H. rewrite size_rcons in Heq. discriminate.
  - rewrite ones_cons -ones_rcons. rewrite mk_conjs_rec_eval.
    move/eqP=> H. move: (rcons_inj H) => {H} [] /eqP H1 H2.
    rewrite -H2 andTb. exact: (IH _ H1).
Qed.

Lemma interp_word_interp_cnf E s es lrs :
  QFBV.eval_bexp (mk_conjs es) s ->
  size lrs = size es ->
  all size1 lrs ->
  interp_lit E lit_tt ->
  interp_word E (tflatten lrs) == mapr (QFBV.eval_bexp^~ s) es ->
  interp_cnf E (add_prelude lrs).
Proof.
  elim: es lrs => [| e es IH] [| ls lrs] //=.
  - move=> _ _ _ Htt _. rewrite add_prelude_expand /=. by rewrite Htt.
  - rewrite mk_conjs_rec_eval. move/andP=> [He Hes].
    move/eqP. rewrite eqSS. move/eqP=> Hs.
    move/andP=> [Hs1ls Hs1lrs]. move=> Htt.
    move: (size1_singleton Hs1ls) => [l Hls]; subst.
    rewrite tflatten_cons. rewrite /rev /=. rewrite cats1. rewrite interp_word_rcons.
    rewrite mapr_cons. rewrite eqseq_rcons. move/andP=> [Heqlrs Heql].
    rewrite add_prelude_cons. rewrite add_prelude_singleton /=. rewrite Htt (eqP Heql) He /=.
    exact: (IH _ Hes Hs Hs1lrs Htt Heqlrs).
Qed.


Lemma bit_blast_hbexps_hccache_conjs_rec_enc_bits
      TE E es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc s ies :
  bit_blast_hbexps_hccache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  QFBV.well_formed_bexps es TE ->
  well_formed_ccache ihc ->
  ccache_compatible ihc ifc ->
  CCacheFlatten.ccache_compatible ifc icc ->
  CompCache.well_formed icc ->
  CompCache.bound icc ihm ->
  adhere ihm TE ->
  interp_cnf E (add_prelude (tflatten ohcs)) ->
  CompCache.interp_cache_ct E icc ->
  CompCache.correct ihm icc ->
  AdhereConform.conform_bexps es s TE ->
  consistent ohm E s ->
  enc_bits E (tflatten ihlrs) (mapr (fun e => QFBV.eval_bexp e s) ies) ->
  enc_bits E (tflatten ohlrs) (mapr (fun e => QFBV.eval_bexp e s) (es ++ ies)).
Proof.
  elim: es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc =>
  [| hd tl IH] ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc //=.
  - case=> ? ? ? ? ?; subst. done.
  - rewrite mapr_cons. rewrite bit_blast_hbexps_hccache_conjs_rec_rcons.
    dcase (bit_blast_hbexps_hccache_conjs_rec TE ihm ihc ihg ihcs ihlrs
                                             (mapr hash_bexp tl))
    => [[[[[hm1 hc1] hg1] hcs1] hlrs1] Hhbb_tl].
    rewrite bit_blast_hbexps_hccache_conjs_rec_singleton.
    dcase (bit_blast_bexp_hccache TE hm1 hc1 hg1 (hash_bexp hd)) =>
    [[[[[hm2 hc2] hg2] hcs2] hlrs2] Hhbb_hd]. case=> ? ? ? ? ?; subst.
    move=> /andP [Hwf_hd Hwf_tl] Hwfihc Hccihc Hccifc Hwficc Hboundicc
          Hadihm Hsat Hcticc Hcorricc /andP [Hco_hd Hco_tl] Hcoohm Hencihlrs.
    move: (bit_blast_hbexps_hccache_conjs_rec_well_formed_ccache Hhbb_tl Hwfihc)
    => Hwfhc1.

    rewrite interp_cnf_cons /= orbF in Hsat.
    move/andP: Hsat=> [Hsat_tt Hsat].
    rewrite interp_cnf_tflatten_catrev in Hsat.
    move/andP: Hsat=> [Hsat_ofcs Hsat_hcs1].

    move: (bit_blast_hbexps_hccache_conjs_rec_ccache_compatible_full
             Hhbb_tl Hwf_tl Hwfihc Hccihc Hccifc Hwficc Hboundicc
             Hsat_hcs1 Hcticc Hcorricc)
    => [fc1 [cc1 [Hcchc1 [Hccfc1 [Hwfcc1 [Hboundcc1 [Hctcc1 Hcorrcc1]]]]]]].
    move: (bit_blast_hbexps_hccache_conjs_rec_bound
             Hhbb_tl Hwfihc Hccihc Hccifc Hwficc Hboundicc) => Hbbexp_tlhm1.
    move: (bit_blast_bexp_hccache_preserve Hhbb_hd Hwfhc1 Hcchc1 Hccfc1) => Hprehm1.
    move: (bit_blast_bexp_hccache_bound Hhbb_hd Hwfhc1 Hcchc1 Hccfc1 Hwfcc1 Hboundcc1)
    => Hbbexp_hdohm.

    dcase (bit_blast_bexp_fccache TE hm1 fc1 hg1 hd) =>
    [[[[[ofm ofc] ofg] ofcs] oflr] Hfbb_hd].
    move: (bit_blast_bexp_hccache_fccache Hwfhc1 Hcchc1 Hhbb_hd Hfbb_hd) =>
    [? [Hwfohc [Hccohc [? [? ?]]]]]; subst.
    dcase (bit_blast_bexp_ccache TE hm1 cc1 hg1 hd) =>
    [[[[[ocm occ] ocg] occs] oclr] Hcbb_hd].
    move: (bit_blast_bexp_fccache_valid Hccfc1 Hfbb_hd Hcbb_hd) =>
    [? [Hccofc [? [Heqs [Heqn ?]]]]]; subst.
    move: (bit_blast_hbexps_hccache_conjs_adhere Hhbb_tl Hwfihc Hccihc Hccifc Hadihm) => Hadhm1.
    move: (bit_blast_bexp_hccache_adhere Hhbb_hd Hwfhc1 Hcchc1 Hccfc1 Hadhm1) => Hadohm.

    rewrite (Heqs E) in Hsat_ofcs.

    move: (bit_blast_bexp_ccache_correct
             Hcbb_hd Hco_hd Hcoohm Hwf_hd Hwfcc1 (add_prelude_to Hsat_tt Hsat_ofcs)
             Hctcc1 Hcorrcc1) => Hencolr.

    rewrite tflatten_cons. rewrite {1}/rev /=. rewrite cats1.
    rewrite mapr_cons. rewrite enc_bits_rcons.
    rewrite Hencolr andbT.
    move: (vm_preserve_consistent Hprehm1 Hcoohm) => Hcohm1.
    apply: (IH _ _ _ _ _ _ _ _ _ _ _ _
               Hhbb_tl Hwf_tl Hwfihc Hccihc Hccifc Hwficc Hboundicc
               Hadihm _ Hcticc Hcorricc Hco_tl Hcohm1 Hencihlrs).
    rewrite add_prelude_expand. rewrite /interp_lit /=.
    by rewrite Hsat_tt Hsat_hcs1.
Qed.

Lemma bit_blast_hbexps_hccache_conjs_enc_bits TE E es ohm ohc ohg ohcs ohlrs s :
  bit_blast_hbexps_hccache_conjs
    TE init_vm init_hccache init_gen
    (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  QFBV.well_formed_bexps es TE ->
  interp_cnf E (add_prelude (tflatten ohcs)) ->
  AdhereConform.conform_bexps es s TE ->
  consistent ohm E s ->
  enc_bits E (tflatten ohlrs) (mapr (fun e => QFBV.eval_bexp e s) es).
Proof.
  move=> Hbb Hwf_es Hcs Hco_es Hcoohm. rewrite -(cats0 es).
  apply: (bit_blast_hbexps_hccache_conjs_rec_enc_bits
            Hbb Hwf_es init_hccache_well_formed init_hccache_fccache_compatible
            init_fccache_compatible init_ccache_well_formed
            init_bound_cache (init_vm_adhere TE) Hcs (init_interp_cache_ct E)
            (init_correct init_vm) Hco_es Hcoohm). done.
Qed.


Lemma bit_blast_hbexps_hccache_conjs_rec_eval_conjs
      TE E es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc s :
  bit_blast_hbexps_hccache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  QFBV.well_formed_bexps es TE ->
  well_formed_ccache ihc ->
  ccache_compatible ihc ifc ->
  CCacheFlatten.ccache_compatible ifc icc ->
  CompCache.well_formed icc ->
  CompCache.bound icc ihm ->
  adhere ihm TE ->
  interp_cnf E (add_prelude (tflatten (ohlrs :: ohcs))) ->
  CompCache.interp_cache_ct E icc ->
  CompCache.correct ihm icc ->
  AdhereConform.conform_bexps es s TE ->
  consistent ohm E s ->
  QFBV.eval_bexp (mk_conjs es) s.
Proof.
  elim: es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc =>
  [| hd tl IH] ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc //=.
  rewrite mapr_cons. rewrite bit_blast_hbexps_hccache_conjs_rec_rcons.
  dcase (bit_blast_hbexps_hccache_conjs_rec TE ihm ihc ihg ihcs ihlrs
                                           (mapr hash_bexp tl))
  => [[[[[hm1 hc1] hg1] hcs1] hlrs1] Hhbb_tl].
  rewrite bit_blast_hbexps_hccache_conjs_rec_singleton.
  dcase (bit_blast_bexp_hccache TE hm1 hc1 hg1 (hash_bexp hd)) =>
  [[[[[hm2 hc2] hg2] hcs2] hlrs2] Hhbb_hd]. case=> ? ? ? ? ?; subst.
  move=> /andP [Hwf_hd Hwf_tl] Hwfihc Hccihc Hccifc Hwficc Hboundicc
          Hadihm Hsat Hcticc Hcorricc /andP [Hco_hd Hco_tl] Hcoohm.
  move: (bit_blast_hbexps_hccache_conjs_rec_well_formed_ccache Hhbb_tl Hwfihc)
  => Hwfhc1.

  rewrite interp_cnf_cons /= orbF in Hsat.
  move/andP: Hsat=> [Hsat_tt Hsat].
  rewrite interp_cnf_tflatten_cons in Hsat.
  move/andP: Hsat=> [Hsat1 Hsat2].
  rewrite interp_cnf_cons /= orbF in Hsat1.
  move/andP: Hsat1=> [Hsat_olr Hsat_hlrs1].
  rewrite interp_cnf_tflatten_catrev in Hsat2.
  move/andP: Hsat2=> [Hsat_ofcs Hsat_hcs1].

  move: (bit_blast_hbexps_hccache_conjs_rec_ccache_compatible_full
           Hhbb_tl Hwf_tl Hwfihc Hccihc Hccifc Hwficc Hboundicc
           Hsat_hcs1 Hcticc Hcorricc)
  => [fc1 [cc1 [Hcchc1 [Hccfc1 [Hwfcc1 [Hboundcc1 [Hctcc1 Hcorrcc1]]]]]]].
  move: (bit_blast_hbexps_hccache_conjs_rec_bound
           Hhbb_tl Hwfihc Hccihc Hccifc Hwficc Hboundicc) => Hbbexp_tlhm1.
  move: (bit_blast_bexp_hccache_preserve Hhbb_hd Hwfhc1 Hcchc1 Hccfc1) => Hprehm1.
  move: (bit_blast_bexp_hccache_bound Hhbb_hd Hwfhc1 Hcchc1 Hccfc1 Hwfcc1 Hboundcc1)
  => Hbbexp_hdohm.

  rewrite mk_conjs_rec_eval. apply/andP; split.
  - dcase (bit_blast_bexp_fccache TE hm1 fc1 hg1 hd) =>
    [[[[[ofm ofc] ofg] ofcs] oflr] Hfbb_hd].
    move: (bit_blast_bexp_hccache_fccache Hwfhc1 Hcchc1 Hhbb_hd Hfbb_hd) =>
    [? [Hwfohc [Hccohc [? [? ?]]]]]; subst.
    dcase (bit_blast_bexp_ccache TE hm1 cc1 hg1 hd) =>
    [[[[[ocm occ] ocg] occs] oclr] Hcbb_hd].
    move: (bit_blast_bexp_fccache_valid Hccfc1 Hfbb_hd Hcbb_hd) =>
    [? [Hccofc [? [Heqs [Heqn ?]]]]]; subst.
    move: (bit_blast_hbexps_hccache_conjs_adhere Hhbb_tl Hwfihc Hccihc Hccifc Hadihm) => Hadhm1.
    move: (bit_blast_bexp_hccache_adhere Hhbb_hd Hwfhc1 Hcchc1 Hccfc1 Hadhm1) => Hadohm.

    rewrite (Heqs E) in Hsat_ofcs.

    move: (bit_blast_bexp_ccache_correct
             Hcbb_hd Hco_hd Hcoohm Hwf_hd Hwfcc1 (add_prelude_to Hsat_tt Hsat_ofcs)
             Hctcc1 Hcorrcc1).
    rewrite /enc_bit. rewrite Hsat_olr. rewrite eq_sym. by move/eqP=> ->.
  - move: (vm_preserve_consistent Hprehm1 Hcoohm) => Hcohm1.
    apply: (IH _ _ _ _ _ _ _ _ _ _ _ _
               Hhbb_tl Hwf_tl Hwfihc Hccihc Hccifc Hwficc Hboundicc
               Hadihm _ Hcticc Hcorricc Hco_tl Hcohm1).
    rewrite add_prelude_expand interp_cnf_tflatten_cons /=.
    rewrite Hsat_tt /=. by rewrite Hsat_hlrs1 Hsat_hcs1.
Qed.

Lemma bit_blast_hbexps_hccache_conjs_rec_mk_state
      TE E es ihm ihc ihg ihcs ihlrs ohm ohc ohg ohcs ohlrs ifc icc :
  bit_blast_hbexps_hccache_conjs_rec
    TE ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  QFBV.well_formed_bexps es TE ->
  well_formed_ccache ihc ->
  ccache_compatible ihc ifc ->
  CCacheFlatten.ccache_compatible ifc icc ->
  CompCache.well_formed icc ->
  CompCache.bound icc ihm ->
  adhere ihm TE ->
  interp_cnf E (add_prelude (tflatten (ohlrs :: ohcs))) ->
  CompCache.interp_cache_ct E icc ->
  CompCache.correct ihm icc ->
  QFBV.eval_bexp (mk_conjs es) (mk_state E ohm).
Proof.
  move=> Hbb Hwf_es Hwfihc Hccihc Hccifc Hwficc Hboundicc Hadihm Hcs Hcticc Hcorricc.
  apply: (bit_blast_hbexps_hccache_conjs_rec_eval_conjs
            Hbb Hwf_es Hwfihc Hccihc Hccifc Hwficc Hboundicc Hadihm Hcs Hcticc Hcorricc).
  - exact: (bit_blast_hbexps_hccache_conjs_rec_conform
              _ Hbb Hwfihc Hccihc Hccifc Hwficc Hboundicc Hadihm).
  - exact: mk_state_consistent.
Qed.

Lemma bit_blast_hbexps_hccache_conjs_mk_state TE E es ohm ohc ohg ohcs ohlrs :
  bit_blast_hbexps_hccache_conjs
    TE init_vm init_hccache init_gen
    (mapr hash_bexp es) = (ohm, ohc, ohg, ohcs, ohlrs) ->
  QFBV.well_formed_bexps es TE ->
  interp_cnf E (add_prelude (tflatten (ohlrs :: ohcs))) ->
  QFBV.eval_bexp (mk_conjs es) (mk_state E ohm).
Proof.
  rewrite /bit_blast_hbexps_hccache_conjs. move=> Hbb Hwf Hcs.
  exact: (bit_blast_hbexps_hccache_conjs_rec_mk_state
            Hbb Hwf init_hccache_well_formed init_hccache_fccache_compatible
            init_fccache_compatible init_ccache_well_formed
            init_bound_cache (init_vm_adhere TE) Hcs
            (init_interp_cache_ct E) (init_correct init_vm)).
Qed.


(* Soundness of bit_blast_hbexps_hccache_conjs *)

Lemma bit_blast_hbexps_hccache_conjs_sat_sound TE es m c g cs lrs :
  bit_blast_hbexps_hccache_conjs
    TE init_vm init_hccache init_gen (mapr hash_bexp es) = (m, c, g, cs, lrs) ->
  QFBV.well_formed_bexps es TE ->
  (sat (add_prelude (tflatten (lrs::cs)))) ->
  (exists s, AdhereConform.conform_bexps es s TE /\
             QFBV.eval_bexp (mk_conjs es) s).
Proof.
  move=> Hhbb Hwf [E Hcs]. exists (mk_state E m). split.
  - exact: (bit_blast_hbexps_hccache_conjs_conform _ Hhbb).
  - exact: (bit_blast_hbexps_hccache_conjs_mk_state Hhbb Hwf Hcs).
Qed.



Definition bit_blast_bexps_hccache_conjs TE es : cnf :=
  let '(m', c', g', cs, lrs) :=
      bit_blast_hbexps_hccache_conjs
        TE init_vm init_hccache init_gen (mapr hash_bexp es) in
  add_prelude (tflatten (lrs::cs)).

Theorem bit_blast_bexps_hccache_conjs_sat_sound TE es :
  QFBV.well_formed_bexps es TE ->
  (sat (bit_blast_bexps_hccache_conjs TE es)) ->
  (exists s, AdhereConform.conform_bexps es s TE /\
             QFBV.eval_bexp (mk_conjs es) s).
Proof.
  move=> Hwf. rewrite /bit_blast_bexps_hccache_conjs.
  dcase (bit_blast_hbexps_hccache_conjs
           TE init_vm init_hccache init_gen
           (mapr hash_bexp es)) => [[[[[m c] g] cs] lrs] Hbb].
  move=> Hsat. exact: (bit_blast_hbexps_hccache_conjs_sat_sound Hbb Hwf Hsat).
Qed.



(* ==== mk_env_exp_hccache and mk_env_bexp_hccache ==== *)

Fixpoint mk_env_exp_hccache E s m c g (e : hexp) : env * vm * ccache * generator * seq cnf * word :=
  (* = mk_env_exp_nocet = *)
  let mk_env_exp_nocet E s m c g (e : hexp) : env * vm * ccache * generator * seq cnf * word * seq cnf :=
      match e with
      | epair (HEvar v) _ =>
        match find_het e c with
        | Some (cs, ls) => (E, m, c, g, cs, ls, cs)
        | None => match SSAVM.find v m with
                  | None => let '(E', g', cs, rs) := mk_env_var E g (SSAStore.acc v s) v in
                            (E', SSAVM.add v rs m, add_het e [:: cs] rs c, g', [:: cs], rs, [:: cs])
                  | Some rs => (E, m, add_het e [::] rs c, g, [::], rs, [::])
                  end
        end
      | epair (HEconst bs) _ =>
        match find_het e c with
        | Some (cs, ls) => (E, m, c, g, cs, ls, cs)
        | None => let '(E', g', cs, rs) := mk_env_const E g bs in
                  (E', m, add_het e [:: cs] rs c, g', [:: cs], rs, [:: cs])
        end
      | epair (HEunop op e1) _ =>
        let '(E1, m1, c1, g1, cs1, ls1) := mk_env_exp_hccache E s m c g e1 in
        match find_het e c1 with
        | Some (csop, lsop) => (E1, m1, c1, g1, catrev cs1 csop, lsop, csop)
        | None =>
          let '(Eop, gop, csop, lsop) := mk_env_eunop op E1 g1 ls1 in
          (Eop, m1, add_het e [:: csop] lsop c1, gop,
           catrev cs1 [:: csop], lsop, [:: csop])
        end
      | epair (HEbinop op e1 e2) _ =>
        let '(E1, m1, c1, g1, cs1, ls1) := mk_env_exp_hccache E s m c g e1 in
        let '(E2, m2, c2, g2, cs2, ls2) := mk_env_exp_hccache E1 s m1 c1 g1 e2 in
        match find_het e c2 with
        | Some (csop, lsop) => (E2, m2, c2, g2, catrev cs1 (catrev cs2 csop), lsop, csop)
        | None =>
          let '(Eop, gop, csop, lsop) := mk_env_ebinop op E2 g2 ls1 ls2 in
          (Eop, m2, add_het e [:: csop] lsop c2, gop,
           catrev cs1 (catrev cs2 [:: csop]), lsop, [:: csop])
        end
      | epair (HEite b e1 e2) _ =>
        let '(Eb, mb, cb, gb, csb, lb) := mk_env_bexp_hccache E s m c g b in
        let '(E1, m1, c1, g1, cs1, ls1) := mk_env_exp_hccache Eb s mb cb gb e1 in
        let '(E2, m2, c2, g2, cs2, ls2) := mk_env_exp_hccache E1 s m1 c1 g1 e2 in
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
            (E', m', CCacheHash.add_cet e csop lrs c', g', cs, lrs)
  end
with
mk_env_bexp_hccache E s m c g (e : hbexp) : env * vm * ccache * generator * seq cnf * literal :=
  (* = mk_env_bexp_nocbt = *)
  let mk_env_bexp_nocbt E s m c g (e : hbexp) : env * vm * ccache * generator * seq cnf * literal * seq cnf :=
      match e with
      | bpair HBfalse _ =>
        match find_hbt e c with
        | Some (cs, l) => (E, m, c, g, cs, l, cs)
        | None => (E, m, add_hbt e [::] lit_ff c, g, [::], lit_ff, [::])
        end
      | bpair HBtrue _ =>
        match find_hbt e c with
        | Some (cs, l) => (E, m, c, g, cs, l, cs)
        | None => (E, m, add_hbt e [::] lit_tt c, g, [::], lit_tt, [::])
        end
      | bpair (HBbinop op e1 e2) _ =>
        let '(E1, m1, c1, g1, cs1, ls1) := mk_env_exp_hccache E s m c g e1 in
        let '(E2, m2, c2, g2, cs2, ls2) := mk_env_exp_hccache E1 s m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (E2, m2, c2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None =>
          let '(Eop, gop, csop, lop) := mk_env_bbinop op E2 g2 ls1 ls2 in
          (Eop, m2, add_hbt e [:: csop] lop c2, gop,
           catrev cs1 (catrev cs2 [:: csop]), lop, [:: csop])
        end
      | bpair (HBlneg e1) _ =>
        let '(E1, m1, c1, g1, cs1, l1) := mk_env_bexp_hccache E s m c g e1 in
        match find_hbt e c1 with
        | Some (csop, lop) => (E1, m1, c1, g1, catrev cs1 csop, lop, csop)
        | None => let '(Eop, gop, csop, lop) := mk_env_lneg E1 g1 l1 in
                  (Eop, m1, add_hbt e [:: csop] lop c1, gop,
                   catrev cs1 [:: csop], lop, [:: csop])
        end
      | bpair (HBconj e1 e2) _ =>
        let '(E1, m1, c1, g1, cs1, l1) := mk_env_bexp_hccache E s m c g e1 in
        let '(E2, m2, c2, g2, cs2, l2) := mk_env_bexp_hccache E1 s m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (E2, m2, c2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None => let '(Eop, gop, csop, lop) := mk_env_conj E2 g2 l1 l2 in
                  (Eop, m2, add_hbt e [:: csop] lop c2, gop,
                   catrev cs1 (catrev cs2 [:: csop]), lop, [:: csop])
        end
      | bpair (HBdisj e1 e2) _ =>
        let '(E1, m1, c1, g1, cs1, l1) := mk_env_bexp_hccache E s m c g e1 in
        let '(E2, m2, c2, g2, cs2, l2) := mk_env_bexp_hccache E1 s m1 c1 g1 e2 in
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
            (E', m', CCacheHash.add_cbt e csop lr c', g', cs, lr)
  end.


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
  | |- context f [bit_blast_exp_hccache ?E ?m ?ec ?g ?e] =>
    let m' := fresh in
    let ec' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lrs := fresh in
    let H := fresh in
    dcase (bit_blast_exp_hccache E m ec g e) =>
    [[[[[m' ec'] g'] cs] lrs] H]
  | |- context f [bit_blast_bexp_hccache ?E ?m ?ec ?g ?e] =>
    let m' := fresh in
    let ec' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lr := fresh in
    let H := fresh in
    dcase (bit_blast_bexp_hccache E m ec g e) =>
    [[[[[m' ec'] g'] cs] lr] H]
  | |- context f [bit_blast_exp_fccache ?E ?m ?c ?g ?e] =>
    let m' := fresh in
    let c' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lrs := fresh in
    let H := fresh in
    dcase (bit_blast_exp_fccache E m c g e) =>
    [[[[[m' c'] g'] cs] lrs] H]
  | |- context f [bit_blast_bexp_fccache ?E ?m ?c ?g ?e] =>
    let m' := fresh in
    let c' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lr := fresh in
    let H := fresh in
    dcase (bit_blast_bexp_fccache E m c g e) =>
    [[[[[m' c'] g'] cs] lr] H]
  (**)
  | |- _ => dcase_bb_base
  end.

Ltac dcase_mk_env_ccache :=
  match goal with
  (**)
  | |- context f [SSAVM.find ?v ?m] =>
    let lrs := fresh in
    case: (SSAVM.find v m) => [lrs|]
  | |- context f [mk_env_exp_hccache ?E ?s ?m ?ec ?g ?e] =>
    let E' := fresh in
    let m' := fresh in
    let ec' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lrs := fresh in
    let H := fresh in
    dcase (mk_env_exp_hccache E s m ec g e) =>
    [[[[[[E' m'] ec'] g'] cs] lrs] H]
  | |- context f [mk_env_bexp_hccache ?E ?s ?m ?ec ?g ?e] =>
    let E' := fresh in
    let m' := fresh in
    let ec' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lr := fresh in
    let H := fresh in
    dcase (mk_env_bexp_hccache E s m ec g e) =>
    [[[[[[E' m'] ec'] g'] cs] lr] H]
  | |- context f [mk_env_exp_fccache ?m ?c ?s ?E ?g ?e] =>
    let m' := fresh in
    let c' := fresh in
    let E' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lrs := fresh in
    let H := fresh in
    dcase (mk_env_exp_ccache m c s E g e) =>
    [[[[[[m' c'] E'] g'] cs] lrs] H]
  | |- context f [mk_env_bexp_fccache ?m ?c ?s ?E ?g ?e] =>
    let m' := fresh in
    let c' := fresh in
    let E' := fresh in
    let g' := fresh in
    let cs := fresh in
    let lr := fresh in
    let H := fresh in
    dcase (mk_env_bexp_fccache m c s E g e) =>
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
    | H1 : bit_blast_exp_hccache ?E ?m ?c ?g ?e = (?m1, ?c1, ?g1, ?cs1, ?lrs1),
      H2 : bit_blast_exp_hccache ?E ?m ?c ?g ?e = (?m2, ?c2, ?g2, ?cs2, ?lrs2) |- _ =>
      rewrite H1 in H2; case: H2 => ? ? ? ? ?; subst
    | H1 : bit_blast_bexp_hccache ?E ?m ?c ?g ?e = (?m1, ?c1, ?g1, ?cs1, ?lr1),
      H2 : bit_blast_bexp_hccache ?E ?m ?c ?g ?e = (?m2, ?c2, ?g2, ?cs2, ?lr2) |- _ =>
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
    | mk_env_exp_hccache_is_bit_blast_exp_hccache :
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
            mk_env_exp_hccache iE s im ic ig (hash_exp e) =
            (oE, om, oc, og, ocs, olrs) ->
            bit_blast_exp_hccache TE im ic ig (hash_exp e) =
            (om, oc, og, ocs, olrs)),
        Hco : is_true (AdhereConform.conform_exp ?e ?s ?TE),
        Hwf : is_true (QFBV.well_formed_exp ?e ?TE),
        Henv : mk_env_exp_hccache ?iE ?s ?im ?ic ?ig (hash_exp ?e) = _ |- _ =>
      let H := fresh "H" in
      (move: (mk_env_exp_hccache_is_bit_blast_exp_hccache _ _ _ _ _ _ _ _ _ _ _ _ _
                                                          Hco Hwf Henv) => H);
      clear Henv
    | mk_env_bexp_hccache_is_bit_blast_bexp_hccache :
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
            mk_env_bexp_hccache iE s im ic ig (hash_bexp e) =
            (oE, om, oc, og, ocs, olr) ->
            bit_blast_bexp_hccache TE im ic ig (hash_bexp e) =
            (om, oc, og, ocs, olr)),
        Hco : is_true (AdhereConform.conform_bexp ?e ?s ?TE),
        Hwf : is_true (QFBV.well_formed_bexp ?e ?TE),
        Henv : mk_env_bexp_hccache ?iE ?s ?im ?ic ?ig (hash_bexp ?e) = _ |- _ =>
      let H := fresh "H" in
      (move: (mk_env_bexp_hccache_is_bit_blast_bexp_hccache _ _ _ _ _ _ _ _ _ _ _ _ _
                                                            Hco Hwf Henv) => H);
      clear Henv
    | |- _ => dcase_bb_ccache || dcase_mk_env_ccache
    end.

Lemma mk_env_exp_hccache_is_bit_blast_exp_hccache
      e s TE iE im ic ig oE om oc og ocs olrs :
  AdhereConform.conform_exp e s TE ->
  QFBV.well_formed_exp e TE ->
  mk_env_exp_hccache iE s im ic ig (hash_exp e) = (oE, om, oc, og, ocs, olrs) ->
  bit_blast_exp_hccache TE im ic ig (hash_exp e) = (om, oc, og, ocs, olrs)
with
mk_env_bexp_hccache_is_bit_blast_bexp_hccache
      e s TE iE im ic ig oE om oc og ocs olr :
  AdhereConform.conform_bexp e s TE ->
  QFBV.well_formed_bexp e TE ->
  mk_env_bexp_hccache iE s im ic ig (hash_bexp e) = (oE, om, oc, og, ocs, olr) ->
  bit_blast_bexp_hccache TE im ic ig (hash_bexp e) = (om, oc, og, ocs, olr).
Proof.
  (* mk_env_exp_hccache_is_bit_blast_exp_hccache *)
  case: e => //=.
  - move=> v Hs Hm. by myauto.
  - move=> bs _ _. by myauto.
  - move=> op e Hco Hwf. by myauto.
  - move=> op e1 e2 /andP [Hco1 Hco2] /andP [/andP [/andP [Hwf1 Hwf2] Hwfs1] Hwfs2].
    by myauto.
  - move=> e1 e2 e3 /andP [/andP [Hco1 Hco2] Hco3] /andP [/andP [/andP [Hwf1 Hwf2] Hwf3] Hwfs].
    by myauto.
  (* mk_env_bexp_fccache_is_bit_blast_bexp_hccache *)
  case: e => //=.
  - move=> _ _. by myauto.
  - move=> _ _. by myauto.
  - move=> op e1 e2 /andP [Hco1 Hco2] /andP [/andP [Hwf1 Hwf2] Hwfs]. by myauto.
  - move=> e Hco Hwf. by myauto.
  - move=> e1 e2 /andP [Hco1 Hco2] /andP [Hwf1 Hwf2]. by myauto.
  - move=> e1 e2 /andP [Hco1 Hco2] /andP [Hwf1 Hwf2]. by myauto.
Qed.

Lemma mk_env_exp_hccache_fccache
      iE s im ihc ifc ig e ohE ofE ohm ohc ohg ohcs ohlrs ofm ofc ofg ofcs oflrs :
  well_formed_ccache ihc ->
  ccache_compatible ihc ifc ->
  mk_env_exp_hccache iE s im ihc ig (hash_exp e) = (ohE, ohm, ohc, ohg, ohcs, ohlrs) ->
  mk_env_exp_fccache iE s im ifc ig e = (ofE, ofm, ofc, ofg, ofcs, oflrs) ->
  ohE = ofE
  /\ ohm = ofm
  /\ well_formed_ccache ohc
  /\ ccache_compatible ohc ofc
  /\ ohg = ofg
  /\ ohcs = ofcs
  /\ ohlrs = oflrs
with
mk_env_bexp_hccache_fccache
  iE s im ihc ifc ig e ohE ofE ohm ohc ohg ohcs ohlr ofm ofc ofg ofcs oflr :
  well_formed_ccache ihc ->
  ccache_compatible ihc ifc ->
  mk_env_bexp_hccache iE s im ihc ig (hash_bexp e) = (ohE, ohm, ohc, ohg, ohcs, ohlr) ->
  mk_env_bexp_fccache iE s im ifc ig e = (ofE, ofm, ofc, ofg, ofcs, oflr) ->
  ohE = ofE
  /\ ohm = ofm
  /\ well_formed_ccache ohc
  /\ ccache_compatible ohc ofc
  /\ ohg = ofg
  /\ ohcs = ofcs
  /\ ohlr = oflr.
Proof.
  (* mk_env_exp_hccache_fccache *)
  - case: e => /=.
    + move=> v Hwf Hcc.
      replace (epair (HEvar v) 1) with (hash_exp (QFBV.Evar v)) by reflexivity.
      rewrite (ccache_compatible_find_cet _ Hcc).
      rewrite (ccache_compatible_find_het _ Hcc).
      case: (CCacheFlatten.find_cet (QFBV.Evar v) ifc).
      * move=> [cs ls] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst. done.
      * case: (CCacheFlatten.find_het (QFBV.Evar v) ifc).
        -- move=> [cs ls] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
        -- case Hvm: (SSAVM.find v im).
           ++ move=> [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
                by t_auto.
           ++ dcase (mk_env_var iE ig (SSAStore.acc v s) v) => [[[[E1 g1] cs1] rs1] Henvv].
              move=> [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
                by t_auto.
    + move=> bs Hf Hcc.
      replace (epair (HEconst bs) 1) with (hash_exp (QFBV.Econst bs)) by reflexivity.
      rewrite (ccache_compatible_find_cet _ Hcc).
      rewrite (ccache_compatible_find_het _ Hcc).
      case: (CCacheFlatten.find_cet (QFBV.Econst bs) ifc).
      * move=> [cs ls] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst. done.
      * case: (CCacheFlatten.find_het (QFBV.Econst bs) ifc).
        -- move=> [cs ls] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
        -- move=> [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
    + move=> op e Hwf Hcc.
      replace (epair (HEunop op (hash_exp e)) (ehval (hash_exp e) + 1))
        with (hash_exp (QFBV.Eunop op e)) by reflexivity.
      rewrite (ccache_compatible_find_cet _ Hcc).
      case: (CCacheFlatten.find_cet (QFBV.Eunop op e) ifc).
      * move=> [cs ls] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst. done.
      * dcase (mk_env_exp_hccache iE s im ihc ig (hash_exp e)) =>
        [[[[[[E1 hm1] hc1] hg1] hcs1] hls1] Hhenv].
        dcase (mk_env_exp_fccache iE s im ifc ig e) =>
        [[[[[[fE1 fm1] fc1] fg1] fcs1] fls1] Hfenv].
        move: (mk_env_exp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                          Hwf Hcc Hhenv Hfenv).
        move=> [? [? [Hwf1 [Hcc1 [? [? ?]]]]]]; subst.
        rewrite (ccache_compatible_find_het _ Hcc1).
        case: (CCacheFlatten.find_het (QFBV.Eunop op e) fc1).
        -- move=> [cs ls] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
        -- dcase (mk_env_eunop op fE1 fg1 fls1) => [[[[Eop gop] csop] lsop] Henvop].
           move=> [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
    + move=> op e1 e2 Hwf Hcc.
      replace (epair (HEbinop op (hash_exp e1) (hash_exp e2))
                     (ehval (hash_exp e1) + ehval (hash_exp e2) + 1))
        with (hash_exp (QFBV.Ebinop op e1 e2)) by reflexivity.
      rewrite (ccache_compatible_find_cet _ Hcc).
      case: (CCacheFlatten.find_cet (QFBV.Ebinop op e1 e2) ifc).
      * move=> [cs ls] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst. done.
      * dcase (mk_env_exp_hccache iE s im ihc ig (hash_exp e1)) =>
        [[[[[[hE1 hm1] hc1] hg1] hcs1] hls1] Hhenv1].
        dcase (mk_env_exp_hccache hE1 s hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[[hE2 hm2] hc2] hg2] hcs2] hls2] Hhenv2].
        dcase (mk_env_exp_fccache iE s im ifc ig e1) =>
        [[[[[[fE1 fm1] fc1] fg1] fcs1] fls1] Hfenv1].
        dcase (mk_env_exp_fccache fE1 s fm1 fc1 fg1 e2) =>
        [[[[[[fE2 fm2] fc2] fg2] fcs2] fls2] Hfenv2].
        move: (mk_env_exp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                          Hwf Hcc Hhenv1 Hfenv1).
        move=> [? [? [Hwf1 [Hcc1 [? [? ?]]]]]]; subst.
        move: (mk_env_exp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf1 Hcc1 Hhenv2 Hfenv2).
        move=> [? [? [Hwf2 [Hcc2 [? [? ?]]]]]]; subst.
        rewrite (ccache_compatible_find_het _ Hcc2).
        case: (CCacheFlatten.find_het (QFBV.Ebinop op e1 e2) fc2).
        -- move=> [cs ls] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
        -- dcase (mk_env_ebinop op fE2 fg2 fls1 fls2) => [[[[Eop gop] csop] lsop] Henvop].
           move=> [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
    + move=> e1 e2 e3 Hwf Hcc.
      replace (epair (HEite (hash_bexp e1) (hash_exp e2) (hash_exp e3))
                     (bhval (hash_bexp e1) +
                      ehval (hash_exp e2) + ehval (hash_exp e3) + 1)) with
          (hash_exp (QFBV.Eite e1 e2 e3)) by reflexivity.
      rewrite (ccache_compatible_find_cet _ Hcc).
      case: (CCacheFlatten.find_cet (QFBV.Eite e1 e2 e3) ifc).
      * move=> [cs ls] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst. done.
      * dcase (mk_env_bexp_hccache iE s im ihc ig (hash_bexp e1)) =>
        [[[[[[hE1 hm1] hc1] hg1] hcs1] hls1] Hhenv1].
        dcase (mk_env_exp_hccache hE1 s hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[[hE2 hm2] hc2] hg2] hcs2] hls2] Hhenv2].
        dcase (mk_env_exp_hccache hE2 s hm2 hc2 hg2 (hash_exp e3)) =>
        [[[[[[hE3 hm3] hc3] hg3] hcs3] hls3] Hhenv3].
        dcase (mk_env_bexp_fccache iE s im ifc ig e1) =>
        [[[[[[fE1 fm1] fc1] fg1] fcs1] fls1] Hfenv1].
        dcase (mk_env_exp_fccache fE1 s fm1 fc1 fg1 e2) =>
        [[[[[[fE2 fm2] fc2] fg2] fcs2] fls2] Hfenv2].
        dcase (mk_env_exp_fccache fE2 s fm2 fc2 fg2 e3) =>
        [[[[[[fE3 fm3] fc3] fg3] fcs3] fls3] Hfenv3].
        move: (mk_env_bexp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf Hcc Hhenv1 Hfenv1).
        move=> [? [? [Hwf1 [Hcc1 [? [? ?]]]]]]; subst.
        move: (mk_env_exp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf1 Hcc1 Hhenv2 Hfenv2).
        move=> [? [? [Hwf2 [Hcc2 [? [? ?]]]]]]; subst.
        move: (mk_env_exp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf2 Hcc2 Hhenv3 Hfenv3).
        move=> [? [? [Hwf3 [Hcc3 [? [? ?]]]]]]; subst.
        rewrite (ccache_compatible_find_het _ Hcc3).
        case: (CCacheFlatten.find_het (QFBV.Eite e1 e2 e3) fc3).
        -- move=> [cs ls] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
        -- dcase (mk_env_ite fE3 fg3 fls1 fls2 fls3) => [[[[Eop gop] csop] lsop] Henvop].
           move=> [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
  (* mk_env_bexp_hccache_fccache *)
  - case: e => /=.
    + move=> Hwf Hcc.
      replace (bpair HBfalse 1) with (hash_bexp QFBV.Bfalse) by reflexivity.
      rewrite (ccache_compatible_find_cbt _ Hcc).
      case: (CCacheFlatten.find_cbt QFBV.Bfalse ifc).
      * move=> [cs lr] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst. done.
      * rewrite (ccache_compatible_find_hbt _ Hcc).
        case: (CCacheFlatten.find_hbt QFBV.Bfalse ifc).
        -- move=> [cs lr] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
        -- move=> [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
    + move=> Hwf Hcc.
      replace (bpair HBtrue 1) with (hash_bexp QFBV.Btrue) by reflexivity.
      rewrite (ccache_compatible_find_cbt _ Hcc).
      case: (CCacheFlatten.find_cbt QFBV.Btrue ifc).
      * move=> [cs lr] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst. done.
      * rewrite (ccache_compatible_find_hbt _ Hcc).
        case: (CCacheFlatten.find_hbt QFBV.Btrue ifc).
        -- move=> [cs lr] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
        -- move=> [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
    + move=> op e1 e2 Hwf Hcc.
      replace (bpair (HBbinop op (hash_exp e1) (hash_exp e2))
                     (ehval (hash_exp e1) + ehval (hash_exp e2) + 1)) with
          (hash_bexp (QFBV.Bbinop op e1 e2)) by reflexivity.
      rewrite (ccache_compatible_find_cbt _ Hcc).
      case: (CCacheFlatten.find_cbt (QFBV.Bbinop op e1 e2) ifc).
      * move=> [cs lr] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst. done.
      * dcase (mk_env_exp_hccache iE s im ihc ig (hash_exp e1)) =>
        [[[[[[hE1 hm1] hc1] hg1] hcs1] hlr1] Hhenv1].
        dcase (mk_env_exp_hccache hE1 s hm1 hc1 hg1 (hash_exp e2)) =>
        [[[[[[hE2 hm2] hc2] hg2] hcs2] hlr2] Hhenv2].
        dcase (mk_env_exp_fccache iE s im ifc ig e1) =>
        [[[[[[fE1 fm1] fc1] fg1] fcs1] flr1] Hfenv1].
        dcase (mk_env_exp_fccache fE1 s fm1 fc1 fg1 e2) =>
        [[[[[[fE2 fm2] fc2] fg2] fcs2] flr2] Hfenv2].
        move: (mk_env_exp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf Hcc Hhenv1 Hfenv1).
        move=> [? [? [Hwf1 [Hcc1 [? [? ?]]]]]]; subst.
        move: (mk_env_exp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf1 Hcc1 Hhenv2 Hfenv2).
        move=> [? [? [Hwf2 [Hcc2 [? [? ?]]]]]]; subst.
        rewrite (ccache_compatible_find_hbt _ Hcc2).
        case: (CCacheFlatten.find_hbt (QFBV.Bbinop op e1 e2) fc2).
        -- move=> [cs lr] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
        -- dcase (mk_env_bbinop op fE2 fg2 flr1 flr2) => [[[[Eop gop] csop] lop] Henvop].
           move=> [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
    + move=> e Hwf Hcc.
      replace (bpair (HBlneg (hash_bexp e)) (bhval (hash_bexp e) + 1)) with
          (hash_bexp (QFBV.Blneg e)) by reflexivity.
      rewrite (ccache_compatible_find_cbt _ Hcc).
      case: (CCacheFlatten.find_cbt (QFBV.Blneg e) ifc).
      * move=> [cs lr] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst. done.
      * dcase (mk_env_bexp_hccache iE s im ihc ig (hash_bexp e)) =>
        [[[[[[hE1 hm1] hc1] hg1] hcs1] hlr1] Hhenv1].
        dcase (mk_env_bexp_fccache iE s im ifc ig e) =>
        [[[[[[fE1 fm1] fc1] fg1] fcs1] flr1] Hfenv1].
        move: (mk_env_bexp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                            Hwf Hcc Hhenv1 Hfenv1).
        move=> [? [? [Hwf1 [Hcc1 [? [? ?]]]]]]; subst.
        rewrite (ccache_compatible_find_hbt _ Hcc1).
        case: (CCacheFlatten.find_hbt (QFBV.Blneg e) fc1).
        -- move=> [cs lr] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
        -- move=> [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
    + move=> e1 e2 Hwf Hcc.
      replace (bpair (HBconj (hash_bexp e1) (hash_bexp e2))
                     (bhval (hash_bexp e1) + bhval (hash_bexp e2) + 1)) with
          (hash_bexp (QFBV.Bconj e1 e2)) by reflexivity.
      rewrite (ccache_compatible_find_cbt _ Hcc).
      case: (CCacheFlatten.find_cbt (QFBV.Bconj e1 e2) ifc).
      * move=> [cs lr] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst. done.
      * dcase (mk_env_bexp_hccache iE s im ihc ig (hash_bexp e1)) =>
        [[[[[[hE1 hm1] hc1] hg1] hcs1] hlr1] Hhenv1].
        dcase (mk_env_bexp_hccache hE1 s hm1 hc1 hg1 (hash_bexp e2)) =>
        [[[[[[hE2 hm2] hc2] hg2] hcs2] hlr2] Hhenv2].
        dcase (mk_env_bexp_fccache iE s im ifc ig e1) =>
        [[[[[[fE1 fm1] fc1] fg1] fcs1] flr1] Hfenv1].
        dcase (mk_env_bexp_fccache fE1 s fm1 fc1 fg1 e2) =>
        [[[[[[fE2 fm2] fc2] fg2] fcs2] flr2] Hfenv2].
        move: (mk_env_bexp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf Hcc Hhenv1 Hfenv1).
        move=> [? [? [Hwf1 [Hcc1 [? [? ?]]]]]]; subst.
        move: (mk_env_bexp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf1 Hcc1 Hhenv2 Hfenv2).
        move=> [? [? [Hwf2 [Hcc2 [? [? ?]]]]]]; subst.
        rewrite (ccache_compatible_find_hbt _ Hcc2).
        case: (CCacheFlatten.find_hbt (QFBV.Bconj e1 e2) fc2).
        -- move=> [cs lr] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
        -- move=> [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
    + move=> e1 e2 Hwf Hcc.
      replace (bpair (HBdisj (hash_bexp e1) (hash_bexp e2))
                     (bhval (hash_bexp e1) + bhval (hash_bexp e2) + 1)) with
          (hash_bexp (QFBV.Bdisj e1 e2)) by reflexivity.
      rewrite (ccache_compatible_find_cbt _ Hcc).
      case: (CCacheFlatten.find_cbt (QFBV.Bdisj e1 e2) ifc).
      * move=> [cs lr] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst. done.
      * dcase (mk_env_bexp_hccache iE s im ihc ig (hash_bexp e1)) =>
        [[[[[[hE1 hm1] hc1] hg1] hcs1] hlr1] Hhenv1].
        dcase (mk_env_bexp_hccache hE1 s hm1 hc1 hg1 (hash_bexp e2)) =>
        [[[[[[hE2 hm2] hc2] hg2] hcs2] hlr2] Hhenv2].
        dcase (mk_env_bexp_fccache iE s im ifc ig e1) =>
        [[[[[[fE1 fm1] fc1] fg1] fcs1] flr1] Hfenv1].
        dcase (mk_env_bexp_fccache fE1 s fm1 fc1 fg1 e2) =>
        [[[[[[fE2 fm2] fc2] fg2] fcs2] flr2] Hfenv2].
        move: (mk_env_bexp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf Hcc Hhenv1 Hfenv1).
        move=> [? [? [Hwf1 [Hcc1 [? [? ?]]]]]]; subst.
        move: (mk_env_bexp_hccache_fccache _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                           Hwf1 Hcc1 Hhenv2 Hfenv2).
        move=> [? [? [Hwf2 [Hcc2 [? [? ?]]]]]]; subst.
        rewrite (ccache_compatible_find_hbt _ Hcc2).
        case: (CCacheFlatten.find_hbt (QFBV.Bdisj e1 e2) fc2).
        -- move=> [cs lr] [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
        -- move=> [] ? ? ? ? ? ? [] ? ? ? ? ? ?; subst.
             by t_auto.
Qed.



Fixpoint mk_env_hbexps_hccache_conjs_rec E s m c g rcs rlrs es :
  env * vm * ccache * generator * seq cnf * cnf :=
  match es with
  | [::] => (E, m, c, g, rcs, rlrs)
  | hd::tl => let '(E', m', c', g', cs, lr) := mk_env_bexp_hccache E s m c g hd in
              mk_env_hbexps_hccache_conjs_rec E' s m' c' g'
                                              (catrev cs rcs) ([:: lr]::rlrs) tl
  end.

Definition mk_env_hbexps_hccache_conjs E s m c g es :=
  mk_env_hbexps_hccache_conjs_rec E s m c g [::] [::] es.

Lemma mk_env_hbexps_hccache_conjs_rec_empty E s m c g rcs rlrs :
  mk_env_hbexps_hccache_conjs_rec E s m c g rcs rlrs [::] = (E, m, c, g, rcs, rlrs).
Proof. reflexivity. Qed.

Lemma mk_env_hbexps_hccache_conjs_rec_singleton E s m c g rcs rlrs e :
  mk_env_hbexps_hccache_conjs_rec E s m c g rcs rlrs [:: e] =
  let '(E', m', c', g', cs, lr) := mk_env_bexp_hccache E s m c g e in
  (E', m', c', g', (catrev cs rcs), [::lr]::rlrs).
Proof. reflexivity. Qed.

Lemma mk_env_hbexps_hccache_conjs_rec_cons E s m c g rcs rlrs e es :
  mk_env_hbexps_hccache_conjs_rec E s m c g rcs rlrs (e::es) =
  let '(E', m', c', g', cs, lr) := mk_env_bexp_hccache E s m c g e in
  mk_env_hbexps_hccache_conjs_rec E' s m' c' g'
                                  (catrev cs rcs) ([::lr]::rlrs) es.
Proof. reflexivity. Qed.

Lemma mk_env_hbexps_hccache_conjs_rec_rcons E s m c g rcs rlrs es e :
  mk_env_hbexps_hccache_conjs_rec E s m c g rcs rlrs (rcons es e) =
  let '(E', m', c', g', cs, lrs) := mk_env_hbexps_hccache_conjs_rec
                                      E s m c g rcs rlrs es in
  mk_env_hbexps_hccache_conjs_rec E' s m' c' g' cs lrs [:: e].
Proof.
  rewrite /=. elim: es E m c g rcs rlrs e => [| hd tl IH] E m c g rcs rlrs e //=.
  dcase (mk_env_bexp_hccache E s m c g hd) => [[[[[[E1 m1] c1] g1] cs1] lr1] Hbb_hd].
  rewrite -IH. reflexivity.
Qed.

Lemma mk_env_hbexps_hccache_conjs_rec_cat E s m c g rcs rlrs es1 es2 :
  mk_env_hbexps_hccache_conjs_rec E s m c g rcs rlrs (es1 ++ es2) =
  let '(E', m', c', g', cs1, lrs1) := mk_env_hbexps_hccache_conjs_rec
                                    E s m c g rcs rlrs es1 in
  mk_env_hbexps_hccache_conjs_rec E' s m' c' g' cs1 lrs1 es2.
Proof.
  elim: es1 es2 E m c g rcs rlrs => [| hd tl IH] es2 E m c g rcs rlrs //=.
  dcase (mk_env_bexp_hccache E s m c g hd) => [[[[[[E1 m1] c1] g1] cs1] lr1] Hbb_hd].
  rewrite -IH. reflexivity.
Qed.

Lemma mk_env_hbexps_hccache_conjs_rec_is_bit_blast_hbexps_hccache_conjs_rec
      TE E s m c g rcs rlrs es Ev mv cv gv rcsv rlrsv mb cb gb rcsb rlrsb :
  AdhereConform.conform_bexps es s TE ->
  QFBV.well_formed_bexps es TE ->
  mk_env_hbexps_hccache_conjs_rec E s m c g rcs rlrs (mapr hash_bexp es) =
  (Ev, mv, cv, gv, rcsv, rlrsv) ->
  bit_blast_hbexps_hccache_conjs_rec TE m c g rcs rlrs (mapr hash_bexp es) =
  (mb, cb, gb, rcsb, rlrsb) ->
  mv = mb /\ cv = cb /\ gv = gb /\ rcsv = rcsb /\ rlrsv = rlrsb.
Proof.
  elim: es TE E s m c g rcs rlrs Ev mv cv gv rcsv rlrsv mb cb gb rcsb rlrsb =>
  [| e es IH] //= TE E s m c g rcs rlrs Ev mv cv gv rcsv rlrsv mb cb gb rcsb rlrsb Hco Hwf.
  - case=> ? ? ? ? ? ?; case=> ? ? ? ? ?; subst. done.
  - move/andP: Hco=> [Hco_hd Hco_tl]. move/andP: Hwf => [Hwf_hd Hwf_tl].
    rewrite mapr_cons.
    rewrite mk_env_hbexps_hccache_conjs_rec_rcons.
    rewrite bit_blast_hbexps_hccache_conjs_rec_rcons.
    dcase (mk_env_hbexps_hccache_conjs_rec E s m c g rcs rlrs (mapr hash_bexp es))
    => [[[[[[Ev1 mv1] cv1] gv1] csv1] lrsv1] Henv1].
    dcase (bit_blast_hbexps_hccache_conjs_rec TE m c g rcs rlrs (mapr hash_bexp es))
    => [[[[[mb1 cb1] gb1] csb1] lrsb1] Hbb1].
    rewrite mk_env_hbexps_hccache_conjs_rec_singleton.
    rewrite bit_blast_hbexps_hccache_conjs_rec_singleton.
    dcase (mk_env_bexp_hccache Ev1 s mv1 cv1 gv1 (hash_bexp e))
    => [[[[[[Ev2 mv2] cv2] gv2] csv2] lrsv2] Henv2].
    dcase (bit_blast_bexp_hccache TE mb1 cb1 gb1 (hash_bexp e))
    => [[[[[mb2 cb2] gb2] csb2] lrsb2] Hbb2].
    case=> ? ? ? ? ? ?; case=> ? ? ? ? ?; subst.
    move: (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hco_tl Hwf_tl Henv1 Hbb1) =>
    [? [? [? [? ?]]]]; subst.
    move: (mk_env_bexp_hccache_is_bit_blast_bexp_hccache Hco_hd Hwf_hd Henv2) => Hbb2'.
    rewrite Hbb2 in Hbb2'; case: Hbb2' => ? ? ? ? ?; subst. done.
Qed.

Lemma mk_env_hbexps_hccache_conjs_is_bit_blast_hbexps_hccache_conjs
      TE E s m c g es Ev mv cv gv rcsv rlrsv mb cb gb rcsb rlrsb :
  AdhereConform.conform_bexps es s TE ->
  QFBV.well_formed_bexps es TE ->
  mk_env_hbexps_hccache_conjs E s m c g (mapr hash_bexp es) = (Ev, mv, cv, gv, rcsv, rlrsv) ->
  bit_blast_hbexps_hccache_conjs TE m c g (mapr hash_bexp es) = (mb, cb, gb, rcsb, rlrsb) ->
  mv = mb /\ cv = cb /\ gv = gb /\ rcsv = rcsb /\ rlrsv = rlrsb.
Proof.
  exact: mk_env_hbexps_hccache_conjs_rec_is_bit_blast_hbexps_hccache_conjs_rec.
Qed.

Lemma mk_env_exp_hccache_well_formed_ccache
      TE E s m ihc g (e : QFBV.exp) hE hm ohc hg hcs hlrs :
  QFBV.well_formed_exp e TE ->
  AdhereConform.conform_exp e s TE ->
  well_formed_ccache ihc ->
  mk_env_exp_hccache E s m ihc g (hash_exp e) =  (hE, hm, ohc, hg, hcs, hlrs) ->
  well_formed_ccache ohc.
Proof.
  move=> Hwf Hco Hwfihc Henv.
  move: (mk_env_exp_hccache_is_bit_blast_exp_hccache Hco Hwf Henv) => Hbb.
  exact: (bit_blast_exp_hccache_well_formed_ccache Hwfihc Hbb).
Qed.

Lemma mk_env_bexp_hccache_well_formed_ccache
      TE E s m ihc g (e : QFBV.bexp) hE hm ohc hg hcs hlr :
  QFBV.well_formed_bexp e TE ->
  AdhereConform.conform_bexp e s TE ->
  well_formed_ccache ihc ->
  mk_env_bexp_hccache E s m ihc g (hash_bexp e) =  (hE, hm, ohc, hg, hcs, hlr) ->
  well_formed_ccache ohc.
Proof.
  move=> Hwf Hco Hwfihc Henv.
  move: (mk_env_bexp_hccache_is_bit_blast_bexp_hccache Hco Hwf Henv) => Hbb.
  exact: (bit_blast_bexp_hccache_well_formed_ccache Hwfihc Hbb).
Qed.

Lemma mk_env_hbexps_hccache_conjs_rec_well_formed_ccache
      TE E s m c g es E' m' c' g' ics ilrs cs lrs :
  QFBV.well_formed_bexps es TE ->
  AdhereConform.conform_bexps es s TE ->
  mk_env_hbexps_hccache_conjs_rec
    E s m c g ics ilrs (mapr hash_bexp es) = (E', m', c', g', cs, lrs) ->
  well_formed_ccache c -> well_formed_ccache c'.
Proof.
  elim: es m c g E' m' c' g' ics ilrs cs lrs =>
  [| hd tl IH] im ic ig oE om oc og ics ilrs ocs olrs /=.
  - move=> _ _. case=> ? ? ? ? ? ?; subst. by apply.
  - move=> /andP [Hwf_hd Hwf_tl] /andP [Hco_hd Hco_tl].
    rewrite mapr_cons. rewrite mk_env_hbexps_hccache_conjs_rec_rcons.
    dcase (mk_env_hbexps_hccache_conjs_rec E s im ic ig ics ilrs (mapr hash_bexp tl))
    => [[[[[[E1 m1] c1] g1] cs1] lrs1] Henv_tl].
    rewrite mk_env_hbexps_hccache_conjs_rec_singleton.
    dcase (mk_env_bexp_hccache E1 s m1 c1 g1 (hash_bexp hd)) =>
    [[[[[[E2 m2] c2] g2] cs2] lrs2] Henv_hd]. case=> ? ? ? ? ? ?; subst.
    move=> Hwf_ic. move: (IH _ _ _ _ _ _ _ _ _ _ _ Hwf_tl Hco_tl Henv_tl Hwf_ic) => Hwf_c1.
    exact: (mk_env_bexp_hccache_well_formed_ccache Hwf_hd Hco_hd Hwf_c1 Henv_hd).
Qed.

Ltac myauto :=
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
    | H : mk_env_var _ _ _ _ = _ |- _ =>
      move: (mk_env_var_newer_gen H) => {H} H
    | H : mk_env_eunop _ _ _ _ = _ |- _ =>
      move: (mk_env_eunop_newer_gen H) => {H} H
    | H : mk_env_ite _ _ _ _ _ = _ |- _ =>
      move: (mk_env_ite_newer_gen H) => {H} H
    | H : mk_env_ebinop _ _ _ _ _ = _ |- _ =>
      move: (mk_env_ebinop_newer_gen H) => {H} H
    | H : mk_env_bbinop _ _ _ _ _ = _ |- _ =>
      move: (mk_env_bbinop_newer_gen H) => {H} H
    (* apply induction hypothesis *)
    | mk_env_exp_hccache_newer_gen :
        (forall (iE : env) (s : SSAStore.t) (im : vm)
                (ic : ccache) (ig : generator) (e : hexp)
                (oE : env) (om : vm) (oc : ccache)
                (og : generator) (ocs : seq cnf) (olrs : word),
            mk_env_exp_hccache iE s im ic ig e = (oE, om, oc, og, ocs, olrs) ->
            is_true (ig <=? og)%positive),
      Henv : mk_env_exp_hccache _ _ _ _ _ _ = _ |- _ =>
      move: (mk_env_exp_hccache_newer_gen _ _ _ _ _ _ _ _ _ _ _ _ Henv) => {Henv} Henv
    | mk_env_bexp_hccache_newer_gen :
        (forall (iE : env) (s : SSAStore.t)
                (im : vm) (ic : ccache) (ig : generator)
                (e : hbexp) (oE : env) (om : vm)
                (oc : ccache) (og : generator) (ocs : seq cnf)
                (olr : literal),
            mk_env_bexp_hccache iE s im ic ig e =
            (oE, om, oc, og, ocs, olr) -> is_true (ig <=? og)%positive),
      Henv : mk_env_bexp_hccache _ _ _ _ _ _ = _ |- _ =>
      move: (mk_env_bexp_hccache_newer_gen _ _ _ _ _ _ _ _ _ _ _ _ Henv) => {Henv} Henv
    (**)
    | |- is_true (?g <=? ?g)%positive => apply: Pos.leb_refl
    | H : is_true (?g1 <=? ?g2)%positive |- is_true (?g1 <=? ?g3)%positive =>
      apply: (pos_leb_trans H)
    | H : is_true (?g2 <=? ?g3)%positive |- is_true (?g1 <=? ?g3)%positive =>
      apply: (pos_leb_trans _ H)
    | |- is_true (?g <=? ?g + _)%positive => exact: pos_leb_add_diag_r
    (**)
    | |- _ => dcase_bb_ccache || dcase_mk_env_ccache
    end.

Lemma mk_env_exp_hccache_newer_gen iE s im ic ig e oE om oc og ocs olrs :
  mk_env_exp_hccache iE s im ic ig e = (oE, om, oc, og, ocs, olrs) ->
  (ig <=? og)%positive
with
mk_env_bexp_hccache_newer_gen iE s im ic ig e oE om oc og ocs olr :
  mk_env_bexp_hccache iE s im ic ig e = (oE, om, oc, og, ocs, olr) ->
  (ig <=? og)%positive.
Proof.
  (* mk_env_exp_hccache_newer_gen *)
  case: e. case=> //=.
  - move=> v z. by myauto.
  - move=> bs z. by myauto.
  - move=> op e z. by myauto.
  - move=> op e1 e2 z. by myauto.
  - move=> e1 e2 e3 z. by myauto.
  (* mk_env_bexp_hccache_newer_gen *)
  case: e. case=> //=.
  - move=> z. by myauto.
  - move=> z. by myauto.
  - move=> op e1 e2 z. by myauto.
  - move=> e z. by myauto.
  - move=> e1 e2 z. by myauto.
  - move=> e1 e2 z. by myauto.
Qed.

Lemma mk_env_hbexps_hccache_conjs_rec_newer_gen
      iE s im ic ig ircs irlrs es oE om oc og ocs olrs :
  mk_env_hbexps_hccache_conjs_rec
    iE s im ic ig ircs irlrs (mapr hash_bexp es) = (oE, om, oc, og, ocs, olrs) ->
  (ig <=? og)%positive.
Proof.
  elim: es iE s im ic ig ircs irlrs oE om oc og ocs olrs
  => [| e es IH] iE s im ic ig ircs irlrs oE om oc og ocs olrs //=.
  - case=> ? ? ? ? ? ?; subst. exact: Pos.leb_refl.
  - rewrite mapr_cons. rewrite mk_env_hbexps_hccache_conjs_rec_rcons.
    dcase (mk_env_hbexps_hccache_conjs_rec iE s im ic ig ircs irlrs (mapr hash_bexp es))
    => [[[[[[E1 m1] c1] g1] cs1] lrs1] Henv1].
    rewrite mk_env_hbexps_hccache_conjs_rec_singleton.
    dcase (mk_env_bexp_hccache E1 s m1 c1 g1 (hash_bexp e))
    => [[[[[[E2 m2] c2] g2] cs2] lrs2] Henv2].
    case=> ? ? ? ? ? ?; subst. move: (mk_env_bexp_hccache_newer_gen Henv2).
    apply: pos_leb_trans. exact: (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Henv1).
Qed.

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
    | H : mk_env_var _ _ _ _ = _ |- _ =>
      move: (mk_env_var_preserve H) => {H} H
    | H : mk_env_eunop _ _ _ _ = _ |- _ =>
      move: (mk_env_eunop_preserve H) => {H} H
    | H : mk_env_ite _ _ _ _ _ = _ |- _ =>
      move: (mk_env_ite_preserve H) => {H} H
    | H : mk_env_ebinop _ _ _ _ _ = _ |- _ =>
      move: (mk_env_ebinop_preserve H) => {H} H
    | H : mk_env_bbinop _ _ _ _ _ = _ |- _ =>
      move: (mk_env_bbinop_preserve H) => {H} H
    (* apply induction hypothesis *)
    | mk_env_exp_hccache_preserve :
        (forall (iE : env) (s : SSAStore.t) (im : vm)
                (ic : ccache) (ig : generator) (e : hexp)
                (oE : env) (om : vm) (oc : ccache)
                (og : generator) (ocs : seq cnf) (olrs : word),
            mk_env_exp_hccache iE s im ic ig e = (oE, om, oc, og, ocs, olrs) ->
            env_preserve iE oE ig),
      Henv : mk_env_exp_hccache _ _ _ _ _ _ = _ |- _ =>
      let Hpre := fresh "Hpre" in
      let Hg := fresh "Hg" in
      (move: (mk_env_exp_hccache_preserve _ _ _ _ _ _ _ _ _ _ _ _ Henv) => Hpre);
      (move: (mk_env_exp_hccache_newer_gen Henv) => Hg); clear Henv
    | mk_env_bexp_hccache_preserve :
        (forall (iE : env) (s : SSAStore.t)
                (im : vm) (ic : ccache) (ig : generator)
                (e : hbexp) (oE : env) (om : vm)
                (oc : ccache) (og : generator) (ocs : seq cnf)
                (olr : literal),
            mk_env_bexp_hccache iE s im ic ig e = (oE, om, oc, og, ocs, olr) ->
            env_preserve iE oE ig),
      Henv : mk_env_bexp_hccache _ _ _ _ _ _ = _ |- _ =>
      let Hpre := fresh "Hpre" in
      let Hg := fresh "Hg" in
      (move: (mk_env_bexp_hccache_preserve _ _ _ _ _ _ _ _ _ _ _ _ Henv) => Hpre);
      (move: (mk_env_bexp_hccache_newer_gen Henv) => Hg); clear Henv
    (**)
    | |- env_preserve ?E ?E _ => exact: env_preserve_refl
    | Hg : is_true (?g2 <=? ?g1)%positive,
      H : env_preserve ?E1 ?E2 ?g1 |- env_preserve ?E1 ?E2 ?g2 =>
      exact: (env_preserve_le H Hg)
    | |- env_preserve ?E (env_upd ?E ?g _) ?g =>
      exact: env_upd_eq_preserve
    | H : env_preserve ?E _ ?g |- env_preserve ?E _ ?g =>
      apply: (env_preserve_trans H)
    | Hg : is_true (?g2 <=? ?g1)%positive,
      H : env_preserve ?E1 _ ?g1 |- env_preserve ?E1 _ ?g2 =>
      apply: (env_preserve_le _ Hg)
    | Hg : is_true (?g1 <=? ?g2)%positive
      |- env_preserve ?E (env_upd ?E ?g2 _) ?g1 =>
      apply: (env_preserve_le _ Hg)
    (**)
    | |- _ => dcase_bb_ccache || dcase_mk_env_ccache
    end.

Lemma mk_env_exp_hccache_preserve iE s im ic ig e oE om oc og ocs olrs :
  mk_env_exp_hccache iE s im ic ig e = (oE, om, oc, og, ocs, olrs) ->
  env_preserve iE oE ig
with
mk_env_bexp_hccache_preserve iE s im ic ig e oE om oc og ocs olr :
  mk_env_bexp_hccache iE s im ic ig e = (oE, om, oc, og, ocs, olr) ->
  env_preserve iE oE ig.
Proof.
  (* mk_env_exp_hccache_preserve *)
  case: e. case=> //=.
  - move=> v z. by myauto.
  - move=> bs z. by myauto.
  - move=> op e z. by myauto.
  - move=> op e1 e2 z. by myauto.
  - move=> e1 e2 e3 z. by myauto.
  (* mk_env_bexp_hccache_preserve *)
  case: e. case=> //=.
  - move=> z. by myauto.
  - move=> z. by myauto.
  - move=> op e1 e2 z. by myauto.
  - move=> e z. by myauto.
  - move=> e1 e2 z. by myauto.
  - move=> e1 e2 z. by myauto.
Qed.

Lemma mk_env_hbexps_hccache_conjs_rec_preserve
      iE s im ic ig ircs irlrs es oE om oc og ocs olrs :
  mk_env_hbexps_hccache_conjs_rec
    iE s im ic ig ircs irlrs (mapr hash_bexp es) = (oE, om, oc, og, ocs, olrs) ->
  env_preserve iE oE ig.
Proof.
  elim: es iE s im ic ig ircs irlrs oE om oc og ocs olrs
  => [| e es IH] iE s im ic ig ircs irlrs oE om oc og ocs olrs //=.
  - case=> ? ? ? ? ? ?; subst. done.
  - rewrite mapr_cons. rewrite mk_env_hbexps_hccache_conjs_rec_rcons.
    dcase (mk_env_hbexps_hccache_conjs_rec iE s im ic ig ircs irlrs (mapr hash_bexp es))
    => [[[[[[E1 m1] c1] g1] cs1] lrs1] Henv1].
    rewrite mk_env_hbexps_hccache_conjs_rec_singleton.
    dcase (mk_env_bexp_hccache E1 s m1 c1 g1 (hash_bexp e))
    => [[[[[[E2 m2] c2] g2] cs2] lrs2] Henv2].
    case=> ? ? ? ? ? ?; subst. move: (mk_env_bexp_hccache_preserve Henv2) => Hpre.
    move: (env_preserve_le Hpre (mk_env_hbexps_hccache_conjs_rec_newer_gen Henv1)).
    apply: env_preserve_trans. exact: (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Henv1).
Qed.

Ltac mydestruct :=
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
    | |- ?e -> ?e => by apply
    (**)
    | |- _ => dcase_bb_ccache || dcase_mk_env_ccache
    end.

Lemma mk_env_exp_hccache_newer_vm iE s im ic ig e oE om oc og ocs olrs :
  mk_env_exp_hccache iE s im ic ig e = (oE, om, oc, og, ocs, olrs) ->
  newer_than_vm ig im ->
  newer_than_vm og om
with
mk_env_bexp_hccache_newer_vm iE s im ic ig e oE om oc og ocs olr :
  mk_env_bexp_hccache iE s im ic ig e = (oE, om, oc, og, ocs, olr) ->
  newer_than_vm ig im ->
  newer_than_vm og om.
Proof.
  (* mk_env_exp_hccache_newer_vm *)
  case: e. case=> //=.
  - move=> v z. mydestruct. move=> Hnew. apply: (newer_than_vm_add _ _ Hnew).
    + exact: (mk_env_var_newer_gen H5).
    + exact: (mk_env_var_newer_res H5).
  - move=> bs z. by mydestruct.
  - move=> op e z. mydestruct.
    + exact: (mk_env_exp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H6).
    + move=> Hnew_igim. move: (mk_env_eunop_newer_gen H12) => Hnew_og.
      apply: (newer_than_vm_le_newer _ Hnew_og).
      exact: (mk_env_exp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H6).
  - move=> op e1 e2 z. mydestruct.
    + move=> Hnew_igim. apply: (mk_env_exp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H13).
      exact: (mk_env_exp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H6).
    + move=> Hnew_igim. move: (mk_env_ebinop_newer_gen H19) => Hnew_og.
      apply: (newer_than_vm_le_newer _ Hnew_og).
      apply: (mk_env_exp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H13).
      exact: (mk_env_exp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H6).
  - move=> e1 e2 e3 z. mydestruct.
    + move=> Hnew_igim.
      apply: (mk_env_exp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H20).
      apply: (mk_env_exp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H13).
      exact: (mk_env_bexp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H6).
    + move=> Hnew_igim. move: (mk_env_ite_newer_gen H26) => Hnew_og.
      apply: (newer_than_vm_le_newer _ Hnew_og).
      apply: (mk_env_exp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H20).
      apply: (mk_env_exp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H13).
      exact: (mk_env_bexp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H6).
  (* mk_env_bexp_hccache_newer_vm *)
  case: e. case=> //=.
  - move=> z. by mydestruct.
  - move=> z. by mydestruct.
  - move=> op e1 e2 z. mydestruct.
    + move=> Hnew_igim. apply: (mk_env_exp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H13).
      exact: (mk_env_exp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H6).
    + move=> Hnew_igim. move: (mk_env_bbinop_newer_gen H19) => Hnew_og.
      apply: (newer_than_vm_le_newer _ Hnew_og).
      apply: (mk_env_exp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H13).
      exact: (mk_env_exp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H6).
  - move=> e z. mydestruct.
    + move=> Hnew_igim. exact: (mk_env_bexp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H6).
    + move=> Hnew_igim. apply: newer_than_vm_add_r.
      exact: (mk_env_bexp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H6).
  - move=> e1 e2 z. mydestruct.
    + move=> Hnew_igim. apply: (mk_env_bexp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H13).
      exact: (mk_env_bexp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H6).
    + move=> Hnew_igim. apply: newer_than_vm_add_r.
      apply: (mk_env_bexp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H13).
      exact: (mk_env_bexp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H6).
  - move=> e1 e2 z. mydestruct.
    + move=> Hnew_igim. apply: (mk_env_bexp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H13).
      exact: (mk_env_bexp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H6).
    + move=> Hnew_igim. apply: newer_than_vm_add_r.
      apply: (mk_env_bexp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H13).
      exact: (mk_env_bexp_hccache_newer_vm _ _ _ _ _ _ _ _ _ _ _ _ H6).
Qed.

Lemma mk_env_hbexps_hccache_conjs_rec_newer_vm
      iE s im ic ig ircs irlrs es oE om oc og ocs olrs :
  mk_env_hbexps_hccache_conjs_rec
    iE s im ic ig ircs irlrs (mapr hash_bexp es) = (oE, om, oc, og, ocs, olrs) ->
  newer_than_vm ig im -> newer_than_vm og om.
Proof.
  elim: es iE s im ic ig ircs irlrs oE om oc og ocs olrs
  => [| e es IH] iE s im ic ig ircs irlrs oE om oc og ocs olrs //=.
  - case=> ? ? ? ? ? ?; subst. by apply.
  - rewrite mapr_cons. rewrite mk_env_hbexps_hccache_conjs_rec_rcons.
    dcase (mk_env_hbexps_hccache_conjs_rec iE s im ic ig ircs irlrs (mapr hash_bexp es))
    => [[[[[[E1 m1] c1] g1] cs1] lrs1] Henv1].
    rewrite mk_env_hbexps_hccache_conjs_rec_singleton.
    dcase (mk_env_bexp_hccache E1 s m1 c1 g1 (hash_bexp e))
    => [[[[[[E2 m2] c2] g2] cs2] lrs2] Henv2].
    case=> ? ? ? ? ? ?; subst. move=> Hnew_igim.
    apply: (mk_env_bexp_hccache_newer_vm Henv2).
    exact: (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Henv1 Hnew_igim).
Qed.

Lemma mk_env_hbexps_hccache_conjs_rec_cache_compatible_full
      TE ihE s ihm ihc ihg ihcs ihlrs es ohE ohm ohc ohg ohcs ohlrs ifc icc :
  mk_env_hbexps_hccache_conjs_rec
    ihE s ihm ihc ihg ihcs ihlrs (mapr hash_bexp es) = (ohE, ohm, ohc, ohg, ohcs, ohlrs) ->
  QFBV.well_formed_bexps es TE ->
  AdhereConform.conform_bexps es s TE ->
  well_formed_ccache ihc ->
  ccache_compatible ihc ifc ->
  CCacheFlatten.ccache_compatible ifc icc ->
  CompCache.well_formed icc ->
  newer_than_vm ihg ihm ->
  newer_than_lit ihg lit_tt ->
  newer_than_cnf ihg (tflatten ihcs) ->
  CompCache.newer_than_cache ihg icc ->
  CompCache.interp_cache ihE icc ->
  interp_cnf ihE (tflatten ihcs) ->
  exists ofc, exists occ,
        ccache_compatible ohc ofc
        /\ CCacheFlatten.ccache_compatible ofc occ
        /\ CompCache.well_formed occ
        /\ newer_than_cnf ohg (tflatten ohcs)
        /\ CompCache.newer_than_cache ohg occ
        /\ interp_cnf ohE (tflatten ohcs) /\ CompCache.interp_cache ohE occ.
Proof.
  elim: es TE s ihE ihm ihc ihg ihcs ihlrs ohE ohm ohc ohg ohcs ohlrs ifc icc =>
  [| hd tl IH] TE s ihE ihm ihc ihg ihcs ihlrs ohE ohm ohc ohg ohcs ohlrs ifc icc //=.
  - case=> ? ? ? ? ? ?; subst. move=> _ ? ? ? ? ? ? ? ? ? ? ?.
    exists ifc. exists icc. tauto.
  - rewrite mapr_cons. rewrite mk_env_hbexps_hccache_conjs_rec_rcons.
    dcase (mk_env_hbexps_hccache_conjs_rec ihE s ihm ihc ihg ihcs ihlrs (mapr hash_bexp tl))
    => [[[[[[hE1 hm1] hc1] hg1] hcs1] hlrs1] Hhenv_tl].
    rewrite mk_env_hbexps_hccache_conjs_rec_singleton.
    dcase (mk_env_bexp_hccache hE1 s hm1 hc1 hg1 (hash_bexp hd)) =>
    [[[[[[hE2 hm2] hc2] hg2] hcs2] hlrs2] Hhenv_hd]. case=> ? ? ? ? ? ?; subst.
    move=> /andP [Hwf_hd Hwf_tl] /andP [Hco_hd Hco_tl]
            Hwfihc Hccihc Hccifc Hwficc Hnewvm_ihg Hnewlit_ihg Hnewcs_ihcs Hnewihg Hicicc Hicihcs.

    move: (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              Hhenv_tl Hwf_tl Hco_tl Hwfihc Hccihc Hccifc Hwficc
              Hnewvm_ihg Hnewlit_ihg Hnewcs_ihcs Hnewihg Hicicc Hicihcs)
    => [fc1 [cc1 [Hcchc1 [Hccfc1 [Hwfcc1 [Hnewcs_hg1 [Hnewhg1 [Hichcs1 Hicocc]]]]]]]].

    move: (mk_env_hbexps_hccache_conjs_rec_well_formed_ccache Hwf_tl Hco_tl Hhenv_tl Hwfihc)
    => Hwfhc1.
    dcase (mk_env_bexp_fccache hE1 s hm1 fc1 hg1 hd) =>
    [[[[[[fE2 fm2] fc2] fg2] fcs2] flrs2] Hfenv_hd].
    move: (mk_env_bexp_hccache_fccache Hwfhc1 Hcchc1 Hhenv_hd Hfenv_hd)
    => [? [? [Hwfohc [Hccohc [? [? ?]]]]]]; subst.

    dcase (mk_env_bexp_ccache hm1 cc1 s hE1 hg1 hd) =>
    [[[[[[m2 cc2] E2] g2] cs2] lrs2] Henv_hd]; subst.

    move: (mk_env_bexp_fccache_valid Hccfc1 Hfenv_hd Henv_hd)
    => [? [? [Hccfc2 [? [Heqs [Heqn ?]]]]]]; subst.

    move: (mk_env_bexp_ccache_well_formed Henv_hd Hwfcc1) => Hwfcc2.

    exists fc2. exists cc2. split; first assumption.
    split; first assumption. split; first assumption.

    move: (mk_env_hbexps_hccache_conjs_rec_newer_vm Hhenv_tl Hnewvm_ihg) => Hnewvm_hg1.
    move: (mk_env_hbexps_hccache_conjs_rec_newer_gen Hhenv_tl) => Hihghg1.
    move: (newer_than_lit_le_newer Hnewlit_ihg Hihghg1) => Hnewlit_hg1.

    split. Focus 2.

    split; first exact: (mk_env_bexp_ccache_newer_cache
                           Henv_hd Hnewvm_hg1 Hnewlit_hg1 Hwfcc1 Hnewhg1).

    move: (mk_env_bexp_ccache_interp_cache Henv_hd Hnewvm_hg1 Hnewlit_hg1 Hwfcc1 Hnewhg1
                                           Hicocc) => [H1 H2].
    split; last exact: H2.

    rewrite interp_cnf_tflatten_catrev. rewrite (Heqs E2) H1 andTb.
    move: (mk_env_bexp_ccache_preserve Henv_hd) => Hpre.
    rewrite (env_preserve_cnf Hpre); first assumption.
    assumption.

    move: (mk_env_bexp_ccache_newer_cnf Henv_hd Hnewvm_hg1 Hnewlit_hg1 Hwfcc1 Hnewhg1).
    rewrite -(Heqn g2) => Hnew_fcs2. rewrite newer_than_cnf_tflatten_catrev.
    rewrite Hnew_fcs2 andTb. apply: (newer_than_cnf_le_newer Hnewcs_hg1).
    exact: (mk_env_bexp_hccache_newer_gen Hhenv_hd).
Qed.





Lemma bit_blast_hbexps_hccache_conjs_rec_size
      TE pre_es im ic ig ircs irlrs es om oc og ocs olrs :
  bit_blast_hbexps_hccache_conjs_rec TE im ic ig ircs irlrs es = (om, oc, og, ocs, olrs) ->
  size irlrs = size pre_es ->
  all size1 irlrs ->
  size olrs = size (pre_es ++ es) /\ all size1 olrs.
Proof.
  elim: es pre_es im ic ig ircs irlrs om oc og ocs olrs
           => [| e es IH] pre_es im ic ig ircs irlrs om oc og ocs olrs //=.
  - case=> ? ? ? ? ? Hs Hs1; subst. rewrite cats0. done.
  - dcase (bit_blast_bexp_hccache TE im ic ig e) => [[[[[m1 c1] g1] cs1] lr1] Hbb1].
    move=> Hbb2 Hs Hs1. rewrite -cat_rcons. apply: (IH _ _ _ _ _ _ _ _ _ _ _ Hbb2).
    + rewrite /=. rewrite size_rcons. apply/eqP. rewrite eqSS. by rewrite Hs eqxx.
    + rewrite /=. assumption.
Qed.

Lemma bit_blast_hbexps_hccache_conjs_size TE es m c g cs lrs :
  bit_blast_hbexps_hccache_conjs TE init_vm init_hccache init_gen es = (m, c, g, cs, lrs) ->
  size lrs = size es /\ all size1 lrs.
Proof.
  rewrite /bit_blast_hbexps_hccache_conjs. move=> Hbb.
  have Hs: (size ([::] : seq QFBV.bexp) = size ([::] : seq QFBV.bexp)) by done.
  have Hs1: (all size1 ([::] : seq (seq literal))) by done.
  move: (bit_blast_hbexps_hccache_conjs_rec_size (pre_es:=[::]) Hbb Hs Hs1) => {Hs Hs1} [Hs Hs1].
  rewrite cat0s in Hs. done.
Qed.



Ltac mydestruct ::=
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
    | |- _ -> ?e -> ?e => intro; by apply
    (**)
    | |- _ => dcase_bb_ccache || dcase_mk_env_ccache
    end.

Lemma mk_env_exp_hccache_consistent iE s im ic ig e oE om oc og ocs olrs :
  mk_env_exp_hccache iE s im ic ig e = (oE, om, oc, og, ocs, olrs) ->
  newer_than_vm ig im ->
  consistent im iE s ->
  consistent om oE s
with
mk_env_bexp_hccache_consistent iE s im ic ig e oE om oc og ocs olr :
  mk_env_bexp_hccache iE s im ic ig e = (oE, om, oc, og, ocs, olr) ->
  newer_than_vm ig im ->
  consistent im iE s ->
  consistent om oE s.
Proof.
  (* mk_env_exp_hccache_consistent *)
  case: e. case=> //=.
  - move=> v z. mydestruct. move=> Hnew Hcon. exact: (mk_env_var_consistent H5 Hnew Hcon).
  - move=> bs z. by mydestruct.
  - move=> op e z. mydestruct.
    + move=> Hnew Hcon.
      exact: (mk_env_exp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H6 Hnew Hcon).
    + move=> Hnew Hcon.
      move: (mk_env_exp_hccache_newer_vm H6 Hnew) => Hnew3om.
      apply: (env_preserve_consistent Hnew3om (mk_env_eunop_preserve H12)).
      exact: (mk_env_exp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H6 Hnew Hcon).
  - move=> op e1 e2 z. mydestruct.
    + move=> Hnew Hcon.
      move: (mk_env_exp_hccache_newer_vm H6 Hnew) => Hnew31.
      apply: (mk_env_exp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H13 Hnew31).
      exact: (mk_env_exp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H6 Hnew).
    + move=> Hnew Hcon.
      move: (mk_env_exp_hccache_newer_vm H6 Hnew) => Hnew31.
      move: (mk_env_exp_hccache_newer_vm H13 Hnew31) => Hnew10om.
      apply: (env_preserve_consistent Hnew10om (mk_env_ebinop_preserve H19)).
      apply: (mk_env_exp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H13 Hnew31).
      exact: (mk_env_exp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H6 Hnew).
  - move=> e1 e2 e3 z. mydestruct.
    + move=> Hnew Hcon.
      move: (mk_env_bexp_hccache_newer_vm H6 Hnew) => Hnew31.
      move: (mk_env_exp_hccache_newer_vm H13 Hnew31) => Hnew108.
      apply: (mk_env_exp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H20 Hnew108).
      apply: (mk_env_exp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H13 Hnew31).
      exact: (mk_env_bexp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H6 Hnew Hcon).
    + move=> Hnew Hcon.
      move: (mk_env_bexp_hccache_newer_vm H6 Hnew) => Hnew31.
      move: (mk_env_exp_hccache_newer_vm H13 Hnew31) => Hnew108.
      move: (mk_env_exp_hccache_newer_vm H20 Hnew108) => Hnewogom.
      apply: (env_preserve_consistent Hnewogom (mk_env_ite_preserve H26)).
      apply: (mk_env_exp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H20 Hnew108).
      apply: (mk_env_exp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H13 Hnew31).
      exact: (mk_env_bexp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H6 Hnew Hcon).
  (* mk_env_bexp_hccache_consistent *)
  case: e. case=> //=.
  - move=> z. by mydestruct.
  - move=> z. by mydestruct.
  - move=> op e1 e2 z. mydestruct.
    + move=> Hnew Hcon.
      move: (mk_env_exp_hccache_newer_vm H6 Hnew) => Hnew31.
      apply: (mk_env_exp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H13 Hnew31).
      exact: (mk_env_exp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H6 Hnew).
    + move=> Hnew Hcon.
      move: (mk_env_exp_hccache_newer_vm H6 Hnew) => Hnew31.
      move: (mk_env_exp_hccache_newer_vm H13 Hnew31) => Hnew10om.
      apply: (env_preserve_consistent Hnew10om (mk_env_bbinop_preserve H19)).
      apply: (mk_env_exp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H13 Hnew31).
      exact: (mk_env_exp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H6 Hnew).
  - move=> e z. mydestruct.
    + move=> Hnew Hcon.
      exact: (mk_env_bexp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H6 Hnew Hcon).
    + move=> Hnew Hcon.
      move: (mk_env_bexp_hccache_newer_vm H6 Hnew) => Hnew3om.
      apply: (consistent_env_upd_newer _ Hnew3om _ (Pos.leb_refl H3)).
      exact: (mk_env_bexp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H6 Hnew Hcon).
  - move=> e1 e2 z. mydestruct.
    + move=> Hnew Hcon.
      move: (mk_env_bexp_hccache_newer_vm H6 Hnew) => Hnew31.
      apply: (mk_env_bexp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H13 Hnew31).
      exact: (mk_env_bexp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H6 Hnew).
    + move=> Hnew Hcon.
      move: (mk_env_bexp_hccache_newer_vm H6 Hnew) => Hnew31.
      move: (mk_env_bexp_hccache_newer_vm H13 Hnew31) => Hnew10om.
      apply: (consistent_env_upd_newer _ Hnew10om _ (Pos.leb_refl H10)).
      apply: (mk_env_bexp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H13 Hnew31).
      exact: (mk_env_bexp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H6 Hnew).
  - move=> e1 e2 z. mydestruct.
    + move=> Hnew Hcon.
      move: (mk_env_bexp_hccache_newer_vm H6 Hnew) => Hnew31.
      apply: (mk_env_bexp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H13 Hnew31).
      exact: (mk_env_bexp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H6 Hnew).
    + move=> Hnew Hcon.
      move: (mk_env_bexp_hccache_newer_vm H6 Hnew) => Hnew31.
      move: (mk_env_bexp_hccache_newer_vm H13 Hnew31) => Hnew10om.
      apply: (consistent_env_upd_newer _ Hnew10om _ (Pos.leb_refl H10)).
      apply: (mk_env_bexp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H13 Hnew31).
      exact: (mk_env_bexp_hccache_consistent _ _ _ _ _ _ _ _ _ _ _ _ H6 Hnew).
Qed.

Lemma mk_env_hbexps_hccache_conjs_rec_consistent
      iE s im ic ig ircs irlrs es oE om oc og ocs olrs :
  mk_env_hbexps_hccache_conjs_rec
    iE s im ic ig ircs irlrs (mapr hash_bexp es) = (oE, om, oc, og, ocs, olrs) ->
  newer_than_vm ig im ->
  consistent im iE s ->
  consistent om oE s.
Proof.
  elim: es iE s im ic ig ircs irlrs oE om oc og ocs olrs
  => [| e es IH] iE s im ic ig ircs irlrs oE om oc og ocs olrs //=.
  - case=> ? ? ? ? ? ? Hnew Hcon; subst. assumption.
  - rewrite mapr_cons. rewrite mk_env_hbexps_hccache_conjs_rec_rcons.
    dcase (mk_env_hbexps_hccache_conjs_rec iE s im ic ig ircs irlrs (mapr hash_bexp es))
    => [[[[[[E1 m1] c1] g1] cs1] lrs1] Henv1].
    rewrite mk_env_hbexps_hccache_conjs_rec_singleton.
    dcase (mk_env_bexp_hccache E1 s m1 c1 g1 (hash_bexp e))
    => [[[[[[E2 m2] c2] g2] cs2] lrs2] Henv2].
    case=> ? ? ? ? ? ?; subst. move=> Hnew1 Hcon1.
    move: (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Henv1 Hnew1 Hcon1) => Hcon2.
    move: (mk_env_hbexps_hccache_conjs_rec_newer_vm Henv1 Hnew1) => Hnew2.
    exact: (mk_env_bexp_hccache_consistent Henv2 Hnew2 Hcon2).
Qed.

Lemma mk_env_hbexps_hccache_conjs_consistent
      s es oE om oc og ocs olrs :
  mk_env_hbexps_hccache_conjs
    init_env s init_vm init_hccache init_gen (mapr hash_bexp es) = (oE, om, oc, og, ocs, olrs) ->    consistent om oE s.
Proof.
  move=> Henv. by apply: (mk_env_hbexps_hccache_conjs_rec_consistent Henv).
Qed.

Lemma mk_env_hbexps_hcache_conjs_sat_rec
      es TE s ihE ihm ihc ihg ihrcs ihrlrs ohE ohm ohc ohg ohcs ohlrs ifc icc :
  mk_env_hbexps_hccache_conjs_rec
    ihE s ihm ihc ihg ihrcs ihrlrs (mapr hash_bexp es) = (ohE, ohm, ohc, ohg, ohcs, ohlrs) ->
  QFBV.well_formed_bexps es TE ->
  AdhereConform.conform_bexps es s TE ->
  well_formed_ccache ihc ->
  ccache_compatible ihc ifc ->
  CCacheFlatten.ccache_compatible ifc icc ->
  CompCache.well_formed icc ->
  newer_than_vm ihg ihm ->
  newer_than_lit ihg lit_tt ->
  newer_than_cnf ihg (tflatten ihrcs) ->
  CompCache.newer_than_cache ihg icc ->
  CompCache.interp_cache ihE icc ->
  interp_cnf ihE (add_prelude (tflatten ihrcs)) ->
  interp_cnf ohE (add_prelude (tflatten (ohcs))).
Proof.
  move=> Henv Hwf Hco Hwfihc Hccifc Hccicc Hwficc Hnew_vm Hnew_lit Hnew_cnf Hnew_cache
              Hicicc Hicihrcs.
  rewrite add_prelude_expand in Hicihrcs. move/andP: Hicihrcs => [Htt_ihE Hicihrcs].
  move: (mk_env_hbexps_hccache_conjs_rec_cache_compatible_full
           Henv Hwf Hco Hwfihc Hccifc Hccicc Hwficc Hnew_vm Hnew_lit Hnew_cnf Hnew_cache
           Hicicc Hicihrcs)
  => [ofc [oc [Hccofc [Hccocc [Hwfocc [Hnew_ohg [Hnew_oc [Hohcs Hoc]]]]]]]].
  rewrite add_prelude_expand. rewrite Hohcs andbT.
  move: (mk_env_hbexps_hccache_conjs_rec_preserve Henv) => Hpre.
  rewrite (env_preserve_lit Hpre Hnew_lit). assumption.
Qed.

Lemma mk_env_hbexps_hcache_conjs_sat
  TE s es oE om oc og ocs olrs :
  mk_env_hbexps_hccache_conjs
    init_env s init_vm init_hccache init_gen (mapr hash_bexp es) = (oE, om, oc, og, ocs, olrs) ->
  QFBV.well_formed_bexps es TE ->
  AdhereConform.conform_bexps es s TE ->
  interp_cnf oE (add_prelude (tflatten (ocs))).
Proof.
  move=> Hhenv Hwf Hco.
  have init_newer_than_cnf_ihrcs: (newer_than_cnf init_gen (tflatten [::])) by done.
  have init_interp_cnf_ihrcs: interp_cnf init_env (add_prelude (tflatten [::])) by done.
  exact: (mk_env_hbexps_hcache_conjs_sat_rec
            Hhenv Hwf Hco init_hccache_well_formed init_hccache_fccache_compatible
            init_fccache_compatible init_ccache_well_formed
            init_newer_than_vm init_newer_than_tt init_newer_than_cnf_ihrcs
            init_newer_than_cache init_interp_cache init_interp_cnf_ihrcs).
Qed.



(* Completeness of bit_blast_hbexps_hccache_conjs *)

Lemma bit_blast_hbexps_hccache_conjs_sat_complete TE es m c g cs lrs :
  bit_blast_hbexps_hccache_conjs
    TE init_vm init_hccache init_gen (mapr hash_bexp es) = (m, c, g, cs, lrs) ->
  QFBV.well_formed_bexps es TE ->
  (exists s, AdhereConform.conform_bexps es s TE /\
             QFBV.eval_bexp (mk_conjs es) s) ->
  (sat (add_prelude (tflatten (lrs::cs)))).
Proof.
  move=> Hhbb Hwf [s [Hco Hev]].
  dcase (mk_env_hbexps_hccache_conjs
           init_env s init_vm init_hccache init_gen (mapr hash_bexp es)) =>
  [[[[[[ovE ovm] ovc] ovg] ovcs] ovlrs] Hhenv].
  move: (mk_env_hbexps_hccache_conjs_is_bit_blast_hbexps_hccache_conjs Hco Hwf Hhenv Hhbb) =>
  [? [? [? [? ?]]]]; subst.
  move: (mk_env_hbexps_hcache_conjs_sat Hhenv Hwf Hco) => Hcs.
  move: (add_prelude_tt Hcs) => Htt.
  move: (bit_blast_hbexps_hccache_conjs_size Hhbb) => [Hs1 Hs2].

  move: (mk_env_hbexps_hccache_conjs_consistent Hhenv) => Hcon.
  move: (bit_blast_hbexps_hccache_conjs_enc_bits Hhbb Hwf Hcs Hco Hcon).
  rewrite /enc_bits => Henc.

  exists ovE.
  rewrite interp_cnf_add_prelude_tflatten_cons. rewrite Hcs andbT.
  rewrite size_mapr in Hs1.
  exact: (interp_word_interp_cnf Hev Hs1 Hs2 Htt Henc).
Qed.

Theorem bit_blast_bexps_hccache_conjs_sat_complete TE es :
  QFBV.well_formed_bexps es TE ->
  (exists s, AdhereConform.conform_bexps es s TE /\
             QFBV.eval_bexp (mk_conjs es) s) ->
  (sat (bit_blast_bexps_hccache_conjs TE es)).
Proof.
  move=> Hwf. rewrite /bit_blast_bexps_hccache_conjs.
  dcase (bit_blast_hbexps_hccache_conjs
           TE init_vm init_hccache init_gen
           (mapr hash_bexp es)) => [[[[[m c] g] cs] lrs] Hbb].
  move=> Hev.
  exact: (bit_blast_hbexps_hccache_conjs_sat_complete Hbb Hwf Hev).
Qed.
