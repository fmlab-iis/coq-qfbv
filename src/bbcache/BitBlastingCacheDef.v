From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
From BBCache Require Import Cache BitBlastingCCacheDef.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ==== bit_blast_exp_cache and bit_blast_bexp_cache ==== *)

Fixpoint bit_blast_exp_cache te m c g e : vm * cache * generator * cnf * word :=
  (* = bit_blast_exp_nocet = *)
  let bit_blast_exp_nocet te m c g e : vm * cache * generator * cnf * word :=
      match e with
      | QFBV.Evar v =>
        match find_het e c with
        | Some (cs, ls) => (m, c, g, cs, ls)
        | None => match SSAVM.find v m with
                  | None => let '(g', cs, rs) := bit_blast_var te g v in
                            (SSAVM.add v rs m, add_het e cs rs c, g', cs, rs)
                  | Some rs => (m, add_het e [::] rs c, g, [::], rs)
                  end
        end
      | QFBV.Econst bs => 
        match find_het e c with
        | Some (cs, ls) => (m, c, g, cs, ls)
        | None => let '(g', cs, rs) := bit_blast_const g bs in
                  (m, add_het e cs rs c, g', cs, rs)
        end
      | QFBV.Eunop op e1 =>
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_cache te m c g e1 in
        match find_het e c1 with
        | Some (csop, lsop) => (m1, c1, g1, catrev cs1 csop, lsop)
        | None =>
          let '(gop, csop, lsop) := bit_blast_eunop op g1 ls1 in
          (m1, add_het e csop lsop c1, gop, catrev cs1 csop, lsop)
        end
      | QFBV.Ebinop op e1 e2 =>
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_cache te m c g e1 in
        let '(m2, c2, g2, cs2, ls2) := bit_blast_exp_cache te m1 c1 g1 e2 in
        match find_het e c2 with
        | Some (csop, lsop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lsop)
        | None => 
          let '(gop, csop, lsop) := bit_blast_ebinop op g2 ls1 ls2 in
          (m2, add_het e csop lsop c2, gop, catrev cs1 (catrev cs2 csop), lsop)
        end
      | QFBV.Eite b e1 e2 => 
        let '(mb, cb, gb, csb, lb) := bit_blast_bexp_cache te m c g b in
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_cache te mb cb gb e1 in
        let '(m2, c2, g2, cs2, ls2) := bit_blast_exp_cache te m1 c1 g1 e2 in
        match find_het e c2 with
        | Some (csop, lsop) => 
          (m2, c2, g2, catrev csb (catrev cs1 (catrev cs2 csop)), lsop)
        | None => 
          let '(gop, csop, lsop) := bit_blast_ite g2 lb ls1 ls2 in
          (m2, add_het e csop lsop c2, gop, 
           catrev csb (catrev cs1 (catrev cs2 csop)), lsop)
        end
      end
  (* = = *)
  in
  match find_cet e c with
  | Some ls => (m, c, g, [::], ls)
  | None => let '(m', c', g', cs, lrs) := bit_blast_exp_nocet te m c g e in
            (m', add_cet e lrs c', g', cs, lrs)
  end
with
bit_blast_bexp_cache te m c g e : vm * cache * generator * cnf * literal :=
  (* = bit_blast_bexp_nocbt = *)
  let bit_blast_bexp_nocbt te m c g e : vm * cache * generator * cnf * literal :=
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
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_cache te m c g e1 in
        let '(m2, c2, g2, cs2, ls2) := bit_blast_exp_cache te m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lop)
        | None => 
          let '(gop, csop, lop) := bit_blast_bbinop op g2 ls1 ls2 in
          (m2, add_hbt e csop lop c2, gop, catrev cs1 (catrev cs2 csop), lop)
        end
      | QFBV.Blneg e1 => 
        let '(m1, c1, g1, cs1, l1) := bit_blast_bexp_cache te m c g e1 in
        match find_hbt e c1 with
        | Some (csop, lop) => (m1, c1, g1, catrev cs1 csop, lop)
        | None => let '(gop, csop, lop) := bit_blast_lneg g1 l1 in
                  (m1, add_hbt e csop lop c1, gop, catrev cs1 csop, lop)
        end
      | QFBV.Bconj e1 e2 => 
        let '(m1, c1, g1, cs1, l1) := bit_blast_bexp_cache te m c g e1 in
        let '(m2, c2, g2, cs2, l2) := bit_blast_bexp_cache te m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lop)
        | None => let '(gop, csop, lop) := bit_blast_conj g2 l1 l2 in
                  (m2, add_hbt e csop lop c2, gop, 
                   catrev cs1 (catrev cs2 csop), lop)
        end
      | QFBV.Bdisj e1 e2 => 
        let '(m1, c1, g1, cs1, l1) := bit_blast_bexp_cache te m c g e1 in
        let '(m2, c2, g2, cs2, l2) := bit_blast_bexp_cache te m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lop)
        | None => let '(gop, csop, lop) := bit_blast_disj g2 l1 l2 in
                  (m2, add_hbt e csop lop c2, gop, 
                   catrev cs1 (catrev cs2 csop), lop)
        end
      end
  (* = = *)
  in
  match find_cbt e c with
  | Some l => (m, c, g, [::], l)
  | None => let '(m', c', g', cs, lr) := bit_blast_bexp_nocbt te m c g e in
            (m', add_cbt e lr c', g', cs, lr)
  end.


Lemma bit_blast_exp_cache_equation : 
  forall te m c g e,
    bit_blast_exp_cache te m c g e =
  (* = bit_blast_exp_nocet = *)
  let bit_blast_exp_nocet te m c g e : vm * cache * generator * cnf * word :=
      match e with
      | QFBV.Evar v =>
        match find_het e c with
        | Some (cs, ls) => (m, c, g, cs, ls)
        | None => match SSAVM.find v m with
                  | None => let '(g', cs, rs) := bit_blast_var te g v in
                            (SSAVM.add v rs m, add_het e cs rs c, g', cs, rs)
                  | Some rs => (m, add_het e [::] rs c, g, [::], rs)
                  end
        end
      | QFBV.Econst bs => 
        match find_het e c with
        | Some (cs, ls) => (m, c, g, cs, ls)
        | None => let '(g', cs, rs) := bit_blast_const g bs in
                  (m, add_het e cs rs c, g', cs, rs)
        end
      | QFBV.Eunop op e1 =>
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_cache te m c g e1 in
        match find_het e c1 with
        | Some (csop, lsop) => (m1, c1, g1, catrev cs1 csop, lsop)
        | None =>
          let '(gop, csop, lsop) := bit_blast_eunop op g1 ls1 in
          (m1, add_het e csop lsop c1, gop, catrev cs1 csop, lsop)
        end
      | QFBV.Ebinop op e1 e2 =>
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_cache te m c g e1 in
        let '(m2, c2, g2, cs2, ls2) := bit_blast_exp_cache te m1 c1 g1 e2 in
        match find_het e c2 with
        | Some (csop, lsop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lsop)
        | None => 
          let '(gop, csop, lsop) := bit_blast_ebinop op g2 ls1 ls2 in
          (m2, add_het e csop lsop c2, gop, catrev cs1 (catrev cs2 csop), lsop)
        end
      | QFBV.Eite b e1 e2 => 
        let '(mb, cb, gb, csb, lb) := bit_blast_bexp_cache te m c g b in
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_cache te mb cb gb e1 in
        let '(m2, c2, g2, cs2, ls2) := bit_blast_exp_cache te m1 c1 g1 e2 in
        match find_het e c2 with
        | Some (csop, lsop) => 
          (m2, c2, g2, catrev csb (catrev cs1 (catrev cs2 csop)), lsop)
        | None => 
          let '(gop, csop, lsop) := bit_blast_ite g2 lb ls1 ls2 in
          (m2, add_het e csop lsop c2, gop, 
           catrev csb (catrev cs1 (catrev cs2 csop)), lsop)
        end
      end
  (* = = *)
  in
  match find_cet e c with
  | Some ls => (m, c, g, [::], ls)
  | None => let '(m', c', g', cs, lrs) := bit_blast_exp_nocet te m c g e in
            (m', add_cet e lrs c', g', cs, lrs)
  end.
Proof. move=> te m cc g e. elim e; done. Qed.

Lemma bit_blast_bexp_cache_equation :
  forall te m c g e,
    bit_blast_bexp_cache te m c g e =
  (* = bit_blast_bexp_nocbt = *)
  let bit_blast_bexp_nocbt te m c g e : vm * cache * generator * cnf * literal :=
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
        let '(m1, c1, g1, cs1, ls1) := bit_blast_exp_cache te m c g e1 in
        let '(m2, c2, g2, cs2, ls2) := bit_blast_exp_cache te m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lop)
        | None => 
          let '(gop, csop, lop) := bit_blast_bbinop op g2 ls1 ls2 in
          (m2, add_hbt e csop lop c2, gop, catrev cs1 (catrev cs2 csop), lop)
        end
      | QFBV.Blneg e1 => 
        let '(m1, c1, g1, cs1, l1) := bit_blast_bexp_cache te m c g e1 in
        match find_hbt e c1 with
        | Some (csop, lop) => (m1, c1, g1, catrev cs1 csop, lop)
        | None => let '(gop, csop, lop) := bit_blast_lneg g1 l1 in
                  (m1, add_hbt e csop lop c1, gop, catrev cs1 csop, lop)
        end
      | QFBV.Bconj e1 e2 => 
        let '(m1, c1, g1, cs1, l1) := bit_blast_bexp_cache te m c g e1 in
        let '(m2, c2, g2, cs2, l2) := bit_blast_bexp_cache te m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lop)
        | None => let '(gop, csop, lop) := bit_blast_conj g2 l1 l2 in
                  (m2, add_hbt e csop lop c2, gop, 
                   catrev cs1 (catrev cs2 csop), lop)
        end
      | QFBV.Bdisj e1 e2 => 
        let '(m1, c1, g1, cs1, l1) := bit_blast_bexp_cache te m c g e1 in
        let '(m2, c2, g2, cs2, l2) := bit_blast_bexp_cache te m1 c1 g1 e2 in
        match find_hbt e c2 with
        | Some (csop, lop) => (m2, c2, g2, catrev cs1 (catrev cs2 csop), lop)
        | None => let '(gop, csop, lop) := bit_blast_disj g2 l1 l2 in
                  (m2, add_hbt e csop lop c2, gop, 
                   catrev cs1 (catrev cs2 csop), lop)
        end
      end
  (* = = *)
  in
  match find_cbt e c with
  | Some l => (m, c, g, [::], l)
  | None => let '(m', c', g', cs, lr) := bit_blast_bexp_nocbt te m c g e in
            (m', add_cbt e lr c', g', cs, lr)
  end.
Proof. move=> te m cc g e. elim e; done. Qed.


(* = bit_blast_exp_cache_is_bit_blast_exp_ccache and 
     bit_blast_bexp_cache_is_bit_blast_bexp_ccache = *)

Ltac auto_prove_exist :=
  match goal with
  | |- exists cc', (?m, ?cc, ?g, ?cs, ?ls) = (?m, cc', ?g, ?cs, ?ls) 
                  /\ compatible ?c cc' =>
    exists cc; split; first done; 
    try (apply compatible_add_cet || apply compatible_add_cbt); 
    try (apply compatible_add_het || apply compatible_add_hbt)
  end .

Lemma bit_blast_exp_cache_is_bit_blast_exp_ccache :
  forall e te m c g m' c' g' cs ls cc,
    Cache.compatible c cc
    -> bit_blast_exp_cache te m c g e = (m', c', g', cs, ls)
    -> exists cc', bit_blast_exp_ccache te m cc g e = (m', cc', g', cs, ls) 
                   /\ Cache.compatible c' cc'
  with
    bit_blast_bexp_cache_is_bit_blast_bexp_ccache :
      forall e te m c g m' c' g' cs l cc,
        Cache.compatible c cc
        -> bit_blast_bexp_cache te m c g e = (m', c', g', cs, l)
        -> exists cc', bit_blast_bexp_ccache te m cc g e = (m', cc', g', cs, l) 
                       /\ Cache.compatible c' cc'.
Proof.
  (* exp *)
  set IHe := bit_blast_exp_cache_is_bit_blast_exp_ccache.
  set IHb := bit_blast_bexp_cache_is_bit_blast_bexp_ccache.
  move=> e te m c g m' c' g' cs ls cc Hcomp.
  case Hfcetc: (find_cet e c) => [lse | ]. 
  - rewrite bit_blast_exp_cache_equation Hfcetc /=.
    case=> <- <- <- <- <-. 
    move: (compatible_find_cet_some Hcomp Hfcetc) => [cse Hfcetcc].
    rewrite bit_blast_exp_ccache_equation Hfcetcc /=.
    by auto_prove_exist.
  - move: e te m c g m' c' g' cs ls cc Hcomp Hfcetc.
    case => [ v | bs | op e1 | op e1 e2 | b e1 e2 ]; 
      move=> te m c g m' c' g' cs ls cc Hcomp Hfcetc; rewrite /= Hfcetc;
      move: (compatible_find_cet_none Hcomp Hfcetc) => ->.
    + case Hfhetc : (find_het (QFBV.Evar v) c) => [[cse lse] | ];
        rewrite -(compatible_find_het _ Hcomp) Hfhetc;
        last case Hfv : (SSAVM.find v m) => [ rs | ] ;
        last case Hbbv : (bit_blast_var te g v) => [[vg vcs] vls];
        case=> <- <- <- <- <-; by auto_prove_exist.
    + case Hfhetc : (find_het (QFBV.Econst bs) c) => [[cse lse] | ];
        rewrite -(compatible_find_het _ Hcomp) Hfhetc;
        case=> <- <- <- <- <-; by auto_prove_exist.
    + case He1 : (bit_blast_exp_cache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ Hcomp He1) => [cc1 [-> Hcomp1]].
      case Hfhetc : (find_het (QFBV.Eunop op e1) c1) => [[csop lsop] | ];
        rewrite -(compatible_find_het _ Hcomp1) Hfhetc;
        last case Hbbop : (bit_blast_eunop op g1 ls1) => [[gop csop] lsop];
        case=> <- <- <- <- <-; by auto_prove_exist.
    + case He1 : (bit_blast_exp_cache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ Hcomp He1) => [cc1 [-> Hcomp1]].
      case He2 : (bit_blast_exp_cache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ Hcomp1 He2) => [cc2 [-> Hcomp2]].
      case Hfhetc : (find_het (QFBV.Ebinop op e1 e2) c2) => [[csop lsop] | ];
        rewrite -(compatible_find_het _ Hcomp2) Hfhetc;
        last case Hbbop : (bit_blast_ebinop op g2 ls1 ls2) => [[gop csop] lsop];
        case=> <- <- <- <- <-; by auto_prove_exist.
    + case Hb : (bit_blast_bexp_cache te m c g b) => [[[[mb cb] gb] csb] lb].
      move: (IHb _ _ _ _ _ _ _ _ _ _ _ Hcomp Hb) => [ccb [-> Hcompb]].
      case He1 : (bit_blast_exp_cache te mb cb gb e1) => [[[[m1 c1] g1] cs1] ls1].
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ Hcompb He1) => [cc1 [-> Hcomp1]].
      case He2 : (bit_blast_exp_cache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ Hcomp1 He2) => [cc2 [-> Hcomp2]].
      case Hfhetc : (find_het (QFBV.Eite b e1 e2) c2) => [[csop lsop] | ];
        rewrite -(compatible_find_het _ Hcomp2) Hfhetc;
        last case Hbbop : (bit_blast_ite g2 lb ls1 ls2) => [[gop csop] lsop];
        case=> <- <- <- <- <-; by auto_prove_exist.
  (* bexp *)
  set IHe := bit_blast_exp_cache_is_bit_blast_exp_ccache.
  set IHb := bit_blast_bexp_cache_is_bit_blast_bexp_ccache.
  move=> e te m c g m' c' g' cs l cc Hcomp.
  case Hfcbtc: (find_cbt e c) => [le | ]. 
  - rewrite bit_blast_bexp_cache_equation Hfcbtc /=.
    case=> <- <- <- <- <-. 
    move: (compatible_find_cbt_some Hcomp Hfcbtc) => [cse Hfcbtcc].
    rewrite bit_blast_bexp_ccache_equation Hfcbtcc /=.
    by auto_prove_exist.
  - move: e te m c g m' c' g' cs l cc Hcomp Hfcbtc.
    case => [ | | op e1 e2 | e1 | e1 e2 | e1 e2 ]; 
      move=> te m c g m' c' g' cs l cc Hcomp Hfcbtc; rewrite /= Hfcbtc;
      move: (compatible_find_cbt_none Hcomp Hfcbtc) => ->.
    + case Hfhbtc : (find_hbt (QFBV.Bfalse) c) => [[cse le] | ];
        rewrite -(compatible_find_hbt _ Hcomp) Hfhbtc;
        case=> <- <- <- <- <-; by auto_prove_exist.
    + case Hfhbtc : (find_hbt (QFBV.Btrue) c) => [[cse le] | ];
        rewrite -(compatible_find_hbt _ Hcomp) Hfhbtc;
        case=> <- <- <- <- <-; by auto_prove_exist.
    + case He1 : (bit_blast_exp_cache te m c g e1) => [[[[m1 c1] g1] cs1] ls1].
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ Hcomp He1) => [cc1 [-> Hcomp1]].
      case He2 : (bit_blast_exp_cache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] ls2].
      move: (IHe _ _ _ _ _ _ _ _ _ _ _ Hcomp1 He2) => [cc2 [-> Hcomp2]].
      case Hfhbtc : (find_hbt (QFBV.Bbinop op e1 e2) c2) => [[csop lop] | ];
        rewrite -(compatible_find_hbt _ Hcomp2) Hfhbtc;
        last case Hbbop : (bit_blast_bbinop op g2 ls1 ls2) => [[gop csop] lop];
        case=> <- <- <- <- <-; by auto_prove_exist.
    + case He1 : (bit_blast_bexp_cache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
      move: (IHb _ _ _ _ _ _ _ _ _ _ _ Hcomp He1) => [cc1 [-> Hcomp1]].
      case Hfhbtc : (find_hbt (QFBV.Blneg e1) c1) => [[csop lop] | ];
        rewrite -(compatible_find_hbt _ Hcomp1) Hfhbtc;
        case=> <- <- <- <- <-; by auto_prove_exist.
    + case He1 : (bit_blast_bexp_cache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
      move: (IHb _ _ _ _ _ _ _ _ _ _ _ Hcomp He1) => [cc1 [-> Hcomp1]].
      case He2 : (bit_blast_bexp_cache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
      move: (IHb _ _ _ _ _ _ _ _ _ _ _ Hcomp1 He2) => [cc2 [-> Hcomp2]].
      case Hfhbtc : (find_hbt (QFBV.Bconj e1 e2) c2) => [[csop lop] | ];
        rewrite -(compatible_find_hbt _ Hcomp2) Hfhbtc;
        case=> <- <- <- <- <-; by auto_prove_exist.
    + case He1 : (bit_blast_bexp_cache te m c g e1) => [[[[m1 c1] g1] cs1] l1].
      move: (IHb _ _ _ _ _ _ _ _ _ _ _ Hcomp He1) => [cc1 [-> Hcomp1]].
      case He2 : (bit_blast_bexp_cache te m1 c1 g1 e2) => [[[[m2 c2] g2] cs2] l2].
      move: (IHb _ _ _ _ _ _ _ _ _ _ _ Hcomp1 He2) => [cc2 [-> Hcomp2]].
      case Hfhbtc : (find_hbt (QFBV.Bdisj e1 e2) c2) => [[csop lop] | ];
        rewrite -(compatible_find_hbt _ Hcomp2) Hfhbtc;
        case=> <- <- <- <- <-; by auto_prove_exist.
Qed.

