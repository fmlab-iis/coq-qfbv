From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
From BBCache Require Import CompCache.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ==== bit-blasting with complete cache information ==== *)

Definition bit_blast_eunop (op : QFBV.eunop) :=
  match op with
  | QFBV.Unot => bit_blast_not
  | QFBV.Uneg => bit_blast_neg
  | QFBV.Uextr i j => (fun g ls => bit_blast_extract g i j ls)
  | QFBV.Uhigh n => (fun g ls => bit_blast_high g n ls)
  | QFBV.Ulow n => (fun g ls => bit_blast_low g n ls)
  | QFBV.Uzext n => bit_blast_zeroextend n
  | QFBV.Usext n => bit_blast_signextend n
  | QFBV.Urepeat n => (fun g ls => bit_blast_repeat g n ls)
  | QFBV.Urotl n => (fun g ls => bit_blast_rotateleft g n ls)
  | QFBV.Urotr n => (fun g ls => bit_blast_rotateright g n ls)
  end .

Definition bit_blast_ebinop (op : QFBV.ebinop) :=
  match op with
  | QFBV.Band => bit_blast_and
  | QFBV.Bor => bit_blast_or 
  | QFBV.Bxor => bit_blast_xor 
  | QFBV.Badd => bit_blast_add 
  | QFBV.Bsub => bit_blast_sub 
  | QFBV.Bmul => bit_blast_mul 
  | QFBV.Bmod => bit_blast_umod
  | QFBV.Bsrem => bit_blast_srem
  | QFBV.Bsmod => bit_blast_smod
  | QFBV.Bshl => bit_blast_shl 
  | QFBV.Blshr => bit_blast_lshr 
  | QFBV.Bashr => bit_blast_ashr 
  | QFBV.Bconcat => bit_blast_concat 
  | QFBV.Bcomp => bit_blast_comp
  end .

Definition bit_blast_bbinop (op : QFBV.bbinop) :=
  match op with
  | QFBV.Beq => bit_blast_eq 
  | QFBV.Bult => bit_blast_ult 
  | QFBV.Bule => bit_blast_ule 
  | QFBV.Bugt => bit_blast_ugt 
  | QFBV.Buge => bit_blast_uge 
  | QFBV.Bslt => bit_blast_slt 
  | QFBV.Bsle => bit_blast_sle 
  | QFBV.Bsgt => bit_blast_sgt 
  | QFBV.Bsge => bit_blast_sge 
  | QFBV.Buaddo => bit_blast_uaddo 
  | QFBV.Busubo => bit_blast_usubo 
  | QFBV.Bumulo => bit_blast_umulo 
  | QFBV.Bsaddo => bit_blast_saddo 
  | QFBV.Bssubo => bit_blast_ssubo 
  | QFBV.Bsmulo => bit_blast_smulo 
  end .

Fixpoint bit_blast_exp_ccache te m cc g e :
  vm * compcache * generator * cnf * word :=
  (* = bit_blast_exp_nocet = *)
  let bit_blast_exp_nocet te m cc g e : 
        vm * compcache * generator * cnf * word * cnf :=
      match e with
      | QFBV.Evar v =>
        match find_het e cc with
        | Some (cs, ls) => (m, cc, g, cs, ls, cs)
        | None => match SSAVM.find v m with
                  | None => let '(g', cs, rs) := bit_blast_var te g v in
                            (SSAVM.add v rs m, add_het e cs rs cc, g', cs, rs, cs)
                  | Some rs => (m, add_het e [::] rs cc, g, [::], rs, [::])
                  end
        end
      | QFBV.Econst bs => 
        match find_het e cc with
        | Some (cs, ls) => (m, cc, g, cs, ls, cs)
        | None => let '(g', cs, rs) := bit_blast_const g bs in
                  (m, add_het e cs rs cc, g', cs, rs, cs)
        end
      | QFBV.Eunop op e1 =>
        let '(m1, cc1, g1, cs1, ls1) := bit_blast_exp_ccache te m cc g e1 in
        match find_het e cc1 with
        | Some (csop, lsop) => (m1, cc1, g1, catrev cs1 csop, lsop, csop)
        | None =>
          let '(gop, csop, lsop) := bit_blast_eunop op g1 ls1 in
          (m1, add_het e csop lsop cc1, gop, catrev cs1 csop, lsop, csop)
        end
      | QFBV.Ebinop op e1 e2 =>
        let '(m1, cc1, g1, cs1, ls1) := bit_blast_exp_ccache te m cc g e1 in
        let '(m2, cc2, g2, cs2, ls2) := bit_blast_exp_ccache te m1 cc1 g1 e2 in
        match find_het e cc2 with
        | Some (csop, lsop) => (m2, cc2, g2, catrev cs1 (catrev cs2 csop), lsop, csop)
        | None => 
          let '(gop, csop, lsop) := bit_blast_ebinop op g2 ls1 ls2 in
          (m2, add_het e csop lsop cc2, gop, catrev cs1 (catrev cs2 csop), lsop, csop)
        end
      | QFBV.Eite c e1 e2 => 
        let '(mc, ccc, gc, csc, lc) := bit_blast_bexp_ccache te m cc g c in
        let '(m1, cc1, g1, cs1, ls1) := bit_blast_exp_ccache te mc ccc gc e1 in
        let '(m2, cc2, g2, cs2, ls2) := bit_blast_exp_ccache te m1 cc1 g1 e2 in
        match find_het e cc2 with
        | Some (csop, lsop) => 
          (m2, cc2, g2, catrev csc (catrev cs1 (catrev cs2 csop)), lsop, csop)
        | None => 
          let '(gop, csop, lsop) := bit_blast_ite g2 lc ls1 ls2 in
          (m2, add_het e csop lsop cc2, gop, 
           catrev csc (catrev cs1 (catrev cs2 csop)), lsop, csop)
        end
      end
  (* = = *)
  in
  match CompCache.find_cet e cc with
  | Some (cs, ls) => (m, cc, g, [::], ls)
  | None => let '(m', cc', g', cs, lrs, csop) := bit_blast_exp_nocet te m cc g e in
            (m', CompCache.add_cet e csop lrs cc', g', cs, lrs)
  end
with
bit_blast_bexp_ccache te m cc g e : vm * compcache * generator * cnf * literal :=
  (* = bit_blast_bexp_nocbt = *)
  let bit_blast_bexp_nocbt te m cc g e : 
        vm * compcache * generator * cnf * literal * cnf :=
      match e with
      | QFBV.Bfalse => 
        match find_hbt e cc with
        | Some (cs, l) => (m, cc, g, cs, l, cs)
        | None => (m, add_hbt e [::] lit_ff cc, g, [::], lit_ff, [::])
        end
      | QFBV.Btrue => 
        match find_hbt e cc with
        | Some (cs, l) => (m, cc, g, cs, l, cs)
        | None => (m, add_hbt e [::] lit_tt cc, g, [::], lit_tt, [::])
        end
      | QFBV.Bbinop op e1 e2 =>
        let '(m1, cc1, g1, cs1, ls1) := bit_blast_exp_ccache te m cc g e1 in
        let '(m2, cc2, g2, cs2, ls2) := bit_blast_exp_ccache te m1 cc1 g1 e2 in
        match find_hbt e cc2 with
        | Some (csop, lop) => (m2, cc2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None => 
          let '(gop, csop, lop) := bit_blast_bbinop op g2 ls1 ls2 in
          (m2, add_hbt e csop lop cc2, gop, catrev cs1 (catrev cs2 csop), lop, csop)
        end
      | QFBV.Blneg e1 => 
        let '(m1, cc1, g1, cs1, l1) := bit_blast_bexp_ccache te m cc g e1 in
        match find_hbt e cc1 with
        | Some (csop, lop) => (m1, cc1, g1, catrev cs1 csop, lop, csop)
        | None => let '(gop, csop, lop) := bit_blast_lneg g1 l1 in
                  (m1, add_hbt e csop lop cc1, gop, catrev cs1 csop, lop, csop)
        end
      | QFBV.Bconj e1 e2 => 
        let '(m1, cc1, g1, cs1, l1) := bit_blast_bexp_ccache te m cc g e1 in
        let '(m2, cc2, g2, cs2, l2) := bit_blast_bexp_ccache te m1 cc1 g1 e2 in
        match find_hbt e cc2 with
        | Some (csop, lop) => (m2, cc2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None => let '(gop, csop, lop) := bit_blast_conj g2 l1 l2 in
                  (m2, add_hbt e csop lop cc2, gop, 
                   catrev cs1 (catrev cs2 csop), lop, csop)
        end
      | QFBV.Bdisj e1 e2 => 
        let '(m1, cc1, g1, cs1, l1) := bit_blast_bexp_ccache te m cc g e1 in
        let '(m2, cc2, g2, cs2, l2) := bit_blast_bexp_ccache te m1 cc1 g1 e2 in
        match find_hbt e cc2 with
        | Some (csop, lop) => (m2, cc2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None => let '(gop, csop, lop) := bit_blast_disj g2 l1 l2 in
                  (m2, add_hbt e csop lop cc2, gop, 
                   catrev cs1 (catrev cs2 csop), lop, csop)
        end
      end
  (* = = *)
  in
  match CompCache.find_cbt e cc with
  | Some (cs, l) => (m, cc, g, [::], l)
  | None => let '(m', cc', g', cs, lr, csop) := bit_blast_bexp_nocbt te m cc g e in
            (m', CompCache.add_cbt e csop lr cc', g', cs, lr)
  end.


Lemma bit_blast_exp_ccache_equation : 
  forall te m cc g e, 
    bit_blast_exp_ccache te m cc g e =
  (* = bit_blast_exp_nocet = *)
  let bit_blast_exp_nocet te m cc g e : 
        vm * compcache * generator * cnf * word * cnf :=
      match e with
      | QFBV.Evar v =>
        match find_het e cc with
        | Some (cs, ls) => (m, cc, g, cs, ls, cs)
        | None => match SSAVM.find v m with
                  | None => let '(g', cs, rs) := bit_blast_var te g v in
                            (SSAVM.add v rs m, add_het e cs rs cc, g', cs, rs, cs)
                  | Some rs => (m, add_het e [::] rs cc, g, [::], rs, [::])
                  end
        end
      | QFBV.Econst bs => 
        match find_het e cc with
        | Some (cs, ls) => (m, cc, g, cs, ls, cs)
        | None => let '(g', cs, rs) := bit_blast_const g bs in
                  (m, add_het e cs rs cc, g', cs, rs, cs)
        end
      | QFBV.Eunop op e1 =>
        let '(m1, cc1, g1, cs1, ls1) := bit_blast_exp_ccache te m cc g e1 in
        match find_het e cc1 with
        | Some (csop, lsop) => (m1, cc1, g1, catrev cs1 csop, lsop, csop)
        | None =>
          let '(gop, csop, lsop) := bit_blast_eunop op g1 ls1 in
          (m1, add_het e csop lsop cc1, gop, catrev cs1 csop, lsop, csop)
        end
      | QFBV.Ebinop op e1 e2 =>
        let '(m1, cc1, g1, cs1, ls1) := bit_blast_exp_ccache te m cc g e1 in
        let '(m2, cc2, g2, cs2, ls2) := bit_blast_exp_ccache te m1 cc1 g1 e2 in
        match find_het e cc2 with
        | Some (csop, lsop) => (m2, cc2, g2, catrev cs1 (catrev cs2 csop), lsop, csop)
        | None => 
          let '(gop, csop, lsop) := bit_blast_ebinop op g2 ls1 ls2 in
          (m2, add_het e csop lsop cc2, gop, catrev cs1 (catrev cs2 csop), lsop, csop)
        end
      | QFBV.Eite c e1 e2 => 
        let '(mc, ccc, gc, csc, lc) := bit_blast_bexp_ccache te m cc g c in
        let '(m1, cc1, g1, cs1, ls1) := bit_blast_exp_ccache te mc ccc gc e1 in
        let '(m2, cc2, g2, cs2, ls2) := bit_blast_exp_ccache te m1 cc1 g1 e2 in
        match find_het e cc2 with
        | Some (csop, lsop) => 
          (m2, cc2, g2, catrev csc (catrev cs1 (catrev cs2 csop)), lsop, csop)
        | None => 
          let '(gop, csop, lsop) := bit_blast_ite g2 lc ls1 ls2 in
          (m2, add_het e csop lsop cc2, gop, 
           catrev csc (catrev cs1 (catrev cs2 csop)), lsop, csop)
        end
      end
  (* = = *)
  in
  match CompCache.find_cet e cc with
  | Some (cs, ls) => (m, cc, g, [::], ls)
  | None => let '(m', cc', g', cs, lrs, csop) := bit_blast_exp_nocet te m cc g e in
            (m', CompCache.add_cet e csop lrs cc', g', cs, lrs)
  end.
Proof. move=> te m cc g e. elim e; done. Qed.

Lemma bit_blast_bexp_ccache_equation :
  forall te m cc g e, 
    bit_blast_bexp_ccache te m cc g e =
  (* = bit_blast_bexp_nocbt = *)
  let bit_blast_bexp_nocbt te m cc g e : 
        vm * compcache * generator * cnf * literal * cnf :=
      match e with
      | QFBV.Bfalse => 
        match find_hbt e cc with
        | Some (cs, l) => (m, cc, g, cs, l, cs)
        | None => (m, add_hbt e [::] lit_ff cc, g, [::], lit_ff, [::])
        end
      | QFBV.Btrue => 
        match find_hbt e cc with
        | Some (cs, l) => (m, cc, g, cs, l, cs)
        | None => (m, add_hbt e [::] lit_tt cc, g, [::], lit_tt, [::])
        end
      | QFBV.Bbinop op e1 e2 =>
        let '(m1, cc1, g1, cs1, ls1) := bit_blast_exp_ccache te m cc g e1 in
        let '(m2, cc2, g2, cs2, ls2) := bit_blast_exp_ccache te m1 cc1 g1 e2 in
        match find_hbt e cc2 with
        | Some (csop, lop) => (m2, cc2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None => 
          let '(gop, csop, lop) := bit_blast_bbinop op g2 ls1 ls2 in
          (m2, add_hbt e csop lop cc2, gop, catrev cs1 (catrev cs2 csop), lop, csop)
        end
      | QFBV.Blneg e1 => 
        let '(m1, cc1, g1, cs1, l1) := bit_blast_bexp_ccache te m cc g e1 in
        match find_hbt e cc1 with
        | Some (csop, lop) => (m1, cc1, g1, catrev cs1 csop, lop, csop)
        | None => let '(gop, csop, lop) := bit_blast_lneg g1 l1 in
                  (m1, add_hbt e csop lop cc1, gop, catrev cs1 csop, lop, csop)
        end
      | QFBV.Bconj e1 e2 => 
        let '(m1, cc1, g1, cs1, l1) := bit_blast_bexp_ccache te m cc g e1 in
        let '(m2, cc2, g2, cs2, l2) := bit_blast_bexp_ccache te m1 cc1 g1 e2 in
        match find_hbt e cc2 with
        | Some (csop, lop) => (m2, cc2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None => let '(gop, csop, lop) := bit_blast_conj g2 l1 l2 in
                  (m2, add_hbt e csop lop cc2, gop, 
                   catrev cs1 (catrev cs2 csop), lop, csop)
        end
      | QFBV.Bdisj e1 e2 => 
        let '(m1, cc1, g1, cs1, l1) := bit_blast_bexp_ccache te m cc g e1 in
        let '(m2, cc2, g2, cs2, l2) := bit_blast_bexp_ccache te m1 cc1 g1 e2 in
        match find_hbt e cc2 with
        | Some (csop, lop) => (m2, cc2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None => let '(gop, csop, lop) := bit_blast_disj g2 l1 l2 in
                  (m2, add_hbt e csop lop cc2, gop, 
                   catrev cs1 (catrev cs2 csop), lop, csop)
        end
      end
  (* = = *)
  in
  match CompCache.find_cbt e cc with
  | Some (cs, l) => (m, cc, g, [::], l)
  | None => let '(m', cc', g', cs, lr, csop) := bit_blast_bexp_nocbt te m cc g e in
            (m', CompCache.add_cbt e csop lr cc', g', cs, lr)
  end.
Proof. move=> te m cc g e. elim e; done. Qed.



(* === mk_env_exp_ccache and mk_env_bexp_ccache === *)

Definition mk_env_eunop (op : QFBV.eunop) :=
  match op with
  | QFBV.Unot => mk_env_not
  | QFBV.Uneg => mk_env_neg
  | QFBV.Uextr i j => (fun E g ls => mk_env_extract E g i j ls)
  | QFBV.Uhigh n => (fun E g ls => mk_env_high E g n ls)
  | QFBV.Ulow n => (fun E g ls => mk_env_low E g n ls)
  | QFBV.Uzext n => mk_env_zeroextend n
  | QFBV.Usext n => mk_env_signextend n
  | QFBV.Urepeat n => (fun E g ls => mk_env_repeat E g n ls)
  | QFBV.Urotl n => (fun E g ls => mk_env_rotateleft E g n ls)
  | QFBV.Urotr n => (fun E g ls => mk_env_rotateright E g n ls)
  end .

Definition mk_env_ebinop (op : QFBV.ebinop) :=
  match op with
  | QFBV.Band => mk_env_and
  | QFBV.Bor => mk_env_or 
  | QFBV.Bxor => mk_env_xor 
  | QFBV.Badd => mk_env_add 
  | QFBV.Bsub => mk_env_sub 
  | QFBV.Bmul => mk_env_mul 
  | QFBV.Bmod => mk_env_umod
  | QFBV.Bsrem => mk_env_srem
  | QFBV.Bsmod => mk_env_smod
  | QFBV.Bshl => mk_env_shl 
  | QFBV.Blshr => mk_env_lshr 
  | QFBV.Bashr => mk_env_ashr 
  | QFBV.Bconcat => mk_env_concat 
  | QFBV.Bcomp => mk_env_comp
  end .

Definition mk_env_bbinop (op : QFBV.bbinop) :=
  match op with
  | QFBV.Beq => mk_env_eq 
  | QFBV.Bult => mk_env_ult 
  | QFBV.Bule => mk_env_ule 
  | QFBV.Bugt => mk_env_ugt 
  | QFBV.Buge => mk_env_uge 
  | QFBV.Bslt => mk_env_slt 
  | QFBV.Bsle => mk_env_sle 
  | QFBV.Bsgt => mk_env_sgt 
  | QFBV.Bsge => mk_env_sge 
  | QFBV.Buaddo => mk_env_uaddo 
  | QFBV.Busubo => mk_env_usubo 
  | QFBV.Bumulo => mk_env_umulo 
  | QFBV.Bsaddo => mk_env_saddo 
  | QFBV.Bssubo => mk_env_ssubo 
  | QFBV.Bsmulo => mk_env_smulo 
  end .


Fixpoint mk_env_exp_ccache m cc s E g e :
  vm * compcache * env * generator * cnf * word :=
  (* = mk_env_exp_nocet = *)
  let mk_env_exp_nocet m cc s E g e : 
        vm * compcache * env * generator * cnf * word * cnf :=
      match e with
      | QFBV.Evar v =>
        match find_het e cc with
        | Some (cs, ls) => (m, cc, E, g, cs, ls, cs)
        | None => match SSAVM.find v m with
                  | None => 
                    let '(E', g', cs, rs) := mk_env_var E g (SSAStore.acc v s) v in
                    (SSAVM.add v rs m, add_het e cs rs cc, E', g', cs, rs, cs)
                  | Some rs => (m, add_het e [::] rs cc, E, g, [::], rs, [::])
                  end
        end
      | QFBV.Econst bs => 
        match find_het e cc with
        | Some (cs, ls) => (m, cc, E, g, cs, ls, cs)
        | None => let '(E', g', cs, rs) := mk_env_const E g bs in
                  (m, add_het e cs rs cc, E', g', cs, rs, cs)
        end
      | QFBV.Eunop op e1 =>
        let '(m1, cc1, E1, g1, cs1, ls1) := mk_env_exp_ccache m cc s E g e1 in
        match find_het e cc1 with
        | Some (csop, lsop) => (m1, cc1, E1, g1, catrev cs1 csop, lsop, csop)
        | None =>
          let '(Eop, gop, csop, lsop) := mk_env_eunop op E1 g1 ls1 in
          (m1, add_het e csop lsop cc1, Eop, gop, catrev cs1 csop, lsop, csop)
        end
      | QFBV.Ebinop op e1 e2 =>
        let '(m1, cc1, E1, g1, cs1, ls1) := mk_env_exp_ccache m cc s E g e1 in
        let '(m2, cc2, E2, g2, cs2, ls2) := mk_env_exp_ccache m1 cc1 s E1 g1 e2 in
        match find_het e cc2 with
        | Some (csop, lsop) => (m2, cc2, E2, g2, catrev cs1 (catrev cs2 csop), lsop, csop)
        | None => 
          let '(Eop, gop, csop, lsop) := mk_env_ebinop op E2 g2 ls1 ls2 in
          (m2, add_het e csop lsop cc2, Eop, gop, catrev cs1 (catrev cs2 csop), lsop, csop)
        end
      | QFBV.Eite c e1 e2 => 
        let '(mc, ccc, Ec, gc, csc, lc) := mk_env_bexp_ccache m cc s E g c in
        let '(m1, cc1, E1, g1, cs1, ls1) := mk_env_exp_ccache mc ccc s Ec gc e1 in
        let '(m2, cc2, E2, g2, cs2, ls2) := mk_env_exp_ccache m1 cc1 s E1 g1 e2 in
        match find_het e cc2 with
        | Some (csop, lsop) => 
          (m2, cc2, E2, g2, catrev csc (catrev cs1 (catrev cs2 csop)), lsop, csop)
        | None => 
          let '(Eop, gop, csop, lsop) := mk_env_ite E2 g2 lc ls1 ls2 in
          (m2, add_het e csop lsop cc2, Eop, gop, 
           catrev csc (catrev cs1 (catrev cs2 csop)), lsop, csop)
        end
      end
  (* = = *)
  in
  match CompCache.find_cet e cc with
  | Some (cs, ls) => (m, cc, E, g, [::], ls)
  | None => let '(m', cc', E', g', cs, lrs, csop) := mk_env_exp_nocet m cc s E g e in
            (m', CompCache.add_cet e csop lrs cc', E', g', cs, lrs)
  end
with
mk_env_bexp_ccache m cc s E g e : vm * compcache * env * generator * cnf * literal :=
  (* = mk_env_bexp_nocbt = *)
  let mk_env_bexp_nocbt m cc s E g e : 
        vm * compcache * env * generator * cnf * literal * cnf :=
      match e with
      | QFBV.Bfalse => 
        match find_hbt e cc with
        | Some (cs, l) => (m, cc, E, g, cs, l, cs)
        | None => (m, add_hbt e [::] lit_ff cc, E, g, [::], lit_ff, [::])
        end
      | QFBV.Btrue => 
        match find_hbt e cc with
        | Some (cs, l) => (m, cc, E, g, cs, l, cs)
        | None => (m, add_hbt e [::] lit_tt cc, E, g, [::], lit_tt, [::])
        end
      | QFBV.Bbinop op e1 e2 =>
        let '(m1, cc1, E1, g1, cs1, ls1) := mk_env_exp_ccache m cc s E g e1 in
        let '(m2, cc2, E2, g2, cs2, ls2) := mk_env_exp_ccache m1 cc1 s E1 g1 e2 in
        match find_hbt e cc2 with
        | Some (csop, lop) => (m2, cc2, E2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None => 
          let '(Eop, gop, csop, lop) := mk_env_bbinop op E2 g2 ls1 ls2 in
          (m2, add_hbt e csop lop cc2, Eop, gop, catrev cs1 (catrev cs2 csop), lop, csop)
        end
      | QFBV.Blneg e1 => 
        let '(m1, cc1, E1, g1, cs1, l1) := mk_env_bexp_ccache m cc s E g e1 in
        match find_hbt e cc1 with
        | Some (csop, lop) => (m1, cc1, E1, g1, catrev cs1 csop, lop, csop)
        | None => let '(Eop, gop, csop, lop) := mk_env_lneg E1 g1 l1 in
                  (m1, add_hbt e csop lop cc1, Eop, gop, catrev cs1 csop, lop, csop)
        end
      | QFBV.Bconj e1 e2 => 
        let '(m1, cc1, E1, g1, cs1, l1) := mk_env_bexp_ccache m cc s E g e1 in
        let '(m2, cc2, E2, g2, cs2, l2) := mk_env_bexp_ccache m1 cc1 s E1 g1 e2 in
        match find_hbt e cc2 with
        | Some (csop, lop) => (m2, cc2, E2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None => let '(Eop, gop, csop, lop) := mk_env_conj E2 g2 l1 l2 in
                  (m2, add_hbt e csop lop cc2, Eop, gop, 
                   catrev cs1 (catrev cs2 csop), lop, csop)
        end
      | QFBV.Bdisj e1 e2 => 
        let '(m1, cc1, E1, g1, cs1, l1) := mk_env_bexp_ccache m cc s E g e1 in
        let '(m2, cc2, E2, g2, cs2, l2) := mk_env_bexp_ccache m1 cc1 s E1 g1 e2 in
        match find_hbt e cc2 with
        | Some (csop, lop) => (m2, cc2, E2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None => let '(Eop, gop, csop, lop) := mk_env_disj E2 g2 l1 l2 in
                  (m2, add_hbt e csop lop cc2, Eop, gop, 
                   catrev cs1 (catrev cs2 csop), lop, csop)
        end
      end
  (* = = *)
  in
  match CompCache.find_cbt e cc with
  | Some (cs, l) => (m, cc, E, g, [::], l)
  | None => let '(m', cc', E', g', cs, lr, csop) := mk_env_bexp_nocbt m cc s E g e in
            (m', CompCache.add_cbt e csop lr cc', E', g', cs, lr)
  end.


Lemma mk_env_exp_ccache_equation :
  forall m cc s E g e,  mk_env_exp_ccache m cc s E g e =
  (* = mk_env_exp_nocet = *)
  let mk_env_exp_nocet m cc s E g e : 
        vm * compcache * env * generator * cnf * word * cnf :=
      match e with
      | QFBV.Evar v =>
        match find_het e cc with
        | Some (cs, ls) => (m, cc, E, g, cs, ls, cs)
        | None => match SSAVM.find v m with
                  | None => 
                    let '(E', g', cs, rs) := mk_env_var E g (SSAStore.acc v s) v in
                    (SSAVM.add v rs m, add_het e cs rs cc, E', g', cs, rs, cs)
                  | Some rs => (m, add_het e [::] rs cc, E, g, [::], rs, [::])
                  end
        end
      | QFBV.Econst bs => 
        match find_het e cc with
        | Some (cs, ls) => (m, cc, E, g, cs, ls, cs)
        | None => let '(E', g', cs, rs) := mk_env_const E g bs in
                  (m, add_het e cs rs cc, E', g', cs, rs, cs)
        end
      | QFBV.Eunop op e1 =>
        let '(m1, cc1, E1, g1, cs1, ls1) := mk_env_exp_ccache m cc s E g e1 in
        match find_het e cc1 with
        | Some (csop, lsop) => (m1, cc1, E1, g1, catrev cs1 csop, lsop, csop)
        | None =>
          let '(Eop, gop, csop, lsop) := mk_env_eunop op E1 g1 ls1 in
          (m1, add_het e csop lsop cc1, Eop, gop, catrev cs1 csop, lsop, csop)
        end
      | QFBV.Ebinop op e1 e2 =>
        let '(m1, cc1, E1, g1, cs1, ls1) := mk_env_exp_ccache m cc s E g e1 in
        let '(m2, cc2, E2, g2, cs2, ls2) := mk_env_exp_ccache m1 cc1 s E1 g1 e2 in
        match find_het e cc2 with
        | Some (csop, lsop) => (m2, cc2, E2, g2, catrev cs1 (catrev cs2 csop), lsop, csop)
        | None => 
          let '(Eop, gop, csop, lsop) := mk_env_ebinop op E2 g2 ls1 ls2 in
          (m2, add_het e csop lsop cc2, Eop, gop, catrev cs1 (catrev cs2 csop), lsop, csop)
        end
      | QFBV.Eite c e1 e2 => 
        let '(mc, ccc, Ec, gc, csc, lc) := mk_env_bexp_ccache m cc s E g c in
        let '(m1, cc1, E1, g1, cs1, ls1) := mk_env_exp_ccache mc ccc s Ec gc e1 in
        let '(m2, cc2, E2, g2, cs2, ls2) := mk_env_exp_ccache m1 cc1 s E1 g1 e2 in
        match find_het e cc2 with
        | Some (csop, lsop) => 
          (m2, cc2, E2, g2, catrev csc (catrev cs1 (catrev cs2 csop)), lsop, csop)
        | None => 
          let '(Eop, gop, csop, lsop) := mk_env_ite E2 g2 lc ls1 ls2 in
          (m2, add_het e csop lsop cc2, Eop, gop, 
           catrev csc (catrev cs1 (catrev cs2 csop)), lsop, csop)
        end
      end
  (* = = *)
  in
  match CompCache.find_cet e cc with
  | Some (cs, ls) => (m, cc, E, g, [::], ls)
  | None => let '(m', cc', E', g', cs, lrs, csop) := mk_env_exp_nocet m cc s E g e in
            (m', CompCache.add_cet e csop lrs cc', E', g', cs, lrs)
  end .
Proof. move=> m cc s E g e. elim e; done. Qed.

Lemma mk_env_bexp_ccache_equation :
  forall m cc s E g e, 
    mk_env_bexp_ccache m cc s E g e =
  (* = mk_env_bexp_nocbt = *)
  let mk_env_bexp_nocbt m cc s E g e : 
        vm * compcache * env * generator * cnf * literal * cnf :=
      match e with
      | QFBV.Bfalse => 
        match find_hbt e cc with
        | Some (cs, l) => (m, cc, E, g, cs, l, cs)
        | None => (m, add_hbt e [::] lit_ff cc, E, g, [::], lit_ff, [::])
        end
      | QFBV.Btrue => 
        match find_hbt e cc with
        | Some (cs, l) => (m, cc, E, g, cs, l, cs)
        | None => (m, add_hbt e [::] lit_tt cc, E, g, [::], lit_tt, [::])
        end
      | QFBV.Bbinop op e1 e2 =>
        let '(m1, cc1, E1, g1, cs1, ls1) := mk_env_exp_ccache m cc s E g e1 in
        let '(m2, cc2, E2, g2, cs2, ls2) := mk_env_exp_ccache m1 cc1 s E1 g1 e2 in
        match find_hbt e cc2 with
        | Some (csop, lop) => (m2, cc2, E2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None => 
          let '(Eop, gop, csop, lop) := mk_env_bbinop op E2 g2 ls1 ls2 in
          (m2, add_hbt e csop lop cc2, Eop, gop, catrev cs1 (catrev cs2 csop), lop, csop)
        end
      | QFBV.Blneg e1 => 
        let '(m1, cc1, E1, g1, cs1, l1) := mk_env_bexp_ccache m cc s E g e1 in
        match find_hbt e cc1 with
        | Some (csop, lop) => (m1, cc1, E1, g1, catrev cs1 csop, lop, csop)
        | None => let '(Eop, gop, csop, lop) := mk_env_lneg E1 g1 l1 in
                  (m1, add_hbt e csop lop cc1, Eop, gop, catrev cs1 csop, lop, csop)
        end
      | QFBV.Bconj e1 e2 => 
        let '(m1, cc1, E1, g1, cs1, l1) := mk_env_bexp_ccache m cc s E g e1 in
        let '(m2, cc2, E2, g2, cs2, l2) := mk_env_bexp_ccache m1 cc1 s E1 g1 e2 in
        match find_hbt e cc2 with
        | Some (csop, lop) => (m2, cc2, E2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None => let '(Eop, gop, csop, lop) := mk_env_conj E2 g2 l1 l2 in
                  (m2, add_hbt e csop lop cc2, Eop, gop, 
                   catrev cs1 (catrev cs2 csop), lop, csop)
        end
      | QFBV.Bdisj e1 e2 => 
        let '(m1, cc1, E1, g1, cs1, l1) := mk_env_bexp_ccache m cc s E g e1 in
        let '(m2, cc2, E2, g2, cs2, l2) := mk_env_bexp_ccache m1 cc1 s E1 g1 e2 in
        match find_hbt e cc2 with
        | Some (csop, lop) => (m2, cc2, E2, g2, catrev cs1 (catrev cs2 csop), lop, csop)
        | None => let '(Eop, gop, csop, lop) := mk_env_disj E2 g2 l1 l2 in
                  (m2, add_hbt e csop lop cc2, Eop, gop, 
                   catrev cs1 (catrev cs2 csop), lop, csop)
        end
      end
  (* = = *)
  in
  match CompCache.find_cbt e cc with
  | Some (cs, l) => (m, cc, E, g, [::], l)
  | None => let '(m', cc', E', g', cs, lr, csop) := mk_env_bexp_nocbt m cc s E g e in
            (m', CompCache.add_cbt e csop lr cc', E', g', cs, lr)
  end.
Proof. move=> m cc s E g e. elim e; done. Qed.

