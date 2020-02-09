From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
From BBCache Require Import Cache.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== bit_blast_exp_cache and bit_blast_bexp_cache ===== *)

Fixpoint bit_blast_exp_cache te m ca g e : vm * cache * generator * cnf * word :=
  (* = bit_blast_exp_nocache = *)
  let bit_blast_exp_nocache te m ca g e : vm * cache * generator * cnf * word :=
      match e with
      | QFBV.Evar v =>
        match SSAVM.find v m with
        | None => let '(g', cs, rs) := bit_blast_var te g v in
                  (SSAVM.add v rs m, ca, g', cs, rs)
        | Some rs => (m, ca, g, [::], rs)
        end
      | QFBV.Econst bs => let '(g', cs, rs) := bit_blast_const g bs in
                          (m, ca, g', cs, rs)
      | QFBV.Eunop op e1 =>
        (match op with
         | QFBV.Unot => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(gr, csr, lsr) := bit_blast_not g1 ls1 in
                        (m1, ca1, gr, catrev cs1 csr, lsr)
         | QFBV.Uneg => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(gr, csr, lsr) := bit_blast_neg g1 ls1 in
                        (m1, ca1, gr, catrev cs1 csr, lsr)
         | QFBV.Uextr i j => let: (m', ca', ge, cse, lse) := bit_blast_exp_cache te m ca g e1 in
                             let: (g', cs, ls') := bit_blast_extract ge i j lse in
                             (m', ca', g', catrev cse cs, ls')
         | QFBV.Uhigh n => let: (m', ca', ge, cse, lse) := bit_blast_exp_cache te m ca g e1 in
                           let: (g', cs, ls') := bit_blast_high ge n lse in
                           (m', ca', g', catrev cse cs, ls')
         | QFBV.Ulow n => let: (m', ca', ge, cse, lse) := bit_blast_exp_cache te m ca g e1 in
                          let: (g', cs, ls') := bit_blast_low ge n lse in
                          (m', ca', g', catrev cse cs, ls')
         | QFBV.Uzext n =>  let '(m', ca', ge, cse, lse) := bit_blast_exp_cache te m ca g e1 in
                            let '(g', cs, ls) := bit_blast_zeroextend n ge lse in
                            (m', ca', g', catrev cse cs, ls)
         | QFBV.Usext n =>  let: (m', ca', ge, cse, lse) := bit_blast_exp_cache te m ca g e1 in
                            let: (g', cs, ls) := bit_blast_signextend n ge lse in
                            (m', ca', g', catrev cse cs, ls)
         end)
      | QFBV.Ebinop op e1 e2 =>
        (match op with
         | QFBV.Band => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(gr, csr, lsr) := bit_blast_and g2 ls1 ls2 in
                        (m2, ca2, gr, catrev cs1 (catrev cs2 csr), lsr)
         | QFBV.Bor => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in
                       let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                       let '(g', cs, rs) := bit_blast_or g2 rs1 rs2 in
                       (m2, ca2, g', catrev cs1 (catrev cs2 cs), rs)
         | QFBV.Bxor => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(gr, csr, lsr) := bit_blast_xor g2 ls1 ls2 in
                        (m2, ca2, gr, catrev cs1 (catrev cs2 csr), lsr)
         | QFBV.Badd => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(g', cs, rs) := bit_blast_add g2 rs1 rs2 in
                        (m2, ca2, g', catrev cs1 (catrev cs2 cs), rs)
         | QFBV.Bsub => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(g', cs, rs) := bit_blast_sub g2 rs1 rs2 in
                        (m2, ca2, g', catrev cs1 (catrev cs2 cs), rs)
         | QFBV.Bmul => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(g', cs, rs) := bit_blast_mul g2 rs1 rs2 in
                        (m2, ca2, g', catrev cs1 (catrev cs2 cs), rs)
         | QFBV.Bmod => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in (* TODO *)
                        let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        (m2, ca2, g2, catrev cs1 cs2, rs1)
         | QFBV.Bsrem => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in (* TODO *)
                         let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                         (m2, ca2, g2, catrev cs1 cs2, rs1)
         | QFBV.Bsmod => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in (* TODO *)
                         let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                         (m2, ca2, g2, catrev cs1 cs2, rs1)
         | QFBV.Bshl => let: (m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let: (m', ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let: (g', cs, ls) := bit_blast_shl g2 ls1 ls2 in
                        (m', ca2, g', catrev cs1 (catrev cs2 cs), ls)
         | QFBV.Blshr => let: (m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                         let: (m', ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                         let: (g', cs, ls) := bit_blast_lshr g2 ls1 ls2 in
                         (m', ca2, g', catrev cs1 (catrev cs2 cs), ls)
         | QFBV.Bashr => let: (m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                         let: (m', ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                         let: (g', cs, ls) := bit_blast_ashr g2 ls1 ls2 in
                         (m', ca2, g', catrev cs1 (catrev cs2 cs), ls)
         | QFBV.Bconcat => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in
                           let '(m', ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                           let '(g', cs, rs) := bit_blast_concat g2 rs1 rs2 in
                           (m', ca2, g', catrev cs1 (catrev cs2 cs), rs)
     end)
      | QFBV.Eite c e1 e2 => let '(mc, cac, gc, csc, lc) := bit_blast_bexp_cache te m ca g c in
                             let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te mc cac gc e1 in
                             let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                             let '(gr, csr, lsr) := bit_blast_ite g2 lc ls1 ls2 in
                             (m2, ca2, gr, catrev csc (catrev cs1 (catrev cs2 csr)), lsr)
      end
  (* = = *)
  in
  match Cache.find_cet e ca with
  | Some ls => (m, ca, g, [::], ls)
  | None => 
    match Cache.find_het e ca with
    | Some (cs, ls) => (m, (Cache.add_cet e ls ca), g, cs, ls)
    | None => let '(m', ca', g', cs, rs) := bit_blast_exp_nocache te m ca g e in
              (m', Cache.add_het e cs rs (Cache.add_cet e rs ca'), g', cs, rs)
    end
  end
with
bit_blast_bexp_cache te m ca g e : vm * cache * generator * cnf * literal :=
  (* = bit_blast_bexp_nocache = *)
  let bit_blast_bexp_nocache te m ca g e : vm * cache * generator * cnf * literal :=
      match e with
      | QFBV.Bfalse => (m, ca, g, [::], lit_ff)
      | QFBV.Btrue => (m, ca, g, [::], lit_tt)
      | QFBV.Bbinop op e1 e2 =>
        (match op with
         | QFBV.Beq => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                       let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                       let '(g', cs, r) := bit_blast_eq g2 ls1 ls2 in
                       (m2, ca2, g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Bult => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(g', cs, r) := bit_blast_ult g2 ls1 ls2 in
                        (m2, ca2, g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Bule => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(g', cs, r) := bit_blast_ule g2 ls1 ls2 in
                        (m2, ca2, g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Bugt => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(g', cs, r) := bit_blast_ugt g2 ls1 ls2 in
                        (m2, ca2, g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Buge => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(g', cs, r) := bit_blast_uge g2 ls1 ls2 in
                        (m2, ca2, g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Bslt => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(gr, csr, lr) := bit_blast_slt g2 ls1 ls2 in
                        (m2, ca2, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bsle => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(gr, csr, lr) := bit_blast_sle g2 ls1 ls2 in
                        (m2, ca2, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bsgt => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(gr, csr, lr) := bit_blast_sgt g2 ls1 ls2 in
                        (m2, ca2, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bsge => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(gr, csr, lr) := bit_blast_sge g2 ls1 ls2 in
                        (m2, ca2, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Buaddo => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in
                          let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                          let '(g', cs, lr) := bit_blast_uaddo g2 rs1 rs2 in
                          (m2, ca2, g', catrev cs1 (catrev cs2 cs), lr)
         | QFBV.Busubo => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in
                          let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                          let '(g', cs, lr) := bit_blast_usubo g2 rs1 rs2 in
                          (m2, ca2, g', catrev cs1 (catrev cs2 cs), lr)
         | QFBV.Bumulo => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in
                          let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                          let '(g', cs, lr) := bit_blast_umulo g2 rs1 rs2 in
                          (m2, ca2, g', catrev cs1 (catrev cs2 cs), lr)
         | QFBV.Bsaddo => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                          let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                          let '(gr, csr, lr) := bit_blast_saddo g2 ls1 ls2 in
                          (m2, ca2, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bssubo => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                          let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                          let '(gr, csr, lr) := bit_blast_ssubo g2 ls1 ls2 in
                          (m2, ca2, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bsmulo => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                          let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                          let '(gr, csr, lr) := bit_blast_smulo g2 ls1 ls2 in
                          (m2, ca2, gr, catrev cs1 (catrev cs2 csr), lr)
         end)
      | QFBV.Blneg e => let '(m1, ca1, g1, cs1, l1) := bit_blast_bexp_cache te m ca g e in
                        let '(g', cs, r) := bit_blast_lneg g1 l1 in
                        (m1, ca1, g', catrev cs1 cs, r)
      | QFBV.Bconj e1 e2 => let '(m1, ca1, g1, cs1, l1) := bit_blast_bexp_cache te m ca g e1 in
                            let '(m2, ca2, g2, cs2, l2) := bit_blast_bexp_cache te m1 ca1 g1 e2 in
                            let '(g', cs, r) := bit_blast_conj g2 l1 l2 in
                            (m2, ca2, g', catrev cs1 (catrev cs2 cs), r)
      | QFBV.Bdisj e1 e2 => let '(m1, ca1, g1, cs1, l1) := bit_blast_bexp_cache te m ca g e1 in
                            let '(m2, ca2, g2, cs2, l2) := bit_blast_bexp_cache te m1 ca1 g1 e2 in
                            let '(g', cs, r) := bit_blast_disj g2 l1 l2 in
                            (m2, ca2, g', catrev cs1 (catrev cs2 cs), r)
      end
  (* = = *)
  in
  match Cache.find_cbt e ca with
  | Some l => (m, ca, g, [::], l)
  | None => 
    match Cache.find_hbt e ca with
    | Some (cs, l) => (m, (Cache.add_cbt e l ca), g, cs, l)
    | None => let '(m', ca', g', cs, r) := bit_blast_bexp_nocache te m ca g e in
              (m', Cache.add_hbt e cs r (Cache.add_cbt e r ca'), g', cs, r)
    end
  end.

Lemma bit_blast_exp_cache_equation : 
  forall te m ca g e,
    bit_blast_exp_cache te m ca g e =
  (* = bit_blast_exp_nocache = *)
  let bit_blast_exp_nocache te m ca g e : vm * cache * generator * cnf * word :=
      match e with
      | QFBV.Evar v =>
        match SSAVM.find v m with
        | None => let '(g', cs, rs) := bit_blast_var te g v in
                  (SSAVM.add v rs m, ca, g', cs, rs)
        | Some rs => (m, ca, g, [::], rs)
        end
      | QFBV.Econst bs => let '(g', cs, rs) := bit_blast_const g bs in
                          (m, ca, g', cs, rs)
      | QFBV.Eunop op e1 =>
        (match op with
         | QFBV.Unot => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(gr, csr, lsr) := bit_blast_not g1 ls1 in
                        (m1, ca1, gr, catrev cs1 csr, lsr)
         | QFBV.Uneg => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(gr, csr, lsr) := bit_blast_neg g1 ls1 in
                        (m1, ca1, gr, catrev cs1 csr, lsr)
         | QFBV.Uextr i j => let: (m', ca', ge, cse, lse) := bit_blast_exp_cache te m ca g e1 in
                             let: (g', cs, ls') := bit_blast_extract ge i j lse in
                             (m', ca', g', catrev cse cs, ls')
         | QFBV.Uhigh n => let: (m', ca', ge, cse, lse) := bit_blast_exp_cache te m ca g e1 in
                           let: (g', cs, ls') := bit_blast_high ge n lse in
                           (m', ca', g', catrev cse cs, ls')
         | QFBV.Ulow n => let: (m', ca', ge, cse, lse) := bit_blast_exp_cache te m ca g e1 in
                          let: (g', cs, ls') := bit_blast_low ge n lse in
                          (m', ca', g', catrev cse cs, ls')
         | QFBV.Uzext n =>  let '(m', ca', ge, cse, lse) := bit_blast_exp_cache te m ca g e1 in
                            let '(g', cs, ls) := bit_blast_zeroextend n ge lse in
                            (m', ca', g', catrev cse cs, ls)
         | QFBV.Usext n =>  let: (m', ca', ge, cse, lse) := bit_blast_exp_cache te m ca g e1 in
                            let: (g', cs, ls) := bit_blast_signextend n ge lse in
                            (m', ca', g', catrev cse cs, ls)
         end)
      | QFBV.Ebinop op e1 e2 =>
        (match op with
         | QFBV.Band => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(gr, csr, lsr) := bit_blast_and g2 ls1 ls2 in
                        (m2, ca2, gr, catrev cs1 (catrev cs2 csr), lsr)
         | QFBV.Bor => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in
                       let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                       let '(g', cs, rs) := bit_blast_or g2 rs1 rs2 in
                       (m2, ca2, g', catrev cs1 (catrev cs2 cs), rs)
         | QFBV.Bxor => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(gr, csr, lsr) := bit_blast_xor g2 ls1 ls2 in
                        (m2, ca2, gr, catrev cs1 (catrev cs2 csr), lsr)
         | QFBV.Badd => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(g', cs, rs) := bit_blast_add g2 rs1 rs2 in
                        (m2, ca2, g', catrev cs1 (catrev cs2 cs), rs)
         | QFBV.Bsub => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(g', cs, rs) := bit_blast_sub g2 rs1 rs2 in
                        (m2, ca2, g', catrev cs1 (catrev cs2 cs), rs)
         | QFBV.Bmul => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(g', cs, rs) := bit_blast_mul g2 rs1 rs2 in
                        (m2, ca2, g', catrev cs1 (catrev cs2 cs), rs)
         | QFBV.Bmod => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in (* TODO *)
                        let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        (m2, ca2, g2, catrev cs1 cs2, rs1)
         | QFBV.Bsrem => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in (* TODO *)
                         let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                         (m2, ca2, g2, catrev cs1 cs2, rs1)
         | QFBV.Bsmod => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in (* TODO *)
                         let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                         (m2, ca2, g2, catrev cs1 cs2, rs1)
         | QFBV.Bshl => let: (m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let: (m', ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let: (g', cs, ls) := bit_blast_shl g2 ls1 ls2 in
                        (m', ca2, g', catrev cs1 (catrev cs2 cs), ls)
         | QFBV.Blshr => let: (m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                         let: (m', ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                         let: (g', cs, ls) := bit_blast_lshr g2 ls1 ls2 in
                         (m', ca2, g', catrev cs1 (catrev cs2 cs), ls)
         | QFBV.Bashr => let: (m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                         let: (m', ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                         let: (g', cs, ls) := bit_blast_ashr g2 ls1 ls2 in
                         (m', ca2, g', catrev cs1 (catrev cs2 cs), ls)
         | QFBV.Bconcat => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in
                           let '(m', ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                           let '(g', cs, rs) := bit_blast_concat g2 rs1 rs2 in
                           (m', ca2, g', catrev cs1 (catrev cs2 cs), rs)
     end)
      | QFBV.Eite c e1 e2 => let '(mc, cac, gc, csc, lc) := bit_blast_bexp_cache te m ca g c in
                             let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te mc cac gc e1 in
                             let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                             let '(gr, csr, lsr) := bit_blast_ite g2 lc ls1 ls2 in
                             (m2, ca2, gr, catrev csc (catrev cs1 (catrev cs2 csr)), lsr)
      end
  (* = = *)
  in
  match Cache.find_cet e ca with
  | Some ls => (m, ca, g, [::], ls)
  | None => 
    match Cache.find_het e ca with
    | Some (cs, ls) => (m, (Cache.add_cet e ls ca), g, cs, ls)
    | None => let '(m', ca', g', cs, rs) := bit_blast_exp_nocache te m ca g e in
              (m', Cache.add_het e cs rs (Cache.add_cet e rs ca'), g', cs, rs)
    end
  end.
Proof. move=> te m ca g e. elim e; done. Qed.

Lemma bit_blast_bexp_cache_equation : 
  forall te m ca g e, 
    bit_blast_bexp_cache te m ca g e =
  (* = bit_blast_bexp_nocache = *)
  let bit_blast_bexp_nocache te m ca g e : vm * cache * generator * cnf * literal :=
      match e with
      | QFBV.Bfalse => (m, ca, g, [::], lit_ff)
      | QFBV.Btrue => (m, ca, g, [::], lit_tt)
      | QFBV.Bbinop op e1 e2 =>
        (match op with
         | QFBV.Beq => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                       let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                       let '(g', cs, r) := bit_blast_eq g2 ls1 ls2 in
                       (m2, ca2, g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Bult => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(g', cs, r) := bit_blast_ult g2 ls1 ls2 in
                        (m2, ca2, g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Bule => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(g', cs, r) := bit_blast_ule g2 ls1 ls2 in
                        (m2, ca2, g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Bugt => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(g', cs, r) := bit_blast_ugt g2 ls1 ls2 in
                        (m2, ca2, g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Buge => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(g', cs, r) := bit_blast_uge g2 ls1 ls2 in
                        (m2, ca2, g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Bslt => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(gr, csr, lr) := bit_blast_slt g2 ls1 ls2 in
                        (m2, ca2, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bsle => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(gr, csr, lr) := bit_blast_sle g2 ls1 ls2 in
                        (m2, ca2, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bsgt => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(gr, csr, lr) := bit_blast_sgt g2 ls1 ls2 in
                        (m2, ca2, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bsge => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                        let '(gr, csr, lr) := bit_blast_sge g2 ls1 ls2 in
                        (m2, ca2, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Buaddo => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in
                          let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                          let '(g', cs, lr) := bit_blast_uaddo g2 rs1 rs2 in
                          (m2, ca2, g', catrev cs1 (catrev cs2 cs), lr)
         | QFBV.Busubo => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in
                          let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                          let '(g', cs, lr) := bit_blast_usubo g2 rs1 rs2 in
                          (m2, ca2, g', catrev cs1 (catrev cs2 cs), lr)
         | QFBV.Bumulo => let '(m1, ca1, g1, cs1, rs1) := bit_blast_exp_cache te m ca g e1 in
                          let '(m2, ca2, g2, cs2, rs2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                          let '(g', cs, lr) := bit_blast_umulo g2 rs1 rs2 in
                          (m2, ca2, g', catrev cs1 (catrev cs2 cs), lr)
         | QFBV.Bsaddo => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                          let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                          let '(gr, csr, lr) := bit_blast_saddo g2 ls1 ls2 in
                          (m2, ca2, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bssubo => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                          let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                          let '(gr, csr, lr) := bit_blast_ssubo g2 ls1 ls2 in
                          (m2, ca2, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bsmulo => let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_cache te m ca g e1 in
                          let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_cache te m1 ca1 g1 e2 in
                          let '(gr, csr, lr) := bit_blast_smulo g2 ls1 ls2 in
                          (m2, ca2, gr, catrev cs1 (catrev cs2 csr), lr)
         end)
      | QFBV.Blneg e => let '(m1, ca1, g1, cs1, l1) := bit_blast_bexp_cache te m ca g e in
                        let '(g', cs, r) := bit_blast_lneg g1 l1 in
                        (m1, ca1, g', catrev cs1 cs, r)
      | QFBV.Bconj e1 e2 => let '(m1, ca1, g1, cs1, l1) := bit_blast_bexp_cache te m ca g e1 in
                            let '(m2, ca2, g2, cs2, l2) := bit_blast_bexp_cache te m1 ca1 g1 e2 in
                            let '(g', cs, r) := bit_blast_conj g2 l1 l2 in
                            (m2, ca2, g', catrev cs1 (catrev cs2 cs), r)
      | QFBV.Bdisj e1 e2 => let '(m1, ca1, g1, cs1, l1) := bit_blast_bexp_cache te m ca g e1 in
                            let '(m2, ca2, g2, cs2, l2) := bit_blast_bexp_cache te m1 ca1 g1 e2 in
                            let '(g', cs, r) := bit_blast_disj g2 l1 l2 in
                            (m2, ca2, g', catrev cs1 (catrev cs2 cs), r)
      end
  (* = = *)
  in
  match Cache.find_cbt e ca with
  | Some l => (m, ca, g, [::], l)
  | None => 
    match Cache.find_hbt e ca with
    | Some (cs, l) => (m, (Cache.add_cbt e l ca), g, cs, l)
    | None => let '(m', ca', g', cs, r) := bit_blast_bexp_nocache te m ca g e in
              (m', Cache.add_hbt e cs r (Cache.add_cbt e r ca'), g', cs, r)
    end
  end.
Proof. move=> te m ca g e; elim e; done. Qed.


Fixpoint mk_env_exp_cache m ca s E g e : vm * cache * env * generator * cnf * word :=
  (* = mk_env_exp_nocache = *)
  let mk_env_exp_nocache m ca s E g e : vm * cache * env * generator * cnf * word :=
      match e with
      | QFBV.Evar v =>
        match SSAVM.find v m with
        | None => let '(E', g', cs, rs) := mk_env_var E g (SSAStore.acc v s) v in
                  (SSAVM.add v rs m, ca, E', g', cs, rs)
        | Some rs => (m, ca, E, g, [::], rs)
        end
      | QFBV.Econst bs => let '(E', g', cs, rs) := mk_env_const E g bs in
                          (m, ca, E', g', cs, rs)
      | QFBV.Eunop op e1 =>
        (match op with
         | QFBV.Unot => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(Er, gr, csr, lsr) := mk_env_not E1 g1 ls1 in
                        (m1, ca1, Er, gr, catrev cs1 csr, lsr)
         | QFBV.Uneg => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(Er, gr, csr, lsr) := mk_env_neg E1 g1 ls1 in
                        (m1, ca1, Er, gr, catrev cs1 csr, lsr)
         | QFBV.Uextr i j => let: (m', ca', Ee, ge, cse, lse) := mk_env_exp_cache m ca s E g e1 in
                             let: (E', g', cs, ls') := mk_env_extract Ee ge i j lse in
                             (m', ca', E', g', catrev cse cs, ls')
         | QFBV.Uhigh n => let: (m', ca', Ee, ge, cse, lse) := mk_env_exp_cache m ca s E g e1 in
                           let: (E', g', cs, ls') := mk_env_high Ee ge n lse in
                           (m', ca', E', g', catrev cse cs, ls')
         | QFBV.Ulow n => let: (m', ca', Ee, ge, cse, lse) := mk_env_exp_cache m ca s E g e1 in
                          let: (E', g', cs, ls') := mk_env_low Ee ge n lse in
                          (m', ca', E', g', catrev cse cs, ls')
         | QFBV.Uzext n => let '(m', ca', Ee, ge, cse, lse) := mk_env_exp_cache m ca s E g e1 in
                           let '(E', g', cs, ls') := mk_env_zeroextend n Ee ge lse in
                           (m', ca', E', g', catrev cse cs, ls')
         | QFBV.Usext n => let: (m', ca', Ee, ge, cse, lse) := mk_env_exp_cache m ca s E g e1 in
                           let: (E', g', cs, ls') := mk_env_signextend n Ee ge lse in
                           (m', ca', E', g', catrev cse cs, ls')
         end)
      | QFBV.Ebinop op e1 e2 =>
        (match op with
         | QFBV.Band => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(Er, gr, csr, lsr) := mk_env_and E2 g2 ls1 ls2 in
                        (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lsr)
         | QFBV.Bor => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                       let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                       let '(E', g', cs, ls) := mk_env_or E2 g2 ls1 ls2 in
                       (m2, ca2, E', g', catrev cs1 (catrev cs2 cs), ls)
         | QFBV.Bxor => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(Er, gr, csr, lsr) := mk_env_xor E2 g2 ls1 ls2 in
                        (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lsr)
         | QFBV.Badd => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(Er, gr, csr, lsr) := mk_env_add E2 g2 ls1 ls2 in
                        (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lsr)
         | QFBV.Bsub => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(Er, gr, csr, lsr) := mk_env_sub E2 g2 ls1 ls2 in
                        (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lsr)
         | QFBV.Bmul => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(Er, gr, csr, lsr) := mk_env_mul E2 g2 ls1 ls2 in
                        (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lsr)
         | QFBV.Bmod => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        (m2, ca2, E2, g2, catrev cs1 cs2, ls1) (* TODO *)
         | QFBV.Bsrem => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                         let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                         (m2, ca2, E2, g2, catrev cs1 cs2, ls1) (* TODO *)
         | QFBV.Bsmod => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                         let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                         (m2, ca2, E2, g2, catrev cs1 cs2, ls1) (* TODO *)
         | QFBV.Bshl => let: (m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let: (m', ca', E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let: (E', g', cs, ls) := mk_env_shl E2 g2 ls1 ls2 in
                        (m', ca', E', g', catrev cs1 (catrev cs2 cs), ls)
         | QFBV.Blshr => let: (m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                         let: (m', ca', E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                         let: (E', g', cs, ls) := mk_env_lshr E2 g2 ls1 ls2 in
                         (m', ca', E', g', catrev cs1 (catrev cs2 cs), ls)
         | QFBV.Bashr => let: (m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                         let: (m', ca', E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                         let: (E', g', cs, ls) := mk_env_ashr E2 g2 ls1 ls2 in
                         (m', ca', E', g', catrev cs1 (catrev cs2 cs), ls)
         | QFBV.Bconcat => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                           let '(m', ca', E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                           let '(E', g', cs, ls) := mk_env_concat E2 g2 ls1 ls2 in
                           (m', ca', E', g', catrev cs1 (catrev cs2 cs), ls)
         end)
      | QFBV.Eite c e1 e2 => let '(mc, cac, Ec, gc, csc, lc) := mk_env_bexp_cache m ca s E g c in
                             let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache mc cac s Ec gc e1 in
                             let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                             let '(Er, gr, csr, lsr) := mk_env_ite E2 g2 lc ls1 ls2 in
                             (m2, ca2, Er, gr, catrev csc (catrev cs1 (catrev cs2 csr)), lsr)
      end
  (* = = *)
  in
  match Cache.find_cet e ca with
  | Some ls => (m, ca, E, g, [::], ls)
  | None => 
    match Cache.find_het e ca with
    | Some (cs, ls) => (m, (Cache.add_cet e ls ca), E, g, cs, ls)
    | None => let '(m', ca', E', g', cs, rs) := mk_env_exp_nocache m ca s E g e in
              (m', Cache.add_het e cs rs (Cache.add_cet e rs ca'), E', g', cs, rs)
    end
  end
with
mk_env_bexp_cache m ca s E g e : vm * cache * env * generator * cnf * literal :=
  (* = mk_env_bexp_nocache = *)
  let mk_env_bexp_nocache m ca s E g e : vm * cache * env * generator * cnf * literal := 
      match e with
      | QFBV.Bfalse => (m, ca, E, g, [::], lit_ff)
      | QFBV.Btrue => (m, ca, E, g, [::], lit_tt)
      | QFBV.Bbinop op e1 e2 =>
        (match op with
         | QFBV.Beq => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                       let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                       let '(E', g', cs, r) := mk_env_eq E2 g2 ls1 ls2 in
                       (m2, ca2, E', g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Bult => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(E', g', cs, r) := mk_env_ult E2 g2 ls1 ls2 in
                        (m2, ca2, E', g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Bule => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(E', g', cs, r) := mk_env_ule E2 g2 ls1 ls2 in
                        (m2, ca2, E', g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Bugt => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(E', g', cs, r) := mk_env_ugt E2 g2 ls1 ls2 in
                        (m2, ca2, E', g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Buge => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(E', g', cs, r) := mk_env_uge E2 g2 ls1 ls2 in
                        (m2, ca2, E', g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Bslt => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(Er, gr, csr, lr) := mk_env_slt E2 g2 ls1 ls2 in
                        (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bsle => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(Er, gr, csr, lr) := mk_env_sle E2 g2 ls1 ls2 in
                        (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bsgt => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(Er, gr, csr, lr) := mk_env_sgt E2 g2 ls1 ls2 in
                        (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bsge => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(Er, gr, csr, lr) := mk_env_sge E2 g2 ls1 ls2 in
                        (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Buaddo => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                          let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                          let '(Er, gr, csr, lr) := mk_env_uaddo E2 g2 ls1 ls2 in
                          (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Busubo => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                          let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                          let '(Er, gr, csr, lr) := mk_env_usubo E2 g2 ls1 ls2 in
                          (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bumulo => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                          let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                          let '(Er, gr, csr, lr) := mk_env_umulo E2 g2 ls1 ls2 in
                          (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bsaddo => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                          let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                          let '(Er, gr, csr, lr) := mk_env_saddo E2 g2 ls1 ls2 in
                          (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bssubo => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                          let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                          let '(Er, gr, csr, lr) := mk_env_ssubo E2 g2 ls1 ls2 in
                          (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bsmulo => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                          let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                          let '(Er, gr, csr, lr) := mk_env_smulo E2 g2 ls1 ls2 in
                          (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         end)
      | QFBV.Blneg e1 => let '(m1, ca1, E1, g1, cs1, l1) := mk_env_bexp_cache m ca s E g e1 in
                         let '(E', g', cs, r) := mk_env_lneg E1 g1 l1 in
                         (m1, ca1, E', g', catrev cs1 cs, r)
      | QFBV.Bconj e1 e2 => let '(m1, ca1, E1, g1, cs1, l1) := mk_env_bexp_cache m ca s E g e1 in
                            let '(m2, ca2, E2, g2, cs2, l2) := mk_env_bexp_cache m1 ca1 s E1 g1 e2 in
                            let '(E', g', cs, r) := mk_env_conj E2 g2 l1 l2 in
                            (m2, ca2, E', g', catrev cs1 (catrev cs2 cs), r)
      | QFBV.Bdisj e1 e2 => let '(m1, ca1, E1, g1, cs1, l1) := mk_env_bexp_cache m ca s E g e1 in
                            let '(m2, ca2, E2, g2, cs2, l2) := mk_env_bexp_cache m1 ca1 s E1 g1 e2 in
                            let '(E', g', cs, r) := mk_env_disj E2 g2 l1 l2 in
                            (m2, ca2, E', g', catrev cs1 (catrev cs2 cs), r)
      end 
  (* = = *)
  in
  match Cache.find_cbt e ca with
  | Some l => (m, ca, E, g, [::], l)
  | None => 
    match Cache.find_hbt e ca with
    | Some (cs, l) => (m, (Cache.add_cbt e l ca), E, g, cs, l)
    | None => let '(m', ca', E', g', cs, r) := mk_env_bexp_nocache m ca s E g e in
              (m', Cache.add_hbt e cs r (Cache.add_cbt e r ca'), E', g', cs, r)
    end
  end.
  
Lemma mk_env_exp_cache_equation : 
  forall m ca s E g e,
    mk_env_exp_cache m ca s E g e =
  (* = mk_env_exp_nocache = *)
  let mk_env_exp_nocache m ca s E g e : vm * cache * env * generator * cnf * word :=
      match e with
      | QFBV.Evar v =>
        match SSAVM.find v m with
        | None => let '(E', g', cs, rs) := mk_env_var E g (SSAStore.acc v s) v in
                  (SSAVM.add v rs m, ca, E', g', cs, rs)
        | Some rs => (m, ca, E, g, [::], rs)
        end
      | QFBV.Econst bs => let '(E', g', cs, rs) := mk_env_const E g bs in
                          (m, ca, E', g', cs, rs)
      | QFBV.Eunop op e1 =>
        (match op with
         | QFBV.Unot => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(Er, gr, csr, lsr) := mk_env_not E1 g1 ls1 in
                        (m1, ca1, Er, gr, catrev cs1 csr, lsr)
         | QFBV.Uneg => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(Er, gr, csr, lsr) := mk_env_neg E1 g1 ls1 in
                        (m1, ca1, Er, gr, catrev cs1 csr, lsr)
         | QFBV.Uextr i j => let: (m', ca', Ee, ge, cse, lse) := mk_env_exp_cache m ca s E g e1 in
                             let: (E', g', cs, ls') := mk_env_extract Ee ge i j lse in
                             (m', ca', E', g', catrev cse cs, ls')
         | QFBV.Uhigh n => let: (m', ca', Ee, ge, cse, lse) := mk_env_exp_cache m ca s E g e1 in
                           let: (E', g', cs, ls') := mk_env_high Ee ge n lse in
                           (m', ca', E', g', catrev cse cs, ls')
         | QFBV.Ulow n => let: (m', ca', Ee, ge, cse, lse) := mk_env_exp_cache m ca s E g e1 in
                          let: (E', g', cs, ls') := mk_env_low Ee ge n lse in
                          (m', ca', E', g', catrev cse cs, ls')
         | QFBV.Uzext n => let '(m', ca', Ee, ge, cse, lse) := mk_env_exp_cache m ca s E g e1 in
                           let '(E', g', cs, ls') := mk_env_zeroextend n Ee ge lse in
                           (m', ca', E', g', catrev cse cs, ls')
         | QFBV.Usext n => let: (m', ca', Ee, ge, cse, lse) := mk_env_exp_cache m ca s E g e1 in
                           let: (E', g', cs, ls') := mk_env_signextend n Ee ge lse in
                           (m', ca', E', g', catrev cse cs, ls')
         end)
      | QFBV.Ebinop op e1 e2 =>
        (match op with
         | QFBV.Band => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(Er, gr, csr, lsr) := mk_env_and E2 g2 ls1 ls2 in
                        (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lsr)
         | QFBV.Bor => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                       let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                       let '(E', g', cs, ls) := mk_env_or E2 g2 ls1 ls2 in
                       (m2, ca2, E', g', catrev cs1 (catrev cs2 cs), ls)
         | QFBV.Bxor => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(Er, gr, csr, lsr) := mk_env_xor E2 g2 ls1 ls2 in
                        (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lsr)
         | QFBV.Badd => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(Er, gr, csr, lsr) := mk_env_add E2 g2 ls1 ls2 in
                        (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lsr)
         | QFBV.Bsub => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(Er, gr, csr, lsr) := mk_env_sub E2 g2 ls1 ls2 in
                        (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lsr)
         | QFBV.Bmul => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(Er, gr, csr, lsr) := mk_env_mul E2 g2 ls1 ls2 in
                        (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lsr)
         | QFBV.Bmod => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        (m2, ca2, E2, g2, catrev cs1 cs2, ls1) (* TODO *)
         | QFBV.Bsrem => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                         let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                         (m2, ca2, E2, g2, catrev cs1 cs2, ls1) (* TODO *)
         | QFBV.Bsmod => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                         let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                         (m2, ca2, E2, g2, catrev cs1 cs2, ls1) (* TODO *)
         | QFBV.Bshl => let: (m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let: (m', ca', E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let: (E', g', cs, ls) := mk_env_shl E2 g2 ls1 ls2 in
                        (m', ca', E', g', catrev cs1 (catrev cs2 cs), ls)
         | QFBV.Blshr => let: (m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                         let: (m', ca', E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                         let: (E', g', cs, ls) := mk_env_lshr E2 g2 ls1 ls2 in
                         (m', ca', E', g', catrev cs1 (catrev cs2 cs), ls)
         | QFBV.Bashr => let: (m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                         let: (m', ca', E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                         let: (E', g', cs, ls) := mk_env_ashr E2 g2 ls1 ls2 in
                         (m', ca', E', g', catrev cs1 (catrev cs2 cs), ls)
         | QFBV.Bconcat => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                           let '(m', ca', E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                           let '(E', g', cs, ls) := mk_env_concat E2 g2 ls1 ls2 in
                           (m', ca', E', g', catrev cs1 (catrev cs2 cs), ls)
         end)
      | QFBV.Eite c e1 e2 => let '(mc, cac, Ec, gc, csc, lc) := mk_env_bexp_cache m ca s E g c in
                             let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache mc cac s Ec gc e1 in
                             let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                             let '(Er, gr, csr, lsr) := mk_env_ite E2 g2 lc ls1 ls2 in
                             (m2, ca2, Er, gr, catrev csc (catrev cs1 (catrev cs2 csr)), lsr)
      end
  (* = = *)
  in
  match Cache.find_cet e ca with
  | Some ls => (m, ca, E, g, [::], ls)
  | None => 
    match Cache.find_het e ca with
    | Some (cs, ls) => (m, (Cache.add_cet e ls ca), E, g, cs, ls)
    | None => let '(m', ca', E', g', cs, rs) := mk_env_exp_nocache m ca s E g e in
              (m', Cache.add_het e cs rs (Cache.add_cet e rs ca'), E', g', cs, rs)
    end
  end.
Proof. move=> m ca s E g e; elim e; done. Qed.

Lemma mk_env_bexp_cache_equation :
  forall m ca s E g e,
    mk_env_bexp_cache m ca s E g e =
  (* = mk_env_bexp_nocache = *)
  let mk_env_bexp_nocache m ca s E g e : vm * cache * env * generator * cnf * literal := 
      match e with
      | QFBV.Bfalse => (m, ca, E, g, [::], lit_ff)
      | QFBV.Btrue => (m, ca, E, g, [::], lit_tt)
      | QFBV.Bbinop op e1 e2 =>
        (match op with
         | QFBV.Beq => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                       let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                       let '(E', g', cs, r) := mk_env_eq E2 g2 ls1 ls2 in
                       (m2, ca2, E', g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Bult => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(E', g', cs, r) := mk_env_ult E2 g2 ls1 ls2 in
                        (m2, ca2, E', g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Bule => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(E', g', cs, r) := mk_env_ule E2 g2 ls1 ls2 in
                        (m2, ca2, E', g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Bugt => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(E', g', cs, r) := mk_env_ugt E2 g2 ls1 ls2 in
                        (m2, ca2, E', g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Buge => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(E', g', cs, r) := mk_env_uge E2 g2 ls1 ls2 in
                        (m2, ca2, E', g', catrev cs1 (catrev cs2 cs), r)
         | QFBV.Bslt => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(Er, gr, csr, lr) := mk_env_slt E2 g2 ls1 ls2 in
                        (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bsle => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(Er, gr, csr, lr) := mk_env_sle E2 g2 ls1 ls2 in
                        (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bsgt => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(Er, gr, csr, lr) := mk_env_sgt E2 g2 ls1 ls2 in
                        (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bsge => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                        let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                        let '(Er, gr, csr, lr) := mk_env_sge E2 g2 ls1 ls2 in
                        (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Buaddo => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                          let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                          let '(Er, gr, csr, lr) := mk_env_uaddo E2 g2 ls1 ls2 in
                          (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Busubo => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                          let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                          let '(Er, gr, csr, lr) := mk_env_usubo E2 g2 ls1 ls2 in
                          (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bumulo => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                          let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                          let '(Er, gr, csr, lr) := mk_env_umulo E2 g2 ls1 ls2 in
                          (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bsaddo => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                          let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                          let '(Er, gr, csr, lr) := mk_env_saddo E2 g2 ls1 ls2 in
                          (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bssubo => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                          let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                          let '(Er, gr, csr, lr) := mk_env_ssubo E2 g2 ls1 ls2 in
                          (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         | QFBV.Bsmulo => let '(m1, ca1, E1, g1, cs1, ls1) := mk_env_exp_cache m ca s E g e1 in
                          let '(m2, ca2, E2, g2, cs2, ls2) := mk_env_exp_cache m1 ca1 s E1 g1 e2 in
                          let '(Er, gr, csr, lr) := mk_env_smulo E2 g2 ls1 ls2 in
                          (m2, ca2, Er, gr, catrev cs1 (catrev cs2 csr), lr)
         end)
      | QFBV.Blneg e1 => let '(m1, ca1, E1, g1, cs1, l1) := mk_env_bexp_cache m ca s E g e1 in
                         let '(E', g', cs, r) := mk_env_lneg E1 g1 l1 in
                         (m1, ca1, E', g', catrev cs1 cs, r)
      | QFBV.Bconj e1 e2 => let '(m1, ca1, E1, g1, cs1, l1) := mk_env_bexp_cache m ca s E g e1 in
                            let '(m2, ca2, E2, g2, cs2, l2) := mk_env_bexp_cache m1 ca1 s E1 g1 e2 in
                            let '(E', g', cs, r) := mk_env_conj E2 g2 l1 l2 in
                            (m2, ca2, E', g', catrev cs1 (catrev cs2 cs), r)
      | QFBV.Bdisj e1 e2 => let '(m1, ca1, E1, g1, cs1, l1) := mk_env_bexp_cache m ca s E g e1 in
                            let '(m2, ca2, E2, g2, cs2, l2) := mk_env_bexp_cache m1 ca1 s E1 g1 e2 in
                            let '(E', g', cs, r) := mk_env_disj E2 g2 l1 l2 in
                            (m2, ca2, E', g', catrev cs1 (catrev cs2 cs), r)
      end 
  (* = = *)
  in
  match Cache.find_cbt e ca with
  | Some l => (m, ca, E, g, [::], l)
  | None => 
    match Cache.find_hbt e ca with
    | Some (cs, l) => (m, (Cache.add_cbt e l ca), E, g, cs, l)
    | None => let '(m', ca', E', g', cs, r) := mk_env_bexp_nocache m ca s E g e in
              (m', Cache.add_hbt e cs r (Cache.add_cbt e r ca'), E', g', cs, r)
    end
  end.
Proof. move=> m ca s E g e; elim e; done. Qed.
