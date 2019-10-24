
(*
 * Require the following libraries:
 * - coq-nbit from https://github.com/mht208/coq-nbits
 * - ssrlib from https://github.com/mht208/coq-ssrlib.git
 *)

From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport AdhereConform.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== bit_blast_exp and bit_blast_bexp ===== *)

Fixpoint bit_blast_exp te m g e { struct e } : vm * generator * cnf * word :=
  match e with
  | QFBV.Evar v =>
    match SSAVM.find v m with
    | None => let '(g', cs, rs) := bit_blast_var te g v in
              (SSAVM.add v rs m, g', cs, rs)
    | Some rs => (m, g, [::], rs)
    end
  | QFBV.Econst bs => let '(g', cs, rs) := bit_blast_const g bs in
                 (m, g', cs, rs)
  | QFBV.Eunop op e1 =>
    (match op with
     | QFBV.Unot => let '(m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                    let '(gr, csr, lsr) := bit_blast_not g1 ls1 in
                    (m1, gr, cs1++csr, lsr)
     | QFBV.Uneg => let '(m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                    let '(gr, csr, lsr) := bit_blast_neg g1 ls1 in
                    (m1, gr, cs1++csr, lsr)
     | QFBV.Uextr i j => let: (m', ge, cse, lse) := bit_blast_exp te m g e1 in
                         let: (g', cs, ls') := bit_blast_extract ge i j lse in
                         (m', g', cse ++ cs, ls')
     | QFBV.Uhigh n => let: (m', ge, cse, lse) := bit_blast_exp te m g e1 in
                       let: (g', cs, ls') := bit_blast_high ge n lse in
                       (m', g', cse ++ cs, ls')
     | QFBV.Ulow n => let: (m', ge, cse, lse) := bit_blast_exp te m g e1 in
                      let: (g', cs, ls') := bit_blast_low ge n lse in
                      (m', g', cse ++ cs, ls')
     | QFBV.Uzext n =>  let '(m', ge, cse, lse) := bit_blast_exp te m g e1 in
                        let '(g', cs, ls) := bit_blast_zeroextend n ge lse in
                        (m', g', cse ++ cs, ls)
     | QFBV.Usext n =>  let: (m', ge, cse, lse) := bit_blast_exp te m g e1 in
                        let: (g', cs, ls) := bit_blast_signextend n ge lse in
                        (m', g', cse ++ cs, ls)
     end)
  | QFBV.Ebinop op e1 e2 =>
    (match op with
     | QFBV.Band => let '(m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                    let '(m2, g2, cs2, ls2) := bit_blast_exp te m1 g1 e2 in
                    let '(gr, csr, lsr) := bit_blast_and g2 ls1 ls2 in
                    (m2, gr, cs1++cs2++csr, lsr)
     | QFBV.Bor => let '(m1, g1, cs1, rs1) := bit_blast_exp te m  g e1 in
                   let '(m2, g2, cs2, rs2) := bit_blast_exp te m1 g1 e2 in
                   let '(g', cs, rs) := bit_blast_or g2 rs1 rs2 in
                   (m2, g', cs1 ++ cs2 ++ cs, rs)
     | QFBV.Bxor => let '(m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                    let '(m2, g2, cs2, ls2) := bit_blast_exp te m1 g1 e2 in
                    let '(gr, csr, lsr) := bit_blast_xor g2 ls1 ls2 in
                    (m2, gr, cs1++cs2++csr, lsr)
     | QFBV.Badd => let '(m1, g1, cs1, rs1) := bit_blast_exp te m g e1 in
                    let '(m2, g2, cs2, rs2) := bit_blast_exp te m1 g1 e2 in
                    let '(g', cs, rs) := bit_blast_add g2 rs1 rs2 in
               (m2, g', cs1 ++ cs2 ++ cs, rs)
     | QFBV.Bsub => let '(m1, g1, cs1, rs1) := bit_blast_exp te m g e1 in
                    let '(m2, g2, cs2, rs2) := bit_blast_exp te m1 g1 e2 in
                    let '(g', cs, rs) := bit_blast_sub g2 rs1 rs2 in
                    (m2, g', cs1 ++ cs2 ++ cs, rs)
     | QFBV.Bmul => let '(m1, g1, cs1, rs1) := bit_blast_exp te m g e1 in
                    let '(m2, g2, cs2, rs2) := bit_blast_exp te m1 g1 e2 in
                    let '(g', cs, rs) := bit_blast_mul g2 rs1 rs2 in
                    (m2, g', cs1 ++ cs2 ++ cs, rs)
     | QFBV.Bmod => let '(m1, g1, cs1, rs1) := bit_blast_exp te m g e1 in (* TODO *)
                    let '(m2, g2, cs2, rs2) := bit_blast_exp te m1 g1 e2 in
                    (m2, g2, cs1 ++ cs2, rs1)
     | QFBV.Bsrem => let '(m1, g1, cs1, rs1) := bit_blast_exp te m g e1 in (* TODO *)
                     let '(m2, g2, cs2, rs2) := bit_blast_exp te m1 g1 e2 in
                     (m2, g2, cs1 ++ cs2, rs1)
     | QFBV.Bsmod => let '(m1, g1, cs1, rs1) := bit_blast_exp te m g e1 in (* TODO *)
                     let '(m2, g2, cs2, rs2) := bit_blast_exp te m1 g1 e2 in
                     (m2, g2, cs1 ++ cs2, rs1)
     | QFBV.Bshl => let: (m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                    let: (m', g2, cs2, ls2) := bit_blast_exp te m1 g1 e2 in
                    let: (g', cs, ls) := bit_blast_shl g2 ls1 ls2 in
                    (m', g', cs1 ++ cs2 ++ cs, ls)
     | QFBV.Blshr => let: (m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                     let: (m', g2, cs2, ls2) := bit_blast_exp te m1 g1 e2 in
                     let: (g', cs, ls) := bit_blast_lshr g2 ls1 ls2 in
                (m', g', cs1 ++ cs2 ++ cs, ls)
     | QFBV.Bashr => let: (m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                     let: (m', g2, cs2, ls2) := bit_blast_exp te m1 g1 e2 in
                     let: (g', cs, ls) := bit_blast_ashr g2 ls1 ls2 in
                (m', g', cs1 ++ cs2 ++ cs, ls)
     | QFBV.Bconcat => let '(m1, g1, cs1, rs1) := bit_blast_exp te m g e1 in
                       let '(m', g2, cs2, rs2) := bit_blast_exp te m1 g1 e2 in
                       let '(g', cs, rs) := bit_blast_concat g2 rs1 rs2 in
                       (m', g', cs1 ++ cs2 ++ cs, rs)
     end)
  | QFBV.Eite c e1 e2 => let '(mc, gc, csc, lc) := bit_blast_bexp te m g c in
                         let '(m1, g1, cs1, ls1) := bit_blast_exp te mc gc e1 in
                         let '(m2, g2, cs2, ls2) := bit_blast_exp te m1 g1 e2 in
                         let '(gr, csr, lsr) := bit_blast_ite g2 lc ls1 ls2 in
                         (m2, gr, csc++cs1++cs2++csr, lsr)
  end
with
bit_blast_bexp te m g e { struct e } : vm * generator * cnf * literal :=
  match e with
  | QFBV.Bfalse => (m, g, [::], lit_ff)
  | QFBV.Btrue => (m, g, [::], lit_tt)
  | QFBV.Bbinop op e1 e2 =>
    (match op with
     | QFBV.Beq => let '(m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                   let '(m2, g2, cs2, ls2) := bit_blast_exp te m1 g1 e2 in
                   let '(g', cs, r) := bit_blast_eq g2 ls1 ls2 in
                   (m2, g', cs1++cs2++cs, r)
     | QFBV.Bult => let '(m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                    let '(m2, g2, cs2, ls2) := bit_blast_exp te m1 g1 e2 in
                    let '(g', cs, r) := bit_blast_ult g2 ls1 ls2 in
                    (m2, g', cs1++cs2++cs, r)
     | QFBV.Bule => let '(m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                    let '(m2, g2, cs2, ls2) := bit_blast_exp te m1 g1 e2 in
                    let '(g', cs, r) := bit_blast_ule g2 ls1 ls2 in
                    (m2, g', cs1++cs2++cs, r)
     | QFBV.Bugt => let '(m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                    let '(m2, g2, cs2, ls2) := bit_blast_exp te m1 g1 e2 in
                    let '(g', cs, r) := bit_blast_ugt g2 ls1 ls2 in
                    (m2, g', cs1++cs2++cs, r)
     | QFBV.Buge => let '(m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                    let '(m2, g2, cs2, ls2) := bit_blast_exp te m1 g1 e2 in
                    let '(g', cs, r) := bit_blast_uge g2 ls1 ls2 in
                    (m2, g', cs1++cs2++cs, r)
     | QFBV.Bslt => let '(m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                    let '(m2, g2, cs2, ls2) := bit_blast_exp te m1 g1 e2 in
                    let '(gr, csr, lr) := bit_blast_slt g2 ls1 ls2 in
                    (m2, gr, cs1++cs2++csr, lr)
     | QFBV.Bsle => let '(m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                    let '(m2, g2, cs2, ls2) := bit_blast_exp te m1 g1 e2 in
                    let '(gr, csr, lr) := bit_blast_sle g2 ls1 ls2 in
                    (m2, gr, cs1++cs2++csr, lr)
     | QFBV.Bsgt => let '(m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                    let '(m2, g2, cs2, ls2) := bit_blast_exp te m1 g1 e2 in
                    let '(gr, csr, lr) := bit_blast_sgt g2 ls1 ls2 in
                    (m2, gr, cs1++cs2++csr, lr)
     | QFBV.Bsge => let '(m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                    let '(m2, g2, cs2, ls2) := bit_blast_exp te m1 g1 e2 in
                    let '(gr, csr, lr) := bit_blast_sge g2 ls1 ls2 in
                    (m2, gr, cs1++cs2++csr, lr)
     | QFBV.Buaddo => let '(m1, g1, cs1, rs1) := bit_blast_exp te m g e1 in
                      let '(m2, g2, cs2, rs2) := bit_blast_exp te m1 g1 e2 in
                      let '(g', cs, lr) := bit_blast_uaddo g2 rs1 rs2 in
                      (m2, g', cs1 ++ cs2 ++ cs, lr)
     | QFBV.Busubo => let '(m1, g1, cs1, rs1) := bit_blast_exp te m g e1 in
                      let '(m2, g2, cs2, rs2) := bit_blast_exp te m1 g1 e2 in
                      let '(g', cs, lr) := bit_blast_usubo g2 rs1 rs2 in
                      (m2, g', cs1 ++ cs2 ++ cs, lr)
     | QFBV.Bumulo => let '(m1, g1, cs1, rs1) := bit_blast_exp te m g e1 in
                      let '(m2, g2, cs2, rs2) := bit_blast_exp te m1 g1 e2 in
                      let '(g', cs, lr) := bit_blast_umulo g2 rs1 rs2 in
                      (m2, g', cs1 ++ cs2 ++ cs, lr)
     | QFBV.Bsaddo => let '(m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                      let '(m2, g2, cs2, ls2) := bit_blast_exp te m1 g1 e2 in
                      let '(gr, csr, lr) := bit_blast_saddo g2 ls1 ls2 in
                      (m2, gr, cs1++cs2++csr, lr)
     | QFBV.Bssubo => let '(m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                      let '(m2, g2, cs2, ls2) := bit_blast_exp te m1 g1 e2 in
                      let '(gr, csr, lr) := bit_blast_ssubo g2 ls1 ls2 in
                      (m2, gr, cs1++cs2++csr, lr)
     | QFBV.Bsmulo => let '(m1, g1, cs1, ls1) := bit_blast_exp te m g e1 in
                      let '(m2, g2, cs2, ls2) := bit_blast_exp te m1 g1 e2 in
                      let '(gr, csr, lr) := bit_blast_smulo g2 ls1 ls2 in
                      (m2, gr, cs1++cs2++csr, lr)
     end)
  | QFBV.Blneg e => let '(m1, g1, cs1, l1) := bit_blast_bexp te m g e in
                    let '(g', cs, r) := bit_blast_lneg g1 l1 in
                    (m1, g', cs1++cs, r)
  | QFBV.Bconj e1 e2 => let '(m1, g1, cs1, l1) := bit_blast_bexp te m g e1 in
                        let '(m2, g2, cs2, l2) := bit_blast_bexp te m1 g1 e2 in
                        let '(g', cs, r) := bit_blast_conj g2 l1 l2 in
                        (m2, g', cs1++cs2++cs, r)
  | QFBV.Bdisj e1 e2 => let '(m1, g1, cs1, l1) := bit_blast_bexp te m g e1 in
                        let '(m2, g2, cs2, l2) := bit_blast_bexp te m1 g1 e2 in
                        let '(g', cs, r) := bit_blast_disj g2 l1 l2 in
                        (m2, g', cs1++cs2++cs, r)
  end .

Fixpoint mk_env_exp m s E g e : vm * env * generator * cnf * word :=
  match e with
  | QFBV.Evar v =>
    match SSAVM.find v m with
    | None => let '(E', g', cs, rs) := mk_env_var E g (SSAStore.acc v s) v in
              (SSAVM.add v rs m, E', g', cs, rs)
    | Some rs => (m, E, g, [::], rs)
    end
  | QFBV.Econst bs => let '(E', g', cs, rs) := mk_env_const E g bs in
                      (m, E', g', cs, rs)
  | QFBV.Eunop op e1 =>
    (match op with
     | QFBV.Unot => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                    let '(Er, gr, csr, lsr) := mk_env_not E1 g1 ls1 in
                    (m1, Er, gr, cs1++csr, lsr)
     | QFBV.Uneg => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                    let '(Er, gr, csr, lsr) := mk_env_neg E1 g1 ls1 in
                    (m1, Er, gr, cs1++csr, lsr)
     | QFBV.Uextr i j => let: (m', Ee, ge, cse, lse) := mk_env_exp m s E g e1 in
                         let: (E', g', cs, ls') := mk_env_extract Ee ge i j lse in
                         (m', E', g', cse ++ cs, ls')
     | QFBV.Uhigh n => let: (m', Ee, ge, cse, lse) := mk_env_exp m s E g e1 in
                       let: (E', g', cs, ls') := mk_env_high Ee ge n lse in
                       (m', E', g', cse ++ cs, ls')
     | QFBV.Ulow n => let: (m', Ee, ge, cse, lse) := mk_env_exp m s E g e1 in
                      let: (E', g', cs, ls') := mk_env_low Ee ge n lse in
                      (m', E', g', cse ++ cs, ls')
     | QFBV.Uzext n => let '(m', Ee, ge, cse, lse) := mk_env_exp m s E g e1 in
                       let '(E', g', cs, ls') := mk_env_zeroextend n Ee ge lse in
                       (m', E', g', cse ++ cs, ls')
     | QFBV.Usext n => let: (m', Ee, ge, cse, lse) := mk_env_exp m s E g e1 in
                       let: (E', g', cs, ls') := mk_env_signextend n Ee ge lse in
                       (m', E', g', cse ++ cs, ls')
     end)
  | QFBV.Ebinop op e1 e2 =>
    (match op with
     | QFBV.Band => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                    let '(Er, gr, csr, lsr) := mk_env_and E2 g2 ls1 ls2 in
                    (m2, Er, gr, cs1++cs2++csr, lsr)
     | QFBV.Bor => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                   let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                   let '(E', g', cs, ls) := mk_env_or E2 g2 ls1 ls2 in
                   (m2, E', g', cs1 ++ cs2 ++ cs, ls)
     | QFBV.Bxor => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                    let '(Er, gr, csr, lsr) := mk_env_xor E2 g2 ls1 ls2 in
                    (m2, Er, gr, cs1++cs2++csr, lsr)
     | QFBV.Badd => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                    let '(Er, gr, csr, lsr) := mk_env_add E2 g2 ls1 ls2 in
                    (m2, Er, gr, cs1++cs2++csr, lsr)
     | QFBV.Bsub => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                    let '(Er, gr, csr, lsr) := mk_env_sub E2 g2 ls1 ls2 in
                    (m2, Er, gr, cs1++cs2++csr, lsr)
     | QFBV.Bmul => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                    let '(Er, gr, csr, lsr) := mk_env_mul E2 g2 ls1 ls2 in
                    (m2, Er, gr, cs1++cs2++csr, lsr)
     | QFBV.Bmod => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                    (m2, E2, g2, cs1++cs2, ls1) (* TODO *)
     | QFBV.Bsrem => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                     let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                     (m2, E2, g2, cs1++cs2, ls1) (* TODO *)
     | QFBV.Bsmod => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                     let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                     (m2, E2, g2, cs1++cs2, ls1) (* TODO *)
     | QFBV.Bshl => let: (m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                    let: (m', E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                    let: (E', g', cs, ls) := mk_env_shl E2 g2 ls1 ls2 in
                    (m', E', g', cs1 ++ cs2 ++ cs, ls)
     | QFBV.Blshr => let: (m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                     let: (m', E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                     let: (E', g', cs, ls) := mk_env_lshr E2 g2 ls1 ls2 in
                     (m', E', g', cs1 ++ cs2 ++ cs, ls)
     | QFBV.Bashr => let: (m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                     let: (m', E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                     let: (E', g', cs, ls) := mk_env_ashr E2 g2 ls1 ls2 in
                     (m', E', g', cs1 ++ cs2 ++ cs, ls)
     | QFBV.Bconcat => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                       let '(m', E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                       let '(E', g', cs, ls) := mk_env_concat E2 g2 ls1 ls2 in
                       (m', E', g', cs1 ++ cs2 ++ cs, ls)
     end)
  | QFBV.Eite c e1 e2 => let '(mc, Ec, gc, csc, lc) := mk_env_bexp m s E g c in
                         let '(m1, E1, g1, cs1, ls1) := mk_env_exp mc s Ec gc e1 in
                         let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                         let '(Er, gr, csr, lsr) := mk_env_ite E2 g2 lc ls1 ls2 in
                         (m2, Er, gr, csc++cs1++cs2++csr, lsr)
  end
with
mk_env_bexp m s E g e : vm * env * generator * cnf * literal :=
  match e with
  | QFBV.Bfalse => (m, E, g, [::], lit_ff)
  | QFBV.Btrue => (m, E, g, [::], lit_tt)
  | QFBV.Bbinop op e1 e2 =>
    (match op with
     | QFBV.Beq => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                   let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                   let '(E', g', cs, r) := mk_env_eq E2 g2 ls1 ls2 in
              (m2, E', g', cs1++cs2++cs, r)
     | QFBV.Bult => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                    let '(E', g', cs, r) := mk_env_ult E2 g2 ls1 ls2 in
                    (m2, E', g', cs1++cs2++cs, r)
     | QFBV.Bule => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                    let '(E', g', cs, r) := mk_env_ule E2 g2 ls1 ls2 in
                    (m2, E', g', cs1++cs2++cs, r)
     | QFBV.Bugt => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                    let '(E', g', cs, r) := mk_env_ugt E2 g2 ls1 ls2 in
                    (m2, E', g', cs1++cs2++cs, r)
     | QFBV.Buge => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                    let '(E', g', cs, r) := mk_env_uge E2 g2 ls1 ls2 in
                    (m2, E', g', cs1++cs2++cs, r)
     | QFBV.Bslt => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                    let '(Er, gr, csr, lr) := mk_env_slt E2 g2 ls1 ls2 in
                    (m2, Er, gr, cs1++cs2++csr, lr)
     | QFBV.Bsle => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                    let '(Er, gr, csr, lr) := mk_env_sle E2 g2 ls1 ls2 in
                    (m2, Er, gr, cs1++cs2++csr, lr)
     | QFBV.Bsgt => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                    let '(Er, gr, csr, lr) := mk_env_sgt E2 g2 ls1 ls2 in
                    (m2, Er, gr, cs1++cs2++csr, lr)
     | QFBV.Bsge => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                    let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                    let '(Er, gr, csr, lr) := mk_env_sge E2 g2 ls1 ls2 in
                    (m2, Er, gr, cs1++cs2++csr, lr)
     | QFBV.Buaddo => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                      let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                      let '(Er, gr, csr, lr) := mk_env_uaddo E2 g2 ls1 ls2 in
                      (m2, Er, gr, cs1++cs2++csr, lr)
     | QFBV.Busubo => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                      let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                      let '(Er, gr, csr, lr) := mk_env_usubo E2 g2 ls1 ls2 in
                      (m2, Er, gr, cs1++cs2++csr, lr)
     | QFBV.Bumulo => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                      let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                      let '(Er, gr, csr, lr) := mk_env_umulo E2 g2 ls1 ls2 in
                      (m2, Er, gr, cs1++cs2++csr, lr)
     | QFBV.Bsaddo => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                      let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                      let '(Er, gr, csr, lr) := mk_env_saddo E2 g2 ls1 ls2 in
                      (m2, Er, gr, cs1++cs2++csr, lr)
     | QFBV.Bssubo => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                      let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                      let '(Er, gr, csr, lr) := mk_env_ssubo E2 g2 ls1 ls2 in
                      (m2, Er, gr, cs1++cs2++csr, lr)
     | QFBV.Bsmulo => let '(m1, E1, g1, cs1, ls1) := mk_env_exp m s E g e1 in
                      let '(m2, E2, g2, cs2, ls2) := mk_env_exp m1 s E1 g1 e2 in
                      let '(Er, gr, csr, lr) := mk_env_smulo E2 g2 ls1 ls2 in
                      (m2, Er, gr, cs1++cs2++csr, lr)
     end)
  | QFBV.Blneg e1 => let '(m1, E1, g1, cs1, l1) := mk_env_bexp m s E g e1 in
                     let '(E', g', cs, r) := mk_env_lneg E1 g1 l1 in
                     (m1, E', g', cs1++cs, r)
  | QFBV.Bconj e1 e2 => let '(m1, E1, g1, cs1, l1) := mk_env_bexp m s E g e1 in
                        let '(m2, E2, g2, cs2, l2) := mk_env_bexp m1 s E1 g1 e2 in
                        let '(E', g', cs, r) := mk_env_conj E2 g2 l1 l2 in
                        (m2, E', g', cs1++cs2++cs, r)
  | QFBV.Bdisj e1 e2 => let '(m1, E1, g1, cs1, l1) := mk_env_bexp m s E g e1 in
                        let '(m2, E2, g2, cs2, l2) := mk_env_bexp m1 s E1 g1 e2 in
                        let '(E', g', cs, r) := mk_env_disj E2 g2 l1 l2 in
                        (m2, E', g', cs1++cs2++cs, r)

  end .

Ltac bb_exp_bexp_vm_preserve :=
  lazymatch goal with
  | |- vm_preserve ?m ?m => exact: vm_preserve_refl
  | H1 : context f [bit_blast_exp _ _ _ ?e = (_, _, _, _) -> vm_preserve _ _],
         H2 : bit_blast_exp _ ?m1 _ ?e = (?m2, _, _, _)
    |- vm_preserve ?m1 ?m2 =>
    eapply H1; exact: H2
  | H1 : context f [bit_blast_bexp _ _ _ ?e = (_, _, _, _) -> vm_preserve _ _],
         H2 : bit_blast_bexp _ ?m1 _ ?e = (?m2, _, _, _)
    |- vm_preserve ?m1 ?m2 =>
    eapply H1; exact: H2
  | H1 : context f [bit_blast_exp _ _ _ ?e = (_, _, _, _) -> vm_preserve _ _],
         H2 : bit_blast_exp _ ?m1 _ ?e = (?m2, _, _, _)
    |- vm_preserve _ ?m2 =>
    apply: (@vm_preserve_trans _ m1);
    [bb_exp_bexp_vm_preserve | bb_exp_bexp_vm_preserve]
  | H1 : context f [bit_blast_bexp _ _ _ ?e = (_, _, _, _) -> vm_preserve _ _],
         H2 : bit_blast_bexp _ ?m1 _ ?e = (?m2, _, _, _)
    |- vm_preserve _ ?m2 =>
    apply: (@vm_preserve_trans _ m1);
    [bb_exp_bexp_vm_preserve | bb_exp_bexp_vm_preserve]
  | |- _ => idtac
  end.

(* Solve vm_preserve for those cases in bit_blast_exp and bit_blast_bexp
   that does not update vm. *)
Ltac auto_bit_blast_vm_preserve :=
  simpl; intros; dcase_hyps; subst; bb_exp_bexp_vm_preserve.

Lemma bit_blast_exp_preserve_var :
  forall t (te : SSATE.env) (m : vm) (g : generator) (m' : vm)
         (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Evar t) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  move=> v te m g m' g' cs lrs /=. case Hfind: (SSAVM.find v m).
  - case=> <- _ _ _. exact: vm_preserve_refl.
  - case Hv: (bit_blast_var te g v)=> [[og ocs] olrs].
    case=> <- _ _ _. exact: vm_preserve_add_diag.
Qed.

Lemma bit_blast_exp_preserve_const :
  forall (b : bits) (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Econst b) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_not :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop QFBV.Unot e1) = (m', g', cs, lrs) ->
      vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H0 .
  dcase (bit_blast_exp te m g e1) => [[[[m1 g1] cs1] s1] Hexp] .
  dcase (bit_blast_not g1 s1) => [[[gr csr] lsr] Hnot] .
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_and :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g (QFBV.Ebinop QFBV.Band e1 e2) = (m', g', cs, lrs) ->
        vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e1) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_and g2 ls1 ls2) => [[[gr csr] lsr] Hand] .
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_or :
  forall (e0 : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (g  : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m  : vm) (g  : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] rs1] Hexp0] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] rs2] Hexp1] .
  dcase (bit_blast_or g2 rs1 rs2) => [[[g'0 cs0] rs] Hor] .
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_xor :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', g', cs, lrs) ->
        vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e1) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_xor g2 ls1 ls2) => [[[gr csr] lsr] Hxor] .
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_neg :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop QFBV.Uneg e1) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H0 .
  dcase (bit_blast_exp te m g e1) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_neg g1 ls1) => [[[gr csr] lsr] Hneg] .
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_add :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : word),
        bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
             (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Badd e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e0) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_add g2 ls1 ls2) => [[[g'0 cs0] rs] Hadd] .
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_sub :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : word),
        bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
             (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bsub e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  rewrite /=; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e0) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_sub g2 ls1 ls2) => [[[g'0 cs0] rs] Hsub] .
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_mul :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : word),
        bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
             (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bmul e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e0) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_mul g2 ls1 ls2) => [[[g'0 cs0] rs] Hmul] .
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_exp_preserve_mod :
  forall (e : QFBV.exp) (e0 : QFBV.exp) (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bmod e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_srem :
  forall (e : QFBV.exp) (e0 : QFBV.exp) (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_smod :
  forall (e : QFBV.exp) (e0 : QFBV.exp) (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
Admitted.

Lemma bit_blast_exp_preserve_shl :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_shl g2 ls1 ls2) => [[[g'0 cs0] ls] Hshl] .
  auto_bit_blast_vm_preserve.
Qed .

Lemma bit_blast_exp_preserve_lshr :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
           (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_lshr g2 ls1 ls2) => [[[g'0 cs0] ls] Hlshr] .
  auto_bit_blast_vm_preserve.
Qed .

Lemma bit_blast_exp_preserve_ashr :
  forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
  forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_ashr g2 ls1 ls2) => [[[g'0 cs0] ls] Hashr] .
  auto_bit_blast_vm_preserve .
Qed .

Lemma bit_blast_exp_preserve_concat :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
           (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', g', cs, lrs) ->
      vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hexp2] .
  auto_bit_blast_vm_preserve.
Qed .

Lemma bit_blast_exp_preserve_extract :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (i j :nat) (g' : generator) (cs : cnf)
           (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', g', cs, lrs) ->
      vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H0 .
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  auto_bit_blast_vm_preserve .
Qed .

(*
Lemma bit_blast_exp_preserve_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV64.exp (w3 + w2 + w1)),
      (forall (m  : vm) (g  : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : (w3+w2+w1).-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (m : vm) (g : generator) (m' : vm) (g' : generator)
           (cs : cnf) (lrs : w2.-tuple literal),
      bit_blast_exp m g (QFBV64.bvSlice w1 w2 w3 e) = (m', g', cs, lrs) ->
      vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve .
Qed .
*)

Lemma bit_blast_exp_preserve_high :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator) (n :nat)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H0 .
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  auto_bit_blast_vm_preserve .
Qed .

Lemma bit_blast_exp_preserve_low :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator) (n : nat)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop (QFBV.Ulow n) e) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H0 .
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  auto_bit_blast_vm_preserve .
Qed .

Lemma bit_blast_exp_preserve_zeroextend :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator) (n : nat)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Eunop (QFBV.Uzext n) e) = (m', g', cs, lrs) ->
    vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H0 .
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  auto_bit_blast_vm_preserve .
Qed .

Lemma bit_blast_exp_preserve_signextend :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (te : SSATE.env) (m : vm) (g : generator) (n : nat)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop (QFBV.Usext n) e) = (m', g', cs, lrs) ->
      vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H0 .
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  auto_bit_blast_vm_preserve .
Qed .

Lemma bit_blast_exp_preserve_ite :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp te m g b = (m', g', cs, lr) -> vm_preserve m m') ->
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (e0 : QFBV.exp),
        (forall (te : SSATE.env) (m : vm) (g : generator)
                (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
            bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
        forall (te : SSATE.env) (m : vm) (g : generator)
               (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g (QFBV.Eite b e e0) = (m', g', cs, lrs) ->
          vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  rewrite /=; intros .
  move : H2 .
  dcase (bit_blast_bexp te m g b) => [[[[mc gc] csc] lc] Hbexp] .
  dcase (bit_blast_exp te mc gc e) => [[[[m1 g1] cs1] ls1] Hexpe] .
  dcase (bit_blast_exp te m1 g1 e0)=> [[[[m2 g2] cs2] ls2] Hexpe0] .
  dcase (bit_blast_ite g2 lc ls1 ls2) => [[[gr csr] lsr] Hite] .
auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_false :
  forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
         (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g QFBV.Bfalse = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_true :
  forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
         (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g QFBV.Btrue = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_eq :
  forall (e1 : QFBV.exp)
         (IH1 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (e2 : QFBV.exp)
         (IH2 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Beq e1 e2) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_eq g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_ult :
  forall (e1 : QFBV.exp)
         (IH1 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (e2 : QFBV.exp)
         (IH2 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bult e1 e2) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_ult g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_ule :
  forall (e1 : QFBV.exp)
         (IH1 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (e2 : QFBV.exp)
         (IH2 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bule e1 e2) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_ule g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_ugt :
  forall (e1 : QFBV.exp)
         (IH1 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (e2 : QFBV.exp)
         (IH2 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bugt e1 e2) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_eq g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_uge :
  forall (e1 : QFBV.exp)
         (IH1 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (e2 : QFBV.exp)
         (IH2 : forall (te : SSATE.env) (m : vm) (g : generator)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
             vm_preserve m m')
         (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Buge e1 e2) = (m', g', cs, lrs) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_eq g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_slt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_slt g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_sle :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_sle g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_sgt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_sgt g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_sge :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_sge g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_uaddo :
  forall (e : QFBV.exp) ,
    (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : word),
        bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', g', cs, lr) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  dcase (bit_blast_exp te m'0 ge e0) => [[[[m2 g2] cs2] ls2] Hexp0] .
  dcase (bit_blast_uaddo g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_usubo :
  forall (e : QFBV.exp) ,
    (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : word),
        bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Busubo e e0) = (m', g', cs, lr) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  dcase (bit_blast_exp te m'0 ge e0) => [[[[m2 g2] cs2] ls2] Hexp0] .
  dcase (bit_blast_usubo g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_umulo :
  forall (e : QFBV.exp) ,
    (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
            (cs : cnf) (lrs : word),
        bit_blast_exp te m g e = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator) (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', g', cs, lr) -> vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  dcase (bit_blast_exp te m'0 ge e0) => [[[[m2 g2] cs2] ls2] Hexp0] .
  dcase (bit_blast_umulo g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_saddo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_saddo g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_ssubo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_ssubo g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_smulo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) -> vm_preserve m m') ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) -> vm_preserve m m') ->
      forall (te : SSATE.env) (m : vm) (g : generator)
             (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', g', cs, lr) ->
        vm_preserve m m'.
Proof.
  (* TODO: fix auto_bit_blast_vm_preserve *)
  simpl; intros .
  move : H1 .
  dcase (bit_blast_exp te m g e1) => [[[[m'0 ge] cse] lse] Hexp1] .
  dcase (bit_blast_exp te m'0 ge e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_smulo g2 lse ls2) => [[[g'0 cs0] r] Heq] .
  auto_bit_blast_vm_preserve .
Qed.

Lemma bit_blast_bexp_preserve_lneg :
  forall (b : QFBV.bexp)
         (IH :
            forall (te : SSATE.env) (m : vm) (g : generator)
                   (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
              bit_blast_bexp te m g b = (m', g', cs, lrs) ->
              vm_preserve m m')
         (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g (QFBV.Blneg b) = (m', g', cs, lrs) ->
    vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_conj :
  forall (b : QFBV.bexp)
         (IH :
            forall (te : SSATE.env) (m : vm) (g : generator)
                   (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
              bit_blast_bexp te m g b = (m', g', cs, lrs) ->
              vm_preserve m m')
         (b0 : QFBV.bexp)
         (IH0 :
            forall (te : SSATE.env) (m : vm) (g : generator)
                   (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
              bit_blast_bexp te m g b0 = (m', g', cs, lrs) ->
              vm_preserve m m')
         (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g (QFBV.Bconj b b0) = (m', g', cs, lrs) ->
    vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Lemma bit_blast_bexp_preserve_disj :
  forall (b : QFBV.bexp)
         (IH :
            forall (te : SSATE.env) (m : vm) (g : generator)
                   (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
              bit_blast_bexp te m g b = (m', g', cs, lrs) ->
              vm_preserve m m')
         (b0 : QFBV.bexp)
         (IH0 :
            forall (te : SSATE.env) (m : vm) (g : generator)
                   (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
              bit_blast_bexp te m g b0 = (m', g', cs, lrs) ->
              vm_preserve m m')
         (te : SSATE.env) (m : vm) (g : generator)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : literal),
    bit_blast_bexp te m g (QFBV.Bdisj b b0) = (m', g', cs, lrs) ->
    vm_preserve m m'.
Proof.
  auto_bit_blast_vm_preserve.
Qed.

Corollary bit_blast_exp_preserve :
  forall (e : QFBV.exp) te m g m' g' cs lrs,
    bit_blast_exp te m g e = (m', g', cs, lrs) ->
    vm_preserve m m'
  with
    bit_blast_bexp_preserve :
      forall (e : QFBV.bexp) te m g m' g' cs lrs,
        bit_blast_bexp te m g e = (m', g', cs, lrs) ->
        vm_preserve m m'.
Proof.
  (* bit_blast_exp_preserve *)
  move => e te m g m' g' cs lrs .
  case : e .
  - move => t; exact : bit_blast_exp_preserve_var.
  - move => b; exact : bit_blast_exp_preserve_const.
  - case .
    + move => e .
      apply : bit_blast_exp_preserve_not;
        exact : bit_blast_exp_preserve .
    + move => e .
      apply : bit_blast_exp_preserve_neg;
        exact : bit_blast_exp_preserve .
    + move => i j e .
      apply : bit_blast_exp_preserve_extract;
        exact : bit_blast_exp_preserve .
    + move => n e .
      apply : bit_blast_exp_preserve_high;
        exact : bit_blast_exp_preserve .
    + move => n e .
      apply : bit_blast_exp_preserve_low;
        exact : bit_blast_exp_preserve .
    + move => n e .
      apply : bit_blast_exp_preserve_zeroextend;
        exact : bit_blast_exp_preserve .
    + move => n e .
      apply : bit_blast_exp_preserve_signextend;
        exact : bit_blast_exp_preserve .
  - case; move => e0 e1.
    + apply : bit_blast_exp_preserve_and;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_or;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_xor;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_add;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_sub;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_mul;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_mod;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_srem;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_smod;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_shl;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_lshr;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_ashr;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_exp_preserve_concat;
        exact : bit_blast_exp_preserve .
  - move => b e0 e1 .
    apply : bit_blast_exp_preserve_ite;
      (exact : bit_blast_bexp_preserve ||
       exact : bit_blast_exp_preserve) .
(* bit_blast_bexp_preserve *)
  move => e te m g m' g' cs lrs .
  case : e .
  - apply : bit_blast_bexp_preserve_false .
  - apply : bit_blast_bexp_preserve_true .
  - case; move => e0 e1 .
    + apply : bit_blast_bexp_preserve_eq;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_ult;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_ule;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_ugt;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_uge;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_slt;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_sle;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_sgt;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_sge;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_uaddo;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_usubo;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_umulo;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_saddo;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_ssubo;
        exact : bit_blast_exp_preserve .
    + apply : bit_blast_bexp_preserve_smulo;
        exact : bit_blast_exp_preserve .
  - move => b .
    apply : bit_blast_bexp_preserve_lneg;
      exact : bit_blast_bexp_preserve .
  - move => b0 b1 .
    apply : bit_blast_bexp_preserve_conj;
      exact : bit_blast_bexp_preserve .
  - move => b0 b1 .
    apply : bit_blast_bexp_preserve_disj;
      exact : bit_blast_bexp_preserve .
Qed.

Corollary mk_env_exp_preserve_vm :
  forall (e : QFBV.exp) E m s g E' m' g' cs' lrs',
    mk_env_exp m s E g e = (m', E', g', cs', lrs') ->
    vm_preserve m m'
  with
    mk_env_bexp_preserve_vm :
      forall (e : QFBV.bexp) E m s g E' m' g' cs' lrs',
        mk_env_bexp m s E g e = (m', E', g', cs', lrs') ->
        vm_preserve m m'.
Proof .
  (* mk_env_exp_preserve_vm *)
  elim . (*  rewrite /= . *)
  - move => v E m s g E' m' g' cs' lrs' /= .
    case Hf : (SSAVM.find v m) .
    + case => <- _ _ _ _; apply : vm_preserve_refl .
    + dcase (mk_env_var E g (SSAStore.acc v s) v) => [[[[E'0 g'0] cs] rs] Hmke] .
      case => <- _ _ _ _ .
      exact : vm_preserve_add_diag .
  - rewrite /=; t_auto_preserve; exact : vm_preserve_refl .
  - elim => /= [e IHe E m s g E' m' g' cs' lrs' |
                e IHe E m s g E' m' g' cs' lrs' |
                i j e IHe E m s g E' m' g' cs' lrs' |
                n e IHe E m s g E' m' g' cs' lrs' |
                n e IHe E m s g E' m' g' cs' lrs' |
                n e IHe E m s g E' m' g' cs' lrs' |
                n e IHe E m s g E' m' g' cs' lrs'];
      dcase (mk_env_exp m s E g e) => [[[[[m1 E1] g1] cs1] ls1] Hmke] .
    + dcase (mk_env_not E1 g1 ls1) => [[[[Er gr] csr] lsr] Hmkr];
      case => <- _ _ _ _; exact : (IHe _ _ _ _ _ _ _ _ _ Hmke) .
    + dcase (mk_env_neg E1 g1 ls1) => [[[[Er gr] csr] lsr] Hmkr];
      case => <- _ _ _ _; exact : (IHe _ _ _ _ _ _ _ _ _ Hmke) .
    + case => <- _ _ _ _; exact : (IHe _ _ _ _ _ _ _ _ _ Hmke) .
    + case => <- _ _ _ _; exact : (IHe _ _ _ _ _ _ _ _ _ Hmke) .
    + case => <- _ _ _ _; exact : (IHe _ _ _ _ _ _ _ _ _ Hmke) .
    + case => <- _ _ _ _; exact : (IHe _ _ _ _ _ _ _ _ _ Hmke) .
    + case => <- _ _ _ _; exact : (IHe _ _ _ _ _ _ _ _ _ Hmke) .
  - elim => e0 IH0 e1 IH1 E m s g E' m' g' cs' lrs' /=;
      dcase (mk_env_exp m s E g e0) => [[[[[m1 E1] g1] cs1] ls1] Hmke0];
      dcase (mk_env_exp m1 s E1 g1 e1) => [[[[[m2 E2] g2] cs2] ls2] Hmke1] .
    + dcase (mk_env_and E2 g2 ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + dcase (mk_env_or E2 g2 ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + dcase (mk_env_xor E2 g2 ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + dcase (mk_env_add E2 g2 ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + dcase (mk_env_sub E2 g2 ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + dcase (mk_env_mul E2 g2 ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + dcase (mk_env_shl E2 g2 ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + dcase (mk_env_lshr E2 g2 ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + dcase (mk_env_ashr E2 g2 ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
    + case => <- _ _ _ _ .
      exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmke0) (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
  - move => c e0 IH0 e1 IH1 E m s g E' m' g' cs' lrs' /= .
    dcase (mk_env_bexp m s E g c) => [[[[[mc Ec] gc] csc] lc] Hmkc] .
    dcase (mk_env_exp mc s Ec gc e0) => [[[[[m1 E1] g1] cs1] ls1] Hmke0] .
    dcase (mk_env_exp m1 s E1 g1 e1) => [[[[[m2 E2] g2] cs2] ls2] Hmke1] .
    dcase (mk_env_ite E2 g2 lc ls1 ls2) => [[[[Er gr] csr] lsr] Hmkr] .
    case => <- _ _ _ _ .
    exact: (vm_preserve_trans
              (vm_preserve_trans
                 (mk_env_bexp_preserve_vm c _ _ _ _ _ _ _ _ _ Hmkc)
                 (IH0 _ _ _ _ _ _ _ _ _ Hmke0))
              (IH1 _ _ _ _ _ _ _ _ _ Hmke1)) .
  (* mk_env_bexp_preserve_vm *)
  elim .
  - move => E m s g E' m' g' cs' lrs' .
    case => <- _ _ _ _; exact : vm_preserve_refl .
  - move => E m s g E' m' g' cs' lrs' .
    case => <- _ _ _ _; exact : vm_preserve_refl .
  - elim => e0 e1 E m s g E' m' g' cs' lrs'; rewrite /=;
      dcase (mk_env_exp m s E g e0) => [[[[[m1 E1] g1] cs1] ls1] Hmke0];
      dcase (mk_env_exp m1 s E1 g1 e1) => [[[[[m2 E2] g2] cs2] ls2] Hmke1];
      move : (mk_env_exp_preserve_vm e0 _ _ _ _ _ _ _ _ _ Hmke0)
             (mk_env_exp_preserve_vm e1 _ _ _ _ _ _ _ _ _ Hmke1)
    => Hmm1 Hm1m2 .
    + dcase (mk_env_eq E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_ult E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_ule E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_ugt E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_uge E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_slt E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_sle E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_sgt E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_sge E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_uaddo E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_usubo E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_umulo E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_saddo E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_ssubo E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
    + dcase (mk_env_smulo E2 g2 ls1 ls2) => [[[[E'0 g'0] cs] r] Hmkr] .
      case => <- _ _ _ _ .
      exact : (vm_preserve_trans Hmm1 Hm1m2) .
  - move => b IHb E m s g E' m' g' cs' lrs' /= .
    dcase (mk_env_bexp m s E g b) => [[[[[m1 E1] g1] cs1] l1] Hmkb] .
    case => <- _ _ _ _ .
    exact : (IHb _ _ _ _ _ _ _ _ _ Hmkb) .
  - move => b0 IH0 b1 IH1 E m s g E' m' g' cs' lrs' /= .
    dcase (mk_env_bexp m s E g b0) => [[[[[m1 E1] g1] cs1] l1] Hmkb0 ] .
    dcase (mk_env_bexp m1 s E1 g1 b1) => [[[[[m2 E2] g2] cs2] l2] Hmkb1] .
    case => <- _ _ _ _ .
    exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmkb0)
                               (IH1 _ _ _ _ _ _ _ _ _ Hmkb1)) .
  - move => b0 IH0 b1 IH1 E m s g E' m' g' cs' lrs' /= .
    dcase (mk_env_bexp m s E g b0) => [[[[[m1 E1] g1] cs1] l1] Hmkb0 ] .
    dcase (mk_env_bexp m1 s E1 g1 b1) => [[[[[m2 E2] g2] cs2] l2] Hmkb1] .
    case => <- _ _ _ _ .
    exact : (vm_preserve_trans (IH0 _ _ _ _ _ _ _ _ _ Hmkb0)
                               (IH1 _ _ _ _ _ _ _ _ _ Hmkb1)) .
Qed .

(* = bit_blast_exp_correct and bit_blast_bexp_correct = *)

Lemma bit_blast_exp_var :
  forall v (te : SSATE.env) (m : vm) (g : generator)
         (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Evar v) = (m', g', cs, lrs) ->
    AdhereConform.conform_exp (QFBV.Evar v) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Evar v) te ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Evar v) s) .
Proof .
  move=> v te im ig s E om og ocs olrs. move=> Hblast _ Hcon _ Hcnf.
  move: (Hcon v) Hblast => {Hcon} Hcon. rewrite /=. case Hfind: (SSAVM.find v im).
  - case=> Hm Hg Hcs Hlrs. move: Hcon; rewrite /consistent1.
    rewrite -Hm Hfind Hlrs // .
  - case Hblast: (bit_blast_var te ig v) => [[vg vcs] vlrs].
    case=> [Hom Hog Hocs Holrs]. move: Hcon; rewrite /consistent1.
    rewrite -Hom. rewrite (SSAVM.Lemmas.find_add_eq (eq_refl v)).
    rewrite Holrs // .
Qed.

Lemma bit_blast_exp_const :
  forall (b : bits) (te : SSATE.env) (m : vm) (g : generator)
         (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Econst b) = (m', g', cs, lrs) ->
    AdhereConform.conform_exp (QFBV.Econst b) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Econst b) te ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Econst b) s).
Proof.
  move=> bv te im ig s E om og ocs olrs. case=> _ _ <- <- _ _ Hprelude _ .
  move: (add_prelude_enc_bit_tt Hprelude) => Htt {im ig om og ocs olrs Hprelude}.
  elim: bv; first by done. move=> a l IH. 
  rewrite enc_bits_cons; apply /andP; split .
  - rewrite enc_bit_lit_of_bool // .
  - exact : IH .
Qed.

Lemma bit_blast_exp_not :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp (QFBV.Eunop QFBV.Unot e1) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator)
           (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop QFBV.Unot e1) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Eunop QFBV.Unot e1) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.QFBV.well_formed_exp (QFBV.Eunop QFBV.Unot e1) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Eunop QFBV.Unot e1) s).
Proof.
  move=> e1 IH1 te m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case Hr : (bit_blast_not g1 ls1) => [[gr csr] lsr].
  case=> <- _ <- <-. move=> Hcf Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_cat. move/andP=> [Hic1 Hicr] Hwf .
  apply: (bit_blast_not_correct Hr _ Hicr).
  exact: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf Hcons1 Hic1 Hwf).
Qed.


Lemma bit_blast_exp_and :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e1 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e2 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e2 te ->
          enc_bits E lrs (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lrs : word),
        bit_blast_exp te m g (QFBV.Ebinop QFBV.Band e1 e2) = (m', g', cs, lrs) ->
        AdhereConform.conform_exp (QFBV.Ebinop QFBV.Band e1 e2) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Band e1 e2) te ->
        enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Band e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_and g2 ls1 ls2) => [[gr csr] lsr].
  case=> <- _ <- <-. move=> /andP [Hcf1 Hcf2] Hcons2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcons2) => Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_cat. move/andP=> [Hic1 /andP [Hic2 Hicr]] .
  move => /andP [/andP [Hwf1 Hwf2] _] .
  apply: (bit_blast_and_correct Hr _ _ Hicr).
  - exact: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcons1 Hic1 Hwf1).
  - exact: (IH2 _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcons2 Hic2 Hwf2).
Qed.


Lemma bit_blast_exp_or :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e0 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e0 te ->
          enc_bits E lrs (QFBV.eval_exp e0 s)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e1 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e1 te ->
          enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bor e0 e1) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bor e0 e1) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bor e0 e1) s).
Proof.
  move=> e0 IHe0 e1 IHe1 te m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] rs1] Hexp0] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] rs2] Hexp1] .
  dcase (bit_blast_or g2 rs1 rs2) => [[[g'0 cs0] rs] Hor] .
  case => <- _ <- <- .
  move => /andP [Hcf0 Hcf1] Hcon Hprelude /andP [/andP [Hwf0 Hwf1] _] .
  rewrite !add_prelude_cat in Hprelude.
  move: Hprelude => /andP [Hcs0 /andP [Hcs1 Hcs2]] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp1) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp0) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ _ Hexp0 Hcf0 Hcon1 Hcs0 Hwf0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ _ Hexp1 Hcf1 Hcon Hcs1 Hwf1) => Hencls1.
  apply: (bit_blast_or_correct Hor Hencls0 Hencls1 Hcs2).
Qed .

Lemma bit_blast_exp_xor :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e1 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e2 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e2 te ->
          enc_bits E lrs (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lrs : word),
        bit_blast_exp te m g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', g', cs, lrs) ->
        AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bxor e1 e2) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bxor e1 e2) te ->
        enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bxor e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_xor g2 ls1 ls2) => [[gr csr] lsr].
  case=> <- _ <- <-. move=> /andP [Hcf1 Hcf2] Hcons2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcons2) => Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_cat.
  move/andP=> [Hic1 /andP [Hic2 Hicr]] /andP [/andP [Hwf1 Hwf2] _].
  apply: (bit_blast_xor_correct Hr _ _ Hicr).
  - exact: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcons1 Hic1 Hwf1).
  - exact: (IH2 _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcons2 Hic2 Hwf2).
Qed.

Lemma bit_blast_exp_neg :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e te ->
        enc_bits E lrs (QFBV.eval_exp e s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator)
           (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Eunop QFBV.Uneg e) = (m', g', cs, lrs) ->
    AdhereConform.conform_exp (QFBV.Eunop QFBV.Uneg e)s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Eunop QFBV.Uneg e) te ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Eunop QFBV.Uneg e) s).
Proof.
  move=> e IH1 te m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e) => [[[m1 g1] cs1] ls1].
  case Hr : (bit_blast_neg g1 ls1) => [[gr csr] lsr].
  case=> <- _ <- <-. move=> Hcf Hcons1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcons1) => Hcons0.
  rewrite !add_prelude_cat.
  move/andP=> [Hic1 Hicr] Hwf .
  apply: (bit_blast_neg_correct Hr _ Hicr).
  exact : (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf Hcons1 Hic1 Hwf).
Qed.

Lemma bit_blast_exp_add :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e0 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e0 te ->
          enc_bits E lrs (QFBV.eval_exp e0 s)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e1 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e1 te ->
          enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Badd e0 e1) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Badd e0 e1) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Badd e0 e1) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Badd e0 e1) s).
Proof.
  move => e0 IHe0 e1 IHe1 te m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] rs1] Hexp0] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] rs2] Hexp1] .
  dcase (bit_blast_add g2 rs1 rs2) => [[[g'0 cs0] rs] Hadd] .
  case => <- _ <- <- .
  move => /andP [Hcf0 Hcf1] Hcon Hprelude /andP [/andP [Hwf0 Hwf1] Hsize] .
  rewrite !add_prelude_cat in Hprelude.
  move: Hprelude => /andP [Hcs0 /andP [Hcs1 Hcs2]] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp1) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp0) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ _ Hexp0 Hcf0 Hcon1 Hcs0 Hwf0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ _ Hexp1 Hcf1 Hcon Hcs1 Hwf1) => Hencls1.
  apply : (bit_blast_add_correct Hadd Hencls0 Hencls1); [done|done|idtac] .
  rewrite (enc_bits_size Hencls0) (enc_bits_size Hencls1)
          (AdhereConform.eval_conform_exp_size Hwf0 Hcf0) (AdhereConform.eval_conform_exp_size Hwf1 Hcf1)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_exp_sub :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e0 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e0 te ->
          enc_bits E lrs (QFBV.eval_exp e0 s)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e1 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e1 te ->
          enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bsub e0 e1) = (m', g', cs, lrs) ->
    AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bsub e0 e1) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsub e0 e1) te ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bsub e0 e1) s).
Proof.
  move => e0 IHe0 e1 IHe1 te m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] rs1] Hexp0] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] rs2] Hexp1] .
  dcase (bit_blast_sub g2 rs1 rs2) => [[[g'0 cs0] rs] Hsub] .
  case => <- _ <- <- /andP [Hcf0 Hcf1] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs0 /andP [Hcs1 Hcs2]] /andP [/andP [Hwf0 Hwf1] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp1) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp0) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ _ Hexp0 Hcf0 Hcon1 Hcs0 Hwf0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ _ Hexp1 Hcf1 Hcon Hcs1 Hwf1) => Hencls1.
  apply (bit_blast_sub_correct Hsub Hencls0 Hencls1); first done .
  rewrite (enc_bits_size Hencls0) (enc_bits_size Hencls1)
          (AdhereConform.eval_conform_exp_size Hwf0 Hcf0) (AdhereConform.eval_conform_exp_size Hwf1 Hcf1)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_exp_mul :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e te ->
          enc_bits E lrs (QFBV.eval_exp e s)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e0 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e0 te ->
          enc_bits E lrs (QFBV.eval_exp e0 s)) ->
    forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bmul e e0) = (m', g', cs, lrs) ->
    AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bmul e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bmul e e0) te ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bmul e e0) s).
Proof.
  move => e0 IHe0 e1 IHe1 te m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] rs1] Hexp0] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] rs2] Hexp1] .
  dcase (bit_blast_mul g2 rs1 rs2) => [[[g'0 cs0] rs] Hmul] .
  case => <- _ <- <- /andP [Hcf0 Hcf1] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs0 /andP [Hcs1 Hcs2]] /andP [/andP [Hwf0 Hwf1] Hsize] .
  move : (vm_preserve_consistent (bit_blast_exp_preserve Hexp1) Hcon) => Hconm0.
  move : (vm_preserve_consistent (bit_blast_exp_preserve Hexp0) Hconm0) => Hconm.
  move : (IHe0 _ _ _ _ _ _ _ _ _ Hexp0 Hcf0 Hconm0 Hcs0 Hwf0) => Hence0.
  move : (IHe1 _ _ _ _ _ _ _ _ _ Hexp1 Hcf1 Hcon Hcs1 Hwf1) => Hence1.
  apply : (bit_blast_mul_correct Hmul Hence0 Hence1); first done.
  rewrite (enc_bits_size Hence0) (enc_bits_size Hence1)
          (AdhereConform.eval_conform_exp_size Hwf0 Hcf0) (AdhereConform.eval_conform_exp_size Hwf1 Hcf1)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_exp_mod :
  forall (e e0 : QFBV.exp) (te : SSATE.env) (m : vm) (g : generator)
         (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bmod e e0) = (m', g', cs, lrs) ->
    AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bmod e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bmod e e0) te ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bmod e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_srem :
  forall (e e0 : QFBV.exp) (te : SSATE.env) (m : vm) (g : generator)
         (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', g', cs, lrs) ->
    AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bsrem e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsrem e e0) te ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bsrem e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_smod :
  forall (e e0 : QFBV.exp) (te : SSATE.env) (m : vm) (g : generator)
         (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', g', cs, lrs) ->
    AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bsmod e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsmod e e0) te ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bsmod e e0) s).
Proof.
Admitted.

Lemma bit_blast_exp_shl :
    forall (e0: QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e0 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e0 te ->
          enc_bits E lrs (QFBV.eval_exp e0 s)) ->
    forall (e1: QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e1 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e1 te ->
          enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bshl e0 e1) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bshl e0 e1) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bshl e0 e1) s).
Proof.
  move => e0 IHe0 e1 IHe1 te m g s E m' g' cs lrs .
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] rs1] Hexp0] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] rs2] Hexp1] .
  dcase (bit_blast_shl g2 rs1 rs2) => [[[g'0 cs0] rs] Hshl] .
  case => <- _ <- <- /andP [Hcf0 Hcf1] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs0 /andP [Hcs1 Hcs2]] /andP [/andP [Hwf0 Hwf1] _] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp1) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp0) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ _ Hexp0 Hcf0 Hcon1 Hcs0 Hwf0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ _ Hexp1 Hcf1 Hcon Hcs1 Hwf1) => Hencls1.
  apply : (bit_blast_shl_correct Hshl Hencls0 Hencls1 Hcs2) .
Qed .

Lemma bit_blast_exp_lshr :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e0 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e0 te ->
          enc_bits E lrs (QFBV.eval_exp e0 s)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e1 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e1 te ->
          enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Blshr e0 e1) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Blshr e0 e1) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Blshr e0 e1) s).
Proof.
  move => e0 IHe0 e1 IHe1 te m g s E m' g' cs lrs .
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] rs1] Hexp0] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] rs2] Hexp1] .
  dcase (bit_blast_lshr g2 rs1 rs2) => [[[g'0 cs0] rs] Hlshr] .
  case => <- _ <- <- /andP [Hcf0 Hcf1] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs0 /andP [Hcs1 Hcs2]] /andP [/andP [Hwf0 Hwf1] _] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp1) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp0) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ _ Hexp0 Hcf0 Hcon1 Hcs0 Hwf0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ _ Hexp1 Hcf1 Hcon Hcs1 Hwf1) => Hencls1.
  apply (bit_blast_lshr_correct Hlshr Hencls0 Hencls1 Hcs2) .
Qed .

Lemma bit_blast_exp_ashr :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e0 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e0 te ->
          enc_bits E lrs (QFBV.eval_exp e0 s)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator)
              (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e1 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e1 te ->
          enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator)
           (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bashr e0 e1) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bashr e0 e1) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bashr e0 e1) s).
Proof.
  move => e0 IHe0 e1 IHe1 te m g s E m' g' cs lrs .
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] rs1] Hexp0] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] rs2] Hexp1] .
  dcase (bit_blast_ashr g2 rs1 rs2) => [[[g'0 cs0] rs] Hashr] .
  case => <- _ <- <- /andP [Hcf0 Hcf1] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs0 /andP [Hcs1 Hcs2]] /andP [/andP [Hwf0 Hwf1] _].
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp1) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp0) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ _ Hexp0 Hcf0 Hcon1 Hcs0 Hwf0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ _ Hexp1 Hcf1 Hcon Hcs1 Hwf1) => Hencls1.
  apply (bit_blast_ashr_correct Hashr Hencls0 Hencls1 Hcs2) .
Qed .

Lemma bit_blast_exp_concat :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e0 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e0 te ->
          enc_bits E lrs (QFBV.eval_exp e0 s)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e1 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e1 te ->
          enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bconcat e0 e1) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bconcat e0 e1) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Ebinop QFBV.Bconcat e0 e1) s).
Proof.
  move => e0 IHe0 e1 IHe1 te m g s E m' g' cs lrs .
  rewrite (lock interp_cnf) /= -lock .
  dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] rs1] Hexp0] .
  dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] rs2] Hexp1] .
  case => <- _ <- <- /andP [Hcf0 Hcf1] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs0 /andP [Hcs1 _]] /andP [/andP [Hwf0 Hwf1] _].
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp1) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp0) Hcon1) => Hcon0.
  move: (IHe0 _ _ _ _ _ _ _ _ _ Hexp0 Hcf0 Hcon1 Hcs0 Hwf0) => Hencls0.
  move: (IHe1 _ _ _ _ _ _ _ _ _ Hexp1 Hcf1 Hcon Hcs1 Hwf1) => Hencls1.
  apply : (@bit_blast_concat_correct E g _ _ rs2 rs1 g _ _ _ Hencls1 Hencls0) .
  rewrite /bit_blast_concat // .
Qed .

Lemma bit_blast_exp_extract :
    forall (i j : nat) (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf)
              (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e te ->
          enc_bits E lrs (QFBV.eval_exp e s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Eunop (QFBV.Uextr i j) e) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uextr i j) e) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Eunop (QFBV.Uextr i j) e) s).
Proof.
  move=> i j e IH te m g s E m' g' cs lr .
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  case => <- _ <- <- Hcf Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcse Hcs0] Hwf .
  move: (IH _ _ _ _ _ _ _ _ _ Hexp Hcf Hcon Hcse Hwf) => Henc .
  apply : (@bit_blast_extract_correct E g _ _ _ _ _ _ _ _ Henc Hcs0) .
  rewrite /bit_blast_extract // .
Qed .

(*
Lemma bit_blast_exp_slice :
  forall (w1 w2 w3 : nat),
    forall (e : exp (w3 + w2 + w1)),
      (forall (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : (w3 + w2 +w1).-tuple literal),
          bit_blast_exp m g e = (m', g', cs, lrs) ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          enc_bits E lrs (QFBV.eval_exp e s)) ->
    forall (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf)
           (lrs : w2.-tuple literal),
      bit_blast_exp m g (QFBV64.bvSlice w1 w2 w3 e) = (m', g', cs, lrs) ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      enc_bits E lrs (QFBV.eval_exp (QFBV64.bvSlice w1 w2 w3 e) s).
Proof.
  move=> w1 w2 w3 e IH m g s E m' g' cs lr .
  rewrite (lock interp_cnf) /= -lock. dcase_goal. case; intros; subst.
  rewrite !add_prelude_append in H5.
  move: H5 => /andP [Hcs0 _] .
  move: (IH _ _ _ _ _ _ _ _ H H4 Hcs0) => Henc .
  apply: bit_blast_slice_correct Henc Hcs0 .
Qed .
*)

Lemma bit_blast_exp_high :
    forall (n : nat) (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e te ->
          enc_bits E lrs (QFBV.eval_exp e s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Eunop (QFBV.Uhigh n) e) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uhigh n) e) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Eunop (QFBV.Uhigh n) e) s).
Proof.
  move=> n e IH te m g s E m' g' cs lr .
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  case => <- _ <- <- Hcf Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcse Hcs0] Hwf .
  move: (IH _ _ _ _ _ _ _ _ _ Hexp Hcf Hcon Hcse Hwf) => Henc .
  apply: (@bit_blast_high_correct _ g _ _ _ g _ _ _ Henc Hcs0) .
  rewrite /bit_blast_high // .
Qed .

Lemma bit_blast_exp_low :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e te ->
          enc_bits E lrs (QFBV.eval_exp e s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop (QFBV.Ulow n) e) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Eunop (QFBV.Ulow n) e) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Ulow n) e) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Eunop (QFBV.Ulow n) e) s).
Proof.
  move=> n e IH te m g s E m' g' cs lr .
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  case => <- _ <- <- Hcf Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcse Hcs0] Hwf .
  move: (IH _ _ _ _ _ _ _ _ _ Hexp Hcf Hcon Hcse Hwf) => Henc .
  apply: (@bit_blast_low_correct _ g _ _ _ g _ _ _ Henc Hcs0) .
  rewrite /bit_blast_low // .
Qed .

Lemma bit_blast_exp_zeroextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e te ->
          enc_bits E lrs (QFBV.eval_exp e s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
           (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
      bit_blast_exp te m g (QFBV.Eunop (QFBV.Uzext n) e) = (m', g', cs, lrs) ->
      AdhereConform.conform_exp (QFBV.Eunop (QFBV.Uzext n) e) s te ->
      consistent m' E s ->
      interp_cnf E (add_prelude cs) ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uzext n) e) te ->
      enc_bits E lrs (QFBV.eval_exp (QFBV.Eunop (QFBV.Uzext n) e) s).
Proof.
  move=> n e IH te m g s E m' g' cs lr .
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  case => <- _ <- <- Hcf Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcse Hcs0] Hwf .
  move: (IH _ _ _ _ _ _ _ _ _ Hexp Hcf Hcon Hcse Hwf) => Henc .
  apply: (@bit_blast_zeroextend_correct _ g _ _ _ g _ _ _ Henc Hcs0) .
  rewrite /bit_blast_zeroextend // .
Qed .

Lemma bit_blast_exp_signextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (g  : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e te ->
          enc_bits E lrs (QFBV.eval_exp e s)) ->
    forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
    bit_blast_exp te m g (QFBV.Eunop (QFBV.Usext n) e) = (m', g', cs, lrs) ->
    AdhereConform.conform_exp (QFBV.Eunop (QFBV.Usext n) e) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp (QFBV.Eunop (QFBV.Usext n) e) te ->
    enc_bits E lrs (QFBV.eval_exp (QFBV.Eunop (QFBV.Usext n) e) s).
Proof.
  move => n e IH te m g s E m' g' cs lr .
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_exp te m g e) => [[[[m'0 ge] cse] lse] Hexp] .
  case => <- _ <- <- Hcf Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcse Hcs0] Hwf .
  move: (IH _ _ _ _ _ _ _ _ _ Hexp Hcf Hcon Hcse Hwf) => Henc .
  apply : (@bit_blast_signextend_correct _ g _ _ _ g _ _ _ Henc Hcs0) .
  rewrite /bit_blast_signextend // .
Qed .

Lemma bit_blast_exp_ite :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
        bit_blast_bexp te m g b = (m', g', cs, lr) ->
        AdhereConform.conform_bexp b s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp b te ->
        enc_bit E lr (QFBV.eval_bexp b s)) ->
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e te ->
          enc_bits E lrs (QFBV.eval_exp e s)) ->
      forall (e0 : QFBV.exp),
        (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
            bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
            AdhereConform.conform_exp e0 s te ->
            consistent m' E s ->
            interp_cnf E (add_prelude cs) ->
            QFBV.well_formed_exp e0 te ->
            enc_bits E lrs (QFBV.eval_exp e0 s)) ->
        forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
               (m' : vm) (g' : generator)
               (cs : cnf) (lrs : word),
          bit_blast_exp te m g (QFBV.Eite b e e0) = (m', g', cs, lrs) ->
          AdhereConform.conform_exp (QFBV.Eite b e e0) s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp (QFBV.Eite b e e0) te ->
          enc_bits E lrs (QFBV.eval_exp (QFBV.Eite b e e0) s) .
Proof.
  move=> c IHc e1 IH1 e2 IH2 te m g s E m' g' cs lrs.
  rewrite (lock interp_cnf) /= -lock.
  dcase (bit_blast_bexp te m g c) => [[[[mc gc] csc] lc] Hexpc] .
  dcase (bit_blast_exp te mc gc e1) => [[[[m1 g1] cs1] ls1] Hexp1] .
  dcase (bit_blast_exp te m1 g1 e2) => [[[[m2 g2] cs2] ls2] Hexp2] .
  dcase (bit_blast_ite g2 lc ls1 ls2) => [[[gr csr] lsr] Hite] .
  case => <- _ <- <- /andP [/andP [Hcfc Hcf1] Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs0 /andP [Hcs1 /andP [Hcs2 Hcs3]]]
          /andP [/andP [/andP [Hwfc Hwf1] Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp2) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hexp1) Hcon1) => Hcon0.
  move: (IHc _ _ _ _ _ _ _ _ _ Hexpc Hcfc Hcon0 Hcs0 Hwfc) => Hencl.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hexp1 Hcf1 Hcon1 Hcs1 Hwf1) => Hencls.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hexp2 Hcf2 Hcon Hcs2 Hwf2) => Hencls0.
  apply: (bit_blast_ite_correct _ Hite Hencl Hencls Hencls0 Hcs3).
  rewrite (enc_bits_size Hencls) (enc_bits_size Hencls0)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_false :
  forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g QFBV.Bfalse = (m', g', cs, lr) ->
    AdhereConform.conform_bexp QFBV.Bfalse s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp QFBV.Bfalse te ->
    enc_bit E lr (QFBV.eval_bexp QFBV.Bfalse s).
Proof.
  move=> te im ig s E om og ocs olr [] <- _ <- <- Hcf Hcon Hcs _ /=.
  exact: (add_prelude_enc_bit_ff Hcs).
Qed.

Lemma bit_blast_bexp_true :
  forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g QFBV.Btrue = (m', g', cs, lr) ->
    AdhereConform.conform_bexp QFBV.Btrue s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp QFBV.QFBV.Btrue te ->
    enc_bit E lr (QFBV.QFBV.eval_bexp QFBV.QFBV.Btrue s).
Proof.
  move=> te im ig s E om og ocs olr [] <- _ <- <- Hcf Hcon Hcs _ /=.
  exact: (add_prelude_enc_bit_tt Hcs).
Qed.

Lemma bit_blast_bexp_eq :
  forall (e : QFBV.exp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e te ->
             enc_bits E lrs (QFBV.eval_exp e s))
         (e0 : QFBV.exp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e0 te ->
             enc_bits E lrs (QFBV.eval_exp e0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Beq e e0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Beq e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Beq e e0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq e e0) s).
Proof.
  move=> e1 IH1 e2 IH2 te im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp te im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblasteq: (bit_blast_eq g2 rs1 rs2) => [[geq cseq] req].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcseq]] /andP [/andP [Hwf1 Hwf2] Hsize].
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast1) Hcon1) => Hcon2.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon1 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_eq_correct Hblasteq _ Henc1 Henc2 Hcseq) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_ult :
  forall (e : QFBV.exp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e te ->
             enc_bits E lrs (QFBV.eval_exp e s))
         (e0 : QFBV.exp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e0 te ->
             enc_bits E lrs (QFBV.eval_exp e0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bult e e0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bult e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bult e e0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bult e e0) s).
Proof.
  move=> e1 IH1 e2 IH2 te im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp te im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastult: (bit_blast_ult g2 rs1 rs2) => [[gult csult] rult].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsult]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon2 .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_ult_correct Hblastult Henc1 Henc2 Hcsult) .
Qed.

Lemma bit_blast_bexp_ule :
  forall (e : QFBV.exp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e te ->
             enc_bits E lrs (QFBV.eval_exp e s))
         (e0 : QFBV.exp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e0 te ->
             enc_bits E lrs (QFBV.eval_exp e0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bule e e0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bule e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bule e e0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bule e e0) s).
Proof.
  move=> e1 IH1 e2 IH2 te im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp te im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastule: (bit_blast_ule g2 rs1 rs2) => [[gule csule] rule].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsule]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_ule_correct Hblastule _ Henc1 Henc2 Hcsule) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_ugt :
  forall (e : QFBV.exp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e te ->
             enc_bits E lrs (QFBV.eval_exp e s))
         (e0 : QFBV.exp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e0 te ->
             enc_bits E lrs (QFBV.eval_exp e0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bugt e e0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bugt e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bugt e e0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bugt e e0) s).
Proof.
  move=> e1 IH1 e2 IH2 te im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp te im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastugt: (bit_blast_ugt g2 rs1 rs2) => [[gugt csugt] rugt].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsugt]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_ugt_correct Hblastugt Henc1 Henc2 Hcsugt) .
Qed.

Lemma bit_blast_bexp_uge :
  forall (e : QFBV.exp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e te ->
             enc_bits E lrs (QFBV.eval_exp e s))
         (e0 : QFBV.exp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e0 te ->
             enc_bits E lrs (QFBV.eval_exp e0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Buge e e0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Buge e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Buge e e0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Buge e e0) s).
Proof.
  move=> e1 IH1 e2 IH2 te im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp te im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastuge: (bit_blast_uge g2 rs1 rs2) => [[guge csuge] ruge].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsuge]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_uge_correct Hblastuge _ Henc1 Henc2 Hcsuge) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_slt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e1 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e2 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e2 te ->
          enc_bits E lrs (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', g', cs, lr) ->
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bslt e1 e2) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bslt e1 e2) te ->
        enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bslt e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_slt g2 ls1 ls2) => [[gr csr] r].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsslt]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_slt_correct Hr Henc1 Henc2 Hcsslt) .
Qed.

Lemma bit_blast_bexp_sle :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e1 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e2 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e2 te ->
          enc_bits E lrs (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', g', cs, lr) ->
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsle e1 e2) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsle e1 e2) te ->
        enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bsle e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_sle g2 ls1 ls2) => [[gr csr] r].
  case=> <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat.
  move => /andP [Hic1 /andP [Hic2 Hicr]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcon) => Hcon1.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcon1) => Hcon2.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcon1 Hic1 Hwf1) => Henc1 .
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcon Hic2 Hwf2) => Henc2 .
  apply: (bit_blast_sle_correct Hr _ Henc1 Henc2 Hicr).
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_sgt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e1 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e2 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e2 te ->
          enc_bits E lrs (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', g', cs, lr) ->
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsgt e1 e2) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsgt e1 e2) te ->
        enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bsgt e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_sgt g2 ls1 ls2) => [[gr csr] r].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsult]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_sgt_correct Hr Henc1 Henc2 Hcsult) .
Qed.

Lemma bit_blast_bexp_sge :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e1 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e2 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e2 te ->
          enc_bits E lrs (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', g', cs, lr) ->
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsge e1 e2) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsge e1 e2) te ->
        enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bsge e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_sge g2 ls1 ls2) => [[gr csr] r].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsult]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_sge_correct Hr _ Henc1 Henc2 Hcsult) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_uaddo :
  forall (e : QFBV.exp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e te ->
             enc_bits E lrs (QFBV.eval_exp e s))
         (e0 : QFBV.exp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e0 te ->
             enc_bits E lrs (QFBV.eval_exp e0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Buaddo e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Buaddo e e0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Buaddo e e0) s).
Proof.
  move=> e1 IH1 e2 IH2 te im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp te im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastuaddo: (bit_blast_uaddo g2 rs1 rs2) => [[guaddo csuaddo] ruaddo].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsult]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_uaddo_correct Hblastuaddo _ Henc1 Henc2 Hcsult) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_usubo :
  forall (e : QFBV.exp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e te ->
             enc_bits E lrs (QFBV.eval_exp e s))
         (e0 : QFBV.exp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e0 te ->
             enc_bits E lrs (QFBV.eval_exp e0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Busubo e e0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Busubo e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Busubo e e0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Busubo e e0) s).
Proof.
  move=> e1 IH1 e2 IH2 te im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp te im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastusubo: (bit_blast_usubo g2 rs1 rs2) => [[gusubo csusubo] rusubo].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsult]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_usubo_correct Hblastusubo Henc1 Henc2 Hcsult) .
Qed.

Lemma bit_blast_bexp_umulo :
  forall (e : QFBV.exp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e te ->
             enc_bits E lrs (QFBV.eval_exp e s))
         (e0 : QFBV.exp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                       (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
             bit_blast_exp te m g e0 = (m', g', cs, lrs) ->
             AdhereConform.conform_exp e0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_exp e0 te ->
             enc_bits E lrs (QFBV.eval_exp e0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bumulo e e0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bumulo e e0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bumulo e e0) s).
Proof.
  move=> e1 IH1 e2 IH2 te im ig s E om og ocs olrs.
  rewrite (lock interp_cnf) /= -lock.
  case Hblast1: (bit_blast_exp te im ig e1) => [[[m1 g1] cs1] rs1].
  case Hblast2: (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] rs2].
  case Hblastumulo: (bit_blast_umulo g2 rs1 rs2) => [[gumulo csumulo] rumulo].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsult]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve Hblast1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_umulo_correct Hblastumulo _ Henc1 Henc2 Hcsult) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_saddo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e1 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e2 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e2 te ->
          enc_bits E lrs (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', g', cs, lr) ->
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsaddo e1 e2) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsaddo e1 e2) te ->
        enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bsaddo e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_saddo g2 ls1 ls2) => [[gr csr] r].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsult]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_saddo_correct Hr _ Henc1 Henc2 Hcsult) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_ssubo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e1 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e2 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e2 te ->
          enc_bits E lrs (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', g', cs, lr) ->
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bssubo e1 e2) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bssubo e1 e2) te ->
        enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bssubo e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_ssubo g2 ls1 ls2) => [[gr csr] r].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsult]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_ssubo_correct Hr _ Henc1 Henc2 Hcsult) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_smulo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
            (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
        bit_blast_exp te m g e1 = (m', g', cs, lrs) ->
        AdhereConform.conform_exp e1 s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_exp e1 te ->
        enc_bits E lrs (QFBV.eval_exp e1 s)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
              (m' : vm) (g' : generator) (cs : cnf) (lrs : word),
          bit_blast_exp te m g e2 = (m', g', cs, lrs) ->
          AdhereConform.conform_exp e2 s te ->
          consistent m' E s ->
          interp_cnf E (add_prelude cs) ->
          QFBV.well_formed_exp e2 te ->
          enc_bits E lrs (QFBV.eval_exp e2 s)) ->
      forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
             (m' : vm) (g' : generator)
             (cs : cnf) (lr : literal),
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', g', cs, lr) ->
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsmulo e1 e2) s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsmulo e1 e2) te ->
        enc_bit E lr (QFBV.eval_bexp (QFBV.Bbinop QFBV.Bsmulo e1 e2) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lr.
  rewrite (lock interp_cnf) /= -lock.
  case He1 : (bit_blast_exp te m g e1) => [[[m1 g1] cs1] ls1].
  case He2 : (bit_blast_exp te m1 g1 e2) => [[[m2 g2] cs2] ls2].
  case Hr : (bit_blast_smulo g2 ls1 ls2) => [[gr csr] r].
  case => <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hcsult]]
          /andP [/andP [Hwf1 Hwf2] Hsize] .
  move: (vm_preserve_consistent (bit_blast_exp_preserve He2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_exp_preserve He1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ He1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ He2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (bit_blast_smulo_correct Hr _ Henc1 Henc2 Hcsult) .
  rewrite (enc_bits_size Henc1) (enc_bits_size Henc2)
          (AdhereConform.eval_conform_exp_size Hwf1 Hcf1) (AdhereConform.eval_conform_exp_size Hwf2 Hcf2)
          (eqP Hsize) // .
Qed.

Lemma bit_blast_bexp_lneg :
  forall (b : QFBV.bexp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
             bit_blast_bexp te m g b = (m', g', cs, lr) ->
             AdhereConform.conform_bexp b s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_bexp b te ->
             enc_bit E lr (QFBV.eval_bexp b s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Blneg b) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Blneg b) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Blneg b) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Blneg b) s).
Proof.
  move=> e1 IH te m g s E m' g' cs lr.
  rewrite /bit_blast_bexp /= -/bit_blast_bexp.
  case Hblast : (bit_blast_bexp te m g e1) => [[[m1 g1 ]cs1] r1].
  case => <- _ <- <- Hcf Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 Hocs] Hwf .
  move: (IH _ _ _ _ _ _ _ _ _ Hblast Hcf Hcon Hcs1 Hwf) => Henc.
  apply: (@bit_blast_lneg_correct g1 _ _ _ _ _ _ _ Henc Hocs).
  rewrite /bit_blast_lneg // .
Qed.

Lemma bit_blast_bexp_conj :
  forall (b : QFBV.bexp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
             bit_blast_bexp te m g b = (m', g', cs, lr) ->
             AdhereConform.conform_bexp b s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_bexp b te ->
             enc_bit E lr (QFBV.eval_bexp b s))
         (b0 : QFBV.bexp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
             bit_blast_bexp te m g b0 = (m', g', cs, lr) ->
             AdhereConform.conform_bexp b0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_bexp b0 te ->
             enc_bit E lr (QFBV.eval_bexp b0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bconj b b0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bconj b b0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bconj b b0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bconj b b0) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lr.
  rewrite /bit_blast_bexp /= -/bit_blast_bexp.
  case Hblast1: (bit_blast_bexp te m g e1) => [[[m1 g1] cs1] r1].
  case Hblast2: (bit_blast_bexp te m1 g1 e2) => [[[m2 g2] cs2] r2].
  case=> <- _ <- <- /andP [Hcf1 Hcf2] Hcon.
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hocs]] /andP [Hwf1 Hwf2] .
  move: (vm_preserve_consistent (bit_blast_bexp_preserve Hblast2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_bexp_preserve Hblast1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (@bit_blast_conj_correct g2 _ _ _ _ _ _ _ _ _ Henc1 Henc2 Hocs) .
  rewrite /bit_blast_conj // .
Qed.

Lemma bit_blast_bexp_disj :
  forall (b : QFBV.bexp)
         (IH : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
             bit_blast_bexp te m g b = (m', g', cs, lr) ->
             AdhereConform.conform_bexp b s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_bexp b te ->
             enc_bit E lr (QFBV.eval_bexp b s))
         (b0 : QFBV.bexp)
         (IH0 : forall (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
                      (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
             bit_blast_bexp te m g b0 = (m', g', cs, lr) ->
             AdhereConform.conform_bexp b0 s te ->
             consistent m' E s ->
             interp_cnf E (add_prelude cs) ->
             QFBV.well_formed_bexp b0 te ->
             enc_bit E lr (QFBV.eval_bexp b0 s))
         (te : SSATE.env) (m : vm) (g : generator) (s : SSAStore.t) (E : env)
         (m' : vm) (g' : generator) (cs : cnf) (lr : literal),
    bit_blast_bexp te m g (QFBV.Bdisj b b0) = (m', g', cs, lr) ->
    AdhereConform.conform_bexp (QFBV.Bdisj b b0) s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_bexp (QFBV.Bdisj b b0) te ->
    enc_bit E lr (QFBV.eval_bexp (QFBV.Bdisj b b0) s).
Proof.
  move=> e1 IH1 e2 IH2 te m g s E m' g' cs lr.
  rewrite /bit_blast_bexp /= -/bit_blast_bexp.
  case Hblast1: (bit_blast_bexp te m g e1) => [[[m1 g1] cs1] r1].
  case Hblast2: (bit_blast_bexp te m1 g1 e2) => [[[m2 g2] cs2] r2].
  case=> <- _ <- <- /andP [Hcf1 Hcf2] Hcon .
  rewrite !add_prelude_cat .
  move => /andP [Hcs1 /andP [Hcs2 Hocs]] /andP [Hwf1 Hwf2] .
  move: (vm_preserve_consistent (bit_blast_bexp_preserve Hblast2) Hcon) => Hcon2.
  move: (vm_preserve_consistent (bit_blast_bexp_preserve Hblast1) Hcon2) => Hcon1.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hblast1 Hcf1 Hcon2 Hcs1 Hwf1) => Henc1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hblast2 Hcf2 Hcon Hcs2 Hwf2) => Henc2.
  apply : (@bit_blast_disj_correct g2 _ _ _ _ _ _ _ _ _ Henc1 Henc2 Hocs) .
  rewrite /bit_blast_disj // .
Qed.

Corollary bit_blast_exp_correct :
  forall (e : QFBV.exp) te m g s E m' g' cs lrs,
    bit_blast_exp te m g e = (m', g', cs, lrs) ->
    AdhereConform.conform_exp e s te ->
    consistent m' E s ->
    interp_cnf E (add_prelude cs) ->
    QFBV.well_formed_exp e te ->
    enc_bits E lrs (QFBV.eval_exp e s)
  with
    bit_blast_bexp_correct :
      forall (e : QFBV.bexp) te m g s E m' g' cs lr,
        bit_blast_bexp te m g e = (m', g', cs, lr) ->
        AdhereConform.conform_bexp e s te ->
        consistent m' E s ->
        interp_cnf E (add_prelude cs) ->
        QFBV.well_formed_bexp e te ->
        enc_bit E lr (QFBV.eval_bexp e s) .
Proof .
  (* bit_blast_exp_correct *)
  move => e te m g s E m' g' cs lrs .
  case : e .
  - move => v; apply : bit_blast_exp_var .
  - move => bs; apply : bit_blast_exp_const .
  - elim .
    + move => e; apply : bit_blast_exp_not; apply : bit_blast_exp_correct .
    + move => e; apply : bit_blast_exp_neg; apply bit_blast_exp_correct .
    + move => i j e; apply : bit_blast_exp_extract; apply bit_blast_exp_correct .
    + move => n e; apply : bit_blast_exp_high; apply bit_blast_exp_correct .
    + move => n e; apply : bit_blast_exp_low; apply bit_blast_exp_correct .
    + move => n e; apply : bit_blast_exp_zeroextend; apply bit_blast_exp_correct .
    + move => n e; apply : bit_blast_exp_signextend; apply bit_blast_exp_correct .
  - elim; move => e0 e1 .
    + apply : bit_blast_exp_and; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_or; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_xor; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_add; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_sub; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_mul; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_mod; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_srem; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_smod; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_shl; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_lshr; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_ashr; apply bit_blast_exp_correct .
    + apply : bit_blast_exp_concat; apply bit_blast_exp_correct .
  - move => b e0 e1;
      apply bit_blast_exp_ite;
      first apply : bit_blast_bexp_correct;
      apply : bit_blast_exp_correct .
  (* bit_blast_bexp_correct *)
  elim .
  - exact : bit_blast_bexp_false .
  - exact : bit_blast_bexp_true .
  - elim => e0 e1 .
    + apply : bit_blast_bexp_eq; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_ult; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_ule; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_ugt; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_uge; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_slt; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_sle; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_sgt; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_sge; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_uaddo; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_usubo; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_umulo; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_saddo; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_ssubo; apply : bit_blast_exp_correct .
    + apply : bit_blast_bexp_smulo; apply : bit_blast_exp_correct .
  - apply : bit_blast_bexp_lneg .
  - apply : bit_blast_bexp_conj .
  - apply : bit_blast_bexp_disj .
Qed.

(* = mk_env_exp_is_bit_blast_exp and mk_env_bexp_is_bit_blast_bexp = *)

Lemma mk_env_exp_is_bit_blast_exp_var :
  forall t (te : SSATE.env) (m : vm) (E : env) (g : generator)
         (s : SSAStore.t) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    AdhereConform.conform_exp (QFBV.Evar t) s te ->
    QFBV.well_formed_exp (QFBV.Evar t) te ->
    mk_env_exp m s E g (QFBV.Evar t) = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g (QFBV.Evar t) = (m', g', cs, lrs).
Proof.
  rewrite /= .
  move => t te m E g s m' E' g' cs lrs Hsize _ .
  case : (SSAVM.find t m) .
  - move => a; case => <- _ <- <- <- // .
  - dcase (mk_env_var E g (SSAStore.acc t s) t) => [[[[E'0 g'0] cs0] rs] Hmkr] .
    dcase (bit_blast_var te g t) => [[[g'1 cs1] rs0] Hbst] .
    case => <- _ <- <- <- .
    rewrite (mk_env_var_is_bit_blast_var (Logic.eq_sym (eqP Hsize)) Hmkr) in Hbst .
    move : Hbst; case => <- <- <- // .
Qed.

Lemma mk_env_exp_is_bit_blast_exp_const :
  forall (b : bits) (te : SSATE.env) (m : vm) (E : env) (g : generator)
         (s : SSAStore.t) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    AdhereConform.conform_exp (QFBV.Econst b) s te ->
    QFBV.well_formed_exp (QFBV.Econst b) te ->
    mk_env_exp m s E g (QFBV.Econst b) = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g (QFBV.Econst b) = (m', g', cs, lrs).
Proof.
  rewrite /=; move => b te m E g s m' E' g' cs lrs Hcf _ .
  case => <- _ <- <- <- // .
Qed.

Lemma mk_env_exp_is_bit_blast_exp_not :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      AdhereConform.conform_exp (QFBV.Eunop QFBV.Unot e1) s te ->
      QFBV.well_formed_exp (QFBV.Eunop QFBV.Unot e1) te ->
      mk_env_exp m s E g (QFBV.Eunop QFBV.Unot e1) = (m', E', g', cs, lrs) ->
      bit_blast_exp te m g (QFBV.Eunop QFBV.Unot e1) = (m', g', cs, lrs).
Proof.
  move=> e1 IH1 te m E g s m' E' g' cs lrs /= Hcf Hwf .
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case => <- _ <- <- <- .
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf Hwf Hmke1).
  by rewrite (mk_env_not_is_bit_blast_not Hmkr).
Qed.

Lemma mk_env_exp_is_bit_blast_exp_and :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e2 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        AdhereConform.conform_exp (QFBV.Ebinop QFBV.Band e1 e2) s te ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Band e1 e2) te ->
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Band e1 e2) = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g (QFBV.Ebinop QFBV.Band e1 e2) = (m', g', cs, lrs).
Proof.
  move=> e1 IH1 e2 IH2 te m E g s m' E' g' cs lrs /andP [Hcf1 Hcf2] /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1)
          (IH2 _ _ _ _ _ _ _ _ _ _ Hcf2 Hwf2 Hmke2) .
  by rewrite (mk_env_and_is_bit_blast_and Hmkr).
Qed.

Lemma mk_env_exp_is_bit_blast_exp_or :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e1 s te ->
          QFBV.well_formed_exp e1 te ->
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bor e0 e1) s te ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bor e0 e1) te ->
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', E', g', cs, lrs) ->
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', g', cs, lrs).
Proof.
  move => e0 IH0 e1 IH1 te m E g s m' E' g' cs lrs /andP [Hcf0 Hcf1] /= /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1] .
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2] .
  case Hmkr  : (mk_env_or E2 g2 ls1 ls2) => [[[E'0 g'0] cs0] ls] .
  case => <- _ <- <- <- .
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0) .
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1) .
  rewrite (mk_env_or_is_bit_blast_or Hmkr). reflexivity.
Qed .

Lemma mk_env_exp_is_bit_blast_exp_xor :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e2 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bxor e1 e2) s te ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bxor e1 e2) te ->
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', g', cs, lrs).
Proof.
  move=> e1 IH1 e2 IH2 te m E g s m' E' g' cs lrs /andP [Hcf1 Hcf2] /= /andP [/andP [Hwf1 Hwf2] _] .
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1) (IH2 _ _ _ _ _ _ _ _ _ _ Hcf2 Hwf2 Hmke2).
  by rewrite (mk_env_xor_is_bit_blast_xor Hmkr).
Qed.

Lemma mk_env_exp_is_bit_blast_exp_neg :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      AdhereConform.conform_exp (QFBV.Eunop QFBV.Uneg e1) s te ->
      QFBV.well_formed_exp (QFBV.Eunop QFBV.Uneg e1) te ->
    mk_env_exp m s E g (QFBV.Eunop QFBV.Uneg e1) = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g (QFBV.Eunop QFBV.Uneg e1) = (m', g', cs, lrs).
Proof.
  move=> e1 IH1 te m E g s m' E' g' cs lrs /= Hcf Hwf .
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf Hwf Hmke1).
  by rewrite (mk_env_neg_is_bit_blast_neg Hmkr).
Qed.

Lemma mk_env_exp_is_bit_blast_exp_add :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        AdhereConform.conform_exp (QFBV.Ebinop QFBV.Badd e e0) s te ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Badd e e0) te ->
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Badd e e0) = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g (QFBV.Ebinop QFBV.Badd e e0) = (m', g', cs, lrs).
Proof.
  move=> e0 IH0 e1 IH1 te m E g s m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_add E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  by rewrite (mk_env_add_is_bit_blast_add Hmkr).
Qed.

Lemma mk_env_exp_is_bit_blast_exp_sub :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bsub e e0) s te ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsub e e0) te ->
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsub e e0) = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g (QFBV.Ebinop QFBV.Bsub e e0) = (m', g', cs, lrs).
Proof.
  move=> e0 IH0 e1 IH1 te m E g s m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sub E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  by rewrite (mk_env_sub_is_bit_blast_sub Hmkr).
Qed.

Lemma mk_env_exp_is_bit_blast_exp_mul :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bmul e e0) s te ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bmul e e0) te ->
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmul e e0) = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g (QFBV.Ebinop QFBV.Bmul e e0) = (m', g', cs, lrs).
Proof.
  move=> e0 IH0 e1 IH1 te m E g s m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_mul E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  by rewrite (mk_env_mul_is_bit_blast_mul Hmkr).
Qed.

Lemma mk_env_exp_is_bit_blast_exp_mod :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
  forall (e0 : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e0 s te ->
        QFBV.well_formed_exp e0 te ->
        mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
  forall (te : SSATE.env) (m : vm) (E : env)
         (g : generator) (s : SSAStore.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : word),
    AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bmod e e0) s te ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bmod e e0) te ->
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmod e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bmod e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_srem :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
  forall (e0 : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e0 s te ->
        QFBV.well_formed_exp e0 te ->
        mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
  forall (te : SSATE.env) (m : vm) (E : env)
         (g : generator) (s : SSAStore.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : word),
    AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bsrem e e0) s te ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsrem e e0) te ->
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_smod :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
  forall (e0 : QFBV.exp),
    (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e0 s te ->
        QFBV.well_formed_exp e0 te ->
        mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
  forall (te : SSATE.env) (m : vm) (E : env)
         (g : generator) (s : SSAStore.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : word),
    AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bsmod e e0) s te ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsmod e e0) te ->
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', g', cs, lrs).
Proof.
Admitted.

Lemma mk_env_exp_is_bit_blast_exp_shl :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e1 s te ->
          QFBV.well_formed_exp e1 te ->
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bshl e0 e1) s te ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bshl e0 e1) te ->
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', E', g', cs, lrs) ->
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', g', cs, lrs).
Proof.
  move=> e0 IH0 e1 IH1 te m E g s m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_shl E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  by rewrite (mk_env_shl_is_bit_blast_shl Hmkr).
Qed .

Lemma mk_env_exp_is_bit_blast_exp_lshr :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e1 s te ->
          QFBV.well_formed_exp e1 te ->
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Blshr e0 e1) s te ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Blshr e0 e1) te ->
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', E', g', cs, lrs) ->
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', g', cs, lrs).
Proof.
  move=> e0 IH0 e1 IH1 te m E g s m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_lshr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  by rewrite (mk_env_lshr_is_bit_blast_lshr Hmkr).
Qed .

Lemma mk_env_exp_is_bit_blast_exp_ashr :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e1 s te ->
          QFBV.well_formed_exp e1 te ->
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bashr e0 e1) s te ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bashr e0 e1) te ->
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', E', g', cs, lrs) ->
      bit_blast_exp te m g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', g', cs, lrs).
Proof.
  move=> e0 IH0 e1 IH1 te m E g s m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ashr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  by rewrite (mk_env_ashr_is_bit_blast_ashr Hmkr).
Qed .

Lemma mk_env_exp_is_bit_blast_exp_concat :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e1 s te ->
          QFBV.well_formed_exp e1 te ->
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      AdhereConform.conform_exp (QFBV.Ebinop QFBV.Bconcat e0 e1) s te ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bconcat e0 e1) te ->
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', g', cs, lrs).
Proof.
  move=> e0 IH0 e1 IH1 te m E g s m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1) //.
Qed .

Lemma mk_env_exp_is_bit_blast_exp_extract :
  forall (i j : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e s te ->
          QFBV.well_formed_exp e te ->
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      AdhereConform.conform_exp (QFBV.Eunop (QFBV.Uextr i j) e) s te ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uextr i j) e) te ->
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', E', g', cs, lrs) ->
      bit_blast_exp te m g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', g', cs, lrs).
Proof.
  move=> i j e0 IH0 te m E g s m' E' g' cs lrs /= Hcf Hwf .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf Hwf Hmke0) // .
Qed .

(*
Lemma mk_env_exp_is_bit_blast_exp_slice :
  forall (w1 w2 w3 : nat),
    forall (e : exp (w3 + w2 + w1)),
      (forall (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          bit_blast_exp m g e = (m', g', cs, lrs)) ->
    forall (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      bit_blast_exp m g (QFBV64.bvSlice w1 w2 w3 e) = (m', g', cs, lrs).
Proof.
  rewrite /=; intros; dcase_hyps; subst.
    by rewrite (H _ _ _ _ _ _ _ _ _ H0) .
Qed .
*)

Lemma mk_env_exp_is_bit_blast_exp_high :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e s te ->
          QFBV.well_formed_exp e te ->
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm)
         (E : env) (g : generator) (s : SSAStore.t) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      AdhereConform.conform_exp (QFBV.Eunop (QFBV.Uhigh n) e) s te ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uhigh n) e) te ->
    mk_env_exp m s E g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', g', cs, lrs).
Proof.
  move=> n e0 IH0 te m E g s m' E' g' cs lrs /= Hcf Hwf .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf Hwf Hmke0) //.
Qed .

Lemma mk_env_exp_is_bit_blast_exp_low :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e s te ->
          QFBV.well_formed_exp e te ->
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      AdhereConform.conform_exp (QFBV.Eunop (QFBV.Ulow n) e) s te ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Ulow n) e) te ->
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Ulow n) e) = (m', E', g', cs, lrs) ->
      bit_blast_exp te m g (QFBV.Eunop (QFBV.Ulow n) e) = (m', g', cs, lrs).
Proof.
  move=> n e0 IH0 te m E g s m' E' g' cs lrs /= Hcf Hwf0 .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf Hwf0 Hmke0) // .
Qed .

Lemma mk_env_exp_is_bit_blast_exp_zeroextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e s te ->
          QFBV.well_formed_exp e te ->
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (E : env)
             (g : generator) (s : SSAStore.t) (m' : vm) (E' : env)
             (g' : generator) (cs : cnf) (lrs : word),
        AdhereConform.conform_exp (QFBV.Eunop (QFBV.Uzext n) e) s te ->
        QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uzext n) e) te ->
        mk_env_exp m s E g (QFBV.Eunop (QFBV.Uzext n) e) = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g (QFBV.Eunop (QFBV.Uzext n) e) = (m', g', cs, lrs).
Proof.
  move=> n e0 IH0 te m E g s m' E' g' cs lrs /= Hcf Hwf0 .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf Hwf0 Hmke0) //.
Qed .

Lemma mk_env_exp_is_bit_blast_exp_signextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m  : vm) (E  : env) (g  : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e s te ->
          QFBV.well_formed_exp e te ->
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env)
         (g : generator) (s : SSAStore.t) (m' : vm) (E' : env)
         (g' : generator) (cs : cnf) (lrs : word),
      AdhereConform.conform_exp (QFBV.Eunop (QFBV.Usext n) e) s te ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Usext n) e) te ->
    mk_env_exp m s E g (QFBV.Eunop (QFBV.Usext n) e) = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g (QFBV.Eunop (QFBV.Usext n) e) = (m', g', cs, lrs).
Proof.
  move=> n e0 IH0 te m E g s m' E' g' cs lrs /= Hcf Hwf0 .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf Hwf0 Hmke0) //.
Qed .

Lemma mk_env_exp_is_bit_blast_exp_ite :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        AdhereConform.conform_bexp b s te ->
        QFBV.well_formed_bexp b te ->
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g b = (m', g', cs, lr)) ->
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e0 s te ->
        QFBV.well_formed_exp e0 te ->
        mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
    forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      AdhereConform.conform_exp (QFBV.Eite b e e0) s te ->
      QFBV.well_formed_exp (QFBV.Eite b e e0) te ->
      mk_env_exp m s E g (QFBV.Eite b e e0) = (m', E', g', cs, lrs) ->
      bit_blast_exp te m g (QFBV.Eite b e e0) = (m', g', cs, lrs).
Proof.
  move=> c IHc e0 IH0 e1 IH1 te m E g s m' E' g' cs lrs /= /andP [/andP [Hcfc Hcf0] Hcf1] /andP [/andP [/andP [Hwfc Hwf0] Hwf1] _] .
  case Hmkec : (mk_env_bexp m s E g c) => [[[[mc Ec] gc] csc] lc].
  case Hmke0 : (mk_env_exp mc s Ec gc e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ite E2 g2 lc ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IHc _ _ _ _ _ _ _ _ _ _ Hcfc Hwfc Hmkec).
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  by rewrite (mk_env_ite_is_bit_blast_ite Hmkr).
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_false :
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    AdhereConform.conform_bexp QFBV.Bfalse s te ->
    QFBV.well_formed_bexp QFBV.Bfalse te ->
    mk_env_bexp m s E g QFBV.Bfalse = (m', E', g', cs, lr) ->
    bit_blast_bexp te m g QFBV.Bfalse = (m', g', cs, lr).
Proof.
  move => te m s E g m' E' g' cs lr Hcf _ .
  rewrite /=; case => <- _ <- <- <- // .
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_true :
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    AdhereConform.conform_bexp QFBV.Btrue s te ->
    QFBV.well_formed_bexp QFBV.Btrue te ->
    mk_env_bexp m s E g QFBV.Btrue = (m', E', g', cs, lr) ->
    bit_blast_bexp te m g QFBV.Btrue = (m', g', cs, lr).
Proof.
  move => te m s E g m' E' g' cs lr Hcf _ .
  rewrite /=; case => <- _ <- <- <- // .
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_eq :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Beq e e0) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Beq e e0) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Beq e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Beq e e0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_eq E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  by rewrite (mk_env_eq_is_bit_blast_eq Hmkr).
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_ult :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bult e e0) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bult e e0) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bult e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bult e e0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ult E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  by rewrite (mk_env_ult_is_bit_blast_ult Hmkr).
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_ule :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bule e e0) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bule e e0) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bule e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bule e e0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ule E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_ule_is_bit_blast_ule Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_ugt :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bugt e e0) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bugt e e0) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bugt e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bugt e e0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ugt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_ugt_is_bit_blast_ugt Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_uge :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Buge e e0) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Buge e e0) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buge e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Buge e e0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_uge_is_bit_blast_uge Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_slt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e2 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bslt e1 e2) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bslt e1 e2) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_slt_is_bit_blast_slt Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_sle :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e2 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsle e1 e2) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsle e1 e2) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_sle_is_bit_blast_sle Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_sgt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e2 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsgt e1 e2) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsgt e1 e2) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_sgt_is_bit_blast_sgt Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_sge :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e2 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsge e1 e2) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsge e1 e2) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_sge_is_bit_blast_sge Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_uaddo :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Buaddo e e0) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Buaddo e e0) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uaddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_uaddo_is_bit_blast_uaddo Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_usubo :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Busubo e e0) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Busubo e e0) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Busubo e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Busubo e e0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_usubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_usubo_is_bit_blast_usubo Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_umulo :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e s te ->
        QFBV.well_formed_exp e te ->
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e = (m', g', cs, lrs)) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e0 s te ->
          QFBV.well_formed_exp e0 te ->
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e0 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bumulo e e0) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bumulo e e0) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_umulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_umulo_is_bit_blast_umulo Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_saddo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e2 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsaddo e1 e2) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsaddo e1 e2) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_saddo_is_bit_blast_saddo Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_ssubo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e2 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bssubo e1 e2) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bssubo e1 e2) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_ssubo_is_bit_blast_ssubo Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_smulo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        AdhereConform.conform_exp e1 s te ->
        QFBV.well_formed_exp e1 te ->
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        bit_blast_exp te m g e1 = (m', g', cs, lrs)) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (E : env) (g : generator) (s : SSAStore.t)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          AdhereConform.conform_exp e2 s te ->
          QFBV.well_formed_exp e2 te ->
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          bit_blast_exp te m g e2 = (m', g', cs, lrs)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bbinop QFBV.Bsmulo e1 e2) s te ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsmulo e1 e2) te ->
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [/andP [Hwf0 Hwf1] _] .
  case Hmke0 : (mk_env_exp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_exp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1).
  rewrite (mk_env_smulo_is_bit_blast_smulo Hmkr) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_lneg :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp b s te ->
        QFBV.well_formed_bexp b te ->
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g b = (m', g', cs, lr)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Blneg b) s te ->
        QFBV.well_formed_bexp (QFBV.Blneg b) te ->
        mk_env_bexp m s E g (QFBV.Blneg b) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Blneg b) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 te m s E g m' E' g' cs lrs /= Hcf Hwf0 .
  case Hmke0 : (mk_env_bexp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf Hwf0 Hmke0) // .
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_conj :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp b s te ->
        QFBV.well_formed_bexp b te ->
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g b = (m', g', cs, lr)) ->
    forall (b0 : QFBV.bexp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          AdhereConform.conform_bexp b0 s te ->
          QFBV.well_formed_bexp b0 te ->
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          bit_blast_bexp te m g b0 = (m', g', cs, lr)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bconj b b0) s te ->
        QFBV.well_formed_bexp (QFBV.Bconj b b0) te ->
        mk_env_bexp m s E g (QFBV.Bconj b b0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bconj b b0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [Hwf0 Hwf1] .
  case Hmke0 : (mk_env_bexp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_bexp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1) //.
Qed.

Lemma mk_env_bexp_is_bit_blast_bexp_disj :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp b s te ->
        QFBV.well_formed_bexp b te ->
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g b = (m', g', cs, lr)) ->
    forall (b0 : QFBV.bexp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          AdhereConform.conform_bexp b0 s te ->
          QFBV.well_formed_bexp b0 te ->
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          bit_blast_bexp te m g b0 = (m', g', cs, lr)) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        AdhereConform.conform_bexp (QFBV.Bdisj b b0) s te ->
        QFBV.well_formed_bexp (QFBV.Bdisj b b0) te ->
        mk_env_bexp m s E g (QFBV.Bdisj b b0) = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g (QFBV.Bdisj b b0) = (m', g', cs, lr).
Proof.
  move=> e0 IH0 e1 IH1 te m s E g m' E' g' cs lrs /= /andP [Hcf0 Hcf1] /andP [Hwf0 Hwf1] .
  case Hmke0 : (mk_env_bexp m s E g e0) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke1 : (mk_env_bexp m1 s E1 g1 e1) => [[[[m2 E2] g2] cs2] ls2].
  case=> <- _ <- <- <-.
  rewrite (IH0 _ _ _ _ _ _ _ _ _ _ Hcf0 Hwf0 Hmke0).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hcf1 Hwf1 Hmke1) //.
Qed.

Corollary mk_env_exp_is_bit_blast_exp :
  forall (e : QFBV.exp) te m E g s m' E' g' cs lrs,
    AdhereConform.conform_exp e s te ->
    QFBV.well_formed_exp e te ->
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    bit_blast_exp te m g e = (m', g', cs, lrs)
  with
    mk_env_bexp_is_bit_blast_bexp :
      forall e te m s E g m' E' g' cs lr,
        AdhereConform.conform_bexp e s te ->
        QFBV.well_formed_bexp e te ->
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        bit_blast_bexp te m g e = (m', g', cs, lr).
Proof.
  (* mk_env_exp_is_bit_blast_exp *)
  elim .
  - move => v; apply : mk_env_exp_is_bit_blast_exp_var .
  - move => b; apply : mk_env_exp_is_bit_blast_exp_const .
  - elim .
    + apply : mk_env_exp_is_bit_blast_exp_not .
    + apply : mk_env_exp_is_bit_blast_exp_neg .
    + apply : mk_env_exp_is_bit_blast_exp_extract .
    + apply : mk_env_exp_is_bit_blast_exp_high .
    + apply : mk_env_exp_is_bit_blast_exp_low .
    + apply : mk_env_exp_is_bit_blast_exp_zeroextend .
    + apply : mk_env_exp_is_bit_blast_exp_signextend .
  - elim .
    + apply : mk_env_exp_is_bit_blast_exp_and .
    + apply : mk_env_exp_is_bit_blast_exp_or .
    + apply : mk_env_exp_is_bit_blast_exp_xor .
    + apply : mk_env_exp_is_bit_blast_exp_add .
    + apply : mk_env_exp_is_bit_blast_exp_sub .
    + apply : mk_env_exp_is_bit_blast_exp_mul .
    + apply : mk_env_exp_is_bit_blast_exp_mod .
    + apply : mk_env_exp_is_bit_blast_exp_srem .
    + apply : mk_env_exp_is_bit_blast_exp_smod .
    + apply : mk_env_exp_is_bit_blast_exp_shl .
    + apply : mk_env_exp_is_bit_blast_exp_lshr .
    + apply : mk_env_exp_is_bit_blast_exp_ashr .
    + apply : mk_env_exp_is_bit_blast_exp_concat .
  - move => b .
    move : (mk_env_bexp_is_bit_blast_bexp b) .
    apply : mk_env_exp_is_bit_blast_exp_ite .
  (* mk_env_bexp_is_bit_blast_bexp *)
  elim .
  - apply: mk_env_bexp_is_bit_blast_bexp_false.
  - apply: mk_env_bexp_is_bit_blast_bexp_true.
  - elim;
      move => e e0;
      move :  e (mk_env_exp_is_bit_blast_exp e)
             e0 (mk_env_exp_is_bit_blast_exp e0) .
    + apply : mk_env_bexp_is_bit_blast_bexp_eq .
    + apply : mk_env_bexp_is_bit_blast_bexp_ult .
    + apply : mk_env_bexp_is_bit_blast_bexp_ule .
    + apply : mk_env_bexp_is_bit_blast_bexp_ugt .
    + apply : mk_env_bexp_is_bit_blast_bexp_uge .
    + apply : mk_env_bexp_is_bit_blast_bexp_slt .
    + apply : mk_env_bexp_is_bit_blast_bexp_sle .
    + apply : mk_env_bexp_is_bit_blast_bexp_sgt .
    + apply : mk_env_bexp_is_bit_blast_bexp_sge .
    + apply : mk_env_bexp_is_bit_blast_bexp_uaddo .
    + apply : mk_env_bexp_is_bit_blast_bexp_usubo .
    + apply : mk_env_bexp_is_bit_blast_bexp_umulo .
    + apply : mk_env_bexp_is_bit_blast_bexp_saddo .
    + apply : mk_env_bexp_is_bit_blast_bexp_ssubo .
    + apply : mk_env_bexp_is_bit_blast_bexp_smulo .
  - apply : mk_env_bexp_is_bit_blast_bexp_lneg .
  - apply : mk_env_bexp_is_bit_blast_bexp_conj .
  - apply : mk_env_bexp_is_bit_blast_bexp_disj .
Qed.

(* = mk_env_exp_newer_gen and mk_env_bexp_newer_gen = *)

Lemma mk_env_exp_newer_gen_var :
  forall t (m : vm) (s : SSAStore.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Evar t) = (m', E', g', cs, lrs) -> (g <=? g')%positive.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case: (SSAVM.find v m).
  - move=> ls [] _ _ <- _ _. exact: Pos.leb_refl.
  - case Henv: (mk_env_var E g (SSAStore.acc v s) v) => [[[oE og] ocs] olrs].
    case=> _ _ <- _ _. exact: (mk_env_var_newer_gen Henv).
Qed.

Lemma mk_env_exp_newer_gen_const :
  forall (b : bits) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Econst b) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> bs m s E g m' E' g' cs lrs /=. case=> _ _ <- _ _. exact: Pos.leb_refl.
Qed.

Lemma mk_env_exp_newer_gen_not :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop QFBV.Unot e1) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (mk_env_not_newer_gen Hmkr) => Hg1gr.
  apply: (pos_leb_trans Hg0g1). done.
Qed.

Lemma mk_env_exp_newer_gen_and :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Band e1 e2) = (m', E', g', cs, lrs) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_and_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_exp_newer_gen_or :
    forall (e0: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_or E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_or_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed .

Lemma mk_env_exp_newer_gen_xor :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', E', g', cs, lrs) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_xor_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_exp_newer_gen_neg :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop QFBV.Uneg e1) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (mk_env_neg_newer_gen Hmkr) => Hg1gr.
  apply: (pos_leb_trans Hg0g1). done.
Qed.

Lemma mk_env_exp_newer_gen_add :
    forall (e0: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Badd e0 e1) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_add E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_add_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_exp_newer_gen_sub :
    forall (e0: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsub e0 e1) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sub E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_sub_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_exp_newer_gen_mul :
    forall (e: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmul e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_mul E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_mul_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_exp_newer_gen_mod :
  forall (e : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
  forall (e0 : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmod e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_srem :
  forall (e : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
  forall (e0 : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_smod :
  forall (e : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
  forall (e0 : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
Admitted.

Lemma mk_env_exp_newer_gen_shl :
    forall (e0 : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1 : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_shl E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_shl_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed .

Lemma mk_env_exp_newer_gen_lshr :
    forall (e0 : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1 : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_lshr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_lshr_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed .

Lemma mk_env_exp_newer_gen_ashr :
    forall (e0 : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1 : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ashr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_ashr_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed .

Lemma mk_env_exp_newer_gen_concat :
    forall (e0: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e1: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_concat E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_concat_newer_gen Hmkr) => Hg2gr.
  by apply: (pos_leb_trans _ Hg1g2).
Qed .

Lemma mk_env_exp_newer_gen_extract :
  forall (i j : nat),
    forall (e : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> i j e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ _.
  exact : (IH1 _ _ _ _ _ _ _ _ _ Hmke1) .
Qed .

(*
Lemma mk_env_exp_newer_gen_slice :
  forall (w1 w2 w3 : nat),
    forall (e : exp (w3 + w2 + w1)),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .
*)

Lemma mk_env_exp_newer_gen_high :
    forall (n : nat) (e : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm)
           (s : SSAStore.t) (E : env) (g : generator) (m' : vm)
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ _.
  exact : (IH1 _ _ _ _ _ _ _ _ _ Hmke1) .
Qed .

Lemma mk_env_exp_newer_gen_low :
    forall (n : nat) (e : QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Ulow n) e) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ _.
  exact : (IH1 _ _ _ _ _ _ _ _ _ Hmke1) .
Qed .

Lemma mk_env_exp_newer_gen_zeroextend :
  forall (n : nat),
    forall (e: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop (QFBV.Uzext n) e) = (m', E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ _.
  exact : (IH1 _ _ _ _ _ _ _ _ _ Hmke1) .
Qed .

Lemma mk_env_exp_newer_gen_signextend :
  forall (n : nat),
    forall (e: QFBV.exp),
      (forall (m  : vm) (s  : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Usext n) e) = (m', E', g', cs, lrs) ->
      (g <=? g')%positive.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ _.
  exact : (IH1 _ _ _ _ _ _ _ _ _ Hmke1) .
Qed .

Lemma mk_env_exp_newer_gen_ite :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (e0 : QFBV.exp),
        (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : word),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
        forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp m s E g (QFBV.Eite b e e0) = (m', E', g', cs, lrs) ->
          (g <=? g')%positive.
Proof.
  move=> c IHc e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmkc : (mk_env_bexp m s E g c) => [[[[mc Ec] gc] csc] lc].
  case Hmke1 : (mk_env_exp mc s Ec gc e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ite E2 g2 lc ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IHc _ _ _ _ _ _ _ _ _ Hmkc) => Hggc.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hgcg1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_ite_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_false :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Bfalse = (m', E', g', cs, lr) -> (g <=? g')%positive.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- _ _. exact: Pos.leb_refl.
Qed.

Lemma mk_env_bexp_newer_gen_true :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Btrue = (m', E', g', cs, lr) -> (g <=? g')%positive.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- _ _. exact: Pos.leb_refl.
Qed.

Lemma mk_env_bexp_newer_gen_eq :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Beq e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_eq E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_eq_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_ult :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bult e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ult E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_ult_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_ule :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bule e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ule E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_ule_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_ugt :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bugt e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ugt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_ugt_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.


Lemma mk_env_bexp_newer_gen_uge :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buge e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_uge_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_slt :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_slt_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_sle :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_sle_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_sgt :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_sgt_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_sge :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_sge_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_uaddo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uaddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_uaddo_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_usubo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Busubo e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_usubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_usubo_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_umulo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_umulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_umulo_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_saddo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_saddo_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_ssubo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_ssubo_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_smulo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  move: (mk_env_smulo_newer_gen Hmkr) => Hg2gr.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_lneg :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Blneg b) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
   t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_conj :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
    forall (b0 : QFBV.bexp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bconj b b0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_gen_disj :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
    forall (b0 : QFBV.bexp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) -> (g <=? g')%positive) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bdisj b b0) = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case=> _ _ <- _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => Hg0g1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => Hg1g2.
  t_auto_newer .
Qed.

Corollary mk_env_exp_newer_gen :
  forall (e : QFBV.exp) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    (g <=? g')%positive
  with
    mk_env_bexp_newer_gen :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        (g <=? g')%positive.
Proof.
  (* mk_env_exp_newer_gen *)
  elim .
  - exact: mk_env_exp_newer_gen_var.
  - exact: mk_env_exp_newer_gen_const.
  - elim .
    + apply :mk_env_exp_newer_gen_not .
    + apply :mk_env_exp_newer_gen_neg .
    + apply :mk_env_exp_newer_gen_extract .
    + apply :mk_env_exp_newer_gen_high .
    + apply :mk_env_exp_newer_gen_low .
    + apply :mk_env_exp_newer_gen_zeroextend .
    + apply :mk_env_exp_newer_gen_signextend .
  - elim .
    + apply :mk_env_exp_newer_gen_and .
    + apply :mk_env_exp_newer_gen_or .
    + apply :mk_env_exp_newer_gen_xor .
    + apply :mk_env_exp_newer_gen_add .
    + apply :mk_env_exp_newer_gen_sub .
    + apply :mk_env_exp_newer_gen_mul .
    + apply :mk_env_exp_newer_gen_mod .
    + apply :mk_env_exp_newer_gen_srem .
    + apply :mk_env_exp_newer_gen_smod .
    + apply :mk_env_exp_newer_gen_shl .
    + apply :mk_env_exp_newer_gen_lshr .
    + apply :mk_env_exp_newer_gen_ashr .
    + apply :mk_env_exp_newer_gen_concat .
  - move => b; move : b (mk_env_bexp_newer_gen b) .
    apply :mk_env_exp_newer_gen_ite .
  (* mk_env_bexp_newer_gen *)
  elim .
  - apply : mk_env_bexp_newer_gen_false .
  - apply : mk_env_bexp_newer_gen_true .
  - elim;
      move => e1 e2;
      move : e1 (mk_env_exp_newer_gen e1)
             e2 (mk_env_exp_newer_gen e2) .
    + apply : mk_env_bexp_newer_gen_eq .
    + apply : mk_env_bexp_newer_gen_ult .
    + apply : mk_env_bexp_newer_gen_ule .
    + apply : mk_env_bexp_newer_gen_ugt .
    + apply : mk_env_bexp_newer_gen_uge .
    + apply : mk_env_bexp_newer_gen_slt .
    + apply : mk_env_bexp_newer_gen_sle .
    + apply : mk_env_bexp_newer_gen_sgt .
    + apply : mk_env_bexp_newer_gen_sge .
    + apply : mk_env_bexp_newer_gen_uaddo .
    + apply : mk_env_bexp_newer_gen_usubo .
    + apply : mk_env_bexp_newer_gen_umulo .
    + apply : mk_env_bexp_newer_gen_saddo .
    + apply : mk_env_bexp_newer_gen_ssubo .
    + apply : mk_env_bexp_newer_gen_smulo .
  - apply : mk_env_bexp_newer_gen_lneg .
  - apply : mk_env_bexp_newer_gen_conj .
  - apply : mk_env_bexp_newer_gen_disj .
Qed.



(* = mk_env_exp_newer_vm and mk_env_bexp_newer_vm = *)

Lemma mk_env_exp_newer_vm_var :
  forall t (m : vm) (s : SSAStore.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Evar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case Hfind: (SSAVM.find v m).
  - case=> <- _ <- _ _ Hnew_gm // .
  - case Henv: (mk_env_var E g (SSAStore.acc v s) v) => [[[oE og] ocs] olrs].
    case=> <- _ <- _ _ Hnew_gm.
    move=> x lxs. case Hxv: (x == v).
    + rewrite (SSAVM.Lemmas.find_add_eq Hxv) .
      case => <-; exact: (mk_env_var_newer_res Henv).
    + move/negP: Hxv => Hxv. rewrite (SSAVM.Lemmas.find_add_neq Hxv) => Hfindx.
      move: (Hnew_gm x lxs Hfindx) => Hnew_og.
      apply: (newer_than_lits_le_newer Hnew_og). exact: (mk_env_var_newer_gen Henv).
Qed.

Lemma mk_env_exp_newer_vm_const :
  forall (b : bits) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Econst b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> b m s E g m' E' g' cs lrs. case=> <- _ <- _ _. by apply.
Qed.

Lemma mk_env_exp_newer_vm_not :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop QFBV.Unot e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (mk_env_not_newer_gen Hmkr) => Hg1gr.
  exact: (newer_than_vm_le_newer Hg1m1 Hg1gr).
Qed.

Lemma mk_env_exp_newer_vm_and :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Band e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_and_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_exp_newer_vm_or :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_or E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_or_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed .

Lemma mk_env_exp_newer_vm_xor :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_xor_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_exp_newer_vm_neg :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop QFBV.Uneg e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (mk_env_neg_newer_gen Hmkr) => Hg1gr.
  exact: (newer_than_vm_le_newer Hg1m1 Hg1gr).
Qed.

Lemma mk_env_exp_newer_vm_add :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Badd e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_add E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_add_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_exp_newer_vm_sub :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsub e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sub E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_sub_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_exp_newer_vm_mul :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmul e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_mul E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_mul_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_exp_newer_vm_mod :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_srem :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_smod :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
Admitted.

Lemma mk_env_exp_newer_vm_shl :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_shl E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_shl_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed .

Lemma mk_env_exp_newer_vm_lshr :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_lshr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_lshr_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed .

Lemma mk_env_exp_newer_vm_ashr :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ashr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_ashr_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed .

Lemma mk_env_exp_newer_vm_concat :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_concat E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  apply : (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) .
Qed .

Lemma mk_env_exp_newer_vm_extract :
  forall (i j : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> i j e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- _ _ Hg0m0.
  apply: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) .
Qed .

(*
Lemma mk_env_exp_newer_vm_slice :
  forall (w1 w2 w3 : nat),
    forall (e : exp (w3 + w2 + w1)),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  by apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .
*)

Lemma mk_env_exp_newer_vm_high :
    forall (n : nat) (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm)
           (s : SSAStore.t) (E : env) (g : generator) (m' : vm)
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- _ _ Hg0m0.
  apply : (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) .
Qed .

Lemma mk_env_exp_newer_vm_low :
    forall (n : nat) (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Ulow n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- _ _ Hg0m0.
  apply : (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) .
Qed .

Lemma mk_env_exp_newer_vm_zeroextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : word),
        mk_env_exp m s E g (QFBV.Eunop (QFBV.Uzext n) e) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- _ _ Hg0m0.
  apply : (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) .
Qed .

Lemma mk_env_exp_newer_vm_signextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
    forall (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Usext n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- _ <- _ _ Hg0m0.
  apply : (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) . 
Qed .

Lemma mk_env_exp_newer_vm_ite :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (e0 : QFBV.exp),
        (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : word),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
            newer_than_vm g m -> newer_than_vm g' m') ->
        forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp m s E g (QFBV.Eite b e e0) = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> c IHc e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmkc : (mk_env_bexp m s E g c) => [[[[mc Ec] gc] csc] lsc].
  case Hmke1 : (mk_env_exp mc s Ec gc e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ite E2 g2 lsc ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IHc _ _ _ _ _ _ _ _ _ Hmkc Hg0m0) => Hgcmc.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgcmc) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_ite_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_false :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Bfalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> m s E g m' E' g' cs lr. case=> <- _ <- _ _ // .
Qed.

Lemma mk_env_bexp_newer_vm_true :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Btrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> m s E g m' E' g' cs lr. case=> <- _ <- _ _ // .
Qed.

Lemma mk_env_bexp_newer_vm_eq :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Beq e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_eq E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_eq_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_ult :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bult e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ult E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_ult_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_ule :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bule e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ule E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_ule_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_ugt :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bugt e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ugt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_ugt_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_uge :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buge e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_uge_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.


Lemma mk_env_bexp_newer_vm_slt :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_slt_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_sle :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_sle_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_sgt :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_sgt_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_sge :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_sge_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_uaddo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uaddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_uaddo_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_usubo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Busubo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_usubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_usubo_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_umulo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_umulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_umulo_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_saddo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_saddo_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_ssubo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_ssubo_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_smulo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- _ <- _ _ Hg0m0.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hg0m0) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1) => Hg2m2.
  move: (mk_env_smulo_newer_gen Hmkr) => Hg2gr.
  exact: (newer_than_vm_le_newer Hg2m2 Hg2gr).
Qed.

Lemma mk_env_bexp_newer_vm_lneg :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Blneg b) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e IH m s E g m' E' g' cs lr /=.
  case Henv: (mk_env_bexp m s E g e) => [[[[m1 E1] g1] cs1] lr1].
  case => <- _ <- _ _ Hnew. apply newer_than_vm_add_r.
  apply: (IH _ _ _ _ _ _ _ _ _ Henv).
  exact.
Qed.

Lemma mk_env_bexp_newer_vm_conj :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (b0 : QFBV.bexp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bconj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /=.
  case Henv1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case=> <- _ <- _ _ Hnew. apply: newer_than_vm_add_r.
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2). apply: (IH1 _ _ _ _ _ _ _ _ _ Henv1).
  exact: Hnew.
Qed.

Lemma mk_env_bexp_newer_vm_disj :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m') ->
    forall (b0 : QFBV.bexp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_vm g' m') ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bdisj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /=.
  case Henv1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case=> <- _ <- _ _ Hnew. apply: newer_than_vm_add_r.
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2). apply: (IH1 _ _ _ _ _ _ _ _ _ Henv1).
  exact: Hnew.
Qed.

Corollary mk_env_exp_newer_vm :
  forall (e : QFBV.exp) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_vm g' m'
  with
    mk_env_bexp_newer_vm :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_vm g' m'.
Proof.
  (* mk_env_exp_newer_vm *)
  elim .
  - exact: mk_env_exp_newer_vm_var .
  - exact: mk_env_exp_newer_vm_const .
  - elim .
    + exact: mk_env_exp_newer_vm_not .
    + exact: mk_env_exp_newer_vm_neg .
    + exact: mk_env_exp_newer_vm_extract .
    + exact: mk_env_exp_newer_vm_high .
    + exact: mk_env_exp_newer_vm_low .
    + exact: mk_env_exp_newer_vm_zeroextend .
    + exact: mk_env_exp_newer_vm_signextend .
  - elim .
    + exact: mk_env_exp_newer_vm_and .
    + exact: mk_env_exp_newer_vm_or .
    + exact: mk_env_exp_newer_vm_xor .
    + exact: mk_env_exp_newer_vm_add .
    + exact: mk_env_exp_newer_vm_sub .
    + exact: mk_env_exp_newer_vm_mul .
    + exact: mk_env_exp_newer_vm_mod .
    + exact: mk_env_exp_newer_vm_srem .
    + exact: mk_env_exp_newer_vm_smod .
    + exact: mk_env_exp_newer_vm_shl .
    + exact: mk_env_exp_newer_vm_lshr .
    + exact: mk_env_exp_newer_vm_ashr .
    + exact: mk_env_exp_newer_vm_concat .
  - move => b; move : b (mk_env_bexp_newer_vm b) .
    exact: mk_env_exp_newer_vm_ite .
  (* mk_env_bexp_newer_vm *)
  elim .
  - exact: mk_env_bexp_newer_vm_false .
  - exact: mk_env_bexp_newer_vm_true .
  - elim;
      move => e0 e1;
      move : e0 (mk_env_exp_newer_vm e0)
             e1 (mk_env_exp_newer_vm e1) .
    + exact: mk_env_bexp_newer_vm_eq .
    + exact: mk_env_bexp_newer_vm_ult .
    + exact: mk_env_bexp_newer_vm_ule .
    + exact: mk_env_bexp_newer_vm_ugt .
    + exact: mk_env_bexp_newer_vm_uge .
    + exact: mk_env_bexp_newer_vm_slt .
    + exact: mk_env_bexp_newer_vm_sle .
    + exact: mk_env_bexp_newer_vm_sgt .
    + exact: mk_env_bexp_newer_vm_sge .
    + exact: mk_env_bexp_newer_vm_uaddo .
    + exact: mk_env_bexp_newer_vm_usubo .
    + exact: mk_env_bexp_newer_vm_umulo .
    + exact: mk_env_bexp_newer_vm_saddo .
    + exact: mk_env_bexp_newer_vm_ssubo .
    + exact: mk_env_bexp_newer_vm_smulo .
  - exact: mk_env_bexp_newer_vm_lneg .
  - exact: mk_env_bexp_newer_vm_conj .
  - exact: mk_env_bexp_newer_vm_disj .
Qed.



(* = mk_env_exp_newer_res and mk_env_bexp_newer_res = *)

Lemma mk_env_exp_newer_res_var :
  forall t (m : vm) (s : SSAStore.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Evar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case Hfind: (SSAVM.find v m).
  - case=> _ _ <- _ <- Hnew_gm Hnew_gtt. exact: (Hnew_gm v _ Hfind).
  - case Henv: (mk_env_var E g (SSAStore.acc v s) v)=> [[[Ev gv] csv] lrsv].
    case=> _ _ <- _ <- Hnew_gm Hnew_gtt. exact: (mk_env_var_newer_res Henv).
Qed.

Lemma mk_env_exp_newer_res_const :
  forall (b : bits) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Econst b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> bs m s E g m' E' g' cs lrs. rewrite /mk_env_exp.
  case Henv: (mk_env_const E g bs)=> [[[oE og] ocs] olrs].
  case=> _ _ <- _ <- Hnew_gm Hnew_tt. exact: (mk_env_const_newer_res Henv Hnew_tt).
Qed.

Lemma mk_env_exp_newer_res_not :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator)
            (cs : cnf) (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop QFBV.Unot e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  exact: (mk_env_not_newer_res Hmkr Hg1l1).
Qed.

Lemma mk_env_exp_newer_res_and :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator)
            (cs : cnf) (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        newer_than_lits g' lrs) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Band e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  (* now mk_env_and_newer_res is available *)
  exact: (mk_env_and_newer_res Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_newer_res_or :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_or E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  (* now mk_env_or_newer_res is available *)
  exact: (mk_env_or_newer_res Hmkr Hg2t Hg2l1 Hg2l2).
Qed .

Lemma mk_env_exp_newer_res_xor :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator)
            (cs : cnf) (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        newer_than_lits g' lrs) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  (* now mk_env_xor_newer_res is available *)
  exact: (mk_env_xor_newer_res Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_newer_res_neg :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator)
            (cs : cnf) (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop QFBV.Uneg e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  (* now mk_env_neg_newer_res is available *)
  exact: (mk_env_neg_newer_res Hmkr Hg1t Hg1l1).
Qed.

Lemma mk_env_exp_newer_res_add :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Badd e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_add E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  exact: (mk_env_add_newer_res Hmkr).
Qed.

Lemma mk_env_exp_newer_res_sub :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsub e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sub E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  (* now mk_env_sub_newer_res is available *)
  exact: (mk_env_sub_newer_res Hmkr).
Qed.

Lemma mk_env_exp_newer_res_mul :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmul e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_mul E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  (* now mk_env_mul_newer_res is available *)
  exact: (mk_env_mul_newer_res Hmkr Hg2t).
Qed.

Lemma mk_env_exp_newer_res_mod :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_srem :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_smod :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
Admitted.

Lemma mk_env_exp_newer_res_shl :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_shl E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  (* now mk_env_shl_newer_res is available *)
  exact: (mk_env_shl_newer_res Hg2t Hg2l1 Hg2l2 Hmkr) .
Qed .

Lemma mk_env_exp_newer_res_lshr :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_lshr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  (* now mk_env_lshr_newer_res is available *)
  exact: (mk_env_lshr_newer_res Hg2t Hg2l1 Hg2l2 Hmkr) .
Qed .

Lemma mk_env_exp_newer_res_ashr :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ashr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  (* now mk_env_ashr_newer_res is available *)
  exact: (mk_env_ashr_newer_res Hg2t Hg2l1 Hg2l2 Hmkr) .
Qed .

Lemma mk_env_exp_newer_res_concat :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  rewrite newer_than_lits_cat Hg2l1 Hg2l2 // .
Qed .

Lemma mk_env_exp_newer_res_extract :
  forall (i j : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> i j e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  apply : (@mk_env_extract_newer_res E _ _ _  _ _ _ _ _ _ Hg1t Hg1l1) .
  rewrite /mk_env_extract // .
Qed .

(*
Lemma mk_env_exp_newer_res_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV.exp (w3 + w2 + w1)),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move => w1 w2 w3 e IHe .
  rewrite /=; intros; dcase_hyps; subst .
  move: (IHe _ _ _ _ _ _ _ _ _ H H0 H1) => Hg'ls .
  apply: newer_than_lits_get_high_aux .
  by apply: newer_than_lits_get_low_aux .
Qed .
*)

Lemma mk_env_exp_newer_res_high :
    forall (n : nat) (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm)
         (s : SSAStore.t) (E : env) (g : generator) (m' : vm)
         (E' : env) (g' : generator) (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  (* now mk_env_high_newer_res is available *)
  exact : (@mk_env_high_newer_res E _ _ _ _ _ _ _ _ Hg1t Hg1l1) .
Qed .

Lemma mk_env_exp_newer_res_low :
    forall (n : nat) (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Ulow n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  (* now mk_env_low_newer_res is available *)
  exact : (@mk_env_low_newer_res E _ _ _ _ _ _ _ _ Hg1t Hg1l1) .
Qed .

Lemma mk_env_exp_newer_res_zeroextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uzext n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  (* now mk_env_zeroextend_newer_res is available *)
  exact: (@mk_env_zeroextend_newer_res _ E _ _ _ _ _ _ _ Hg1t Hg1l1) .
Qed .

Lemma mk_env_exp_newer_res_signextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
    forall (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Usext n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  (* now mk_env_signextend_newer_res is available *)
  exact: (@mk_env_signextend_newer_res _ E _ _ _ _ _ _ _ Hg1t Hg1l1) .
Qed .

Lemma mk_env_exp_newer_res_ite :
  forall (b : QFBV.bexp) (e e0 : QFBV.exp)
         (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Eite b e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs.
Proof.
  move=> c e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmkc : (mk_env_bexp m s E g c) => [[[[mc Ec] gc] csc] lsc].
  case Hmke1 : (mk_env_exp mc s Ec gc e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ite E2 g2 lsc ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  exact : mk_env_ite_newer_res Hmkr .
Qed.

Lemma mk_env_bexp_newer_res_false :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Bfalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- _ <- Hnvm Hnew. exact: Hnew.
Qed.

Lemma mk_env_bexp_newer_res_true :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Btrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ _ <- _ <- Hnvm Hnew. exact: Hnew.
Qed.

Lemma mk_env_bexp_newer_res_eq :
  forall (e e0 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Beq e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_eq E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  exact : (mk_env_eq_newer_res Hmkr) .
Qed.

Lemma mk_env_bexp_newer_res_ult :
  forall (e e0 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bult e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ult E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_ult_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_ult_newer_res Hmkr) .
  t_auto_newer .
Qed.


Lemma mk_env_bexp_newer_res_ule :
  forall (e e0 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bule e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ule E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_ule_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_ule_newer_res Hmkr) .
Qed.

Lemma mk_env_bexp_newer_res_ugt :
  forall (e e0 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bugt e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ugt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_ugt_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_ugt_newer_res Hmkr) .
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_res_uge :
  forall (e e0 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buge e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_uge_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_uge_newer_res Hmkr) .
Qed.

Lemma mk_env_bexp_newer_res_slt :
  forall (e1 e2 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_slt_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_slt_newer_res Hmkr) .
Qed.

Lemma mk_env_bexp_newer_res_sle :
  forall (e1 e2 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_sle_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_sle_newer_res Hmkr) .
Qed.

Lemma mk_env_bexp_newer_res_sgt :
  forall (e1 e2 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_sgt_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_sgt_newer_res Hmkr) .
Qed.

Lemma mk_env_bexp_newer_res_sge :
  forall (e1 e2 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_sge_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_sge_newer_res Hmkr) .
Qed.

Lemma mk_env_bexp_newer_res_uaddo :
  forall (e e0 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uaddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_uaddo_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_uaddo_newer_res Hmkr) .
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_res_usubo :
  forall (e e0 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Busubo e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_usubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_usubo_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_usubo_newer_res Hmkr) .
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_res_umulo :
  forall (e e0 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_umulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_umulo_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_umulo_newer_res Hmkr) .
  t_auto_newer .
Qed.

Lemma mk_env_bexp_newer_res_saddo :
  forall (e1 e2 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_saddo_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_saddo_newer_res Hmkr) .
Qed.

Lemma mk_env_bexp_newer_res_ssubo :
  forall (e1 e2 : QFBV.exp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 e2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1 .
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2 .
  move: (mk_env_ssubo_newer_gen Hmkr) => Hg2gr .
  apply : (mk_env_ssubo_newer_res Hmkr) .
Qed.

Lemma mk_env_bexp_newer_res_smulo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator)
            (cs : cnf) (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        newer_than_lits g' lrs) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator)
              (cs : cnf) (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          newer_than_lits g' lrs) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- _ <- Hgm Hgt.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt) => Hg1l1.
  (* newer_than_lits g2 ls2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t) => Hg2l2.
  (* newer_than_lits g2 ls1 *)
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  (* now mk_env_smulo_newer_res is available *)
  exact: (mk_env_smulo_newer_res Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_newer_res_lneg :
  forall (b : QFBV.bexp) (m : vm) (s : SSAStore.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Blneg b) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  exact: newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_bexp_newer_res_conj :
  forall (b b0 : QFBV.bexp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bconj b b0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  exact: newer_than_lit_add_diag_r.
Qed.

Lemma mk_env_bexp_newer_res_disj :
  forall (b b0 : QFBV.bexp) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lr : literal),
    mk_env_bexp m s E g (QFBV.Bdisj b b0) = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lit g' lr.
Proof.
  rewrite/=; intros; dcase_hyps; subst.
  exact: newer_than_lit_add_diag_r.
Qed.

Corollary mk_env_exp_newer_res :
  forall (e : QFBV.exp) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> newer_than_lit g lit_tt -> newer_than_lits g' lrs
  with
    mk_env_bexp_newer_res :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        newer_than_lit g' lr.
Proof.
  (* mk_env_exp_newer_res *)
  elim .
  - exact : mk_env_exp_newer_res_var .
  - exact : mk_env_exp_newer_res_const .
  - elim .
    + exact : mk_env_exp_newer_res_not .
    + exact : mk_env_exp_newer_res_neg .
    + exact : mk_env_exp_newer_res_extract .
    + exact : mk_env_exp_newer_res_high .
    + exact : mk_env_exp_newer_res_low .
    + exact : mk_env_exp_newer_res_zeroextend .
    + exact : mk_env_exp_newer_res_signextend .
  - elim .
    + exact : mk_env_exp_newer_res_and .
    + exact : mk_env_exp_newer_res_or .
    + exact : mk_env_exp_newer_res_xor .
    + exact : mk_env_exp_newer_res_add .
    + exact : mk_env_exp_newer_res_sub .
    + exact : mk_env_exp_newer_res_mul .
    + exact : mk_env_exp_newer_res_mod .
    + exact : mk_env_exp_newer_res_srem .
    + exact : mk_env_exp_newer_res_smod .
    + exact : mk_env_exp_newer_res_shl .
    + exact : mk_env_exp_newer_res_lshr .
    + exact : mk_env_exp_newer_res_ashr .
    + exact : mk_env_exp_newer_res_concat .
  - move => b e0 _ e1 _;
    move: b e0 e1; exact : mk_env_exp_newer_res_ite .
  (* mk_env_bexp_newer_res *)
  elim .
  - exact : mk_env_bexp_newer_res_false .
  - exact : mk_env_bexp_newer_res_true .
  - elim .
    + exact : mk_env_bexp_newer_res_eq .
    + exact : mk_env_bexp_newer_res_ult .
    + exact : mk_env_bexp_newer_res_ule .
    + exact : mk_env_bexp_newer_res_ugt .
    + exact : mk_env_bexp_newer_res_uge .
    + exact : mk_env_bexp_newer_res_slt .
    + exact : mk_env_bexp_newer_res_sle .
    + exact : mk_env_bexp_newer_res_sgt .
    + exact : mk_env_bexp_newer_res_sge .
    + exact : mk_env_bexp_newer_res_uaddo .
    + exact : mk_env_bexp_newer_res_usubo .
    + exact : mk_env_bexp_newer_res_umulo .
    + exact : mk_env_bexp_newer_res_saddo .
    + exact : mk_env_bexp_newer_res_ssubo .
    + move => e e0;
        move : e (mk_env_exp_newer_res e)
               e0 (mk_env_exp_newer_res e0);
        exact : mk_env_bexp_newer_res_smulo .
  - move => b _; exact : mk_env_bexp_newer_res_lneg .
  - move => b0 _ b1 _; exact : mk_env_bexp_newer_res_conj .
  - move => b0 _ b1 _; exact : mk_env_bexp_newer_res_disj .
Qed.



(* = mk_env_exp_newer_cnf and mk_env_bexp_newer_cnf = *)

Lemma mk_env_exp_newer_cnf_var :
  forall t (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Evar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Evar t) te ->
    newer_than_cnf g' cs.
Proof.
  move=> v te m s E g m' E' g' cs lrs /=. case: (SSAVM.find v m).
  - move=> lxs [] _ _ <- <- _ Hnew_gm Hnew_gtt _. done.
  - case Henv: (mk_env_var E g (SSAStore.acc v s) v)=> [[[Ev gv] csv] lrsv].
    case=> _ _ <- <- _ Hnew_gm Hnew_gtt _. exact: (mk_env_var_newer_cnf Henv).
Qed.

Lemma mk_env_exp_newer_cnf_const :
  forall (b : bits) (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Econst b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Econst b) te ->
    newer_than_cnf g' cs.
Proof.
  move=> bs te m s E g m' E' g' cs lrs /=. case=> _ _ <- <- _ Hnew_gm Hnew_gtt _. done.
Qed.

Lemma mk_env_exp_newer_cnf_not :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop QFBV.Unot e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop QFBV.Unot e1) te ->
      newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt Hwf.
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) => Hg1c1.
  move: (mk_env_not_newer_gen Hmkr) => Hg1gr.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1gr) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  exact: (mk_env_not_newer_cnf Hmkr Hg1l1).
Qed.

Lemma mk_env_exp_newer_cnf_and :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Band e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Band e1 e2) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] _] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_and_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  exact: (mk_env_and_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_newer_cnf_or :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bor e0 e1) te ->
    newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_or E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] _] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_or_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  exact: (mk_env_or_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_newer_cnf_xor :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bxor e1 e2) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] _] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_xor_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  exact: (mk_env_xor_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_newer_cnf_neg :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop QFBV.Uneg e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop QFBV.Uneg e1) te ->
      newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt Hwf .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) => Hg1c1.
  move: (mk_env_neg_newer_gen Hmkr) => Hg1gr.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1gr) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  exact : (mk_env_neg_newer_cnf Hmkr (newer_than_lit_le_newer Hgt (mk_env_exp_newer_gen Hmke1)) Hg1l1).
Qed.

Lemma mk_env_exp_newer_cnf_add :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Badd e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Badd e e0) te ->
    newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_add E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_add_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2f.
  rewrite newer_than_lit_tt_ff in Hg2f .
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply : (mk_env_add_newer_cnf Hmkr Hg2l1 Hg2l2 Hg2f).
Qed.

Lemma mk_env_exp_newer_cnf_sub :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsub e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsub e e0) te ->
    newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sub E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_sub_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2f.
  rewrite newer_than_lit_tt_ff in Hg2f .
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply : (mk_env_sub_newer_cnf Hmkr Hg2f Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_newer_cnf_mul :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmul e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsub e e0) te ->
    newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_mul E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_mul_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply : (mk_env_mul_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_newer_cnf_mod :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        newer_than_cnf g' cs) ->
  forall (e0 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e0 te ->
        newer_than_cnf g' cs) ->
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bmod e e0) te ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_srem :
  forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
  forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsrem e e0) te ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_smod :
  forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
  forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsmod e e0) te ->
    newer_than_cnf g' cs.
Proof.
Admitted.

Lemma mk_env_exp_newer_cnf_shl :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bshl e0 e1) te ->
      newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_shl E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_shl_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply : (mk_env_shl_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed .

Lemma mk_env_exp_newer_cnf_lshr :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Blshr e0 e1) te ->
      newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_lshr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_lshr_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply : (mk_env_lshr_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed .

Lemma mk_env_exp_newer_cnf_ashr :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bashr e0 e1) te ->
      newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ashr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_ashr_newer_gen Hmkr) => Hg2gr.
  move: (newer_than_cnf_le_newer Hg1c1 (pos_leb_trans Hg1g2 Hg2gr)) => Hgrc1.
  rewrite Hgrc1 /=.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2gr) => Hgrc2.
  rewrite Hgrc2 /=.
  (* newer_than_cnf gr csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply : (mk_env_ashr_newer_cnf Hmkr Hg2t Hg2l1 Hg2l2).
Qed .

Lemma mk_env_exp_newer_cnf_concat :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bconcat e0 e1) te ->
      newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => Hg2c1.
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite Hg2c1 Hg2c2 // .
Qed .

Lemma mk_env_exp_newer_cnf_extract :
  forall (i j : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uextr i j) e) te ->
      newer_than_cnf g' cs.
Proof.
  move=> i j e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- <- _ Hgm Hgt Hwf .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

(*
Lemma mk_env_exp_newer_cnf_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV.exp (w3 + w2 + w1)),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          newer_than_cnf g' cs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      newer_than_cnf g' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !newer_than_cnf_append.
  move: (mk_env_exp_newer_gen H0) => Hgg0 .
  (* newer_than_cnf g' cs0 *)
  by rewrite (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .
*)

Lemma mk_env_exp_newer_cnf_high :
    forall (n : nat) (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm)
           (s : SSAStore.t) (E : env) (g : generator) (m' : vm)
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uhigh n) e) te ->
      newer_than_cnf g' cs.
Proof.
  move=> n e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- <- _ Hgm Hgt Hwf .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

Lemma mk_env_exp_newer_cnf_low :
    forall (n : nat) (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Ulow n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Ulow n) e) te ->
      newer_than_cnf g' cs.
Proof.
  move=> n e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- <- _ Hgm Hgt Hwf .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

Lemma mk_env_exp_newer_cnf_zeroextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop (QFBV.Uzext n) e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uzext n) e) te ->
    newer_than_cnf g' cs.
Proof.
  move=> n e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- <- _ Hgm Hgt Hwf .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

Lemma mk_env_exp_newer_cnf_signextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Usext n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Usext n) e) te ->
      newer_than_cnf g' cs.
Proof.
  move=> n e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ _ <- <- _ Hgm Hgt Hwf .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

Lemma mk_env_exp_newer_cnf_ite :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt -> 
        QFBV.well_formed_bexp b te ->
        newer_than_cnf g' cs) ->
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          newer_than_cnf g' cs) ->
      forall (e0 : QFBV.exp),
        (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : word),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
            newer_than_vm g m ->
            newer_than_lit g lit_tt ->
            QFBV.well_formed_exp e0 te ->
            newer_than_cnf g' cs) ->
        forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp m s E g (QFBV.Eite b e e0) = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp (QFBV.Eite b e e0) te ->
          newer_than_cnf g' cs.
Proof.
  move=> c IHc e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmkc : (mk_env_bexp m s E g c) => [[[[mc Ec] gc] csc] lsc].
  case Hmke1 : (mk_env_exp mc s Ec gc e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ite E2 g2 lsc ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ _ <- <- _ Hgm Hgt /= /andP [/andP [/andP [Hwfc Hwf1] Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf gr csc *)
  move: (IHc _ _ _ _ _ _ _ _ _ _ Hmkc Hgm Hgt Hwfc) => Hgccc.
  move: (mk_env_bexp_newer_gen Hmkc) => Hggc.
  move: (mk_env_exp_newer_gen Hmke1) => Hgcg1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_ite_newer_gen Hmkr) => Hg2gr.
  move: (pos_leb_trans Hgcg1 Hg1g2) => Hgcg2 .
  move: (pos_leb_trans Hg1g2 Hg2gr) => Hg1gr .
  move: (pos_leb_trans Hgcg1 Hg1gr) => Hgcgr .
  move: (mk_env_bexp_newer_res Hmkc Hgm Hgt) => Hgclsc .
  move: (newer_than_lit_le_newer Hgclsc Hgcg2) => Hg2lsc {Hgclsc}.
  rewrite (newer_than_cnf_le_newer Hgccc Hgcgr) /= {Hgcgr}.
  (* newer_than_cnf gr cs1 *)
  move: (mk_env_bexp_newer_vm Hmkc Hgm) => Hg1m1.
  move: (newer_than_lit_le_newer Hgt Hggc) => Hgct.
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hg1m1 Hgct Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_res Hmke1 Hg1m1 Hgct) => Hg1l1 .
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1 {Hg1l1} .
  rewrite (newer_than_cnf_le_newer Hg1c1 Hg1gr) /= {Hg1gr} .
  (* newer_than_cnf gr cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hg1m1) => Hg2m2.
  move: (newer_than_lit_le_newer Hgct Hgcg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg2m2 Hg1t Hwf2) => Hg2c2.
  move: (mk_env_exp_newer_res Hmke2 Hg2m2 Hg1t) => Hg2l2 .
  rewrite (newer_than_cnf_le_newer Hg2c2 Hg2gr) /= .
  (* newer_than_cnf gr csr *)
  apply: (mk_env_ite_newer_cnf Hmkr (newer_than_lit_le_newer Hg1t Hg1g2) Hg2lsc Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_newer_cnf_false :
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Bfalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt ->
    QFBV.well_formed_bexp QFBV.Bfalse te ->
    newer_than_cnf g' cs.
Proof.
  move=> te m s E g m' E' g' cs lr /=. case=> _ _ <- <- _ Hnew_gm Hnew_gtt _. done.
Qed.

Lemma mk_env_bexp_newer_cnf_true :
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Btrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt ->
    QFBV.well_formed_bexp QFBV.Btrue te ->
    newer_than_cnf g' cs.
Proof.
  move=> te m s E g m' E' g' cs lr /=. case=> _ _ <- <- _ Hnew_gm Hnew_gtt _. done.
Qed.

Lemma mk_env_bexp_newer_cnf_eq :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Beq e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Beq e e0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_eq E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_eq_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_eq_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_ult :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bult e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bult e e0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_ult E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_ult_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_ult_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_ule :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bule e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bule e e0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_ule E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_ule_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_ule_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_ugt :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bugt e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bugt e e0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_ugt E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_ugt_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_ugt_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_uge :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buge e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Buge e e0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_uge E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_uge_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_uge_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_slt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bslt e1 e2) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_slt E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_slt_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_slt_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_sle :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsle e1 e2) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_sle E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_sle_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_sle_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_sgt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsgt e1 e2) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_sgt E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_sgt_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_sgt_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_sge :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsge e1 e2) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_sge E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_sge_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_sge_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_uaddo :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Buaddo e e0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_uaddo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_uaddo_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply : (mk_env_uaddo_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_usubo :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Busubo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Busubo e e0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_usubo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_usubo_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply: (mk_env_usubo_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_umulo :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        newer_than_cnf g' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bumulo e e0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_umulo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_umulo_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply : (mk_env_umulo_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_saddo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsaddo e1 e2) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_saddo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_saddo_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply : (mk_env_saddo_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_ssubo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bssubo e1 e2) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_ssubo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_ssubo_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply : (mk_env_ssubo_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_smulo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        newer_than_cnf g' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsmulo e1 e2) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmr: (mk_env_smulo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> _ _ <- <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize] .
  rewrite !newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) => Hg1c1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (newer_than_cnf_le_newer Hg1c1 Hg1g2) => {Hg1c1} Hg2c1.
  move: (mk_env_smulo_newer_gen Hmr) => Hg2og.
  move: (newer_than_cnf_le_newer Hg2c1 Hg2og) => {Hg2c1} Hogc1.
  rewrite Hogc1 /= .
  (* newer_than_cnf og cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2c2.
  move: (newer_than_cnf_le_newer Hg2c2 Hg2og) => {Hg2c2} Hogc2.
  rewrite Hogc2 /= .
  (* newer_than_cnf og ocs *)
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1l1.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => {Hg1l1} Hg2l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2l2.
  apply : (mk_env_smulo_newer_cnf Hmr Hg2tt Hg2l1 Hg2l2).
Qed.

Lemma mk_env_bexp_newer_cnf_lneg :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp b te ->
        newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Blneg b) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Blneg b) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e IH te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv: (mk_env_bexp m s E g e) => [[[[m1 E1] g1] cs1] lr1].
  case Hlneg: (mk_env_lneg E1 g1 lr1) => [[[oE og] ocs] olr].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt Hwf. rewrite newer_than_cnf_cat .
  (* newer_than_cnf og cs1 *)
  move: (IH _ _ _ _ _ _ _ _ _ _ Henv Hnew_gm Hnew_gtt Hwf) => Hnew_g1cs1.
  move: (mk_env_lneg_newer_gen Hlneg) => H_g1og.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1og). move => {Hnew_g1cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_bexp_newer_res Henv Hnew_gm Hnew_gtt) => Hnew_g1lr1.
  exact: (mk_env_lneg_newer_cnf Hlneg Hnew_g1lr1).
Qed.


Lemma mk_env_bexp_newer_cnf_conj :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp b te ->
        newer_than_cnf g' cs) ->
    forall (b0 : QFBV.bexp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_bexp b0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bconj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bconj b b0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case Hconj: (mk_env_conj E2 g2 lr1 lr2)=> [[[oE og] ocs] olr].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt /= /andP [Hwf1 Hwf2]. rewrite !newer_than_cnf_cat.
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt Hwf1) => Hnew_g1cs1.
  move: (mk_env_bexp_newer_gen Henv2) => H_g1g2.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => {Hnew_g1cs1} Hnew_g2cs1.
  move: (mk_env_conj_newer_gen Hconj) => H_g2og.
  move: (newer_than_cnf_le_newer Hnew_g2cs1 H_g2og) => {Hnew_g2cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og cs2 *)
  move: (mk_env_bexp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (mk_env_bexp_newer_gen Henv1) => H_gg1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt Hwf2) => Hnew_g2cs2.
  move: (newer_than_cnf_le_newer Hnew_g2cs2 H_g2og) => {Hnew_g2cs2} Hnew_ogcs2.
  rewrite Hnew_ogcs2 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_bexp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1lr1.
  move: (newer_than_lit_le_newer Hnew_g1lr1 H_g1g2) => {Hnew_g1lr1} Hnew_g2lr1.
  move: (mk_env_bexp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2lr2.
  exact: (mk_env_conj_newer_cnf Hconj Hnew_g2lr1 Hnew_g2lr2).
Qed.

Lemma mk_env_bexp_newer_cnf_disj :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp b te ->
        newer_than_cnf g' cs) ->
    forall (b0 : QFBV.bexp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_bexp b0 te ->
          newer_than_cnf g' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bdisj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bdisj b b0) te ->
        newer_than_cnf g' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case Hdisj: (mk_env_disj E2 g2 lr1 lr2)=> [[[oE og] ocs] olr].
  case=> _ _ <- <- _ Hnew_gm Hnew_gtt /= /andP [Hwf1 Hwf2]. rewrite !newer_than_cnf_cat.
  (* newer_than_cnf og cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Henv1 Hnew_gm Hnew_gtt Hwf1) => Hnew_g1cs1.
  move: (mk_env_bexp_newer_gen Henv2) => H_g1g2.
  move: (newer_than_cnf_le_newer Hnew_g1cs1 H_g1g2) => {Hnew_g1cs1} Hnew_g2cs1.
  move: (mk_env_disj_newer_gen Hdisj) => H_g2og.
  move: (newer_than_cnf_le_newer Hnew_g2cs1 H_g2og) => {Hnew_g2cs1} Hnew_ogcs1.
  rewrite Hnew_ogcs1 andTb.
  (* newer_than_cnf og cs2 *)
  move: (mk_env_bexp_newer_vm Henv1 Hnew_gm) => Hnew_g1m1.
  move: (mk_env_bexp_newer_gen Henv1) => H_gg1.
  move: (newer_than_lit_le_newer Hnew_gtt H_gg1) => Hnew_g1tt.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Henv2 Hnew_g1m1 Hnew_g1tt Hwf2) => Hnew_g2cs2.
  move: (newer_than_cnf_le_newer Hnew_g2cs2 H_g2og) => {Hnew_g2cs2} Hnew_ogcs2.
  rewrite Hnew_ogcs2 andTb.
  (* newer_than_cnf og ocs *)
  move: (mk_env_bexp_newer_res Henv1 Hnew_gm Hnew_gtt) => Hnew_g1lr1.
  move: (newer_than_lit_le_newer Hnew_g1lr1 H_g1g2) => {Hnew_g1lr1} Hnew_g2lr1.
  move: (mk_env_bexp_newer_res Henv2 Hnew_g1m1 Hnew_g1tt) => Hnew_g2lr2.
  exact: (mk_env_disj_newer_cnf Hdisj Hnew_g2lr1 Hnew_g2lr2).
Qed.

Corollary mk_env_exp_newer_cnf :
  forall (e : QFBV.exp) te m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp e te ->
    newer_than_cnf g' cs
  with
    mk_env_bexp_newer_cnf :
      forall e te m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp e te ->
        newer_than_cnf g' cs.
Proof.
  (* mk_env_exp_newer_cnf *)
  elim .
  - exact: mk_env_exp_newer_cnf_var .
  - exact: mk_env_exp_newer_cnf_const .
  - elim .
    + exact: mk_env_exp_newer_cnf_not .
    + exact: mk_env_exp_newer_cnf_neg .
    + exact: mk_env_exp_newer_cnf_extract .
    + exact: mk_env_exp_newer_cnf_high .
    + exact: mk_env_exp_newer_cnf_low .
    + exact: mk_env_exp_newer_cnf_zeroextend .
    + exact: mk_env_exp_newer_cnf_signextend .
  - elim .
    + exact: mk_env_exp_newer_cnf_and .
    + exact: mk_env_exp_newer_cnf_or .
    + exact: mk_env_exp_newer_cnf_xor .
    + exact: mk_env_exp_newer_cnf_add .
    + exact: mk_env_exp_newer_cnf_sub .
    + exact: mk_env_exp_newer_cnf_mul .
    + exact: mk_env_exp_newer_cnf_mod .
    + exact: mk_env_exp_newer_cnf_srem .
    + exact: mk_env_exp_newer_cnf_smod .
    + exact: mk_env_exp_newer_cnf_shl .
    + exact: mk_env_exp_newer_cnf_lshr .
    + exact: mk_env_exp_newer_cnf_ashr .
    + exact: mk_env_exp_newer_cnf_concat .
  - move => b;
      move : b (mk_env_bexp_newer_cnf b);
      exact: mk_env_exp_newer_cnf_ite .
  (* mk_env_bexp_newer_cnf *)
  elim .
  - exact: mk_env_bexp_newer_cnf_false .
  - exact: mk_env_bexp_newer_cnf_true .
  - elim; move => e0 e1;
          move : e0 (mk_env_exp_newer_cnf e0)
                 e1 (mk_env_exp_newer_cnf e1) .
    + exact: mk_env_bexp_newer_cnf_eq .
    + exact: mk_env_bexp_newer_cnf_ult .
    + exact: mk_env_bexp_newer_cnf_ule .
    + exact: mk_env_bexp_newer_cnf_ugt .
    + exact: mk_env_bexp_newer_cnf_uge .
    + exact: mk_env_bexp_newer_cnf_slt .
    + exact: mk_env_bexp_newer_cnf_sle .
    + exact: mk_env_bexp_newer_cnf_sgt .
    + exact: mk_env_bexp_newer_cnf_sge .
    + exact: mk_env_bexp_newer_cnf_uaddo .
    + exact: mk_env_bexp_newer_cnf_usubo .
    + exact: mk_env_bexp_newer_cnf_umulo .
    + exact: mk_env_bexp_newer_cnf_saddo .
    + exact: mk_env_bexp_newer_cnf_ssubo .
    + exact: mk_env_bexp_newer_cnf_smulo .
  - exact: mk_env_bexp_newer_cnf_lneg .
  - exact: mk_env_bexp_newer_cnf_conj .
  - exact: mk_env_bexp_newer_cnf_disj .
Qed.

(* = mk_env_exp_consistent and mk_env_bexp_consistent = *)

Lemma mk_env_exp_consistent_var :
  forall t (m : vm) (s : SSAStore.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Evar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case Hfind: (SSAVM.find v m).
  - case=> <- <- _ _ _ Hnew_gm Hcon. assumption.
  - case Henv: (mk_env_var E g (SSAStore.acc v s) v) => [[[E_v g_v] cs_v] lrs_v].
    case=> <- <- _ _ _ Hnew_gm Hcon. move=> x. rewrite /consistent1.
    case Hxv: (x == v).
    + rewrite (SSAVM.Lemmas.find_add_eq Hxv). rewrite (eqP Hxv).
      exact: (mk_env_var_enc Henv).
    + move/negP: Hxv => Hxv. rewrite (SSAVM.Lemmas.find_add_neq Hxv).
      move: (Hcon x). rewrite /consistent1.
      case Hfind_xm: (SSAVM.find x m); last done .
      move=> Henc. move: (Hnew_gm x _ Hfind_xm) => Hnew.
      exact: (env_preserve_enc_bits (mk_env_var_preserve Henv) Hnew Henc).
Qed.

Lemma mk_env_exp_consistent_const :
  forall (b : bits) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Econst b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> bs m s E g m' E' g' cs lrs /=. case=> <- <- _ _ _ Hnew_gm Hcon.
  assumption.
Qed.

Lemma mk_env_exp_consistent_not :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop QFBV.Unot e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_not_preserve Hmkr) => HpE1Er.
  exact: (env_preserve_consistent Hg1m1 HpE1Er Hcm1E1).
Qed.

Lemma mk_env_exp_consistent_and :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Band e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_and_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_exp_consistent_or :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_or E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_or_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed .

Lemma mk_env_exp_consistent_xor :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_xor_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_exp_consistent_neg :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop QFBV.Uneg e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_neg_preserve Hmkr) => HpE1Er.
  exact: (env_preserve_consistent Hg1m1 HpE1Er Hcm1E1).
Qed.

Lemma mk_env_exp_consistent_add :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Badd e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_add E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_add_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_exp_consistent_sub :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsub e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sub E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_sub_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_exp_consistent_mul :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmul e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_mul E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_mul_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_exp_consistent_mod :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_srem :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_smod :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
Admitted.

Lemma mk_env_exp_consistent_shl :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_shl E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_shl_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed .

Lemma mk_env_exp_consistent_lshr :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_lshr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_lshr_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed .

Lemma mk_env_exp_consistent_ashr :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ashr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_ashr_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed .

Lemma mk_env_exp_consistent_concat :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_concat E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  exact: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1).
Qed .

Lemma mk_env_exp_consistent_extract :
  forall (i j : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> i j e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- <- _ _ _ Hgm HcmE.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) .
Qed .

(*
Lemma mk_env_exp_consistent_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV.exp (w3 + w2 + w1)),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .
*)

Lemma mk_env_exp_consistent_high :
    forall (n : nat) (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm)
           (s : SSAStore.t) (E : env) (g : generator) (m' : vm)
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- <- _ _ _ Hgm HcmE.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) .
Qed .

Lemma mk_env_exp_consistent_low :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Ulow n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- <- _ _ _ Hgm HcmE.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) .
Qed .

Lemma mk_env_exp_consistent_zeroextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop (QFBV.Uzext n) e) = (m', E', g', cs, lrs) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- <- _ _ _ Hgm HcmE.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) .
Qed .

Lemma mk_env_exp_consistent_signextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Usext n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> <- <- _ _ _ Hgm HcmE.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) .
Qed .

Lemma mk_env_exp_consistent_ite :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (e0 : QFBV.exp),
        (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : word),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
            newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
        forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp m s E g (QFBV.Eite b e e0) = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> c IHc e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmkc : (mk_env_bexp m s E g c) => [[[[mc Ec] gc] csc] lsc].
  case Hmke1 : (mk_env_exp mc s Ec gc e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ite E2 g2 lsc ls1 ls2) => [[[Er gr] csr] lsr].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IHc _ _ _ _ _ _ _ _ _ Hmkc Hgm HcmE) => HcmcEc.
  move: (mk_env_bexp_newer_vm Hmkc Hgm) => Hgcmc.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgcmc HcmcEc) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgcmc) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_ite_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_false :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Bfalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> <- <- _ _ _. move=> _ H; exact: H.
Qed.

Lemma mk_env_bexp_consistent_true :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Btrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> <- <- _ _ _. move=> _ H; exact: H.
Qed.

Lemma mk_env_bexp_consistent_eq :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Beq e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_eq_preserve Heq)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_ult :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bult e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hult: (mk_env_ult E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_ult_preserve Hult)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_ule :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bule e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hule: (mk_env_ule E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_ule_preserve Hule)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_ugt :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bugt e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hugt: (mk_env_ugt E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_ugt_preserve Hugt)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_uge :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buge e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Huge: (mk_env_uge E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_uge_preserve Huge)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_slt :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_slt_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_sle :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_sle_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_sgt :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_sgt_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_sge :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_sge_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_uaddo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Huaddo: (mk_env_uaddo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_uaddo_preserve Huaddo)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_usubo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Busubo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Husubo: (mk_env_usubo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_usubo_preserve Husubo)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_umulo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_exp.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Humulo: (mk_env_umulo E2 g2 ls1 ls2)=> [[[oE og] ocs] or].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_exp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_exp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_umulo_preserve Humulo)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  exact: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew).
Qed.

Lemma mk_env_bexp_consistent_saddo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_saddo_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_ssubo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_ssubo_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_smulo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> <- <- _ _ _ Hgm HcmE.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1 Hgm HcmE) => Hcm1E1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hcm1E1) => Hcm2E2.
  move: (mk_env_smulo_preserve Hmkr) => HpE2Er.
  move: (mk_env_exp_newer_vm Hmke2 Hg1m1) => Hg2m2.
  exact: (env_preserve_consistent Hg2m2 HpE2Er Hcm2E2).
Qed.

Lemma mk_env_bexp_consistent_lneg :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Blneg b) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e IH m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv: (mk_env_bexp m s E g e)=> [[[[m1 E1] g1] cs1] lr1].
  case Hlneg: (mk_env_lneg E1 g1 lr1)=> [[[oE og] ocs] olr].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_bexp_newer_vm Henv Hnew) => Hnew1.
  apply: (env_preserve_consistent Hnew1 (mk_env_lneg_preserve Hlneg)).
  apply: (IH _ _ _ _ _ _ _ _ _ Henv Hnew). exact: Hcon.
Qed.

Lemma mk_env_bexp_consistent_conj :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (b0 : QFBV.bexp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bconj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case Hconj: (mk_env_conj E2 g2 lr1 lr2)=> [[[oE og] ocs] olr].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_bexp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_bexp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_conj_preserve Hconj)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  apply: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew). exact: Hcon.
Qed.

Lemma mk_env_bexp_consistent_disj :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
    forall (b0 : QFBV.bexp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> consistent m E s -> consistent m' E' s) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bdisj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> consistent m E s -> consistent m' E' s.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1)=> [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2)=> [[[[m2 E2] g2] cs2] lr2].
  case Hdisj: (mk_env_disj E2 g2 lr1 lr2)=> [[[oE og] ocs] olr].
  case=> <- <- _ _ _ Hnew Hcon.
  move: (mk_env_bexp_newer_vm Henv1 Hnew) => Hnew1.
  move: (mk_env_bexp_newer_vm Henv2 Hnew1) => Hnew2.
  apply: (env_preserve_consistent Hnew2 (mk_env_disj_preserve Hdisj)).
  apply: (IH2 _ _ _ _ _ _ _ _ _ Henv2 Hnew1).
  apply: (IH1 _ _ _ _ _ _ _ _ _ Henv1 Hnew). exact: Hcon.
Qed.

Corollary mk_env_exp_consistent :
  forall (e : QFBV.exp) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    consistent m E s -> consistent m' E' s
  with
    mk_env_bexp_consistent :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        consistent m E s ->
        consistent m' E' s.
Proof.
  (* mk_env_exp_consistent *)
  elim .
  - exact: mk_env_exp_consistent_var .
  - exact: mk_env_exp_consistent_const .
  - elim .
    + exact: mk_env_exp_consistent_not .
    + exact: mk_env_exp_consistent_neg .
    + exact: mk_env_exp_consistent_extract .
    + exact: mk_env_exp_consistent_high .
    + exact: mk_env_exp_consistent_low .
    + exact: mk_env_exp_consistent_zeroextend .
    + exact: mk_env_exp_consistent_signextend .
  - elim .
    + exact: mk_env_exp_consistent_and .
    + exact: mk_env_exp_consistent_or .
    + exact: mk_env_exp_consistent_xor .
    + exact: mk_env_exp_consistent_add .
    + exact: mk_env_exp_consistent_sub .
    + exact: mk_env_exp_consistent_mul .
    + exact: mk_env_exp_consistent_mod .
    + exact: mk_env_exp_consistent_srem .
    + exact: mk_env_exp_consistent_smod .
    + exact: mk_env_exp_consistent_shl .
    + exact: mk_env_exp_consistent_lshr .
    + exact: mk_env_exp_consistent_ashr .
    + exact: mk_env_exp_consistent_concat .
  - move => b;
      move : b (mk_env_bexp_consistent b);
      exact: mk_env_exp_consistent_ite .
  (* mk_env_bexp_consistent *)
  elim .
  - exact: mk_env_bexp_consistent_false .
  - exact: mk_env_bexp_consistent_true .
  - elim;
      move => e0 e1;
      move : e0 (mk_env_exp_consistent e0)
             e1 (mk_env_exp_consistent e1) .
    + exact: mk_env_bexp_consistent_eq .
    + exact: mk_env_bexp_consistent_ult .
    + exact: mk_env_bexp_consistent_ule .
    + exact: mk_env_bexp_consistent_ugt .
    + exact: mk_env_bexp_consistent_uge .
    + exact: mk_env_bexp_consistent_slt .
    + exact: mk_env_bexp_consistent_sle .
    + exact: mk_env_bexp_consistent_sgt .
    + exact: mk_env_bexp_consistent_sge .
    + exact: mk_env_bexp_consistent_uaddo .
    + exact: mk_env_bexp_consistent_usubo .
    + exact: mk_env_bexp_consistent_umulo .
    + exact: mk_env_bexp_consistent_saddo .
    + exact: mk_env_bexp_consistent_ssubo .
    + exact: mk_env_bexp_consistent_smulo .
  - exact: mk_env_bexp_consistent_lneg .
  - exact: mk_env_bexp_consistent_conj .
  - exact: mk_env_bexp_consistent_disj .
Qed.



(* = mk_env_exp_preserve and mk_env_bexp_preserve = *)

Lemma mk_env_exp_preserve_var :
  forall t (m : vm) (s : SSAStore.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Evar t) = (m', E', g', cs, lrs) -> env_preserve E E' g.
Proof.
  move=> v m s E g m' E' g' cs lrs /=. case Hfind: (SSAVM.find v m).
  - case=> _ <- _ _ _. exact: env_preserve_refl.
  - case Henv: (mk_env_var E g (SSAStore.acc v s) v) => [[[E_v g_v] cs_v] lrs_v].
    case=> _ <- _ _ _. exact: (mk_env_var_preserve Henv).
Qed.

Lemma mk_env_exp_preserve_const :
  forall (b : bits) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Econst b) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> bs m s E g m' E' g' cs lrs /=. case=> _ <- _ _ _. exact: env_preserve_refl.
Qed.

Lemma mk_env_exp_preserve_not :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop QFBV.Unot e1) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (mk_env_not_preserve Hmkr) => HpE1Erg1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (env_preserve_le HpE1Erg1 Hgg1) => HpE1Erg.
  exact: (env_preserve_trans HpEE1g HpE1Erg).
Qed.

Lemma mk_env_exp_preserve_and :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Band e1 e2) = (m', E', g', cs, lrs) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_and_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_exp_preserve_or :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_or E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_or_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed .

Lemma mk_env_exp_preserve_xor :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', E', g', cs, lrs) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_xor_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_exp_preserve_neg :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop QFBV.Uneg e1) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (mk_env_neg_preserve Hmkr) => HpE1Erg1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (env_preserve_le HpE1Erg1 Hgg1) => HpE1Erg.
  exact: (env_preserve_trans HpEE1g HpE1Erg).
Qed.

Lemma mk_env_exp_preserve_add :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Badd e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_add E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_add_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_exp_preserve_sub :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsub e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sub E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_sub_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_exp_preserve_mul :
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmul e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_mul E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_mul_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_exp_preserve_mod :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmod e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_srem :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_smod :
  forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
  forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
  forall (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
Admitted.

Lemma mk_env_exp_preserve_shl :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_shl E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_shl_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed .

Lemma mk_env_exp_preserve_lshr :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_lshr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_lshr_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed .

Lemma mk_env_exp_preserve_ashr :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ashr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_ashr_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed .

Lemma mk_env_exp_preserve_concat :
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e1 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  exact: (env_preserve_trans _ HpE1E2g).
Qed .

Lemma mk_env_exp_preserve_extract :
  forall (i j : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> i j e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ _ _.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
Qed .

(*
Lemma mk_env_exp_preserve_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV.exp (w3 + w2 + w1)),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  rewrite /=; intros; dcase_hyps; subst.
  apply: (H _ _ _ _ _ _ _ _ _ H0) .
Qed .
*)

Lemma mk_env_exp_preserve_high :
    forall (n : nat) (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm)
           (s : SSAStore.t) (E : env) (g : generator) (m' : vm)
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ _ _.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) .
Qed .

Lemma mk_env_exp_preserve_low :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Ulow n) e) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ _ _.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) .
Qed .

Lemma mk_env_exp_preserve_zeroextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uzext n) e) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ _ _.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
Qed .

Lemma mk_env_exp_preserve_signextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Usext n) e) = (m', E', g', cs, lrs) ->
      env_preserve E E' g.
Proof.
  move=> n e1 IH1 m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ _ _.
  exact: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) .
Qed .

Lemma mk_env_exp_preserve_ite :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        env_preserve E E' g) ->
    forall (e : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (e0 : QFBV.exp),
        (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : word),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
        forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp m s E g (QFBV.Eite b e e0) = (m', E', g', cs, lrs) ->
          env_preserve E E' g.
Proof.
  move=> c IHc e1 IH1 e2 IH2 m s E g m' E' g' cs lrs /=.
  case Hmkc : (mk_env_bexp m s E g c) => [[[[mc Ec] gc] csc] lsc].
  case Hmke1 : (mk_env_exp mc s Ec gc e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ite E2 g2 lsc ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ _ _.
  move: (IHc _ _ _ _ _ _ _ _ _ Hmkc) => HpEEcg.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEcE1gc.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_ite_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_bexp_newer_gen Hmkc) (mk_env_exp_newer_gen Hmke1)
        (mk_env_exp_newer_gen Hmke2) => Hggc Hgcg1 Hg1g2.
  move: (env_preserve_le HpEcE1gc Hggc) => HpEcE1g.
  move: (env_preserve_le HpE1E2g1 (pos_leb_trans Hggc Hgcg1)) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2
                         (pos_leb_trans Hggc (pos_leb_trans Hgcg1 Hg1g2))) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  apply: (env_preserve_trans _ HpE1E2g).
  exact: (env_preserve_trans _ HpEcE1g) .
Qed.

Lemma mk_env_bexp_preserve_false :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Bfalse = (m', E', g', cs, lr) -> env_preserve E E' g.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ <- _ _ _. exact: env_preserve_refl.
Qed.

Lemma mk_env_bexp_preserve_true :
  forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Btrue = (m', E', g', cs, lr) -> env_preserve E E' g.
Proof.
  move=> m s E g m' E' g' cs lr /=. case=> _ <- _ _ _. exact: env_preserve_refl.
Qed.

Lemma mk_env_bexp_preserve_eq :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Beq e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Heq: (mk_env_eq E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv2)).
  exact: (mk_env_eq_preserve Heq).
Qed.

Lemma mk_env_bexp_preserve_ult :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bult e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hult: (mk_env_ult E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv2)).
  exact: (mk_env_ult_preserve Hult).
Qed.

Lemma mk_env_bexp_preserve_ule :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bule e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hule: (mk_env_ule E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv2)).
  exact: (mk_env_ule_preserve Hule).
Qed.

Lemma mk_env_bexp_preserve_ugt :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bugt e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hugt: (mk_env_ugt E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv2)).
  exact: (mk_env_ugt_preserve Hugt).
Qed.

Lemma mk_env_bexp_preserve_uge :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buge e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Huge: (mk_env_uge E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv2)).
  exact: (mk_env_uge_preserve Huge).
Qed.

Lemma mk_env_bexp_preserve_slt :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_slt_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_bexp_preserve_sle :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_sle_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_bexp_preserve_sgt :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_sgt_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_bexp_preserve_sge :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_sge_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_bexp_preserve_uaddo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Huaddo: (mk_env_uaddo E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv2)).
  exact: (mk_env_uaddo_preserve Huaddo).
Qed.

Lemma mk_env_bexp_preserve_usubo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Busubo e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Husubo: (mk_env_usubo E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv2)).
  exact: (mk_env_usubo_preserve Husubo).
Qed.

Lemma mk_env_bexp_preserve_umulo :
  forall (e : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e0 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Henv1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Henv2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Humulo: (mk_env_umulo E2 g2 ls1 ls2)=> [[[oE og] ocs] olr]. case=> _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_exp_newer_gen Henv2)).
  exact: (mk_env_umulo_preserve Humulo).
Qed.

Lemma mk_env_bexp_preserve_saddo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_saddo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_bexp_preserve_ssubo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_ssubo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_bexp_preserve_smulo :
  forall (e1 : QFBV.exp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
    forall (e2 : QFBV.exp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) -> env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] r].
  case=> _ <- _ _ _.
  move: (IH1 _ _ _ _ _ _ _ _ _ Hmke1) => HpEE1g.
  move: (IH2 _ _ _ _ _ _ _ _ _ Hmke2) => HpE1E2g1.
  move: (mk_env_smulo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke1) (mk_env_exp_newer_gen Hmke2) => Hgg1 Hg1g2.
  move: (env_preserve_le HpE1E2g1 Hgg1) => HpE1E2g.
  move: (env_preserve_le HpE2Erg2 (pos_leb_trans Hgg1 Hg1g2)) => HpE2Erg.
  apply: (env_preserve_trans _ HpE2Erg).
  exact: (env_preserve_trans HpEE1g HpE1E2g).
Qed.

Lemma mk_env_bexp_preserve_lneg :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Blneg b) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e IH m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv: (mk_env_bexp m s E g e) => [[[[m1 E1] g1] cs1] lr1].
  case Hlneg: (mk_env_lneg E1 g1 lr1) => [[[oE og] ocs] olr].
  case => _ <- _ _ _.
  apply: (env_preserve_trans (IH _ _ _ _ _ _ _ _ _ Henv)).
  apply: (env_preserve_le _ (mk_env_bexp_newer_gen Henv)).
  exact: (mk_env_lneg_preserve Hlneg).
Qed.

Lemma mk_env_bexp_preserve_conj :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        env_preserve E E' g) ->
    forall (b0 : QFBV.bexp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bconj b b0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case Hconj: (mk_env_conj E2 g2 lr1 lr2) => [[[oE og] ocs] olr].
  case => _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_bexp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_bexp_newer_gen Henv2)).
  exact: (mk_env_conj_preserve Hconj).
Qed.

Lemma mk_env_bexp_preserve_disj :
  forall (b : QFBV.bexp),
    (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        env_preserve E E' g) ->
    forall (b0 : QFBV.bexp),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          env_preserve E E' g) ->
      forall (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bdisj b b0) = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  move=> e1 IH1 e2 IH2 m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Henv1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Henv2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case Hdisj: (mk_env_disj E2 g2 lr1 lr2) => [[[oE og] ocs] olr].
  case => _ <- _ _ _.
  apply: (env_preserve_trans (IH1 _ _ _ _ _ _ _ _ _ Henv1)).
  apply: (env_preserve_le _ (mk_env_bexp_newer_gen Henv1)).
  apply: (env_preserve_trans (IH2 _ _ _ _ _ _ _ _ _ Henv2)).
  apply: (env_preserve_le _ (mk_env_bexp_newer_gen Henv2)).
  exact: (mk_env_disj_preserve Hdisj).
Qed.

Corollary mk_env_exp_preserve :
  forall (e : QFBV.exp) m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    env_preserve E E' g
  with
    mk_env_bexp_preserve :
      forall e m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        env_preserve E E' g.
Proof.
  elim .
  - exact: mk_env_exp_preserve_var .
  - exact: mk_env_exp_preserve_const .
  - elim .
    + exact: mk_env_exp_preserve_not .
    + exact: mk_env_exp_preserve_neg .
    + exact: mk_env_exp_preserve_extract .
    + exact: mk_env_exp_preserve_high .
    + exact: mk_env_exp_preserve_low .
    + exact: mk_env_exp_preserve_zeroextend .
    + exact: mk_env_exp_preserve_signextend .
  - elim .
    + exact: mk_env_exp_preserve_and .
    + exact: mk_env_exp_preserve_or .
    + exact: mk_env_exp_preserve_xor .
    + exact: mk_env_exp_preserve_add .
    + exact: mk_env_exp_preserve_sub .
    + exact: mk_env_exp_preserve_mul .
    + exact: mk_env_exp_preserve_mod .
    + exact: mk_env_exp_preserve_srem .
    + exact: mk_env_exp_preserve_smod .
    + exact: mk_env_exp_preserve_shl .
    + exact: mk_env_exp_preserve_lshr .
    + exact: mk_env_exp_preserve_ashr .
    + exact: mk_env_exp_preserve_concat .
  - move => b;
      move : b (mk_env_bexp_preserve b);
      exact: mk_env_exp_preserve_ite .
  (* mk_env_bexp_preserve *)
  elim .
  - exact: mk_env_bexp_preserve_false .
  - exact: mk_env_bexp_preserve_true .
  - elim; move => e0 e1;
      move : e0 (mk_env_exp_preserve e0)
             e1 (mk_env_exp_preserve e1) .
    + exact: mk_env_bexp_preserve_eq .
    + exact: mk_env_bexp_preserve_ult .
    + exact: mk_env_bexp_preserve_ule .
    + exact: mk_env_bexp_preserve_ugt .
    + exact: mk_env_bexp_preserve_uge .
    + exact: mk_env_bexp_preserve_slt .
    + exact: mk_env_bexp_preserve_sle .
    + exact: mk_env_bexp_preserve_sgt .
    + exact: mk_env_bexp_preserve_sge .
    + exact: mk_env_bexp_preserve_uaddo .
    + exact: mk_env_bexp_preserve_usubo .
    + exact: mk_env_bexp_preserve_umulo .
    + exact: mk_env_bexp_preserve_saddo .
    + exact: mk_env_bexp_preserve_ssubo .
    + exact: mk_env_bexp_preserve_smulo .
  - exact: mk_env_bexp_preserve_lneg .
  - exact: mk_env_bexp_preserve_conj .
  - exact: mk_env_bexp_preserve_disj .
Qed.



(* = mk_env_exp_sat and mk_env_bexp_sat = *)

Lemma mk_env_exp_sat_var :
  forall t (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env)
         (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Evar t) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Evar t) te ->
    interp_cnf E' cs.
Proof.
  move=> v te m s E g m' E' g' cs lrs /=. case Hfind: (SSAVM.find v m).
  - case=> _ <- _ <- _ Hnew_gm Hnew_gtt _. done.
  - case Henv: (mk_env_var E g (SSAStore.acc v s) v) => [[[E_v g_v] cs_v] lrs_v].
    case=> _ <- _ <- _ Hnew_gm Hnew_gtt _. exact: (mk_env_var_sat Henv).
Qed.

Lemma mk_env_exp_sat_const :
  forall (b : bits) (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Econst b) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Econst b) te ->
    interp_cnf E' cs.
Proof.
  move=> bs te m s E g m' E' g' cs lrs /=. case=> _ <- _ <- _ Hnew_gm Hnew_gtt _. done.
Qed.

Lemma mk_env_exp_sat_not :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop QFBV.Unot e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m -> newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop QFBV.Unot e1) te ->
      interp_cnf E' cs.
Proof.
  move=> e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_not E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt Hwf. rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) => HiE1c1.
  move: (mk_env_not_preserve Hmkr) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  exact: (mk_env_not_sat Hmkr Hg1l1).
Qed.

Lemma mk_env_exp_sat_and :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Band e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Band e1 e2) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_and E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_and_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  exact: (mk_env_and_sat Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_sat_or :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bor e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bor e0 e1) te ->
      interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_or E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_or_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  exact: (mk_env_or_sat Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_sat_xor :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lrs : word),
        mk_env_exp m s E g (QFBV.Ebinop QFBV.Bxor e1 e2) = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bxor e1 e2) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_xor E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_xor_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  exact: (mk_env_xor_sat Hmkr Hg2t Hg2l1 Hg2l2).
Qed.

Lemma mk_env_exp_sat_neg :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
    mk_env_exp m s E g (QFBV.Eunop QFBV.Uneg e1) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Eunop QFBV.Uneg e1) te ->
    interp_cnf E' cs.
Proof.
  move=> e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmkr : (mk_env_neg E1 g1 ls1) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= Hwf1 .
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_neg_preserve Hmkr) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  exact: (mk_env_neg_sat Hmkr Hg1t Hg1l1).
Qed.

Lemma mk_env_exp_sat_add :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Badd e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Badd e e0) te ->
    interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_add E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_add_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2f.
  rewrite newer_than_lit_tt_ff in Hg2f .
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_add_sat Hmkr Hg2l1 Hg2l2 Hg2f) .
Qed.

Lemma mk_env_exp_sat_sub :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsub e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsub e e0) te ->
    interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sub E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_sub_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_sub_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_exp_sat_mul :
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmul e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bmul e e0) te ->
    interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_mul E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_mul_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_mul_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_exp_sat_mod :
  forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
  forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bmod e e0) te ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_srem :
  forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
  forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsrem e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsrem e e0) te ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_smod :
  forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
  forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
         (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
         (cs : cnf) (lrs : word),
    mk_env_exp m s E g (QFBV.Ebinop QFBV.Bsmod e e0) = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bsmod e e0) te ->
    interp_cnf E' cs.
Proof.
Admitted.

Lemma mk_env_exp_sat_shl :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bshl e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bshl e0 e1) te ->
      interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_shl E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_shl_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_shl_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed .

Lemma mk_env_exp_sat_lshr :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Blshr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Blshr e0 e1) te ->
      interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_lshr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_lshr_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_lshr_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed .

Lemma mk_env_exp_sat_ashr :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bashr e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bashr e0 e1) te ->
      interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ashr E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_ashr_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_ashr_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed .

Lemma mk_env_exp_sat_concat :
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
    forall (e1 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e1 te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Ebinop QFBV.Bconcat e0 e1) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Ebinop QFBV.Bconcat e0 e1) te ->
      interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1E2g1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  rewrite (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) // .
Qed .

Lemma mk_env_exp_sat_extract :
  forall (i j : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uextr i j) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uextr i j) e) te ->
      interp_cnf E' cs.
Proof.
  move=> i j e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ <- _ Hgm Hgt Hwf .
  rewrite !interp_cnf_cat /= .
  (* interp_cnf Er cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

(*
Lemma mk_env_exp_sat_slice :
  forall (w1 w2 w3 : nat),
    forall (e : QFBV.exp (w3 + w2 + w1)),
      (forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : (w3 + w2 + w1).-tuple literal),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          interp_cnf E' cs) ->
    forall (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : w2.-tuple literal),
      mk_env_exp m s E g (QFBV64.bvSlice w1 w2 w3 e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      interp_cnf E' cs.
Proof.
  rewrite /=; intros; dcase_hyps; subst. rewrite !interp_cnf_append.
  by rewrite (H _ _ _ _ _ _ _ _ _ H0 H1 H2) .
Qed .
*)

Lemma mk_env_exp_sat_high :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm)
           (s : SSAStore.t) (E : env) (g : generator) (m' : vm)
           (E' : env) (g' : generator) (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uhigh n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uhigh n) e) te ->
      interp_cnf E' cs.
Proof.
  move=> n e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ <- _ Hgm Hgt Hwf .
  rewrite !interp_cnf_cat /= .
  (* interp_cnf Er cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

Lemma mk_env_exp_sat_low :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
           (m' : vm) (E' : env) (g' : generator) (cs : cnf)
           (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Ulow n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Ulow n) e) te ->
      interp_cnf E' cs.
Proof.
  move=> n e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ <- _ Hgm Hgt Hwf .
  rewrite !interp_cnf_cat /= .
  (* interp_cnf Er cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

Lemma mk_env_exp_sat_zeroextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Uzext n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Uzext n) e) te ->
      interp_cnf E' cs.
Proof.
  move=> n e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ <- _ Hgm Hgt Hwf .
  rewrite !interp_cnf_cat /= .
  (* interp_cnf Er cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

Lemma mk_env_exp_sat_signextend :
  forall (n : nat),
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
    forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
           (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
           (cs : cnf) (lrs : word),
      mk_env_exp m s E g (QFBV.Eunop (QFBV.Usext n) e) = (m', E', g', cs, lrs) ->
      newer_than_vm g m ->
      newer_than_lit g lit_tt ->
      QFBV.well_formed_exp (QFBV.Eunop (QFBV.Usext n) e) te ->
      interp_cnf E' cs.
Proof.
  move=> n e1 IH1 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case=> _ <- _ <- _ Hgm Hgt Hwf .
  rewrite !interp_cnf_cat /= .
  (* interp_cnf Er cs1 *)
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf) // .
Qed .

Lemma mk_env_exp_sat_ite :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp b te ->
        interp_cnf E' cs) ->
    forall (e : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e te ->
          interp_cnf E' cs) ->
      forall (e0 : QFBV.exp),
        (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
                (m' : vm) (E' : env) (g' : generator) (cs : cnf)
                (lrs : word),
            mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
            newer_than_vm g m ->
            newer_than_lit g lit_tt ->
            QFBV.well_formed_exp e0 te ->
            interp_cnf E' cs) ->
        forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
               (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lrs : word),
          mk_env_exp m s E g (QFBV.Eite b e e0) = (m', E', g', cs, lrs) ->
          newer_than_vm g m ->
          newer_than_lit g lit_tt ->
          QFBV.well_formed_exp (QFBV.Eite b e e0) te ->
          interp_cnf E' cs.
Proof.
  move=> c IHc e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmkc : (mk_env_bexp m s E g c) => [[[[mc Ec] gc] csc] lsc].
  case Hmke1 : (mk_env_exp mc s Ec gc e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ite E2 g2 lsc ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [/andP [Hwfc Hwf1] Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er csc *)
  move: (IHc _ _ _ _ _ _ _ _ _ _ Hmkc Hgm Hgt Hwfc) => HiEccc.
  move: (mk_env_exp_preserve Hmke1) => HpEcE1gc.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_ite_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgcg1.
  move: (env_preserve_le HpE1Erg1 Hgcg1) => HpE1Ergc.
  move: (env_preserve_trans HpEcE1gc HpE1Ergc) => HpEcErgc.
  move: (mk_env_bexp_newer_cnf Hmkc Hgm Hgt Hwfc) => Hgccc.
  rewrite (env_preserve_cnf HpEcErgc Hgccc) HiEccc /=.
  (* interp_cnf Er cs1 *)
  move: (mk_env_bexp_newer_vm Hmkc Hgm) => Hgcmc.
  move: (mk_env_bexp_newer_gen Hmkc) => Hggc.
  move: (newer_than_lit_le_newer Hgt Hggc) => Hgct.
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgcmc Hgct Hwf1) => HiE1c1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgcmc Hgct Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgcmc) => Hg1m1.
  move: (newer_than_lit_le_newer Hgct Hgcg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_bexp_newer_res Hmkc Hgm Hgt) => Hgclc.
  move: (mk_env_exp_newer_res Hmke1 Hgcmc Hgct) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hgclc (pos_leb_trans Hgcg1 Hg1g2)) => Hg2lc .
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_ite_sat Hmkr Hg2t Hg2lc Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_false :
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Bfalse = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt ->
    QFBV.well_formed_bexp QFBV.Bfalse te ->
    interp_cnf E' cs.
Proof.
  move=> te m s E g m' E' g' cs lr /=. case=> _ <- _ <- _ Hnew_gm Hnew_gtt _ // .
Qed.

Lemma mk_env_bexp_sat_true :
  forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
         (m' : vm) (E' : env) (g' : generator) (cs : cnf) (lr : literal),
    mk_env_bexp m s E g QFBV.Btrue = (m', E', g', cs, lr) ->
    newer_than_vm g m -> newer_than_lit g lit_tt ->
    QFBV.well_formed_bexp QFBV.Btrue te ->
    interp_cnf E' cs.
Proof.
  move=> te m s E g m' E' g' cs lr /=. case=> _ <- _ <- _ Hnew_gm Hnew_gtt _ // .
Qed.

Lemma mk_env_bexp_sat_eq :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Beq e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Beq e e0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr /=.
  case Hmke1: (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2: (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr: (mk_env_eq E2 g2 ls1 ls2) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hgm Hgtt /= /andP [/andP [Hwf1 Hwf2] Hsize]. rewrite !interp_cnf_cat.
  move: (mk_env_exp_preserve Hmke2) => HE1E2g1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgtt Hwf1) => Hg1cs1.
  move: (newer_than_cnf_le_newer Hg1cs1 Hg1g2) => Hg2cs1.
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => Hg1tt.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2cs2.
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgtt) => Hg1ls1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2ls2.
  move: (newer_than_lit_le_newer Hg1tt Hg1g2) => Hg2tt .
  move: (newer_than_lits_le_newer Hg1ls1 Hg1g2) => Hg2ls1.
  (* interp_cnf oE cs1 *)
  rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkr) Hg2cs1).
  rewrite (env_preserve_cnf HE1E2g1 Hg1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) /= .
  (* interp_cnf oE cs2 *)
  rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkr) Hg2cs2).
  rewrite (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) /= .
  (* interp_cnf oE ocs *)
  apply: (mk_env_eq_sat Hmkr Hg2tt Hg2ls1 Hg2ls2).
Qed.

Lemma mk_env_bexp_sat_ult :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bult e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bult e e0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ult E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_ult_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_ult_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_ule :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bule e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bule e e0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ule E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_ule_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_ule_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_ugt :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bugt e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bugt e e0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ugt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_ugt_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_ugt_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_uge :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buge e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Buge e e0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_uge_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_uge_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_slt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bslt e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bslt e1 e2) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_slt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_slt_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_slt_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_sle :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsle e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsle e1 e2) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sle E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_sle_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_sle_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_sgt :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsgt e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsgt e1 e2) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sgt E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_sgt_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_sgt_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_sge :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsge e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsge e1 e2) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_sge E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_sge_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_sge_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_uaddo :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Buaddo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Buaddo e e0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_uaddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_uaddo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_uaddo_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_usubo :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Busubo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Busubo e e0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_usubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_usubo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_usubo_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_umulo :
  forall (e : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e te ->
        interp_cnf E' cs) ->
    forall (e0 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e0 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bumulo e e0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bumulo e e0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_umulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_umulo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_umulo_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_saddo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsaddo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsaddo e1 e2) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_saddo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_saddo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_saddo_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_ssubo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bssubo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bssubo e1 e2) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_ssubo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_ssubo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_ssubo_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_smulo :
  forall (e1 : QFBV.exp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lrs : word),
        mk_env_exp m s E g e1 = (m', E', g', cs, lrs) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_exp e1 te ->
        interp_cnf E' cs) ->
    forall (e2 : QFBV.exp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lrs : word),
          mk_env_exp m s E g e2 = (m', E', g', cs, lrs) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_exp e2 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
             (m' : vm) (E' : env) (g' : generator) (cs : cnf)
             (lr : literal),
        mk_env_bexp m s E g (QFBV.Bbinop QFBV.Bsmulo e1 e2) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bbinop QFBV.Bsmulo e1 e2) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lrs /=.
  case Hmke1 : (mk_env_exp m s E g e1) => [[[[m1 E1] g1] cs1] ls1].
  case Hmke2 : (mk_env_exp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] ls2].
  case Hmkr : (mk_env_smulo E2 g2 ls1 ls2) => [[[Er gr] csr] lsr].
  case=> _ <- _ <- _ Hgm Hgt /= /andP [/andP [Hwf1 Hwf2] Hsize].
  rewrite !interp_cnf_cat.
  (* interp_cnf Er cs1 *)
  move: (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgt Hwf1) => HiE1c1.
  move: (mk_env_exp_preserve Hmke2) => HpE1E2g1.
  move: (mk_env_smulo_preserve Hmkr) => HpE2Erg2.
  move: (mk_env_exp_newer_gen Hmke2) => Hg1g2.
  move: (env_preserve_le HpE2Erg2 Hg1g2) => HpE2Erg1.
  move: (env_preserve_trans HpE1E2g1 HpE2Erg1) => HpE1Erg1.
  move: (mk_env_exp_newer_cnf Hmke1 Hgm Hgt Hwf1) => Hg1c1.
  rewrite (env_preserve_cnf HpE1Erg1 Hg1c1) HiE1c1 /=.
  (* interp_cnf Er cs2 *)
  move: (mk_env_exp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (mk_env_exp_newer_gen Hmke1) => Hgg1.
  move: (newer_than_lit_le_newer Hgt Hgg1) => Hg1t.
  move: (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1t Hwf2) => HiE2c2.
  move: (mk_env_exp_newer_cnf Hmke2 Hg1m1 Hg1t Hwf2) => Hg2c2.
  rewrite (env_preserve_cnf HpE2Erg2 Hg2c2) HiE2c2 /=.
  (* interp_cnf Er csr *)
  move: (mk_env_exp_newer_res Hmke1 Hgm Hgt) => Hg1l1.
  move: (mk_env_exp_newer_res Hmke2 Hg1m1 Hg1t) => Hg2l2.
  move: (newer_than_lit_le_newer Hg1t Hg1g2) => Hg2t.
  move: (newer_than_lits_le_newer Hg1l1 Hg1g2) => Hg2l1.
  apply: (mk_env_smulo_sat Hmkr Hg2t Hg2l1 Hg2l2) .
Qed.

Lemma mk_env_bexp_sat_lneg :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp b te ->
        interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Blneg b) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Blneg b) te ->
        interp_cnf E' cs.
Proof.
  move=> e IH te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Hmke: (mk_env_bexp m s E g e) => [[[[m1 E1] g1] cs1] lr1].
  case Hmkr: (mk_env_lneg E1 g1 lr1) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hgm Hgtt Hwf. rewrite !interp_cnf_cat.
  move: (mk_env_bexp_newer_gen Hmke) => Hgg1.
  move: (mk_env_bexp_newer_cnf Hmke Hgm Hgtt Hwf) => Hg1cs1.
  move: (mk_env_bexp_newer_vm Hmke Hgm) => Hg1m1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => {Hgg1} Hg1tt.
  move: (mk_env_bexp_newer_res Hmke Hgm Hgtt) => Hg1lr1.
  (* interp_cnf E2 cs1 *)
  rewrite (env_preserve_cnf (mk_env_lneg_preserve Hmkr) Hg1cs1).
  rewrite (IH _ _ _ _ _ _ _ _ _ _ Hmke Hgm Hgtt Hwf) // .
  (* interp_cnf oE ocs *)
  apply: (mk_env_lneg_sat Hmkr Hg1lr1).
Qed.

Lemma mk_env_bexp_sat_conj :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp b te ->
        interp_cnf E' cs) ->
    forall (b0 : QFBV.bexp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_bexp b0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bconj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bconj b b0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Hmke1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Hmke2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case Hmkr: (mk_env_conj E2 g2 lr1 lr2) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hgm Hgtt /= /andP [Hwf1 Hwf2]. rewrite !interp_cnf_cat.
  move: (mk_env_bexp_preserve Hmke2) => HE1E2g1.
  move: (mk_env_bexp_newer_gen Hmke1) => Hgg1.
  move: (mk_env_bexp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_bexp_newer_cnf Hmke1 Hgm Hgtt Hwf1) => Hg1cs1.
  move: (newer_than_cnf_le_newer Hg1cs1 Hg1g2) => Hg2cs1.
  move: (mk_env_bexp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => {Hgg1} Hg1tt.
  move: (mk_env_bexp_newer_cnf Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2cs2.
  move: (mk_env_bexp_newer_res Hmke1 Hgm Hgtt) => Hg1lr1.
  move: (mk_env_bexp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2lr2.
  move: (newer_than_lit_le_newer Hg1lr1 Hg1g2) => {Hg1g2 Hg1lr1} Hg2lr1.
  (* interp_cnf E2 cs1 *)
  rewrite (env_preserve_cnf (mk_env_conj_preserve Hmkr) Hg2cs1).
  rewrite (env_preserve_cnf HE1E2g1 Hg1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) // .
  (* interp_cnf E2 cs2 *)
  rewrite (env_preserve_cnf (mk_env_conj_preserve Hmkr) Hg2cs2).
  rewrite (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) // .
  (* interp_cnf oE ocs *)
  apply: (mk_env_conj_sat Hmkr Hg2lr1 Hg2lr2).
Qed.

Lemma mk_env_bexp_sat_disj :
  forall (b : QFBV.bexp),
    (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
            (m' : vm) (E' : env) (g' : generator) (cs : cnf)
            (lr : literal),
        mk_env_bexp m s E g b = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp b te ->
        interp_cnf E' cs) ->
    forall (b0 : QFBV.bexp),
      (forall (te : SSATE.env) (m : vm) (s : SSAStore.t) (E : env) (g : generator)
              (m' : vm) (E' : env) (g' : generator) (cs : cnf)
              (lr : literal),
          mk_env_bexp m s E g b0 = (m', E', g', cs, lr) ->
          newer_than_vm g m -> newer_than_lit g lit_tt ->
          QFBV.well_formed_bexp b0 te ->
          interp_cnf E' cs) ->
      forall (te : SSATE.env) (m : vm) (s : SSAStore.t)
             (E : env) (g : generator) (m' : vm) (E' : env) (g' : generator)
             (cs : cnf) (lr : literal),
        mk_env_bexp m s E g (QFBV.Bdisj b b0) = (m', E', g', cs, lr) ->
        newer_than_vm g m -> newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp (QFBV.Bdisj b b0) te ->
        interp_cnf E' cs.
Proof.
  move=> e1 IH1 e2 IH2 te m s E g m' E' g' cs lr. rewrite /mk_env_bexp -/mk_env_bexp.
  case Hmke1: (mk_env_bexp m s E g e1) => [[[[m1 E1] g1] cs1] lr1].
  case Hmke2: (mk_env_bexp m1 s E1 g1 e2) => [[[[m2 E2] g2] cs2] lr2].
  case Hmkr: (mk_env_disj E2 g2 lr1 lr2) => [[[oE og] ocs] olr].
  case=> _ <- _ <- _ Hgm Hgtt /= /andP [Hwf1 Hwf2]. rewrite !interp_cnf_cat.
  move: (mk_env_bexp_preserve Hmke2) => HE1E2g1.
  move: (mk_env_bexp_newer_gen Hmke1) => Hgg1.
  move: (mk_env_bexp_newer_gen Hmke2) => Hg1g2.
  move: (mk_env_bexp_newer_cnf Hmke1 Hgm Hgtt Hwf1) => Hg1cs1.
  move: (newer_than_cnf_le_newer Hg1cs1 Hg1g2) => Hg2cs1.
  move: (mk_env_bexp_newer_vm Hmke1 Hgm) => Hg1m1.
  move: (newer_than_lit_le_newer Hgtt Hgg1) => {Hgg1} Hg1tt.
  move: (mk_env_bexp_newer_cnf Hmke2 Hg1m1 Hg1tt Hwf2) => Hg2cs2.
  move: (mk_env_bexp_newer_res Hmke1 Hgm Hgtt) => Hg1lr1.
  move: (mk_env_bexp_newer_res Hmke2 Hg1m1 Hg1tt) => Hg2lr2.
  move: (newer_than_lit_le_newer Hg1lr1 Hg1g2) => {Hg1g2 Hg1lr1} Hg2lr1.
  (* interp_cnf E2 cs1 *)
  rewrite (env_preserve_cnf (mk_env_disj_preserve Hmkr) Hg2cs1).
  rewrite (env_preserve_cnf HE1E2g1 Hg1cs1).
  rewrite (IH1 _ _ _ _ _ _ _ _ _ _ Hmke1 Hgm Hgtt Hwf1) // .
  (* interp_cnf E2 cs2 *)
  rewrite (env_preserve_cnf (mk_env_disj_preserve Hmkr) Hg2cs2).
  rewrite (IH2 _ _ _ _ _ _ _ _ _ _ Hmke2 Hg1m1 Hg1tt Hwf2) // .
  (* interp_cnf oE ocs *)
  apply: (mk_env_disj_sat Hmkr Hg2lr1 Hg2lr2).
Qed.

Corollary mk_env_exp_sat :
  forall e te m s E g m' E' g' cs lrs,
    mk_env_exp m s E g e = (m', E', g', cs, lrs) ->
    newer_than_vm g m ->
    newer_than_lit g lit_tt ->
    QFBV.well_formed_exp e te ->
    interp_cnf E' cs
  with
    mk_env_bexp_sat :
      forall e te m s E g m' E' g' cs lr,
        mk_env_bexp m s E g e = (m', E', g', cs, lr) ->
        newer_than_vm g m ->
        newer_than_lit g lit_tt ->
        QFBV.well_formed_bexp e te ->
        interp_cnf E' cs.
Proof.
  (* mk_env_exp_sat *)
  elim .
  - exact: mk_env_exp_sat_var .
  - exact: mk_env_exp_sat_const .
  - elim .
    + exact: mk_env_exp_sat_not .
    + exact: mk_env_exp_sat_neg .
    + exact: mk_env_exp_sat_extract .
    + exact: mk_env_exp_sat_high .
    + exact: mk_env_exp_sat_low .
    + exact: mk_env_exp_sat_zeroextend .
    + exact: mk_env_exp_sat_signextend .
  - elim .
    + exact: mk_env_exp_sat_and .
    + exact: mk_env_exp_sat_or .
    + exact: mk_env_exp_sat_xor .
    + exact: mk_env_exp_sat_add .
    + exact: mk_env_exp_sat_sub .
    + exact: mk_env_exp_sat_mul .
    + exact: mk_env_exp_sat_mod .
    + exact: mk_env_exp_sat_srem .
    + exact: mk_env_exp_sat_smod .
    + exact: mk_env_exp_sat_shl .
    + exact: mk_env_exp_sat_lshr .
    + exact: mk_env_exp_sat_ashr .
    + exact: mk_env_exp_sat_concat .
  - move => b;
      move : b (mk_env_bexp_sat b);
      exact: mk_env_exp_sat_ite .
  (* mk_env_bexp_sat *)
  elim .
  - exact: mk_env_bexp_sat_false .
  - exact: mk_env_bexp_sat_true .
  - elim; move => e0 e1;
          move : e0 (mk_env_exp_sat e0)
                 e1 (mk_env_exp_sat e1) .
    + exact: mk_env_bexp_sat_eq .
    + exact: mk_env_bexp_sat_ult .
    + exact: mk_env_bexp_sat_ule .
    + exact: mk_env_bexp_sat_ugt .
    + exact: mk_env_bexp_sat_uge .
    + exact: mk_env_bexp_sat_slt .
    + exact: mk_env_bexp_sat_sle .
    + exact: mk_env_bexp_sat_sgt .
    + exact: mk_env_bexp_sat_sge .
    + exact: mk_env_bexp_sat_uaddo .
    + exact: mk_env_bexp_sat_usubo .
    + exact: mk_env_bexp_sat_umulo .
    + exact: mk_env_bexp_sat_saddo .
    + exact: mk_env_bexp_sat_ssubo .
    + exact: mk_env_bexp_sat_smulo .
  - exact: mk_env_bexp_sat_lneg .
  - exact: mk_env_bexp_sat_conj .
  - exact: mk_env_bexp_sat_disj .
Qed.



(* ===== mk_env ===== *)

Definition init_vm := SSAVM.empty word.
Definition init_gen := (var_tt + 1)%positive.
Definition init_env : env := fun _ => true.

Lemma init_newer_than_vm :
  newer_than_vm init_gen init_vm.
Proof.
  done.
Qed.

Lemma init_newer_than_tt :
  newer_than_lit init_gen lit_tt.
Proof.
  done.
Qed.

Lemma init_tt :
  interp_lit init_env lit_tt.
Proof.
  done.
Qed.

Definition mk_env (s : SSAStore.t) (e : QFBV.bexp) : env :=
  let '(m', E', g, cs, lr) := mk_env_bexp init_vm s init_env init_gen e in
  E'.

Lemma init_consistent :
  forall s, consistent init_vm init_env s.
Proof.
  move=> s x. rewrite /consistent1 /init_vm. rewrite SSAVM.Lemmas.empty_o. done.
Qed.

Lemma mk_env_consistent :
  forall s e te m g cs lr,
    bit_blast_bexp te init_vm init_gen e = (m, g, cs, lr) ->
    AdhereConform.conform_bexp e s te ->
    QFBV.well_formed_bexp e te ->
    consistent m (mk_env s e) s.
Proof.
  move=> s e te m g cs lr Hbb Hcf Hwf. rewrite /mk_env.
  case Henv: (mk_env_bexp init_vm s init_env init_gen e) => [[[[m' E'] g'] cs'] lr'].
  move: (mk_env_bexp_is_bit_blast_bexp Hcf Hwf Henv). rewrite Hbb. case=> Hm Hg Hcs Hlr.
  rewrite Hm. apply: (mk_env_bexp_consistent Henv init_newer_than_vm).
  exact: init_consistent.
Qed.

Lemma mk_env_tt :
  forall s e, interp_lit (mk_env s e) lit_tt.
Proof.
  move=> s e. rewrite /mk_env.
  set m' := mk_env_bexp init_vm s init_env init_gen e.
  have: mk_env_bexp init_vm s init_env init_gen e = m' by reflexivity. move: m'.
  case=> [[[[m' E'] g'] cs'] lr'] Henv.
  rewrite (env_preserve_lit (mk_env_bexp_preserve Henv) init_newer_than_tt).
  exact: init_tt.
Qed.

Lemma mk_env_sat :
  forall s e te m g cs lr,
    bit_blast_bexp te init_vm init_gen e = (m, g, cs, lr) ->
    AdhereConform.conform_bexp e s te ->
    QFBV.well_formed_bexp e te ->
    interp_cnf (mk_env s e) cs.
Proof.
  move=> s e te m g cs lr Hbb Hcf Hwf. move: (mk_env_tt s e). rewrite /mk_env.
  set m' := mk_env_bexp init_vm s init_env init_gen e.
  have: mk_env_bexp init_vm s init_env init_gen e = m' by reflexivity. move: m'.
  case=> [[[[m' E'] g'] cs'] lr'] Henv. move: (mk_env_bexp_is_bit_blast_bexp Hcf Hwf Henv).
  rewrite Hbb; case=> _ _ -> _ Htt.
  exact: (mk_env_bexp_sat Henv init_newer_than_vm init_newer_than_tt Hwf).
Qed.


(* ===== mk_state ===== *)

Fixpoint lits_as_bits E (ls : word) : bits :=
  match ls with
  | [::] => [::]
  | hd::tl => joinlsb (interp_lit E hd) (lits_as_bits E tl)
  end .

Lemma enc_bits_lits_as_bits :
  forall E (ls : word),
    enc_bits E ls (lits_as_bits E ls).
Proof.
  move => E .
  elim .
  - done.
  - move => l ls IH .
    rewrite /= enc_bits_cons IH /= /enc_bit eqxx // .
Qed.

(* TypEnv.deftyp is Tuint 0. *)
Definition init_state : SSAStore.t := fun _ => from_nat 0 0.

Definition mk_state (E : env) (m : vm) : SSAStore.t :=
  (SSAVM.fold (fun v ls s => SSAStore.upd v (lits_as_bits E ls) s) m init_state).

Lemma mk_state_find :
  forall E m x ls,
    SSAVM.find x m = Some ls ->
    SSAStore.acc x (mk_state E m) = lits_as_bits E ls.
Proof.
  move=> E m.
  apply: (@SSAVM.Lemmas.OP.P.fold_rec
            word (SSAStore.t)
            (fun m s =>
               forall x ls,
                 SSAVM.find x m = Some ls ->
                 SSAStore.acc x s = lits_as_bits E ls)
            (fun v ls s => SSAStore.upd v (lits_as_bits E ls) s)
            init_state
            m).
  - move=> m0 Hempty x ls Hfind. rewrite (SSAVM.Lemmas.Empty_find _ Hempty) in Hfind.
    discriminate.
  - move=> x lsx s m' m'' Hmapsto_xm Hin_xm' Hadd IH. move=> y lsy Hfind_y.
    case Hyx: (y == x).
    + rewrite (SSAStore.acc_upd_eq Hyx). move: (Hadd y).
      rewrite Hfind_y (SSAVM.Lemmas.find_add_eq Hyx). case=> ->. reflexivity.
    + move/idP/negP: Hyx => Hyx. rewrite (SSAStore.acc_upd_neq  Hyx).
      apply: IH. move: (Hadd y). rewrite Hfind_y. move/negP: Hyx => Hyx.
      rewrite (SSAVM.Lemmas.find_add_neq Hyx). by move=> ->; reflexivity.
Qed.

Lemma mk_state_consistent :
  forall E m, consistent m E (mk_state E m).
Proof.
  move=> E m x. rewrite /consistent1. case Hfind: (SSAVM.find x m); last by trivial.
  rewrite (mk_state_find _ Hfind). exact: enc_bits_lits_as_bits.
Qed.

Lemma size_bit_blast_var' g n g' vs' :
  bit_blast_var' g n = (g', vs') -> size vs' = n .
Proof .
  elim : n g g' vs' => [ |n IH] g g' vs' .
  - case => _ <- // .
  - rewrite /bit_blast_var' /= -/bit_blast_var' .
    dcase (bit_blast_var' (g+1)%positive n) => [[g'' tl] Hbbr] .
    case => _ <- /= .
    rewrite (IH _ _ _ Hbbr) // .
Qed .

Lemma size_lits_as_bits E ls :
  size ls = size (lits_as_bits E ls) .
Proof .
  elim ls; first done .
  move => a l IH .
  rewrite /= IH // .
Qed .

Lemma bit_blast_adhere_exp :
  forall e te m m' g g' cs' lr',
    AdhereConform.adhere m te ->
    bit_blast_exp te m g e = (m', g', cs', lr') ->
    AdhereConform.adhere m' te
with
bit_blast_adhere_bexp :
  forall e te m m' g g' cs' lr',
    AdhereConform.adhere m te ->
    bit_blast_bexp te m g e = (m', g', cs', lr') ->
    AdhereConform.adhere m' te .
Proof .
  (* bit_blast_adhere_exp *)
  elim; rewrite /= .
  - move => v te m m' g g' cs lr Hadm .
    case : (SSAVM.find v m) .
    + move => a; case => <- _ _ _ // .
    + rewrite /bit_blast_var .
      dcase (bit_blast_var' g (SSATE.vsize v te)) => [[g'0 vs] Hbbr ] .
      case => <- _ _ _ .
      rewrite /adhere => u .
      case Heq : (u == v) .
      * rewrite (eqP Heq) => _ .
        have Hfind : (SSAVM.M.find v (SSAVM.M.add v vs m) = Some vs) .
        { apply : SSAVM.Lemmas.find_add_eq; done . }
        exists vs .
        rewrite Hfind (size_bit_blast_var' Hbbr) // .
      * have Hneq : ~(SSAVM.E.eq u v) .
        { rewrite /SSAVM.E.eq Heq // . }
        rewrite (SSAVM.Lemmas.mem_add_neq Hneq) => Hmem .
        rewrite (SSAVM.Lemmas.find_add_neq Hneq) .
        apply : (Hadm u Hmem) .
  - move =>b te m m' g g' cs' lr' Hadm .
    case => <- _ _ _ // .
  - elim => /= [e IHe te m m' g g' cs' lr' Hadm |
                e IHe te m m' g g' cs' lr' Hadm |
                i j e IHe te m m' g g' cs' lr' Hadm |
                n e IHe te m m' g g' cs' lr' Hadm |
                n e IHe te m m' g g' cs' lr' Hadm |
                n e IHe te m m' g g' cs' lr' Hadm |
                n e IHe te m m' g g' cs' lr' Hadm];
      dcase (bit_blast_exp te m g e) => [[[[m1 g1] cs1] ls1] Hbbe] .
    + dcase (bit_blast_not g1 ls1) => [[[gr csr] lsr] _];
      case => <- _ _ _; apply : (IHe _ _ _ _ _ _ _ Hadm Hbbe) .
    + dcase (bit_blast_neg g1 ls1) => [[[gr csr] lsr] _];
      case => <- _ _ _; apply : (IHe _ _ _ _ _ _ _ Hadm Hbbe) .
    + case => <- _ _ _; apply : (IHe _ _ _ _ _ _ _ Hadm Hbbe) .
    + case => <- _ _ _; apply : (IHe _ _ _ _ _ _ _ Hadm Hbbe) .
    + case => <- _ _ _; apply : (IHe _ _ _ _ _ _ _ Hadm Hbbe) .
    + case => <- _ _ _; apply : (IHe _ _ _ _ _ _ _ Hadm Hbbe) .
    + case => <- _ _ _; apply : (IHe _ _ _ _ _ _ _ Hadm Hbbe) .
  - elim => /= e0 IH0 e1 IH1 te m m' g g' cs' lr' Hadm;
      dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] ls1] Hbbe0];
      dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hbbe1];
      move : (IH0 _ _ _ _ _ _ _ Hadm Hbbe0) => {Hadm Hbbe0} Hadm1;
      move : (IH1 _ _ _ _ _ _ _ Hadm1 Hbbe1) => {Hadm1 Hbbe1} Hadm2 .
    + dcase (bit_blast_and g2 ls1 ls2) => [[[gr csr] lsr] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_or g2 ls1 ls2) => [[[gr csr] lsr] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_xor g2 ls1 ls2) => [[[gr csr] lsr] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_add g2 ls1 ls2) => [[[gr csr] lsr] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_sub g2 ls1 ls2) => [[[gr csr] lsr] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_mul g2 ls1 ls2) => [[[gr csr] lsr] _];
      case => <- _ _ _ // .
    + case => <- _ _ _ // .
    + case => <- _ _ _ // .
    + case => <- _ _ _ // .
    + dcase (bit_blast_shl g2 ls1 ls2) => [[[gr csr] lsr] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_lshr g2 ls1 ls2) => [[[gr csr] lsr] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_ashr g2 ls1 ls2) => [[[gr csr] lsr] _];
      case => <- _ _ _ // .
    + case => <- _ _ _ // .
  - move => b e0 IH0 e1 IH1 te m m' g g' cs' lr' Hadm .
    dcase (bit_blast_bexp te m g b) => [[[[mc gc] csc] lc] Hbbc] .
    move : (bit_blast_adhere_bexp b _ _ _ _ _ _ _ Hadm Hbbc) => {Hadm Hbbc} Hadmc .
    dcase (bit_blast_exp te mc gc e0) => [[[[m1 g1] cs1] ls1] Hbbe0] .
    move : (IH0 _ _ _ _ _ _ _ Hadmc Hbbe0) => {Hadmc Hbbe0} Hadm1 .
    dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hbbe1] .
    move : (IH1 _ _ _ _ _ _ _ Hadm1 Hbbe1) => {Hadm1 Hbbe1} Hadm2 .
    dcase (bit_blast_ite g2 lc ls1 ls2) => [[[gr csr] lsr] _ ] .
    case => <- _ _ _ // .
  (* bit_blast_adhere_bexp *)
  elim; rewrite /= .
  - move => te m m' g g' cs' lr' Hadm .
    case => <- _ _ _ // .
  - move => te m m' g g' cs' lr' Hadm .
    case => <- _ _ _ // .
  - elim => e0 e1 te m m' g g' cs' lr' Hadm;
      dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] ls1] Hbbe0];
      move : (bit_blast_adhere_exp e0 _ _ _ _ _ _ _ Hadm Hbbe0) => {Hadm Hbbe0} Hadm1;
      dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hbbe1];
      move : (bit_blast_adhere_exp e1 _ _ _ _ _ _ _ Hadm1 Hbbe1) => {Hadm1 Hbbe1} Hadm2 .
    + dcase (bit_blast_eq g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_ult g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_ule g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_ugt g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_uge g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_slt g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_sle g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_sgt g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_sge g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_uaddo g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_usubo g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_umulo g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_saddo g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_ssubo g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_smulo g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
  - move => b IHb te m m' g g' cs' lr' Hadm .
    dcase (bit_blast_bexp te m g b) => [[[[m1 g1] cs1] l1] Hbbe] .
    case => <- _ _ _ .
    apply : (bit_blast_adhere_bexp b _ _ _ _ _ _ _ Hadm Hbbe) .
  - move => b0 IH0 b1 IH1 te m m' g g' cs' lr' Hadm .
    dcase (bit_blast_bexp te m g b0) => [[[[m1 g1] cs1] l1] Hbbe0] .
    move : (IH0 _ _ _ _ _ _ _ Hadm Hbbe0) => {Hadm Hbbe0} Hadm1 .
    dcase (bit_blast_bexp te m1 g1 b1) => [[[[m2 g2] cs2] l2] Hbbe1] .
    move : (IH1 _ _ _ _ _ _ _ Hadm1 Hbbe1) => {Hadm1 Hbbe1} Hadm2 .
    case => <- _ _ _ // .
  - move => b0 IH0 b1 IH1 te m m' g g' cs' lr' Hadm .
    dcase (bit_blast_bexp te m g b0) => [[[[m1 g1] cs1] l1] Hbbe0] .
    move : (IH0 _ _ _ _ _ _ _ Hadm Hbbe0) => {Hadm Hbbe0} Hadm1 .
    dcase (bit_blast_bexp te m1 g1 b1) => [[[[m2 g2] cs2] l2] Hbbe1] .
    move : (IH1 _ _ _ _ _ _ _ Hadm1 Hbbe1) => {Hadm1 Hbbe1} Hadm2 .
    case => <- _ _ _ // .
Qed .

Lemma mk_state_conform_exp :
  forall e te E m',
    AdhereConform.bound_exp e m' ->
    AdhereConform.adhere m' te ->
    AdhereConform.conform_exp e (mk_state E m') te
with
mk_state_conform_bexp :
  forall e te E m',
    AdhereConform.bound_bexp e m' ->
    AdhereConform.adhere m' te ->
    AdhereConform.conform_bexp e (mk_state E m') te .
Proof .
  (* mk_state_conform_exp *)
  elim; rewrite /= .
  - move => v te E m' Hmem Had .
    elim : (Had _ Hmem) => ls [Hfind Hsize] .
    rewrite (eqP Hsize) (mk_state_find _ Hfind) -size_lits_as_bits // .
  - done .
  - elim => /= [e IHe te E m' Hbound Had |
                e IHe te E m' Hbound Had |
                i j e IHe te E m' Hbound Had |
                n e IHe te E m' Hbound Had |
                n e IHe te E m' Hbound Had |
                n e IHe te E m' Hbound Had |
                n e IHe te E m' Hbound Had];
              exact : (IHe _ _ _ Hbound Had) .
  - elim => /= e0 IH0 e1 IH1 te E m' /andP [Hbound0 Hbound1] Had;
      rewrite (IH0 _ _ _ Hbound0 Had) (IH1 _ _ _ Hbound1 Had) // .
  - move => c e0 IH0 e1 IH1 te E m' /andP [/andP [Hboundc Hbound0] Hbound1] Had .
    rewrite (mk_state_conform_bexp c _ _ _ Hboundc Had)
            (IH0 _ _ _ Hbound0 Had) (IH1 _ _ _ Hbound1 Had) // .
  (* mk_state_conform_bexp *)
  elim; rewrite /= .
  - done .
  - done .
  - elim => e0 e1 te E m' /andP [Hbound0 Hbound1] Had;
      rewrite (mk_state_conform_exp e0 _ _ _ Hbound0 Had)
              (mk_state_conform_exp e1 _ _ _ Hbound1 Had) // .
  - move => b IHb te E m'; apply : IHb .
  - move => b0 IH0 b1 IH1 te E m' /andP [Hbound0 Hbound1] Had;
      rewrite (IH0 _ _ _ Hbound0 Had) (IH1 _ _ _ Hbound1 Had) // .
  - move => b0 IH0 b1 IH1 te E m' /andP [Hbound0 Hbound1] Had;
      rewrite (IH0 _ _ _ Hbound0 Had) (IH1 _ _ _ Hbound1 Had) // .
Qed .

Lemma bit_blast_bound_exp :
  forall e te m m' g g' cs' lrs',
    bit_blast_exp te m g e = (m', g', cs', lrs') ->
    AdhereConform.bound_exp e m'
with
bit_blast_bound_bexp :
  forall e te m m' g g' cs' lrs',
    bit_blast_bexp te m g e = (m', g', cs', lrs') ->
    AdhereConform.bound_bexp e m' .
Proof .
  (* bit_blast_bound_exp *)
  elim; rewrite /= .
  - move => v te m m' g g' cs' lrs' .
    case Hf : (SSAVM.find v m) .
    + case => <- _ _ _; exact : (SSAVM.Lemmas.find_some_mem Hf) .
    + dcase (bit_blast_var te g v) => [[[g'0 cs] rs] Hbbr] .
      case => <- _ _ _ .
      exact : SSAVM.Lemmas.mem_add_eq .
  - done .
  - elim => /= [e IHe te m m' g g' cs' lrs' |
                e IHe te m m' g g' cs' lrs' |
                i j e IHe te m m' g g' cs' lrs' |
                n e IHe te m m' g g' cs' lrs' |
                n e IHe te m m' g g' cs' lrs' |
                n e IHe te m m' g g' cs' lrs' |
                n e IHe te m m' g g' cs' lrs'];
      dcase (bit_blast_exp te m g e) => [[[[m1 g1] cs1] ls1] Hbbe] .
    + dcase (bit_blast_not g1 ls1) => [[[gr csr] lsr] Hbbr];
        case => <- _ _ _;
        exact : (IHe _ _ _ _ _ _ _ Hbbe) .
    + dcase (bit_blast_neg g1 ls1) => [[[gr csr] lsr] Hbbr];
        case => <- _ _ _;
        exact : (IHe _ _ _ _ _ _ _ Hbbe) .
    + case => <- _ _ _; exact : (IHe _ _ _ _ _ _ _ Hbbe) .
    + case => <- _ _ _; exact : (IHe _ _ _ _ _ _ _ Hbbe) .
    + case => <- _ _ _; exact : (IHe _ _ _ _ _ _ _ Hbbe) .
    + case => <- _ _ _; exact : (IHe _ _ _ _ _ _ _ Hbbe) .
    + case => <- _ _ _; exact : (IHe _ _ _ _ _ _ _ Hbbe) .
  - elim => /= e0 IH0 e1 IH1 te m m' g g' cs' lrs';
      dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] ls1] Hbbe0];
      dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hbbe1];
      move : (bit_blast_exp_preserve Hbbe0)
             (bit_blast_exp_preserve Hbbe1) => Hmm1 Hm1m2 .
    + dcase (bit_blast_and g2 ls1 ls2) => [[[gr csr] lsr] Hbbr];
      case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_or g2 ls1 ls2) => [[[gr csr] lsr] Hbbr];
      case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_xor g2 ls1 ls2) => [[[gr csr] lsr] Hbbr];
      case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_add g2 ls1 ls2) => [[[gr csr] lsr] Hbbr];
      case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_sub g2 ls1 ls2) => [[[gr csr] lsr] Hbbr];
      case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_mul g2 ls1 ls2) => [[[gr csr] lsr] Hbbr];
      case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_shl g2 ls1 ls2) => [[[gr csr] lsr] Hbbr];
      case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_lshr g2 ls1 ls2) => [[[gr csr] lsr] Hbbr];
      case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_ashr g2 ls1 ls2) => [[[gr csr] lsr] Hbbr];
      case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
  - move => c e0 IH0 e1 IH1 te m m' g g' cs' lrs' .
    dcase (bit_blast_bexp te m g c) => [[[[mc gc] csc] lc] Hbbc] .
    dcase (bit_blast_exp te mc gc e0) => [[[[m1 g1] cs1] ls1] Hbb0] .
    dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hbb1] .
    dcase (bit_blast_ite g2 lc ls1 ls2) => [[[gr csr] lsr] Hbbr] .
    case => <- _ _ _ .
    move : (bit_blast_exp_preserve Hbb0)
           (bit_blast_exp_preserve Hbb1) => Hmcm1 Hm1m2 .
    move : (vm_preserve_trans Hmcm1 Hm1m2) => Hmcm2 .
    rewrite (vm_preserve_bound_bexp (bit_blast_bound_bexp c _ _ _ _ _ _ _ Hbbc) Hmcm2)
            (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbb0) Hm1m2)
            (IH1 _ _ _ _ _ _ _ Hbb1) // .
  (* bit_blast_bound_bexp *)
  elim; rewrite /= .
  - done .
  - done .
  - elim => /= e0 e1 te m m' g g' cs' lrs';
      dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] ls1] Hbbe0];
      dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hbbe1];
      move : (bit_blast_exp_preserve Hbbe1) => Hm1m2 .
    + dcase (bit_blast_eq g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_ult g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_ule g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_ugt g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_uge g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_slt g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_sle g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_sgt g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_sge g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_uaddo g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_usubo g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_umulo g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_saddo g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_ssubo g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_smulo g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
  - move => c IHc te m m' g g' cs' lrs' .
    dcase (bit_blast_bexp te m g c) => [[[[m1 g1] cs1] l1] Hbbc] .
    case => <- _ _ _ ; rewrite (IHc _ _ _ _ _ _ _ Hbbc) // .
  - move => b0 IH0 b1 IH1 te m m' g g' cs' lrs' .
    dcase (bit_blast_bexp te m g b0) => [[[[m1 g1] cs1] l1] Hbb0] .
    dcase (bit_blast_bexp te m1 g1 b1) => [[[[m2 g2] cs2] l2] Hbb1] .
    case => <- _ _ _ .
    move : (bit_blast_bexp_preserve Hbb1) => Hm1m2 .
    rewrite (vm_preserve_bound_bexp (IH0 _ _ _ _ _ _ _ Hbb0) Hm1m2)
            (IH1 _ _ _ _ _ _ _ Hbb1) // .
  - move => b0 IH0 b1 IH1 te m m' g g' cs' lrs' .
    dcase (bit_blast_bexp te m g b0) => [[[[m1 g1] cs1] l1] Hbb0] .
    dcase (bit_blast_bexp te m1 g1 b1) => [[[[m2 g2] cs2] l2] Hbb1] .
    case => <- _ _ _ .
    move : (bit_blast_bexp_preserve Hbb1) => Hm1m2 .
    rewrite (vm_preserve_bound_bexp (IH0 _ _ _ _ _ _ _ Hbb0) Hm1m2)
            (IH1 _ _ _ _ _ _ _ Hbb1) // .
Qed .

(* ===== Soundness and completeness ===== *)

Lemma valid_implies_unsat :
  forall premises goal,
    (forall E, ~~ interp_cnf E (add_prelude premises) || interp_lit E goal) ->
    ~ (sat (add_prelude ([::neg_lit goal]::premises))).
Proof.
  move=> premises goal H1 [E H2]. move: (H1 E) => {H1} H1.
  rewrite add_prelude_cons in H2. move/andP: H2 => [H2 H3].
  move/orP: H1. case => H1.
  - move/negP: H1. apply. exact: H3.
  - rewrite add_prelude_expand in H2. move/andP: H2 => [_ H2].
    rewrite /= interp_lit_neg_lit in H2. move/negP: H2; apply.
    rewrite H1 // .
Qed.

Lemma unsat_implies_valid :
  forall premises goal,
    ~ (sat (add_prelude ([::neg_lit goal]::premises))) ->
    (forall E, ~~ interp_cnf E (add_prelude premises) || interp_lit E goal).
Proof.
  move=> premises goal H E. case Hgoal: (interp_lit E goal).
  - by rewrite orbT.
  - rewrite orbF. apply/negP => H2. apply: H. exists E.
    rewrite add_prelude_cons H2 /= .
    rewrite add_prelude_expand /=  interp_lit_neg_lit.
    rewrite Hgoal /= . move : (add_prelude_tt H2) => Htt .
    rewrite /interp_lit /lit_tt in Htt .
    rewrite Htt // .
Qed.


(* NOTE: change valid e to
      forall s, conform s te -> QFBV.eval_bexp e s
 *)
Theorem bit_blast_sound :
  forall (e : QFBV.bexp) te m' g' cs lr,
    bit_blast_bexp te init_vm init_gen e = (m', g', cs, lr) ->
    QFBV.well_formed_bexp e te ->
    ~ (sat (add_prelude ([::neg_lit lr]::cs))) ->
    (forall s,
        AdhereConform.conform_bexp e s te ->
        QFBV.eval_bexp e s) .
Proof.
  move=> e te m' g' cs lr Hblast Hwf Hsat s Hcf.
  move: (unsat_implies_valid Hsat) => {Hsat} Hsat.
  move: (Hsat (mk_env s e)) => {Hsat} Hsat.
  move: (mk_env_sat Hblast Hcf Hwf) => Hcs. move: (mk_env_tt s e) => Htt.
  have Hprelude: interp_cnf (mk_env s e) (add_prelude cs)
    by rewrite add_prelude_expand Hcs Htt.
  move: ((bit_blast_bexp_correct Hblast Hcf (mk_env_consistent Hblast Hcf Hwf) Hprelude) Hwf).
  rewrite /enc_bit. move=> /eqP <-.
  rewrite Hprelude /= in Hsat. exact: Hsat.
Qed.

Theorem bit_blast_complete :
  forall (e : QFBV.bexp) te m' g' cs lr,
    bit_blast_bexp te init_vm init_gen e = (m', g', cs, lr) ->
    QFBV.well_formed_bexp e te ->
    (forall s, AdhereConform.conform_bexp e s te ->
               QFBV.eval_bexp e s)
    ->
    ~ (sat (add_prelude ([::neg_lit lr]::cs))).
Proof.
  move=> e te m' g' cs lr Hblast Hwf He.
  move=> [E Hcs].
  rewrite add_prelude_cons in Hcs. move/andP: Hcs => [Hlr Hcs].
  rewrite add_prelude_expand in Hlr. move/andP: Hlr => [Htt Hlr].
  rewrite /= interp_lit_neg_lit in Hlr.
  have init_vm_adhere : (AdhereConform.adhere init_vm te) .
  { done . }
  move : (bit_blast_adhere_bexp init_vm_adhere Hblast) => Hadm' .
  move : (bit_blast_bound_bexp Hblast) => Hbound .
  move : (mk_state_conform_bexp E Hbound Hadm') => Hcf .
  move : (He (mk_state E m') Hcf) => {He} He .
  move: (bit_blast_bexp_correct Hblast Hcf (mk_state_consistent E m') Hcs Hwf).
  rewrite /enc_bit => /eqP H. rewrite -H in He.
  rewrite He in Hlr. exact: not_false_is_true.
Qed.

Definition bexp_to_cnf te e :=
  let '(m', g', cs, lr) := bit_blast_bexp te init_vm init_gen e in
  add_prelude ([::neg_lit lr]::cs).
