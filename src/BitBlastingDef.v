From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport .

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
