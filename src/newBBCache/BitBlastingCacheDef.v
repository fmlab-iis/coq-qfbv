From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport.
From newBBCache Require Import Cache.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ==== bit-blasting via two functions/phases ==== *)

(* First, bit-blasting and update the historical tables het and hbt *)

Fixpoint update_het te m ca g e : vm * cache * generator * word :=
  (* = update_het_nocache = *)
  let update_het_nocache te m ca g e : vm * cache * generator * cnf * word :=
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
         | QFBV.Unot => let '(m1, ca1, g1, ls1) := update_het te m ca g e1 in
                        let '(gr, csr, lsr) := bit_blast_not g1 ls1 in
                        (m1, ca1, gr, csr, lsr)
         | QFBV.Uneg => let '(m1, ca1, g1, ls1) := update_het te m ca g e1 in
                        let '(gr, csr, lsr) := bit_blast_neg g1 ls1 in
                        (m1, ca1, gr, csr, lsr)
         | QFBV.Uextr i j => let: (m', ca', ge, lse) := update_het te m ca g e1 in
                             let: (g', cs, ls') := bit_blast_extract ge i j lse in
                             (m', ca', g', cs, ls')
         | QFBV.Uhigh n => let: (m', ca', ge, lse) := update_het te m ca g e1 in
                           let: (g', cs, ls') := bit_blast_high ge n lse in
                           (m', ca', g', cs, ls')
         | QFBV.Ulow n => let: (m', ca', ge, lse) := update_het te m ca g e1 in
                          let: (g', cs, ls') := bit_blast_low ge n lse in
                          (m', ca', g', cs, ls')
         | QFBV.Uzext n =>  let '(m', ca', ge, lse) := update_het te m ca g e1 in
                            let '(g', cs, ls) := bit_blast_zeroextend n ge lse in
                            (m', ca', g', cs, ls)
         | QFBV.Usext n =>  let: (m', ca', ge, lse) := update_het te m ca g e1 in
                            let: (g', cs, ls) := bit_blast_signextend n ge lse in
                            (m', ca', g', cs, ls)
         end)
      | QFBV.Ebinop op e1 e2 =>
        (match op with
         | QFBV.Band => let '(m1, ca1, g1, ls1) := update_het te m ca g e1 in
                        let '(m2, ca2, g2, ls2) := update_het te m1 ca1 g1 e2 in
                        let '(gr, csr, lsr) := bit_blast_and g2 ls1 ls2 in
                        (m2, ca2, gr, csr, lsr)
         | QFBV.Bor => let '(m1, ca1, g1, rs1) := update_het te m ca g e1 in
                       let '(m2, ca2, g2, rs2) := update_het te m1 ca1 g1 e2 in
                       let '(g', cs, rs) := bit_blast_or g2 rs1 rs2 in
                       (m2, ca2, g', cs, rs)
         | QFBV.Bxor => let '(m1, ca1, g1, ls1) := update_het te m ca g e1 in
                        let '(m2, ca2, g2, ls2) := update_het te m1 ca1 g1 e2 in
                        let '(gr, csr, lsr) := bit_blast_xor g2 ls1 ls2 in
                        (m2, ca2, gr, csr, lsr)
         | QFBV.Badd => let '(m1, ca1, g1, rs1) := update_het te m ca g e1 in
                        let '(m2, ca2, g2, rs2) := update_het te m1 ca1 g1 e2 in
                        let '(g', cs, rs) := bit_blast_add g2 rs1 rs2 in
                        (m2, ca2, g', cs, rs)
         | QFBV.Bsub => let '(m1, ca1, g1, rs1) := update_het te m ca g e1 in
                        let '(m2, ca2, g2, rs2) := update_het te m1 ca1 g1 e2 in
                        let '(g', cs, rs) := bit_blast_sub g2 rs1 rs2 in
                        (m2, ca2, g', cs, rs)
         | QFBV.Bmul => let '(m1, ca1, g1, rs1) := update_het te m ca g e1 in
                        let '(m2, ca2, g2, rs2) := update_het te m1 ca1 g1 e2 in
                        let '(g', cs, rs) := bit_blast_mul g2 rs1 rs2 in
                        (m2, ca2, g', cs, rs)
         | QFBV.Bmod => let '(m1, ca1, g1, rs1) := update_het te m ca g e1 in (* TODO *)
                        let '(m2, ca2, g2, rs2) := update_het te m1 ca1 g1 e2 in
                        (m2, ca2, g2, [::], rs1)
         | QFBV.Bsrem => let '(m1, ca1, g1, rs1) := update_het te m ca g e1 in (* TODO *)
                         let '(m2, ca2, g2, rs2) := update_het te m1 ca1 g1 e2 in
                         (m2, ca2, g2, [::], rs1)
         | QFBV.Bsmod => let '(m1, ca1, g1, rs1) := update_het te m ca g e1 in (* TODO *)
                         let '(m2, ca2, g2, rs2) := update_het te m1 ca1 g1 e2 in
                         (m2, ca2, g2, [::], rs1)
         | QFBV.Bshl => let: (m1, ca1, g1, ls1) := update_het te m ca g e1 in
                        let: (m', ca2, g2, ls2) := update_het te m1 ca1 g1 e2 in
                        let: (g', cs, ls) := bit_blast_shl g2 ls1 ls2 in
                        (m', ca2, g', cs, ls)
         | QFBV.Blshr => let: (m1, ca1, g1, ls1) := update_het te m ca g e1 in
                         let: (m', ca2, g2, ls2) := update_het te m1 ca1 g1 e2 in
                         let: (g', cs, ls) := bit_blast_lshr g2 ls1 ls2 in
                         (m', ca2, g', cs, ls)
         | QFBV.Bashr => let: (m1, ca1, g1, ls1) := update_het te m ca g e1 in
                         let: (m', ca2, g2, ls2) := update_het te m1 ca1 g1 e2 in
                         let: (g', cs, ls) := bit_blast_ashr g2 ls1 ls2 in
                         (m', ca2, g', cs, ls)
         | QFBV.Bconcat => let '(m1, ca1, g1, rs1) := update_het te m ca g e1 in
                           let '(m', ca2, g2, rs2) := update_het te m1 ca1 g1 e2 in
                           let '(g', cs, rs) := bit_blast_concat g2 rs1 rs2 in
                           (m', ca2, g', cs, rs)
     end)
      | QFBV.Eite c e1 e2 => let '(mc, cac, gc, lc) := update_hbt te m ca g c in
                             let '(m1, ca1, g1, ls1) := update_het te mc cac gc e1 in
                             let '(m2, ca2, g2, ls2) := update_het te m1 ca1 g1 e2 in
                             let '(gr, csr, lsr) := bit_blast_ite g2 lc ls1 ls2 in
                             (m2, ca2, gr, csr, lsr)
      end
      (* = = *)
  in
  match Cache.find_het e ca with
  | Some (cs, ls) => (m, ca, g, ls)
  | None => let '(m', ca', g', cs, lrs) := update_het_nocache te m ca g e in
            (m', Cache.add_het e cs lrs ca', g', lrs)
  end
with
update_hbt te m ca g e : vm * cache * generator * literal :=
  (* = update_hbt_nocache = *)
  let update_hbt_nocache te m ca g e : vm * cache * generator * cnf * literal :=
      match e with
      | QFBV.Bfalse => (m, ca, g, [::], lit_ff)
      | QFBV.Btrue => (m, ca, g, [::], lit_tt)
      | QFBV.Bbinop op e1 e2 =>
        (match op with
         | QFBV.Beq => let '(m1, ca1, g1, ls1) := update_het te m ca g e1 in
                       let '(m2, ca2, g2, ls2) := update_het te m1 ca1 g1 e2 in
                       let '(g', cs, r) := bit_blast_eq g2 ls1 ls2 in
                       (m2, ca2, g', cs, r)
         | QFBV.Bult => let '(m1, ca1, g1, ls1) := update_het te m ca g e1 in
                        let '(m2, ca2, g2, ls2) := update_het te m1 ca1 g1 e2 in
                        let '(g', cs, r) := bit_blast_ult g2 ls1 ls2 in
                        (m2, ca2, g', cs, r)
         | QFBV.Bule => let '(m1, ca1, g1, ls1) := update_het te m ca g e1 in
                        let '(m2, ca2, g2, ls2) := update_het te m1 ca1 g1 e2 in
                        let '(g', cs, r) := bit_blast_ule g2 ls1 ls2 in
                        (m2, ca2, g', cs, r)
         | QFBV.Bugt => let '(m1, ca1, g1, ls1) := update_het te m ca g e1 in
                        let '(m2, ca2, g2, ls2) := update_het te m1 ca1 g1 e2 in
                        let '(g', cs, r) := bit_blast_ugt g2 ls1 ls2 in
                        (m2, ca2, g', cs, r)
         | QFBV.Buge => let '(m1, ca1, g1, ls1) := update_het te m ca g e1 in
                        let '(m2, ca2, g2, ls2) := update_het te m1 ca1 g1 e2 in
                        let '(g', cs, r) := bit_blast_uge g2 ls1 ls2 in
                        (m2, ca2, g', cs, r)
         | QFBV.Bslt => let '(m1, ca1, g1, ls1) := update_het te m ca g e1 in
                        let '(m2, ca2, g2, ls2) := update_het te m1 ca1 g1 e2 in
                        let '(gr, csr, lr) := bit_blast_slt g2 ls1 ls2 in
                        (m2, ca2, gr, csr, lr)
         | QFBV.Bsle => let '(m1, ca1, g1, ls1) := update_het te m ca g e1 in
                        let '(m2, ca2, g2, ls2) := update_het te m1 ca1 g1 e2 in
                        let '(gr, csr, lr) := bit_blast_sle g2 ls1 ls2 in
                        (m2, ca2, gr, csr, lr)
         | QFBV.Bsgt => let '(m1, ca1, g1, ls1) := update_het te m ca g e1 in
                        let '(m2, ca2, g2, ls2) := update_het te m1 ca1 g1 e2 in
                        let '(gr, csr, lr) := bit_blast_sgt g2 ls1 ls2 in
                        (m2, ca2, gr, csr, lr)
         | QFBV.Bsge => let '(m1, ca1, g1, ls1) := update_het te m ca g e1 in
                        let '(m2, ca2, g2, ls2) := update_het te m1 ca1 g1 e2 in
                        let '(gr, csr, lr) := bit_blast_sge g2 ls1 ls2 in
                        (m2, ca2, gr, csr, lr)
         | QFBV.Buaddo => let '(m1, ca1, g1, rs1) := update_het te m ca g e1 in
                          let '(m2, ca2, g2, rs2) := update_het te m1 ca1 g1 e2 in
                          let '(g', cs, lr) := bit_blast_uaddo g2 rs1 rs2 in
                          (m2, ca2, g', cs, lr)
         | QFBV.Busubo => let '(m1, ca1, g1, rs1) := update_het te m ca g e1 in
                          let '(m2, ca2, g2, rs2) := update_het te m1 ca1 g1 e2 in
                          let '(g', cs, lr) := bit_blast_usubo g2 rs1 rs2 in
                          (m2, ca2, g', cs, lr)
         | QFBV.Bumulo => let '(m1, ca1, g1, rs1) := update_het te m ca g e1 in
                          let '(m2, ca2, g2, rs2) := update_het te m1 ca1 g1 e2 in
                          let '(g', cs, lr) := bit_blast_umulo g2 rs1 rs2 in
                          (m2, ca2, g', cs, lr)
         | QFBV.Bsaddo => let '(m1, ca1, g1, ls1) := update_het te m ca g e1 in
                          let '(m2, ca2, g2, ls2) := update_het te m1 ca1 g1 e2 in
                          let '(gr, csr, lr) := bit_blast_saddo g2 ls1 ls2 in
                          (m2, ca2, gr, csr, lr)
         | QFBV.Bssubo => let '(m1, ca1, g1, ls1) := update_het te m ca g e1 in
                          let '(m2, ca2, g2, ls2) := update_het te m1 ca1 g1 e2 in
                          let '(gr, csr, lr) := bit_blast_ssubo g2 ls1 ls2 in
                          (m2, ca2, gr, csr, lr)
         | QFBV.Bsmulo => let '(m1, ca1, g1, ls1) := update_het te m ca g e1 in
                          let '(m2, ca2, g2, ls2) := update_het te m1 ca1 g1 e2 in
                          let '(gr, csr, lr) := bit_blast_smulo g2 ls1 ls2 in
                          (m2, ca2, gr, csr, lr)
         end)
      | QFBV.Blneg e => let '(m1, ca1, g1, l1) := update_hbt te m ca g e in
                        let '(g', cs, r) := bit_blast_lneg g1 l1 in
                        (m1, ca1, g', cs, r)
      | QFBV.Bconj e1 e2 => let '(m1, ca1, g1, l1) := update_hbt te m ca g e1 in
                            let '(m2, ca2, g2, l2) := update_hbt te m1 ca1 g1 e2 in
                            let '(g', cs, r) := bit_blast_conj g2 l1 l2 in
                            (m2, ca2, g', cs, r)
      | QFBV.Bdisj e1 e2 => let '(m1, ca1, g1, l1) := update_hbt te m ca g e1 in
                            let '(m2, ca2, g2, l2) := update_hbt te m1 ca1 g1 e2 in
                            let '(g', cs, r) := bit_blast_disj g2 l1 l2 in
                            (m2, ca2, g', cs, r)
      end
  (* = = *)
  in
  match Cache.find_hbt e ca with
  | Some (cs, l) => (m, ca, g, l)
  | None => let '(m', ca', g', cs, lr) := update_hbt_nocache te m ca g e in
            (m', Cache.add_hbt e cs lr ca', g', lr)
  end.

(* Second, look up het & hbt to get the final CNF, while updating current tables cet & cbt *)

Fixpoint update_cet ca e : cache * cnf * word :=
  (* = update_cet_nocache = *)
  let update_cet_nocache ca e : cache * cnf * word :=
      match e with
      | QFBV.Evar _
      | QFBV.Econst _ => let '(cs, ls) := get_het e ca in
                          (ca, cs, ls)
      | QFBV.Eunop op e1 => let '(ca1, cs1, ls1) := update_cet ca e1 in
                            let '(csop, lsop) := get_het e ca1 in
                            (ca1, catrev cs1 csop, lsop)
      | QFBV.Ebinop op e1 e2 => let '(ca1, cs1, ls1) := update_cet ca e1 in
                                let '(ca2, cs2, ls2) := update_cet ca1 e2 in
                                let '(csop, lsop) := get_het e ca2 in
                                (ca2, catrev cs1 (catrev cs2 csop), lsop)
      | QFBV.Eite c e1 e2 => let '(cac, csc, lc) := update_cbt ca c in
                             let '(ca1, cs1, ls1) := update_cet cac e1 in
                             let '(ca2, cs2, ls2) := update_cet ca1 e2 in
                             let '(csop, lsop) := get_het e ca2 in
                             (ca2, catrev csc (catrev cs1 (catrev cs2 csop)), lsop)
      end
  (* = = *)
  in
  match Cache.find_cet e ca with
  | Some ls => (ca, [::], ls)
  | None => let '(ca', cs, lrs) := update_cet_nocache ca e in
            (Cache.add_cet e lrs ca', cs, lrs)
  end
with
update_cbt ca e : cache * cnf * literal :=
  (* = update_cbt_nocache = *)
  let update_cbt_nocache ca e : cache * cnf * literal :=
      match e with
      | QFBV.Bfalse
      | QFBV.Btrue => let '(cs, l) := get_hbt e ca in
                      (ca, cs, l)
      | QFBV.Bbinop op e1 e2 => let '(ca1, cs1, ls1) := update_cet ca e1 in
                                let '(ca2, cs2, ls2) := update_cet ca1 e2 in
                                let '(csop, lop) := get_hbt e ca2 in
                                (ca2, catrev cs1 (catrev cs2 csop), lop)
      | QFBV.Blneg e => let '(ca1, cs1, l1) := update_cbt ca e in
                        let '(csop, lop) := get_hbt e ca1 in 
                        (ca1, catrev cs1 csop, lop)
      | QFBV.Bconj e1 e2 
      | QFBV.Bdisj e1 e2 => let '(ca1, cs1, l1) := update_cbt ca e1 in
                            let '(ca2, cs2, l2) := update_cbt ca1 e2 in
                            let '(csop, lop) := get_hbt e ca2 in
                            (ca2, catrev cs1 (catrev cs2 csop), lop)
      end
  (* = = *)
  in
  match Cache.find_cbt e ca with
  | Some l => (ca, [::], l)
  | None => let '(ca', cs, lr) := update_cbt_nocache ca e in
            (Cache.add_cbt e lr ca', cs, lr)
  end.

(* the bit-blasting functions are combined with the above two phases *)

Definition bit_blast_exp_two te m ca g e : vm * cache * generator * cnf * word :=
  let '(mh, cah, gh, _) := update_het te m ca g e in
  let '(cac, cs, lrs) := update_cet cah e in
  (mh, cac, gh, cs, lrs).

Definition bit_blast_bexp_two te m ca g e : vm * cache * generator * cnf * literal :=
  let '(mh, cah, gh, _) := update_hbt te m ca g e in
  let '(cac, cs, lr) := update_cbt cah e in
  (mh, cac, gh, cs, lr).


    

(* ==== bit-blasting via only one function ==== *)

(* this method updates historical tables and current tables at the same time when 
traversing the expression *)

Fixpoint bit_blast_exp_one te m ca g e : vm * cache * generator * cnf * word :=
  (* = bit_blast_exp_nocet = *)
  let bit_blast_exp_nocet te m ca g e : vm * cache * generator * cnf * word :=
      match e with
      | QFBV.Evar v =>
        match find_het e ca with
        | Some (cs, ls) => (m, ca, g, cs, ls)
        | None => match SSAVM.find v m with
                  | None => let '(g', cs, rs) := bit_blast_var te g v in
                            (SSAVM.add v rs m, add_het e cs rs ca, g', cs, rs)
                  | Some rs => (m, add_het e [::] rs ca, g, [::], rs)
                  end
        end
      | QFBV.Econst bs => 
        match find_het e ca with
        | Some (cs, ls) => (m, ca, g, cs, ls)
        | None => let '(g', cs, rs) := bit_blast_const g bs in
                  (m, add_het e cs rs ca, g', cs, rs)
        end
      | QFBV.Eunop op e1 =>
        let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_one te m ca g e1 in
        match find_het e ca1 with
        | Some (csop, lsop) => (m1, ca1, g1, catrev cs1 csop, lsop)
        | None =>
          let '(gop, csop, lsop) := match op with
                                    | QFBV.Unot => bit_blast_not g1 ls1
                                    | QFBV.Uneg => bit_blast_neg g1 ls1
                                    | QFBV.Uextr i j => bit_blast_extract g1 i j ls1
                                    | QFBV.Uhigh n => bit_blast_high g1 n ls1 
                                    | QFBV.Ulow n => bit_blast_low g1 n ls1
                                    | QFBV.Uzext n => bit_blast_zeroextend n g1 ls1
                                    | QFBV.Usext n => bit_blast_signextend n g1 ls1
                                    end 
          in
          (m1, add_het e csop lsop ca1, gop, catrev cs1 csop, lsop)
        end
      | QFBV.Ebinop op e1 e2 =>
        let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_one te m ca g e1 in
        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_one te m1 ca1 g1 e2 in
        match find_het e ca2 with
        | Some (csop, lsop) => (m2, ca2, g2, catrev cs1 (catrev cs2 csop), lsop)
        | None => 
          let '(gop, csop, lsop) := match op with
                                    | QFBV.Band => bit_blast_and g2 ls1 ls2
                                    | QFBV.Bor => bit_blast_or g2 ls1 ls2
                                    | QFBV.Bxor => bit_blast_xor g2 ls1 ls2
                                    | QFBV.Badd => bit_blast_add g2 ls1 ls2
                                    | QFBV.Bsub => bit_blast_sub g2 ls1 ls2
                                    | QFBV.Bmul => bit_blast_mul g2 ls1 ls2
                                    | QFBV.Bmod => (g2, [::], ls1) (* TODO *)
                                    | QFBV.Bsrem => (g2, [::], ls1) (* TODO *)
                                    | QFBV.Bsmod => (g2, [::], ls1) (* TODO *)
                                    | QFBV.Bshl => bit_blast_shl g2 ls1 ls2
                                    | QFBV.Blshr => bit_blast_lshr g2 ls1 ls2
                                    | QFBV.Bashr => bit_blast_ashr g2 ls1 ls2
                                    | QFBV.Bconcat => bit_blast_concat g2 ls1 ls2
                                    end
          in
          (m2, add_het e csop lsop ca2, gop, catrev cs1 (catrev cs2 csop), lsop)
        end
      | QFBV.Eite c e1 e2 => 
        let '(mc, cac, gc, csc, lc) := bit_blast_bexp_one te m ca g c in
        let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_one te mc cac gc e1 in
        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_one te m1 ca1 g1 e2 in
        match find_het e ca2 with
        | Some (csop, lsop) => 
          (m2, ca2, g2, catrev csc (catrev cs1 (catrev cs2 csop)), lsop)
        | None => 
          let '(gop, csop, lsop) := bit_blast_ite g2 lc ls1 ls2 in
          (m2, add_het e csop lsop ca2, gop, 
           catrev csc (catrev cs1 (catrev cs2 csop)), lsop)
        end
      end
  (* = = *)
  in
  match Cache.find_cet e ca with
  | Some ls => (m, ca, g, [::], ls)
  | None => let '(m', ca', g', cs, lrs) := bit_blast_exp_nocet te m ca g e in
            (m', Cache.add_cet e lrs ca', g', cs, lrs)
  end
with
bit_blast_bexp_one te m ca g e : vm * cache * generator * cnf * literal :=
  (* = bit_blast_bexp_nocbt = *)
  let bit_blast_bexp_nocbt te m ca g e : vm * cache * generator * cnf * literal :=
      match e with
      | QFBV.Bfalse => 
        match find_hbt e ca with
        | Some (cs, l) => (m, ca, g, cs, l)
        | None => (m, add_hbt e [::] lit_ff ca, g, [::], lit_ff)
        end
      | QFBV.Btrue => 
        match find_hbt e ca with
        | Some (cs, l) => (m, ca, g, cs, l)
        | None => (m, add_hbt e [::] lit_tt ca, g, [::], lit_tt)
        end
      | QFBV.Bbinop op e1 e2 =>
        let '(m1, ca1, g1, cs1, ls1) := bit_blast_exp_one te m ca g e1 in
        let '(m2, ca2, g2, cs2, ls2) := bit_blast_exp_one te m1 ca1 g1 e2 in
        match find_hbt e ca2 with
        | Some (csop, lop) => (m2, ca2, g2, catrev cs1 (catrev cs2 csop), lop)
        | None => 
          let '(gop, csop, lop) := match op with
                                   | QFBV.Beq => bit_blast_eq g2 ls1 ls2
                                   | QFBV.Bult => bit_blast_ult g2 ls1 ls2
                                   | QFBV.Bule => bit_blast_ule g2 ls1 ls2
                                   | QFBV.Bugt => bit_blast_ugt g2 ls1 ls2
                                   | QFBV.Buge => bit_blast_uge g2 ls1 ls2
                                   | QFBV.Bslt => bit_blast_slt g2 ls1 ls2
                                   | QFBV.Bsle => bit_blast_sle g2 ls1 ls2
                                   | QFBV.Bsgt => bit_blast_sgt g2 ls1 ls2
                                   | QFBV.Bsge => bit_blast_sge g2 ls1 ls2
                                   | QFBV.Buaddo => bit_blast_uaddo g2 ls1 ls2
                                   | QFBV.Busubo => bit_blast_usubo g2 ls1 ls2
                                   | QFBV.Bumulo => bit_blast_umulo g2 ls1 ls2
                                   | QFBV.Bsaddo => bit_blast_saddo g2 ls1 ls2
                                   | QFBV.Bssubo => bit_blast_ssubo g2 ls1 ls2
                                   | QFBV.Bsmulo => bit_blast_smulo g2 ls1 ls2
                                   end
          in
          (m2, add_hbt e csop lop ca2, gop, catrev cs1 (catrev cs2 csop), lop)
        end
      | QFBV.Blneg e1 => 
        let '(m1, ca1, g1, cs1, l1) := bit_blast_bexp_one te m ca g e1 in
        match find_hbt e ca1 with
        | Some (csop, lop) => (m1, ca1, g1, catrev cs1 csop, lop)
        | None => let '(gop, csop, lop) := bit_blast_lneg g1 l1 in
                  (m1, add_hbt e csop lop ca1, gop, catrev cs1 csop, lop)
        end
      | QFBV.Bconj e1 e2 => 
        let '(m1, ca1, g1, cs1, l1) := bit_blast_bexp_one te m ca g e1 in
        let '(m2, ca2, g2, cs2, l2) := bit_blast_bexp_one te m1 ca1 g1 e2 in
        match find_hbt e ca2 with
        | Some (csop, lop) => (m2, ca2, g2, catrev cs1 (catrev cs2 csop), lop)
        | None => let '(gop, csop, lop) := bit_blast_conj g2 l1 l2 in
                  (m2, add_hbt e csop lop ca2, gop, 
                   catrev cs1 (catrev cs2 csop), lop)
        end
      | QFBV.Bdisj e1 e2 => 
        let '(m1, ca1, g1, cs1, l1) := bit_blast_bexp_one te m ca g e1 in
        let '(m2, ca2, g2, cs2, l2) := bit_blast_bexp_one te m1 ca1 g1 e2 in
        match find_hbt e ca2 with
        | Some (csop, lop) => (m2, ca2, g2, catrev cs1 (catrev cs2 csop), lop)
        | None => let '(gop, csop, lop) := bit_blast_disj g2 l1 l2 in
                  (m2, add_hbt e csop lop ca2, gop, 
                   catrev cs1 (catrev cs2 csop), lop)
        end
      end
  (* = = *)
  in
  match Cache.find_cbt e ca with
  | Some l => (m, ca, g, [::], l)
  | None => let '(m', ca', g', cs, lr) := bit_blast_bexp_nocbt te m ca g e in
            (m', Cache.add_cbt e lr ca', g', cs, lr)
  end.

