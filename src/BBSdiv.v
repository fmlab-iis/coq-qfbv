From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBConst BBXor BBEq BBZeroExtend BBNeg BBAnd BBAdd BBShl BBSub BBMul BBAshr BBUge BBUdiv BBLneg.
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_abs ===== *)

Definition bit_blast_abs g ls : generator * cnf * word :=
  let (ls_tl, ls_sign) := eta_expand (splitmsl ls) in
  if (ls_sign == lit_tt) then  bit_blast_neg g ls
  else if (ls_sign == lit_ff) then (g, [::], ls)
       else let ws := copy (size ls) ls_sign in
            let '(g_xor, cs_xor, rs_xor) := bit_blast_xor g ls ws in
            let '(g_zext, cs_zext, rs_zext) := bit_blast_zeroextend (size ls_tl) g_xor (ls_sign::nil) in 
            let '(g_add, cs_add, rs_add) := bit_blast_add g_zext rs_xor rs_zext in
            (g_add, catrev (catrev cs_xor cs_zext) cs_add, rs_add).

Definition mk_env_abs E g ls : env * generator * cnf * word :=
  let (ls_tl, ls_sign) := eta_expand (splitmsl ls) in
  if (ls_sign == lit_tt) then  mk_env_neg E g ls
  else if (ls_sign == lit_ff) then (E, g, [::], ls)
       else let ws := copy (size ls) ls_sign in
            let '(E_xor, g_xor, cs_xor, rs_xor) := mk_env_xor E g ls ws in
            let '(E_zext, g_zext, cs_zext, rs_zext) := mk_env_zeroextend (size ls_tl) E_xor g_xor (ls_sign::nil) in 
            let '(E_add, g_add, cs_add, rs_add) := mk_env_add E_zext g_zext rs_xor rs_zext in
            (E_add, g_add, catrev (catrev cs_xor cs_zext) cs_add, rs_add).

Lemma mk_env_abs_newer_gen :
  forall E g ls E' g' cs lrs,
    mk_env_abs E g ls = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move=> E g ls E' g' cs lrs. rewrite /mk_env_abs.
  case ((splitmsl ls).2 == lit_tt); last case ((splitmsl ls).2 == lit_ff).
  - exact: mk_env_neg_newer_gen.
  - case=> _ <- _ _. by rewrite Pos.leb_refl.
  - dcase (mk_env_xor E g ls (copy (size ls) (splitmsl ls).2)) 
    => [[[[E_xor] g_xor] cs_xor] lrs_xor] Hmkxor.
    dcase (mk_env_zeroextend (size (splitmsl ls).1) E_xor g_xor [:: (splitmsl ls).2])
    => [[[[E_zext] g_zext] cs_zext] lrs_zext] Hmkzext.
    dcase (mk_env_add E_zext g_zext lrs_xor lrs_zext)
    => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    case=> _ <- _ _.
    move: (mk_env_xor_newer_gen Hmkxor) => Hggxor.
    move: (mk_env_zeroextend_newer_gen Hmkzext) => Hgxorgzext.
    move: (mk_env_add_newer_gen Hmkadd) => Hgzextgadd.
    by apply (pos_leb_trans Hggxor); apply (pos_leb_trans Hgxorgzext).
Qed.

Lemma mk_env_abs_newer_res :
  forall E g ls E' g' cs lrs,
    mk_env_abs E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    newer_than_lits g' lrs.
Proof.
  move=> E g ls E' g' cs lrs. rewrite /mk_env_abs.
  case ((splitmsl ls).2 == lit_tt); last case ((splitmsl ls).2 == lit_ff).
  - exact: mk_env_neg_newer_res.
  - by case=> _ <- _ <-. 
  - dcase (mk_env_xor E g ls (copy (size ls) (splitmsl ls).2)) 
    => [[[[E_xor] g_xor] cs_xor] lrs_xor] Hmkxor.
    dcase (mk_env_zeroextend (size (splitmsl ls).1) E_xor g_xor [:: (splitmsl ls).2])
    => [[[[E_zext] g_zext] cs_zext] lrs_zext] Hmkzext.
    dcase (mk_env_add E_zext g_zext lrs_xor lrs_zext)
    => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    case=> _ <- _ <- Hgtt Hgls.
    exact: (mk_env_add_newer_res Hmkadd).
Qed.

Lemma mk_env_abs_newer_cnf :
  forall E g ls E' g' cs lrs,
    mk_env_abs E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    newer_than_cnf g' cs.
Proof.
  move=> E g ls E' g' cs lrs. rewrite /mk_env_abs.
  case ((splitmsl ls).2 == lit_tt); last case ((splitmsl ls).2 == lit_ff).
  - exact: mk_env_neg_newer_cnf.
  - by case=> _ <- <- _. 
  - dcase (mk_env_xor E g ls (copy (size ls) (splitmsl ls).2)) 
    => [[[[E_xor] g_xor] cs_xor] lrs_xor] Hmkxor.
    dcase (mk_env_zeroextend (size (splitmsl ls).1) E_xor g_xor [:: (splitmsl ls).2])
    => [[[[E_zext] g_zext] cs_zext] lrs_zext] Hmkzext.
    dcase (mk_env_add E_zext g_zext lrs_xor lrs_zext)
    => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    case=> _ <- <- _ Hgtt Hgls.
    move: (mk_env_xor_newer_gen Hmkxor) => Hggxor.
    move: (mk_env_zeroextend_newer_gen Hmkzext) => Hgxorgzext.
    move: (mk_env_add_newer_gen Hmkadd) => Hgzextgadd.
    move: (newer_than_lits_msl Hgtt Hgls) => Hgmsl.
    move: (newer_than_lits_copy (size ls) Hgmsl) => Hgcopy.
    move: (mk_env_xor_newer_cnf Hmkxor Hgtt Hgls Hgcopy) => Hgxorcsxor.
    move: (newer_than_cnf_le_newer Hgxorcsxor (pos_leb_trans Hgxorgzext Hgzextgadd)) => Hgaddcsxor.
    move: (newer_than_lit_le_newer Hgtt Hggxor) => Hgxortt.
    move: (newer_than_lit_le_newer Hgmsl Hggxor) => Hgxormsl.
    move: (newer_than_lits_copy 1 Hgxormsl) => Hgxor1msl.
    move: (mk_env_zeroextend_newer_cnf Hmkzext Hgxortt Hgxor1msl) => Hgzextcszext.
    move: (newer_than_cnf_le_newer Hgzextcszext Hgzextgadd) => Hgaddcszext.
    move: (mk_env_xor_newer_res Hmkxor Hgtt Hgls Hgcopy) => Hgxorlxor.
    move: (newer_than_lits_le_newer Hgxorlxor Hgxorgzext) => Hgzextlxor.
    move: (mk_env_zeroextend_newer_res Hmkzext Hgxortt Hgxor1msl) => Hgzextlzext.
    move: (newer_than_lit_le_newer Hgxortt Hgxorgzext) => Hgzexttt.
    rewrite newer_than_lit_tt_ff in Hgzexttt.
    move: (mk_env_add_newer_cnf Hmkadd Hgzextlxor Hgzextlzext Hgzexttt) => Hgaddcsadd.
    by rewrite !newer_than_cnf_catrev Hgaddcsxor Hgaddcszext Hgaddcsadd.
Qed.

Lemma mk_env_abs_preserve :
  forall E g ls E' g' cs lrs,
    mk_env_abs E g ls = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> E g ls E' g' cs lrs. rewrite /mk_env_abs.
  case ((splitmsl ls).2 == lit_tt); last case ((splitmsl ls).2 == lit_ff).
  - exact: mk_env_neg_preserve.
  - by case=> <- _ _ _. 
  - dcase (mk_env_xor E g ls (copy (size ls) (splitmsl ls).2)) 
    => [[[[E_xor] g_xor] cs_xor] lrs_xor] Hmkxor.
    dcase (mk_env_zeroextend (size (splitmsl ls).1) E_xor g_xor [:: (splitmsl ls).2])
    => [[[[E_zext] g_zext] cs_zext] lrs_zext] Hmkzext.
    dcase (mk_env_add E_zext g_zext lrs_xor lrs_zext)
    => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    case=> <- _ _ _. 
    move: (mk_env_xor_newer_gen Hmkxor) => Hggxor.
    move: (mk_env_zeroextend_newer_gen Hmkzext) => Hgxorgzext.
    move: (mk_env_add_newer_gen Hmkadd) => Hgzextgadd.
    move: (mk_env_xor_preserve Hmkxor) => HEExorg.
    move: (mk_env_zeroextend_preserve Hmkzext) => HExorEzextgxor.
    move: (mk_env_add_preserve Hmkadd) => HEzextEaddgzext. 
    move: (env_preserve_le HExorEzextgxor Hggxor) => HExorEzextg.
    move: (env_preserve_le HEzextEaddgzext (pos_leb_trans Hggxor Hgxorgzext)) => HEzextEaddg.
    by apply (env_preserve_trans HEExorg); apply (env_preserve_trans HExorEzextg).
Qed.    

Lemma mk_env_abs_sat :
  forall E g ls E' g' cs lrs,
    mk_env_abs E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt -> newer_than_lits g ls -> interp_cnf E' cs.
Proof.
  move => E g ls E' g' cs lrs. rewrite /mk_env_abs.
  case ((splitmsl ls).2 == lit_tt); last case ((splitmsl ls).2 == lit_ff).
  - rewrite newer_than_lit_tt_ff. exact : mk_env_neg_sat.
  - by case => <- _ <- _.
  - dcase (mk_env_xor E g ls (copy (size ls) (splitmsl ls).2)) 
    => [[[[E_xor] g_xor] cs_xor] lrs_xor] Hmkxor.
    dcase (mk_env_zeroextend (size (splitmsl ls).1) E_xor g_xor [:: (splitmsl ls).2])
    => [[[[E_zext] g_zext] cs_zext] lrs_zext] Hmkzext.
    dcase (mk_env_add E_zext g_zext lrs_xor lrs_zext)
    => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    case=> <- _ <- _; rewrite !interp_cnf_catrev => Htt Hgls.
    move : (newer_than_lits_msl Htt Hgls); rewrite /msl => Hmsl.
    generalize Hmsl; move => /newer_than_lits_copy => Hcpmsl.
    move : (mk_env_xor_newer_res Hmkxor Htt Hgls (Hcpmsl (size ls))) => Hgxlx.
    move : (mk_env_xor_sat Hmkxor Htt Hgls (Hcpmsl (size ls))) => HExcsx.
    move : (env_preserve_trans (mk_env_zeroextend_preserve Hmkzext) (env_preserve_le (mk_env_add_preserve Hmkadd) (mk_env_zeroextend_newer_gen Hmkzext))) => HExEagx.
    rewrite (env_preserve_cnf HExEagx (mk_env_xor_newer_cnf Hmkxor Htt Hgls (Hcpmsl (size ls)))) HExcsx.
    move : (mk_env_zeroextend_newer_res Hmkzext (newer_than_lit_le_newer Htt (mk_env_xor_newer_gen Hmkxor))); rewrite (lock splitmsl)/= -lock andbT.
    move => Hgzlz'; move : (Hgzlz' (newer_than_lit_le_newer Hmsl (mk_env_xor_newer_gen Hmkxor))) => Hgzlz{Hgzlz'}.
    move : (mk_env_zeroextend_sat Hmkzext (newer_than_lit_le_newer Htt (mk_env_xor_newer_gen Hmkxor))); rewrite (lock splitmsl)/= -lock andbT => HEzcsz'.
    move : (HEzcsz' (newer_than_lit_le_newer Hmsl (mk_env_xor_newer_gen Hmkxor))) => HEzcsz{HEzcsz'}.
    move : (mk_env_zeroextend_newer_cnf Hmkzext (newer_than_lit_le_newer Htt (mk_env_xor_newer_gen Hmkxor))); rewrite (lock splitmsl) /= -lock andbT => Hgzcsz'.
    move : (Hgzcsz' (newer_than_lit_le_newer Hmsl (mk_env_xor_newer_gen Hmkxor))) => Hgzcsz{Hgzcsz'}.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) Hgzcsz) HEzcsz.
    rewrite (mk_env_add_sat Hmkadd (newer_than_lits_le_newer Hgxlx (mk_env_zeroextend_newer_gen Hmkzext)) Hgzlz (newer_than_lit_le_newer Htt (pos_leb_trans (mk_env_xor_newer_gen Hmkxor) (mk_env_zeroextend_newer_gen Hmkzext))))//.
Qed.    

(* ===== bit_blast_sdiv ===== *)

(* Definition bit_blast_sdiv g ls1 ls2 : generator * cnf * word * word := *)
(*   let (ls1_tl, ls1_sign) := eta_expand (splitmsl ls1) in *)
(*   let (ls2_tl, ls2_sign) := eta_expand (splitmsl ls2) in *)
(*   let ws1 := copy (size ls1) ls1_sign in *)
(*   let '(g_abs1, cs_abs1, lrs_abs1) := bit_blast_abs g ls1 in *)
(*   let '(g_abs2, cs_abs2, lrs_abs2) := bit_blast_abs g_abs1 ls2 in *)
(*   let '(g_udiv, cs_udiv, qs_udiv, rs_udiv) := bit_blast_udiv g_abs2 lrs_abs1 lrs_abs2 in *)
(*   if (ls1_sign == lit_ff) && (ls2_sign == lit_ff) then *)
(*     (g_udiv, catrev (catrev cs_abs1 cs_abs2) cs_udiv, qs_udiv, rs_udiv) *)
(*   else if  (ls1_sign == lit_tt) && (ls2_sign == lit_tt) then *)
(*          let '(g_negr, cs_negr, lrs_negr) := bit_blast_neg g_udiv rs_udiv in *)
(*          (g_negr, catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negr, qs_udiv, lrs_negr) *)
(*        else if (ls1_sign == lit_ff) && (ls2_sign == lit_tt) then *)
(*               let '(g_negq, cs_negq, lrs_negq) := bit_blast_neg g_udiv qs_udiv in *)
(*               (g_negq, catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negq, lrs_negq, rs_udiv) *)
(*             else if (ls1_sign == lit_tt) && (ls2_sign == lit_ff) then *)
(*                    let '(g_negq, cs_negq, lrs_negq) := bit_blast_neg g_udiv qs_udiv in *)
(*                    let '(g_negr, cs_negr, lrs_negr) := bit_blast_neg g_negq rs_udiv in *)
(*                    (g_negr, catrev (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negq) cs_negr, lrs_negq, lrs_negr) *)
(*             else  *)
(*               let '(g_eq, cs_eq, r_eq) := bit_blast_eq g_udiv (ls1_sign::nil) (ls2_sign::nil) in *)
(*               let '(g_lneg, cs_lneg, r_lneg) := bit_blast_lneg g_eq r_eq in *)
(*               let wneq := copy (size ls1) r_lneg in  *)
(*               let '(g_xor, cs_xor, rs_xor) := bit_blast_xor g_lneg qs_udiv wneq in *)
(*               let '(g_zext, cs_zext, rs_zext) := bit_blast_zeroextend (size ls1_tl) g_xor (r_lneg::nil) in *)
(*               let '(g_add, cs_add, rs_add) := bit_blast_add g_zext rs_xor rs_zext in *)
(*               let '(g_xor1, cs_xor1, rs_xor1) := bit_blast_xor g_add rs_udiv ws1 in *)
(*               let '(g_zext1, cs_zext1, rs_zext1) := bit_blast_zeroextend (size ls1_tl) g_xor1 (ls1_sign::nil) in *)
(*               let '(g_add1, cs_add1, rs_add1) := bit_blast_add g_zext1 rs_xor1 rs_zext1 in *)
(*               (g_add1, catrev (catrev (catrev (catrev (catrev (catrev (catrev (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_eq) cs_lneg) cs_xor) cs_zext) cs_add) cs_xor1) cs_zext1) cs_add1, rs_add, rs_add1). *)

(* Definition sdivB bs1' bs2' : bits * bits := *)
(*   let bs1 := absB bs1' in let bs2 := absB bs2' in *)
(*   if (msb bs1' == msb bs2') && negb (msb bs1') then udivB bs1 bs2 *)
(*   else if (msb bs1' == msb bs2') && (msb bs1') then ((udivB bs1 bs2).1, negB (udivB bs1 bs2).2) *)
(*        else if (msb bs1' != msb bs2') && negb (msb bs1') then (negB (udivB bs1 bs2).1, (udivB bs1 bs2).2) *)
(*             else (negB (udivB bs1 bs2).1, negB (udivB bs1 bs2).2). *)

Definition bit_blast_sdiv g ls1 ls2 : generator * cnf * word :=
  let (ls1_tl, ls1_sign) := eta_expand (splitmsl ls1) in
  let (ls2_tl, ls2_sign) := eta_expand (splitmsl ls2) in
  let ws1 := copy (size ls1) ls1_sign in
  let '(g_abs1, cs_abs1, lrs_abs1) := bit_blast_abs g ls1 in
  let '(g_abs2, cs_abs2, lrs_abs2) := bit_blast_abs g_abs1 ls2 in
  let '(g_udiv, cs_udiv, qs_udiv) := bit_blast_udiv' g_abs2 lrs_abs1 lrs_abs2 in
  if (((ls1_sign == lit_ff) && (ls2_sign == lit_ff)) || ((ls1_sign == lit_tt) && (ls2_sign == lit_tt))) then
    (g_udiv, catrev (catrev cs_abs1 cs_abs2) cs_udiv, qs_udiv)
  else if (((ls1_sign == lit_ff) && (ls2_sign == lit_tt)) || ((ls1_sign == lit_tt) && (ls2_sign == lit_ff))) then
         let '(g_negq, cs_negq, lrs_negq) := bit_blast_neg g_udiv qs_udiv in
         (g_negq, catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negq, lrs_negq)
       else 
         let '(g_eq, cs_eq, r_eq) := bit_blast_eq g_udiv (ls1_sign::nil) (ls2_sign::nil) in
         let '(g_lneg, cs_lneg, r_lneg) := bit_blast_lneg g_eq r_eq in
         let wneq := copy (size ls1) r_lneg in 
         let '(g_xor, cs_xor, rs_xor) := bit_blast_xor g_lneg qs_udiv wneq in
         let '(g_zext, cs_zext, rs_zext) := bit_blast_zeroextend (size ls1_tl) g_xor (r_lneg::nil) in
         let '(g_add, cs_add, rs_add) := bit_blast_add g_zext rs_xor rs_zext in
         (g_add, catrev (catrev (catrev (catrev (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_eq) cs_lneg) cs_xor) cs_zext) cs_add, rs_add).

(* Definition mk_env_sdiv E g ls1 ls2 : env * generator * cnf * word * word := *)
(*   let (ls1_tl, ls1_sign) := eta_expand (splitmsl ls1) in *)
(*   let (ls2_tl, ls2_sign) := eta_expand (splitmsl ls2) in *)
(*   let ws1 := copy (size ls1) ls1_sign in *)
(*   let '(E_abs1, g_abs1, cs_abs1, lrs_abs1) := mk_env_abs E g ls1 in *)
(*   let '(E_abs2, g_abs2, cs_abs2, lrs_abs2) := mk_env_abs E_abs1 g_abs1 ls2 in *)
(*   let '(E_udiv, g_udiv, cs_udiv, qs_udiv, rs_udiv) := mk_env_udiv E_abs2 g_abs2 lrs_abs1 lrs_abs2 in *)
(*   if (ls1_sign == lit_ff) && (ls1_sign == lit_ff) then *)
(*     (E_udiv, g_udiv, catrev (catrev cs_abs1 cs_abs2) cs_udiv, qs_udiv, rs_udiv) *)
(*   else if (ls1_sign == lit_tt) && (ls1_sign == lit_tt) then *)
(*          let '(E_negr, g_negr, cs_negr, lrs_negr) := mk_env_neg E_udiv g_udiv rs_udiv in *)
(*          (E_negr, g_negr, catrev (catrev  (catrev cs_abs1 cs_abs2) cs_udiv) cs_negr, qs_udiv, lrs_negr) *)
(*        else if (ls1_sign == lit_ff) && (ls1_sign == lit_tt) then *)
(*               let '(E_negq, g_negq, cs_negq, lrs_negq) := mk_env_neg E_udiv g_udiv qs_udiv in *)
(*               (E_negq, g_negq, catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negq, lrs_negq, rs_udiv) *)
(*                 else if (ls1_sign == lit_tt) && (ls2_sign == lit_ff) then *)
(*                        let '(E_negq, g_negq, cs_negq, lrs_negq) := mk_env_neg E_udiv g_udiv qs_udiv in *)
(*                        let '(E_negr, g_negr, cs_negr, lrs_negr) := mk_env_neg E_negq g_negq rs_udiv in *)
(*                        (E_negr, g_negr, catrev (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negq) cs_negr, lrs_negq, lrs_negr) *)
(*             else  *)
(*               let '(E_eq, g_eq, cs_eq, r_eq) := mk_env_eq E_udiv g_udiv (ls1_sign::nil) (ls2_sign::nil) in *)
(*               let '(E_lneg, g_lneg, cs_lneg, r_lneg) := mk_env_lneg E_eq g_eq r_eq in *)
(*               let wneq := copy (size ls1) r_lneg in  *)
(*               let '(E_xor, g_xor, cs_xor, rs_xor) := mk_env_xor E_lneg g_lneg qs_udiv wneq in *)
(*               let '(E_zext, g_zext, cs_zext, rs_zext) := mk_env_zeroextend (size ls1_tl) E_xor g_xor (r_lneg::nil) in *)
(*               let '(E_add, g_add, cs_add, rs_add) := mk_env_add E_zext g_zext rs_xor rs_zext in *)
(*               let '(E_xor1, g_xor1, cs_xor1, rs_xor1) := mk_env_xor E_add g_add rs_udiv ws1 in *)
(*               let '(E_zext1, g_zext1, cs_zext1, rs_zext1) := mk_env_zeroextend (size ls1_tl) E_xor1 g_xor1 (ls1_sign::nil) in *)
(*               let '(E_add1, g_add1, cs_add1, rs_add1) := mk_env_add E_zext1 g_zext1 rs_xor1 rs_zext1 in *)
(*               (E_add1, g_add1, catrev (catrev (catrev (catrev (catrev (catrev (catrev (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_eq) cs_lneg) cs_xor) cs_zext) cs_add) cs_xor1) cs_zext1) cs_add1, rs_add, rs_add1). *)

Definition mk_env_sdiv E g ls1 ls2 : env * generator * cnf * word :=
  let (ls1_tl, ls1_sign) := eta_expand (splitmsl ls1) in
  let (ls2_tl, ls2_sign) := eta_expand (splitmsl ls2) in
  let ws1 := copy (size ls1) ls1_sign in
  let '(E_abs1, g_abs1, cs_abs1, lrs_abs1) := mk_env_abs E g ls1 in
  let '(E_abs2, g_abs2, cs_abs2, lrs_abs2) := mk_env_abs E_abs1 g_abs1 ls2 in
  let '(E_udiv, g_udiv, cs_udiv, qs_udiv) := mk_env_udiv' E_abs2 g_abs2 lrs_abs1 lrs_abs2 in
  if (((ls1_sign == lit_ff) && (ls2_sign == lit_ff)) || ((ls1_sign == lit_tt) && (ls2_sign == lit_tt))) then
    (E_udiv, g_udiv, (catrev (catrev cs_abs1 cs_abs2) cs_udiv), qs_udiv)
  else if (((ls1_sign == lit_ff) && (ls2_sign == lit_tt)) || ((ls1_sign == lit_tt) && (ls2_sign == lit_ff))) then
         let '(E_negq, g_negq, cs_negq, lrs_negq) := mk_env_neg E_udiv g_udiv qs_udiv in
         (E_negq, g_negq, catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negq, lrs_negq)
       else 
         let '(E_eq, g_eq, cs_eq, r_eq) := mk_env_eq E_udiv g_udiv (ls1_sign::nil) (ls2_sign::nil) in
         let '(E_lneg, g_lneg, cs_lneg, r_lneg) := mk_env_lneg E_eq g_eq r_eq in
         let wneq := copy (size ls1) r_lneg in 
         let '(E_xor, g_xor, cs_xor, rs_xor) := mk_env_xor E_lneg g_lneg qs_udiv wneq in
         let '(E_zext, g_zext, cs_zext, rs_zext) := mk_env_zeroextend (size ls1_tl) E_xor g_xor (r_lneg::nil) in
         let '(E_add, g_add, cs_add, rs_add) := mk_env_add E_zext g_zext rs_xor rs_zext in
         (E_add, g_add, catrev (catrev (catrev (catrev (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_eq) cs_lneg) cs_xor) cs_zext) cs_add, rs_add).

Lemma size_splitmsl ls : (size (splitmsl ls).1) = size ls -1.
Proof.
  intros. rewrite /splitmsl /split_last /=.
  elim ls => [|lshd lstl IH]; try done. rewrite /= size_belast subn1//. 
Qed.

Lemma bit_blast_xor_zip_size_ss : forall lsp g g' cs rls,
  bit_blast_xor_zip g lsp = (g', cs, rls) ->
  size rls = size lsp.
Proof.
  elim => [|lhd ltl IH] g g' cs rls.
  - rewrite/=. by case => _ _ <-.
  - rewrite/=. case Hbbxorz : (bit_blast_xor_zip (g + 1)%positive ltl) => [[g_xor cs_xor] rls_xor].
    case lhd => [lhd1 lhd2]. case => _ _ <-. rewrite/=.
    by rewrite(IH _ _ _ _ Hbbxorz).
Qed.
    
Lemma bit_blast_xor_size_max : forall ls1 ls2 g g' cs rls,
  bit_blast_xor g ls1 ls2 = (g', cs, rls) ->
  size rls = maxn (size ls1) (size ls2).
Proof.
  rewrite/bit_blast_xor. move =>  ls1 ls2 g g' cs rls Hbbxor.
  by rewrite (bit_blast_xor_zip_size_ss Hbbxor) /extzip_ff size_extzip. 
Qed.

Lemma bit_blast_full_adder_zip_size_ss :
  forall lsp lcin g g' cs lrs lcout, bit_blast_full_adder_zip g lcin lsp = (g', cs, lcout, lrs) -> size lsp = size lrs.
Proof.
  elim => [|lhd ltl IH] lcin g g' cs lrs lcout. 
  - rewrite/=. by case => _ _ _ <-.
  - rewrite/=. case lhd => [lhd1 lhd2]. case Hbbfa : (bit_blast_full_adder_zip (g + 1 + 1)%positive (Pos (g + 1)%positive) ltl) => [[[gtl cstl] lcouttl] lrstl].
    case => _ _ _ <-. by rewrite (IH _ _ _ _ _ _ Hbbfa).
Qed.

Lemma bit_blast_full_adder_size_max :
  forall ls1 ls2 lcin g g' cs lrs lcout, bit_blast_full_adder g lcin ls1 ls2 = (g', cs, lcout, lrs) -> maxn (size ls1) (size ls2) = size lrs.
Proof.
  rewrite/bit_blast_full_adder. intros.
  by rewrite -(bit_blast_full_adder_zip_size_ss H)/extzip_ff size_extzip.
Qed.

Lemma bit_blast_add_size_max :
  forall ls1 ls2 g g' cs lrs, bit_blast_add g ls1 ls2 = (g', cs, lrs) -> maxn (size ls1) (size ls2) = size lrs.
Proof.
  rewrite /bit_blast_add. move => ls1 ls2 g g' cs lrs.
  case Hbbfa : (bit_blast_full_adder g lit_ff ls1 ls2) => [[[ga csa] oa]  rsa].
  case => _ _ <-.
  by rewrite  (bit_blast_full_adder_size_max Hbbfa).
Qed.

Lemma bit_blast_zeroextend_size :
  forall n l g g' cs lrs,
    bit_blast_zeroextend n g l = (g', cs, lrs) -> size lrs = (size l) + n.
Proof.
  rewrite /bit_blast_zeroextend. intros; move : H.
  case => _ _ <-; rewrite seq.size_cat/= size_nseq//. 
Qed.

Lemma bits_v1_cons_zeros bs :
  0 < size bs ->
  (true :: copy (size bs - 1) b0) = (size (invB bs)) -bits of (1)%bits.
Proof.
  intro Hszgt0.
  apply/eqP; rewrite -to_nat_inj_ss ; rewrite size_invB; last rewrite size_from_nat /= size_copy subn1 (ltn_predK Hszgt0)//.
  rewrite to_nat_from_nat_bounded/= -/(zeros _); [rewrite to_nat_zeros //|rewrite -{1}(expn0 2) (ltn_exp2l _ _ (ltnSn 1))//].
Qed.

Lemma bits_v1_zext_b1 bs :
  0 < size bs ->
  zext (size bs - 1) [:: true] = (size (invB bs)) -bits of (1)%bits.
Proof.
  intro Hszgt0.
  apply/eqP; rewrite -to_nat_inj_ss ; rewrite size_invB; last rewrite size_zext addnC/= (subnK Hszgt0) size_from_nat//.
  rewrite to_nat_from_nat_bounded/= -/(zeros _); [rewrite to_nat_zeros //|rewrite -{1}(expn0 2) (ltn_exp2l _ _ (ltnSn 1))//].
Qed.

Lemma bit_blast_sdiv_correct g ls1 ls2 g' cs qlrs E bs1 bs2 :
  bit_blast_sdiv g ls1 ls2 = (g', cs, qlrs) ->
  size ls1 = size ls2 ->
  0 < size ls1 ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E qlrs (sdivB bs1 bs2).
Proof.
  rewrite /bit_blast_sdiv /bit_blast_abs.
  dcase (bit_blast_neg g ls1) => [[[g_neg1 cs_neg1] lrs_neg1] Hbbneg1].
  dcase (bit_blast_xor g ls1 (copy (size ls1) (splitmsl ls1).2)) => [[[g_xor1 cs_xor1] lrs_xor1] Hbbxor1].
  dcase (bit_blast_zeroextend (size (splitmsl ls1).1) g_xor1 [:: (splitmsl ls1).2]) => [[[g_zext1 cs_zext1] lrs_zext1] Hbbzext1].
  dcase (bit_blast_add g_zext1 lrs_xor1 lrs_zext1) => [[[g_add1 cs_add1] lrs_add1] Hbbadd1].
  case Hls1mb1 :((splitmsl ls1).2 == lit_tt); case Hls1mb0 : ((splitmsl ls1).2 == lit_ff);
    case Hls2mb1 :((splitmsl ls2).2 == lit_tt); case Hls2mb0 : ((splitmsl ls2).2 == lit_ff);
    try (rewrite (eqP Hls1mb1) in Hls1mb0; discriminate); try (rewrite (eqP Hls2mb1) in Hls2mb0; discriminate).
  - dcase (bit_blast_neg g_neg1 ls2) => [[[g_neg2 cs_neg2] lrs_neg2] Hbbneg2].
    dcase (bit_blast_udiv' g_neg2 lrs_neg1 lrs_neg2) => [[[g_udiv cs_udiv] lqs_udiv] Hbbudiv].
    case => _ <- <-.
    move => Hsz Hgt01 Henc1 Henc2. rewrite !add_prelude_catrev.
    move => /andP [/andP [Hcsneg1 Hcsneg2] Hcsudiv].
    move : (add_prelude_tt Hcsudiv) => Htt.
    move : (enc_bit_msb Htt Henc1); rewrite/msl (eqP Hls1mb1); move => Hencmsb1.
    move : (add_prelude_enc_bit_true (msb bs1) Hcsudiv). rewrite Hencmsb1 => Hmsb1t.
    move : (enc_bit_msb Htt Henc2). rewrite/msl (eqP Hls2mb1) => Hencmsb2.
    move : (add_prelude_enc_bit_true (msb bs2) Hcsudiv). rewrite Hencmsb2 => Hmsb2t.
    rewrite /sdivB /absB -Hmsb1t -Hmsb2t /=.
    move : (bit_blast_neg_correct Hbbneg1 Henc1 Hcsneg1) => Hencneg1.
    move : (bit_blast_neg_correct Hbbneg2 Henc2 Hcsneg2) => Hencneg2.
    have Hszeq : (size lrs_neg1 = size lrs_neg2) by rewrite -(bit_blast_neg_size_ss Hbbneg1) -(bit_blast_neg_size_ss Hbbneg2).
    exact : (bit_blast_udiv_correct' Hbbudiv Hszeq Hencneg1 Hencneg2 Hcsudiv).
  - dcase (bit_blast_udiv' g_neg1 lrs_neg1 ls2) => [[[g_udiv cs_udiv] lqs_udiv] Hbbudiv].
    dcase (bit_blast_neg g_udiv lqs_udiv) => [[[g_neg cs_neg] lrs_neg] Hbbneg].
    case => _ <- <-.
    move => Hsz Hgt01 Henc1 Henc2. rewrite !add_prelude_catrev.
    move => /andP [/andP [/andP [Hcsneg1 _] Hcsudiv] Hcsneg].
    move : (add_prelude_tt Hcsudiv) => Htt.
    move : (enc_bit_msb Htt Henc1); rewrite /msl (eqP Hls1mb1); move => Hencmsb1.
    move : (add_prelude_enc_bit_true (msb bs1) Hcsudiv). rewrite Hencmsb1 => Hmsb1t.
    move : (enc_bit_msb Htt Henc2); rewrite /msl (eqP Hls2mb0); move => Hencmsb2.
    move : (add_prelude_enc_bit_is_not_true (msb bs2) Hcsudiv); rewrite Hencmsb2 => Hmsb2f; symmetry in Hmsb2f.
    rewrite -> Bool.negb_true_iff in Hmsb2f; rewrite /sdivB /absB -Hmsb1t Hmsb2f/=.
    have Hszeq : size lrs_neg1 = size ls2 by rewrite -Hsz (bit_blast_neg_size_ss Hbbneg1).
    move : (bit_blast_udiv_correct' Hbbudiv Hszeq (bit_blast_neg_correct Hbbneg1 Henc1 Hcsneg1) Henc2 Hcsudiv) => Hencudiv.
    exact : (bit_blast_neg_correct Hbbneg Hencudiv Hcsneg).
  - dcase (bit_blast_xor g_neg1 ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[g_xor2 cs_xor2] lrs_xor2] Hbbxor2].
    dcase (bit_blast_zeroextend (size (splitmsl ls2).1) g_xor2 [:: (splitmsl ls2).2]) => [[[g_zext2 cs_zext2] lrs_zext2] Hbbzext2].
    dcase (bit_blast_add g_zext2 lrs_xor2 lrs_zext2) => [[[g_add2 cs_add2] lrs_add2] Hbbadd2].
    dcase (bit_blast_udiv' g_add2 lrs_neg1 lrs_add2) => [[[g_udiv cs_udiv] lqs_udiv] Hbbudiv].
    dcase (bit_blast_eq g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[g_eq cs_eq] lrs_eq] Hbbeq].
    dcase (bit_blast_lneg g_eq lrs_eq) => [[[g_lneg cs_lneg] lrs_lneg] Hbblneg].
    dcase (bit_blast_xor g_lneg lqs_udiv (copy (size ls1) lrs_lneg)) => [[[g_xor cs_xor] lrs_xor] Hbbxor].
    dcase (bit_blast_zeroextend (size (splitmsl ls1).1) g_xor [:: lrs_lneg]) => [[[g_zext cs_zext] lrs_zext] Hbbzext].
    dcase (bit_blast_add g_zext lrs_xor lrs_zext) => [[[g_add cs_add] lrs_add] Hbbadd].
    case => _ <- <-.
    move => Hsz Hgt Henc1 Henc2. rewrite !add_prelude_catrev.
    move => /andP [/andP [/andP [/andP [/andP [/andP [/andP [Hcsneg1 [/andP [/andP [Hcsxor2 Hcszext2] Hcsadd2]]] Hcsudiv] Hcseq] Hcslneg] Hcsxor] Hcszext] Hcsadd].
    move : (add_prelude_tt Hcsudiv) => Htt.
    move : (enc_bit_msb Htt Henc1); rewrite /msl (eqP Hls1mb1); move => Hencmsb1.
    move : (add_prelude_enc_bit_true (msb bs1) Hcsudiv). rewrite Hencmsb1 => Hmsb1t.
    move : (enc_bit_msb Htt Henc2) => Hencmsb2.
    move : (enc_bit_msb Htt Henc1) => Hencmsb1'.
    move : (bit_blast_xor_correct Hbbxor2 Henc2 (enc_bits_copy (size ls2) Hencmsb2) Hcsxor2) => Hencxor2.
    rewrite <- enc_bits_seq1 in Hencmsb2. rewrite <- enc_bits_seq1 in Hencmsb1'.
    move : (bit_blast_zeroextend_correct Hbbzext2 Hencmsb2 Hcszext2) => Henczext2.
    have Hszeq : size lrs_xor2 = size lrs_zext2.
    {
      rewrite (bit_blast_xor_size_max Hbbxor2) (bit_blast_zeroextend_size Hbbzext2) size_nseq maxnn size_splitmsl.
      rewrite addnC subnK// -Hsz//.
    }
    move : (enc_bits_size Henc1) => Hszlsbs1.
    move : (enc_bits_size Henc2) => Hszlsbs2.
    have Haddr2 : ((bs2 ^# copy (size ls2) (msb bs2) +# (zext (size (splitmsl ls2).1) [:: msb bs2]))%bits
                  = if (msb bs2) then (-#bs2)%bits else bs2).
    {
      rewrite xorBC Hszlsbs2 xorB_copy_case size_splitmsl Hszlsbs2.
      case Hm2 : (msb bs2). rewrite /negB -addB1 bits_v1_zext_b1// -Hszlsbs2 -Hsz//.
      rewrite (eqP (zext_zeros_bit (size bs2 - 1) false)) zeros_cons addB0 unzip1_zip// size_zeros -addn1 subnK//
      -Hszlsbs2 -Hsz//.
    }
    move : (bit_blast_add_correct Hbbadd2 Hencxor2 Henczext2 Haddr2 Hcsadd2 Hszeq) => Hencadd2 {Hszeq}.
    have Hszeq : size lrs_neg1 = size lrs_add2.
    {
      rewrite -(bit_blast_neg_size_ss Hbbneg1) -(bit_blast_add_size_ss Hbbadd2);
      move :(bit_blast_xor_size_max Hbbxor2); rewrite size_nseq maxnn => ->//.
      rewrite (bit_blast_zeroextend_size Hbbzext2) size_splitmsl/= addnC subnK// -Hsz//.
    }
    move : (bit_blast_udiv_correct' Hbbudiv Hszeq (bit_blast_neg_correct Hbbneg1 Henc1 Hcsneg1) Hencadd2 Hcsudiv) => Hencudiv {Hszeq}.
    have Hszeq : size [:: (splitmsl ls1).2] = size [:: (splitmsl ls2).2] by done.
    move : (bit_blast_eq_correct Hbbeq Hszeq Hencmsb1' Hencmsb2 Hcseq) => Henceq.
    move : (bit_blast_lneg_correct Hbblneg Henceq Hcslneg) => Henclneg.
    generalize Henclneg; rewrite <-enc_bits_seq1 => Henclneg1.
    move : (bit_blast_zeroextend_correct Hbbzext Henclneg1 Hcszext) => Henczext.
    move : (bit_blast_xor_correct Hbbxor Hencudiv (enc_bits_copy (size ls1) Henclneg) Hcsxor).
    rewrite /sdivB /absB -Hmsb1t xorBC Hszlsbs1 -size_negB -(size_udivB (-# bs1)%bits (if msb bs2 then (-# bs2)%bits else bs2)) xorB_copy_case.
    move => Hencxor {Hszeq}.
    have Hszeq : size lrs_xor = size lrs_zext.
    {
      rewrite (bit_blast_zeroextend_size Hbbzext) (bit_blast_xor_size_max Hbbxor).
      rewrite (bit_blast_udiv_size_ss' Hbbudiv) -(bit_blast_add_size_ss Hbbadd2) (bit_blast_xor_size_max Hbbxor2) !size_nseq -Hsz !maxnn.
      rewrite size_splitmsl/= addnC subnK//.
      rewrite (bit_blast_zeroextend_size Hbbzext2) size_splitmsl/= -Hsz addnC subnK//.
      rewrite (bit_blast_neg_size_ss Hbbneg1)//.
      rewrite (bit_blast_zeroextend_size Hbbzext2) size_splitmsl/= -Hsz addnC subnK//.
    }
    have Haddr : ((if [:: true] != [:: msb bs2]
                   then (~~# (udivB (-# bs1) (if msb bs2 then -# bs2 else bs2)).1)
                   else (udivB (-# bs1) (if msb bs2 then (-# bs2) else bs2)).1)
                    +# (zext (size (splitmsl ls1).1) [:: [:: msb bs1] != [:: msb bs2]])
                  = if (msb bs2) then (udivB (-# bs1)%bits (if msb bs2 then (-# bs2)%bits else bs2)).1
                    else (-# (udivB (-# bs1) (if msb bs2 then -# bs2 else bs2)).1))%bits.
    {
      case Hms2 : (msb bs2); rewrite -Hmsb1t size_splitmsl /=.
      rewrite (eqP (zext_zeros_bit (size ls1 - 1) false)) zeros_cons addB0 unzip1_zip//
              size_udivB size_negB size_zeros -Hszlsbs1 -addn1 subnK//.
      rewrite Hszlsbs1 bits_v1_zext_b1; last rewrite -Hszlsbs1//.
      rewrite size_invB -size_negB -(size_udivB (-#bs1)%bits bs2) -size_invB addB1 -/(negB _)//.
    }
    move : (bit_blast_add_correct Hbbadd Hencxor Henczext Haddr Hcsadd Hszeq); done.
  - dcase (bit_blast_neg g ls2) => [[[g_neg2 cs_neg2] lrs_neg2] Hbbneg2].
    dcase (bit_blast_udiv' g_neg2 ls1 lrs_neg2) => [[[g_udiv cs_udiv] lrs_udiv] Hbbudiv].
    dcase (bit_blast_neg g_udiv lrs_udiv) => [[[g_neg cs_neg] lrs_neg] Hbbneg].
    case => _ <- <- Hsz Hgt Henc1 Henc2.
    rewrite !add_prelude_catrev => /andP [/andP [Hcsneg2 Hcsudiv] Hcsneg].
    move : (add_prelude_tt Hcsudiv) => Htt.
    move : (enc_bit_msb Htt Henc1). rewrite /msl (eqP Hls1mb0); move => Hencmsb1.
    move : (add_prelude_enc_bit_is_not_true (msb bs1) Hcsudiv). rewrite Hencmsb1 => Hmsb1f; symmetry in Hmsb1f.
    rewrite -> Bool.negb_true_iff in Hmsb1f.
    move : (enc_bit_msb Htt Henc2). rewrite /msl (eqP Hls2mb1); move => Hencmsb2.
    move : (add_prelude_enc_bit_true (msb bs2) Hcsudiv). rewrite Hencmsb2 => Hmsb2t.
    move : (bit_blast_neg_correct Hbbneg2 Henc2 Hcsneg2) => Hencneg2.
    have Hszeq : size ls1 = size lrs_neg2 by rewrite -(bit_blast_neg_size_ss Hbbneg2).
    move : (bit_blast_neg_correct Hbbneg (bit_blast_udiv_correct' Hbbudiv Hszeq Henc1 Hencneg2 Hcsudiv) Hcsneg).
    rewrite /sdivB /absB -Hmsb2t Hmsb1f//.
  - dcase (bit_blast_udiv' g ls1 ls2) => [[[g_udiv cs_udiv] lrs_udiv] Hbbudiv].
    case => _ <- <- Hsz Hgt Henc1 Henc2 Hcsudiv.
    move : (add_prelude_tt Hcsudiv) => Htt.
    move : (enc_bit_msb Htt Henc1). rewrite /msl (eqP Hls1mb0); move => Hencmsb1.
    move : (add_prelude_enc_bit_is_not_true (msb bs1) Hcsudiv). rewrite Hencmsb1 => Hmsb1f; symmetry in Hmsb1f.
    move : (enc_bit_msb Htt Henc2). rewrite /msl (eqP Hls2mb0); move => Hencmsb2.
    move : (add_prelude_enc_bit_is_not_true (msb bs2) Hcsudiv). rewrite Hencmsb2 => Hmsb2f; symmetry in Hmsb2f.
    rewrite -> Bool.negb_true_iff in Hmsb1f, Hmsb2f.
    rewrite /sdivB /absB Hmsb1f Hmsb2f eq_refl.
    move : (bit_blast_udiv_correct' Hbbudiv Hsz Henc1 Henc2 Hcsudiv); done.
  - dcase (bit_blast_xor g ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[g_xor2 cs_xor2] lrs_xor2] Hbbxor2].
    dcase (bit_blast_zeroextend (size (splitmsl ls2).1) g_xor2 [:: (splitmsl ls2).2]) => [[[g_zext2 cs_zext2] lrs_zext2] Hbbzext2].
    dcase (bit_blast_add g_zext2 lrs_xor2 lrs_zext2) => [[[g_add2 cs_add2] lrs_add2] Hbbadd2].
    dcase (bit_blast_udiv' g_add2 ls1 lrs_add2) => [[[g_udiv cs_udiv] lqs_udiv] Hbbudiv].
    dcase (bit_blast_eq g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[g_eq cs_eq] lrs_eq] Hbbeq].
    dcase (bit_blast_lneg g_eq lrs_eq) => [[[g_lneg cs_lneg] lrs_lneg] Hbblneg].
    dcase (bit_blast_xor g_lneg lqs_udiv (copy (size ls1) lrs_lneg)) => [[[g_xor cs_xor] lrs_xor] Hbbxor].
    dcase (bit_blast_zeroextend (size (splitmsl ls1).1) g_xor [:: lrs_lneg]) => [[[g_zext cs_zext] lrs_zext] Hbbzext].
    dcase (bit_blast_add g_zext lrs_xor lrs_zext) => [[[g_add cs_add] lrs_add] Hbbadd].
    case => _ <- <-.
    move => Hsz Hgt Henc1 Henc2. rewrite !add_prelude_catrev.
    move => /andP [/andP [/andP [/andP [/andP [/andP [/andP [/andP [Hcsxor2 Hcszext2] Hcsadd2] Hcsudiv] Hcseq] Hcslneg] Hcsxor] Hcszext] Hcsadd].
    move : (add_prelude_tt Hcsudiv) => Htt.
    move : (enc_bit_msb Htt Henc1); rewrite /msl (eqP Hls1mb0); move => Hencmsb1.
    move : (add_prelude_enc_bit_is_not_true (msb bs1) Hcsudiv). rewrite Hencmsb1 => Hmsb1f; symmetry in Hmsb1f.
    rewrite -> Bool.negb_true_iff in Hmsb1f.
    move : (enc_bit_msb Htt Henc1); rewrite <- enc_bits_seq1 => Hencmsb1'.
    move : (enc_bit_msb Htt Henc2) => Hencmsb2; generalize Hencmsb2; rewrite <- enc_bits_seq1 => Hencmsb2'.
    move : (bit_blast_xor_correct Hbbxor2 Henc2 (enc_bits_copy  (size ls2) Hencmsb2) Hcsxor2) => Hencxor2.
    move : (bit_blast_zeroextend_correct Hbbzext2 Hencmsb2' Hcszext2) => Henczext2.
    move : (enc_bits_size Henc1) => Hszlsbs1; move : (enc_bits_size Henc2) => Hszlsbs2.
    have Hszeq : size lrs_xor2 = size lrs_zext2.
    {
      rewrite (bit_blast_xor_size_max Hbbxor2) size_nseq maxnn.
      rewrite (bit_blast_zeroextend_size Hbbzext2) size_splitmsl addnC subnK// -Hsz//.
    }
    have Haddr2 : ((bs2 ^# copy (size ls2) (msb bs2)) +# (zext (size (splitmsl ls2).1) [:: msb bs2])
                   = if (msb bs2) then -#bs2 else bs2)%bits.
    {
      rewrite xorBC Hszlsbs2 xorB_copy_case size_splitmsl.
      case (msb bs2); [rewrite Hszlsbs2 bits_v1_zext_b1;
                       [rewrite addB1//|rewrite -Hszlsbs2 -Hsz//]
                      |rewrite (eqP (zext_zeros_bit (size ls2 - 1) false)) zeros_cons -addn1 subnK;
                       [rewrite addB0 unzip1_zip// size_zeros Hszlsbs2//|rewrite -Hsz//]]. 
    }
    move : (bit_blast_add_correct Hbbadd2 Hencxor2 Henczext2 Haddr2 Hcsadd2 Hszeq) => Hencadd2.
    have Hszeq' : size ls1 = size lrs_add2.
    {
      rewrite -(bit_blast_add_size_ss Hbbadd2); last rewrite Hszeq//.
      rewrite (bit_blast_xor_size_max Hbbxor2) size_nseq maxnn //.
    }
    move : (bit_blast_udiv_correct' Hbbudiv Hszeq' Henc1 Hencadd2 Hcsudiv) => Hencudiv.
    have Hszeq'' : size [:: (splitmsl ls1).2] = size [:: (splitmsl ls2).2] by done.
    move : (bit_blast_eq_correct Hbbeq Hszeq'' Hencmsb1' Hencmsb2' Hcseq) => Henceq.
    move : (bit_blast_lneg_correct Hbblneg Henceq Hcslneg) => Henclneg.
    generalize Henclneg; rewrite <-enc_bits_seq1 => Henclneg1.
    move : (bit_blast_zeroextend_correct Hbbzext Henclneg1 Hcszext) => Henczext.
    move : (bit_blast_xor_correct Hbbxor Hencudiv (enc_bits_copy (size ls1) Henclneg) Hcsxor).
    rewrite /sdivB /absB Hmsb1f xorBC Hszlsbs1 -(size_udivB (bs1)%bits (if msb bs2 then (-# bs2)%bits else bs2)) xorB_copy_case => Hencxor{Hszeq Hszeq''}.
    have Hszeq : size lrs_xor = size lrs_zext.
    {
      rewrite (bit_blast_xor_size_max Hbbxor) (bit_blast_udiv_size_ss' Hbbudiv)// -Hszeq'.
      rewrite (bit_blast_zeroextend_size Hbbzext) size_splitmsl size_nseq maxnn addnC subnK//.
    }
    have Haddr : ((if [:: false] != [:: msb bs2]
                   then (~~# (udivB bs1 (if msb bs2 then -# bs2 else bs2)).1)
                   else (udivB bs1 (if msb bs2 then (-# bs2) else bs2)).1)
                    +# (zext (size (splitmsl ls1).1) [:: [:: msb bs1] != [:: msb bs2]])
                  = (if false == msb bs2
                     then (udivB bs1 (if msb bs2 then (-# bs2) else bs2)).1
                     else (-# (udivB bs1 (if msb bs2 then -# bs2 else bs2)).1)))%bits.
    {
      case (msb bs2); rewrite Hmsb1f size_splitmsl/= Hszlsbs1;
        [rewrite bits_v1_zext_b1;[rewrite size_invB -(size_udivB bs1 (-#bs2)%bits) -size_invB addB1//|rewrite -Hszlsbs1//]
        |rewrite (eqP (zext_zeros_bit (size bs1 -1) false)) zeros_cons addB0 unzip1_zip// size_udivB size_zeros -addn1 subnK -Hszlsbs1//].
    }
    move : (bit_blast_add_correct Hbbadd Hencxor Henczext Haddr Hcsadd Hszeq); done.
  - dcase (bit_blast_neg g_add1 ls2) => [[[g_neg2 cs_neg2] lrs_neg2] Hbbneg2].
    dcase (bit_blast_udiv' g_neg2 lrs_add1 lrs_neg2) => [[[g_udiv cs_udiv] lqs_udiv] Hbbudiv].
    dcase (bit_blast_eq g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[g_eq cs_eq] lrs_eq] Hbbeq].
    dcase (bit_blast_lneg g_eq lrs_eq) => [[[g_lneg cs_lneg] lrs_lneg] Hbblneg].
    dcase (bit_blast_xor g_lneg lqs_udiv (copy (size ls1) lrs_lneg)) => [[[g_xor cs_xor] lrs_xor] Hbbxor].
    dcase (bit_blast_zeroextend (size (splitmsl ls1).1) g_xor [:: lrs_lneg]) => [[[g_zext cs_zext] lrs_zext] Hbbzext].
    dcase (bit_blast_add g_zext lrs_xor lrs_zext) => [[[g_add cs_add] lrs_add] Hbbadd].
    case => _ <- <-.
    move => Hsz Hgt Henc1 Henc2. rewrite !add_prelude_catrev.
    move => /andP [/andP [/andP [/andP [/andP [/andP [/andP [/andP [/andP [Hcsxor1 Hcszext1] Hcsadd1] Hcsneg2] Hcsudiv] Hcseq] Hcslneg] Hcsxor] Hcszext] Hcsadd].
    move : (add_prelude_tt Hcsudiv) => Htt.
    move : (enc_bit_msb Htt Henc2); rewrite /msl (eqP Hls2mb1); move => Hencmsb2.
    move : (add_prelude_enc_bit_true (msb bs2) Hcsudiv). rewrite Hencmsb2 => Hmsb2t; symmetry in Hmsb2t.
    move : (enc_bit_msb Htt Henc2); rewrite <- enc_bits_seq1 => Hencmsb2'.
    move : (enc_bit_msb Htt Henc1) => Hencmsb1; generalize Hencmsb1; rewrite <- enc_bits_seq1 => Hencmsb1'.
    move : (bit_blast_xor_correct Hbbxor1 Henc1 (enc_bits_copy (size ls1) Hencmsb1) Hcsxor1) => Hencxor1.
    move : (bit_blast_zeroextend_correct Hbbzext1 Hencmsb1' Hcszext1) => Henczext1.
    move : (enc_bits_size Henc1) (enc_bits_size Henc2) => Hszlsbs1 Hszlsbs2.
    have Hszeq : size lrs_xor1 = size lrs_zext1.
    {
      rewrite (bit_blast_xor_size_max Hbbxor1) (bit_blast_zeroextend_size Hbbzext1) size_nseq maxnn size_splitmsl.
      rewrite addnC -addn1 subnK//.
    }
    have Haddr1 : (bs1 ^# copy (size ls1) (msb bs1) +# (zext (size (splitmsl ls1).1) [:: msb bs1])
                   = if (msb bs1) then -#bs1 else bs1)%bits.
    {
      rewrite xorBC size_splitmsl Hszlsbs1 xorB_copy_case.
      case (msb bs1); [rewrite bits_v1_zext_b1; [rewrite addB1//|rewrite -Hszlsbs1//]
                      |rewrite (eqP (zext_zeros_bit _ _)) zeros_cons addB0 unzip1_zip//size_zeros -addn1 subnK//-Hszlsbs1//].
    }
    move : (bit_blast_add_correct Hbbadd1 Hencxor1 Henczext1 Haddr1 Hcsadd1 Hszeq) => Hencadd1.
    have Hszeq' : size lrs_add1 = size lrs_neg2.
    {
      rewrite -(bit_blast_add_size_ss Hbbadd1 Hszeq) (bit_blast_xor_size_max Hbbxor1) size_nseq maxnn -(bit_blast_neg_size_ss Hbbneg2)//.
    }
    move : (bit_blast_udiv_correct' Hbbudiv Hszeq' Hencadd1 (bit_blast_neg_correct Hbbneg2 Henc2 Hcsneg2) Hcsudiv) => Hencudiv.
    have Hszeq'' : size [:: (splitmsl ls1).2] = size [:: (splitmsl ls2).2] by done.
    move : (bit_blast_eq_correct Hbbeq Hszeq'' Hencmsb1' Hencmsb2' Hcseq) => Henceq.
    move : (bit_blast_lneg_correct Hbblneg Henceq Hcslneg) => Henclneg.
    generalize Henclneg; rewrite <-enc_bits_seq1 => Henclneg1.
    move : (bit_blast_zeroextend_correct Hbbzext Henclneg1 Hcszext) => Henczext.
    move : (bit_blast_xor_correct Hbbxor Hencudiv (enc_bits_copy (size ls1) Henclneg) Hcsxor).
    rewrite /sdivB /absB Hmsb2t xorBC Hszlsbs1.
    have -> : (size bs1 = size ((if msb bs1 then (-# bs1)%bits else bs1))) by (case (msb bs1); [rewrite size_negB//|done]).
    rewrite -(size_udivB (if msb bs1 then (-# bs1)%bits else bs1) (-# bs2)%bits) xorB_copy_case => Hencxor{Hszeq Hszeq''}.
    have Hszeq : size lrs_xor = size lrs_zext.
    {
      rewrite (bit_blast_xor_size_max Hbbxor) (bit_blast_udiv_size_ss' Hbbudiv)// -(bit_blast_neg_size_ss Hbbneg2) -Hsz. 
      rewrite (bit_blast_zeroextend_size Hbbzext) size_splitmsl size_nseq maxnn addnC subnK//.
    }
    have Haddr : ((if [:: msb bs1] != [:: true]
                  then (~~# (udivB (if msb bs1 then -# bs1 else bs1) (-# bs2)).1)
                   else (udivB (if msb bs1 then (-# bs1) else bs1) (-# bs2)).1)
                    +# (zext (size (splitmsl ls1).1) [:: [:: msb bs1] != [:: msb bs2]])
                  = (if msb bs1 == true
                     then (udivB (if msb bs1 then (-# bs1) else bs1) (-# bs2)).1
                     else (-# (udivB (if msb bs1 then -# bs1 else bs1) (-# bs2)).1)))%bits.
    {
      case (msb bs1);
        rewrite Hmsb2t size_splitmsl /=;
                [rewrite (eqP (zext_zeros_bit _ _)) zeros_cons addB0 unzip1_zip// size_udivB size_zeros -addn1 subnK// size_negB Hszlsbs1//
                |rewrite Hszlsbs1 bits_v1_zext_b1; [rewrite size_invB -(size_udivB bs1 (-#bs2)%bits) -size_invB addB1//
                                                   |rewrite -Hszlsbs1//]].
    }
    move : (bit_blast_add_correct Hbbadd Hencxor Henczext Haddr Hcsadd Hszeq); done.
  - dcase (bit_blast_udiv' g_add1 lrs_add1 ls2) => [[[g_udiv cs_udiv] lqs_udiv] Hbbudiv].
    dcase (bit_blast_eq g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[g_eq cs_eq] lrs_eq] Hbbeq].
    dcase (bit_blast_lneg g_eq lrs_eq) => [[[g_lneg cs_lneg] lrs_lneg] Hbblneg].
    dcase (bit_blast_xor g_lneg lqs_udiv (copy (size ls1) lrs_lneg)) => [[[g_xor cs_xor] lrs_xor] Hbbxor].
    dcase (bit_blast_zeroextend (size (splitmsl ls1).1) g_xor [:: lrs_lneg]) => [[[g_zext cs_zext] lrs_zext] Hbbzext].
    dcase (bit_blast_add g_zext lrs_xor lrs_zext) => [[[g_add cs_add] lrs_add] Hbbadd].
    case => _ <- <-.
    move => Hsz Hgt Henc1 Henc2. rewrite !add_prelude_catrev.
    move => /andP [/andP [/andP [/andP [/andP [/andP [/andP [/andP [/andP [Hcsxor1 Hcszext1] Hcsadd1] _] Hcsudiv] Hcseq] Hcslneg] Hcsxor] Hcszext] Hcsadd].
    move : (add_prelude_tt Hcsudiv) => Htt.
    move : (enc_bit_msb Htt Henc2); rewrite /msl (eqP Hls2mb0); move => Hencmsb2.
    move : (add_prelude_enc_bit_is_not_true (msb bs2) Hcsudiv). rewrite Hencmsb2 => Hmsb2f; symmetry in Hmsb2f.
    rewrite -> Bool.negb_true_iff in Hmsb2f.
    move : (enc_bit_msb Htt Henc2); rewrite <- enc_bits_seq1 => Hencmsb2'.
    move : (enc_bit_msb Htt Henc1) => Hencmsb1; generalize Hencmsb1; rewrite <- enc_bits_seq1 => Hencmsb1'.
    move : (bit_blast_xor_correct Hbbxor1 Henc1 (enc_bits_copy (size ls1) Hencmsb1) Hcsxor1) => Hencxor1.
    move : (bit_blast_zeroextend_correct Hbbzext1 Hencmsb1' Hcszext1) => Henczext1.
    move : (enc_bits_size Henc1) (enc_bits_size Henc2) => Hszlsbs1 Hszlsbs2.
    have Hszeq : size lrs_xor1 = size lrs_zext1.
    {
      rewrite (bit_blast_xor_size_max Hbbxor1) (bit_blast_zeroextend_size Hbbzext1) size_nseq maxnn size_splitmsl.
      rewrite addnC -addn1 subnK//.
    }
    have Haddr1 : (bs1 ^# copy (size ls1) (msb bs1) +# (zext (size (splitmsl ls1).1) [:: msb bs1])
                   = if (msb bs1) then -#bs1 else bs1)%bits.
    {
      rewrite xorBC size_splitmsl Hszlsbs1 xorB_copy_case.
      case (msb bs1); [rewrite bits_v1_zext_b1; [rewrite addB1//|rewrite -Hszlsbs1//]
                      |rewrite (eqP (zext_zeros_bit _ _)) zeros_cons addB0 unzip1_zip//size_zeros -addn1 subnK//-Hszlsbs1//].
    }
    move : (bit_blast_add_correct Hbbadd1 Hencxor1 Henczext1 Haddr1 Hcsadd1 Hszeq) => Hencadd1.
    have Hszeq' : size lrs_add1 = size ls2.
    {
      rewrite -(bit_blast_add_size_ss Hbbadd1 Hszeq) (bit_blast_xor_size_max Hbbxor1) size_nseq maxnn//.
    }
    move : (bit_blast_udiv_correct' Hbbudiv Hszeq' Hencadd1 Henc2 Hcsudiv) => Hencudiv.
    have Hszeq'' : size [:: (splitmsl ls1).2] = size [:: (splitmsl ls2).2] by done.
    move : (bit_blast_eq_correct Hbbeq Hszeq'' Hencmsb1' Hencmsb2' Hcseq) => Henceq.
    move : (bit_blast_lneg_correct Hbblneg Henceq Hcslneg) => Henclneg.
    generalize Henclneg; rewrite <-enc_bits_seq1 => Henclneg1.
    move : (bit_blast_zeroextend_correct Hbbzext Henclneg1 Hcszext) => Henczext.
    move : (bit_blast_xor_correct Hbbxor Hencudiv (enc_bits_copy (size ls1) Henclneg) Hcsxor).
    rewrite /sdivB /absB Hmsb2f xorBC Hszlsbs1.
    have -> : (size bs1 = size ((if msb bs1 then (-# bs1)%bits else bs1))) by (case (msb bs1); [rewrite size_negB//|done]).
    rewrite -(size_udivB (if msb bs1 then (-# bs1)%bits else bs1) bs2) xorB_copy_case => Hencxor{Hszeq Hszeq''}.
    have Hszeq : size lrs_xor = size lrs_zext.
    {
      rewrite (bit_blast_xor_size_max Hbbxor) (bit_blast_udiv_size_ss' Hbbudiv)// -Hsz. 
      rewrite (bit_blast_zeroextend_size Hbbzext) size_splitmsl size_nseq maxnn addnC subnK//.
    }
    have Haddr : ((if [:: msb bs1] != [:: false]
                  then (~~# (udivB (if msb bs1 then -# bs1 else bs1) bs2).1)
                   else (udivB (if msb bs1 then (-# bs1) else bs1) bs2).1)
                    +# (zext (size (splitmsl ls1).1) [:: [:: msb bs1] != [:: msb bs2]])
                  = (if msb bs1 == false
                     then (udivB (if msb bs1 then (-# bs1) else bs1) bs2).1
                     else (-# (udivB (if msb bs1 then -# bs1 else bs1) bs2).1)))%bits.
    {
      case (msb bs1);
        rewrite Hmsb2f size_splitmsl /=;
                [rewrite Hszlsbs1 bits_v1_zext_b1;
                 [rewrite size_invB -size_negB -(size_udivB (-#bs1)%bits bs2) -size_invB addB1//
                 |rewrite -Hszlsbs1//]
                |rewrite (eqP (zext_zeros_bit _ _)) zeros_cons addB0 unzip1_zip// size_udivB size_zeros -addn1 subnK// Hszlsbs1//].
    }
    move : (bit_blast_add_correct Hbbadd Hencxor Henczext Haddr Hcsadd Hszeq); done.
  - dcase (bit_blast_xor g_add1 ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[g_xor2 cs_xor2] lrs_xor2] Hbbxor2].
    dcase (bit_blast_zeroextend (size (splitmsl ls2).1) g_xor2 [:: (splitmsl ls2).2]) => [[[g_zext2 cs_zext2] lrs_zext2] Hbbzext2].
    dcase (bit_blast_add g_zext2 lrs_xor2 lrs_zext2) => [[[g_add2 cs_add2] lrs_add2] Hbbadd2].
    dcase (bit_blast_udiv' g_add2 lrs_add1 lrs_add2) => [[[g_udiv cs_udiv] lqs_udiv] Hbbudiv].
    dcase (bit_blast_eq g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[g_eq cs_eq] lrs_eq] Hbbeq].
    dcase (bit_blast_lneg g_eq lrs_eq) => [[[g_lneg cs_lneg] lrs_lneg] Hbblneg].
    dcase (bit_blast_xor g_lneg lqs_udiv (copy (size ls1) lrs_lneg)) => [[[g_xor cs_xor] lrs_xor] Hbbxor].
    dcase (bit_blast_zeroextend (size (splitmsl ls1).1) g_xor [:: lrs_lneg]) => [[[g_zext cs_zext] lrs_zext] Hbbzext].
    dcase (bit_blast_add g_zext lrs_xor lrs_zext) => [[[g_add cs_add] lrs_add] Hbbadd].
    case => _ <- <-.
    move => Hsz Hgt Henc1 Henc2. rewrite !add_prelude_catrev.
    move => /andP [/andP [/andP [/andP [/andP [/andP [/andP [/andP [/andP [Hcsxor1 Hcszext1] Hcsadd1] /andP [/andP [Hcsxor2 Hcszext2] Hcsadd2]] Hcsudiv] Hcseq] Hcslneg] Hcsxor] Hcszext] Hcsadd].
    move : (add_prelude_tt Hcsudiv) => Htt.
    move : (enc_bit_msb Htt Henc2) => Hencmsb2.
    move : (enc_bit_msb Htt Henc2); rewrite <- enc_bits_seq1 => Hencmsb2'.
    move : (enc_bit_msb Htt Henc1) => Hencmsb1; generalize Hencmsb1; rewrite <- enc_bits_seq1 => Hencmsb1'.
    move : (bit_blast_xor_correct Hbbxor1 Henc1 (enc_bits_copy (size ls1) Hencmsb1) Hcsxor1) => Hencxor1.
    move : (bit_blast_zeroextend_correct Hbbzext1 Hencmsb1' Hcszext1) => Henczext1.
    move : (enc_bits_size Henc1) (enc_bits_size Henc2) => Hszlsbs1 Hszlsbs2.
    have Hszeq : size lrs_xor1 = size lrs_zext1.
    {
      rewrite (bit_blast_xor_size_max Hbbxor1) (bit_blast_zeroextend_size Hbbzext1) size_nseq maxnn size_splitmsl.
      rewrite addnC -addn1 subnK//.
    }
    have Haddr1 : (bs1 ^# copy (size ls1) (msb bs1) +# (zext (size (splitmsl ls1).1) [:: msb bs1])
                   = if (msb bs1) then -#bs1 else bs1)%bits.
    {
      rewrite xorBC size_splitmsl Hszlsbs1 xorB_copy_case.
      case (msb bs1); [rewrite bits_v1_zext_b1; [rewrite addB1//|rewrite -Hszlsbs1//]
                      |rewrite (eqP (zext_zeros_bit _ _)) zeros_cons addB0 unzip1_zip//size_zeros -addn1 subnK//-Hszlsbs1//].
    }
    move : (bit_blast_add_correct Hbbadd1 Hencxor1 Henczext1 Haddr1 Hcsadd1 Hszeq) => Hencadd1.
    move : (bit_blast_xor_correct Hbbxor2 Henc2 (enc_bits_copy  (size ls2) Hencmsb2) Hcsxor2) => Hencxor2.
    move : (bit_blast_zeroextend_correct Hbbzext2 Hencmsb2' Hcszext2) => Henczext2.
    have Hszeq' : size lrs_xor2 = size lrs_zext2.
    {
      rewrite (bit_blast_xor_size_max Hbbxor2) size_nseq maxnn.
      rewrite (bit_blast_zeroextend_size Hbbzext2) size_splitmsl addnC subnK// -Hsz//.
    }
    have Haddr2 : ((bs2 ^# copy (size ls2) (msb bs2)) +# (zext (size (splitmsl ls2).1) [:: msb bs2])
                   = if (msb bs2) then -#bs2 else bs2)%bits.
    {
      rewrite xorBC Hszlsbs2 xorB_copy_case size_splitmsl.
      case (msb bs2); [rewrite Hszlsbs2 bits_v1_zext_b1;
                       [rewrite addB1//|rewrite -Hszlsbs2 -Hsz//]
                      |rewrite (eqP (zext_zeros_bit (size ls2 - 1) false)) zeros_cons -addn1 subnK;
                       [rewrite addB0 unzip1_zip// size_zeros Hszlsbs2//|rewrite -Hsz//]]. 
    }
    move : (bit_blast_add_correct Hbbadd2 Hencxor2 Henczext2 Haddr2 Hcsadd2 Hszeq') => Hencadd2.
    have Hszeq'' : size lrs_add1 = size lrs_add2.
    {
      rewrite -(bit_blast_add_size_ss Hbbadd1 Hszeq) -(bit_blast_add_size_ss Hbbadd2 Hszeq').
      rewrite (bit_blast_xor_size_max Hbbxor1) (bit_blast_xor_size_max Hbbxor2) !size_nseq !maxnn//.
    }
    move : (bit_blast_udiv_correct' Hbbudiv Hszeq'' Hencadd1 Hencadd2 Hcsudiv) => Hencudiv {Hszeq }.
    have Hszeq : size [:: (splitmsl ls1).2] = size [:: (splitmsl ls2).2] by done.
    move : (bit_blast_eq_correct Hbbeq Hszeq Hencmsb1' Hencmsb2' Hcseq) => Henceq.
    move : (bit_blast_lneg_correct Hbblneg Henceq Hcslneg) => Henclneg.
    generalize Henclneg; rewrite <-enc_bits_seq1 => Henclneg1.
    move : (bit_blast_zeroextend_correct Hbbzext Henclneg1 Hcszext) => Henczext.
    move : (bit_blast_xor_correct Hbbxor Hencudiv (enc_bits_copy (size ls1) Henclneg) Hcsxor).
    rewrite /sdivB /absB xorBC Hszlsbs1.
    have Hszaux : (size bs1 = size ((if msb bs1 then (-# bs1)%bits else bs1))) by (case (msb bs1); [rewrite size_negB//|done]).
    rewrite Hszaux -(size_udivB (if msb bs1 then (-# bs1)%bits else bs1) (if msb bs2 then (-# bs2)%bits else bs2)) xorB_copy_case => Hencxor.
    have Hszeq''' : size lrs_xor = size lrs_zext.
    {
      rewrite (bit_blast_xor_size_max Hbbxor) (bit_blast_udiv_size_ss' Hbbudiv Hszeq'')// .
      rewrite (bit_blast_zeroextend_size Hbbzext) size_splitmsl size_nseq addnC subnK//.
      rewrite -(bit_blast_add_size_ss Hbbadd2 Hszeq') (bit_blast_xor_size_max Hbbxor2) size_nseq Hsz !maxnn//.
    }
    have Haddr : ((if [:: msb bs1] != [:: msb bs2]
                  then (~~# (udivB (if msb bs1 then -# bs1 else bs1) (if msb bs2 then -# bs2 else bs2)).1)
                   else (udivB (if msb bs1 then (-# bs1) else bs1) (if msb bs2 then -# bs2 else bs2)).1)
                    +# (zext (size (splitmsl ls1).1) [:: [:: msb bs1] != [:: msb bs2]])
                  = (if msb bs1 == msb bs2
                     then (udivB (if msb bs1 then (-# bs1) else bs1) (if msb bs2 then -# bs2 else bs2)).1
                     else (-# (udivB (if msb bs1 then -# bs1 else bs1) (if msb bs2 then -# bs2 else bs2)).1)))%bits.
    {
      case Hmsb : (msb bs1 == msb bs2); rewrite -Seqs.singleton_eq in Hmsb; rewrite Hmsb size_splitmsl/=.
      rewrite (eqP (zext_zeros_bit _ _)) zeros_cons addB0 unzip1_zip// size_udivB -Hszaux size_zeros -Hszlsbs1 -addn1 subnK//.
      rewrite Hszlsbs1 bits_v1_zext_b1;
        [rewrite size_invB Hszaux -(size_udivB (if msb bs1 then -# bs1 else bs1)%bits (if msb bs2 then -# bs2 else bs2)%bits) -size_invB addB1//
        |rewrite -Hszlsbs1//].
    }
    move : (bit_blast_add_correct Hbbadd Hencxor Henczext Haddr Hcsadd Hszeq'''); done.
Qed.

Lemma mk_env_sdiv_is_bit_blast_sdiv : forall ls1 E g ls2 g' cs rlrs E',
  mk_env_sdiv E g ls1 ls2 = (E', g', cs, rlrs) ->
  bit_blast_sdiv g ls1 ls2  = (g', cs, rlrs).
Proof.
  rewrite /bit_blast_sdiv /mk_env_sdiv /bit_blast_abs /mk_env_abs.
  move => ls1 E g ls2 g' cs rlrs E'.
  dcase (mk_env_neg E g ls1) => [[[[E_neg1] g_neg1] cs_neg1] rs_neg1] Hmkneg1.
  dcase (mk_env_xor E g ls1 (copy (size ls1) (splitmsl ls1).2)) => [[[[E_xor1] g_xor1] cs_xor1] rs_xor1] Hmkxor1.
  dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor1 g_xor1 [:: (splitmsl ls1).2]) => [[[[E_zext1] g_zext1] cs_zext1] rs_zext1] Hmkzext1.
  dcase (mk_env_add E_zext1 g_zext1 rs_xor1 rs_zext1) => [[[[E_add] g_add] cs_add] rs_add] Hmkadd1.
  rewrite (mk_env_neg_is_bit_blast_neg Hmkneg1) (mk_env_xor_is_bit_blast_xor Hmkxor1) (mk_env_zeroextend_is_bit_blast_zeroextend Hmkzext1) (mk_env_add_is_bit_blast_add Hmkadd1).
  case Htt1: ((splitmsl ls1).2 == lit_tt); case Hff1 : ((splitmsl ls1).2 == lit_ff);
    case Htt2 : ((splitmsl ls2).2 == lit_tt); case Hff2 : ((splitmsl ls2).2 == lit_ff);
      try rewrite (eqP Htt1)// in Hff1; try rewrite (eqP Htt2)// in Hff2.
  - dcase (mk_env_neg E_neg1 g_neg1 ls2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkneg2.
    dcase (mk_env_udiv' E_abs2 g_abs2 rs_neg1 lrs_abs2) => [[[[E_udiv] g_udiv] cs_udiv] lqs_udiv] Hmkudiv.
    rewrite (mk_env_neg_is_bit_blast_neg Hmkneg2) (mk_env_udiv_is_bit_blast_udiv' Hmkudiv).
    by case => _ <- <- <-. 
  - dcase (mk_env_udiv' E_neg1 g_neg1 rs_neg1 ls2) => [[[[E_udiv] g_udiv] cs_udiv] lqs_udiv] Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lqs_udiv) => [[[[E_neg] g_neg] cs_neg] lrs_neg] Hmkneg.
    rewrite (mk_env_udiv_is_bit_blast_udiv' Hmkudiv) (mk_env_neg_is_bit_blast_neg Hmkneg).
    by case => _ <- <- <-.
  - dcase (mk_env_xor E_neg1 g_neg1 ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[[E_xor2] g_xor2] cs_xor2] rs_xor2] Hmkxor2.
    dcase (mk_env_zeroextend (size (splitmsl ls2).1) E_xor2 g_xor2 [:: (splitmsl ls2).2]) => [[[[E_ze2] g_ze2] cs_ze2] rs_ze2] Hmkze2.
    dcase (mk_env_add E_ze2 g_ze2 rs_xor2 rs_ze2) => [[[[E_add2] g_add2] cs_add2] rs_add2] Hmkadd2.
    dcase (mk_env_udiv' E_add2 g_add2 rs_neg1 rs_add2) => [[[[E_udiv] g_udiv] cs_udiv] lqs_udiv] Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lqs_udiv) => [[[[E_neg] g_neg] cs_neg] lrs_neg] Hmkneg.
    dcase (mk_env_eq E_udiv g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[[E_eq] g_eq] cs_eq] rs_eq] Hmkeq.
    dcase (mk_env_lneg E_eq g_eq rs_eq) => [[[[E_lneg] g_lneg] cs_lneg] rs_lneg] Hmklneg.
    dcase (mk_env_xor E_lneg g_lneg lqs_udiv (copy (size ls1) rs_lneg)) => [[[[E_xor] g_xor] cs_xor] rs_xor] Hmkxor.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor g_xor [:: rs_lneg]) => [[[[E_ze] g_ze] cs_ze] rs_ze] Hmkze.
    dcase (mk_env_add E_ze g_ze rs_xor rs_ze) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    rewrite (mk_env_xor_is_bit_blast_xor Hmkxor2) (mk_env_zeroextend_is_bit_blast_zeroextend Hmkze2) (mk_env_add_is_bit_blast_add Hmkadd2).
    rewrite (mk_env_udiv_is_bit_blast_udiv' Hmkudiv) (mk_env_neg_is_bit_blast_neg Hmkneg) (mk_env_eq_is_bit_blast_eq Hmkeq).
    rewrite (mk_env_lneg_is_bit_blast_lneg Hmklneg) (mk_env_xor_is_bit_blast_xor Hmkxor) (mk_env_zeroextend_is_bit_blast_zeroextend Hmkze).
    rewrite (mk_env_add_is_bit_blast_add Hmkaddr).
    by case => _ <- <- <-.
  - dcase (mk_env_neg E g ls2) => [[[[E_neg2] g_neg2] cs_neg2] lrs_neg2] Hmkneg2.
    dcase (mk_env_udiv' E_neg2 g_neg2 ls1 lrs_neg2) => [[[[E_udiv] g_udiv] cs_udiv] lqs_udiv] Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lqs_udiv) => [[[[E_neg] g_neg] cs_neg] lrs_neg] Hmkneg.
    dcase (mk_env_eq E_udiv g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[[E_eq] g_eq] cs_eq] rs_eq] Hmkeq.
    dcase (mk_env_lneg E_eq g_eq rs_eq) => [[[[E_lneg] g_lneg] cs_lneg] rs_lneg] Hmklneg.
    dcase (mk_env_xor E_lneg g_lneg lqs_udiv (copy (size ls1) rs_lneg)) => [[[[E_xor] g_xor] cs_xor] rs_xor] Hmkxor.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor g_xor [:: rs_lneg]) => [[[[E_ze] g_ze] cs_ze] rs_ze] Hmkze.
    dcase (mk_env_add E_ze g_ze rs_xor rs_ze) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    rewrite (mk_env_neg_is_bit_blast_neg Hmkneg2) (mk_env_udiv_is_bit_blast_udiv' Hmkudiv) (mk_env_neg_is_bit_blast_neg Hmkneg).
    rewrite (mk_env_eq_is_bit_blast_eq Hmkeq) (mk_env_lneg_is_bit_blast_lneg Hmklneg) (mk_env_xor_is_bit_blast_xor Hmkxor).
    rewrite (mk_env_zeroextend_is_bit_blast_zeroextend Hmkze) (mk_env_add_is_bit_blast_add Hmkaddr).
    by case => _ <- <- <-.
  - dcase (mk_env_udiv' E g ls1 ls2) => [[[[E_udiv] g_udiv] cs_udiv] lqs_udiv] Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lqs_udiv) => [[[[E_neg] g_neg] cs_neg] lrs_neg] Hmkneg.
    dcase (mk_env_eq E_udiv g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[[E_eq] g_eq] cs_eq] rs_eq] Hmkeq.
    dcase (mk_env_lneg E_eq g_eq rs_eq) => [[[[E_lneg] g_lneg] cs_lneg] rs_lneg] Hmklneg.
    dcase (mk_env_xor E_lneg g_lneg lqs_udiv (copy (size ls1) rs_lneg)) => [[[[E_xor] g_xor] cs_xor] rs_xor] Hmkxor.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor g_xor [:: rs_lneg]) => [[[[E_ze] g_ze] cs_ze] rs_ze] Hmkze.
    dcase (mk_env_add E_ze g_ze rs_xor rs_ze) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    rewrite (mk_env_udiv_is_bit_blast_udiv' Hmkudiv) (mk_env_neg_is_bit_blast_neg Hmkneg) (mk_env_eq_is_bit_blast_eq Hmkeq).
    rewrite (mk_env_lneg_is_bit_blast_lneg Hmklneg) (mk_env_xor_is_bit_blast_xor Hmkxor) (mk_env_zeroextend_is_bit_blast_zeroextend Hmkze).
    rewrite (mk_env_add_is_bit_blast_add Hmkaddr).
    by case => _ <- <- <-.
  - dcase (mk_env_xor E g ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[[E_xor2] g_xor2] cs_xor2] rs_xor2] Hmkxor2.
    dcase (mk_env_zeroextend (size (splitmsl ls2).1) E_xor2 g_xor2 [:: (splitmsl ls2).2]) => [[[[E_ze2] g_ze2] cs_ze2] rs_ze2] Hmkze2.
    dcase (mk_env_add E_ze2 g_ze2 rs_xor2 rs_ze2) => [[[[E_add2] g_add2] cs_add2] rs_add2] Hmkadd2.
    dcase (mk_env_udiv' E_add2 g_add2 ls1 rs_add2) => [[[[E_udiv] g_udiv] cs_udiv] lqs_udiv] Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lqs_udiv) => [[[[E_neg] g_neg] cs_neg] lrs_neg] Hmkneg.
    dcase (mk_env_eq E_udiv g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[[E_eq] g_eq] cs_eq] rs_eq] Hmkeq.
    dcase (mk_env_lneg E_eq g_eq rs_eq) => [[[[E_lneg] g_lneg] cs_lneg] rs_lneg] Hmklneg.
    dcase (mk_env_xor E_lneg g_lneg lqs_udiv (copy (size ls1) rs_lneg)) => [[[[E_xor] g_xor] cs_xor] rs_xor] Hmkxor.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor g_xor [:: rs_lneg]) => [[[[E_ze] g_ze] cs_ze] rs_ze] Hmkze.
    dcase (mk_env_add E_ze g_ze rs_xor rs_ze) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    rewrite (mk_env_xor_is_bit_blast_xor Hmkxor2) (mk_env_zeroextend_is_bit_blast_zeroextend Hmkze2) (mk_env_add_is_bit_blast_add Hmkadd2).
    rewrite (mk_env_udiv_is_bit_blast_udiv' Hmkudiv) (mk_env_neg_is_bit_blast_neg Hmkneg).
    rewrite (mk_env_eq_is_bit_blast_eq Hmkeq) (mk_env_lneg_is_bit_blast_lneg Hmklneg) (mk_env_xor_is_bit_blast_xor Hmkxor).
    rewrite (mk_env_zeroextend_is_bit_blast_zeroextend Hmkze) (mk_env_add_is_bit_blast_add Hmkaddr).
    by case => _ <- <- <-.
  - dcase (mk_env_neg E_add g_add ls2) => [[[[E_neg2] g_neg2] cs_neg2] lrs_neg2] Hmkneg2.
    dcase (mk_env_udiv' E_neg2 g_neg2 rs_add lrs_neg2) => [[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lqs_udiv) => [[[[E_neg] g_neg] cs_neg] lrs_neg] Hmkneg. 
    dcase (mk_env_eq E_udiv g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[[E_eq] g_eq] cs_eq] rs_eq] Hmkeq.
    dcase (mk_env_lneg E_eq g_eq rs_eq) => [[[[E_lneg] g_lneg] cs_lneg] rs_lneg] Hmklneg.
    dcase (mk_env_xor E_lneg g_lneg lqs_udiv (copy (size ls1) rs_lneg)) => [[[[E_xor] g_xor] cs_xor] rs_xor] Hmkxor.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor g_xor [:: rs_lneg]) => [[[[E_ze] g_ze] cs_ze] rs_ze] Hmkze.
    dcase (mk_env_add E_ze g_ze rs_xor rs_ze) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    rewrite (mk_env_neg_is_bit_blast_neg Hmkneg2).
    rewrite (mk_env_udiv_is_bit_blast_udiv' Hmkudiv) (mk_env_neg_is_bit_blast_neg Hmkneg).
    rewrite (mk_env_eq_is_bit_blast_eq Hmkeq) (mk_env_lneg_is_bit_blast_lneg Hmklneg) (mk_env_xor_is_bit_blast_xor Hmkxor).
    rewrite (mk_env_zeroextend_is_bit_blast_zeroextend Hmkze) (mk_env_add_is_bit_blast_add Hmkaddr).
    by case => _ <- <- <-.
  - dcase (mk_env_udiv' E_add g_add rs_add ls2)=> [[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lqs_udiv) => [[[[E_neg] g_neg] cs_neg] lrs_neg] Hmkneg. 
    dcase (mk_env_eq E_udiv g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[[E_eq] g_eq] cs_eq] rs_eq] Hmkeq.
    dcase (mk_env_lneg E_eq g_eq rs_eq) => [[[[E_lneg] g_lneg] cs_lneg] rs_lneg] Hmklneg.
    dcase (mk_env_xor E_lneg g_lneg lqs_udiv (copy (size ls1) rs_lneg)) => [[[[E_xor] g_xor] cs_xor] rs_xor] Hmkxor.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor g_xor [:: rs_lneg]) => [[[[E_ze] g_ze] cs_ze] rs_ze] Hmkze.
    dcase (mk_env_add E_ze g_ze rs_xor rs_ze) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    rewrite (mk_env_udiv_is_bit_blast_udiv' Hmkudiv) (mk_env_neg_is_bit_blast_neg Hmkneg).
    rewrite (mk_env_eq_is_bit_blast_eq Hmkeq) (mk_env_lneg_is_bit_blast_lneg Hmklneg) (mk_env_xor_is_bit_blast_xor Hmkxor).
    rewrite (mk_env_zeroextend_is_bit_blast_zeroextend Hmkze) (mk_env_add_is_bit_blast_add Hmkaddr).
    by case => _ <- <- <-.
  - dcase (mk_env_xor E_add g_add ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[[E_xor2] g_xor2] cs_xor2] rs_xor2] Hmkxor2.
    dcase (mk_env_zeroextend (size (splitmsl ls2).1) E_xor2 g_xor2 [:: (splitmsl ls2).2]) => [[[[E_ze2] g_ze2] cs_ze2] rs_ze2] Hmkze2.
    dcase (mk_env_add E_ze2 g_ze2 rs_xor2 rs_ze2) => [[[[E_add2] g_add2] cs_add2] rs_add2] Hmkadd2.
    dcase (mk_env_udiv' E_add2 g_add2 rs_add rs_add2) => [[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lqs_udiv) => [[[[E_neg] g_neg] cs_neg] lrs_neg] Hmkneg.
    dcase (mk_env_eq E_udiv g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[[E_eq] g_eq] cs_eq] rs_eq] Hmkeq.
    dcase (mk_env_lneg E_eq g_eq rs_eq) => [[[[E_lneg] g_lneg] cs_lneg] rs_lneg] Hmklneg.
    dcase (mk_env_xor E_lneg g_lneg lqs_udiv (copy (size ls1) rs_lneg)) => [[[[E_xor] g_xor] cs_xor] rs_xor] Hmkxor.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor g_xor [:: rs_lneg]) => [[[[E_ze] g_ze] cs_ze] rs_ze] Hmkze.
    dcase (mk_env_add E_ze g_ze rs_xor rs_ze) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    rewrite (mk_env_xor_is_bit_blast_xor Hmkxor2) (mk_env_zeroextend_is_bit_blast_zeroextend Hmkze2) (mk_env_add_is_bit_blast_add Hmkadd2).
    rewrite (mk_env_udiv_is_bit_blast_udiv' Hmkudiv) (mk_env_neg_is_bit_blast_neg Hmkneg).
    rewrite (mk_env_eq_is_bit_blast_eq Hmkeq) (mk_env_lneg_is_bit_blast_lneg Hmklneg) (mk_env_xor_is_bit_blast_xor Hmkxor).
    rewrite (mk_env_zeroextend_is_bit_blast_zeroextend Hmkze) (mk_env_add_is_bit_blast_add Hmkaddr).
    by case => _ <- <- <-.
Qed.

Lemma mk_env_sdiv_newer_gen :
  forall ls1 E g ls2 E' g' cs lrs,
    mk_env_sdiv E g ls1 ls2 = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move => ls1 E g ls2 E' g' cs lrs. rewrite /mk_env_sdiv.
  dcase (mk_env_abs E g ls1) => [[[[E_abs1 g_abs1] cs_abs1] lrs_abs1] Hmkabs1].
  dcase (mk_env_abs E_abs1 g_abs1 ls2) => [[[[E_abs2 g_abs2] cs_abs2] lrs_abs2] Hmkabs2].
  dcase (mk_env_udiv' E_abs2 g_abs2 lrs_abs1 lrs_abs2) => [[[[E_udiv g_udiv] cs_udiv] lrs_udiv] Hmkudiv].
  dcase (mk_env_neg E_udiv g_udiv lrs_udiv) => [[[[E_neg g_neg] cs_neg] lrs_neg] Hmkneg].
  dcase (mk_env_eq E_udiv g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[[E_eq g_eq] cs_eq] lrs_eq] Hmkeq].
  dcase (mk_env_lneg E_eq g_eq lrs_eq) => [[[[E_lneg g_lneg] cs_lneg] lrs_lneg] Hmklneg].
  dcase (mk_env_xor E_lneg g_lneg lrs_udiv (copy (size ls1) lrs_lneg)) => [[[[E_xor g_xor] cs_xor] lrs_xor] Hmkxor].
  dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor g_xor [:: lrs_lneg]) => [[[[E_z g_z] cs_z] lrs_z] Hmkz].
  dcase (mk_env_add E_z g_z lrs_xor lrs_z) => [[[[E_add g_add] cs_add] lrs_add] Hmkadd].
  move : (pos_leb_trans (mk_env_abs_newer_gen Hmkabs1) (mk_env_abs_newer_gen Hmkabs2)) => Hggabs2.
  move : (pos_leb_trans Hggabs2 (mk_env_udiv_newer_gen' Hmkudiv)) => Hggudiv.
  move : (pos_leb_trans Hggudiv (mk_env_neg_newer_gen Hmkneg)) => Hgudivgneg. SearchAbout mk_env_eq.
  move : (pos_leb_trans Hggudiv (pos_leb_trans (mk_env_eq_newer_gen Hmkeq) (mk_env_lneg_newer_gen Hmklneg))) => Hgglneg.
  move : (pos_leb_trans Hgglneg (pos_leb_trans (mk_env_xor_newer_gen Hmkxor) (mk_env_zeroextend_newer_gen Hmkz))) => Hggz.
  move : (pos_leb_trans Hggz (mk_env_add_newer_gen Hmkadd)) => Hggadd.
  case Hmsl1f : ((splitmsl ls1).2 == lit_ff); case Hmsl2f : ((splitmsl ls2).2 == lit_ff); try (case => _ <- _ _ => //).
  - case Hmsl2t: ((splitmsl ls2).2 == lit_tt). rewrite (eqP Hmsl1f). case => _ <- _ _ => //. 
  - rewrite !andbF. case => _ <- _ _ =>//.
  - rewrite (eqP Hmsl2f) !andbF. case ((splitmsl ls1).2 == lit_tt). case => _ <- _ _ => //.
  - case => _ <- _ _ => //.
  - rewrite !andbF !andFb. case ((splitmsl ls1).2 == lit_tt); case ((splitmsl ls2).2 == lit_tt); try (case => _ <- _ _ => //).
Qed.

Lemma mk_env_sdiv_newer_res :
  forall ls1 E g ls2 E' g' cs lrs,
    mk_env_sdiv E g ls1 ls2  = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_lits g' lrs.
Proof.
  move => ls1 E g ls2 E' g' cs lrs. rewrite /mk_env_sdiv. move => Hmk Htt Hgls1 Hgls2. move : Hmk.
  dcase (mk_env_abs E g ls1) => [[[[E_abs1 g_abs1] cs_abs1] lrs_abs1] Hmkabs1].
  dcase (mk_env_abs E_abs1 g_abs1 ls2) => [[[[E_abs2 g_abs2] cs_abs2] lrs_abs2] Hmkabs2].
  dcase (mk_env_udiv' E_abs2 g_abs2 lrs_abs1 lrs_abs2) => [[[[E_udiv g_udiv] cs_udiv] lrs_udiv] Hmkudiv].
  dcase (mk_env_neg E_udiv g_udiv lrs_udiv) => [[[[E_neg g_neg] cs_neg] lrs_neg] Hmkneg].
  dcase (mk_env_eq E_udiv g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[[E_eq g_eq] cs_eq] lrs_eq] Hmkeq].
  dcase (mk_env_lneg E_eq g_eq lrs_eq) => [[[[E_lneg g_lneg] cs_lneg] lrs_lneg] Hmklneg].
  dcase (mk_env_xor E_lneg g_lneg lrs_udiv (copy (size ls1) lrs_lneg)) => [[[[E_xor g_xor] cs_xor] lrs_xor] Hmkxor].
  dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor g_xor [:: lrs_lneg]) => [[[[E_z g_z] cs_z] lrs_z] Hmkz].
  dcase (mk_env_add E_z g_z lrs_xor lrs_z) => [[[[E_add g_add] cs_add] lrs_add] Hmkadd].
  move : (mk_env_abs_newer_gen Hmkabs1) => Hggabs1. 
  move : (pos_leb_trans (mk_env_abs_newer_gen Hmkabs1) (mk_env_abs_newer_gen Hmkabs2)) => Hggabs2.
  move : (pos_leb_trans Hggabs2 (mk_env_udiv_newer_gen' Hmkudiv)) => Hggudiv.
  move : (mk_env_abs_newer_res Hmkabs1 Htt Hgls1) => Hglsabs1.
  move : (mk_env_abs_newer_res Hmkabs2 (newer_than_lit_le_newer Htt Hggabs1) (newer_than_lits_le_newer Hgls2 Hggabs1)) => Hglsabs2.
  move : (mk_env_udiv_newer_res' Hmkudiv (newer_than_lit_le_newer Htt Hggabs2) (newer_than_lits_le_newer Hglsabs1 (mk_env_abs_newer_gen Hmkabs2)) Hglsabs2) => Hglsudiv.
  move : (mk_env_neg_newer_res Hmkneg (newer_than_lit_le_newer Htt Hggudiv) Hglsudiv) => Hglsneg.
  move : (mk_env_add_newer_res Hmkadd) => Hglsadd.
  case Hmsl1f : ((splitmsl ls1).2 == lit_ff); case Hmsl2f : ((splitmsl ls2).2 == lit_ff).
  - rewrite (eqP Hmsl1f) (eqP Hmsl2f); case => _ <- _ <- => //.
  - rewrite (eqP Hmsl1f) !andFb. case : ((splitmsl ls2).2 == lit_tt); try case => _ <- _ <- => //.
  - rewrite (eqP Hmsl2f). case ((splitmsl ls1).2 == lit_tt); try case => _ <- _ <- => //.
  - case ((splitmsl ls1).2 == lit_tt); case ((splitmsl ls2).2 == lit_tt); try (case => _ <- _ <- => //).
Qed.

Lemma mk_env_sdiv_newer_cnf :
  forall ls1 E g ls2 E' g' cs lrs,
    mk_env_sdiv E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  move => ls1 E g ls2 E' g' cs lrs. rewrite /mk_env_sdiv. move => Hmk Htt Hgls1 Hgls2. move : Hmk.
  dcase (mk_env_abs E g ls1) => [[[[E_abs1 g_abs1] cs_abs1] lrs_abs1] Hmkabs1].
  dcase (mk_env_abs E_abs1 g_abs1 ls2) => [[[[E_abs2 g_abs2] cs_abs2] lrs_abs2] Hmkabs2].
  dcase (mk_env_udiv' E_abs2 g_abs2 lrs_abs1 lrs_abs2) => [[[[E_udiv g_udiv] cs_udiv] lrs_udiv] Hmkudiv].
  dcase (mk_env_neg E_udiv g_udiv lrs_udiv) => [[[[E_neg g_neg] cs_neg] lrs_neg] Hmkneg].
  dcase (mk_env_eq E_udiv g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[[E_eq g_eq] cs_eq] lrs_eq] Hmkeq].
  dcase (mk_env_lneg E_eq g_eq lrs_eq) => [[[[E_lneg g_lneg] cs_lneg] lrs_lneg] Hmklneg].
  dcase (mk_env_xor E_lneg g_lneg lrs_udiv (copy (size ls1) lrs_lneg)) => [[[[E_xor g_xor] cs_xor] lrs_xor] Hmkxor].
  dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor g_xor [:: lrs_lneg]) => [[[[E_z g_z] cs_z] lrs_z] Hmkz].
  dcase (mk_env_add E_z g_z lrs_xor lrs_z) => [[[[E_add g_add] cs_add] lrs_add] Hmkadd].
  move : (mk_env_abs_newer_gen Hmkabs1) => Hggabs1.
  move : (pos_leb_trans (mk_env_abs_newer_gen Hmkabs2) (mk_env_udiv_newer_gen' Hmkudiv)) => Hgabs1gudiv.
  move : (pos_leb_trans (mk_env_abs_newer_gen Hmkabs1) (mk_env_abs_newer_gen Hmkabs2)) => Hggabs2.
  move : (mk_env_udiv_newer_gen' Hmkudiv) => Hgabs2gudiv.
  move : (pos_leb_trans Hggabs2 (mk_env_udiv_newer_gen' Hmkudiv)) => Hggudiv.
  move : (mk_env_neg_newer_gen Hmkneg) => Hgudivgneg.
  move : (pos_leb_trans Hggudiv (mk_env_neg_newer_gen Hmkneg)) => Hggneg.
  move : (mk_env_eq_newer_gen Hmkeq) => Hgudivgeq.
  move : (mk_env_lneg_newer_gen Hmklneg) => Hgeqglneg.
  move : (pos_leb_trans Hggudiv (mk_env_eq_newer_gen Hmkeq)) => Hggeq.
  move : (pos_leb_trans Hggeq (mk_env_lneg_newer_gen Hmklneg)) => Hgglneg.
  move : (pos_leb_trans Hgglneg (mk_env_xor_newer_gen Hmkxor)) => Hggxor.
  move : (mk_env_xor_newer_gen Hmkxor) => Hglneggxor. move : (mk_env_zeroextend_newer_gen Hmkz) => Hgxorgz.
  move : (mk_env_add_newer_gen Hmkadd) => Hgzgadd.
  move : (mk_env_abs_newer_res Hmkabs1 Htt Hgls1) => Hglsabs1.
  move : (newer_than_cnf_le_newer (mk_env_abs_newer_cnf Hmkabs1 Htt Hgls1) Hgabs1gudiv) => Hgudivcsabs1.
  move : (mk_env_abs_newer_res Hmkabs2 (newer_than_lit_le_newer Htt Hggabs1) (newer_than_lits_le_newer Hgls2 Hggabs1)) => Hglsabs2.
  move : (newer_than_cnf_le_newer (mk_env_abs_newer_cnf Hmkabs2 (newer_than_lit_le_newer Htt Hggabs1) (newer_than_lits_le_newer Hgls2 Hggabs1)) Hgabs2gudiv) => Hgudivcsabs2.
  move : (mk_env_udiv_newer_res' Hmkudiv (newer_than_lit_le_newer Htt Hggabs2) (newer_than_lits_le_newer Hglsabs1 (mk_env_abs_newer_gen Hmkabs2)) Hglsabs2) => Hglsudiv.
  move : (mk_env_udiv_newer_cnf' Hmkudiv (newer_than_lit_le_newer Htt Hggabs2) (newer_than_lits_le_newer Hglsabs1 (mk_env_abs_newer_gen Hmkabs2)) Hglsabs2) => Hcsudiv.
  move : (mk_env_neg_newer_res Hmkneg (newer_than_lit_le_newer Htt Hggudiv) Hglsudiv) => Hglsneg.
  move : (mk_env_neg_newer_cnf Hmkneg (newer_than_lit_le_newer Htt Hggudiv) Hglsudiv) => Hcsneg.
  move : (mk_env_eq_newer_res Hmkeq) => Hglseq.
  move : (newer_than_lits_le_newer Hgls1 Hggudiv) => Hgudivls1.
  move : (newer_than_lits_le_newer Hgls2 Hggudiv) => Hgudivls2.
  move : (newer_than_lits_splitmsl (newer_than_lit_le_newer Htt Hggudiv) Hgudivls1) => /andP [_ Hgudivmsl1].
  move : (newer_than_lits_splitmsl (newer_than_lit_le_newer Htt Hggudiv) Hgudivls2) => /andP [_ Hgudivmsl2].
  move : (mk_env_eq_newer_cnf Hmkeq (newer_than_lit_le_newer Htt Hggudiv)).
  rewrite (lock splitmsl) /= -lock !andbT => Hcseq'. move : (Hcseq' Hgudivmsl1 Hgudivmsl2) => Hcseq{Hcseq'}.
  move : (mk_env_lneg_newer_res Hmklneg) => Hglslneg.
  move : (mk_env_lneg_newer_cnf Hmklneg Hglseq) => Hcslneg.
  move : (mk_env_xor_newer_res Hmkxor (newer_than_lit_le_newer Htt Hgglneg) (newer_than_lits_le_newer Hglsudiv (pos_leb_trans (mk_env_eq_newer_gen Hmkeq) (mk_env_lneg_newer_gen Hmklneg))) (newer_than_lits_copy (size ls1) Hglslneg)) => Hglsxor.
  move : (mk_env_xor_newer_cnf Hmkxor (newer_than_lit_le_newer Htt Hgglneg) (newer_than_lits_le_newer Hglsudiv (pos_leb_trans (mk_env_eq_newer_gen Hmkeq) (mk_env_lneg_newer_gen Hmklneg))) (newer_than_lits_copy (size ls1) Hglslneg)) => Hcsxor.
  move : (mk_env_zeroextend_newer_res Hmkz (newer_than_lit_le_newer Htt Hggxor)). rewrite (lock splitmsl) /= !andbT -lock => Hglsz'.
  move : (Hglsz' (newer_than_lit_le_newer Hglslneg (mk_env_xor_newer_gen Hmkxor))) => Hglsz{Hglsz'}.
  move : (mk_env_zeroextend_newer_cnf Hmkz (newer_than_lit_le_newer Htt Hggxor)). rewrite (lock splitmsl) /= !andbT -lock => Hcsz'.
  move : (Hcsz' (newer_than_lit_le_newer Hglslneg (mk_env_xor_newer_gen Hmkxor))) => Hcsz{Hcsz'}.
  move : (mk_env_add_newer_res Hmkadd) => Hglsadd.
  generalize Htt; rewrite newer_than_lit_tt_ff => Hff.
  move : (mk_env_add_newer_cnf Hmkadd (newer_than_lits_le_newer Hglsxor (mk_env_zeroextend_newer_gen Hmkz)) Hglsz (newer_than_lit_le_newer Hff (pos_leb_trans Hggxor Hgxorgz))) => Hcsadd. 
  case Hmsl1f : ((splitmsl ls1).2 == lit_ff); case Hmsl2f : ((splitmsl ls2).2 == lit_ff).
  - rewrite (eqP Hmsl1f) (eqP Hmsl2f); case => _ <- <- _. rewrite !newer_than_cnf_catrev Hgudivcsabs1 Hgudivcsabs2 Hcsudiv//.
  - rewrite (eqP Hmsl1f) !andFb. case : ((splitmsl ls2).2 == lit_tt); case => _ <- <- _; rewrite !newer_than_cnf_catrev.
    + rewrite (newer_than_cnf_le_newer Hgudivcsabs1 Hgudivgneg) (newer_than_cnf_le_newer Hgudivcsabs2 Hgudivgneg).
      rewrite (newer_than_cnf_le_newer Hcsudiv Hgudivgneg) Hcsneg //.
    + rewrite (newer_than_cnf_le_newer Hgudivcsabs1 (pos_leb_trans (pos_leb_trans (pos_leb_trans Hgudivgeq Hgeqglneg) (pos_leb_trans Hglneggxor Hgxorgz)) Hgzgadd)).
      rewrite (newer_than_cnf_le_newer Hgudivcsabs2 (pos_leb_trans (pos_leb_trans (pos_leb_trans Hgudivgeq Hgeqglneg) (pos_leb_trans Hglneggxor Hgxorgz)) Hgzgadd)).
      rewrite (newer_than_cnf_le_newer Hcsudiv (pos_leb_trans (pos_leb_trans (pos_leb_trans Hgudivgeq Hgeqglneg) (pos_leb_trans Hglneggxor Hgxorgz)) Hgzgadd)).
      rewrite (newer_than_cnf_le_newer Hcseq (pos_leb_trans (pos_leb_trans Hgeqglneg (pos_leb_trans Hglneggxor Hgxorgz)) Hgzgadd)).
      rewrite (newer_than_cnf_le_newer Hcslneg (pos_leb_trans (pos_leb_trans Hglneggxor Hgxorgz) Hgzgadd)).
      rewrite (newer_than_cnf_le_newer Hcsxor (pos_leb_trans Hgxorgz Hgzgadd)).
      rewrite (newer_than_cnf_le_newer Hcsz Hgzgadd) Hcsadd //.
  - rewrite (eqP Hmsl2f). case ((splitmsl ls1).2 == lit_tt); case => _ <- <- _; rewrite !newer_than_cnf_catrev.
    + rewrite (newer_than_cnf_le_newer Hgudivcsabs1 Hgudivgneg) (newer_than_cnf_le_newer Hgudivcsabs2 Hgudivgneg).
      rewrite (newer_than_cnf_le_newer Hcsudiv Hgudivgneg) Hcsneg //.
    + rewrite (newer_than_cnf_le_newer Hgudivcsabs1 (pos_leb_trans (pos_leb_trans (pos_leb_trans Hgudivgeq Hgeqglneg) (pos_leb_trans Hglneggxor Hgxorgz)) Hgzgadd)).
      rewrite (newer_than_cnf_le_newer Hgudivcsabs2 (pos_leb_trans (pos_leb_trans (pos_leb_trans Hgudivgeq Hgeqglneg) (pos_leb_trans Hglneggxor Hgxorgz)) Hgzgadd)).
      rewrite (newer_than_cnf_le_newer Hcsudiv (pos_leb_trans (pos_leb_trans (pos_leb_trans Hgudivgeq Hgeqglneg) (pos_leb_trans Hglneggxor Hgxorgz)) Hgzgadd)).
      rewrite (newer_than_cnf_le_newer Hcseq (pos_leb_trans (pos_leb_trans Hgeqglneg (pos_leb_trans Hglneggxor Hgxorgz)) Hgzgadd)).
      rewrite (newer_than_cnf_le_newer Hcslneg (pos_leb_trans (pos_leb_trans Hglneggxor Hgxorgz) Hgzgadd)).
      rewrite (newer_than_cnf_le_newer Hcsxor (pos_leb_trans Hgxorgz Hgzgadd)).
      rewrite (newer_than_cnf_le_newer Hcsz Hgzgadd) Hcsadd //.
  - case ((splitmsl ls1).2 == lit_tt); case ((splitmsl ls2).2 == lit_tt);
      case => _ <- <- _;
                rewrite !newer_than_cnf_catrev ;
                try by (rewrite (newer_than_cnf_le_newer Hgudivcsabs1 (pos_leb_trans (pos_leb_trans (pos_leb_trans Hgudivgeq Hgeqglneg) (pos_leb_trans Hglneggxor Hgxorgz)) Hgzgadd))
      (newer_than_cnf_le_newer Hgudivcsabs2 (pos_leb_trans (pos_leb_trans (pos_leb_trans Hgudivgeq Hgeqglneg) (pos_leb_trans Hglneggxor Hgxorgz)) Hgzgadd))
      (newer_than_cnf_le_newer Hcsudiv (pos_leb_trans (pos_leb_trans (pos_leb_trans Hgudivgeq Hgeqglneg) (pos_leb_trans Hglneggxor Hgxorgz)) Hgzgadd))
      (newer_than_cnf_le_newer Hcseq (pos_leb_trans (pos_leb_trans Hgeqglneg (pos_leb_trans Hglneggxor Hgxorgz)) Hgzgadd))
      (newer_than_cnf_le_newer Hcslneg (pos_leb_trans (pos_leb_trans Hglneggxor Hgxorgz) Hgzgadd))
      (newer_than_cnf_le_newer Hcsxor (pos_leb_trans Hgxorgz Hgzgadd))
      (newer_than_cnf_le_newer Hcsz Hgzgadd) Hcsadd //).
    rewrite Hgudivcsabs1 Hgudivcsabs2 Hcsudiv //.
Qed.

Lemma mk_env_sdiv_preserve :
  forall E g ls1 ls2 E' g' cs lrs,
    mk_env_sdiv E g ls1 ls2 = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move => E g ls1 ls2 E' g' cs lrs. rewrite /mk_env_sdiv.
  dcase (mk_env_abs E g ls1) => [[[[E_abs1 g_abs1] cs_abs1] lrs_abs1] Hmkabs1].
  dcase (mk_env_abs E_abs1 g_abs1 ls2) => [[[[E_abs2 g_abs2] cs_abs2] lrs_abs2] Hmkabs2].
  dcase (mk_env_udiv' E_abs2 g_abs2 lrs_abs1 lrs_abs2) => [[[[E_udiv g_udiv] cs_udiv] lrs_udiv] Hmkudiv].
  dcase (mk_env_neg E_udiv g_udiv lrs_udiv) => [[[[E_neg g_neg] cs_neg] lrs_neg] Hmkneg].
  dcase (mk_env_eq E_udiv g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[[E_eq g_eq] cs_eq] lrs_eq] Hmkeq].
  dcase (mk_env_lneg E_eq g_eq lrs_eq) => [[[[E_lneg g_lneg] cs_lneg] lrs_lneg] Hmklneg].
  dcase (mk_env_xor E_lneg g_lneg lrs_udiv (copy (size ls1) lrs_lneg)) => [[[[E_xor g_xor] cs_xor] lrs_xor] Hmkxor].
  dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor g_xor [:: lrs_lneg]) => [[[[E_z g_z] cs_z] lrs_z] Hmkz].
  dcase (mk_env_add E_z g_z lrs_xor lrs_z) => [[[[E_add g_add] cs_add] lrs_add] Hmkadd].
  move : (mk_env_abs_newer_gen Hmkabs1) => Hggabs1.
  move : (pos_leb_trans (mk_env_abs_newer_gen Hmkabs1) (mk_env_abs_newer_gen Hmkabs2)) => Hggabs2.
  move : (pos_leb_trans Hggabs2 (mk_env_udiv_newer_gen' Hmkudiv)) => Hggudiv.
  move : (pos_leb_trans Hggudiv (mk_env_neg_newer_gen Hmkneg)) => Hggneg.
  move : (pos_leb_trans Hggudiv (mk_env_eq_newer_gen Hmkeq)) => Hggeq.
  move : (pos_leb_trans Hggeq (mk_env_lneg_newer_gen Hmklneg)) => Hgglneg.
  move : (pos_leb_trans Hgglneg (mk_env_xor_newer_gen Hmkxor)) => Hggxor.
  move : (pos_leb_trans Hggxor (mk_env_zeroextend_newer_gen Hmkz)) => Hggz.
  move : (pos_leb_trans Hggz (mk_env_add_newer_gen Hmkadd)) => Hggadd.
  move : (mk_env_abs_preserve Hmkabs1) => HEEa1g.
  move : (mk_env_abs_preserve Hmkabs2) => HEa1Ea2ga1.
  move : (env_preserve_trans HEEa1g (env_preserve_le HEa1Ea2ga1 Hggabs1)) => HEEa2g.
  move : (mk_env_udiv_preserve' Hmkudiv) => HEa2Euga2.
  move : (env_preserve_trans HEEa2g (env_preserve_le HEa2Euga2 Hggabs2)) => HEEug.
  move : (mk_env_neg_preserve Hmkneg) => HEuEngu.
  move : (env_preserve_trans HEEug (env_preserve_le HEuEngu Hggudiv)) => HEEng.
  move : (mk_env_eq_preserve Hmkeq) => HEuEegu.
  move : (env_preserve_trans HEEug (env_preserve_le HEuEegu Hggudiv)) => HEEeg.
  move : (mk_env_lneg_preserve Hmklneg) => HEeElge.
  move : (env_preserve_trans HEEeg (env_preserve_le HEeElge Hggeq)) => HEElg.
  move : (mk_env_xor_preserve Hmkxor) => HElExgl.
  move : (env_preserve_trans HEElg (env_preserve_le HElExgl Hgglneg)) => HEExg.
  move : (mk_env_zeroextend_preserve Hmkz) => HExEzgx.
  move : (env_preserve_trans HEExg (env_preserve_le HExEzgx Hggxor)) => HEEzg.
  move : (mk_env_add_preserve Hmkadd) => HEzEagz.
  move : (env_preserve_trans HEEzg (env_preserve_le HEzEagz Hggz)) => HEEag.
  case Hmsl1f : ((splitmsl ls1).2 == lit_ff); case Hmsl2f : ((splitmsl ls2).2 == lit_ff).
  - case => <- _ _ _ //.
  - rewrite (eqP Hmsl1f). case Hmsl2t : ((splitmsl ls2).2 == lit_tt); case => <- _ _ _ //.
  - rewrite (eqP Hmsl2f). case Hmsl1t : ((splitmsl ls1).2 == lit_tt); case => <- _ _ _ //.
  - case ((splitmsl ls1).2 == lit_tt); case ((splitmsl ls2).2 == lit_tt); case => <- _ _ _ //.
Qed.

Lemma mk_env_sdiv_sat :
  forall E g ls1 ls2 E' g' cs lrs,
    mk_env_sdiv E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move => E g ls1 ls2 E' g' cs lrs. rewrite /mk_env_sdiv.
  dcase (mk_env_abs E g ls1) => [[[[E_abs1 g_abs1] cs_abs1] lrs_abs1] Hmkabs1].
  dcase (mk_env_abs E_abs1 g_abs1 ls2) => [[[[E_abs2 g_abs2] cs_abs2] lrs_abs2] Hmkabs2].
  dcase (mk_env_udiv' E_abs2 g_abs2 lrs_abs1 lrs_abs2) => [[[[E_udiv g_udiv] cs_udiv] lrs_udiv] Hmkudiv].
  dcase (mk_env_neg E_udiv g_udiv lrs_udiv) => [[[[E_neg g_neg] cs_neg] lrs_neg] Hmkneg].
  dcase (mk_env_eq E_udiv g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[[E_eq g_eq] cs_eq] lrs_eq] Hmkeq].
  dcase (mk_env_lneg E_eq g_eq lrs_eq) => [[[[E_lneg g_lneg] cs_lneg] lrs_lneg] Hmklneg].
  dcase (mk_env_xor E_lneg g_lneg lrs_udiv (copy (size ls1) lrs_lneg)) => [[[[E_xor g_xor] cs_xor] lrs_xor] Hmkxor].
  dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor g_xor [:: lrs_lneg]) => [[[[E_z g_z] cs_z] lrs_z] Hmkz].
  dcase (mk_env_add E_z g_z lrs_xor lrs_z) => [[[[E_add g_add] cs_add] lrs_add] Hmkadd].
  move => Hmk Htt Hgls1 Hgls2; move : Hmk.
  generalize Htt; rewrite newer_than_lit_tt_ff => Hff.
  move : (mk_env_abs_newer_gen Hmkabs1) => Hgga1. move : (mk_env_abs_newer_gen Hmkabs2) => Hga1ga2.
  move : (mk_env_udiv_newer_gen' Hmkudiv) => Hga2gu. move : (mk_env_eq_newer_gen Hmkeq) => Hguge.
  move : (mk_env_lneg_newer_gen Hmklneg) => Hgegl. move : (mk_env_xor_newer_gen Hmkxor) => Hglgx.
  move : (mk_env_zeroextend_newer_gen Hmkz) => Hgxgz. move : (mk_env_add_newer_gen Hmkadd) => Hgzga.
  move : (pos_leb_trans Hgga1 (pos_leb_trans Hga1ga2 Hga2gu)) => Hggu.
  move : (pos_leb_trans Hggu (pos_leb_trans Hguge Hgegl)) => Hggl.
  move : (mk_env_abs_sat Hmkabs1 Htt Hgls1) => HEa1csa1.
  move : (mk_env_abs_newer_res Hmkabs1 Htt Hgls1) => Hga1la1.
  move : (mk_env_abs_newer_cnf Hmkabs1 Htt Hgls1) => Hga1csa1.
  move : (env_preserve_trans (mk_env_abs_preserve Hmkabs2) (env_preserve_le (mk_env_udiv_preserve' Hmkudiv) Hga1ga2)) => HEa1Euga1.
  move : (mk_env_abs_sat Hmkabs2 (newer_than_lit_le_newer Htt Hgga1) (newer_than_lits_le_newer Hgls2 Hgga1)) => HEa2csa2.
  move : (mk_env_abs_newer_res Hmkabs2 (newer_than_lit_le_newer Htt Hgga1) (newer_than_lits_le_newer Hgls2 Hgga1)) => Hga2la2.
  move : (mk_env_abs_newer_cnf Hmkabs2 (newer_than_lit_le_newer Htt Hgga1) (newer_than_lits_le_newer Hgls2 Hgga1)) => Hga2csa2.
  move : (env_preserve_trans HEa1Euga1 (env_preserve_le (mk_env_neg_preserve Hmkneg) (pos_leb_trans Hga1ga2 (mk_env_udiv_newer_gen' Hmkudiv)))) => HEa1Enga1.
  move : (env_preserve_trans (mk_env_udiv_preserve' Hmkudiv) (env_preserve_le (mk_env_neg_preserve Hmkneg) Hga2gu)) => HEa2Enga2.
  move : (mk_env_udiv_newer_res' Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hgga1 Hga1ga2)) (newer_than_lits_le_newer Hga1la1 Hga1ga2) Hga2la2) => Hgulsu.
  move : (mk_env_udiv_newer_cnf' Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hgga1 Hga1ga2)) (newer_than_lits_le_newer Hga1la1 Hga1ga2) Hga2la2) => Hgucsu.
  move : (mk_env_udiv_sat' Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hgga1 Hga1ga2)) (newer_than_lits_le_newer Hga1la1 Hga1ga2) Hga2la2) => HEucsu.
  move : (mk_env_xor_newer_res Hmkxor (newer_than_lit_le_newer Htt Hggl) (newer_than_lits_le_newer Hgulsu (pos_leb_trans Hguge Hgegl)) (newer_than_lits_copy (size ls1) (mk_env_lneg_newer_res Hmklneg))) => Hgxlsx.
  move : (mk_env_xor_newer_cnf Hmkxor (newer_than_lit_le_newer Htt Hggl) (newer_than_lits_le_newer Hgulsu (pos_leb_trans Hguge Hgegl)) (newer_than_lits_copy (size ls1) (mk_env_lneg_newer_res Hmklneg))) => Hgxcsx.
  move : (mk_env_xor_sat Hmkxor (newer_than_lit_le_newer Htt Hggl) (newer_than_lits_le_newer Hgulsu (pos_leb_trans Hguge Hgegl)) (newer_than_lits_copy (size ls1) (mk_env_lneg_newer_res Hmklneg))) => HExcsx.
  move : (mk_env_zeroextend_newer_res Hmkz (newer_than_lit_le_newer Htt (pos_leb_trans Hggl Hglgx))); rewrite (lock splitmsl) /= -lock andbT => Hgzlsz'.
  move : (Hgzlsz' (newer_than_lit_le_newer (mk_env_lneg_newer_res Hmklneg) Hglgx)) => Hgzlsz {Hgzlsz'}.
  move : (mk_env_zeroextend_newer_cnf Hmkz (newer_than_lit_le_newer Htt (pos_leb_trans Hggl Hglgx))); rewrite (lock splitmsl) /= -lock andbT => Hgzcsz'.
  move : (Hgzcsz' (newer_than_lit_le_newer (mk_env_lneg_newer_res Hmklneg) Hglgx)) => Hgzcsz {Hgzcsz'}.
  move : (mk_env_add_sat Hmkadd (newer_than_lits_le_newer Hgxlsx Hgxgz) Hgzlsz (newer_than_lit_le_newer Hff (pos_leb_trans Hggl (pos_leb_trans Hglgx Hgxgz)))) => HEacsa.
  move : (mk_env_zeroextend_sat Hmkz (newer_than_lit_le_newer Htt (pos_leb_trans Hggl Hglgx))); rewrite (lock splitmsl) /= -lock andbT => HEzcsz'.
  move : (HEzcsz' (newer_than_lit_le_newer (mk_env_lneg_newer_res Hmklneg) Hglgx)) => HEzcsz {HEzcsz'}.
  move : (mk_env_eq_newer_cnf Hmkeq (newer_than_lit_le_newer Htt Hggu)); rewrite (lock splitmsl) /= -lock !andbT -{1}/(msl ls1) -{1}/(msl ls2) => Hgecse'.
  move : (Hgecse' (newer_than_lit_le_newer (newer_than_lits_msl Htt Hgls1) Hggu) (newer_than_lit_le_newer (newer_than_lits_msl Htt Hgls2) Hggu)) => Hgecse{Hgecse'}.
  move : (mk_env_eq_sat Hmkeq (newer_than_lit_le_newer Htt Hggu)); rewrite (lock splitmsl) /= -lock !andbT -{1}/(msl ls1) -{1}/(msl ls2)=> HEecse'.
  move : (HEecse' (newer_than_lit_le_newer (newer_than_lits_msl Htt Hgls1) Hggu) (newer_than_lit_le_newer (newer_than_lits_msl Htt Hgls2) Hggu)) => HEecse{HEecse'}.
  move : (mk_env_lneg_sat Hmklneg (mk_env_eq_newer_res Hmkeq)) => HElcsl.
  move : (mk_env_lneg_newer_cnf Hmklneg (mk_env_eq_newer_res Hmkeq)) => Hglcsl.
  move : (env_preserve_trans HEa1Euga1 (env_preserve_le (mk_env_eq_preserve Hmkeq) (pos_leb_trans Hga1ga2 Hga2gu))) => HEa1Eega1.
  move : (env_preserve_trans HEa1Eega1 (env_preserve_le (mk_env_lneg_preserve Hmklneg) (pos_leb_trans Hga1ga2 (pos_leb_trans Hga2gu Hguge)))) => HEa1Elga1.
  move : (env_preserve_trans HEa1Elga1 (env_preserve_le (mk_env_xor_preserve Hmkxor) (pos_leb_trans Hga1ga2 (pos_leb_trans Hga2gu (pos_leb_trans Hguge Hgegl))))) => HEa1Exga1.
  move : (env_preserve_trans HEa1Exga1 (env_preserve_le (mk_env_zeroextend_preserve Hmkz) (pos_leb_trans Hga1ga2 (pos_leb_trans Hga2gu (pos_leb_trans Hguge (pos_leb_trans Hgegl Hglgx)))))) => HEa1Ezga1.
  move : (env_preserve_trans HEa1Ezga1 (env_preserve_le (mk_env_add_preserve Hmkadd) (pos_leb_trans Hga1ga2 (pos_leb_trans Hga2gu (pos_leb_trans Hguge (pos_leb_trans Hgegl (pos_leb_trans Hglgx Hgxgz))))))) => HEa1Eaga1{HEa1Eega1 HEa1Elga1 HEa1Exga1 HEa1Ezga1}.
  move : (env_preserve_trans (mk_env_zeroextend_preserve Hmkz) (env_preserve_le (mk_env_add_preserve Hmkadd) Hgxgz)) => HExEagx.
  move : (env_preserve_trans (mk_env_xor_preserve Hmkxor) (env_preserve_le HExEagx Hglgx)) => HElEagl.
  move : (env_preserve_trans (mk_env_lneg_preserve Hmklneg) (env_preserve_le HElEagl Hgegl)) => HEeEage.
  move : (env_preserve_trans (mk_env_eq_preserve Hmkeq) (env_preserve_le HEeEage Hguge)) => HEuEagu.
  move : (env_preserve_trans (mk_env_udiv_preserve' Hmkudiv) (env_preserve_le HEuEagu Hga2gu)) => HEa2Eaga2.
  case Hmsl1f : ((splitmsl ls1).2 == lit_ff); case Hmsl2f : ((splitmsl ls2).2 == lit_ff).
  - case => <- _ <- _; rewrite !interp_cnf_catrev.
    rewrite (env_preserve_cnf HEa1Euga1 (mk_env_abs_newer_cnf Hmkabs1 Htt Hgls1)) HEa1csa1. 
    rewrite (env_preserve_cnf (mk_env_udiv_preserve' Hmkudiv) Hga2csa2) HEa2csa2.
    rewrite (mk_env_udiv_sat' Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hgga1 Hga1ga2)) (newer_than_lits_le_newer Hga1la1 Hga1ga2) Hga2la2)//. 
  - rewrite (eqP Hmsl1f) !andFb; case ((splitmsl ls2).2 == lit_tt); case => <- _ <- _; rewrite !interp_cnf_catrev.
    + rewrite (env_preserve_cnf HEa1Enga1 Hga1csa1) HEa1csa1 (env_preserve_cnf HEa2Enga2 Hga2csa2) HEa2csa2.
      rewrite (env_preserve_cnf (mk_env_neg_preserve Hmkneg) Hgucsu) HEucsu (mk_env_neg_sat Hmkneg (newer_than_lit_le_newer Hff (pos_leb_trans Hgga1 (pos_leb_trans Hga1ga2 Hga2gu))) Hgulsu) //.
    + rewrite (env_preserve_cnf HEa1Eaga1 (mk_env_abs_newer_cnf Hmkabs1 Htt Hgls1)) HEa1csa1 (env_preserve_cnf (mk_env_add_preserve Hmkadd) Hgzcsz) HEzcsz HEacsa.
      rewrite (env_preserve_cnf HExEagx Hgxcsx) HExcsx (env_preserve_cnf HElEagl Hglcsl) HElcsl (env_preserve_cnf HEeEage Hgecse) HEecse (env_preserve_cnf HEuEagu Hgucsu) HEucsu (env_preserve_cnf HEa2Eaga2 Hga2csa2) HEa2csa2//.
  - rewrite (eqP Hmsl2f) !andbF; case ((splitmsl ls1).2 == lit_tt); case => <- _ <- _; rewrite !interp_cnf_catrev.
    + rewrite (env_preserve_cnf HEa1Enga1 Hga1csa1) HEa1csa1 (env_preserve_cnf HEa2Enga2 Hga2csa2) HEa2csa2.
      rewrite (env_preserve_cnf (mk_env_neg_preserve Hmkneg) Hgucsu) HEucsu (mk_env_neg_sat Hmkneg (newer_than_lit_le_newer Hff (pos_leb_trans Hgga1 (pos_leb_trans Hga1ga2 Hga2gu))) Hgulsu) //.
    + rewrite (env_preserve_cnf HEa1Eaga1 (mk_env_abs_newer_cnf Hmkabs1 Htt Hgls1)) HEa1csa1 (env_preserve_cnf (mk_env_add_preserve Hmkadd) Hgzcsz) HEzcsz HEacsa.
      rewrite (env_preserve_cnf HExEagx Hgxcsx) HExcsx (env_preserve_cnf HElEagl Hglcsl) HElcsl (env_preserve_cnf HEeEage Hgecse) HEecse (env_preserve_cnf HEuEagu Hgucsu) HEucsu (env_preserve_cnf HEa2Eaga2 Hga2csa2) HEa2csa2//.
  - case ((splitmsl ls1).2 == lit_tt); case ((splitmsl ls2).2 == lit_tt); case => <- _ <- _; rewrite !interp_cnf_catrev;
    try by (rewrite (env_preserve_cnf HEa1Eaga1 (mk_env_abs_newer_cnf Hmkabs1 Htt Hgls1)) HEa1csa1 (env_preserve_cnf (mk_env_add_preserve Hmkadd) Hgzcsz) HEzcsz HEacsa;
    rewrite (env_preserve_cnf HExEagx Hgxcsx) HExcsx (env_preserve_cnf HElEagl Hglcsl) HElcsl (env_preserve_cnf HEeEage Hgecse) HEecse (env_preserve_cnf HEuEagu Hgucsu) HEucsu (env_preserve_cnf HEa2Eaga2 Hga2csa2) HEa2csa2//).
    rewrite (env_preserve_cnf HEa1Euga1 (mk_env_abs_newer_cnf Hmkabs1 Htt Hgls1)) HEa1csa1. 
    rewrite (env_preserve_cnf (mk_env_udiv_preserve' Hmkudiv) Hga2csa2) HEa2csa2.
    rewrite (mk_env_udiv_sat' Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hgga1 Hga1ga2)) (newer_than_lits_le_newer Hga1la1 Hga1ga2) Hga2la2)//. 
Qed.

    (* Lemma bit_blast_sdiv_correct g ls1 ls2 g' cs qlrs rlrs E bs1 bs2 : *)
(*   bit_blast_sdiv g ls1 ls2 = (g', cs, qlrs, rlrs) -> *)
(*   size ls1 = size ls2 -> *)
(*   0 < size ls2 -> *)
(*   enc_bits E ls1 bs1 -> *)
(*   enc_bits E ls2 bs2 -> *)
(*   interp_cnf E (add_prelude cs) -> *)
(*   enc_bits E qlrs (sdivB bs1 bs2).1 /\ *)
(*   enc_bits E rlrs (sdivB bs1 bs2).2. *)
(* Proof. *)
(*  rewrite/bit_blast_sdiv /bit_blast_abs.
  dcase (bit_blast_neg g ls1) => [[[g_neg ] cs_neg] lrs_neg] Hbbneg.
  dcase (bit_blast_xor g ls1 (copy (size ls1) (splitmsl ls1).2)) => [[[g_xor ] cs_xor] lrs_xor] Hbbxor.
  dcase (bit_blast_zeroextend (size (splitmsl ls1).1) g_xor [:: (splitmsl ls1).2]) => [[[g_zext ] cs_zext] lrs_zext] Hbbzext.
  dcase (bit_blast_add g_zext lrs_xor lrs_zext) => [[[g_add] cs_add] lrs_add] Hbbadd.
  case Hls1mb1 :((splitmsl ls1).2 == lit_tt); case Hls1mb0 : ((splitmsl ls1).2 == lit_ff);
    case Hls2mb1 :((splitmsl ls2).2 == lit_tt); case Hls2mb0 : ((splitmsl ls2).2 == lit_ff);
      try (rewrite (eqP Hls1mb1) in Hls1mb0; discriminate); try (rewrite (eqP Hls2mb1) in Hls2mb0; discriminate).
  - rewrite /=.
    dcase (bit_blast_neg g_neg ls2)=> [[[g_neg1 ] cs_neg1] lrs_neg1] Hbbneg1.
    dcase (bit_blast_udiv g_neg1 lrs_neg lrs_neg1) => [[[[g_udiv ] cs_udiv] lqs_udiv] lrs_udiv] Hbbudiv.
    dcase (bit_blast_neg g_udiv lrs_udiv) => [[[g_neg3 ] cs_neg3] lrs_neg3] Hbbneg3.
    case => _ <- <- <-. move => Hsz12 Hsz2 Henc1 Henc2.
    rewrite 3!add_prelude_catrev. move/andP => [Hcsu Hcsneg3]. move/andP : Hcsu => [Hcsneg Hcsu].
    move/andP : Hcsneg => [Hcsneg Hcsneg1].
    move : (add_prelude_tt Hcsu) => Htt. 
    move : (enc_bit_msb Htt Henc1). rewrite/msl (eqP Hls1mb1). move => Hencmsb1.
    move : (add_prelude_enc_bit_true (msb bs1) Hcsu). rewrite Hencmsb1. move => Hmsb1t.
    move : (enc_bit_msb Htt Henc2). rewrite/msl (eqP Hls2mb1). move => Hencmsb2.
    move : (add_prelude_enc_bit_true (msb bs2) Hcsu). rewrite Hencmsb2. move => Hmsb2t.
    rewrite /sdivB /absB -Hmsb1t -Hmsb2t/=. 
    move : (bit_blast_neg_correct Hbbneg Henc1 Hcsneg) => Hencneg.
    move : (bit_blast_neg_correct Hbbneg1 Henc2 Hcsneg1) => Hencneg1.
    generalize Hsz12.
    rewrite (bit_blast_neg_size_ss Hbbneg1) (bit_blast_neg_size_ss Hbbneg). move => Hszn.
    move : (bit_blast_udiv_correct Hbbudiv Hszn Hencneg Hencneg1 Hcsu) => [Hencuq Hencur].
    move : (bit_blast_neg_correct Hbbneg3 Hencur Hcsneg3).
    have Hszaux : size (-# bs1)%bits = size (-# bs2)%bits
      by rewrite 2!size_negB -(enc_bits_size Henc1) -(enc_bits_size Henc2) Hsz12.
    rewrite udivB_negB_negB; last by rewrite -(enc_bits_size Henc1) -(enc_bits_size Henc2) Hsz12.
    move => Hencneg3.
    rewrite udivB_negB_negB in Hencuq; last by rewrite -(enc_bits_size Henc1) -(enc_bits_size Henc2) Hsz12.
      by rewrite Hencuq Hencneg3.
  - rewrite /=. 
    dcase (bit_blast_udiv g_neg lrs_neg ls2) => [[[[g_udiv ] cs_udiv] lqs_udiv] lrs_udiv] Hbbudiv.
    dcase (bit_blast_neg g_udiv lqs_udiv) => [[[g_neg2 ] cs_neg2] lrs_neg2] Hbbneg2.
    dcase (bit_blast_neg g_neg2 lrs_udiv) => [[[g_neg3 ] cs_neg3] lrs_neg3] Hbbneg3.
    case => _ <- <- <-. move => Hsz12 Hsz2 Henc1 Henc2.
    rewrite 4!add_prelude_catrev. move/andP => [Hcsu Hcsneg3]. move/andP : Hcsu => [Hcsneg Hcsneg2].
    move/andP : Hcsneg => [Hcsneg Hcsu]. move/andP : Hcsneg => [Hcsneg Hcsnil].
    move : (add_prelude_tt Hcsu) => Htt. 
    move : (enc_bit_msb Htt Henc1). rewrite/msl (eqP Hls1mb1). move => Hencmsb1.
    move : (add_prelude_enc_bit_true (msb bs1) Hcsu). rewrite Hencmsb1. move => Hmsb1t.
    move : (enc_bit_msb Htt Henc2). rewrite/msl (eqP Hls2mb0). move => Hencmsb2.
    move : (add_prelude_enc_bit_is_not_true (msb bs2) Hcsu). rewrite Hencmsb2. move => Hmsb2f.
    symmetry in Hmsb2f. rewrite->Bool.negb_true_iff in Hmsb2f.
    rewrite/sdivB /absB -Hmsb1t Hmsb2f/=.
    move : (bit_blast_neg_correct Hbbneg Henc1 Hcsneg) => Hencneg.
    generalize Hsz12.
    rewrite (bit_blast_neg_size_ss Hbbneg). move => Hszn.
    move : (bit_blast_udiv_correct Hbbudiv Hszn Hencneg Henc2 Hcsu) => [Hencuq Hencur].
    move : (bit_blast_neg_correct Hbbneg2 Hencuq Hcsneg2) => Hencneg2.
    move : (bit_blast_neg_correct Hbbneg3 Hencur Hcsneg3) => Hencneg3.
    by rewrite Hencneg2 Hencneg3.
  - rewrite (lock splitmsl) (lock bit_blast_eq) (lock bit_blast_lneg)/= -!lock. 
    dcase (bit_blast_xor g_neg ls2 (copy (size ls2) (splitmsl ls2).2))=> [[[g_xor1 ] cs_xor1] lrs_xor1] Hbbxor1.
    dcase (bit_blast_add g_xor1 lrs_xor1 ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff))=>[[[g_add1 ] cs_add1] lrs_add1] Hbbadd1.
    dcase (bit_blast_udiv g_add1 lrs_neg lrs_add1)=>[[[[g_udiv1] cs_udiv1] lqs_udiv1] lrs_udiv1] Hbbudiv1.
    dcase (bit_blast_eq g_udiv1 [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[g_eq] cs_eq] lrs_eq] Hbbeq.
    dcase (bit_blast_lneg g_eq lrs_eq) => [[[g_lneg] cs_lneg] lrs_lneg] Hbblneg.
    dcase (bit_blast_xor g_lneg lqs_udiv1 (copy (size ls1) lrs_lneg)) =>[[[g_xor2 ] cs_xor2] lrs_xor2] Hbbxor2.
    dcase (bit_blast_add g_xor2 lrs_xor2 (lrs_lneg :: copy (size (splitmsl ls1).1) lit_ff)) =>[[[g_add2 ] cs_add2] lrs_add2] Hbbadd2.
    dcase (bit_blast_xor g_add2 lrs_udiv1 (copy (size ls1) (splitmsl ls1).2)) =>[[[g_xor3 ] cs_xor3] lrs_xor3] Hbbxor3.
    dcase (bit_blast_add g_xor3 lrs_xor3 ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff)) =>[[[g_add3 ] cs_add3] lrs_add3] Hbbadd3.
    case => _ <- <- <-. move => Hsz12 Hsz2 Henc1 Henc2.
    rewrite 11!add_prelude_catrev/=. move/andP => [Hcsu Hcsadd3]. move/andP : Hcsu => [Hcsu Hcsnil1].
    move/andP : Hcsu => [Hcsu Hcsxor3]. move/andP : Hcsu => [Hcsu Hcsadd2]. move/andP : Hcsu => [Hcsu Hcsnil2].
    move/andP : Hcsu => [Hcsu Hcsxor2]. move/andP : Hcsu => [Hcsu Hcslneg]. move/andP : Hcsu => [Hcsu Hcseq].
    move/andP : Hcsu => [Hcsu Hcsu1]. move/andP : Hcsu => [Hcsneg Hcsu]. move/andP : Hcsu => [Hcsxor1 Hcsadd1].
    move : (add_prelude_tt Hcsu1) => Htt. 
    move : (add_prelude_ff Hcsu1) => Hff. 
    move : (enc_bit_msb Htt Henc1). rewrite/msl (eqP Hls1mb1). move => Hencmsb1.
    move : (add_prelude_enc_bit_true (msb bs1) Hcsu1). rewrite Hencmsb1. move => Hmsb1t.
    rewrite /sdivB /absB -Hmsb1t andbT /= !andbF eq_sym.
    move : (bit_blast_neg_correct Hbbneg Henc1 Hcsneg) => Hencnegbs1.
    move : (enc_bits_size Henc2) => Hszlb2.
    have Hencmsl2 : enc_bit E (splitmsl ls2).2 (splitmsb bs2).2 by rewrite (enc_bit_msb Htt Henc2).
    have Henccp2 : enc_bits E (copy (size ls2) (splitmsl ls2).2) (copy (size bs2) (splitmsb bs2).2) by rewrite -Hszlb2 (enc_bits_copy (size ls2) Hencmsl2).
    move : (bit_blast_xor_correct Hbbxor1 Henc2 Henccp2 Hcsxor1).
    move : (add_prelude_enc_bit_ff Hcsu1) => Hencff.
    have Henccp1 : (enc_bits E ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff) ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0)) by rewrite enc_bits_cons Hencmsl2 size_splitmsb size_splitmsl -Hszlb2 (enc_bits_copy (size ls2 -1) Hencff).
    have -> : (splitmsb bs2).2 = msb bs2 by done. 
    move => Hencxor1.
    have Haddr : ((bs2 ^# copy (size bs2) (msb bs2))%bits +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))%bits = ((bs2 ^# copy (size bs2) (msb bs2))%bits +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))%bits by done.
    move : (bit_blast_xor_size_max Hbbxor1). rewrite size_nseq maxnn.
    move => Hszxor1.
    have Hszadd1 : size lrs_xor1 = size ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff) by rewrite (lock splitmsl)/= size_nseq -lock size_splitmsl -addn1 (subnK Hsz2) -Hszxor1. 
    move : (bit_blast_add_correct Hbbadd1 Hencxor1 Henccp1 Haddr Hcsadd1 Hszadd1) => Hencadd1.
    move :(bit_blast_xor_size_max Hbbxor1). rewrite size_nseq maxnn (bit_blast_add_size_ss Hbbadd1 Hszadd1) -Hsz12 (bit_blast_neg_size_ss Hbbneg). move => Hszadd1neg. symmetry in Hszadd1neg.
    move : (bit_blast_udiv_correct Hbbudiv1 Hszadd1neg Hencnegbs1 Hencadd1 Hcsu1) => [Hencq Hencr].
    have Hszeq : size [:: (splitmsl ls1).2]= size [:: (splitmsl ls2).2] by done.
    have Henceq1 : enc_bits E [:: (splitmsl ls1).2] [:: (splitmsb bs1).2] by rewrite enc_bits_cons enc_bits_nil -/(msb bs1) -Hmsb1t (eqP Hls1mb1) (add_prelude_enc_bit_tt Hcsu1). 
    have Henceq2 : enc_bits E [:: (splitmsl ls2).2] [:: (splitmsb bs2).2] by rewrite enc_bits_cons enc_bits_nil Hencmsl2.
    move : (bit_blast_eq_correct Hbbeq Hszeq Henceq1 Henceq2 Hcseq) => Henceq.
    move : (bit_blast_lneg_correct Hbblneg Henceq Hcslneg) => Henclnegr.
    move : (enc_bits_size Henc1) => Hszlb1.
    move : (enc_bits_copy (size ls1) Henclnegr) => Henclnegcp. rewrite {2}Hszlb1 in Henclnegcp.
    move : (bit_blast_xor_correct Hbbxor2 Hencq Henclnegcp Hcsxor2) => Hencrxor2.
    generalize Hsz2; rewrite -{1}Hsz12; move => Hsz1.
    move : (bit_blast_neg_size_ss Hbbneg) => Hszneg.
    move : (bit_blast_add_size_ss Hbbadd1 Hszadd1) => Hszadd1rs.
    generalize Hszadd1rs.
    rewrite Hszxor1 -Hsz12 Hszneg => Hszu.
    move : (bit_blast_udiv_size_ss Hbbudiv1 Hszu) => [Hszuq Hszur]. 
    move : (bit_blast_xor_size_max Hbbxor2); rewrite size_nseq Hszuq -Hszu Hszneg maxnn.
    move => Hszxor2.
    have Hencrseqcp : enc_bits E  (lrs_lneg :: copy (size (splitmsl ls1).1) lit_ff) (([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]):: copy (size (splitmsb bs1).1) b0) by rewrite enc_bits_cons Henclnegr size_splitmsb size_splitmsl Hszlb1 /b0 (enc_bits_copy _ (add_prelude_enc_bit_ff Hcsu1)).
    have Hszadd2 : size lrs_xor2 = size (lrs_lneg :: copy (size (splitmsl ls1).1) lit_ff) by rewrite size_splitmsl/=size_nseq -addn1 (subnK Hsz1) Hszneg Hszxor2.
    have Hadd2rs : (((udivB (-# bs1)
                            (bs2 ^# copy (size bs2) (msb bs2) +#
                                 ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))).1
                                                                                        ^# copy (size bs1) ([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]))%bits +# (([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]) :: copy (size (splitmsb bs1).1) b0))%bits = (((udivB (-# bs1)
                                                                                                                                                                                                                                                                            (bs2 ^# copy (size bs2) (msb bs2) +#
                                                                                                                                                                                                                                                                                 ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))).1
                                                                                                                                                                                                                                                                                                                                        ^# copy (size bs1) ([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]))%bits +# (([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]) :: copy (size (splitmsb bs1).1) b0))%bits by done.
    move : (bit_blast_add_correct Hbbadd2 Hencrxor2 Hencrseqcp Hadd2rs Hcsadd2 Hszadd2).
    generalize Hencmsb1. rewrite -{1}(eqP Hls1mb1) /msb. move => Hencsplmsb1.
    have Henccpmsb1 : enc_bits E (copy (size ls1) (splitmsl ls1).2) (copy (size bs1) (splitmsb bs1).2) by rewrite Hszlb1 (enc_bits_copy _ Hencsplmsb1).
    move : (bit_blast_xor_correct Hbbxor3 Hencr Henccpmsb1 Hcsxor3) => Hencxor3r.
    have Henccpcmsb1 : enc_bits E ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff) ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false) by rewrite size_splitmsb size_splitmsl enc_bits_cons Hencsplmsb1 Hszlb1 (enc_bits_copy _ Hencff).
    have Hadd3rs : (((udivB (-# bs1)
                            (bs2 ^# copy (size bs2) (msb bs2) +#
                                 ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))).2
                                                                                        ^# copy (size bs1) (splitmsb bs1).2)%bits +# ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false))%bits =  (((udivB (-# bs1)
                                                                                                                                                                                                                (bs2 ^# copy (size bs2) (msb bs2) +#
                                                                                                                                                                                                                     ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))).2
                                                                                                                                                                                                                                                                            ^# copy (size bs1) (splitmsb bs1).2)%bits +# ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false))%bits by done.
    move : (bit_blast_xor_size_max Hbbxor3). rewrite size_nseq Hszur -Hszu -Hszneg maxnn. move => Hszxor3.
    have Hszadd3 : size lrs_xor3 = size ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff) by rewrite size_splitmsl/=size_nseq -addn1 (subnK Hsz1) Hszxor3.
    move : (bit_blast_add_correct Hbbadd3 Hencxor3r Henccpcmsb1 Hadd3rs Hcsadd3 Hszadd3).
    have Hexp2 : 1 < 2 ^ size bs2 by rewrite -Hszlb2 -{1}(expn0 2) (ltn_exp2l _ _ (ltnSn 1)).
    have His1 : (true :: zeros (size bs2 - 1)) = from_nat (size bs2) 1. apply/eqP. rewrite -to_nat_inj_ss; last rewrite /=size_zeros size_from_nat -Hszlb2 -addn1 (subnK Hsz2); first rewrite/= to_nat_zeros -muln2 mul0n addn0 (to_nat_from_nat_bounded Hexp2); first done. done.
    have Hszb12 : size bs1 = size bs2 by rewrite -Hszlb1 Hsz12 Hszlb2.
    case Hmsb2 : (msb bs2).
    + rewrite -/(msb bs2) Hmsb2 -/(msb bs1) -Hmsb1t size_splitmsb -/(zeros (size bs2 -1)) !eq_refl. 
      have -> : (bs2 ^# copy (size bs2) true)%bits = invB bs2 by rewrite xorBC xorB_copy_case.
      rewrite His1 {1 2}(invB_size_ss bs2) addB1 -/(negB bs2). 
      have Hszurem: (size ((udivB (-# bs1) (-# bs2)).2)%bits) = size bs1 by rewrite size_uremB size_negB.
      have Hszudiv: (size ((udivB (bs1) (bs2)).1)%bits) = size bs1 by rewrite size_udivB. 
      rewrite {1}xorBC -{1}Hszurem xorB_copy_case size_splitmsb -/(zeros (size bs1 -1)) .
      rewrite Hszb12 His1 -Hszb12 -{1}Hszurem (invB_size_ss ((udivB (-# bs1) (-# bs2)).2)%bits) addB1 -/(negB ((udivB (-# bs1) (-# bs2)).2)%bits) -/(negB ((udivB (-# bs1) (-# bs2)).1)%bits).
      rewrite udivB_negB_negB/=; last by rewrite -(enc_bits_size Henc1) -(enc_bits_size Henc2) Hsz12/=.
      have ->: (false :: zeros (size bs1 - 1)) = zeros (size bs1) by rewrite zeros_cons -addn1 -Hszlb1 (subnK Hsz1).
      rewrite addB0 unzip1_zip; last by rewrite size_xorB size_udivB size_zeros maxnn.
      by rewrite xorBC -{1}Hszudiv xorB_copy_case /=.
    + rewrite -/(msb bs2) Hmsb2 -/(msb bs1) -Hmsb1t size_splitmsb -/(zeros (size bs2 -1)) size_splitmsb/=.
      rewrite zeros_cons -addn1 -Hszlb2 (subnK Hsz2) Hszlb2.
      have -> : (bs2 ^# copy (size bs2) false)%bits = bs2 by rewrite xorBC xorB_copy_case.
      rewrite addB0 unzip1_zip; last by rewrite size_zeros.
      have Hszurem: (size ((udivB (-# bs1) (bs2)).2)%bits) = size bs1 by rewrite size_uremB size_negB.
      have Hszudiv: (size ((udivB (-# bs1) (bs2)).1)%bits) = size bs1 by rewrite size_udivB size_negB.
      rewrite Hszb12 His1 -Hszb12 -{1}Hszurem -{2}Hszudiv; repeat (rewrite xorBC xorB_copy_case).
      by rewrite -{1}Hszurem -(size_invB ((udivB (-# bs1)%bits bs2).2)%bits)  -{1}Hszudiv -(size_invB ((udivB (-# bs1)%bits bs2).1)%bits) (addB1 (~~#(udivB (-# bs1) bs2).2)%bits) (addB1 (~~#(udivB (-# bs1) bs2).1)%bits) -/(negB ((udivB (-# bs1) bs2).2)%bits) -/(negB ((udivB (-# bs1) bs2).1)%bits).
  - rewrite /=.
    dcase (bit_blast_neg g ls2) => [[[g_asb2] cs_abs2] lrs_abs2] Hbbabs2.
    dcase (bit_blast_udiv g_asb2 ls1 lrs_abs2)=> [[[[g_udiv] cs_udiv] lqs_udiv] lrs_udiv] Hbbudiv.
    dcase (bit_blast_neg g_udiv lqs_udiv)=> [[[g_neg1] cs_neg1] lrs_neg1] Hbbneg1.
    case => _ <- <- <-. move => Hsz12 Hsz2 Henc1 Henc2.
    rewrite !add_prelude_catrev. move/andP => [Hcsu Hcsneg1]. move/andP : Hcsu => [Hcsabs2 Hcsu].
    move : (bit_blast_neg_correct Hbbabs2 Henc2 Hcsabs2) => Hencabs2.
    generalize Hsz12. rewrite (bit_blast_neg_size_ss Hbbabs2). move => Hszabs2.
    move : (bit_blast_udiv_correct Hbbudiv Hszabs2 Henc1 Hencabs2 Hcsu)=> [Hencq Hencr].
    move : (bit_blast_neg_correct Hbbneg1 Hencq Hcsneg1) => Hencneg1.
    move : (add_prelude_tt Hcsu) => Htt. 
    move : (add_prelude_ff Hcsu) => Hff. 
    move : (enc_bit_msb Htt Henc1). rewrite/msl (eqP Hls1mb0). move => Hencmsb1.
    move : (enc_bit_msb Htt Henc2). rewrite/msl (eqP Hls2mb1). move => Hencmsb2.
    move : (add_prelude_enc_bit_is_not_true (msb bs1) Hcsu). rewrite Hencmsb1. move => Hmsb1f. symmetry in Hmsb1f. rewrite<- Bool.negb_false_iff in Hmsb1f. rewrite Bool.negb_involutive in Hmsb1f. 
    move : (add_prelude_enc_bit_true (msb bs2) Hcsu). rewrite Hencmsb2. move => Hmsb2t. symmetry in Hmsb2t.
    rewrite /sdivB /absB Hmsb2t Hmsb1f/=.
    by rewrite Hencr Hencneg1.
  - rewrite/=.
    dcase (bit_blast_udiv g ls1 ls2 ) =>[[[[g_udiv] cs_udiv] qs_udiv] rs_udiv] Hbbudiv.
    case => _ <- <- <-.
    move => Hsz12 Hsz2 Henc1 Henc2. rewrite add_prelude_catrev. move/andP => [Hcsu Hcsnil].
    move : (add_prelude_tt Hcsu) => Htt. 
    move : (add_prelude_ff Hcsu) => Hff. 
    move : (enc_bit_msb Htt Henc1). rewrite/msl (eqP Hls1mb0). move => Hencmsb1.
    move : (enc_bit_msb Htt Henc2). rewrite/msl (eqP Hls2mb0). move => Hencmsb2.
    move : (add_prelude_enc_bit_is_not_true (msb bs1) Hcsu). rewrite Hencmsb1. move => Hmsb1f. symmetry in Hmsb1f. rewrite<- Bool.negb_false_iff in Hmsb1f. rewrite Bool.negb_involutive in Hmsb1f. 
    move : (add_prelude_enc_bit_is_not_true (msb bs2) Hcsu). rewrite Hencmsb2. move => Hmsb2f. symmetry in Hmsb2f. rewrite<- Bool.negb_false_iff in Hmsb2f. rewrite Bool.negb_involutive in Hmsb2f. 
    rewrite /sdivB /absB Hmsb2f Hmsb1f/=.
    exact : (bit_blast_udiv_correct Hbbudiv Hsz12 Henc1 Henc2 Hcsu).
  - rewrite (lock splitmsl) (lock bit_blast_eq) (lock bit_blast_lneg)/= -!lock. 
    dcase (bit_blast_xor g ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[g_xor1] cs_xor1] lrs_xor1] Hbbxor1.
    dcase (bit_blast_add g_xor1 lrs_xor1 ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff)) => [[[g_add1] cs_add1] lrs_add1] Hbbadd1.
    dcase (bit_blast_udiv g_add1 ls1 lrs_add1) =>[[[[g_udiv] cs_udiv] qs_udiv] rs_udiv] Hbbudiv.
    dcase (bit_blast_eq g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[g_eq] cs_eq] lrs_eq] Hbbeq.
    dcase (bit_blast_lneg g_eq lrs_eq) => [[[g_lneg] cs_lneg] lrs_lneg] Hbblneg.
    dcase (bit_blast_xor g_lneg qs_udiv (copy (size ls1) lrs_lneg)) =>[[[g_xor2 ] cs_xor2] lrs_xor2] Hbbxor2.
    dcase (bit_blast_add g_xor2 lrs_xor2 (lrs_lneg :: copy (size (splitmsl ls1).1) lit_ff)) =>[[[g_add2 ] cs_add2] lrs_add2] Hbbadd2.
    dcase (bit_blast_xor g_add2 rs_udiv (copy (size ls1) (splitmsl ls1).2)) =>[[[g_xor3 ] cs_xor3] lrs_xor3] Hbbxor3.
    dcase (bit_blast_add g_xor3 lrs_xor3 ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff)) =>[[[g_add3 ] cs_add3] lrs_add3] Hbbadd3.
    case => _ <- <- <-. move => Hsz12 Hsz2 Henc1 Henc2.
    rewrite 10!add_prelude_catrev/=. move/andP => [Hcsu Hcsadd3]. move/andP : Hcsu => [Hcsu Hcsnil1].
    move/andP : Hcsu => [Hcsu Hcsxor3]. move/andP : Hcsu => [Hcsu Hcsadd2]. move/andP : Hcsu => [Hcsu Hcsnil2].
    move/andP : Hcsu => [Hcsu Hcsxor2]. move/andP : Hcsu => [Hcsu Hcslneg]. move/andP : Hcsu => [Hcsu Hcseq].
    move/andP : Hcsu => [Hcsu Hcsu1]. move/andP : Hcsu => [Hcsxor1 Hcsadd1]. 
    move : (add_prelude_tt Hcsu1) => Htt. 
    move : (add_prelude_ff Hcsu1) => Hff. 
    move : (enc_bit_msb Htt Henc1). rewrite/msl (eqP Hls1mb0). move => Hencmsb1.
    move : (add_prelude_enc_bit_is_not_true (msb bs1) Hcsu1). rewrite Hencmsb1. move => Hmsb1f.
    symmetry in Hmsb1f. rewrite->Bool.negb_true_iff in Hmsb1f.
    rewrite /sdivB /absB Hmsb1f andbT /= !andbF eq_sym.
    move : (enc_bits_size Henc2) => Hszlb2.
    have Hencmsl2 : enc_bit E (splitmsl ls2).2 (splitmsb bs2).2 by rewrite (enc_bit_msb Htt Henc2).
    have Hencmsl1 : enc_bit E (splitmsl ls1).2 (splitmsb bs1).2 by rewrite (enc_bit_msb Htt Henc1).
    have Henccp2 : enc_bits E (copy (size ls2) (splitmsl ls2).2) (copy (size bs2) (splitmsb bs2).2) by rewrite -Hszlb2 (enc_bits_copy (size ls2) Hencmsl2).
    move : (bit_blast_xor_correct Hbbxor1 Henc2 Henccp2 Hcsxor1).
    move : (add_prelude_enc_bit_ff Hcsu1) => Hencff.
    have Henccp1 : (enc_bits E ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff) ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0)) by rewrite enc_bits_cons Hencmsl2 size_splitmsb size_splitmsl -Hszlb2 (enc_bits_copy (size ls2 -1) Hencff).
    have -> : (splitmsb bs2).2 = msb bs2 by done. 
    move => Hencxor1.
    have Haddr : ((bs2 ^# copy (size bs2) (msb bs2))%bits +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))%bits = ((bs2 ^# copy (size bs2) (msb bs2))%bits +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))%bits by done.
    move : (bit_blast_xor_size_max Hbbxor1). rewrite size_nseq maxnn.
    move => Hszxor1.
    have Hszadd1 : size lrs_xor1 = size ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff) by rewrite (lock splitmsl)/= size_nseq -lock size_splitmsl -addn1 (subnK Hsz2) -Hszxor1. 
    move : (bit_blast_add_correct Hbbadd1 Hencxor1 Henccp1 Haddr Hcsadd1 Hszadd1) => Hencadd1.
    move : (bit_blast_add_size_ss Hbbadd1 Hszadd1). rewrite Hszxor1 -Hsz12. move => Hsz1add1.
    move : (bit_blast_udiv_correct Hbbudiv Hsz1add1 Henc1 Hencadd1 Hcsu1) => [Hencq Hencr].
    generalize Hencmsl2. rewrite -enc_bits_seq1. move => Henceq2.
    generalize Hencmsl1. rewrite -enc_bits_seq1. move => Henceq1.
    have Hszeq : size [:: (splitmsl ls1).2]= size [:: (splitmsl ls2).2] by done.
    move : (bit_blast_eq_correct Hbbeq Hszeq Henceq1 Henceq2 Hcseq) => Henceq.
    move : (bit_blast_lneg_correct Hbblneg Henceq Hcslneg) => Henclnegr.
    move : (enc_bits_size Henc1) => Hszlb1.
    move : (enc_bits_copy (size ls1) Henclnegr) => Henclnegcp. rewrite {2}Hszlb1 in Henclnegcp.
    move : (bit_blast_xor_correct Hbbxor2 Hencq Henclnegcp Hcsxor2) => Hencrxor2.
    generalize Hsz2; rewrite -{1}Hsz12; move => Hsz1.
    move : (bit_blast_neg_size_ss Hbbneg) => Hszneg.
    move : (bit_blast_add_size_ss Hbbadd1 Hszadd1) => Hszadd1rs.
    generalize Hszadd1rs.
    rewrite Hszxor1 -Hsz12 Hszneg => Hszu.
    have Hszu1 : size ls1 = size lrs_add1 by rewrite Hszneg.
    move : (bit_blast_udiv_size_ss Hbbudiv Hszu1) => [Hszuq Hszur]. 
    move : (bit_blast_xor_size_max Hbbxor2); rewrite size_nseq Hszuq -Hszu Hszneg maxnn.
    move => Hszxor2.
    have Hencrseqcp : enc_bits E  (lrs_lneg :: copy (size (splitmsl ls1).1) lit_ff) (([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]):: copy (size (splitmsb bs1).1) b0) by rewrite enc_bits_cons Henclnegr size_splitmsb size_splitmsl Hszlb1 /b0 (enc_bits_copy _ (add_prelude_enc_bit_ff Hcsu1)).
    have Hszadd2 : size lrs_xor2 = size (lrs_lneg :: copy (size (splitmsl ls1).1) lit_ff) by rewrite size_splitmsl/=size_nseq -addn1 (subnK Hsz1) Hszneg Hszxor2.
    have Hadd2rs : (((udivB bs1 (bs2 ^# copy (size bs2) (msb bs2) +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))).1 ^# copy (size bs1) ([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]))%bits +# (([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]) :: copy (size (splitmsb bs1).1) b0))%bits = (((udivB bs1 (bs2 ^# copy (size bs2) (msb bs2) +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))).1 ^# copy (size bs1) ([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]))%bits +# (([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]) :: copy (size (splitmsb bs1).1) b0))%bits by done.
    move : (bit_blast_add_correct Hbbadd2 Hencrxor2 Hencrseqcp Hadd2rs Hcsadd2 Hszadd2).
    have Henccpmsb1 : enc_bits E (copy (size ls1) (splitmsl ls1).2) (copy (size bs1) (splitmsb bs1).2) by rewrite Hszlb1 (enc_bits_copy _ Hencmsl1).
    move : (bit_blast_xor_correct Hbbxor3 Hencr Henccpmsb1 Hcsxor3) => Hencxor3r.
    have Henccpcmsb1 : enc_bits E ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff) ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false) by rewrite size_splitmsb size_splitmsl enc_bits_cons Hencmsl1 Hszlb1 (enc_bits_copy _ Hencff).
    have Hadd3rs : (((udivB bs1 (bs2 ^# copy (size bs2) (msb bs2) +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))).2 ^# copy (size bs1) (splitmsb bs1).2)%bits +# ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false))%bits = (((udivB bs1 (bs2 ^# copy (size bs2) (msb bs2) +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))).2 ^# copy (size bs1) (splitmsb bs1).2)%bits +# ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false))%bits by done.
    move : (bit_blast_xor_size_max Hbbxor3). rewrite size_nseq Hszur -Hszu -Hszneg maxnn. move => Hszxor3.
    have Hszadd3 : size lrs_xor3 = size ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff) by rewrite size_splitmsl/=size_nseq -addn1 (subnK Hsz1) Hszxor3.
    move : (bit_blast_add_correct Hbbadd3 Hencxor3r Henccpcmsb1 Hadd3rs Hcsadd3 Hszadd3).
    have Hexp2 : 1 < 2 ^ size bs2 by rewrite -Hszlb2 -{1}(expn0 2) (ltn_exp2l _ _ (ltnSn 1)).
    have His1 : (true :: zeros (size bs2 - 1)) = from_nat (size bs2) 1. apply/eqP. rewrite -to_nat_inj_ss; last rewrite /=size_zeros size_from_nat -Hszlb2 -addn1 (subnK Hsz2); first rewrite/= to_nat_zeros -muln2 mul0n addn0 (to_nat_from_nat_bounded Hexp2); first done. done.
    have Hszb12 : size bs1 = size bs2 by rewrite -Hszlb1 Hsz12 Hszlb2.
    case Hmsb2 : (msb bs2).
    + rewrite -/(msb bs2) Hmsb2 -/(msb bs1) Hmsb1f size_splitmsb -/(zeros (size bs2 -1)) size_splitmsb /=.
      have -> : (bs2 ^# copy (size bs2) true)%bits = invB bs2 by rewrite xorBC xorB_copy_case.
      rewrite His1 {1 2}(invB_size_ss bs2) addB1 -/(negB bs2).
      have Hszurem: (size ((udivB (bs1) (-# bs2)).2)%bits) = size bs1 by rewrite size_uremB.
      have Hszudiv: (size ((udivB (bs1) (-# bs2)).1)%bits) = size bs1 by rewrite size_udivB. 
      rewrite {1}xorBC -{1}Hszurem xorB_copy_case -/(zeros (size bs1 -1)) zeros_cons addB0 unzip1_zip; last by rewrite -addn1 -Hszlb1 (subnK Hsz1) size_uremB size_zeros Hszlb1. 
      by rewrite Hszb12 His1 -Hszb12 -{1}Hszudiv xorBC xorB_copy_case -Hszudiv (invB_size_ss ( (udivB bs1 (-# bs2)).1)%bits) addB1 -/(negB ((udivB (bs1) (-# bs2)).1)%bits). 
    + rewrite -/(msb bs2) Hmsb2 -/(msb bs1) Hmsb1f size_splitmsb -/(zeros (size bs2 -1)) size_splitmsb/=.
      rewrite 2!zeros_cons -addn1 -Hszlb2 (subnK Hsz2) Hszlb2.
      rewrite addB0 unzip1_zip; last by rewrite size_zeros size_xorB size_uremB -Hszlb1 -addn1 (subnK Hsz1) size_nseq maxnn.
      rewrite addB0 unzip1_zip; last by rewrite size_xorB size_zeros maxnn.
      rewrite addB0 unzip1_zip; last by rewrite size_zeros size_xorB size_udivB -addn1 -Hszlb1 (subnK Hsz1) size_nseq maxnn.
      have -> : (bs2 ^# copy (size bs2) false)%bits = bs2 by rewrite xorBC xorB_copy_case.
      rewrite -{1}(size_uremB bs1 bs2) -{1}(size_udivB bs1 bs2).
      by repeat (rewrite xorBC xorB_copy_case).
  - rewrite (lock splitmsl) (lock bit_blast_eq) (lock bit_blast_lneg)/= -!lock.
    dcase (bit_blast_neg g_add ls2) => [[[g_neg1] cs_neg1] lrs_neg1] Hbbneg1.
    dcase (bit_blast_udiv g_neg1 lrs_add lrs_neg1) =>[[[[g_udiv] cs_udiv] qs_udiv] rs_udiv] Hbbudiv.
    dcase (bit_blast_eq g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[g_eq] cs_eq] lrs_eq] Hbbeq.
    dcase (bit_blast_lneg g_eq lrs_eq) => [[[g_lneg] cs_lneg] lrs_lneg] Hbblneg.
    dcase (bit_blast_xor g_lneg qs_udiv (copy (size ls1) lrs_lneg)) =>[[[g_xor2 ] cs_xor2] lrs_xor2] Hbbxor2.
    dcase (bit_blast_add g_xor2 lrs_xor2 (lrs_lneg :: copy (size (splitmsl ls1).1) lit_ff)) =>[[[g_add2 ] cs_add2] lrs_add2] Hbbadd2.
    dcase (bit_blast_xor g_add2 rs_udiv (copy (size ls1) (splitmsl ls1).2)) =>[[[g_xor3 ] cs_xor3] lrs_xor3] Hbbxor3.
    dcase (bit_blast_add g_xor3 lrs_xor3 ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff)) =>[[[g_add3 ] cs_add3] lrs_add3] Hbbadd3.
    case => _ <- <- <-. move => Hsz12 Hsz2 Henc1 Henc2.
    rewrite 12!add_prelude_catrev/=. move/andP => [Hcsu Hcsadd3]. move/andP : Hcsu => [Hcsu Hcsnil1].
    move/andP : Hcsu => [Hcsu Hcsxor3]. move/andP : Hcsu => [Hcsu Hcsadd2]. move/andP : Hcsu => [Hcsu Hcsnil2].
    move/andP : Hcsu => [Hcsu Hcsxor2]. move/andP : Hcsu => [Hcsu Hcslneg]. move/andP : Hcsu => [Hcsu Hcseq].
    move/andP : Hcsu => [Hcsu Hcsu1]. move/andP : Hcsu => [Hcsu Hcsneg1]. move/andP : Hcsu => [Hcsxor Hcsu].
    move/andP : Hcsu => [Hcszext Hcsadd].
    move : (add_prelude_tt Hcsu1) => Htt. 
    move : (add_prelude_ff Hcsu1) => Hff. 
    move : (enc_bit_msb Htt Henc2). rewrite/msl (eqP Hls2mb1). move => Hencmsb2.
    move : (add_prelude_enc_bit_true (msb bs2) Hcsu1). rewrite Hencmsb2. move => Hmsb2t.
    symmetry in Hmsb2t.
    generalize Hsz2; rewrite -{1}Hsz12; move => Hsz1.
    rewrite /sdivB /absB Hmsb2t /=. 
    move : (enc_bits_size Henc1) => Hszlb1.
    move : (enc_bits_size Henc2) => Hszlb2.
    have Hencmsl2 : enc_bit E (splitmsl ls2).2 (splitmsb bs2).2 by rewrite (enc_bit_msb Htt Henc2).
    have Hencmsl1 : enc_bit E (splitmsl ls1).2 (splitmsb bs1).2 by rewrite (enc_bit_msb Htt Henc1).
    have Henccp2 : enc_bits E (copy (size ls1) (splitmsl ls1).2) (copy (size bs1) (splitmsb bs1).2) by rewrite -Hszlb1 (enc_bits_copy (size ls1) Hencmsl1).
    move : (bit_blast_xor_correct Hbbxor Henc1 Henccp2 Hcsxor) => Hencxor.
    move : (add_prelude_enc_bit_ff Hcsu1) => Hencff.
    generalize Hencmsl1. rewrite -enc_bits_seq1. move => Hencseq1.
    move : (bit_blast_zeroextend_correct Hbbzext Hencseq1 Hcszext) => Henczext.
    move : (bit_blast_zeroextend_size Hbbzext). rewrite size_splitmsl -addn1 (subnK Hsz1). move => Hszzext.
    have Hszadd : size lrs_xor = size lrs_zext by rewrite (bit_blast_xor_size_max Hbbxor) size_nseq maxnn Hszzext.
    have Haddr : ((bs1 ^# copy (size bs1) (splitmsb bs1).2)%bits +# (zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]))%bits = ((bs1 ^# copy (size bs1) (splitmsb bs1).2)%bits +# (zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]))%bits by done.
    move : (bit_blast_add_correct Hbbadd Hencxor Henczext Haddr Hcsadd Hszadd) => Hencaddr.
    move : (bit_blast_neg_correct Hbbneg1 Henc2 Hcsneg1) => Hencnegr1.
    move : (bit_blast_add_size_ss Hbbadd Hszadd). rewrite Hszadd Hszzext Hsz12 (bit_blast_neg_size_ss Hbbneg1).
    move => Hszneg1add. symmetry in Hszneg1add.
    move : (bit_blast_udiv_correct Hbbudiv Hszneg1add Hencaddr Hencnegr1 Hcsu1) => [Hencq Hencr].
    generalize Hencmsl2. rewrite -enc_bits_seq1. move => Hencseq2.
    have Hszeq : size [:: (splitmsl ls1).2]= size [:: (splitmsl ls2).2] by done.
    move : (bit_blast_eq_correct Hbbeq Hszeq Hencseq1 Hencseq2 Hcseq) => Henceq.
    move : (bit_blast_lneg_correct Hbblneg Henceq Hcslneg) => Henclnegr.
    move : (enc_bits_copy (size ls1) Henclnegr) => Henclnegcp. rewrite {2}Hszlb1 in Henclnegcp.
    move : (bit_blast_xor_correct Hbbxor2 Hencq Henclnegcp Hcsxor2) => Hencrxor2.
    move : (bit_blast_neg_size_ss Hbbneg) => Hszneg.
    move : (bit_blast_add_size_ss Hbbadd Hszadd) => Hszadd1rs.
    move : (bit_blast_neg_size_ss Hbbneg1) => Hszneg1.
    generalize Hszadd1rs. rewrite Hszadd Hszzext Hsz12 Hszneg1. move => Hszu; symmetry in Hszu.
    have Hszu1 : size ls1 = size lrs_add by rewrite -Hszadd1rs Hszadd Hszzext.
    move : (bit_blast_udiv_size_ss Hbbudiv Hszu) => [Hszuq Hszur]. 
    move : (bit_blast_xor_size_max Hbbxor2). rewrite size_nseq Hszuq -Hszneg1 -Hsz12 maxnn.
    move => Hszxor2.
    have Hencrseqcp : enc_bits E  (lrs_lneg :: copy (size (splitmsl ls1).1) lit_ff) (([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]):: copy (size (splitmsb bs1).1) b0) by rewrite enc_bits_cons Henclnegr size_splitmsb size_splitmsl Hszlb1 /b0 (enc_bits_copy _ (add_prelude_enc_bit_ff Hcsu1)).
    have Hszadd2 : size lrs_xor2 = size (lrs_lneg :: copy (size (splitmsl ls1).1) lit_ff) by rewrite size_splitmsl/=size_nseq -addn1 (subnK Hsz1) Hszneg Hszxor2.
    have Hadd2rs : (((udivB (bs1 ^# copy (size bs1) (splitmsb bs1).2 +# zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]) (-# bs2)).1 ^# copy (size bs1) ([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]))%bits +# (([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]) :: copy (size (splitmsb bs1).1) b0))%bits = (((udivB (bs1 ^# copy (size bs1) (splitmsb bs1).2 +# zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]) (-# bs2)).1 ^# copy (size bs1) ([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]))%bits +# (([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]) :: copy (size (splitmsb bs1).1) b0))%bits by done.
    (*(((udivB bs1 (bs2 ^# copy (size bs2) (msb bs2) +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))).1 ^# copy (size bs1) ([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]))%bits +# (([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]) :: copy (size (splitmsb bs1).1) b0))%bits = (((udivB bs1 (bs2 ^# copy (size bs2) (msb bs2) +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))).1 ^# copy (size bs1) ([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]))%bits +# (([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]) :: copy (size (splitmsb bs1).1) b0))%bits by done.*)
    move : (bit_blast_add_correct Hbbadd2 Hencrxor2 Hencrseqcp Hadd2rs Hcsadd2 Hszadd2).
    move : (bit_blast_xor_correct Hbbxor3 Hencr Henccp2 Hcsxor3) => Hencxor3r.
    have Henccpcmsb1 : enc_bits E ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff) ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false) by rewrite size_splitmsb size_splitmsl enc_bits_cons Hencmsl1 Hszlb1 (enc_bits_copy _ Hencff).
    have Hadd3rs : (((udivB (bs1 ^# copy (size bs1) (splitmsb bs1).2 +# zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]) (-# bs2)).2 ^# copy (size bs1) (splitmsb bs1).2)%bits +# ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false))%bits = (((udivB (bs1 ^# copy (size bs1) (splitmsb bs1).2 +# zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]) (-# bs2)).2 ^# copy (size bs1) (splitmsb bs1).2)%bits +# ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false))%bits by done.
    move : (bit_blast_xor_size_max Hbbxor3). rewrite size_nseq Hszur -Hszneg1 -Hsz12 maxnn. move => Hszxor3.
    have Hszadd3 : size lrs_xor3 = size ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff) by rewrite size_splitmsl/=size_nseq -addn1 (subnK Hsz1) Hszxor3.
    move : (bit_blast_add_correct Hbbadd3 Hencxor3r Henccpcmsb1 Hadd3rs Hcsadd3 Hszadd3).
    have Hexp2 : 1 < 2 ^ size bs2 by rewrite -Hszlb2 -{1}(expn0 2) (ltn_exp2l _ _ (ltnSn 1)).
    have His1 : (true :: zeros (size bs2 - 1)) = from_nat (size bs2) 1. apply/eqP. rewrite -to_nat_inj_ss; last rewrite /=size_zeros size_from_nat -Hszlb2 -addn1 (subnK Hsz2); first rewrite/= to_nat_zeros -muln2 mul0n addn0 (to_nat_from_nat_bounded Hexp2); first done. done.
    have His1' : zext (size ls1 - 1) [:: true] = from_nat (size ls1) 1. apply/eqP. rewrite -to_nat_inj_ss; last by rewrite size_zext size_from_nat /= addnC (subnK Hsz1). rewrite to_nat_zext/= -muln2 mul0n addn0 to_nat_from_nat_bounded ; last by rewrite Hsz12 Hszlb2 Hexp2. done.
    have Hszb12 : size bs1 = size bs2 by rewrite -Hszlb1 Hsz12 Hszlb2.
    case Hmsb1 : (msb bs1).
    + rewrite -/(msb bs1) -/(msb bs2) Hmsb1 Hmsb2t size_splitmsl size_splitmsb/=.
      have -> : (bs1 ^# copy (size bs1) true)%bits = invB bs1 by rewrite xorBC xorB_copy_case.
      rewrite His1' Hszlb1 {1 4}(invB_size_ss bs1) addB1 -/(negB bs1) {2}Hszb12 His1.
      have Hszurem: (size ((udivB (-# bs1)%bits (-# bs2)).2)%bits) = size bs1 by rewrite size_uremB size_negB.
      have Hszudiv: (size ((udivB (-# bs1)%bits (-# bs2)).1)%bits) = size bs1 by rewrite size_udivB size_negB. 
      rewrite {1}xorBC -{1}Hszurem xorB_copy_case -{1}Hszb12 -{1}Hszurem (invB_size_ss ((udivB (-# bs1) (-# bs2)).2))%bits addB1 -/(negB ((udivB (-# bs1) (-# bs2)).2)%bits).
      by rewrite {1}xorBC -{1}Hszudiv xorB_copy_case zeros_cons -addn1 -{1}Hszlb1 (subnK Hsz1) Hszlb1 addB0 unzip1_zip; last by rewrite size_udivB size_zeros size_negB.
    + rewrite -/(msb bs1) -/(msb bs2) Hmsb1 Hmsb2t size_splitmsl size_splitmsb/=.
      have ->: [:: false] = zeros 1 by done. 
      rewrite zeros_cons zext_zero (subnK Hsz1) addB0 unzip1_zip; last by rewrite size_xorB size_uremB size_addB size_xorB !size_zeros -Hszlb1 -addn1 (subnK Hsz1) maxnn minnn maxnn.
      rewrite addB0 unzip1_zip; last by rewrite size_xorB size_zeros Hszlb1 size_nseq maxnn.
      have -> : (bs1 ^# copy (size bs1) false)%bits = bs1 by rewrite xorBC xorB_copy_case.
      have Hszurem: (size ((udivB (bs1)%bits (-# bs2)).2)%bits) = size bs1 by rewrite size_uremB.
      have Hszudiv: (size ((udivB (bs1)%bits (-# bs2)).1)%bits) = size bs1 by rewrite size_udivB.
      rewrite xorBC -{1}Hszurem xorB_copy_case.
      by rewrite {2}Hszb12 His1 -Hszb12 -Hszudiv xorBC xorB_copy_case (invB_size_ss ((udivB bs1 (-# bs2)).1)%bits) addB1 -/(negB ((udivB bs1 (-# bs2)).1)%bits).
  - rewrite (lock splitmsl) (lock bit_blast_eq) (lock bit_blast_lneg)/= -!lock.
    dcase (bit_blast_udiv g_add lrs_add ls2) => [[[[g_udiv] cs_udiv] qs_udiv] rs_udiv] Hbbudiv.
    dcase (bit_blast_eq g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[g_eq] cs_eq] r_eq] Hbbeq.
    dcase (bit_blast_lneg g_eq r_eq) => [[[g_lneg] cs_lneg] r_lneg] Hbblneg.
    dcase (bit_blast_xor g_lneg qs_udiv (copy (size ls1) r_lneg)) => [[[g_xor1] cs_xor1] r_xor1] Hbbxor1.
    dcase (bit_blast_add g_xor1 r_xor1 (r_lneg :: copy (size (splitmsl ls1).1) lit_ff) ) => [[[g_add1] cs_add1] r_add1] Hbbadd1.
    dcase (bit_blast_xor g_add1 rs_udiv (copy (size ls1) (splitmsl ls1).2)) => [[[g_xor2] cs_xor2] r_xor2] Hbbxor2.
    dcase (bit_blast_add g_xor2 r_xor2 ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff)) => [[[g_add2] cs_add2] r_add2] Hbbadd2.
    case => _ <- <- <-. move => Hsz12 Hsz2 Henc1 Henc2. rewrite !add_prelude_catrev.
    move/andP => [Hcsu Hcsadd2].
    move/andP : Hcsu => [Hcsu Hcsnil]. move/andP : Hcsu => [Hcsu Hcsxor2]. move/andP : Hcsu => [Hcsu Hcsadd1].
    move/andP : Hcsu => [Hcsu Hcsnil2]. move/andP : Hcsu => [Hcsu Hcsxor1]. move/andP : Hcsu => [Hcsu Hcslneg].
    move/andP : Hcsu => [Hcsu Hcseq]. move/andP : Hcsu => [Hcsu Hcsu1]. move/andP : Hcsu => [Hcsu Hcsnil3].
    move/andP : Hcsu => [Hcsxor Hcsu]. move/andP : Hcsu => [Hcszext Hcsadd].
    move : (add_prelude_tt Hcsu1) => Htt. 
    move : (add_prelude_ff Hcsu1) => Hff. 
    move : (enc_bit_msb Htt Henc2). rewrite/msl (eqP Hls2mb0). move => Hencmsb2.
    move : (add_prelude_enc_bit_is_not_true (msb bs2) Hcsu1). rewrite Hencmsb2. move => Hmsb2f.
    symmetry in Hmsb2f. rewrite->Bool.negb_true_iff in Hmsb2f.
    generalize Hsz2; rewrite -{1}Hsz12; move => Hsz1.
    rewrite /sdivB /absB Hmsb2f /=. 
    move : (enc_bits_size Henc1) => Hszlb1.
    move : (enc_bits_size Henc2) => Hszlb2.
    have Hencmsl2 : enc_bit E (splitmsl ls2).2 (splitmsb bs2).2 by rewrite (enc_bit_msb Htt Henc2).
    have Hencmsl1 : enc_bit E (splitmsl ls1).2 (splitmsb bs1).2 by rewrite (enc_bit_msb Htt Henc1).
    have Henccp2 : enc_bits E (copy (size ls1) (splitmsl ls1).2) (copy (size bs1) (splitmsb bs1).2) by rewrite -Hszlb1 (enc_bits_copy (size ls1) Hencmsl1).
    move : (bit_blast_xor_correct Hbbxor Henc1 Henccp2 Hcsxor) => Hencxor.
    move : (add_prelude_enc_bit_ff Hcsu1) => Hencff.
    generalize Hencmsl1. rewrite -enc_bits_seq1. move => Hencseq1.
    move : (bit_blast_zeroextend_correct Hbbzext Hencseq1 Hcszext) => Henczext.
    move : (bit_blast_zeroextend_size Hbbzext). rewrite size_splitmsl -addn1 (subnK Hsz1). move => Hszzext.
    have Hszadd : size lrs_xor = size lrs_zext by rewrite (bit_blast_xor_size_max Hbbxor) size_nseq maxnn Hszzext.
    have Haddr : ((bs1 ^# copy (size bs1) (splitmsb bs1).2)%bits +# (zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]))%bits = ((bs1 ^# copy (size bs1) (splitmsb bs1).2)%bits +# (zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]))%bits by done.
    move : (bit_blast_add_correct Hbbadd Hencxor Henczext Haddr Hcsadd Hszadd) => Hencaddr.
    move : (bit_blast_add_size_max Hbbadd). rewrite Hszadd maxnn Hszzext Hsz12. move => Hszls2add. symmetry in Hszls2add.
    move : (bit_blast_udiv_correct Hbbudiv Hszls2add Hencaddr Henc2 Hcsu1) => [Hencq Hencr].
    generalize Hencmsl2. rewrite -enc_bits_seq1. move => Hencseq2.
    have Hszeq : size [:: (splitmsl ls1).2]= size [:: (splitmsl ls2).2] by done.
    move : (bit_blast_eq_correct Hbbeq Hszeq Hencseq1 Hencseq2 Hcseq) => Henceq.
    move : (bit_blast_lneg_correct Hbblneg Henceq Hcslneg) => Henclnegq.
    move : (enc_bits_copy (size ls1) Henclnegq) => Henclnegcp. rewrite {2}Hszlb1 in Henclnegcp.
    move : (bit_blast_xor_correct Hbbxor1 Hencq Henclnegcp Hcsxor1) => Hencrxor1.
    move : (bit_blast_neg_size_ss Hbbneg) => Hszneg.
    move : (bit_blast_add_size_ss Hbbadd Hszadd) => Hszadd1rs.
    (*move : (bit_blast_neg_size_ss Hbbneg1) => Hszneg1.*)
    generalize Hszadd1rs. rewrite Hszadd Hszzext Hsz12 . move => Hszu; symmetry in Hszu.
    have Hszu1 : size ls1 = size lrs_add by rewrite -Hszadd1rs Hszadd Hszzext.
    move : (bit_blast_udiv_size_ss Hbbudiv Hszu) => [Hszuq Hszur]. 
    move : (bit_blast_xor_size_max Hbbxor1). rewrite size_nseq Hszuq -Hsz12 maxnn.
    move : (bit_blast_xor_size_max Hbbxor2). rewrite size_nseq Hszur -Hsz12 maxnn.
    move => Hszxor2 Hszxor1.
    have Hencrseqcp : enc_bits E  (r_lneg :: copy (size (splitmsl ls1).1) lit_ff) (([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]):: copy (size (splitmsb bs1).1) b0) by rewrite enc_bits_cons Henclnegq size_splitmsb size_splitmsl Hszlb1 /b0 (enc_bits_copy _ (add_prelude_enc_bit_ff Hcsu1)).
    have Hszadd1 : size r_xor1 = size (r_lneg :: copy (size (splitmsl ls1).1) lit_ff) by rewrite size_splitmsl/=size_nseq -addn1 (subnK Hsz1) Hszneg Hszxor1.
    have Hadd1rs : (((udivB (bs1 ^# copy (size bs1) (splitmsb bs1).2 +# zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]) bs2).1 ^# copy (size bs1) ([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]))%bits +# (([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]) :: copy (size (splitmsb bs1).1) b0))%bits =  (((udivB (bs1 ^# copy (size bs1) (splitmsb bs1).2 +# zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]) bs2).1 ^# copy (size bs1) ([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]))%bits +# (([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]) :: copy (size (splitmsb bs1).1) b0))%bits by done.
    move : (bit_blast_add_correct Hbbadd1 Hencrxor1 Hencrseqcp Hadd1rs Hcsadd1 Hszadd1).
    move : (bit_blast_xor_correct Hbbxor2 Hencr Henccp2 Hcsxor2) => Hencxor2.
    have Henccpcmsb1 : enc_bits E ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff) ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false) by rewrite size_splitmsb size_splitmsl enc_bits_cons Hencmsl1 Hszlb1 (enc_bits_copy _ Hencff).
    have Hadd2rs : (((udivB (bs1 ^# copy (size bs1) (splitmsb bs1).2 +# zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]) bs2).2 ^# copy (size bs1) (splitmsb bs1).2)%bits +# ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false))%bits = (((udivB (bs1 ^# copy (size bs1) (splitmsb bs1).2 +# zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]) bs2).2 ^# copy (size bs1) (splitmsb bs1).2)%bits +# ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false))%bits by done.
    move : (bit_blast_xor_size_max Hbbxor2). rewrite size_nseq Hszur -Hsz12 maxnn. move => Hszxor3.
    have Hszadd2 : size r_xor2 = size ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff) by rewrite size_splitmsl/=size_nseq -addn1 (subnK Hsz1) Hszxor2.
    move : (bit_blast_add_correct Hbbadd2 Hencxor2 Henccpcmsb1 Hadd2rs Hcsadd2 Hszadd2).
    have Hexp2 : 1 < 2 ^ size bs2 by rewrite -Hszlb2 -{1}(expn0 2) (ltn_exp2l _ _ (ltnSn 1)).
    have His1 : (true :: zeros (size bs2 - 1)) = from_nat (size bs2) 1. apply/eqP. rewrite -to_nat_inj_ss; last rewrite /=size_zeros size_from_nat -Hszlb2 -addn1 (subnK Hsz2); first rewrite/= to_nat_zeros -muln2 mul0n addn0 (to_nat_from_nat_bounded Hexp2); first done. done.
    have His1' : zext (size ls1 - 1) [:: true] = from_nat (size ls1) 1. apply/eqP. rewrite -to_nat_inj_ss; last by rewrite size_zext size_from_nat /= addnC (subnK Hsz1). rewrite to_nat_zext/= -muln2 mul0n addn0 to_nat_from_nat_bounded ; last by rewrite Hsz12 Hszlb2 Hexp2. done.
    have Hszb12 : size bs1 = size bs2 by rewrite -Hszlb1 Hsz12 Hszlb2.
    case Hmsb1 : (msb bs1).
    + rewrite -/(msb bs1) -/(msb bs2) Hmsb1 Hmsb2f size_splitmsl size_splitmsb/=.
      have -> : (bs1 ^# copy (size bs1) true)%bits = invB bs1 by rewrite xorBC xorB_copy_case.
      rewrite His1' Hszlb1 {1 4}(invB_size_ss bs1) addB1 -/(negB bs1) {2 4}Hszb12 His1 -Hszb12.
      have Hszurem: (size ((udivB (-# bs1)%bits (bs2)).2)%bits) = size bs1 by rewrite size_uremB size_negB.
      have Hszudiv: (size ((udivB (-# bs1)%bits (bs2)).1)%bits) = size bs1 by rewrite size_udivB size_negB. 
      rewrite {1}xorBC -{1}Hszurem xorB_copy_case -{1}Hszurem (invB_size_ss ((udivB (-# bs1) (bs2)).2))%bits addB1 -/(negB ((udivB (-# bs1) (bs2)).2)%bits).
      by rewrite {1}xorBC -{1}Hszudiv xorB_copy_case -Hszudiv (invB_size_ss ((udivB (-# bs1) (bs2)).1))%bits addB1 -/(negB ((udivB (-# bs1) (bs2)).1)%bits).
    + rewrite -/(msb bs1) -/(msb bs2) Hmsb1 Hmsb2f size_splitmsl size_splitmsb/=.
      have ->: [:: false] = zeros 1 by done. 
      rewrite zeros_cons zext_zero (subnK Hsz1) addB0 unzip1_zip; last by rewrite size_xorB size_uremB size_addB size_xorB !size_zeros -Hszlb1 -addn1 (subnK Hsz1) maxnn minnn maxnn.
      rewrite addB0 unzip1_zip; last by rewrite size_xorB size_zeros Hszlb1 size_nseq maxnn.
      rewrite addB0 unzip1_zip; last by rewrite size_xorB size_udivB size_xorB size_zeros -addn1 -Hszlb1 (subnK Hsz1) size_nseq 2!maxnn.
      have -> : (bs1 ^# copy (size bs1) false)%bits = bs1 by rewrite xorBC xorB_copy_case.
      have Hszurem: (size ((udivB (bs1)%bits (bs2)).2)%bits) = size bs1 by rewrite size_uremB.
      have Hszudiv: (size ((udivB (bs1)%bits (bs2)).1)%bits) = size bs1 by rewrite size_udivB.
      by rewrite xorBC -{1}Hszurem xorB_copy_case xorBC -{1}Hszudiv xorB_copy_case. 
  - rewrite (lock splitmsl) (lock bit_blast_eq) (lock bit_blast_lneg)/= -!lock.
    dcase (bit_blast_xor g_add ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[g_xor1] cs_xor1] r_xor1] Hbbxor1.
    dcase (bit_blast_add g_xor1 r_xor1 ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff)) => [[[g_add1] cs_add1] r_add1] Hbbadd1.
    dcase (bit_blast_udiv g_add1 lrs_add r_add1) => [[[[g_udiv] cs_udiv] qs_udiv] rs_udiv] Hbbudiv.
    dcase (bit_blast_eq g_udiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[g_eq] cs_eq] r_eq] Hbbeq.
    dcase (bit_blast_lneg g_eq r_eq) => [[[g_lneg] cs_lneg] r_lneg] Hbblneg.
    dcase (bit_blast_xor g_lneg qs_udiv (copy (size ls1) r_lneg)) => [[[g_xor2] cs_xor2] r_xor2] Hbbxor2.
    dcase (bit_blast_add g_xor2 r_xor2 (r_lneg :: copy (size (splitmsl ls1).1) lit_ff) ) => [[[g_add2] cs_add2] r_add2] Hbbadd2.
    dcase (bit_blast_xor g_add2 rs_udiv (copy (size ls1) (splitmsl ls1).2)) => [[[g_xor3] cs_xor3] r_xor3] Hbbxor3.
    dcase (bit_blast_add g_xor3 r_xor3 ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff)) => [[[g_add3] cs_add3] r_add3] Hbbadd3.
    case => _ <- <- <-. move => Hsz12 Hsz2 Henc1 Henc2. rewrite !add_prelude_catrev.
    move/andP => [Hcsu Hcsadd3].
    move/andP : Hcsu => [Hcsu Hcsnil]. move/andP : Hcsu => [Hcsu Hcsxor3]. move/andP : Hcsu => [Hcsu Hcsadd2].
    move/andP : Hcsu => [Hcsu Hcsnil2]. move/andP : Hcsu => [Hcsu Hcsxor2]. move/andP : Hcsu => [Hcsu Hcslneg].
    move/andP : Hcsu => [Hcsu Hcseq]. move/andP : Hcsu => [Hcsu Hcsu1]. move/andP : Hcsu => [Hcsu Hcsu2].
    move/andP : Hcsu => [Hcsxor Hcsu]. move/andP : Hcsu => [Hcszext Hcsadd].
    move/andP : Hcsu2 => [Hcsxor1 Hcsadd1].
    move : (add_prelude_tt Hcsu1) => Htt. 
    move : (add_prelude_ff Hcsu1) => Hff. 
    generalize Hsz2; rewrite -{1}Hsz12; move => Hsz1.
    rewrite /sdivB /absB /=. 
    move : (enc_bits_size Henc1) => Hszlb1.
    move : (enc_bits_size Henc2) => Hszlb2.
    have Hencmsl2 : enc_bit E (splitmsl ls2).2 (splitmsb bs2).2 by rewrite (enc_bit_msb Htt Henc2).
    have Hencmsl1 : enc_bit E (splitmsl ls1).2 (splitmsb bs1).2 by rewrite (enc_bit_msb Htt Henc1).
    have Henccp1 : enc_bits E (copy (size ls1) (splitmsl ls1).2) (copy (size bs1) (splitmsb bs1).2) by rewrite -Hszlb1 (enc_bits_copy (size ls1) Hencmsl1).
    have Henccp2 : enc_bits E (copy (size ls2) (splitmsl ls2).2) (copy (size bs2) (splitmsb bs2).2) by rewrite -Hszlb2 (enc_bits_copy (size ls2) Hencmsl2).
    move : (bit_blast_xor_correct Hbbxor Henc1 Henccp1 Hcsxor) => Hencxor.
    move : (add_prelude_enc_bit_ff Hcsu1) => Hencff.
    generalize Hencmsl1. rewrite -enc_bits_seq1. move => Hencseq1.
    move : (bit_blast_zeroextend_correct Hbbzext Hencseq1 Hcszext) => Henczext.
    move : (bit_blast_zeroextend_size Hbbzext). rewrite size_splitmsl -addn1 (subnK Hsz1). move => Hszzext.
    have Hszadd : size lrs_xor = size lrs_zext by rewrite (bit_blast_xor_size_max Hbbxor) size_nseq maxnn Hszzext.
    have Haddr : ((bs1 ^# copy (size bs1) (splitmsb bs1).2)%bits +# (zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]))%bits = ((bs1 ^# copy (size bs1) (splitmsb bs1).2)%bits +# (zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]))%bits by done.
    move : (bit_blast_add_correct Hbbadd Hencxor Henczext Haddr Hcsadd Hszadd) => Hencaddr.
    move : (bit_blast_xor_correct Hbbxor1 Henc2 Henccp2 Hcsxor1).
    have -> : (splitmsb bs2).2 = msb bs2 by done. 
    move => Hencxor1.
    have Haddr1 : ((bs2 ^# copy (size bs2) (msb bs2))%bits +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) false))%bits = ((bs2 ^# copy (size bs2) (msb bs2))%bits +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))%bits by done.
    move : (bit_blast_xor_size_max Hbbxor1). rewrite size_nseq maxnn.
    move => Hszxor1.
    have Hszadd1 : size r_xor1 = size ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff) by rewrite (lock splitmsl)/= size_nseq -lock size_splitmsl -addn1 (subnK Hsz2) -Hszxor1.
    have Henccpcmsb2 : enc_bits E ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff) ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) false) by rewrite size_splitmsb size_splitmsl enc_bits_cons Hencmsl2 Hszlb2 (enc_bits_copy _ Hencff).
    move : (bit_blast_add_correct Hbbadd1 Hencxor1 Henccpcmsb2 Haddr1 Hcsadd1 Hszadd1) => Hencadd1.
    move : (bit_blast_add_size_max Hbbadd). rewrite Hszadd maxnn Hszzext Hsz12.
    move : (bit_blast_add_size_ss Hbbadd1 Hszadd1). rewrite (bit_blast_xor_size_max Hbbxor1) size_nseq maxnn.
    move => Hsz2add1 Hsz2add. rewrite Hsz2add in Hsz2add1.
    move : (bit_blast_udiv_correct Hbbudiv Hsz2add1 Hencaddr Hencadd1 Hcsu1) => [Hencq Hencr].
    generalize Hencmsl2. rewrite -enc_bits_seq1. move => Hencseq2.
    have Hszeq : size [:: (splitmsl ls1).2]= size [:: (splitmsl ls2).2] by done.
    move : (bit_blast_eq_correct Hbbeq Hszeq Hencseq1 Hencseq2 Hcseq) => Henceq.
    move : (bit_blast_lneg_correct Hbblneg Henceq Hcslneg) => Henclnegq.
    move : (enc_bits_copy (size ls1) Henclnegq) => Henclnegcp. rewrite {2}Hszlb1 in Henclnegcp.
    move : (bit_blast_xor_correct Hbbxor2 Hencq Henclnegcp Hcsxor2) => Hencrxor2.
    move : (bit_blast_add_size_ss Hbbadd Hszadd) => Hszaddrs.
    move : (bit_blast_add_size_ss Hbbadd1 Hszadd1) => Hszadd1rs.
    generalize Hszadd1rs. rewrite Hszxor1 -Hsz12 -Hszzext -Hszadd Hszaddrs.  move => Hszu.
    have Hszu1 : size ls1 = size lrs_add by rewrite -Hszaddrs Hszadd Hszzext.
    move : (bit_blast_udiv_size_ss Hbbudiv Hszu) => [Hszuq Hszur]. 
    move : (bit_blast_xor_size_max Hbbxor2). rewrite size_nseq Hszuq -Hszu -Hszu1 maxnn.
    move : (bit_blast_xor_size_max Hbbxor3). rewrite size_nseq Hszur -Hszu -Hszu1 maxnn.
    move => Hszxor3 Hszxor2.
    have Hencrseqcp : enc_bits E  (r_lneg :: copy (size (splitmsl ls1).1) lit_ff) (([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]):: copy (size (splitmsb bs1).1) b0) by rewrite enc_bits_cons Henclnegq size_splitmsb size_splitmsl Hszlb1 /b0 (enc_bits_copy _ (add_prelude_enc_bit_ff Hcsu1)).
    have Hszadd2 : size r_xor2 = size (r_lneg :: copy (size (splitmsl ls1).1) lit_ff) by rewrite size_splitmsl/=size_nseq -addn1 (subnK Hsz1) Hszxor2.
    have Hadd2rs : (((udivB (bs1 ^# copy (size bs1) (splitmsb bs1).2 +# zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]) (bs2 ^# copy (size bs2) (msb bs2) +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))).1 ^# copy (size bs1) ([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]))%bits +# (([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]) :: copy (size (splitmsb bs1).1) b0))%bits = (((udivB (bs1 ^# copy (size bs1) (splitmsb bs1).2 +# zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]) (bs2 ^# copy (size bs2) (msb bs2) +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))).1 ^# copy (size bs1) ([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]))%bits +# (([:: (splitmsb bs1).2] != [:: (splitmsb bs2).2]) :: copy (size (splitmsb bs1).1) b0))%bits by done.
    move : (bit_blast_add_correct Hbbadd2 Hencrxor2 Hencrseqcp Hadd2rs Hcsadd2 Hszadd2).
    move : (bit_blast_xor_correct Hbbxor3 Hencr Henccp1 Hcsxor3) => Hencxor3.
    have Henccpcmsb1 : enc_bits E ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff) ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false) by rewrite size_splitmsb size_splitmsl enc_bits_cons Hencmsl1 Hszlb1 (enc_bits_copy _ Hencff).
    have Hadd3rs : (((udivB (bs1 ^# copy (size bs1) (splitmsb bs1).2 +#  zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]) (bs2 ^# copy (size bs2) (msb bs2) +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))).2 ^# copy (size bs1) (splitmsb bs1).2)%bits +# ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false))%bits = (((udivB (bs1 ^# copy (size bs1) (splitmsb bs1).2 +#  zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]) (bs2 ^# copy (size bs2) (msb bs2) +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))).2 ^# copy (size bs1) (splitmsb bs1).2)%bits +# ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false))%bits by done.
    move : (bit_blast_xor_size_max Hbbxor3). rewrite size_nseq Hszur -Hszu -Hszu1 maxnn. move => Hszxor4.
    have Hszadd3 : size r_xor3 = size ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff) by rewrite size_splitmsl/=size_nseq -addn1 (subnK Hsz1) Hszxor3.
    move : (bit_blast_add_correct Hbbadd3 Hencxor3 Henccpcmsb1 Hadd3rs Hcsadd3 Hszadd3).
    have Hexp2 : 1 < 2 ^ size bs2 by rewrite -Hszlb2 -{1}(expn0 2) (ltn_exp2l _ _ (ltnSn 1)).
    have His1 : (true :: zeros (size bs2 - 1)) = from_nat (size bs2) 1. apply/eqP. rewrite -to_nat_inj_ss; last rewrite /=size_zeros size_from_nat -Hszlb2 -addn1 (subnK Hsz2); first rewrite/= to_nat_zeros -muln2 mul0n addn0 (to_nat_from_nat_bounded Hexp2); first done. done.
    have His1' : zext (size ls1 - 1) [:: true] = from_nat (size ls1) 1. apply/eqP. rewrite -to_nat_inj_ss; last by rewrite size_zext size_from_nat /= addnC (subnK Hsz1). rewrite to_nat_zext/= -muln2 mul0n addn0 to_nat_from_nat_bounded ; last by rewrite Hsz12 Hszlb2 Hexp2. done.
    have Hszb12 : size bs1 = size bs2 by rewrite -Hszlb1 Hsz12 Hszlb2.
    case Hmsb1 : (msb bs1); case Hmsb2 : (msb bs2).
    + rewrite -/(msb bs1) -/(msb bs2) Hmsb1 Hmsb2 size_splitmsl !size_splitmsb /=.
      have -> : (bs1 ^# copy (size bs1) true)%bits = invB bs1 by rewrite xorBC xorB_copy_case.
      have -> : (bs2 ^# copy (size bs2) true)%bits = invB bs2 by rewrite xorBC xorB_copy_case.
      rewrite His1' Hszlb1 His1 {1 4}(invB_size_ss bs1) (invB_size_ss bs2) !addB1 -/(negB bs1) -/(negB bs2) {2}Hszb12 His1 -{1}Hszb12.
      rewrite zeros_cons addB0 unzip1_zip; last by rewrite size_xorB size_udivB size_negB size_zeros -addn1-Hszlb1 (subnK Hsz1) size_nseq maxnn.
      have Hszurem: (size ((udivB (-# bs1)%bits (-# bs2)%bits).2)%bits) = size bs1 by rewrite size_uremB size_negB.
      have Hszudiv: (size ((udivB (-# bs1)%bits (-# bs2)%bits).1)%bits) = size bs1 by rewrite size_udivB size_negB. 
      rewrite {1}xorBC -{1}Hszurem xorB_copy_case -{1}Hszurem (invB_size_ss ((udivB (-# bs1) (-# bs2)%bits).2))%bits addB1 -/(negB ((udivB (-# bs1) (-# bs2)%bits).2)%bits).
      by rewrite {1}xorBC -{1}Hszudiv xorB_copy_case. 
    + rewrite -/(msb bs1) -/(msb bs2) Hmsb1 Hmsb2 size_splitmsl !size_splitmsb/=.
      have -> : (bs1 ^# copy (size bs1) true)%bits = invB bs1 by rewrite xorBC xorB_copy_case.
      have -> : (bs2 ^# copy (size bs2) false)%bits = bs2 by rewrite xorBC xorB_copy_case.
      rewrite zeros_cons addB0 unzip1_zip; last by rewrite size_zeros -addn1 -Hszlb2 (subnK Hsz2).
      rewrite {2 4}Hszb12 His1 -Hszb12 His1' Hszlb1 {1 4}(invB_size_ss bs1) !addB1 -/(negB bs1).
      have Hszurem: (size ((udivB (-# bs1)%bits (bs2)%bits).2)%bits) = size bs1 by rewrite size_uremB size_negB.
      have Hszudiv: (size ((udivB (-# bs1)%bits (bs2)%bits).1)%bits) = size bs1 by rewrite size_udivB size_negB. 
      rewrite xorBC -{1 2}Hszurem xorB_copy_case (invB_size_ss ((udivB (-# bs1) bs2).2)%bits) addB1 -/(negB ((udivB (-# bs1) bs2).2)%bits).
      by rewrite xorBC -{1 2}Hszudiv xorB_copy_case (invB_size_ss ((udivB (-# bs1) bs2).1)%bits) addB1 -/(negB ((udivB (-# bs1) bs2).1)%bits).
    + rewrite -/(msb bs1) -/(msb bs2) Hmsb1 Hmsb2 size_splitmsl !size_splitmsb/=.
      have ->: [:: false] = zeros 1 by done. 
      have -> : (bs1 ^# copy (size bs1) false)%bits = bs1 by rewrite xorBC xorB_copy_case.
      have -> : (bs2 ^# copy (size bs2) true)%bits = invB bs2 by rewrite xorBC xorB_copy_case.
      rewrite zeros_cons zext_zero (subnK Hsz1) addB0 unzip1_zip; last by rewrite size_xorB size_uremB size_addB !size_zeros -Hszlb1 -addn1 (subnK Hsz1)  minnn maxnn.
      rewrite {3}Hszb12 His1 addB0 unzip1_zip; last by rewrite size_zeros Hszlb1.
      have Hszurem: (size ((udivB (bs1)%bits (-# bs2)%bits).2)%bits) = size bs1 by rewrite size_uremB.
      have Hszudiv: (size ((udivB (bs1)%bits (-# bs2)%bits).1)%bits) = size bs1 by rewrite size_udivB. 
      rewrite {1 2}(invB_size_ss bs2) addB1 -/(negB bs2).
      by rewrite xorBC -{1}Hszurem xorB_copy_case xorBC -{1}Hszudiv xorB_copy_case -Hszb12 -{1}Hszudiv (invB_size_ss ((udivB (bs1)%bits (-# bs2)%bits).1)%bits) addB1 -/(negB ((udivB (bs1)%bits (-# bs2)%bits).1)%bits).
    + rewrite -/(msb bs1) -/(msb bs2) Hmsb1 Hmsb2 size_splitmsl !size_splitmsb/=.
      have ->: [:: false] = zeros 1 by done. 
      have -> : (bs1 ^# copy (size bs1) false)%bits = bs1 by rewrite xorBC xorB_copy_case.
      have -> : (bs2 ^# copy (size bs2) false)%bits = bs2 by rewrite xorBC xorB_copy_case.
      rewrite !zeros_cons zext_zero (subnK Hsz1).
      rewrite addB0 unzip1_zip; last by rewrite size_xorB size_uremB size_addB !size_zeros -addn1 -Hszlb1 (subnK Hsz1) minnn maxnn.
      rewrite addB0 unzip1_zip; last by rewrite size_zeros Hszlb1.
      rewrite addB0 unzip1_zip; last by rewrite size_zeros -Hszlb2 -addn1 (subnK Hsz2).
      rewrite addB0 unzip1_zip; last by rewrite size_zeros size_xorB size_udivB -addn1 -Hszlb1 (subnK Hsz1) size_nseq maxnn.
      have Hszurem: (size ((udivB (bs1)%bits (bs2)%bits).2)%bits) = size bs1 by rewrite size_uremB.
      have Hszudiv: (size ((udivB (bs1)%bits (bs2)%bits).1)%bits) = size bs1 by rewrite size_udivB. 
      by rewrite xorBC -{1}Hszurem -{1}Hszudiv xorB_copy_case xorBC xorB_copy_case.
Qed.*)

(* ===== bit_blast_srem ===== *)

Definition bit_blast_srem g ls1 ls2 : generator * cnf * word :=
  let (ls1_tl, ls1_sign) := eta_expand (splitmsl ls1) in
  let ws1 := copy (size ls1) ls1_sign in
  let '(g_abs1, cs_abs1, lrs_abs1) := bit_blast_abs g ls1 in
  let '(g_abs2, cs_abs2, lrs_abs2) := bit_blast_abs g_abs1 ls2 in
  let '(g_udiv, cs_udiv, qs_udiv, rs_udiv) := bit_blast_udiv g_abs2 lrs_abs1 lrs_abs2 in
  if (ls1_sign == lit_ff) then (g_udiv, catrev (catrev cs_abs1 cs_abs2) cs_udiv, rs_udiv)
  else if (ls1_sign == lit_tt) then
         let '(g_negr, cs_negr, lrs_negr) := bit_blast_neg g_udiv rs_udiv in
         (g_negr, catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negr, lrs_negr)
       else
         let '(g_xor1, cs_xor1, rs_xor1) := bit_blast_xor g_udiv rs_udiv ws1 in
         let '(g_zext1, cs_zext1, rs_zext1) := bit_blast_zeroextend (size ls1_tl) g_xor1 (ls1_sign::nil) in
         let '(g_add1, cs_add1, rs_add1) := bit_blast_add g_zext1 rs_xor1 rs_zext1 in
         (g_add1, catrev (catrev (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_xor1) cs_zext1) cs_add1, rs_add1).

Definition mk_env_srem E g ls1 ls2 : env * generator * cnf * word :=
  let (ls1_tl, ls1_sign) := eta_expand (splitmsl ls1) in
  (*let (ls2_tl, ls2_sign) := eta_expand (splitmsl ls2) in*)
  let ws1 := copy (size ls1) ls1_sign in
  let '(E_abs1, g_abs1, cs_abs1, lrs_abs1) := mk_env_abs E g ls1 in
  let '(E_abs2, g_abs2, cs_abs2, lrs_abs2) := mk_env_abs E_abs1 g_abs1 ls2 in
  let '(E_udiv, g_udiv, cs_udiv, qs_udiv, rs_udiv) := mk_env_udiv E_abs2 g_abs2 lrs_abs1 lrs_abs2 in
  if (ls1_sign == lit_ff) then
    (E_udiv, g_udiv, catrev (catrev cs_abs1 cs_abs2) cs_udiv, rs_udiv)
  else if (ls1_sign == lit_tt) then
         let '(E_negr, g_negr, cs_negr, lrs_negr) := mk_env_neg E_udiv g_udiv rs_udiv in
         (E_negr, g_negr, catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negr, lrs_negr)
       else 
         let '(E_xor1, g_xor1, cs_xor1, rs_xor1) := mk_env_xor E_udiv g_udiv rs_udiv ws1 in
         let '(E_zext1, g_zext1, cs_zext1, rs_zext1) := mk_env_zeroextend (size ls1_tl) E_xor1 g_xor1 (ls1_sign::nil) in
         let '(E_add1, g_add1, cs_add1, rs_add1) := mk_env_add E_zext1 g_zext1 rs_xor1 rs_zext1 in
         (E_add1, g_add1, catrev (catrev (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_xor1) cs_zext1) cs_add1, rs_add1).

Lemma bit_blast_srem_correct g ls1 ls2 g' cs rlrs E bs1 bs2 :
  bit_blast_srem g ls1 ls2 = (g', cs, rlrs) ->
  size ls1 = size ls2 ->
  0 < size ls1 ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E rlrs (sremB bs1 bs2).
Proof.
  rewrite/bit_blast_srem /bit_blast_abs.
  dcase (bit_blast_neg g ls1) => [[[g_neg ] cs_neg] lrs_neg] Hbbneg.
  dcase (bit_blast_xor g ls1 (copy (size ls1) (splitmsl ls1).2)) => [[[g_xor ] cs_xor] lrs_xor] Hbbxor.
  dcase (bit_blast_zeroextend (size (splitmsl ls1).1) g_xor [:: (splitmsl ls1).2]) => [[[g_zext ] cs_zext] lrs_zext] Hbbzext.
  dcase (bit_blast_add g_zext lrs_xor lrs_zext) => [[[g_add] cs_add] lrs_add] Hbbadd.
  case Hls1mb1 :((splitmsl ls1).2 == lit_tt); case Hls1mb0 : ((splitmsl ls1).2 == lit_ff);
    case Hls2mb1 :((splitmsl ls2).2 == lit_tt); case Hls2mb0 : ((splitmsl ls2).2 == lit_ff);
    try (rewrite (eqP Hls1mb1) in Hls1mb0; discriminate); try (rewrite (eqP Hls2mb1) in Hls2mb0; discriminate).
  - dcase (bit_blast_neg g_neg ls2)=> [[[g_neg1 ] cs_neg1] lrs_neg1] Hbbneg1.
    dcase (bit_blast_udiv g_neg1 lrs_neg lrs_neg1) => [[[[g_udiv ] cs_udiv] lqs_udiv] lrs_udiv] Hbbudiv.
    dcase (bit_blast_neg g_udiv lrs_udiv) => [[[g_neg3 ] cs_neg3] lrs_neg3] Hbbneg3.
    case => _ <- <-. move => Hsz12 Hsz2 Henc1 Henc2.
    rewrite 3!add_prelude_catrev.
    move => /andP [/andP [/andP [Hcsneg Hcsneg1] Hcsu] Hcsneg3]. 
    move : (add_prelude_tt Hcsu) => Htt. 
    move : (enc_bit_msb Htt Henc1); rewrite/msl (eqP Hls1mb1); move => Hencmsb1.
    move : (add_prelude_enc_bit_true (msb bs1) Hcsu). rewrite Hencmsb1. move => Hmsb1t.
    move : (enc_bit_msb Htt Henc2). rewrite/msl (eqP Hls2mb1). move => Hencmsb2.
    move : (add_prelude_enc_bit_true (msb bs2) Hcsu). rewrite Hencmsb2. move => Hmsb2t.
    rewrite /sremB /absB -Hmsb1t -Hmsb2t/=. 
    move : (bit_blast_neg_correct Hbbneg Henc1 Hcsneg) => Hencneg.
    move : (bit_blast_neg_correct Hbbneg1 Henc2 Hcsneg1) => Hencneg1.
    generalize Hsz12.
    rewrite (bit_blast_neg_size_ss Hbbneg1) (bit_blast_neg_size_ss Hbbneg). move => Hszn.
    move : (bit_blast_udiv_correct Hbbudiv Hszn Hencneg Hencneg1 Hcsu) => [_ Hencur].
    exact : (bit_blast_neg_correct Hbbneg3 Hencur Hcsneg3).
  - dcase (bit_blast_udiv g_neg lrs_neg ls2) => [[[[g_udiv ] cs_udiv] lqs_udiv] lrs_udiv] Hbbudiv.
    dcase (bit_blast_neg g_udiv lrs_udiv) => [[[g_neg2 ] cs_neg2] lrs_neg2] Hbbneg2.
    case => _ <- <-. move => Hsz12 Hsz2 Henc1 Henc2.
    rewrite 3!add_prelude_catrev. move/andP => [Hcsu Hcsneg3]. move/andP : Hcsu => [Hcsu Hcsudiv].
    move/andP : Hcsu => [Hcsneg _]. 
    move : (add_prelude_tt Hcsudiv) => Htt. 
    move : (enc_bit_msb Htt Henc1). rewrite/msl (eqP Hls1mb1). move => Hencmsb1.
    move : (add_prelude_enc_bit_true (msb bs1) Hcsudiv). rewrite Hencmsb1. move => Hmsb1t.
    move : (enc_bit_msb Htt Henc2). rewrite/msl (eqP Hls2mb0). move => Hencmsb2.
    move : (add_prelude_enc_bit_is_not_true (msb bs2) Hcsudiv). rewrite Hencmsb2. move => Hmsb2f.
    symmetry in Hmsb2f. rewrite->Bool.negb_true_iff in Hmsb2f.
    rewrite/sremB /absB -Hmsb1t Hmsb2f/=.
    move : (bit_blast_neg_correct Hbbneg Henc1 Hcsneg) => Hencneg.
    generalize Hsz12.
    rewrite (bit_blast_neg_size_ss Hbbneg). move => Hszn.
    move : (bit_blast_udiv_correct Hbbudiv Hszn Hencneg Henc2 Hcsudiv) => [_ Hencur].
    exact : (bit_blast_neg_correct Hbbneg2 Hencur Hcsneg3) => Hencneg2.
  - rewrite (lock splitmsl)/= -!lock.
    dcase (bit_blast_xor g_neg ls2 (copy (size ls2) (splitmsl ls2).2))=> [[[g_xor1 ] cs_xor1] lrs_xor1] Hbbxor1.
    dcase (bit_blast_add g_xor1 lrs_xor1 ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff)) => [[[g_add1] cs_add1] lrs_add1] Hbbadd1.
    dcase (bit_blast_udiv g_add1 lrs_neg lrs_add1)=>[[[[g_udiv1] cs_udiv1] lqs_udiv1] lrs_udiv1] Hbbudiv1.
    dcase (bit_blast_neg g_udiv1 lrs_udiv1) => [[[g_neg1] cs_neg1] lrs_neg1] Hbbneg1.
    case => _ <- <-. move => Hsz12 Hsz1 Henc1 Henc2.
    rewrite 5!add_prelude_catrev/=. move/andP => [Hcsu Hcsneg1]. move/andP : Hcsu => [Hcsu Hcsudiv].
    move/andP : Hcsu => [Hcsneg Hcsu]. move/andP : Hcsu => [Hcsu Hcsadd1]. move/andP : Hcsu => [Hcsxor1 _].
    move : (add_prelude_tt Hcsudiv) => Htt. 
    move : (add_prelude_ff Hcsudiv) => Hff. 
    move : (enc_bit_msb Htt Henc1). rewrite/msl (eqP Hls1mb1). move => Hencmsb1.
    move : (add_prelude_enc_bit_true (msb bs1) Hcsudiv). rewrite Hencmsb1. move => Hmsb1t.
    rewrite /sremB /absB -Hmsb1t.
    move : (bit_blast_neg_correct Hbbneg Henc1 Hcsneg) => Hencnegbs1.
    move : (enc_bits_size Henc2) => Hszlb2.
    have Hencmsl2 : enc_bit E (splitmsl ls2).2 (splitmsb bs2).2 by rewrite (enc_bit_msb Htt Henc2).
    have Henccp2 : enc_bits E (copy (size ls2) (splitmsl ls2).2) (copy (size bs2) (splitmsb bs2).2) by rewrite -Hszlb2 (enc_bits_copy (size ls2) Hencmsl2).
    move : (bit_blast_xor_correct Hbbxor1 Henc2 Henccp2 Hcsxor1).
    move : (add_prelude_enc_bit_ff Hcsudiv) => Hencff.
    have Henccp1 : (enc_bits E ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff) ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0)) by rewrite enc_bits_cons Hencmsl2 size_splitmsb size_splitmsl -Hszlb2 (enc_bits_copy (size ls2 -1) Hencff).
    have -> : (splitmsb bs2).2 = msb bs2 by done. 
    move => Hencxor1.
    have Haddr : ((bs2 ^# copy (size bs2) (msb bs2))%bits +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))%bits = ((bs2 ^# copy (size bs2) (msb bs2))%bits +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))%bits by done.
    move : (bit_blast_xor_size_max Hbbxor1). rewrite size_nseq maxnn.
    move => Hszxor1.
    have Hszadd1 : size lrs_xor1 = size ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff)
      by rewrite (lock splitmsl)/= size_nseq -lock size_splitmsl -addn1 -Hsz12 (subnK Hsz1) Hszxor1.
    move : (bit_blast_add_correct Hbbadd1 Hencxor1 Henccp1 Haddr Hcsadd1 Hszadd1) => Hencadd1.
    move :(bit_blast_xor_size_max Hbbxor1).
    rewrite size_nseq maxnn (bit_blast_add_size_ss Hbbadd1 Hszadd1) -Hsz12 (bit_blast_neg_size_ss Hbbneg).
    move => Hszadd1neg; symmetry in Hszadd1neg.
    move : (bit_blast_udiv_correct Hbbudiv1 Hszadd1neg Hencnegbs1 Hencadd1 Hcsudiv) => [_ Hencr].
    move : (bit_blast_neg_size_ss Hbbneg) => Hszneg.
    move : (bit_blast_add_size_ss Hbbadd1 Hszadd1) => Hszadd1rs.
    move : (bit_blast_neg_correct Hbbneg1 Hencr Hcsneg1).
    rewrite -/(msb bs2) xorBC xorB_copy_case size_splitmsb.
    generalize Hsz1; rewrite Hsz12; move => Hsz2.
    generalize Hsz2; rewrite Hszlb2; move => Hszgt02. case Hms2 : (msb bs2).
    rewrite (bits_v1_cons_zeros Hszgt02) addB1 -/(negB bs2)//.
    rewrite /= zeros_cons subn1 (ltn_predK Hszgt02) addB0 unzip1_zip//; last by rewrite size_zeros.
  - dcase (bit_blast_neg g ls2) => [[[g_neg2] cs_neg2] lrs_neg2] Hbbneg2.
    dcase (bit_blast_udiv g_neg2 ls1 lrs_neg2)=> [[[[g_udiv] cs_udiv] lqs_udiv] lrs_udiv] Hbbudiv.
    case => _ <- <-. move => Hsz12 Hsz2 Henc1 Henc2.
    rewrite !add_prelude_catrev. move/andP => [Hcsneg2 Hcsu]. 
    move : (bit_blast_neg_correct Hbbneg2 Henc2 Hcsneg2) => Hencneg2.
    generalize Hsz12. rewrite (bit_blast_neg_size_ss Hbbneg2). move => Hszneg2.
    move : (bit_blast_udiv_correct Hbbudiv Hszneg2 Henc1 Hencneg2 Hcsu)=> [_ Hencr].
    move : (bit_blast_neg_correct Hbbneg2 Henc2 Hcsneg2) => Hencneg1.
    move : (add_prelude_tt Hcsu) => Htt.
    move : (enc_bit_msb Htt Henc1). rewrite/msl (eqP Hls1mb0). move => Hencmsb1.
    move : (enc_bit_msb Htt Henc2). rewrite/msl (eqP Hls2mb1). move => Hencmsb2.
    move : (add_prelude_enc_bit_is_not_true (msb bs1) Hcsu). rewrite Hencmsb1. move => Hmsb1f. symmetry in Hmsb1f.
    rewrite<- Bool.negb_false_iff in Hmsb1f; rewrite Bool.negb_involutive in Hmsb1f.
    move : (add_prelude_enc_bit_true (msb bs2) Hcsu); rewrite Hencmsb2; move => Hmsb2t.
    rewrite /sremB /absB -Hmsb2t Hmsb1f//.
  - dcase (bit_blast_udiv g ls1 ls2 ) =>[[[[g_udiv] cs_udiv] qs_udiv] rs_udiv] Hbbudiv.
    case => _ <- <-. move => Hsz12 Hsz2 Henc1 Henc2.
    (*rewrite add_prelude_catrev.*) move => Hcsu.
    move : (add_prelude_tt Hcsu) => Htt.
    move : (enc_bit_msb Htt Henc1). rewrite/msl (eqP Hls1mb0). move => Hencmsb1.
    move : (enc_bit_msb Htt Henc2). rewrite/msl (eqP Hls2mb0). move => Hencmsb2.
    move : (add_prelude_enc_bit_is_not_true (msb bs1) Hcsu). rewrite Hencmsb1. move => Hmsb1f. symmetry in Hmsb1f.
    rewrite<- Bool.negb_false_iff in Hmsb1f; rewrite Bool.negb_involutive in Hmsb1f.
    move : (add_prelude_enc_bit_is_not_true (msb bs2) Hcsu). rewrite Hencmsb2. move => Hmsb2f. symmetry in Hmsb2f.
    rewrite<- Bool.negb_false_iff in Hmsb2f; rewrite Bool.negb_involutive in Hmsb2f.
    rewrite /sremB /absB Hmsb2f Hmsb1f//.
    move : (bit_blast_udiv_correct Hbbudiv Hsz12 Henc1 Henc2 Hcsu) => [_ Henr]; rewrite//.
  - rewrite (lock splitmsl)/= -!lock.
    dcase (bit_blast_xor g ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[g_xor1] cs_xor1] lrs_xor1] Hbbxor1.
    dcase (bit_blast_add g_xor1 lrs_xor1 ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff)) => [[[g_add1] cs_add1] lrs_add1] Hbbadd1.
    dcase (bit_blast_udiv g_add1 ls1 lrs_add1) =>[[[[g_udiv] cs_udiv] qs_udiv] rs_udiv] Hbbudiv.
    case => _ <- <-. move => Hsz12 Hsz1 Henc1 Henc2.
    rewrite 3!add_prelude_catrev/=. move/andP => [Hcsu Hcsudiv]; move/andP : Hcsu => [Hcsu Hcsadd1].
    move/andP : Hcsu => [Hcsxor1 _].
    move : (add_prelude_tt Hcsudiv) => Htt.
    move : (enc_bit_msb Htt Henc1); rewrite/msl (eqP Hls1mb0); move => Hencmsb1.
    move : (add_prelude_enc_bit_is_not_true (msb bs1) Hcsudiv); rewrite Hencmsb1; move => Hmsb1f.
    symmetry in Hmsb1f; rewrite->Bool.negb_true_iff in Hmsb1f.
    rewrite /sremB /absB Hmsb1f. 
    move : (enc_bits_size Henc2) => Hszlb2.
    have Hencmsl2 : enc_bit E (splitmsl ls2).2 (splitmsb bs2).2 by rewrite (enc_bit_msb Htt Henc2).
    have Henccp2 : enc_bits E (copy (size ls2) (splitmsl ls2).2) (copy (size bs2) (splitmsb bs2).2) by rewrite -Hszlb2 (enc_bits_copy (size ls2) Hencmsl2).
    move : (bit_blast_xor_correct Hbbxor1 Henc2 Henccp2 Hcsxor1).
    move : (add_prelude_enc_bit_ff Hcsudiv) => Hencff.
    have Henccp1 : (enc_bits E ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff) ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))
      by rewrite enc_bits_cons Hencmsl2 size_splitmsb size_splitmsl -Hszlb2 (enc_bits_copy (size ls2 -1) Hencff).
    move => Hencxor1.
    have Haddr : ((bs2 ^# copy (size bs2) (msb bs2))%bits +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))%bits = ((bs2 ^# copy (size bs2) (msb bs2))%bits +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))%bits by done.
    move : (bit_blast_xor_size_max Hbbxor1). rewrite size_nseq maxnn.
    move => Hszxor1.
    have Hszadd1 : size lrs_xor1 = size ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff)
      by rewrite (lock splitmsl)/= size_nseq -lock size_splitmsl -addn1 -Hsz12 (subnK Hsz1) Hszxor1.
    move : (bit_blast_add_correct Hbbadd1 Hencxor1 Henccp1 Haddr Hcsadd1 Hszadd1) => Hencadd1.
    move : (bit_blast_add_size_ss Hbbadd1 Hszadd1). rewrite Hszxor1 -Hsz12. move => Hsz1add1.
    move : (bit_blast_udiv_correct Hbbudiv Hsz1add1 Henc1 Hencadd1 Hcsudiv) => [_ Hencr].
    move : Hencr; rewrite -/(msb bs2) xorBC xorB_copy_case size_splitmsb.
    generalize Hsz1; rewrite Hsz12; move => Hsz2.
    generalize Hsz2; rewrite Hszlb2; move => Hszgt02. case Hms2 : (msb bs2).
    rewrite (bits_v1_cons_zeros Hszgt02) addB1 -/(negB bs2)//.
    rewrite /= zeros_cons subn1 (ltn_predK Hszgt02) addB0 unzip1_zip//; last by rewrite size_zeros.
  - rewrite (lock splitmsl) /= -!lock.
    dcase (bit_blast_neg g_add ls2) => [[[g_neg1] cs_neg1] lrs_neg1] Hbbneg1.
    dcase (bit_blast_udiv g_neg1 lrs_add lrs_neg1) =>[[[[g_udiv] cs_udiv] qs_udiv] rs_udiv] Hbbudiv.
    dcase (bit_blast_xor g_udiv rs_udiv (copy (size ls1) (splitmsl ls1).2)) =>[[[g_xor3 ] cs_xor3] lrs_xor3] Hbbxor3.
    dcase (bit_blast_add g_xor3 lrs_xor3 ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff)) =>[[[g_add3 ] cs_add3] lrs_add3] Hbbadd3.
    case => _ <- <-. move => Hsz12 Hsz1 Henc1 Henc2.
    rewrite 7!add_prelude_catrev/=. move/andP => [Hcsu Hcsadd3]; move/andP : Hcsu => [Hcsu _].
    move/andP : Hcsu => [Hcsu Hcsxor3]; move/andP : Hcsu => [Hcsu Hcsudiv].
    move/andP : Hcsu => [Hcsu Hcsneg1]; move/andP : Hcsu => [Hcsu Hcsadd]; move/andP : Hcsu => [Hcsxor Hcszext]. 
    move : (add_prelude_tt Hcsudiv) => Htt.
    move : (enc_bit_msb Htt Henc2); rewrite/msl (eqP Hls2mb1); move => Hencmsb2.
    move : (add_prelude_enc_bit_true (msb bs2) Hcsudiv); rewrite Hencmsb2; move => Hmsb2t.
    rewrite /sremB /absB -Hmsb2t /=.
    move : (enc_bits_size Henc1) => Hszlb1.
    move : (enc_bits_size Henc2) => Hszlb2.
    have Hencmsl2 : enc_bit E (splitmsl ls2).2 (splitmsb bs2).2 by rewrite (enc_bit_msb Htt Henc2).
    have Hencmsl1 : enc_bit E (splitmsl ls1).2 (splitmsb bs1).2 by rewrite (enc_bit_msb Htt Henc1).
    have Henccp2 : enc_bits E (copy (size ls1) (splitmsl ls1).2) (copy (size bs1) (splitmsb bs1).2) by rewrite -Hszlb1 (enc_bits_copy (size ls1) Hencmsl1).
    move : (bit_blast_xor_correct Hbbxor Henc1 Henccp2 Hcsxor) => Hencxor.
    move : (add_prelude_enc_bit_ff Hcsudiv) => Hencff.
    generalize Hencmsl1; rewrite -enc_bits_seq1; move => Hencseq1.
    move : (bit_blast_zeroextend_correct Hbbzext Hencseq1 Hcszext) => Henczext.
    move : (bit_blast_zeroextend_size Hbbzext). rewrite size_splitmsl/= addnC (subnK Hsz1). move => Hszzext.
    have Hszadd : size lrs_xor = size lrs_zext by rewrite (bit_blast_xor_size_max Hbbxor) size_nseq maxnn Hszzext.
    move : (eq_refl (((bs1 ^# copy (size bs1) (splitmsb bs1).2)%bits +# (zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]))%bits)). move/eqP => Haddr.
    move : (bit_blast_add_correct Hbbadd Hencxor Henczext Haddr Hcsadd Hszadd) => Hencaddr.
    move : (bit_blast_neg_correct Hbbneg1 Henc2 Hcsneg1) => Hencnegr1.
    move : (bit_blast_add_size_ss Hbbadd Hszadd). rewrite Hszadd Hszzext Hsz12 (bit_blast_neg_size_ss Hbbneg1).
    move => Hszneg1add. symmetry in Hszneg1add.
    move : (bit_blast_udiv_correct Hbbudiv Hszneg1add Hencaddr Hencnegr1 Hcsudiv) => [_ Hencr].
    generalize Hencmsl2. rewrite -enc_bits_seq1. move => Hencseq2.
    have Hszeq : size [:: (splitmsl ls1).2]= size [:: (splitmsl ls2).2] by done.
    move : (bit_blast_neg_size_ss Hbbneg) => Hszneg.
    move : (bit_blast_add_size_ss Hbbadd Hszadd) => Hszadd1rs.
    move : (bit_blast_neg_size_ss Hbbneg1) => Hszneg1.
    generalize Hszadd1rs. rewrite Hszadd Hszzext Hsz12 Hszneg1. move => Hszu; symmetry in Hszu.
    have Hszu1 : size ls1 = size lrs_add by rewrite -Hszadd1rs Hszadd Hszzext.
    move : (bit_blast_udiv_size_ss Hbbudiv Hszu) => [Hszuq Hszur].
    move : (bit_blast_xor_correct Hbbxor3 Hencr Henccp2 Hcsxor3) => Hencxor3r.
    have Henccpcmsb1 : enc_bits E ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff) ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false) by rewrite size_splitmsb size_splitmsl enc_bits_cons Hencmsl1 Hszlb1 (enc_bits_copy _ Hencff).
    move/eqP : (eq_refl (((udivB (bs1 ^# copy (size bs1) (splitmsb bs1).2 +# zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]) (-# bs2)).2 ^# copy (size bs1) (splitmsb bs1).2)%bits +# ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false))%bits).
    move => Hadd3rs.
    move : (bit_blast_xor_size_max Hbbxor3); rewrite size_nseq Hszur -Hszneg1 -Hsz12 maxnn; move => Hszxor3.
    have Hszadd3 : size lrs_xor3 = size ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff) by rewrite size_splitmsl/=size_nseq -addn1 (subnK Hsz1) Hszxor3.
    move : (bit_blast_add_correct Hbbadd3 Hencxor3r Henccpcmsb1 Hadd3rs Hcsadd3 Hszadd3).
    rewrite -/(msb bs1) size_splitmsl size_splitmsb.
    have Hszdiv : size bs1 = size ((udivB (bs1 ^# copy (size bs1) true +# zext (size ls1 - 1) [:: true]) (-# bs2)).2)%bits.
    by rewrite size_uremB size_addB size_xorB size_copy size_zext addnC/=(subnK Hsz1) Hszlb1 maxnn minnn//.
    generalize Hsz1; rewrite Hszlb1; move => Hszgt01. case Hmsb1 : (msb bs1).
    + rewrite xorBC {1}Hszdiv (xorBC bs1 (copy (size bs1) true)) Hszlb1 2!xorB_copy_case -/b0 (bits_v1_cons_zeros Hszgt01) (bits_v1_zext_b1 Hszgt01).
      move => {Hszdiv}.
      have {2}-> : size (~~# bs1)%bits = size (~~# (udivB (~~# bs1 +# (size (~~# bs1)) -bits of (1)) (-# bs2)).2)%bits.
        by rewrite !size_invB size_uremB size_addB size_invB size_from_nat minnn.
      rewrite !addB1//.
    + have -> : [:: false] = zeros 1 by done.
      rewrite zext_zero/= zeros_cons -/(zeros _) -(addn1 (size bs1 - 1)) (subnK Hszgt01).
      rewrite (xorBC bs1 (zeros (size bs1))) xorB_copy_case/= !addB0 !unzip1_zip;
        [|rewrite size_zeros//|rewrite size_xorB size_uremB size_zeros maxnn//|rewrite size_zeros//].
      have -> : (size bs1 = size (udivB bs1 (-# bs2)%bits).2) by rewrite size_uremB//.
      rewrite xorBC xorB_copy_case//.
  - rewrite (lock splitmsl) /= -!lock.
    dcase (bit_blast_udiv g_add lrs_add ls2) => [[[[g_udiv] cs_udiv] qs_udiv] rs_udiv] Hbbudiv.
    dcase (bit_blast_xor g_udiv rs_udiv (copy (size ls1) (splitmsl ls1).2)) => [[[g_xor2] cs_xor2] r_xor2] Hbbxor2.
    dcase (bit_blast_add g_xor2 r_xor2 ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff)) => [[[g_add2] cs_add2] r_add2] Hbbadd2.
    case => _ <- <-. move => Hsz12 Hsz1 Henc1 Henc2. rewrite !add_prelude_catrev.
    move/andP => [Hcsu Hcsadd2]; move/andP : Hcsu => [Hcsu _]; move/andP : Hcsu => [Hcsu Hcsxor2].
    move/andP : Hcsu => [Hcsu Hcsudiv]; move/andP : Hcsu => [Hcsu _]; move/andP : Hcsu => [Hcsu Hcsadd].
    move/andP : Hcsu => [Hcsxor Hcszext].
    move : (add_prelude_tt Hcsudiv) => Htt.
    move : (enc_bit_msb Htt Henc2); rewrite/msl (eqP Hls2mb0); move => Hencmsb2.
    move : (add_prelude_enc_bit_is_not_true (msb bs2) Hcsudiv); rewrite Hencmsb2; move => Hmsb2f.
    symmetry in Hmsb2f; rewrite->Bool.negb_true_iff in Hmsb2f.
    rewrite /sremB /absB Hmsb2f /=.
    move : (enc_bits_size Henc1) => Hszlb1.
    have Hencmsl2 : enc_bit E (splitmsl ls2).2 (splitmsb bs2).2 by rewrite (enc_bit_msb Htt Henc2).
    have Hencmsl1 : enc_bit E (splitmsl ls1).2 (splitmsb bs1).2 by rewrite (enc_bit_msb Htt Henc1).
    have Henccp2 : enc_bits E (copy (size ls1) (splitmsl ls1).2) (copy (size bs1) (splitmsb bs1).2) by rewrite -Hszlb1 (enc_bits_copy (size ls1) Hencmsl1).
    move : (bit_blast_xor_correct Hbbxor Henc1 Henccp2 Hcsxor) => Hencxor.
    move : (add_prelude_enc_bit_ff Hcsudiv) => Hencff.
    generalize Hencmsl1; rewrite -enc_bits_seq1; move => Hencseq1.
    move : (bit_blast_zeroextend_correct Hbbzext Hencseq1 Hcszext) => Henczext.
    move : (bit_blast_zeroextend_size Hbbzext); rewrite size_splitmsl addnC (subnK Hsz1); move => Hszzext.
    have Hszadd : size lrs_xor = size lrs_zext by rewrite (bit_blast_xor_size_max Hbbxor) size_nseq maxnn Hszzext.
    move/eqP : (eq_refl ((bs1 ^# copy (size bs1) (splitmsb bs1).2)%bits +# (zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]))%bits) => Haddr.
    move : (bit_blast_add_correct Hbbadd Hencxor Henczext Haddr Hcsadd Hszadd) => Hencaddr.
    move : (bit_blast_add_size_max Hbbadd); rewrite Hszadd maxnn Hszzext Hsz12; move => Hszls2add.
    symmetry in Hszls2add.
    move : (bit_blast_udiv_correct Hbbudiv Hszls2add Hencaddr Henc2 Hcsudiv) => [_ Hencr].
    move : (bit_blast_xor_correct Hbbxor2 Hencr Henccp2 Hcsxor2) => Hencxor2.
    have Henccpcmsb1 : enc_bits E ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff) ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false) by rewrite size_splitmsb size_splitmsl enc_bits_cons Hencmsl1 Hszlb1 (enc_bits_copy _ Hencff).
    move/eqP : (eq_refl (((udivB (bs1 ^# copy (size bs1) (splitmsb bs1).2 +# zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]) bs2).2 ^# copy (size bs1) (splitmsb bs1).2)%bits +# ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false))%bits).
    move => Hadd2rs.
    have Hszu : size r_xor2 = size ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff).
    {
      rewrite (bit_blast_xor_size_max Hbbxor2) size_splitmsl/= /copy 2!size_ncons/= 2!addn0 subn1 (ltn_predK Hsz1).
      rewrite (proj2 (bit_blast_udiv_size_ss Hbbudiv Hszls2add)) Hsz12 maxnn//.
    }
    move : (bit_blast_add_correct Hbbadd2 Hencxor2 Henccpcmsb1 Hadd2rs Hcsadd2 Hszu).
    rewrite -/(msb bs1) size_splitmsl size_splitmsb Hszlb1 (xorBC bs1 (copy (size bs1) (msb bs1))) xorB_copy_case.
    generalize Hsz1; rewrite Hszlb1; move => Hszgt0. case Hmsb1 : (msb bs1).
    + rewrite (bits_v1_zext_b1 Hszgt0) addB1 -/(negB _) -{1}(size_negB bs1) -{1}(size_uremB (-#bs1)%bits (bs2)) xorBC xorB_copy_case (bits_v1_cons_zeros Hszgt0).
      rewrite size_invB -{1}(size_negB bs1) -{1}(size_uremB (-#bs1)%bits (bs2)) -(size_invB _) addB1 -/(negB _)//.
    + have {1}->: [:: false] = zeros 1 by done.
      rewrite zext_zero -/(zeros (size bs1 -1)) zeros_cons -(addn1 (size bs1 -1)) (subnK Hszgt0).
      rewrite !addB0 !unzip1_zip;
        [rewrite -{1}(size_uremB bs1 bs2) xorBC xorB_copy_case//
        |rewrite size_zeros//|rewrite size_xorB size_uremB size_copy maxnn//|rewrite size_zeros//].
  - rewrite (lock splitmsl)/= -!lock.
    dcase (bit_blast_xor g_add ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[g_xor1] cs_xor1] r_xor1] Hbbxor1.
    dcase (bit_blast_add g_xor1 r_xor1 ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff)) => [[[g_add1] cs_add1] r_add1] Hbbadd1.
    dcase (bit_blast_udiv g_add1 lrs_add r_add1) => [[[[g_udiv] cs_udiv] qs_udiv] rs_udiv] Hbbudiv.
    dcase (bit_blast_xor g_udiv rs_udiv (copy (size ls1) (splitmsl ls1).2)) => [[[g_xor3] cs_xor3] r_xor3] Hbbxor3.
    dcase (bit_blast_add g_xor3 r_xor3 ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff)) => [[[g_add3] cs_add3] r_add3] Hbbadd3.
    case => _ <- <-. move => Hsz12 Hsz1 Henc1 Henc2. rewrite !add_prelude_catrev.
    move/andP => [Hcsu Hcsadd3]; move/andP : Hcsu => [Hcsu _]; move/andP : Hcsu => [Hcsu Hcsxor3].
    move/andP : Hcsu => [Hcsu Hcsudiv]; move/andP : Hcsu => [Hcsu1 Hcsu2]; move/andP : Hcsu1 => [Hcsu1 Hcsadd].
    move/andP : Hcsu1 => [Hcsxor Hcszext]; move/andP : Hcsu2 => [Hcsu2 Hcsadd1]; move/andP : Hcsu2 => [Hcsxor1 _].
    move : (add_prelude_tt Hcsudiv) => Htt.
    rewrite /sremB /absB /=.
    move : (enc_bits_size Henc1) => Hszlb1.
    move : (enc_bits_size Henc2) => Hszlb2.
    have Hencmsl2 : enc_bit E (splitmsl ls2).2 (splitmsb bs2).2 by rewrite (enc_bit_msb Htt Henc2).
    have Hencmsl1 : enc_bit E (splitmsl ls1).2 (splitmsb bs1).2 by rewrite (enc_bit_msb Htt Henc1).
    have Henccp1 : enc_bits E (copy (size ls1) (splitmsl ls1).2) (copy (size bs1) (splitmsb bs1).2) by rewrite -Hszlb1 (enc_bits_copy (size ls1) Hencmsl1).
    have Henccp2 : enc_bits E (copy (size ls2) (splitmsl ls2).2) (copy (size bs2) (splitmsb bs2).2) by rewrite -Hszlb2 (enc_bits_copy (size ls2) Hencmsl2).
    move : (bit_blast_xor_correct Hbbxor Henc1 Henccp1 Hcsxor) => Hencxor.
    move : (add_prelude_enc_bit_ff Hcsudiv) => Hencff.
    generalize Hencmsl1. rewrite -enc_bits_seq1. move => Hencseq1.
    move : (bit_blast_zeroextend_correct Hbbzext Hencseq1 Hcszext) => Henczext.
    move : (bit_blast_zeroextend_size Hbbzext). rewrite size_splitmsl addnC (subnK Hsz1). move => Hszzext.
    have Hszadd : size lrs_xor = size lrs_zext by rewrite (bit_blast_xor_size_max Hbbxor) size_nseq maxnn Hszzext.
    have Haddr : ((bs1 ^# copy (size bs1) (splitmsb bs1).2)%bits +# (zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]))%bits = ((bs1 ^# copy (size bs1) (splitmsb bs1).2)%bits +# (zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]))%bits by done.
    move : (bit_blast_add_correct Hbbadd Hencxor Henczext Haddr Hcsadd Hszadd) => Hencaddr.
    move : (bit_blast_xor_correct Hbbxor1 Henc2 Henccp2 Hcsxor1).
    have -> : (splitmsb bs2).2 = msb bs2 by done.
    move => Hencxor1.
    move/eqP : (eq_refl ((bs2 ^# copy (size bs2) (msb bs2))%bits +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) false))%bits) => Haddr1.
    move : (bit_blast_xor_size_max Hbbxor1). rewrite size_nseq maxnn.
    move => Hszxor1.
    have Hszadd1 : size r_xor1 = size ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff)
      by rewrite (lock splitmsl)/= size_nseq -lock size_splitmsl -addn1 -Hsz12 (subnK Hsz1) Hszxor1.
    have Henccpcmsb2 : enc_bits E ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff) ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) false) by rewrite size_splitmsb size_splitmsl enc_bits_cons Hencmsl2 Hszlb2 (enc_bits_copy _ Hencff).
    move : (bit_blast_add_correct Hbbadd1 Hencxor1 Henccpcmsb2 Haddr1 Hcsadd1 Hszadd1) => Hencadd1.
    move : (bit_blast_add_size_max Hbbadd). rewrite Hszadd maxnn Hszzext Hsz12.
    move : (bit_blast_add_size_ss Hbbadd1 Hszadd1). rewrite (bit_blast_xor_size_max Hbbxor1) size_nseq maxnn.
    move => Hsz2add1 Hsz2add. rewrite Hsz2add in Hsz2add1.
    move : (bit_blast_udiv_correct Hbbudiv Hsz2add1 Hencaddr Hencadd1 Hcsudiv) => [Hencq Hencr].
    generalize Hencmsl2. rewrite -enc_bits_seq1. move => Hencseq2.
    move : (bit_blast_udiv_size_ss Hbbudiv Hsz2add1) => [_ Hszur].
    move : (bit_blast_xor_size_max Hbbxor3). rewrite size_nseq Hszur -Hsz2add1 -Hsz2add Hsz12 maxnn.
    move => Hszxor2.
    move : (bit_blast_xor_correct Hbbxor3 Hencr Henccp1 Hcsxor3) => Hencxor3.
    have Henccpcmsb1 : enc_bits E ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff) ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false) by rewrite size_splitmsb size_splitmsl enc_bits_cons Hencmsl1 Hszlb1 (enc_bits_copy _ Hencff).
    move/eqP : (eq_refl (((udivB (bs1 ^# copy (size bs1) (splitmsb bs1).2 +#  zext (size (splitmsl ls1).1) [:: (splitmsb bs1).2]) (bs2 ^# copy (size bs2) (msb bs2) +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))).2 ^# copy (size bs1) (splitmsb bs1).2)%bits +# ((splitmsb bs1).2 :: copy (size (splitmsb bs1).1) false))%bits).
    move => Hadd2rs.
    move : (bit_blast_xor_size_max Hbbxor3); rewrite size_nseq Hszur -Hsz2add1 -Hsz2add Hsz12 maxnn; move => Hszxor4.
    have Hszadd3 : size r_xor3 = size ((splitmsl ls1).2 :: copy (size (splitmsl ls1).1) lit_ff) by rewrite size_splitmsl/=size_nseq -addn1 (subnK Hsz1) Hszxor4.
    move : (bit_blast_add_correct Hbbadd3 Hencxor3 Henccpcmsb1 Hadd2rs Hcsadd3 Hszadd3).
    have Hszb12 : size bs1 = size bs2 by rewrite -Hszlb1 Hsz12 Hszlb2.
    generalize Hsz1; rewrite Hszlb1; move => Hszgt0; generalize Hszgt0; rewrite {1}Hszb12; move => Hszgt02.
    rewrite -/(msb bs1) -/(msb bs2) xorBC (xorBC bs1 (copy (size bs1) (msb bs1))) (xorBC bs2 (copy (size bs2) (msb bs2))) size_splitmsl !size_splitmsb {1}Hszlb1.
    case Hmsb1 : (msb bs1); case Hmsb2 : (msb bs2); rewrite 2!xorB_copy_case//.
    + rewrite (bits_v1_cons_zeros Hszgt02) (bits_v1_zext_b1 Hszgt0) 2!addB1 -2!/(negB _) (bits_v1_cons_zeros Hszgt0).
      rewrite size_invB -{1 2}(size_negB _) -(size_uremB (-#bs1)%bits (-#bs2)%bits) xorB_copy_case -(size_invB _) addB1 -/(negB _)//.
    + rewrite (bits_v1_zext_b1 Hszgt0) zeros_cons subn1 (ltn_predK Hszgt02) addB0 unzip1_zip; last by rewrite size_zeros.
      rewrite addB1 -/(negB _) -{1}(size_negB bs1) -{1}(size_uremB (-#bs1)%bits bs2) xorB_copy_case (bits_v1_cons_zeros Hszgt0).
      rewrite size_invB -{1}(size_negB bs1) -{1}(size_uremB (-#bs1)%bits bs2) -(size_invB _) addB1 -/(negB _)//.
    + have -> : [::false] = zeros 1 by done. rewrite zext_zero (bits_v1_cons_zeros Hszgt02) addB1 (subnK Hszgt0) -/(negB _).
      rewrite zeros_cons !addB0 !unzip1_zip;
        [rewrite -(size_uremB bs1 (-#bs2)%bits) xorB_copy_case//|rewrite size_zeros//
         |rewrite size_xorB /zeros !size_copy size_uremB subn1 (ltn_predK Hszgt0) maxnn//|rewrite size_zeros//].
    + have -> : [::false] = zeros 1 by done. rewrite zext_zero !zeros_cons !subn1 {1}addn1 !(ltn_predK Hszgt0) (ltn_predK Hszgt02).
      rewrite !addB0 !unzip1_zip; try rewrite size_zeros//; last rewrite size_xorB size_copy size_uremB maxnn//.
      rewrite -(size_uremB bs1 bs2) xorB_copy_case//.
Qed.

Lemma bit_blast_srem_correct' g ls1 ls2 g' cs rlrs E bs1 bs2 :
  bit_blast_srem g ls1 ls2 = (g', cs, rlrs) ->
  size ls1 = size ls2 ->
  0 < size ls1 ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E rlrs (sremB' bs1 bs2).
Proof.
  rewrite -sremB_is_sremB'. exact: bit_blast_srem_correct.
Qed.

Lemma mk_env_srem_is_bit_blast_srem : forall ls1 E g ls2 g' cs rlrs E',
  mk_env_srem E g ls1 ls2 = (E', g', cs, rlrs) ->
  bit_blast_srem g ls1 ls2  = (g', cs, rlrs).
Proof.
  rewrite /bit_blast_srem /mk_env_srem /bit_blast_abs /mk_env_abs.
  move => ls1 E g ls2 g' cs rlrs E'.
  dcase (mk_env_neg E g ls1) => [[[[E_neg1] g_neg1] cs_neg1] rs_neg1] Hmkneg1.
  dcase (mk_env_xor E g ls1 (copy (size ls1) (splitmsl ls1).2)) => [[[[E_xor1] g_xor1] cs_xor1] rs_xor1] Hmkxor1.
  dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor1 g_xor1 [:: (splitmsl ls1).2]) => [[[[E_zext1] g_zext1] cs_zext1] rs_zext1] Hmkzext1.
  dcase (mk_env_add E_zext1 g_zext1 rs_xor1 rs_zext1) => [[[[E_add] g_add] cs_add] rs_add] Hmkadd1.
  rewrite (mk_env_neg_is_bit_blast_neg Hmkneg1) (mk_env_xor_is_bit_blast_xor Hmkxor1) (mk_env_zeroextend_is_bit_blast_zeroextend Hmkzext1) (mk_env_add_is_bit_blast_add Hmkadd1).
  case Htt1: ((splitmsl ls1).2 == lit_tt); case Hff1 : ((splitmsl ls1).2 == lit_ff);
    case Htt2 : ((splitmsl ls2).2 == lit_tt); case Hff2 : ((splitmsl ls2).2 == lit_ff);
      try rewrite (eqP Htt1)// in Hff1; try rewrite (eqP Htt2)// in Hff2.
  - dcase (mk_env_neg E_neg1 g_neg1 ls2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkneg2.
    dcase (mk_env_udiv E_abs2 g_abs2 rs_neg1 lrs_abs2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lrs_udiv) => [[[[E_negr] g_negr] cs_negr] lrs_negr] Hmknegr.
    rewrite (mk_env_neg_is_bit_blast_neg Hmkneg2) (mk_env_udiv_is_bit_blast_udiv Hmkudiv) (mk_env_neg_is_bit_blast_neg Hmknegr); case => _ <- <- <- //.
  - dcase (mk_env_udiv E_neg1 g_neg1 rs_neg1 ls2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lrs_udiv) => [[[[E_negr] g_negr] cs_negr] lrs_negr] Hmknegr.
    rewrite (mk_env_udiv_is_bit_blast_udiv Hmkudiv) (mk_env_neg_is_bit_blast_neg Hmknegr); case => _ <- <- <- //.
  - dcase (mk_env_xor E_neg1 g_neg1 ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[[E_xor2] g_xor2] cs_xor2] rs_xor2] Hmkxor2.
    dcase (mk_env_zeroextend (size (splitmsl ls2).1) E_xor2 g_xor2 [:: (splitmsl ls2).2]) => [[[[E_zext2] g_zext2] cs_zext2] rs_zext2] Hmkzext2.
    dcase (mk_env_add E_zext2 g_zext2 rs_xor2 rs_zext2) => [[[[E_add2] g_add2] cs_add2] rs_add2] Hmkadd2.
    dcase (mk_env_udiv E_add2 g_add2 rs_neg1 rs_add2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv] lrs_udiv] Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lrs_udiv) => [[[[E_negr] g_negr] cs_negr] lrs_negr] Hmknegr.
    rewrite (mk_env_xor_is_bit_blast_xor Hmkxor2) (mk_env_zeroextend_is_bit_blast_zeroextend Hmkzext2) (mk_env_add_is_bit_blast_add Hmkadd2) (mk_env_udiv_is_bit_blast_udiv Hmkudiv) (mk_env_neg_is_bit_blast_neg Hmknegr); case => _ <- <- <- //.
  - dcase (mk_env_neg E g ls2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkneg2.
    dcase (mk_env_udiv E_abs2 g_abs2 ls1 lrs_abs2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    rewrite (mk_env_neg_is_bit_blast_neg Hmkneg2) (mk_env_udiv_is_bit_blast_udiv Hmkudiv); case => _ <- <- <- //.
  - dcase (mk_env_udiv E g ls1 ls2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    rewrite (mk_env_udiv_is_bit_blast_udiv Hmkudiv); case => _ <- <- <- //.
  - dcase (mk_env_xor E g ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[[E_xor2] g_xor2] cs_xor2] rs_xor2] Hmkxor2.
    dcase (mk_env_zeroextend (size (splitmsl ls2).1) E_xor2 g_xor2 [:: (splitmsl ls2).2]) => [[[[E_zext2] g_zext2] cs_zext2] rs_zext2] Hmkzext2.
    dcase (mk_env_add E_zext2 g_zext2 rs_xor2 rs_zext2) => [[[[E_add2] g_add2] cs_add2] rs_add2] Hmkadd2.
    dcase (mk_env_udiv E_add2 g_add2 ls1 rs_add2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv] lrs_udiv] Hmkudiv.
    rewrite (mk_env_xor_is_bit_blast_xor Hmkxor2) (mk_env_zeroextend_is_bit_blast_zeroextend Hmkzext2) (mk_env_add_is_bit_blast_add Hmkadd2) (mk_env_udiv_is_bit_blast_udiv Hmkudiv); case => _ <- <- <- //.
  - dcase (mk_env_neg E_add g_add ls2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkneg2.
    dcase (mk_env_udiv E_abs2 g_abs2 rs_add lrs_abs2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_xor E_udiv g_udiv lrs_udiv (copy (size ls1) (splitmsl ls1).2)) => [[[[E_xorr] g_xorr] cs_xorr] rs_xorr] Hmkxorr.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xorr g_xorr [:: (splitmsl ls1).2]) => [[[[E_zextr] g_zextr] cs_zextr] rs_zextr] Hmkzextr.
    dcase (mk_env_add E_zextr g_zextr rs_xorr rs_zextr) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    rewrite (mk_env_neg_is_bit_blast_neg Hmkneg2) (mk_env_udiv_is_bit_blast_udiv Hmkudiv) (mk_env_xor_is_bit_blast_xor Hmkxorr) (mk_env_zeroextend_is_bit_blast_zeroextend Hmkzextr) (mk_env_add_is_bit_blast_add Hmkaddr); case => _ <- <- <- //.
  - dcase (mk_env_udiv E_add g_add rs_add ls2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_xor E_udiv g_udiv lrs_udiv (copy (size ls1) (splitmsl ls1).2)) => [[[[E_xorr] g_xorr] cs_xorr] rs_xorr] Hmkxorr.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xorr g_xorr [:: (splitmsl ls1).2]) => [[[[E_zextr] g_zextr] cs_zextr] rs_zextr] Hmkzextr.
    dcase (mk_env_add E_zextr g_zextr rs_xorr rs_zextr) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    rewrite (mk_env_udiv_is_bit_blast_udiv Hmkudiv) (mk_env_xor_is_bit_blast_xor Hmkxorr) (mk_env_zeroextend_is_bit_blast_zeroextend Hmkzextr) (mk_env_add_is_bit_blast_add Hmkaddr); case => _ <- <- <- //.
  - dcase (mk_env_xor E_add g_add ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[[E_xor2] g_xor2] cs_xor2] rs_xor2] Hmkxor2.
    dcase (mk_env_zeroextend (size (splitmsl ls2).1) E_xor2 g_xor2 [:: (splitmsl ls2).2]) => [[[[E_zext2] g_zext2] cs_zext2] rs_zext2] Hmkzext2.
    dcase (mk_env_add E_zext2 g_zext2 rs_xor2 rs_zext2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkadd2.
    dcase (mk_env_udiv E_abs2 g_abs2 rs_add lrs_abs2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_xor E_udiv g_udiv lrs_udiv (copy (size ls1) (splitmsl ls1).2)) => [[[[E_xorr] g_xorr] cs_xorr] rs_xorr] Hmkxorr.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xorr g_xorr [:: (splitmsl ls1).2]) => [[[[E_zextr] g_zextr] cs_zextr] rs_zextr] Hmkzextr.
    dcase (mk_env_add E_zextr g_zextr rs_xorr rs_zextr) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    rewrite (mk_env_xor_is_bit_blast_xor Hmkxor2) (mk_env_zeroextend_is_bit_blast_zeroextend Hmkzext2) (mk_env_add_is_bit_blast_add Hmkadd2) (mk_env_udiv_is_bit_blast_udiv Hmkudiv) (mk_env_xor_is_bit_blast_xor Hmkxorr) (mk_env_zeroextend_is_bit_blast_zeroextend Hmkzextr) (mk_env_add_is_bit_blast_add Hmkaddr); case => _ <- <- <- //.
Qed.

Lemma mk_env_srem_newer_gen :
  forall ls1 E g ls2 E' g' cs lrs,
    mk_env_srem E g ls1 ls2 = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  rewrite /mk_env_srem /mk_env_abs. move => ls1 E g ls2 E' g' cs lrs.
  dcase (mk_env_neg E g ls1) => [[[[E_neg1] g_neg1] cs_neg1] rs_neg1] Hmkneg1.
  dcase (mk_env_xor E g ls1 (copy (size ls1) (splitmsl ls1).2)) => [[[[E_xor1] g_xor1] cs_xor1] rs_xor1] Hmkxor1.
  dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor1 g_xor1 [:: (splitmsl ls1).2]) => [[[[E_zext1] g_zext1] cs_zext1] rs_zext1] Hmkzext1.
  dcase (mk_env_add E_zext1 g_zext1 rs_xor1 rs_zext1) => [[[[E_add] g_add] cs_add] rs_add] Hmkadd1.
  move : (mk_env_neg_newer_gen Hmkneg1) => Hnewneg1.
  move : (mk_env_xor_newer_gen Hmkxor1) => Hnewxor1.
  move : (mk_env_zeroextend_newer_gen Hmkzext1) => Hnewzext1.
  move : (mk_env_add_newer_gen Hmkadd1) => Hnewadd1.
  move : (pos_leb_trans Hnewxor1 (pos_leb_trans Hnewzext1 Hnewadd1)) => Hnegls1.
  case Htt1: ((splitmsl ls1).2 == lit_tt); case Hff1 : ((splitmsl ls1).2 == lit_ff);
    case Htt2 : ((splitmsl ls2).2 == lit_tt); case Hff2 : ((splitmsl ls2).2 == lit_ff);
      try rewrite (eqP Htt1)// in Hff1; try rewrite (eqP Htt2)// in Hff2.
  - dcase (mk_env_neg E_neg1 g_neg1 ls2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkneg2.
    dcase (mk_env_udiv E_abs2 g_abs2 rs_neg1 lrs_abs2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lrs_udiv) => [[[[E_negr] g_negr] cs_negr] lrs_negr] Hmknegr.
    move : (mk_env_neg_newer_gen Hmkneg2) => Hnewneg2.
    move : (mk_env_udiv_newer_gen Hmkudiv) => Hnewudiv.
    move : (mk_env_neg_newer_gen Hmknegr) => Hnewnegr.
    case => _ <- _ _ //; exact : (pos_leb_trans Hnewneg1 (pos_leb_trans Hnewneg2 (pos_leb_trans Hnewudiv Hnewnegr))).
  - dcase (mk_env_udiv E_neg1 g_neg1 rs_neg1 ls2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lrs_udiv) => [[[[E_negr] g_negr] cs_negr] lrs_negr] Hmknegr.
    move : (mk_env_udiv_newer_gen Hmkudiv) => Hnewudiv.
    move : (mk_env_neg_newer_gen Hmknegr) => Hnewnegr.
    case => _ <- _ _ //; exact : (pos_leb_trans Hnewneg1 (pos_leb_trans Hnewudiv Hnewnegr)).
  - dcase (mk_env_xor E_neg1 g_neg1 ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[[E_xor2] g_xor2] cs_xor2] rs_xor2] Hmkxor2.
    dcase (mk_env_zeroextend (size (splitmsl ls2).1) E_xor2 g_xor2 [:: (splitmsl ls2).2]) => [[[[E_zext2] g_zext2] cs_zext2] rs_zext2] Hmkzext2.
    dcase (mk_env_add E_zext2 g_zext2 rs_xor2 rs_zext2) => [[[[E_add2] g_add2] cs_add2] rs_add2] Hmkadd2.
    dcase (mk_env_udiv E_add2 g_add2 rs_neg1 rs_add2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv] lrs_udiv] Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lrs_udiv) => [[[[E_negr] g_negr] cs_negr] lrs_negr] Hmknegr.
    move : (mk_env_xor_newer_gen Hmkxor2) => Hnewxor2.
    move : (mk_env_zeroextend_newer_gen Hmkzext2) => Hnewzext2.
    move : (mk_env_add_newer_gen Hmkadd2) => Hnewadd2.
    move : (mk_env_udiv_newer_gen Hmkudiv) => Hnewudiv.
    move : (mk_env_neg_newer_gen Hmknegr) => Hnewnegr.
    case  => _ <- _ _ //; exact : (pos_leb_trans Hnewneg1 (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 (pos_leb_trans Hnewadd2 (pos_leb_trans Hnewudiv Hnewnegr))))).
  - dcase (mk_env_neg E g ls2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkneg2.
    dcase (mk_env_udiv E_abs2 g_abs2 ls1 lrs_abs2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    move : (mk_env_neg_newer_gen Hmkneg2) => Hnewneg2.
    move : (mk_env_udiv_newer_gen Hmkudiv) => Hnewudiv.
    case  => _ <- _ _ //; exact : (pos_leb_trans Hnewneg2 Hnewudiv).
  - dcase (mk_env_udiv E g ls1 ls2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    case  => _ <- _ _ //; exact : (mk_env_udiv_newer_gen Hmkudiv).
  - dcase (mk_env_xor E g ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[[E_xor2] g_xor2] cs_xor2] rs_xor2] Hmkxor2.
    dcase (mk_env_zeroextend (size (splitmsl ls2).1) E_xor2 g_xor2 [:: (splitmsl ls2).2]) => [[[[E_zext2] g_zext2] cs_zext2] rs_zext2] Hmkzext2.
    dcase (mk_env_add E_zext2 g_zext2 rs_xor2 rs_zext2) => [[[[E_add2] g_add2] cs_add2] rs_add2] Hmkadd2.
    dcase (mk_env_udiv E_add2 g_add2 ls1 rs_add2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv] lrs_udiv] Hmkudiv.
    move : (mk_env_xor_newer_gen Hmkxor2) => Hnewxor2.
    move : (mk_env_zeroextend_newer_gen Hmkzext2) => Hnewzext2.
    move : (mk_env_add_newer_gen Hmkadd2) => Hnewadd2.
    move : (mk_env_udiv_newer_gen Hmkudiv) => Hnewudiv.
    case  => _ <- _ _ //; exact : (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 (pos_leb_trans Hnewadd2 Hnewudiv))).
  - dcase (mk_env_neg E_add g_add ls2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkneg2.
    dcase (mk_env_udiv E_abs2 g_abs2 rs_add lrs_abs2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_xor E_udiv g_udiv lrs_udiv (copy (size ls1) (splitmsl ls1).2)) => [[[[E_xorr] g_xorr] cs_xorr] rs_xorr] Hmkxorr.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xorr g_xorr [:: (splitmsl ls1).2]) => [[[[E_zextr] g_zextr] cs_zextr] rs_zextr] Hmkzextr.
    dcase (mk_env_add E_zextr g_zextr rs_xorr rs_zextr) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    move : (mk_env_neg_newer_gen Hmkneg2) => Hnewneg2.
    move : (mk_env_udiv_newer_gen Hmkudiv) => Hnewudiv.
    move : (mk_env_xor_newer_gen Hmkxorr) => Hnewxorr.
    move : (mk_env_zeroextend_newer_gen Hmkzextr) => Hnewzextr.
    move : (mk_env_add_newer_gen Hmkaddr) => Hnewaddr.
    case  => _ <- _ _ //; exact : (pos_leb_trans Hnegls1 (pos_leb_trans Hnewneg2 (pos_leb_trans Hnewudiv (pos_leb_trans Hnewxorr (pos_leb_trans Hnewzextr Hnewaddr))))).
  - dcase (mk_env_udiv E_add g_add rs_add ls2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_xor E_udiv g_udiv lrs_udiv (copy (size ls1) (splitmsl ls1).2)) => [[[[E_xorr] g_xorr] cs_xorr] rs_xorr] Hmkxorr.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xorr g_xorr [:: (splitmsl ls1).2]) => [[[[E_zextr] g_zextr] cs_zextr] rs_zextr] Hmkzextr.
    dcase (mk_env_add E_zextr g_zextr rs_xorr rs_zextr) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    move : (mk_env_udiv_newer_gen Hmkudiv) => Hnewudiv.
    move : (mk_env_xor_newer_gen Hmkxorr) => Hnewxorr.
    move : (mk_env_zeroextend_newer_gen Hmkzextr) => Hnewzextr.
    move : (mk_env_add_newer_gen Hmkaddr) => Hnewaddr.
    case  => _ <- _ _ //; exact : (pos_leb_trans Hnegls1 (pos_leb_trans Hnewudiv (pos_leb_trans Hnewxorr (pos_leb_trans Hnewzextr Hnewaddr)))).
  - dcase (mk_env_xor E_add g_add ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[[E_xor2] g_xor2] cs_xor2] rs_xor2] Hmkxor2.
    dcase (mk_env_zeroextend (size (splitmsl ls2).1) E_xor2 g_xor2 [:: (splitmsl ls2).2]) => [[[[E_zext2] g_zext2] cs_zext2] rs_zext2] Hmkzext2.
    dcase (mk_env_add E_zext2 g_zext2 rs_xor2 rs_zext2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkadd2.
    dcase (mk_env_udiv E_abs2 g_abs2 rs_add lrs_abs2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_xor E_udiv g_udiv lrs_udiv (copy (size ls1) (splitmsl ls1).2)) => [[[[E_xorr] g_xorr] cs_xorr] rs_xorr] Hmkxorr.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xorr g_xorr [:: (splitmsl ls1).2]) => [[[[E_zextr] g_zextr] cs_zextr] rs_zextr] Hmkzextr.
    dcase (mk_env_add E_zextr g_zextr rs_xorr rs_zextr) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    move : (mk_env_xor_newer_gen Hmkxor2) => Hnewxor2.
    move : (mk_env_zeroextend_newer_gen Hmkzext2) => Hnewzext2.
    move : (mk_env_add_newer_gen Hmkadd2) => Hnewadd2.
    move : (mk_env_udiv_newer_gen Hmkudiv) => Hnewudiv.
    move : (mk_env_xor_newer_gen Hmkxorr) => Hnewxorr.
    move : (mk_env_zeroextend_newer_gen Hmkzextr) => Hnewzextr.
    move : (mk_env_add_newer_gen Hmkaddr) => Hnewaddr.
    case  => _ <- _ _ //; exact : (pos_leb_trans Hnegls1 (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 (pos_leb_trans Hnewadd2 (pos_leb_trans Hnewudiv (pos_leb_trans Hnewxorr (pos_leb_trans Hnewzextr Hnewaddr))))))).
Qed.

Lemma mk_env_srem_newer_res :
  forall ls1 E g ls2 E' g' cs lrs,
    mk_env_srem E g ls1 ls2  = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_lits g' lrs.
Proof.
  rewrite /mk_env_srem /mk_env_abs.  move => ls1 E g ls2 E' g' cs rlrs.
  dcase (mk_env_neg E g ls1) => [[[[E_neg1] g_neg1] cs_neg1] rs_neg1] Hmkneg1.
  dcase (mk_env_xor E g ls1 (copy (size ls1) (splitmsl ls1).2)) => [[[[E_xor1] g_xor1] cs_xor1] rs_xor1] Hmkxor1.
  dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor1 g_xor1 [:: (splitmsl ls1).2]) => [[[[E_zext1] g_zext1] cs_zext1] rs_zext1] Hmkzext1.
  dcase (mk_env_add E_zext1 g_zext1 rs_xor1 rs_zext1) => [[[[E_add] g_add] cs_add] rs_add] Hmkadd1.
  move : (mk_env_neg_newer_gen Hmkneg1) => Hnewneg1.
  move : (mk_env_xor_newer_gen Hmkxor1) => Hnewxor1.
  move : (mk_env_zeroextend_newer_gen Hmkzext1) => Hnewzext1.
  move : (mk_env_add_newer_gen Hmkadd1) => Hnewadd1.
  move : (pos_leb_trans Hnewxor1 (pos_leb_trans Hnewzext1 Hnewadd1)) => Hnegls1.
  case Htt1: ((splitmsl ls1).2 == lit_tt); case Hff1 : ((splitmsl ls1).2 == lit_ff);
    case Htt2 : ((splitmsl ls2).2 == lit_tt); case Hff2 : ((splitmsl ls2).2 == lit_ff);
      try rewrite (eqP Htt1)// in Hff1; try rewrite (eqP Htt2)// in Hff2.
  - dcase (mk_env_neg E_neg1 g_neg1 ls2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkneg2.
    dcase (mk_env_udiv E_abs2 g_abs2 rs_neg1 lrs_abs2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lrs_udiv) => [[[[E_negr] g_negr] cs_negr] lrs_negr] Hmknegr.
    move : (mk_env_neg_newer_gen Hmkneg2) => Hnewneg2.
    move : (mk_env_udiv_newer_gen Hmkudiv) => Hnewudiv.
    case => _ <- _ <- //; move => Htt Hls1 Hls2.
    move : (mk_env_neg_newer_res Hmkneg1 Htt Hls1) => Hgneg1.
    move : (mk_env_neg_newer_res Hmkneg2 (newer_than_lit_le_newer Htt Hnewneg1) (newer_than_lits_le_newer Hls2 Hnewneg1)) => Hgneg2.
    move/andP : (mk_env_udiv_newer_res Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 Hnewneg2)) (newer_than_lits_le_newer Hgneg1 Hnewneg2) Hgneg2) => [Hgudiv _].
    exact : (mk_env_neg_newer_res Hmknegr (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 (pos_leb_trans Hnewneg2 Hnewudiv))) Hgudiv) => Hgnegr.
  - dcase (mk_env_udiv E_neg1 g_neg1 rs_neg1 ls2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lrs_udiv) => [[[[E_negr] g_negr] cs_negr] lrs_negr] Hmknegr.
    move : (mk_env_udiv_newer_gen Hmkudiv) => Hnewudiv.
    case => _ <- _ <- //; move => Htt Hls1 Hls2.
    move : (mk_env_neg_newer_res Hmkneg1 Htt Hls1) => Hgneg1.
    move/andP : (mk_env_udiv_newer_res Hmkudiv (newer_than_lit_le_newer Htt Hnewneg1) Hgneg1 (newer_than_lits_le_newer Hls2 Hnewneg1)) => [Hgudiv _].
    exact : (mk_env_neg_newer_res Hmknegr (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 Hnewudiv)) Hgudiv).
  - dcase (mk_env_xor E_neg1 g_neg1 ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[[E_xor2] g_xor2] cs_xor2] rs_xor2] Hmkxor2.
    dcase (mk_env_zeroextend (size (splitmsl ls2).1) E_xor2 g_xor2 [:: (splitmsl ls2).2]) => [[[[E_zext2] g_zext2] cs_zext2] rs_zext2] Hmkzext2.
    dcase (mk_env_add E_zext2 g_zext2 rs_xor2 rs_zext2) => [[[[E_add2] g_add2] cs_add2] rs_add2] Hmkadd2.
    dcase (mk_env_udiv E_add2 g_add2 rs_neg1 rs_add2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv] lrs_udiv] Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lrs_udiv) => [[[[E_negr] g_negr] cs_negr] lrs_negr] Hmknegr.
    move : (mk_env_xor_newer_gen Hmkxor2) => Hnewxor2.
    move : (mk_env_zeroextend_newer_gen Hmkzext2) => Hnewzext2.
    move : (mk_env_add_newer_gen Hmkadd2) => Hnewadd2.
    move : (mk_env_udiv_newer_gen Hmkudiv) => Hnewudiv.
    case => _ <- _ <- //; move => Htt Hls1 Hls2.
    move : (mk_env_neg_newer_res Hmkneg1 Htt Hls1) => Hgneg1.
    move : (mk_env_add_newer_res Hmkadd2) => Hgneg2.
    move/andP : (mk_env_udiv_newer_res Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 Hnewadd2)))) (newer_than_lits_le_newer Hgneg1 (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 Hnewadd2))) Hgneg2) => [Hgudiv _].
    exact : (mk_env_neg_newer_res Hmknegr (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 (pos_leb_trans Hnewadd2 Hnewudiv))))) Hgudiv).
  - dcase (mk_env_neg E g ls2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkneg2.
    dcase (mk_env_udiv E_abs2 g_abs2 ls1 lrs_abs2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    move : (mk_env_neg_newer_gen Hmkneg2) => Hnewneg2.
    case => _ <- _ <- //; move => Htt Hls1 Hls2.
    move : (mk_env_neg_newer_res Hmkneg2 Htt Hls2) => Hgneg2.
    move/andP : (mk_env_udiv_newer_res Hmkudiv (newer_than_lit_le_newer Htt Hnewneg2) (newer_than_lits_le_newer Hls1 Hnewneg2) Hgneg2) => [Hgudiv _]; done.
  - dcase (mk_env_udiv E g ls1 ls2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    case => _ <- _ <- //; move => Htt Hls1 Hls2.
    move/andP : (mk_env_udiv_newer_res Hmkudiv Htt Hls1 Hls2) => [Hgudiv _]; done. 
  - dcase (mk_env_xor E g ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[[E_xor2] g_xor2] cs_xor2] rs_xor2] Hmkxor2.
    dcase (mk_env_zeroextend (size (splitmsl ls2).1) E_xor2 g_xor2 [:: (splitmsl ls2).2]) => [[[[E_zext2] g_zext2] cs_zext2] rs_zext2] Hmkzext2.
    dcase (mk_env_add E_zext2 g_zext2 rs_xor2 rs_zext2) => [[[[E_add2] g_add2] cs_add2] rs_add2] Hmkadd2.
    dcase (mk_env_udiv E_add2 g_add2 ls1 rs_add2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv] lrs_udiv] Hmkudiv.
    move : (mk_env_xor_newer_gen Hmkxor2) => Hnewxor2.
    move : (mk_env_zeroextend_newer_gen Hmkzext2) => Hnewzext2.
    move : (mk_env_add_newer_gen Hmkadd2) => Hnewadd2.
    case => _ <- _ <- //; move => Htt Hls1 Hls2.
    move : (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 Hnewadd2)) => Hggadd2.
    move : (mk_env_add_newer_res Hmkadd2) => Hgadd2.
    move/andP : (mk_env_udiv_newer_res Hmkudiv (newer_than_lit_le_newer Htt Hggadd2) (newer_than_lits_le_newer Hls1 Hggadd2) Hgadd2) => [Hgudiv _]; done.
  - dcase (mk_env_neg E_add g_add ls2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkneg2.
    dcase (mk_env_udiv E_abs2 g_abs2 rs_add lrs_abs2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_xor E_udiv g_udiv lrs_udiv (copy (size ls1) (splitmsl ls1).2)) => [[[[E_xorr] g_xorr] cs_xorr] rs_xorr] Hmkxorr.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xorr g_xorr [:: (splitmsl ls1).2]) => [[[[E_zextr] g_zextr] cs_zextr] rs_zextr] Hmkzextr.
    dcase (mk_env_add E_zextr g_zextr rs_xorr rs_zextr) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    case => _ <- _ <- //; move => Htt Hls1 Hls2.
    exact : (mk_env_add_newer_res Hmkaddr).
  - dcase (mk_env_udiv E_add g_add rs_add ls2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_xor E_udiv g_udiv lrs_udiv (copy (size ls1) (splitmsl ls1).2)) => [[[[E_xorr] g_xorr] cs_xorr] rs_xorr] Hmkxorr.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xorr g_xorr [:: (splitmsl ls1).2]) => [[[[E_zextr] g_zextr] cs_zextr] rs_zextr] Hmkzextr.
    dcase (mk_env_add E_zextr g_zextr rs_xorr rs_zextr) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    case => _ <- _ <- //; move => Htt Hls1 Hls2.
    exact : (mk_env_add_newer_res Hmkaddr).
  - dcase (mk_env_xor E_add g_add ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[[E_xor2] g_xor2] cs_xor2] rs_xor2] Hmkxor2.
    dcase (mk_env_zeroextend (size (splitmsl ls2).1) E_xor2 g_xor2 [:: (splitmsl ls2).2]) => [[[[E_zext2] g_zext2] cs_zext2] rs_zext2] Hmkzext2.
    dcase (mk_env_add E_zext2 g_zext2 rs_xor2 rs_zext2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkadd2.
    dcase (mk_env_udiv E_abs2 g_abs2 rs_add lrs_abs2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_xor E_udiv g_udiv lrs_udiv (copy (size ls1) (splitmsl ls1).2)) => [[[[E_xorr] g_xorr] cs_xorr] rs_xorr] Hmkxorr.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xorr g_xorr [:: (splitmsl ls1).2]) => [[[[E_zextr] g_zextr] cs_zextr] rs_zextr] Hmkzextr.
    dcase (mk_env_add E_zextr g_zextr rs_xorr rs_zextr) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    case => _ <- _ <- //; move => Htt Hls1 Hls2.
    exact : (mk_env_add_newer_res Hmkaddr).
Qed.

Lemma mk_env_srem_newer_cnf :
  forall ls1 E g ls2 E' g' cs lrs,
    mk_env_srem E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  move=> ls1 E g ls2 E' g' cs lrs. rewrite /mk_env_srem.
  dcase (mk_env_abs E g ls1) => [[[[E_abs1] g_abs1] cs_abs1] lrs_abs1] Hmkabs1.
  dcase (mk_env_abs E_abs1 g_abs1 ls2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkabs2.
  dcase (mk_env_udiv E_abs2 g_abs2 lrs_abs1 lrs_abs2) => [[[[[E_udiv] g_udiv] cs_udiv] lrs_udiv] lrs_urem] Hmkudiv.
  move=> H Hgtt Hgls1 Hgls2; move: H.
  move: (mk_env_abs_newer_gen Hmkabs1) => Hggabs1.
  move: (mk_env_abs_newer_gen Hmkabs2) => Hgabs1gabs2.
  move: (mk_env_udiv_newer_gen Hmkudiv) => Hgabs2gudiv.
  move: (mk_env_abs_newer_cnf Hmkabs1 Hgtt Hgls1) => Hgabs1csabs1.
  move: (newer_than_cnf_le_newer Hgabs1csabs1 (pos_leb_trans Hgabs1gabs2 Hgabs2gudiv)) => Hgudivcsabs1.
  move: (newer_than_lit_le_newer Hgtt Hggabs1) => Hgabs1tt.
  move: (newer_than_lits_le_newer Hgls2 Hggabs1) => Hgabs1ls2.
  move: (mk_env_abs_newer_cnf Hmkabs2 Hgabs1tt Hgabs1ls2) => Hgabs2csabs2.
  move: (newer_than_cnf_le_newer Hgabs2csabs2 Hgabs2gudiv) => Hgudivcsabs2.
  move: (newer_than_lit_le_newer Hgabs1tt Hgabs1gabs2) => Hgabs2tt.
  move: (mk_env_abs_newer_res Hmkabs1 Hgtt Hgls1) => Hgabs1labs1.
  move: (newer_than_lits_le_newer Hgabs1labs1 Hgabs1gabs2) => Hgabs2labs1.
  move: (mk_env_abs_newer_res Hmkabs2 Hgabs1tt Hgabs1ls2) => Hgabs2labs2.
  move: (mk_env_udiv_newer_cnf Hmkudiv Hgabs2tt Hgabs2labs1 Hgabs2labs2) => Hgudivcsudiv.
  case ((splitmsl ls1).2 == lit_ff); last case ((splitmsl ls1).2 == lit_tt).
  - case=> _ <- <- _.
    by rewrite !newer_than_cnf_catrev Hgudivcsabs1 Hgudivcsabs2 Hgudivcsudiv.
  - dcase (mk_env_neg E_udiv g_udiv lrs_urem) => [[[[E_neg] g_neg] cs_neg] lrs_neg] Hmkneg.
    case=> _ <- <- _.
    move: (mk_env_neg_newer_gen Hmkneg) => Hgudivgneg.
    move: (newer_than_cnf_le_newer Hgudivcsabs1 Hgudivgneg) => Hgnegcsabs1.
    move: (newer_than_cnf_le_newer Hgudivcsabs2 Hgudivgneg) => Hgnegcsabs2.
    move: (newer_than_cnf_le_newer Hgudivcsudiv Hgudivgneg) => Hgnegcsudiv.
    move: (newer_than_lit_le_newer Hgabs2tt Hgabs2gudiv) => Hgudivtt.
    move: (mk_env_udiv_newer_res Hmkudiv Hgabs2tt Hgabs2labs1 Hgabs2labs2) => /andP [Hgudivlurem _].
    move: (mk_env_neg_newer_cnf Hmkneg Hgudivtt Hgudivlurem) => Hgnegcsneg.
    by rewrite !newer_than_cnf_catrev Hgnegcsabs1 Hgnegcsabs2 Hgnegcsudiv Hgnegcsneg.
  - dcase (mk_env_xor E_udiv g_udiv lrs_urem (copy (size ls1) (splitmsl ls1).2)) 
    => [[[[E_xor] g_xor] cs_xor] lrs_xor] Hmkxor.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor g_xor [::(splitmsl ls1).2])
    => [[[[E_zext] g_zext] cs_zext] lrs_zext] Hmkzext.
    dcase (mk_env_add E_zext g_zext lrs_xor lrs_zext)
    => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    case=> _ <- <- _.
    move: (mk_env_xor_newer_gen Hmkxor) => Hgudivgxor.
    move: (mk_env_zeroextend_newer_gen Hmkzext) => Hgxorgzext.
    move: (mk_env_add_newer_gen Hmkadd) => Hgzextgadd.
    move: (pos_leb_trans Hgudivgxor (pos_leb_trans Hgxorgzext Hgzextgadd)) => Hgudivgadd.
    move: (newer_than_cnf_le_newer Hgudivcsabs1 Hgudivgadd) => Hgaddcsabs1.
    move: (newer_than_cnf_le_newer Hgudivcsabs2 Hgudivgadd) => Hgaddcsabs2.
    move: (newer_than_cnf_le_newer Hgudivcsudiv Hgudivgadd) => Hgaddcsudiv.
    move: (newer_than_lit_le_newer Hgabs2tt Hgabs2gudiv) => Hgudivtt.
    move: (mk_env_udiv_newer_res Hmkudiv Hgabs2tt Hgabs2labs1 Hgabs2labs2) => /andP [Hgudivlurem _].
    move: (newer_than_lits_le_newer Hgls1 (pos_leb_trans Hggabs1 (pos_leb_trans Hgabs1gabs2 Hgabs2gudiv))) => Hgudivls1.
    move: (newer_than_lits_msl Hgudivtt Hgudivls1) => Hgudivmsl1.
    move: (newer_than_lits_copy (size ls1) Hgudivmsl1) => Hgudivcopy.
    move: (mk_env_xor_newer_cnf Hmkxor Hgudivtt Hgudivlurem Hgudivcopy) => Hgxorcsxor.
    move: (newer_than_cnf_le_newer Hgxorcsxor (pos_leb_trans Hgxorgzext Hgzextgadd)) => Hgaddcsxor.
    move: (newer_than_lit_le_newer Hgudivtt Hgudivgxor) => Hgxortt.
    move: (newer_than_lit_le_newer Hgudivmsl1 Hgudivgxor) => Hgxormsl1.
    move: (newer_than_lits_copy 1 Hgxormsl1) => Hgxor1msl1.
    move: (mk_env_zeroextend_newer_cnf Hmkzext Hgxortt Hgxor1msl1) => Hgzextcszext.
    move: (newer_than_cnf_le_newer Hgzextcszext Hgzextgadd) => Hgaddcszext.
    move: (mk_env_xor_newer_res Hmkxor Hgudivtt Hgudivlurem Hgudivcopy) => Hgxorlxor.
    move: (newer_than_lits_le_newer Hgxorlxor Hgxorgzext) => Hgzextlxor.
    move: (mk_env_zeroextend_newer_res Hmkzext Hgxortt Hgxor1msl1) => Hgzextlzext.
    move: (newer_than_lit_le_newer Hgxortt Hgxorgzext) => Hgzexttt.
    rewrite newer_than_lit_tt_ff in Hgzexttt.
    move: (mk_env_add_newer_cnf Hmkadd Hgzextlxor Hgzextlzext Hgzexttt) => Hgaddcsadd.
    by rewrite !newer_than_cnf_catrev Hgaddcsabs1 Hgaddcsabs2 Hgaddcsudiv 
               Hgaddcsxor Hgaddcszext Hgaddcsadd.
Qed.

Lemma mk_env_srem_preserve :
  forall E g ls1 ls2 E' g' cs lrs,
    mk_env_srem E g ls1 ls2 = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move=> E g ls1 ls2 E' g' cs lrs. rewrite /mk_env_srem.
  dcase (mk_env_abs E g ls1) => [[[[E_abs1] g_abs1] cs_abs1] lrs_abs1] Hmkabs1.
  dcase (mk_env_abs E_abs1 g_abs1 ls2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkabs2.
  dcase (mk_env_udiv E_abs2 g_abs2 lrs_abs1 lrs_abs2) => [[[[[E_udiv] g_udiv] cs_udiv] lrs_udiv] lrs_urem] Hmkudiv.
  move: (mk_env_abs_newer_gen Hmkabs1) => Hggabs1.
  move: (mk_env_abs_newer_gen Hmkabs2) => Hgabs1gabs2.
  move: (mk_env_udiv_newer_gen Hmkudiv) => Hgabs2gudiv.
  move: (mk_env_abs_preserve Hmkabs1) => HEEabs1g.
  move: (mk_env_abs_preserve Hmkabs2) => HEabs1Eabs2gabs1.
  move: (env_preserve_le HEabs1Eabs2gabs1 Hggabs1) => HEabs1Eabs2g.
  move: (mk_env_udiv_preserve Hmkudiv) => HEabs2Eudivgabs2.
  move: (env_preserve_le HEabs2Eudivgabs2 (pos_leb_trans Hggabs1 Hgabs1gabs2)) => HEabs2Eudivg.
  case ((splitmsl ls1).2 == lit_ff); last case ((splitmsl ls1).2 == lit_tt).
  - case=> <- _ _ _. by t_auto_preserve.
  - dcase (mk_env_neg E_udiv g_udiv lrs_urem) 
    => [[[[E_neg] g_neg] cs_neg] lrs_neg] Hmkneg.
    case=> <- _ _ _.
    move: (mk_env_neg_newer_gen Hmkneg) => Hgudivgneg.
    move: (mk_env_neg_preserve Hmkneg) => HEudivEneggudiv.
    by t_auto_preserve.
  - dcase (mk_env_xor E_udiv g_udiv lrs_urem (copy (size ls1) (splitmsl ls1).2)) 
    => [[[[E_xor] g_xor] cs_xor] lrs_xor] Hmkxor.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor g_xor [::(splitmsl ls1).2])
    => [[[[E_zext] g_zext] cs_zext] lrs_zext] Hmkzext.
    dcase (mk_env_add E_zext g_zext lrs_xor lrs_zext)
    => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    case=> <- _ _ _.
    move: (mk_env_xor_newer_gen Hmkxor) => Hgudivgxor.
    move: (mk_env_zeroextend_newer_gen Hmkzext) => Hgxorgzext.
    move: (mk_env_add_newer_gen Hmkadd) => Hgzextgadd.
    move: (mk_env_xor_preserve Hmkxor) => HEudivExorgudiv.
    move: (mk_env_zeroextend_preserve Hmkzext) => HExorEzextgxor.
    move: (mk_env_add_preserve Hmkadd) => HEzextEaddgzext.
    move: (env_preserve_le HExorEzextgxor Hgudivgxor) => HExorEzextgudiv.
    move: (env_preserve_le HEzextEaddgzext (pos_leb_trans Hgudivgxor Hgxorgzext)) => HEzextEaddgudiv.
    move: (pos_leb_trans Hggabs1 (pos_leb_trans Hgabs1gabs2 Hgabs2gudiv)) => Hggudiv.
    move: (env_preserve_le HEudivExorgudiv Hggudiv) => HEudivExorg.
    move: (env_preserve_le HExorEzextgudiv Hggudiv) => HExorEzextg.
    move: (env_preserve_le HEzextEaddgudiv Hggudiv) => HEzextEaddg.
    apply (env_preserve_trans HEEabs1g); apply (env_preserve_trans HEabs1Eabs2g);
    apply (env_preserve_trans HEabs2Eudivg); apply (env_preserve_trans HEudivExorg);
    by apply (env_preserve_trans HExorEzextg).
Qed.

Lemma mk_env_srem_sat :
  forall E g ls1 ls2 E' g' cs lrs,
    mk_env_srem E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move => E g ls1 ls2 E' g' cs lrs. rewrite /mk_env_srem /mk_env_abs.
  dcase (mk_env_neg E g ls1) => [[[[E_neg1] g_neg1] cs_neg1] rs_neg1] Hmkneg1.
  dcase (mk_env_xor E g ls1 (copy (size ls1) (splitmsl ls1).2)) => [[[[E_xor1] g_xor1] cs_xor1] rs_xor1] Hmkxor1.
  dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xor1 g_xor1 [:: (splitmsl ls1).2]) => [[[[E_zext1] g_zext1] cs_zext1] rs_zext1] Hmkzext1.
  dcase (mk_env_add E_zext1 g_zext1 rs_xor1 rs_zext1) => [[[[E_add] g_add] cs_add] rs_add] Hmkadd1.
  move : (mk_env_neg_newer_gen Hmkneg1) => Hnewneg1.
  move : (mk_env_xor_newer_gen Hmkxor1) => Hnewxor1.
  move : (mk_env_zeroextend_newer_gen Hmkzext1) => Hnewzext1.
  move : (mk_env_add_newer_gen Hmkadd1) => Hnewadd1.
  move : (pos_leb_trans Hnewxor1 (pos_leb_trans Hnewzext1 Hnewadd1)) => Hnegls1.
  case Htt1: ((splitmsl ls1).2 == lit_tt); case Hff1 : ((splitmsl ls1).2 == lit_ff);
    case Htt2 : ((splitmsl ls2).2 == lit_tt); case Hff2 : ((splitmsl ls2).2 == lit_ff);
      try rewrite (eqP Htt1)// in Hff1; try rewrite (eqP Htt2)// in Hff2.
  - dcase (mk_env_neg E_neg1 g_neg1 ls2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkneg2.
    dcase (mk_env_udiv E_abs2 g_abs2 rs_neg1 lrs_abs2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lrs_udiv) => [[[[E_negr] g_negr] cs_negr] lrs_negr] Hmknegr.
    move : (mk_env_neg_newer_gen Hmkneg2) => Hnewneg2.
    move : (mk_env_udiv_newer_gen Hmkudiv) => Hnewudiv.
    case => <- _ <- _ //; move => Htt Hls1 Hls2; generalize Htt; rewrite newer_than_lit_tt_ff; move => Hff.
    move : (mk_env_neg_newer_res Hmkneg1 Htt Hls1) => Hgneg1.
    move : (mk_env_neg_newer_res Hmkneg2 (newer_than_lit_le_newer Htt Hnewneg1) (newer_than_lits_le_newer Hls2 Hnewneg1)) => Hgneg2.
    move/andP : (mk_env_udiv_newer_res Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 Hnewneg2)) (newer_than_lits_le_newer Hgneg1 Hnewneg2) Hgneg2) => [Hgudiv _].
    move : (mk_env_neg_sat Hmkneg1 Hff Hls1) => Hcnfneg1.
    move : (mk_env_neg_sat Hmkneg2 (newer_than_lit_le_newer Hff Hnewneg1) (newer_than_lits_le_newer Hls2 Hnewneg1)) => Hcnfneg2.
    move : (mk_env_udiv_sat Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 Hnewneg2)) (newer_than_lits_le_newer Hgneg1 Hnewneg2) Hgneg2) => Hcnfudiv.
    move : (mk_env_neg_sat Hmknegr (newer_than_lit_le_newer Hff (pos_leb_trans Hnewneg1 (pos_leb_trans Hnewneg2 Hnewudiv))) Hgudiv) => Hcnfnegr.
    rewrite !interp_cnf_catrev.
    move : (mk_env_udiv_newer_cnf Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 Hnewneg2)) (newer_than_lits_le_newer Hgneg1 Hnewneg2) Hgneg2) => Hcsudiv.
    rewrite Hcnfnegr.
    rewrite (env_preserve_cnf (mk_env_neg_preserve Hmknegr) (mk_env_udiv_newer_cnf Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 Hnewneg2)) (newer_than_lits_le_newer Hgneg1 Hnewneg2) Hgneg2)) Hcnfudiv.
    rewrite (env_preserve_cnf (mk_env_neg_preserve Hmknegr) (newer_than_cnf_le_newer (mk_env_neg_newer_cnf Hmkneg2 (newer_than_lit_le_newer Htt Hnewneg1) (newer_than_lits_le_newer Hls2 Hnewneg1)) Hnewudiv)).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (mk_env_neg_newer_cnf Hmkneg2 (newer_than_lit_le_newer Htt Hnewneg1) (newer_than_lits_le_newer Hls2 Hnewneg1))) Hcnfneg2. 
    rewrite (env_preserve_cnf (mk_env_neg_preserve Hmknegr) (newer_than_cnf_le_newer (mk_env_neg_newer_cnf Hmkneg1 Htt Hls1) (pos_leb_trans Hnewneg2 Hnewudiv))).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (newer_than_cnf_le_newer (mk_env_neg_newer_cnf Hmkneg1 Htt Hls1) Hnewneg2)).
    rewrite (env_preserve_cnf (mk_env_neg_preserve Hmkneg2) (mk_env_neg_newer_cnf Hmkneg1 Htt Hls1)) Hcnfneg1//.
  - dcase (mk_env_udiv E_neg1 g_neg1 rs_neg1 ls2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lrs_udiv) => [[[[E_negr] g_negr] cs_negr] lrs_negr] Hmknegr.
    move : (mk_env_udiv_newer_gen Hmkudiv) => Hnewudiv.
    case => <- _ <- _ //; move => Htt Hls1 Hls2; generalize Htt; rewrite newer_than_lit_tt_ff; move => Hff.
    rewrite !interp_cnf_catrev.
    move : (mk_env_neg_newer_res Hmkneg1 Htt Hls1) => Hgneg1.
    move/andP : (mk_env_udiv_newer_res Hmkudiv (newer_than_lit_le_newer Htt Hnewneg1) Hgneg1 (newer_than_lits_le_newer Hls2 Hnewneg1)) => [Hgudiv _].
    move : (mk_env_neg_sat Hmkneg1 Hff Hls1) => Hcnfneg1.
    move : (mk_env_udiv_sat Hmkudiv (newer_than_lit_le_newer Htt Hnewneg1) Hgneg1 (newer_than_lits_le_newer Hls2 Hnewneg1)) => Hcnfudiv.
    rewrite (mk_env_neg_sat Hmknegr (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 Hnewudiv)) Hgudiv).
    rewrite (env_preserve_cnf (mk_env_neg_preserve Hmknegr) (mk_env_udiv_newer_cnf Hmkudiv (newer_than_lit_le_newer Htt Hnewneg1) Hgneg1 (newer_than_lits_le_newer Hls2 Hnewneg1))) Hcnfudiv.
    rewrite (env_preserve_cnf (mk_env_neg_preserve Hmknegr) (newer_than_cnf_le_newer (mk_env_neg_newer_cnf Hmkneg1 Htt Hls1) Hnewudiv)).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (mk_env_neg_newer_cnf Hmkneg1 Htt Hls1)) Hcnfneg1//.
  - dcase (mk_env_xor E_neg1 g_neg1 ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[[E_xor2] g_xor2] cs_xor2] rs_xor2] Hmkxor2.
    dcase (mk_env_zeroextend (size (splitmsl ls2).1) E_xor2 g_xor2 [:: (splitmsl ls2).2]) => [[[[E_zext2] g_zext2] cs_zext2] rs_zext2] Hmkzext2.
    dcase (mk_env_add E_zext2 g_zext2 rs_xor2 rs_zext2) => [[[[E_add2] g_add2] cs_add2] rs_add2] Hmkadd2.
    dcase (mk_env_udiv E_add2 g_add2 rs_neg1 rs_add2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv] lrs_udiv] Hmkudiv.
    dcase (mk_env_neg E_udiv g_udiv lrs_udiv) => [[[[E_negr] g_negr] cs_negr] lrs_negr] Hmknegr.
    move : (mk_env_xor_newer_gen Hmkxor2) => Hnewxor2.
    move : (mk_env_zeroextend_newer_gen Hmkzext2) => Hnewzext2.
    move : (mk_env_add_newer_gen Hmkadd2) => Hnewadd2.
    move : (mk_env_udiv_newer_gen Hmkudiv) => Hnewudiv.
    case => <- _ <- _ //; move => Htt Hls1 Hls2; generalize Htt; rewrite newer_than_lit_tt_ff; move => Hff.
    rewrite !interp_cnf_catrev.
    move : (mk_env_neg_newer_res Hmkneg1 Htt Hls1) => Hgneg1.
    have Hnewcp : (newer_than_lits g_neg1 (copy (size ls2) (splitmsl ls2).2)).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls2) => [_ Hnewcp2].
      exact : (newer_than_lits_le_newer (newer_than_lits_copy (size ls2) Hnewcp2) Hnewneg1).
    }
    have Hnewmsl: (newer_than_lits g_xor2 [:: (splitmsl ls2).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls2) => [_ Hnewcp2].
      exact : (newer_than_lits_le_newer (newer_than_lits_copy 1 Hnewcp2) (pos_leb_trans Hnewneg1 Hnewxor2)).
    }
    move : (mk_env_xor_newer_res Hmkxor2 (newer_than_lit_le_newer Htt Hnewneg1) (newer_than_lits_le_newer Hls2 Hnewneg1) Hnewcp) => Hgxor2.
    move : (mk_env_zeroextend_newer_res Hmkzext2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 Hnewxor2)) Hnewmsl) => Hgzext2.
    move : (mk_env_add_newer_res Hmkadd2) => Hgadd2.
    move/andP : (mk_env_udiv_newer_res Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 Hnewadd2)))) (newer_than_lits_le_newer Hgneg1 (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 Hnewadd2))) Hgadd2) => [Hgudiv _].
    move : (mk_env_neg_sat Hmkneg1 Htt Hls1) => Hcnfneg1.
    move : (mk_env_xor_sat Hmkxor2 (newer_than_lit_le_newer Htt Hnewneg1) (newer_than_lits_le_newer Hls2 Hnewneg1) Hnewcp) => Hcnfxor2.
    move : (mk_env_zeroextend_sat Hmkzext2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 Hnewxor2)) Hnewmsl) => Hcnfzext2.
    move : (mk_env_add_sat Hmkadd2 (newer_than_lits_le_newer Hgxor2 Hnewzext2) Hgzext2 (newer_than_lit_le_newer Hff (pos_leb_trans Hnewneg1 (pos_leb_trans Hnewxor2 Hnewzext2)))) => Hcnfadd2.
    move : (mk_env_udiv_sat Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 Hnewadd2)))) (newer_than_lits_le_newer Hgneg1 (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 Hnewadd2))) Hgadd2) => Hcnfudiv.
    rewrite (mk_env_neg_sat Hmknegr (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 (pos_leb_trans Hnewadd2 Hnewudiv))))) Hgudiv).
    rewrite (env_preserve_cnf (mk_env_neg_preserve Hmknegr) (mk_env_udiv_newer_cnf Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 Hnewadd2)))) (newer_than_lits_le_newer Hgneg1 (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 Hnewadd2))) Hgadd2)) Hcnfudiv.
    rewrite (env_preserve_cnf (mk_env_neg_preserve Hmknegr) (newer_than_cnf_le_newer (mk_env_add_newer_cnf Hmkadd2 (newer_than_lits_le_newer Hgxor2 Hnewzext2) Hgzext2 (newer_than_lit_le_newer Hff (pos_leb_trans Hnewneg1 (pos_leb_trans Hnewxor2 Hnewzext2)))) Hnewudiv)).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (mk_env_add_newer_cnf Hmkadd2 (newer_than_lits_le_newer Hgxor2 Hnewzext2) Hgzext2 (newer_than_lit_le_newer Hff (pos_leb_trans Hnewneg1 (pos_leb_trans Hnewxor2 Hnewzext2))))) Hcnfadd2.
    rewrite (env_preserve_cnf (mk_env_neg_preserve Hmknegr) (newer_than_cnf_le_newer (mk_env_zeroextend_newer_cnf Hmkzext2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 Hnewxor2)) Hnewmsl) (pos_leb_trans Hnewadd2 Hnewudiv))).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (newer_than_cnf_le_newer (mk_env_zeroextend_newer_cnf Hmkzext2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 Hnewxor2)) Hnewmsl) Hnewadd2)).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd2) (mk_env_zeroextend_newer_cnf Hmkzext2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewneg1 Hnewxor2)) Hnewmsl)) Hcnfzext2.
    rewrite (env_preserve_cnf (mk_env_neg_preserve Hmknegr) (newer_than_cnf_le_newer (mk_env_xor_newer_cnf Hmkxor2 (newer_than_lit_le_newer Htt Hnewneg1) (newer_than_lits_le_newer Hls2 Hnewneg1) Hnewcp) (pos_leb_trans Hnewzext2 (pos_leb_trans Hnewadd2 Hnewudiv)))).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (newer_than_cnf_le_newer (mk_env_xor_newer_cnf Hmkxor2 (newer_than_lit_le_newer Htt Hnewneg1) (newer_than_lits_le_newer Hls2 Hnewneg1) Hnewcp) (pos_leb_trans Hnewzext2 Hnewadd2))).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd2) (newer_than_cnf_le_newer (mk_env_xor_newer_cnf Hmkxor2 (newer_than_lit_le_newer Htt Hnewneg1) (newer_than_lits_le_newer Hls2 Hnewneg1) Hnewcp) Hnewzext2)).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzext2) (mk_env_xor_newer_cnf Hmkxor2 (newer_than_lit_le_newer Htt Hnewneg1) (newer_than_lits_le_newer Hls2 Hnewneg1) Hnewcp)) Hcnfxor2.
    rewrite (env_preserve_cnf (mk_env_neg_preserve Hmknegr) (newer_than_cnf_le_newer (mk_env_neg_newer_cnf Hmkneg1 Htt Hls1) (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 (pos_leb_trans Hnewadd2 Hnewudiv))))).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (newer_than_cnf_le_newer (mk_env_neg_newer_cnf Hmkneg1 Htt Hls1) (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 Hnewadd2)))).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd2) (newer_than_cnf_le_newer (mk_env_neg_newer_cnf Hmkneg1 Htt Hls1) (pos_leb_trans Hnewxor2 Hnewzext2))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzext2) (newer_than_cnf_le_newer (mk_env_neg_newer_cnf Hmkneg1 Htt Hls1) Hnewxor2)).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxor2) (mk_env_neg_newer_cnf Hmkneg1 Htt Hls1)) Hcnfneg1//.
  - dcase (mk_env_neg E g ls2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkneg2.
    dcase (mk_env_udiv E_abs2 g_abs2 ls1 lrs_abs2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    move : (mk_env_neg_newer_gen Hmkneg2) => Hnewneg2.
    case => <- _ <- _ //; move => Htt Hls1 Hls2; generalize Htt; rewrite newer_than_lit_tt_ff; move => Hff.
    rewrite !interp_cnf_catrev.
    move : (mk_env_neg_newer_res Hmkneg2 Htt Hls2) => Hgneg2.
    rewrite (mk_env_udiv_sat Hmkudiv (newer_than_lit_le_newer Htt Hnewneg2) (newer_than_lits_le_newer Hls1 Hnewneg2) Hgneg2).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (mk_env_neg_newer_cnf Hmkneg2 Htt Hls2)) (mk_env_neg_sat Hmkneg2 Hff Hls2)//.
  - dcase (mk_env_udiv E g ls1 ls2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    case => <- _ <- _ //; move => Htt Hls1 Hls2; generalize Htt; rewrite newer_than_lit_tt_ff; move => Hff.
    rewrite (mk_env_udiv_sat Hmkudiv Htt Hls1 Hls2)//.
  - dcase (mk_env_xor E g ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[[E_xor2] g_xor2] cs_xor2] rs_xor2] Hmkxor2.
    dcase (mk_env_zeroextend (size (splitmsl ls2).1) E_xor2 g_xor2 [:: (splitmsl ls2).2]) => [[[[E_zext2] g_zext2] cs_zext2] rs_zext2] Hmkzext2.
    dcase (mk_env_add E_zext2 g_zext2 rs_xor2 rs_zext2) => [[[[E_add2] g_add2] cs_add2] rs_add2] Hmkadd2.
    dcase (mk_env_udiv E_add2 g_add2 ls1 rs_add2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv] lrs_udiv] Hmkudiv.
    case => <- _ <- _ //; move => Htt Hls1 Hls2; generalize Htt; rewrite newer_than_lit_tt_ff; move => Hff.
    rewrite !interp_cnf_catrev.
    move : (mk_env_xor_newer_gen Hmkxor2) => Hnewxor2.
    move : (mk_env_zeroextend_newer_gen Hmkzext2) => Hnewzext2.
    move : (mk_env_add_newer_gen Hmkadd2) => Hnewadd2.
    have Hnewcp : (newer_than_lits g (copy (size ls2) (splitmsl ls2).2)).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls2) => [_ Hnewcp2].
      exact : (newer_than_lits_copy (size ls2) Hnewcp2).
    }
    have Hnewmsl: (newer_than_lits g_xor2 [:: (splitmsl ls2).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls2) => [_ Hnewcp2].
      exact : (newer_than_lits_le_newer (newer_than_lits_copy 1 Hnewcp2) Hnewxor2).
    }
    move : (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 Hnewadd2)) => Hggadd2.
    move : (mk_env_xor_newer_res Hmkxor2 Htt Hls2 Hnewcp) => Hgxor2.
    move : (mk_env_zeroextend_newer_res Hmkzext2 (newer_than_lit_le_newer Htt Hnewxor2) Hnewmsl) => Hgzext2.
    move : (mk_env_add_newer_res Hmkadd2) => Hgadd2.
    move/andP : (mk_env_udiv_newer_res Hmkudiv (newer_than_lit_le_newer Htt Hggadd2) (newer_than_lits_le_newer Hls1 Hggadd2) Hgadd2) => [Hgudiv _].
    move : (mk_env_xor_sat Hmkxor2 Htt Hls2 Hnewcp) => Hcnfxor2.
    move : (mk_env_zeroextend_sat Hmkzext2 (newer_than_lit_le_newer Htt Hnewxor2) Hnewmsl) => Hcnfzext2.
    move : (mk_env_add_sat Hmkadd2 (newer_than_lits_le_newer Hgxor2 Hnewzext2) Hgzext2 (newer_than_lit_le_newer Hff (pos_leb_trans Hnewxor2 Hnewzext2))) => Hcnfadd2.
    rewrite (mk_env_udiv_sat Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 Hnewadd2))) (newer_than_lits_le_newer Hls1 Hggadd2) Hgadd2).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (mk_env_add_newer_cnf Hmkadd2 (newer_than_lits_le_newer Hgxor2 Hnewzext2) Hgzext2 (newer_than_lit_le_newer Hff (pos_leb_trans Hnewxor2 Hnewzext2)))) Hcnfadd2.
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (newer_than_cnf_le_newer (mk_env_zeroextend_newer_cnf Hmkzext2 (newer_than_lit_le_newer Htt Hnewxor2) Hnewmsl) Hnewadd2)).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd2) (mk_env_zeroextend_newer_cnf Hmkzext2 (newer_than_lit_le_newer Htt Hnewxor2) Hnewmsl)) Hcnfzext2.
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (newer_than_cnf_le_newer (mk_env_xor_newer_cnf Hmkxor2 Htt Hls2 Hnewcp) (pos_leb_trans Hnewzext2 Hnewadd2))).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd2) (newer_than_cnf_le_newer (mk_env_xor_newer_cnf Hmkxor2 Htt Hls2 Hnewcp) Hnewzext2)).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzext2) (mk_env_xor_newer_cnf Hmkxor2 Htt Hls2 Hnewcp)) Hcnfxor2//.
  - dcase (mk_env_neg E_add g_add ls2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkneg2.
    dcase (mk_env_udiv E_abs2 g_abs2 rs_add lrs_abs2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_xor E_udiv g_udiv lrs_udiv (copy (size ls1) (splitmsl ls1).2)) => [[[[E_xorr] g_xorr] cs_xorr] rs_xorr] Hmkxorr.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xorr g_xorr [:: (splitmsl ls1).2]) => [[[[E_zextr] g_zextr] cs_zextr] rs_zextr] Hmkzextr.
    dcase (mk_env_add E_zextr g_zextr rs_xorr rs_zextr) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    case => <- _ <- _ //; move => Htt Hls1 Hls2; generalize Htt; rewrite newer_than_lit_tt_ff; move => Hff.
    rewrite !interp_cnf_catrev.
    move : (mk_env_neg_newer_gen Hmkneg2) => Hnewneg2.
    move : (mk_env_udiv_newer_gen Hmkudiv) => Hnewudiv.
    move : (mk_env_xor_newer_gen Hmkxorr) => Hnewxorr.
    move : (mk_env_zeroextend_newer_gen Hmkzextr) => Hnewzextr.
    move : (mk_env_add_newer_gen Hmkaddr) => Hnewaddr.
    have Hnewcp : (newer_than_lits g (copy (size ls1) (splitmsl ls1).2)).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls1) => [_ Hnewcp2].
      exact : (newer_than_lits_copy (size ls1) Hnewcp2).
    }
    have Hnewmsl: (newer_than_lits g [:: (splitmsl ls1).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls1) => [_ Hnewcp2].
      exact : (newer_than_lits_copy 1 Hnewcp2) .
    }
    move : (pos_leb_trans Hnegls1 (pos_leb_trans Hnewneg2 (pos_leb_trans Hnewudiv Hnewxorr))) => Hggxorr.
    move : (mk_env_xor_newer_res Hmkxor1 Htt Hls1 Hnewcp) => Hgxor1.
    move : (mk_env_zeroextend_newer_res Hmkzext1 (newer_than_lit_le_newer Htt Hnewxor1) (newer_than_lits_le_newer Hnewmsl Hnewxor1)) => Hgzext1.
    move : (mk_env_add_newer_res Hmkadd1) => Hgadd1.
    move : (mk_env_neg_newer_res Hmkneg2 (newer_than_lit_le_newer Htt Hnegls1) (newer_than_lits_le_newer Hls2 Hnegls1)) => Hgneg2.
    move/andP : (mk_env_udiv_newer_res Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 Hnewneg2)) (newer_than_lits_le_newer Hgadd1 Hnewneg2) Hgneg2) => [Hgudiv _].
    move : (mk_env_xor_newer_res Hmkxorr (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 (pos_leb_trans Hnewneg2 Hnewudiv))) Hgudiv (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnegls1 (pos_leb_trans Hnewneg2 Hnewudiv)))) => Hgxorr.
    move : (mk_env_zeroextend_newer_res Hmkzextr (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 (pos_leb_trans Hnewneg2 (pos_leb_trans Hnewudiv Hnewxorr)))) (newer_than_lits_le_newer Hnewmsl Hggxorr)) => Hgzextr.
    move : (mk_env_xor_sat Hmkxorr (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 (pos_leb_trans Hnewneg2 Hnewudiv))) Hgudiv (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnegls1 (pos_leb_trans Hnewneg2 Hnewudiv)))) => Hcnfxorr.
    move : (mk_env_zeroextend_sat Hmkzextr (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 (pos_leb_trans Hnewneg2 (pos_leb_trans Hnewudiv Hnewxorr)))) (newer_than_lits_le_newer Hnewmsl Hggxorr)) => Hcnfzextr.
    move : (mk_env_udiv_sat Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 Hnewneg2)) (newer_than_lits_le_newer Hgadd1 Hnewneg2) Hgneg2) => Hcnfudiv.
    rewrite (mk_env_add_sat Hmkaddr (newer_than_lits_le_newer Hgxorr Hnewzextr) Hgzextr (newer_than_lit_le_newer Hff (pos_leb_trans Hnegls1 (pos_leb_trans Hnewneg2 (pos_leb_trans Hnewudiv (pos_leb_trans Hnewxorr Hnewzextr)))))).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (mk_env_zeroextend_newer_cnf Hmkzextr (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 (pos_leb_trans Hnewneg2 (pos_leb_trans Hnewudiv Hnewxorr)))) (newer_than_lits_le_newer Hnewmsl Hggxorr))) Hcnfzextr.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer (mk_env_xor_newer_cnf Hmkxorr (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 (pos_leb_trans Hnewneg2 Hnewudiv))) Hgudiv (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnegls1 (pos_leb_trans Hnewneg2 Hnewudiv)))) Hnewzextr)).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) (mk_env_xor_newer_cnf Hmkxorr (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 (pos_leb_trans Hnewneg2 Hnewudiv))) Hgudiv (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnegls1 (pos_leb_trans Hnewneg2 Hnewudiv))))) Hcnfxorr.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer (mk_env_udiv_newer_cnf Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 Hnewneg2)) (newer_than_lits_le_newer Hgadd1 Hnewneg2) Hgneg2) (pos_leb_trans Hnewxorr Hnewzextr))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) (newer_than_cnf_le_newer (mk_env_udiv_newer_cnf Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 Hnewneg2)) (newer_than_lits_le_newer Hgadd1 Hnewneg2) Hgneg2) Hnewxorr)).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxorr) (mk_env_udiv_newer_cnf Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 Hnewneg2)) (newer_than_lits_le_newer Hgadd1 Hnewneg2) Hgneg2)) Hcnfudiv.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer (mk_env_xor_newer_cnf Hmkxor1 Htt Hls1 Hnewcp) (pos_leb_trans Hnewzext1 (pos_leb_trans Hnewadd1 (pos_leb_trans Hnewneg2 (pos_leb_trans Hnewudiv (pos_leb_trans Hnewxorr Hnewzextr))))))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) (newer_than_cnf_le_newer (mk_env_xor_newer_cnf Hmkxor1 Htt Hls1 Hnewcp) (pos_leb_trans Hnewzext1 (pos_leb_trans Hnewadd1 (pos_leb_trans Hnewneg2 (pos_leb_trans Hnewudiv Hnewxorr)))))).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxorr) (newer_than_cnf_le_newer (mk_env_xor_newer_cnf Hmkxor1 Htt Hls1 Hnewcp) (pos_leb_trans Hnewzext1 (pos_leb_trans Hnewadd1 (pos_leb_trans Hnewneg2 Hnewudiv))))).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (newer_than_cnf_le_newer (mk_env_xor_newer_cnf Hmkxor1 Htt Hls1 Hnewcp) (pos_leb_trans Hnewzext1 (pos_leb_trans Hnewadd1 Hnewneg2)))).
    rewrite (env_preserve_cnf (mk_env_neg_preserve Hmkneg2) (newer_than_cnf_le_newer (mk_env_xor_newer_cnf Hmkxor1 Htt Hls1 Hnewcp) (pos_leb_trans Hnewzext1 Hnewadd1))).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd1) (newer_than_cnf_le_newer (mk_env_xor_newer_cnf Hmkxor1 Htt Hls1 Hnewcp) Hnewzext1)).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzext1) (mk_env_xor_newer_cnf Hmkxor1 Htt Hls1 Hnewcp)) (mk_env_xor_sat Hmkxor1 Htt Hls1 Hnewcp).
    move : (mk_env_zeroextend_newer_cnf Hmkzext1 (newer_than_lit_le_newer Htt Hnewxor1) (newer_than_lits_le_newer Hnewmsl Hnewxor1)) => Hcszext1.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer Hcszext1 (pos_leb_trans Hnewadd1 (pos_leb_trans Hnewneg2 (pos_leb_trans Hnewudiv (pos_leb_trans Hnewxorr Hnewzextr)))))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) (newer_than_cnf_le_newer Hcszext1 (pos_leb_trans Hnewadd1 (pos_leb_trans Hnewneg2 (pos_leb_trans Hnewudiv Hnewxorr))))).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxorr) (newer_than_cnf_le_newer Hcszext1 (pos_leb_trans Hnewadd1 (pos_leb_trans Hnewneg2 Hnewudiv)))).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (newer_than_cnf_le_newer Hcszext1 (pos_leb_trans Hnewadd1 Hnewneg2))).
    rewrite (env_preserve_cnf (mk_env_neg_preserve Hmkneg2) (newer_than_cnf_le_newer Hcszext1 Hnewadd1)).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd1) Hcszext1) (mk_env_zeroextend_sat Hmkzext1 (newer_than_lit_le_newer Htt Hnewxor1) (newer_than_lits_le_newer Hnewmsl Hnewxor1)).
    move : (mk_env_add_newer_cnf Hmkadd1 (newer_than_lits_le_newer Hgxor1 Hnewzext1) Hgzext1 (newer_than_lit_le_newer Hff (pos_leb_trans Hnewxor1 Hnewzext1))) => Hcsadd1.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer Hcsadd1 (pos_leb_trans Hnewneg2 (pos_leb_trans Hnewudiv (pos_leb_trans Hnewxorr Hnewzextr))))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) (newer_than_cnf_le_newer Hcsadd1 (pos_leb_trans Hnewneg2 (pos_leb_trans Hnewudiv Hnewxorr)))).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxorr) (newer_than_cnf_le_newer Hcsadd1 (pos_leb_trans Hnewneg2 Hnewudiv))).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (newer_than_cnf_le_newer Hcsadd1 Hnewneg2)).
    rewrite (env_preserve_cnf (mk_env_neg_preserve Hmkneg2) Hcsadd1) (mk_env_add_sat Hmkadd1 (newer_than_lits_le_newer Hgxor1 Hnewzext1) Hgzext1 (newer_than_lit_le_newer Hff (pos_leb_trans Hnewxor1 Hnewzext1))).
    move : (mk_env_neg_sat Hmkneg2 (newer_than_lit_le_newer Hff Hnegls1) (newer_than_lits_le_newer Hls2 Hnegls1)) => Hcnfneg2.
    move : (mk_env_neg_newer_cnf Hmkneg2 (newer_than_lit_le_newer Hff Hnegls1) (newer_than_lits_le_newer Hls2 Hnegls1)) => Hcsneg2.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer Hcsneg2 (pos_leb_trans Hnewudiv (pos_leb_trans Hnewxorr Hnewzextr)))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) (newer_than_cnf_le_newer Hcsneg2 (pos_leb_trans Hnewudiv Hnewxorr))).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxorr) (newer_than_cnf_le_newer Hcsneg2 Hnewudiv)).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) Hcsneg2) Hcnfneg2//.
  - dcase (mk_env_udiv E_add g_add rs_add ls2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_xor E_udiv g_udiv lrs_udiv (copy (size ls1) (splitmsl ls1).2)) => [[[[E_xorr] g_xorr] cs_xorr] rs_xorr] Hmkxorr.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xorr g_xorr [:: (splitmsl ls1).2]) => [[[[E_zextr] g_zextr] cs_zextr] rs_zextr] Hmkzextr.
    dcase (mk_env_add E_zextr g_zextr rs_xorr rs_zextr) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    case => <- _ <- _ //; move => Htt Hls1 Hls2; generalize Htt; rewrite newer_than_lit_tt_ff; move => Hff.
    rewrite !interp_cnf_catrev.
    move : (mk_env_udiv_newer_gen Hmkudiv) => Hnewudiv.
    move : (mk_env_xor_newer_gen Hmkxorr) => Hnewxorr.
    move : (mk_env_zeroextend_newer_gen Hmkzextr) => Hnewzextr.
    move : (mk_env_add_newer_gen Hmkaddr) => Hnewaddr.
    have Hnewcp : (newer_than_lits g (copy (size ls1) (splitmsl ls1).2)).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls1) => [_ Hnewcp2].
      exact : (newer_than_lits_copy (size ls1) Hnewcp2).
    }
    have Hnewmsl: (newer_than_lits g [:: (splitmsl ls1).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls1) => [_ Hnewcp2].
      exact : (newer_than_lits_copy 1 Hnewcp2) .
    }
    move : (pos_leb_trans Hnegls1 (pos_leb_trans Hnewudiv Hnewxorr)) => Hggxorr.
    move : (mk_env_xor_newer_res Hmkxor1 Htt Hls1 Hnewcp) => Hgxor1.
    move : (mk_env_zeroextend_newer_res Hmkzext1 (newer_than_lit_le_newer Htt Hnewxor1) (newer_than_lits_le_newer Hnewmsl Hnewxor1)) => Hgzext1.
    move : (mk_env_add_newer_res Hmkadd1) => Hgadd1.
    move/andP : (mk_env_udiv_newer_res Hmkudiv (newer_than_lit_le_newer Htt Hnegls1) Hgadd1 (newer_than_lits_le_newer Hls2 Hnegls1)) => [Hgudiv _].
    move : (mk_env_xor_newer_res Hmkxorr (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 Hnewudiv)) Hgudiv (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnegls1 Hnewudiv))) => Hgxorr.
    move : (mk_env_zeroextend_newer_res Hmkzextr (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 (pos_leb_trans Hnewudiv Hnewxorr))) (newer_than_lits_le_newer Hnewmsl Hggxorr)) => Hgzextr.
    move : (mk_env_xor_sat Hmkxorr (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 Hnewudiv)) Hgudiv (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnegls1 Hnewudiv))) => Hcnfxorr.
    move : (mk_env_zeroextend_sat Hmkzextr (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 (pos_leb_trans Hnewudiv Hnewxorr))) (newer_than_lits_le_newer Hnewmsl Hggxorr)) => Hcnfzextr.
    move : (mk_env_udiv_sat Hmkudiv (newer_than_lit_le_newer Htt Hnegls1) Hgadd1 (newer_than_lits_le_newer Hls2 Hnegls1)) => Hcnfudiv.
    move : (mk_env_xor_newer_cnf Hmkxor1 Htt Hls1 Hnewcp) => Hcsxor1.
    move : (mk_env_xor_sat Hmkxor1 Htt Hls1 Hnewcp) => Hcnfxor1.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer Hcsxor1 (pos_leb_trans Hnewzext1 (pos_leb_trans Hnewadd1 (pos_leb_trans Hnewudiv (pos_leb_trans Hnewxorr Hnewzextr)))))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) (newer_than_cnf_le_newer Hcsxor1 (pos_leb_trans Hnewzext1 (pos_leb_trans Hnewadd1 (pos_leb_trans Hnewudiv Hnewxorr))))).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxorr) (newer_than_cnf_le_newer Hcsxor1 (pos_leb_trans Hnewzext1 (pos_leb_trans Hnewadd1 Hnewudiv)))).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (newer_than_cnf_le_newer Hcsxor1 (pos_leb_trans Hnewzext1 Hnewadd1))).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd1) (newer_than_cnf_le_newer Hcsxor1 Hnewzext1)).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzext1) Hcsxor1) Hcnfxor1.
    move : (mk_env_zeroextend_newer_cnf Hmkzext1 (newer_than_lit_le_newer Htt Hnewxor1) (newer_than_lits_le_newer Hnewmsl Hnewxor1)) => Hcszext1.
    move : (mk_env_zeroextend_sat Hmkzext1 (newer_than_lit_le_newer Htt Hnewxor1) (newer_than_lits_le_newer Hnewmsl Hnewxor1)) => Hcnfzext1.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer Hcszext1 (pos_leb_trans Hnewadd1 (pos_leb_trans Hnewudiv (pos_leb_trans Hnewxorr Hnewzextr))))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) (newer_than_cnf_le_newer Hcszext1 (pos_leb_trans Hnewadd1 (pos_leb_trans Hnewudiv Hnewxorr)))).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxorr) (newer_than_cnf_le_newer Hcszext1 (pos_leb_trans Hnewadd1 Hnewudiv))).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (newer_than_cnf_le_newer Hcszext1 Hnewadd1)).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd1) Hcszext1) Hcnfzext1.
    move : (mk_env_add_newer_cnf Hmkadd1 (newer_than_lits_le_newer Hgxor1 Hnewzext1) Hgzext1 (newer_than_lit_le_newer Hff (pos_leb_trans Hnewxor1 Hnewzext1))) => Hcsadd1.
    move : (mk_env_add_sat Hmkadd1 (newer_than_lits_le_newer Hgxor1 Hnewzext1) Hgzext1 (newer_than_lit_le_newer Hff (pos_leb_trans Hnewxor1 Hnewzext1))) => Hcnfadd1.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer Hcsadd1 (pos_leb_trans Hnewudiv (pos_leb_trans Hnewxorr Hnewzextr)))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) (newer_than_cnf_le_newer Hcsadd1 (pos_leb_trans Hnewudiv Hnewxorr))).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxorr) (newer_than_cnf_le_newer Hcsadd1 Hnewudiv)).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) Hcsadd1) Hcnfadd1/=.
    move : (mk_env_udiv_newer_cnf Hmkudiv (newer_than_lit_le_newer Htt Hnegls1) Hgadd1 (newer_than_lits_le_newer Hls2 Hnegls1)) => Hcsudiv.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer Hcsudiv (pos_leb_trans Hnewxorr Hnewzextr))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) (newer_than_cnf_le_newer Hcsudiv Hnewxorr)).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxorr) Hcsudiv) Hcnfudiv.
    move : (mk_env_zeroextend_newer_cnf Hmkzextr (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 (pos_leb_trans Hnewudiv Hnewxorr))) (newer_than_lits_le_newer Hnewmsl Hggxorr)) => Hcszextr.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) Hcszextr) Hcnfzextr.
    move : (mk_env_xor_newer_cnf Hmkxorr (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 Hnewudiv)) Hgudiv (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnegls1 Hnewudiv))) => Hcsxorr.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer Hcsxorr Hnewzextr)).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) Hcsxorr) Hcnfxorr.
    rewrite (mk_env_add_sat Hmkaddr (newer_than_lits_le_newer Hgxorr Hnewzextr) Hgzextr (newer_than_lit_le_newer Hff (pos_leb_trans Hggxorr Hnewzextr)))//.
  - dcase (mk_env_xor E_add g_add ls2 (copy (size ls2) (splitmsl ls2).2)) => [[[[E_xor2] g_xor2] cs_xor2] rs_xor2] Hmkxor2.
    dcase (mk_env_zeroextend (size (splitmsl ls2).1) E_xor2 g_xor2 [:: (splitmsl ls2).2]) => [[[[E_zext2] g_zext2] cs_zext2] rs_zext2] Hmkzext2.
    dcase (mk_env_add E_zext2 g_zext2 rs_xor2 rs_zext2) => [[[[E_abs2] g_abs2] cs_abs2] lrs_abs2] Hmkadd2.
    dcase (mk_env_udiv E_abs2 g_abs2 rs_add lrs_abs2) => [[[[[E_udiv] g_udiv] cs_udiv] lqs_udiv]lrs_udiv] Hmkudiv.
    dcase (mk_env_xor E_udiv g_udiv lrs_udiv (copy (size ls1) (splitmsl ls1).2)) => [[[[E_xorr] g_xorr] cs_xorr] rs_xorr] Hmkxorr.
    dcase (mk_env_zeroextend (size (splitmsl ls1).1) E_xorr g_xorr [:: (splitmsl ls1).2]) => [[[[E_zextr] g_zextr] cs_zextr] rs_zextr] Hmkzextr.
    dcase (mk_env_add E_zextr g_zextr rs_xorr rs_zextr) => [[[[E_addr] g_addr] cs_addr] rs_addr] Hmkaddr.
    case => <- _ <- _ //; move => Htt Hls1 Hls2; generalize Htt; rewrite newer_than_lit_tt_ff; move => Hff.
    rewrite !interp_cnf_catrev.
    move : (mk_env_xor_newer_gen Hmkxor2) => Hnewxor2. 
    move : (mk_env_zeroextend_newer_gen Hmkzext2) => Hnewzext2.
    move : (mk_env_add_newer_gen Hmkadd2) => Hnewadd2.
    move : (mk_env_udiv_newer_gen Hmkudiv) => Hnewudiv.
    move : (mk_env_xor_newer_gen Hmkxorr) => Hnewxorr.
    move : (mk_env_zeroextend_newer_gen Hmkzextr) => Hnewzextr.
    move : (mk_env_add_newer_gen Hmkaddr) => Hnewaddr.
    have Hnewcp : (newer_than_lits g (copy (size ls1) (splitmsl ls1).2)).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls1) => [_ Hnewc].
      exact : (newer_than_lits_copy (size ls1) Hnewc).
    }
    have Hnewmsl: (newer_than_lits g [:: (splitmsl ls1).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls1) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc).
    }
    have Hnewcp2 : (newer_than_lits g (copy (size ls2) (splitmsl ls2).2)).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls2) => [_ Hnewc].
      exact : (newer_than_lits_copy (size ls2) Hnewc). 
    }
    have Hnewmsl2 : (newer_than_lits g [:: (splitmsl ls2).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls2) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc) .
    }
    move : (pos_leb_trans Hnewxor2 (pos_leb_trans Hnewzext2 Hnewadd2)) => Hnegls2.
    move : (pos_leb_trans Hnegls1 (pos_leb_trans Hnegls2 (pos_leb_trans Hnewudiv Hnewxorr))) => Hggxorr.
    move : (mk_env_xor_newer_res Hmkxor1 Htt Hls1 Hnewcp) => Hgxor1.
    move : (mk_env_zeroextend_newer_res Hmkzext1 (newer_than_lit_le_newer Htt Hnewxor1) (newer_than_lits_le_newer Hnewmsl Hnewxor1)) => Hgzext1.
    move : (mk_env_add_newer_res Hmkadd1) => Hgadd1.
    move : (mk_env_xor_newer_res Hmkxor2 (newer_than_lit_le_newer Htt Hnegls1) (newer_than_lits_le_newer Hls2 Hnegls1) (newer_than_lits_le_newer Hnewcp2 Hnegls1)) => Hgxor2.
    move : (mk_env_zeroextend_newer_res Hmkzext2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 Hnewxor2)) (newer_than_lits_le_newer Hnewmsl2 (pos_leb_trans Hnegls1 Hnewxor2))) => Hgzext2.
    move : (mk_env_add_newer_res Hmkadd2) => Hgadd2.
    move/andP : (mk_env_udiv_newer_res Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 Hnegls2)) (newer_than_lits_le_newer Hgadd1 Hnegls2) Hgadd2) => [Hgudiv _].
    move : (mk_env_xor_newer_res Hmkxorr (newer_than_lit_le_newer Htt (pos_leb_trans (pos_leb_trans Hnegls1 Hnegls2) Hnewudiv)) Hgudiv (newer_than_lits_le_newer Hnewcp (pos_leb_trans (pos_leb_trans Hnegls1 Hnegls2) Hnewudiv))) => Hgxorr.
    move : (mk_env_zeroextend_newer_res Hmkzextr (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 (pos_leb_trans Hnegls2 (pos_leb_trans Hnewudiv Hnewxorr)))) (newer_than_lits_le_newer Hnewmsl Hggxorr)) => Hgzextr.
    move : (mk_env_xor_sat Hmkxorr (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 (pos_leb_trans Hnegls2 Hnewudiv))) Hgudiv (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnegls1 (pos_leb_trans Hnegls2 Hnewudiv)))) => Hcnfxorr.
    move : (mk_env_zeroextend_sat Hmkzextr (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 (pos_leb_trans Hnegls2 (pos_leb_trans Hnewudiv Hnewxorr)))) (newer_than_lits_le_newer Hnewmsl Hggxorr)) => Hcnfzextr.
    move : (mk_env_udiv_sat Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 Hnegls2)) (newer_than_lits_le_newer Hgadd1 Hnegls2) Hgadd2) => Hcnfudiv.
    move : (mk_env_xor_newer_cnf Hmkxor1 Htt Hls1 Hnewcp) => Hcsxor1.
    move : (mk_env_xor_sat Hmkxor1 Htt Hls1 Hnewcp) => Hcnfxor1.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer Hcsxor1 (pos_leb_trans Hnewzext1 (pos_leb_trans Hnewadd1 (pos_leb_trans Hnegls2 (pos_leb_trans Hnewudiv (pos_leb_trans Hnewxorr Hnewzextr))))))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) (newer_than_cnf_le_newer Hcsxor1 (pos_leb_trans Hnewzext1 (pos_leb_trans Hnewadd1 (pos_leb_trans Hnegls2 (pos_leb_trans Hnewudiv Hnewxorr)))))).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxorr) (newer_than_cnf_le_newer Hcsxor1 (pos_leb_trans Hnewzext1 (pos_leb_trans Hnewadd1 (pos_leb_trans Hnegls2 Hnewudiv))))).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (newer_than_cnf_le_newer Hcsxor1 (pos_leb_trans Hnewzext1 (pos_leb_trans Hnewadd1 Hnegls2)))).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd2) (newer_than_cnf_le_newer Hcsxor1 (pos_leb_trans Hnewzext1 (pos_leb_trans Hnewadd1 (pos_leb_trans Hnewxor2 Hnewzext2))))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzext2) (newer_than_cnf_le_newer Hcsxor1 (pos_leb_trans Hnewzext1 (pos_leb_trans Hnewadd1 Hnewxor2)))).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxor2) (newer_than_cnf_le_newer Hcsxor1 (pos_leb_trans Hnewzext1 Hnewadd1))).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd1) (newer_than_cnf_le_newer Hcsxor1 Hnewzext1)).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzext1) Hcsxor1) Hcnfxor1.
    move : (mk_env_zeroextend_newer_cnf Hmkzext1 (newer_than_lit_le_newer Htt Hnewxor1) (newer_than_lits_le_newer Hnewmsl Hnewxor1)) => Hcszext1.
    move : (mk_env_zeroextend_sat Hmkzext1 (newer_than_lit_le_newer Htt Hnewxor1) (newer_than_lits_le_newer Hnewmsl Hnewxor1)) => Hcnfzext1.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer Hcszext1 (pos_leb_trans Hnewadd1 (pos_leb_trans Hnegls2 (pos_leb_trans Hnewudiv (pos_leb_trans Hnewxorr Hnewzextr)))))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) (newer_than_cnf_le_newer Hcszext1 (pos_leb_trans Hnewadd1 (pos_leb_trans Hnegls2 (pos_leb_trans Hnewudiv Hnewxorr))))).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxorr) (newer_than_cnf_le_newer Hcszext1 (pos_leb_trans Hnewadd1 (pos_leb_trans Hnegls2 Hnewudiv)))).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (newer_than_cnf_le_newer Hcszext1 (pos_leb_trans Hnewadd1 Hnegls2))).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd2) (newer_than_cnf_le_newer Hcszext1 (pos_leb_trans Hnewadd1 (pos_leb_trans Hnewxor2 Hnewzext2)))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzext2) (newer_than_cnf_le_newer Hcszext1 (pos_leb_trans Hnewadd1 Hnewxor2))).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxor2) (newer_than_cnf_le_newer Hcszext1 Hnewadd1)).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd1) Hcszext1) Hcnfzext1.
    move : (mk_env_add_newer_cnf Hmkadd1 (newer_than_lits_le_newer Hgxor1 Hnewzext1) Hgzext1 (newer_than_lit_le_newer Hff (pos_leb_trans Hnewxor1 Hnewzext1))) => Hcsadd1.
    move : (mk_env_add_sat Hmkadd1 (newer_than_lits_le_newer Hgxor1 Hnewzext1) Hgzext1 (newer_than_lit_le_newer Hff (pos_leb_trans Hnewxor1 Hnewzext1))) => Hcnfadd1.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer Hcsadd1 (pos_leb_trans Hnegls2 (pos_leb_trans Hnewudiv (pos_leb_trans Hnewxorr Hnewzextr))))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) (newer_than_cnf_le_newer Hcsadd1 (pos_leb_trans Hnegls2 (pos_leb_trans Hnewudiv Hnewxorr)))).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxorr) (newer_than_cnf_le_newer Hcsadd1 (pos_leb_trans Hnegls2 Hnewudiv))).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (newer_than_cnf_le_newer Hcsadd1 Hnegls2)).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd2) (newer_than_cnf_le_newer Hcsadd1 (pos_leb_trans Hnewxor2 Hnewzext2))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzext2) (newer_than_cnf_le_newer Hcsadd1 Hnewxor2)).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxor2) Hcsadd1) Hcnfadd1/=.
    move : (mk_env_udiv_newer_cnf Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 Hnegls2)) (newer_than_lits_le_newer Hgadd1 Hnegls2) Hgadd2) => Hcsudiv.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer Hcsudiv (pos_leb_trans Hnewxorr Hnewzextr))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) (newer_than_cnf_le_newer Hcsudiv Hnewxorr)).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxorr) Hcsudiv) Hcnfudiv.
    move : (mk_env_zeroextend_newer_cnf Hmkzextr (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 (pos_leb_trans Hnegls2 (pos_leb_trans Hnewudiv Hnewxorr)))) (newer_than_lits_le_newer Hnewmsl Hggxorr)) => Hcszextr.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) Hcszextr) Hcnfzextr.
    move : (mk_env_xor_newer_cnf Hmkxorr (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 (pos_leb_trans Hnegls2 Hnewudiv))) Hgudiv (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnegls1 (pos_leb_trans Hnegls2 Hnewudiv)))) => Hcsxorr.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer Hcsxorr Hnewzextr)).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) Hcsxorr) Hcnfxorr.
    rewrite (mk_env_add_sat Hmkaddr (newer_than_lits_le_newer Hgxorr Hnewzextr) Hgzextr (newer_than_lit_le_newer Hff (pos_leb_trans Hggxorr Hnewzextr))).
    move : (mk_env_xor_sat Hmkxor2 (newer_than_lit_le_newer Htt Hnegls1) (newer_than_lits_le_newer Hls2 Hnegls1) (newer_than_lits_le_newer Hnewcp2 Hnegls1)) => Hcnfxor2.
    move : (mk_env_xor_newer_cnf Hmkxor2 (newer_than_lit_le_newer Htt Hnegls1) (newer_than_lits_le_newer Hls2 Hnegls1) (newer_than_lits_le_newer Hnewcp2 Hnegls1)) => Hcsxor2.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer Hcsxor2 (pos_leb_trans Hnewzext2 (pos_leb_trans Hnewadd2 (pos_leb_trans Hnewudiv (pos_leb_trans Hnewxorr Hnewzextr)))))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) (newer_than_cnf_le_newer Hcsxor2 (pos_leb_trans Hnewzext2 (pos_leb_trans Hnewadd2 (pos_leb_trans Hnewudiv Hnewxorr))))).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxorr) (newer_than_cnf_le_newer Hcsxor2 (pos_leb_trans Hnewzext2 (pos_leb_trans Hnewadd2 Hnewudiv)))).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (newer_than_cnf_le_newer Hcsxor2 (pos_leb_trans Hnewzext2 Hnewadd2))).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd2) (newer_than_cnf_le_newer Hcsxor2 Hnewzext2)).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzext2) Hcsxor2) Hcnfxor2.
    move : (mk_env_zeroextend_newer_cnf Hmkzext2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 Hnewxor2)) (newer_than_lits_le_newer Hnewmsl2 (pos_leb_trans Hnegls1 Hnewxor2))) => Hcszext2.
    move : (mk_env_zeroextend_sat Hmkzext2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnegls1 Hnewxor2)) (newer_than_lits_le_newer Hnewmsl2 (pos_leb_trans Hnegls1 Hnewxor2))) => Hcnfzext2.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer Hcszext2 (pos_leb_trans Hnewadd2 (pos_leb_trans Hnewudiv (pos_leb_trans Hnewxorr Hnewzextr))))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) (newer_than_cnf_le_newer Hcszext2 (pos_leb_trans Hnewadd2 (pos_leb_trans Hnewudiv Hnewxorr)))).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxorr) (newer_than_cnf_le_newer Hcszext2 (pos_leb_trans Hnewadd2 Hnewudiv))).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) (newer_than_cnf_le_newer Hcszext2 Hnewadd2)).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd2) Hcszext2) Hcnfzext2.
    move : (mk_env_add_sat Hmkadd2 (newer_than_lits_le_newer Hgxor2 Hnewzext2) Hgzext2 (newer_than_lit_le_newer Hff (pos_leb_trans Hnegls1 (pos_leb_trans Hnewxor2 Hnewzext2)))) => Hcnfadd2.
    move : (mk_env_add_newer_cnf Hmkadd2 (newer_than_lits_le_newer Hgxor2 Hnewzext2) Hgzext2 (newer_than_lit_le_newer Hff (pos_leb_trans Hnegls1 (pos_leb_trans Hnewxor2 Hnewzext2)))) => Hcsadd2.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer Hcsadd2 (pos_leb_trans Hnewudiv (pos_leb_trans Hnewxorr Hnewzextr)))).
    rewrite (env_preserve_cnf (mk_env_zeroextend_preserve Hmkzextr) (newer_than_cnf_le_newer Hcsadd2 (pos_leb_trans Hnewudiv Hnewxorr))).
    rewrite (env_preserve_cnf (mk_env_xor_preserve Hmkxorr) (newer_than_cnf_le_newer Hcsadd2 Hnewudiv)).
    rewrite (env_preserve_cnf (mk_env_udiv_preserve Hmkudiv) Hcsadd2) Hcnfadd2//.
Qed.
