From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBConst BBXor BBEq BBZeroExtend BBNeg BBAnd BBAdd BBShl BBSub BBMul BBAshr BBUge BBUdiv BBLneg.
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_sdiv ===== *)
Definition absB bs :=
  if msb bs then negB bs else bs.

Definition sdivB bs1' bs2' : bits * bits :=
  let bs1 := absB bs1' in let bs2 := absB bs2' in
  if (msb bs1' == msb bs2') && negb (msb bs1') then udivB bs1 bs2
  else if (msb bs1' == msb bs2') && (msb bs1') then ((udivB bs1 bs2).1, negB (udivB bs1 bs2).2)
       else if (msb bs1' != msb bs2') && negb (msb bs1') then (negB (udivB bs1 bs2).1, (udivB bs1 bs2).2)
            else (negB (udivB bs1 bs2).1, negB (udivB bs1 bs2).2).

Definition bit_blast_abs g ls : generator * cnf * word :=
  let (ls_tl, ls_sign) := eta_expand (splitmsl ls) in
  if (ls_sign == lit_tt) then  bit_blast_neg g ls
  else if (ls_sign == lit_ff) then (g, [::], ls)
       else let ws := copy (size ls) ls_sign in
            let '(g_xor, cs_xor, rs_xor) := bit_blast_xor g ls ws in
            let '(g_zext, cs_zext, rs_zext) := bit_blast_zeroextend (size ls_tl) g_xor (ls_sign::nil) in 
            let '(g_add, cs_add, rs_add) := bit_blast_add g_zext rs_xor rs_zext in
            (g_add, catrev cs_xor (catrev cs_zext cs_add), rs_add).

Definition bit_blast_sdiv g ls1 ls2 : generator * cnf * word * word :=
  let (ls1_tl, ls1_sign) := eta_expand (splitmsl ls1) in
  let (ls2_tl, ls2_sign) := eta_expand (splitmsl ls2) in
  let ws1 := copy (size ls1) ls1_sign in
  let '(g_abs1, cs_abs1, lrs_abs1) := bit_blast_abs g ls1 in
  let '(g_abs2, cs_abs2, lrs_abs2) := bit_blast_abs g_abs1 ls2 in
  let '(g_udiv, cs_udiv, qs_udiv, rs_udiv) := bit_blast_udiv g_abs2 lrs_abs1 lrs_abs2 in
  if (ls1_sign == lit_ff) && (ls2_sign == lit_ff) then
    (g_udiv, catrev cs_udiv (catrev cs_abs1 cs_abs2), qs_udiv, rs_udiv)
  else if  (ls1_sign == lit_tt) && (ls2_sign == lit_tt) then
         let '(g_negr, cs_negr, lrs_negr) := bit_blast_neg g_udiv rs_udiv in
         (g_negr, catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negr, qs_udiv, lrs_negr)
       else if (ls1_sign == lit_ff) && (ls2_sign == lit_tt) then
              let '(g_negq, cs_negq, lrs_negq) := bit_blast_neg g_udiv qs_udiv in
              (g_negq, catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negq, lrs_negq, rs_udiv)
            else if (ls1_sign == lit_tt) && (ls2_sign == lit_ff) then
                   let '(g_negq, cs_negq, lrs_negq) := bit_blast_neg g_udiv qs_udiv in
                   let '(g_negr, cs_negr, lrs_negr) := bit_blast_neg g_negq rs_udiv in
                   (g_negr, catrev (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negq) cs_negr, lrs_negq, lrs_negr)
            else 
              let '(g_eq, cs_eq, r_eq) := bit_blast_eq g_udiv (ls1_sign::nil) (ls2_sign::nil) in
              let '(g_lneg, cs_lneg, r_lneg) := bit_blast_lneg g_eq r_eq in
              let wneq := copy (size ls1) r_lneg in 
              let '(g_xor, cs_xor, rs_xor) := bit_blast_xor g_lneg qs_udiv wneq in
              let '(g_zext, cs_zext, rs_zext) := bit_blast_zeroextend (size ls1_tl) g_xor (r_lneg::nil) in
              let '(g_add, cs_add, rs_add) := bit_blast_add g_zext rs_xor rs_zext in
              let '(g_xor1, cs_xor1, rs_xor1) := bit_blast_xor g_add rs_udiv ws1 in
              let '(g_zext1, cs_zext1, rs_zext1) := bit_blast_zeroextend (size ls1_tl) g_xor1 (ls1_sign::nil) in
              let '(g_add1, cs_add1, rs_add1) := bit_blast_add g_zext1 rs_xor1 rs_zext1 in
              (g_add1, catrev (catrev (catrev (catrev (catrev (catrev (catrev (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_eq) cs_lneg) cs_xor) cs_zext) cs_add) cs_xor1) cs_zext1) cs_add1, rs_add, rs_add1).

Definition mk_env_abs E g ls : env * generator * cnf * word :=
  let (ls_tl, ls_sign) := splitmsl ls in
  if (ls_sign == lit_tt) then  mk_env_neg E g ls
  else if (ls_sign == lit_ff) then (E, g, [::], ls)
       else let ws := copy (size ls_tl) ls_sign in
            let '(E_xor, g_xor, cs_xor, rs_xor) := mk_env_xor E g ls ws in
            let '(E_zext, g_zext, cs_zext, rs_zext) := mk_env_zeroextend (size ls_tl) E_xor g_xor (ls_sign::nil) in 
            let '(E_add, g_add, cs_add, rs_add) := mk_env_add E_zext g_zext rs_xor rs_zext in
            (E_add, g_add, catrev cs_xor (catrev cs_zext cs_add), rs_add).

Definition mk_env_sdiv E g ls1 ls2 : env * generator * cnf * word * word :=
  let (ls1_tl, ls1_sign) := splitmsl ls1 in
  let (ls2_tl, ls2_sign) := splitmsl ls2 in
  let ws1 := copy (size ls1_tl) ls1_sign in
  let '(E_abs1, g_abs1, cs_abs1, lrs_abs1) := mk_env_abs E g ls1 in
  let '(E_abs2, g_abs2, cs_abs2, lrs_abs2) := mk_env_abs E_abs1 g_abs1 ls2 in
  let '(E_udiv, g_udiv, cs_udiv, qs_udiv, rs_udiv) := mk_env_udiv E_abs2 g_abs2 lrs_abs1 lrs_abs2 in
  let '(E_negq, g_negq, cs_negq, lrs_negq) := mk_env_neg E_udiv g_udiv qs_udiv in
  let '(E_negr, g_negr, cs_negr, lrs_negr) := mk_env_neg E_udiv g_udiv rs_udiv in
  if (ls1_sign == ls2_sign) && (ls1_sign == lit_ff) then
    (E_udiv, g_udiv, catrev cs_udiv (catrev cs_abs1 cs_abs2), qs_udiv, rs_udiv)
  else if (ls1_sign == ls2_sign) && (ls1_sign == lit_tt) then
         (E_negr, g_negr, catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negr, qs_udiv, lrs_negr)
       else if (ls1_sign != ls2_sign) && (ls1_sign == lit_ff) then
              (E_negq, g_negq, catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negq, lrs_negq, rs_udiv)
            else 
              let '(E_eq, g_eq, cs_eq, r_eq) := mk_env_eq E_udiv g_udiv (ls1_sign::nil) (ls2_sign::nil) in
              let weq := copy (size ls1_tl) r_eq in 
              let '(E_xor, g_xor, cs_xor, rs_xor) := mk_env_xor E_eq g_eq qs_udiv weq in
              let '(E_zext, g_zext, cs_zext, rs_zext) := mk_env_zeroextend (size ls1_tl) E_xor g_xor weq in
              let '(E_add, g_add, cs_add, rs_add) := mk_env_add E_zext g_zext rs_xor rs_zext in
              let '(E_xor1, g_xor1, cs_xor1, rs_xor1) := mk_env_xor E_add g_add rs_udiv ws1 in
              let '(E_zext1, g_zext1, cs_zext1, rs_zext1) := mk_env_zeroextend (size ls1_tl) E_xor1 g_xor1 (ls1_sign::nil) in
              let '(E_add1, g_add1, cs_add1, rs_add1) := mk_env_add E_zext1 g_zext1 rs_xor1 rs_zext1 in
              (E_add1, g_add1, catrev (catrev (catrev (catrev (catrev (catrev (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_eq) cs_xor) cs_zext) cs_add) cs_xor1) cs_zext1) cs_add1, rs_add, rs_add1).


(*Lemma udivB_negB_negB bs1 bs2 :
  udivB (negB bs1) (negB bs2) = ((udivB bs1 bs2).1, negB (udivB bs1 bs2).2).
Proof.
Admitted.*)

Lemma msb_negB bs :
  msb (negB bs) = ~~ (msb bs).
Proof.
Admitted.


Lemma size_splitmsl ls : (size (splitmsl ls).1) = size ls -1.
Proof.
Admitted.


Lemma size_xorB bs1 bs2 : size (xorB bs1 bs2) = size bs1.
Proof.
Admitted.


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
    bit_blast_zeroextend n g l = (g', cs, lrs) -> size lrs = n.+1.
Proof.
Admitted.


Lemma xor0B n : left_id (from_nat n 0) xorB.
Proof.
Admitted.

Lemma xor1B bs :
  xorB (ones (size bs)) bs = invB bs.
Proof.
Admitted.
  
Lemma xorB_copy_case : forall b bs,
    xorB (copy (size bs) b) bs = if b then (invB bs) else bs.
Proof.
  move => [] bs.
  - by rewrite xor1B.
  - by rewrite -/(zeros (size bs)) -from_natn0 xor0B. 
Qed.

Lemma xorBC: commutative (xorB).
Proof.
  intro. rewrite/xorB. 
  elim x => [|xhd xtl IH] /=; elim => [|yhd ytl IHm] /=.
  - done.
  - rewrite /xorB /lift0 lift0n. rewrite liftn0; first done.
    intro; by rewrite Bool.xorb_false_r.
    rewrite /left_id. intros; by rewrite Bool.xorb_false_l.
  - rewrite /xorB /lift0 liftn0. rewrite lift0n; first done.
    intro; by rewrite Bool.xorb_false_l.
    rewrite /right_id. intros; by rewrite Bool.xorb_false_r.
  - by rewrite /lift0 lift_cons liftE -/lift0 (IH ytl) Bool.xorb_comm. 
Qed.


Lemma bit_blast_sdiv_correct g ls1 ls2 g' cs qlrs rlrs E bs1 bs2 :
  bit_blast_sdiv g ls1 ls2 = (g', cs, qlrs, rlrs) ->
  size ls1 = size ls2 ->
  0 < size ls2 ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E qlrs (sdivB bs1 bs2).1 /\
  enc_bits E rlrs (sdivB bs1 bs2).2.
Proof.
  rewrite/bit_blast_sdiv /bit_blast_abs.
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
    rewrite udivB_negB_negB. move => Hencneg3.
    rewrite udivB_negB_negB in Hencuq. by rewrite Hencuq Hencneg3.
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
      rewrite Hszb12 His1 -Hszb12 -{1}Hszurem (invB_size_ss ((udivB (-# bs1) (-# bs2)).2)%bits) addB1 -/(negB ((udivB (-# bs1) (-# bs2)).2)%bits) -/(negB ((udivB (-# bs1) (-# bs2)).1)%bits) udivB_negB_negB/=.
      have ->: (false :: zeros (size bs1 - 1)) = zeros (size bs1) by rewrite zeros_cons -addn1 -Hszlb1 (subnK Hsz1).
      rewrite addB0 unzip1_zip; last by rewrite size_xorB size_udivB size_zeros.
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
      rewrite addB0 unzip1_zip; last by rewrite size_zeros size_xorB size_uremB -Hszlb1 -addn1 (subnK Hsz1).
      rewrite addB0 unzip1_zip; last by rewrite size_xorB size_zeros.
      rewrite addB0 unzip1_zip; last by rewrite size_zeros size_xorB size_udivB -addn1 -Hszlb1 (subnK Hsz1).
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
      rewrite zeros_cons zext_zero (subnK Hsz1) addB0 unzip1_zip; last by rewrite size_xorB size_uremB size_addB size_xorB !size_zeros -Hszlb1 -addn1 (subnK Hsz1) minnn.
      rewrite addB0 unzip1_zip; last by rewrite size_xorB size_zeros Hszlb1.
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
      rewrite zeros_cons zext_zero (subnK Hsz1) addB0 unzip1_zip; last by rewrite size_xorB size_uremB size_addB size_xorB !size_zeros -Hszlb1 -addn1 (subnK Hsz1) minnn.
      rewrite addB0 unzip1_zip; last by rewrite size_xorB size_zeros Hszlb1.
      rewrite addB0 unzip1_zip; last by rewrite size_xorB size_udivB size_xorB size_zeros -addn1 -Hszlb1 (subnK Hsz1).
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
      rewrite zeros_cons addB0 unzip1_zip; last by rewrite size_xorB size_udivB size_negB size_zeros -addn1-Hszlb1 (subnK Hsz1).
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
      rewrite zeros_cons zext_zero (subnK Hsz1) addB0 unzip1_zip; last by rewrite size_xorB size_uremB size_addB !size_zeros -Hszlb1 -addn1 (subnK Hsz1) minnn.
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
      rewrite addB0 unzip1_zip; last by rewrite size_xorB size_uremB size_addB !size_zeros -addn1 -Hszlb1 (subnK Hsz1) minnn.
      rewrite addB0 unzip1_zip; last by rewrite size_zeros Hszlb1.
      rewrite addB0 unzip1_zip; last by rewrite size_zeros -Hszlb2 -addn1 (subnK Hsz2).
      rewrite addB0 unzip1_zip; last by rewrite size_zeros size_xorB size_udivB -addn1 -Hszlb1 (subnK Hsz1).
      have Hszurem: (size ((udivB (bs1)%bits (bs2)%bits).2)%bits) = size bs1 by rewrite size_uremB.
      have Hszudiv: (size ((udivB (bs1)%bits (bs2)%bits).1)%bits) = size bs1 by rewrite size_udivB. 
      by rewrite xorBC -{1}Hszurem -{1}Hszudiv xorB_copy_case xorBC xorB_copy_case.
Qed.
