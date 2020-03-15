From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBConst BBXor BBEq BBZeroExtend BBNeg BBAnd BBAdd BBShl BBSub BBMul BBAshr BBUge BBUdiv .
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
       else let ws := copy (size ls_tl) ls_sign in
            let '(g_xor, cs_xor, rs_xor) := bit_blast_xor g ls ws in
            let '(g_zext, cs_zext, rs_zext) := bit_blast_zeroextend (size ls_tl) g_xor (ls_sign::nil) in 
            let '(g_add, cs_add, rs_add) := bit_blast_add g_zext rs_xor rs_zext in
            (g_add, catrev cs_xor (catrev cs_zext cs_add), rs_add).

Definition bit_blast_sdiv g ls1 ls2 : generator * cnf * word * word :=
  let (ls1_tl, ls1_sign) := eta_expand (splitmsl ls1) in
  let (ls2_tl, ls2_sign) := eta_expand (splitmsl ls2) in
  let ws1 := copy (size ls1_tl) ls1_sign in
  let '(g_abs1, cs_abs1, lrs_abs1) := bit_blast_abs g ls1 in
  let '(g_abs2, cs_abs2, lrs_abs2) := bit_blast_abs g_abs1 ls2 in
  let '(g_udiv, cs_udiv, qs_udiv, rs_udiv) := bit_blast_udiv g_abs2 lrs_abs1 lrs_abs2 in
  let '(g_negq, cs_negq, lrs_negq) := bit_blast_neg g_udiv qs_udiv in
  let '(g_negr, cs_negr, lrs_negr) := bit_blast_neg g_negq rs_udiv in
  if (ls1_sign == ls2_sign) && (ls1_sign == lit_ff) then
    (g_udiv, catrev cs_udiv (catrev cs_abs1 cs_abs2), qs_udiv, rs_udiv)
  else if (ls1_sign == ls2_sign) && (ls1_sign == lit_tt) then
         (g_negr, catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negr, qs_udiv, lrs_negr)
       else if (ls1_sign != ls2_sign) && (ls1_sign == lit_ff) then
              (g_negq, catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negq, lrs_negq, rs_udiv)
            else if (ls1_sign != ls2_sign) && (ls1_sign == lit_tt) then
                   (g_negr, catrev (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_negq) cs_negr, lrs_negq, lrs_negr)
            else 
              let '(g_eq, cs_eq, r_eq) := bit_blast_eq g_udiv (ls1_sign::nil) (ls2_sign::nil) in
              let weq := copy (size ls1_tl) r_eq in 
              let '(g_xor, cs_xor, rs_xor) := bit_blast_xor g_eq qs_udiv weq in
              let '(g_zext, cs_zext, rs_zext) := bit_blast_zeroextend (size ls1_tl) g_xor weq in
              let '(g_add, cs_add, rs_add) := bit_blast_add g_zext rs_xor rs_zext in
              let '(g_xor1, cs_xor1, rs_xor1) := bit_blast_xor g_add rs_udiv ws1 in
              let '(g_zext1, cs_zext1, rs_zext1) := bit_blast_zeroextend (size ls1_tl) g_xor1 (ls1_sign::nil) in
              let '(g_add1, cs_add1, rs_add1) := bit_blast_add g_zext1 rs_xor1 rs_zext1 in
              (g_add1, catrev (catrev (catrev (catrev (catrev (catrev (catrev (catrev (catrev cs_abs1 cs_abs2) cs_udiv) cs_eq) cs_xor) cs_zext) cs_add) cs_xor1) cs_zext1) cs_add1, rs_add, rs_add1).

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

Lemma udivB_negB_negB bs1 bs2 : 
  udivB (negB bs1) (negB bs2) = udivB bs1 bs2.
Proof.
Admitted.

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

Lemma bit_blast_sdiv_correct g ls1 ls2 g' cs qlrs rlrs E bs1 bs2 :
  bit_blast_sdiv g ls1 ls2 = (g', cs, qlrs, rlrs) ->
  size ls1 = size ls2 ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E qlrs (sdivB bs1 bs2).1 /\
  enc_bits E rlrs (sdivB bs1 bs2).2.
Proof.
  rewrite/bit_blast_sdiv /bit_blast_abs.
  dcase (bit_blast_neg g ls1) => [[[g_neg ] cs_neg] lrs_neg] Hbbneg.
  dcase (bit_blast_xor g ls1 (copy (size (splitmsl ls1).1) (splitmsl ls1).2)) => [[[g_xor ] cs_xor] lrs_xor] Hbbxor.
  dcase (bit_blast_zeroextend (size (splitmsl ls1).1) g_xor [:: (splitmsl ls1).2]) => [[[g_zext ] cs_zext] lrs_zext] Hbbzext.
  dcase (bit_blast_add g_zext lrs_xor lrs_zext) => [[[g_add] cs_add] lrs_add] Hbbadd.
  case Hls1mb1 :((splitmsl ls1).2 == lit_tt); case Hls1mb0 : ((splitmsl ls1).2 == lit_ff);
    case Hls2mb1 :((splitmsl ls2).2 == lit_tt); case Hls2mb0 : ((splitmsl ls2).2 == lit_ff);
      try (rewrite (eqP Hls1mb1) in Hls1mb0; discriminate); try (rewrite (eqP Hls2mb1) in Hls2mb0; discriminate).
  - dcase (bit_blast_neg g_neg ls2)=> [[[g_neg1 ] cs_neg1] lrs_neg1] Hbbneg1.
    dcase (bit_blast_udiv g_neg1 lrs_neg lrs_neg1) => [[[[g_udiv ] cs_udiv] lqs_udiv] lrs_udiv] Hbbudiv.
    dcase (bit_blast_neg g_udiv lqs_udiv) => [[[g_neg2 ] cs_neg2] lrs_neg2] Hbbneg2.
    dcase (bit_blast_neg g_neg2 lrs_udiv) => [[[g_neg3 ] cs_neg3] lrs_neg3] Hbbneg3.
    rewrite (eqP Hls1mb1) (eqP Hls2mb1) eq_refl/=.
    case => _ <- <- <-. move => Hsz12 Henc1 Henc2.
    rewrite 3!add_prelude_catrev. move/andP => [Hcsu Hcsneg3]. move/andP : Hcsu => [Hcsneg Hcsu].
    move/andP : Hcsneg => [Hcsneg Hcsneg1].
    rewrite/sdivB.
    move : (add_prelude_tt Hcsu) => Htt. 
    move : (enc_bit_msb Htt Henc1). rewrite/msl (eqP Hls1mb1). move => Hencmsb1.
    move : (add_prelude_enc_bit_true (msb bs1) Hcsu). rewrite Hencmsb1. move => Hmsb1t.
    move : (enc_bit_msb Htt Henc2). rewrite/msl (eqP Hls2mb1). move => Hencmsb2.
    move : (add_prelude_enc_bit_true (msb bs2) Hcsu). rewrite Hencmsb2. move => Hmsb2t.
    rewrite /absB -Hmsb1t -Hmsb2t/=. 
    move : (bit_blast_neg_correct Hbbneg Henc1 Hcsneg) => Hencneg.
    move : (bit_blast_neg_correct Hbbneg1 Henc2 Hcsneg1) => Hencneg1.
    move : (bit_blast_udiv_correct Hbbudiv Hencneg Hencneg1 Hcsu) => [Hencuq Hencur].
    move : (bit_blast_neg_correct Hbbneg3 Hencur Hcsneg3).
    rewrite udivB_negB_negB. move => Hencneg3.
    rewrite udivB_negB_negB in Hencuq. by rewrite Hencuq Hencneg3.
  - dcase (bit_blast_udiv g_neg lrs_neg ls2) => [[[[g_udiv ] cs_udiv] lqs_udiv] lrs_udiv] Hbbudiv.
    dcase (bit_blast_neg g_udiv lqs_udiv) => [[[g_neg2 ] cs_neg2] lrs_neg2] Hbbneg2.
    dcase (bit_blast_neg g_neg2 lrs_udiv) => [[[g_neg3 ] cs_neg3] lrs_neg3] Hbbneg3.
    rewrite (eqP Hls1mb1) (eqP Hls2mb0) /=.
    case => _ <- <- <-. move => Hsz12 Henc1 Henc2.
    rewrite 4!add_prelude_catrev. move/andP => [Hcsu Hcsneg3]. move/andP : Hcsu => [Hcsneg Hcsneg2].
    move/andP : Hcsneg => [Hcsneg Hcsu]. move/andP : Hcsneg => [Hcsneg Hcsnil].
    rewrite/sdivB.
    move : (add_prelude_tt Hcsu) => Htt. 
    move : (enc_bit_msb Htt Henc1). rewrite/msl (eqP Hls1mb1). move => Hencmsb1.
    move : (add_prelude_enc_bit_true (msb bs1) Hcsu). rewrite Hencmsb1. move => Hmsb1t.
    move : (enc_bit_msb Htt Henc2). rewrite/msl (eqP Hls2mb0). move => Hencmsb2.
    move : (add_prelude_enc_bit_is_not_true (msb bs2) Hcsu). rewrite Hencmsb2. move => Hmsb2f.
    symmetry in Hmsb2f. rewrite->Bool.negb_true_iff in Hmsb2f.
    rewrite /absB -Hmsb1t Hmsb2f/=.
    move : (bit_blast_neg_correct Hbbneg Henc1 Hcsneg) => Hencneg.
    move : (bit_blast_udiv_correct Hbbudiv Hencneg Henc2 Hcsu) => [Hencuq Hencur].
    move : (bit_blast_neg_correct Hbbneg2 Hencuq Hcsneg2) => Hencneg2.
    move : (bit_blast_neg_correct Hbbneg3 Hencur Hcsneg3) => Hencneg3.
    by rewrite Hencneg2 Hencneg3.
  - rewrite !andbF !andbT (eqP Hls1mb1) eq_sym Hls2mb1 (lock splitmsl) /= -lock. 
    dcase (bit_blast_xor g_neg ls2 (copy (size (splitmsl ls2).1) (splitmsl ls2).2))=> [[[g_xor1 ] cs_xor1] lrs_xor1] Hbbxor1.
    dcase (bit_blast_add g_xor1 lrs_xor1 ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff))=>[[[g_add1 ] cs_add1] lrs_add1] Hbbadd1.
    dcase (bit_blast_udiv g_add1 lrs_neg lrs_add1)=>[[[[g_udiv1] cs_udiv1] lqs_udiv1] lrs_udiv1] Hbbudiv1.
    dcase (bit_blast_neg g_udiv1 lqs_udiv1)=>[[[g_neg1] cs_neg1] lrs_neg1] Hbbneg1.
    dcase (bit_blast_neg g_neg1 lrs_udiv1) =>[[[g_neg2] cs_neg2] lrs_neg2] Hbbneg2.
    case => _ <- <- <-. move => Hsz12 Henc1 Henc2.
    rewrite 5!add_prelude_catrev. move/andP => [Hcsu Hcsneg2]. move/andP : Hcsu => [Hcsneg Hcsneg1].
    move/andP : Hcsneg => [Hcsneg Hcsu]. move/andP : Hcsneg => [Hcsneg Hcsxor].
    move/andP : Hcsxor => [Hcsxor1 Hcsadd1].
    rewrite /sdivB.
    move : (add_prelude_tt Hcsu) => Htt. 
    move : (add_prelude_ff Hcsu) => Hff. 
    move : (enc_bit_msb Htt Henc1). rewrite/msl (eqP Hls1mb1). move => Hencmsb1.
    move : (add_prelude_enc_bit_true (msb bs1) Hcsu). rewrite Hencmsb1. move => Hmsb1t.
    rewrite /absB -Hmsb1t andbT /= !andbF eq_sym.
    case Hmsb2 : (msb bs2). rewrite /= udivB_negB_negB. 
    move : (bit_blast_neg_correct Hbbneg Henc1 Hcsneg) => Hencnegbs1.
    move : (enc_bits_size Henc2) => Hsz2.
    have Hencmsl2 : enc_bit E (splitmsl ls2).2 (splitmsb bs2).2 by rewrite (enc_bit_msb Htt Henc2).
    have Henccp2 : enc_bits E (copy (size (splitmsl ls2).1) (splitmsl ls2).2) (copy (size (splitmsb bs2).1) (splitmsb bs2).2) by rewrite size_splitmsb size_splitmsl -Hsz2 (enc_bits_copy (size ls2 - 1) Hencmsl2).
    move : (bit_blast_xor_correct Hbbxor1 Henc2 Henccp2 Hcsxor1).
    move : (add_prelude_enc_bit_ff Hcsu) => Hencff.
    have Henccp1 : enc_bits E ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff) ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0) by rewrite enc_bits_cons Hencmsl2 size_splitmsb size_splitmsl Hsz2 (enc_bits_copy _ Hencff). 
    have -> : (splitmsb bs2).2 = msb bs2 by done. rewrite Hmsb2 size_splitmsb.
    move => Hencxor1.
    have Haddr : (((bs2 ^# copy (size bs2 - 1) true)%bits +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))%bits = ((bs2 ^# copy (size bs2 - 1) true)%bits +# ((splitmsb bs2).2 :: copy (size (splitmsb bs2).1) b0))%bits) by done.
    have Hszadd1 : size lrs_xor1 = size ((splitmsl ls2).2 :: copy (size (splitmsl ls2).1) lit_ff). rewrite size_splitmsl/= size_nseq -addn1 subnK. admit. admit.
    move : (bit_blast_add_correct Hbbadd1 Hencxor1 Henccp1 Haddr Hcsadd1 Hszadd1) => Hencadd1.
Admitted.    
(*
    
    dcase (bit_blast_zeroextend (size (splitmsl ls2).1) g_xor1 [:: (splitmsl ls2).2])=> [[[g_zext1 ] cs_zext1] lrs_zext1] Hbbzext1.

    
    dcase (bit_blast_add g_zext1 lrs_xor1 lrs_zext1) =>[[[g_add1 ] cs_add1] lrs_add1] Hbbadd1.
    dcase (bit_blast_udiv g_add1 lrs_neg lrs_add1)=>[[[[g_udiv1] cs_udiv1] lqs_udiv1] lrs_udiv1] Hbbudiv1.
    dcase (bit_blast_neg g_udiv1 lqs_udiv1 ) =>[[[g_neg1] cs_neg1] lrs_neg1] Hbbneg1.
    dcase (bit_blast_neg g_udiv1 lrs_udiv1) =>[[[g_neg2] cs_neg2] lrs_neg2] Hbbneg2.
    dcase (bit_blast_eq g_udiv1 [:: (splitmsl ls1).2] [:: (splitmsl ls2).2])=>[[[g_eq] cs_eq] lrs_eq] Hbbeq.
    dcase (bit_blast_xor g_eq lqs_udiv1 (copy (size (splitmsl ls1).1) lrs_eq)) =>[[[g_xor2] cs_xor2] lrs_xor2] Hbbxor2.
    dcase (bit_blast_zeroextend (size (splitmsl ls1).1) g_xor2 (copy (size (splitmsl ls1).1) lrs_eq))=> [[[g_zext2 ] cs_zext2] lrs_zext2] Hbbzext2.
    dcase (bit_blast_add g_zext2 lrs_xor2 lrs_zext2)=>[[[g_add2] cs_add2] lrs_add2] Hbbadd2.
    dcase (bit_blast_xor g_add2 lrs_udiv1 (copy (size (splitmsl ls1).1) (splitmsl ls1).2)) =>[[[g_xor3] cs_xor3] lrs_xor3] Hbbxor3.
    dcase (bit_blast_zeroextend (size (splitmsl ls1).1) g_xor3 [:: (splitmsl ls1).2]) => [[[g_zext3 ] cs_zext3] lrs_zext3] Hbbzext3.
    dcase (bit_blast_add g_zext3 lrs_xor3 lrs_zext3) =>[[[g_add3] cs_add3] lrs_add3] Hbbadd3.
    case Hmsbeq : ((splitmsl ls1).2 == (splitmsl ls2).2); last case Hmsbneq : ((splitmsl ls1).2 != (splitmsl ls2).2).
    
*)