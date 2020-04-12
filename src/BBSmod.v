From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBConst BBXor BBEq BBZeroExtend BBNeg BBAnd BBAdd BBShl BBSub BBMul BBAshr BBUge BBUdiv BBLneg BBSdiv BBOr BBNot BBNeg.
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition smodB bs1 bs2 : bits :=
  let (q_sdiv, r_sdiv) := eta_expand (sdivB bs1 bs2) in 
  if (msb bs1 == msb bs2) || (r_sdiv == (zeros (size r_sdiv))) then
    r_sdiv
  else addB r_sdiv bs2.

(* ===== bit_blast_smod ===== *)



Definition bit_blast_smod g ls1 ls2 : generator * cnf * word :=
  let (ls1_tl, ls1_sign) := eta_expand (splitmsl ls1) in
  let (ls2_tl, ls2_sign) := eta_expand (splitmsl ls2) in
  let '(g_sdiv, cs_sdiv, q_sdiv, lrs_sdiv) := bit_blast_sdiv g ls1 ls2 in
  let '(g_eq, cs_eq, r_eq) := bit_blast_eq g_sdiv (ls1_sign::nil) (ls2_sign::nil) in
  let '(g_eq2, cs_eq2, r_eq2) := bit_blast_eq g_eq lrs_sdiv (copy (size lrs_sdiv) lit_ff) in
  if (r_eq == lit_tt) || (r_eq2 == lit_tt) then
    (g_eq, catrev cs_sdiv (catrev cs_eq2 cs_eq), lrs_sdiv)
  else if (r_eq == lit_ff) && (r_eq2 == lit_ff) then
    let '(g_add, cs_add, lrs_add) := bit_blast_add g_eq2 lrs_sdiv ls2 in
    (g_add, catrev cs_sdiv (catrev cs_eq (catrev cs_eq2 cs_add)), lrs_add)
       else let '(g_or, cs_or, lrs_or) := bit_blast_or g_eq2 (copy (size ls2) r_eq) (copy (size ls2) r_eq2) in
            let '(g_not, cs_not, lrs_not) := bit_blast_not g_or lrs_or in
            let '(g_and2, cs_and2, lrs_and2) := bit_blast_and g_not ls2 lrs_not in
            let '(g_add2, cs_add2, lrs_add2) := bit_blast_add g_and2 lrs_sdiv lrs_and2 in
            (g_add2, catrev cs_sdiv (catrev cs_eq (catrev cs_eq2 (catrev cs_or (catrev cs_not (catrev cs_and2 cs_add2))))), lrs_add2).

Lemma size_sdivB : forall bs1 bs2, size (sdivB bs1 bs2).2 = size bs1.
Proof. Admitted.

Lemma or0B : forall n bs, orB (zeros n) bs = bs.
Proof. Admitted.

Lemma andB1 n : right_id (ones n) andB.
Proof. Admitted.

Lemma andB0: forall n : nat, right_zero (n) -bits of (0)%bits andB.
Proof. Admitted.

Lemma bit_blast_sdiv_size_ss g ls1 ls2 g' cs lrs_q lrs_r:
  bit_blast_sdiv g ls1 ls2 = (g', cs, lrs_q, lrs_r) ->
  size lrs_r = size ls1.
Proof. Admitted.

Lemma bit_blast_or_size_ss g ls1 ls2 g' cs lrs_r:
  bit_blast_or g ls1 ls2 = (g', cs, lrs_r) ->
  size lrs_r = size ls1.
Proof. Admitted.

Lemma or1B: forall (bs : bits), (ones (size bs) ||# bs)%bits = ones (size bs).
Proof. Admitted.

Lemma orB0: forall (n : nat) (bs : bits), (bs||# zeros n)%bits = bs.
Proof. Admitted.

Lemma bit_blast_smod_correct g ls1 ls2 g' cs rlrs E bs1 bs2 :
  bit_blast_smod g ls1 ls2 = (g', cs, rlrs) ->
  size ls1 = size ls2 ->
  0 < size ls2 ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E rlrs (smodB bs1 bs2).
Proof.
  rewrite /bit_blast_smod.
  dcase (bit_blast_sdiv g ls1 ls2) => [[[[g_sdiv] cs_sdiv] q_div] r_div] Hbbsdiv.
  dcase (bit_blast_eq g_sdiv [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[g_eq] cs_eq] r_eq] Hbbeq.
  dcase (bit_blast_eq g_eq r_div (copy (size r_div) lit_ff)) => [[[g_eq2] cs_eq2] r_eq2] Hbbeq2.
  dcase (bit_blast_add g_eq2 r_div ls2) => [[[g_add] cs_add] r_add] Hbbadd.
  dcase (bit_blast_or g_eq2 (copy (size ls2) r_eq) (copy (size ls2) r_eq2)) => [[[g_or] cs_or] lrs_or] Hbbor.
  dcase (bit_blast_not g_or lrs_or)  => [[[g_not] cs_not] lrs_not] Hbbnot.
  dcase (bit_blast_and g_not ls2 lrs_not) => [[[g_and2] cs_and2] r_and2] Hbband2.
  dcase (bit_blast_add g_and2 r_div r_and2) => [[[g_add2] cs_add2] r_add2] Hbbadd2.
  case Heq :(r_eq == lit_tt); last case Heq2 : (r_eq2 == lit_tt).
  - rewrite/=; case => _ <- <-.
    move => Hsz12 Hgt02 Henc1 Henc2.
    rewrite 2!add_prelude_catrev. move/andP => [Hcssdiv Hcsu]; move/andP : Hcsu => [Hcseq2 Hcseq].
    rewrite/smodB.
    move : (add_prelude_tt Hcssdiv) => Htt. 
    have Hszmsl12 : size [:: (splitmsl ls1).2] = size [:: (splitmsl ls2).2] by done.
    move/andP : (enc_bits_splitmsb Htt Henc1) => [Henc1r Hencmsb1].
    move/andP : (enc_bits_splitmsb Htt Henc2) => [Henc2r Hencmsb2].
    have Hencmsb1nil : enc_bits E [::(splitmsl ls1).2] [::(splitmsb bs1).2] by rewrite enc_bits_cons Hencmsb1 enc_bits_nil.
    have Hencmsb2nil : enc_bits E [::(splitmsl ls2).2] [::(splitmsb bs2).2] by rewrite enc_bits_cons Hencmsb2 enc_bits_nil.
    move : (bit_blast_eq_correct Hbbeq Hszmsl12 Hencmsb1nil Hencmsb2nil Hcseq). (*=> Henceqr.*)
    rewrite (eqP Heq). (*in Henceqr. generalize Henceqr.*)
    rewrite (add_prelude_enc_bit_true ([:: (splitmsb bs1).2] == [:: (splitmsb bs2).2]) Hcseq) Seqs.singleton_eq-/(msb bs1) -/(msb bs2).
    move => Hmsb12. rewrite Hmsb12 orTb. 
    move : (bit_blast_sdiv_correct Hbbsdiv Hsz12 Hgt02 Henc1 Henc2 Hcssdiv) => [Hencq Hencr]; done.
  - rewrite /=; case => _ <- <-. move => Hsz12 Hgt02 Henc1 Henc2.
    rewrite 2!add_prelude_catrev /smodB. move/andP => [Hcssdiv Hcsu]; move/andP : Hcsu => [Hcseq2 Hcseq].
    have Hszcprdiv : size r_div = size (copy (size r_div) lit_ff) by rewrite size_nseq.
    move : (add_prelude_enc_bit_ff Hcssdiv) => Hencff.
    move : (enc_bits_copy (size r_div) Hencff) => Henccpff.
    move : (bit_blast_sdiv_correct Hbbsdiv Hsz12 Hgt02 Henc1 Henc2 Hcssdiv) => [Hencq Hencr].
    move : (bit_blast_eq_correct Hbbeq2 Hszcprdiv Hencr Henccpff Hcseq2).
    rewrite (eqP Heq2) (add_prelude_enc_bit_true ((sdivB bs1 bs2).2 == copy (size r_div) false) Hcseq2). move => HsdivB.
    rewrite (eqP HsdivB) size_copy {1}/zeros {1}/b0 eq_refl orbT.
    rewrite (eqP HsdivB) in Hencr. done.
  - case Heqf: (r_eq == lit_ff); case Heqf2: (r_eq2 == lit_ff).
    + rewrite/=; case => _ <- <-. move => Hsz12 Hgt02 Henc1 Henc2.
      rewrite 3!add_prelude_catrev /smodB. move/andP => [Hcssdiv Hcsu]; move/andP : Hcsu => [Hcseq Hcsu]; move/andP : Hcsu => [Hcseq2 Hcsadd].
      have Hszmsl12 : size [:: (splitmsl ls1).2] = size [:: (splitmsl ls2).2] by done.
      move : (add_prelude_tt Hcssdiv) => Htt. move : (add_prelude_ff Hcssdiv) => Hff. 
      move/andP : (enc_bits_splitmsb Htt Henc1) => [Henc1r Hencmsb1].
      move/andP : (enc_bits_splitmsb Htt Henc2) => [Henc2r Hencmsb2].
      have Hencmsb1nil : enc_bits E [::(splitmsl ls1).2] [::(splitmsb bs1).2] by rewrite enc_bits_cons Hencmsb1 enc_bits_nil.
      have Hencmsb2nil : enc_bits E [::(splitmsl ls2).2] [::(splitmsb bs2).2] by rewrite enc_bits_cons Hencmsb2 enc_bits_nil.
      move : (bit_blast_eq_correct Hbbeq Hszmsl12 Hencmsb1nil Hencmsb2nil Hcseq).
      rewrite (eqP Heqf).
      rewrite (add_prelude_enc_bit_is_not_true ([:: (splitmsb bs1).2] == [:: (splitmsb bs2).2]) Hcseq) Seqs.singleton_eq-/(msb bs1) -/(msb bs2).
      move/negP/eqP/eqP => Hmsb12. move : (Bool.not_true_is_false (msb bs1 == msb bs2) Hmsb12) => Hmsb12f.
      rewrite Hmsb12f orFb.
      move : (bit_blast_sdiv_correct Hbbsdiv Hsz12 Hgt02 Henc1 Henc2 Hcssdiv) => [Hencq Hencr].
      have Hszcprdiv : size r_div = size (copy (size r_div) lit_ff) by rewrite size_nseq.
      move : (add_prelude_enc_bit_ff Hcssdiv) => Hencff.
      move : (enc_bits_copy (size r_div) Hencff) => Henccpff.
      move : (bit_blast_eq_correct Hbbeq2 Hszcprdiv Hencr Henccpff Hcseq2).
      rewrite (eqP Heqf2) (add_prelude_enc_bit_is_not_true ((sdivB bs1 bs2).2 == copy (size r_div) false) Hcseq2).
      move/negP/eqP/eqP => HsdivB. move : (Bool.not_true_is_false ((sdivB bs1 bs2).2 == copy (size r_div) false) HsdivB) => HsdivBnot0.
      move : (enc_bits_size Hencr) => Hszencr.
      rewrite -Hszencr HsdivBnot0.
      generalize Hszencr. rewrite size_sdivB -(enc_bits_size Henc1) Hsz12. move => Hszrdiv.
      have Haddr : ((addB (sdivB bs1 bs2).2 bs2) = (addB (sdivB bs1 bs2).2 bs2)) by done.
      exact : (bit_blast_add_correct Hbbadd Hencr Henc2 Haddr Hcsadd Hszrdiv).
    + rewrite/=. case => _ <- <-. move => Hsz12 Hgt02 Henc1 Henc2.
      rewrite 6!add_prelude_catrev /smodB. move/andP => [Hcssdiv Hcsu]; move/andP : Hcsu => [Hcseq Hcsu]; move/andP : Hcsu => [Hcseq2 Hcsu]; move/andP : Hcsu => [Hcsor Hcsu]; move/andP : Hcsu => [Hcsnot Hcsu]; move/andP : Hcsu => [Hcsand Hcsadd2].
      have Hszmsl12 : size [:: (splitmsl ls1).2] = size [:: (splitmsl ls2).2] by done.
      move : (add_prelude_tt Hcssdiv) => Htt. move : (add_prelude_ff Hcssdiv) => Hff. 
      move/andP : (enc_bits_splitmsb Htt Henc1) => [Henc1r Hencmsb1].
      move/andP : (enc_bits_splitmsb Htt Henc2) => [Henc2r Hencmsb2].
      have Hencmsb1nil : enc_bits E [::(splitmsl ls1).2] [::(splitmsb bs1).2] by rewrite enc_bits_cons Hencmsb1 enc_bits_nil.
      have Hencmsb2nil : enc_bits E [::(splitmsl ls2).2] [::(splitmsb bs2).2] by rewrite enc_bits_cons Hencmsb2 enc_bits_nil.
      move : (bit_blast_eq_correct Hbbeq Hszmsl12 Hencmsb1nil Hencmsb2nil Hcseq) => Henceqr.
      generalize Henceqr. rewrite (eqP Heqf).
      rewrite (add_prelude_enc_bit_is_not_true ([:: (splitmsb bs1).2] == [:: (splitmsb bs2).2]) Hcseq) Seqs.singleton_eq-/(msb bs1) -/(msb bs2).
      move/negP/eqP/eqP => Hmsb12. move : (Bool.not_true_is_false (msb bs1 == msb bs2) Hmsb12) => Hmsb12f.
      rewrite Hmsb12f orFb.
      move : (bit_blast_sdiv_correct Hbbsdiv Hsz12 Hgt02 Henc1 Henc2 Hcssdiv) => [Hencq Hencr].
      have Hszcprdiv : size r_div = size (copy (size r_div) lit_ff) by rewrite size_nseq.
      move : (add_prelude_enc_bit_ff Hcssdiv) => Hencff.
      move : (enc_bits_copy (size r_div) Hencff) => Henccpff.
      move : (bit_blast_eq_correct Hbbeq2 Hszcprdiv Hencr Henccpff Hcseq2) => Henceq2r.
      case HsdivB0: ((sdivB bs1 bs2).2 == zeros (size (sdivB bs1 bs2).2)).
      * have Hszcpeq : (size (copy (size ls2) r_eq)= size (copy (size ls2) r_eq2)) by rewrite 2!size_nseq.
        move : (bit_blast_or_correct Hbbor (enc_bits_copy (size ls2) Henceqr) (enc_bits_copy (size ls2) Henceq2r) Hcsor).
        rewrite -/(msb bs1) -/(msb bs2) Seqs.singleton_eq Hmsb12f (enc_bits_size Hencr) (eqP HsdivB0) size_sdivB size_zeros -/(zeros (size ls2)) eq_refl or0B. 
        move => Hencorr.
        move : (bit_blast_not_correct Hbbnot Hencorr Hcsnot). rewrite invB_ones. move => Hencnotr.
        move : (bit_blast_and_correct Hbband2 Henc2 Hencnotr Hcsand). rewrite (enc_bits_size Henc2) -from_natn0 andB0.
        move => Hencand2r.
        have Haddr :(addB (zeros (size (sdivB bs1 bs2).2)) ((size bs2) -bits of (0)%bits) = zeros (size bs1)).
        rewrite size_sdivB add0B unzip2_zip; first by rewrite -(enc_bits_size Henc2) -Hsz12 (enc_bits_size Henc1) from_natn0.
        by rewrite size_from_nat size_zeros -(enc_bits_size Henc2) -Hsz12 (enc_bits_size Henc1).
        rewrite -(eqP HsdivB0) in Haddr.
        move : (bit_blast_sdiv_size_ss Hbbsdiv) => Hszsdiv.
        move : (bit_blast_or_size_ss Hbbor) => Hszor. rewrite size_nseq in Hszor.
        move : (bit_blast_not_size_ss Hbbnot) => Hsznot. rewrite Hszor in Hsznot.
        move : (bit_blast_and_size_ss Hbband2 Hsznot) => Hszand2. rewrite -Hsz12 -Hszsdiv in Hszand2.
        exact : (bit_blast_add_correct Hbbadd2 Hencr Hencand2r Haddr Hcsadd2 Hszand2).
      * have Hszcpeq : (size (copy (size ls2) r_eq)= size (copy (size ls2) r_eq2)) by rewrite 2!size_nseq.
        move : (bit_blast_or_correct Hbbor (enc_bits_copy (size ls2) Henceqr) (enc_bits_copy (size ls2) Henceq2r) Hcsor).
        rewrite -/(msb bs1) -/(msb bs2) Seqs.singleton_eq Hmsb12f (enc_bits_size Hencr) HsdivB0 -/(zeros (size ls2)) or0B. 
        move => Hencorr.
        move : (bit_blast_not_correct Hbbnot Hencorr Hcsnot). rewrite invB_zeros. move => Hencnotr.
        move : (bit_blast_and_correct Hbband2 Henc2 Hencnotr Hcsand). rewrite (enc_bits_size Henc2) andB1.
        move => Hencand2r.
        have Haddr :(addB  (sdivB bs1 bs2).2 bs2 = addB  (sdivB bs1 bs2).2 bs2) by done.
        move : (bit_blast_sdiv_size_ss Hbbsdiv) => Hszsdiv.
        move : (bit_blast_or_size_ss Hbbor) => Hszor. rewrite size_nseq in Hszor.
        move : (bit_blast_not_size_ss Hbbnot) => Hsznot. rewrite Hszor in Hsznot.
        move : (bit_blast_and_size_ss Hbband2 Hsznot) => Hszand2. rewrite -Hsz12 -Hszsdiv in Hszand2.
        exact : (bit_blast_add_correct Hbbadd2 Hencr Hencand2r Haddr Hcsadd2 Hszand2).
    + rewrite /=. case => _ <- <-. move => Hsz12 Hgt02 Henc1 Henc2.
      rewrite 6!add_prelude_catrev /smodB. move/andP => [Hcssdiv Hcsu]; move/andP : Hcsu => [Hcseq Hcsu]; move/andP : Hcsu => [Hcseq2 Hcsu]; move/andP : Hcsu => [Hcsor Hcsu]; move/andP : Hcsu => [Hcsnot Hcsu]; move/andP : Hcsu => [Hcsand Hcsadd2].
      have Hszmsl12 : size [:: (splitmsl ls1).2] = size [:: (splitmsl ls2).2] by done.
      move : (add_prelude_tt Hcssdiv) => Htt. move : (add_prelude_ff Hcssdiv) => Hff. 
      move/andP : (enc_bits_splitmsb Htt Henc1) => [Henc1r Hencmsb1].
      move/andP : (enc_bits_splitmsb Htt Henc2) => [Henc2r Hencmsb2].
      have Hencmsb1nil : enc_bits E [::(splitmsl ls1).2] [::(splitmsb bs1).2] by rewrite enc_bits_cons Hencmsb1 enc_bits_nil.
      have Hencmsb2nil : enc_bits E [::(splitmsl ls2).2] [::(splitmsb bs2).2] by rewrite enc_bits_cons Hencmsb2 enc_bits_nil.
      move : (bit_blast_eq_correct Hbbeq Hszmsl12 Hencmsb1nil Hencmsb2nil Hcseq) => Henceqr.
      have Hszcprdiv : size r_div = size (copy (size r_div) lit_ff) by rewrite size_nseq.
      move : (add_prelude_enc_bit_ff Hcssdiv) => Hencff.
      move : (enc_bits_copy (size r_div) Hencff) => Henccpff.
      move : (bit_blast_sdiv_correct Hbbsdiv Hsz12 Hgt02 Henc1 Henc2 Hcssdiv) => [Hencq Hencr].
      move : (bit_blast_eq_correct Hbbeq2 Hszcprdiv Hencr Henccpff Hcseq2) => Henceq2r.
      generalize Henceq2r.
      rewrite (eqP Heqf2) (add_prelude_enc_bit_is_not_true ((sdivB bs1 bs2).2 == copy (size r_div) false) Hcseq2). move => HsdivB.
      generalize HsdivB.
      move/negP/eqP/eqP => HsdivB0. move : (Bool.not_true_is_false ((sdivB bs1 bs2).2 == copy (size r_div) false) HsdivB0) => HsdivB0f. rewrite (enc_bits_size Hencr) -/(zeros (size (sdivB bs1 bs2).2)) in HsdivB0f.
      rewrite HsdivB0f orbF.
      case Hmsbeq : (msb bs1 == msb bs2).
      * have Hszcpeq : (size (copy (size ls2) r_eq)= size (copy (size ls2) r_eq2)) by rewrite 2!size_nseq.
        move : (bit_blast_or_correct Hbbor (enc_bits_copy (size ls2) Henceqr) (enc_bits_copy (size ls2) Henceq2r) Hcsor).
        rewrite -/(msb bs1) -/(msb bs2) Seqs.singleton_eq Hmsbeq (enc_bits_size Hencr) HsdivB0f orB0.
        move => Hencorr.
        move : (bit_blast_not_correct Hbbnot Hencorr Hcsnot). rewrite invB_ones. move => Hencnotr.
        move : (bit_blast_and_correct Hbband2 Henc2 Hencnotr Hcsand). rewrite (enc_bits_size Henc2) -from_natn0 andB0.
        move => Hencand2r.
        have Haddr :(addB  (sdivB bs1 bs2).2 ((size bs2) -bits of (0)%bits) = (sdivB bs1 bs2).2).
        rewrite from_natn0 addB0 unzip1_zip; first done.
        by rewrite size_sdivB size_zeros -(enc_bits_size Henc2)-Hsz12 (enc_bits_size Henc1).
        move : (bit_blast_sdiv_size_ss Hbbsdiv) => Hszsdiv.
        move : (bit_blast_or_size_ss Hbbor) => Hszor. rewrite size_nseq in Hszor.
        move : (bit_blast_not_size_ss Hbbnot) => Hsznot. rewrite Hszor in Hsznot.
        move : (bit_blast_and_size_ss Hbband2 Hsznot) => Hszand2. rewrite -Hsz12 -Hszsdiv in Hszand2.
        exact : (bit_blast_add_correct Hbbadd2 Hencr Hencand2r Haddr Hcsadd2 Hszand2).
      * have Hszcpeq : (size (copy (size ls2) r_eq)= size (copy (size ls2) r_eq2)) by rewrite 2!size_nseq.
        move : (bit_blast_or_correct Hbbor (enc_bits_copy (size ls2) Henceqr) (enc_bits_copy (size ls2) Henceq2r) Hcsor).
        rewrite -/(msb bs1) -/(msb bs2) Seqs.singleton_eq Hmsbeq (enc_bits_size Hencr) HsdivB0f  orB0.
        move => Hencorr.
        move : (bit_blast_not_correct Hbbnot Hencorr Hcsnot). rewrite invB_zeros. move => Hencnotr.
        move : (bit_blast_and_correct Hbband2 Henc2 Hencnotr Hcsand). rewrite (enc_bits_size Henc2) andB1.
        move => Hencand2r.
        have Haddr :(addB  (sdivB bs1 bs2).2 bs2 = addB (sdivB bs1 bs2).2 bs2) by done.
        move : (bit_blast_sdiv_size_ss Hbbsdiv) => Hszsdiv.
        move : (bit_blast_or_size_ss Hbbor) => Hszor. rewrite size_nseq in Hszor.
        move : (bit_blast_not_size_ss Hbbnot) => Hsznot. rewrite Hszor in Hsznot.
        move : (bit_blast_and_size_ss Hbband2 Hsznot) => Hszand2. rewrite -Hsz12 -Hszsdiv in Hszand2.
        exact : (bit_blast_add_correct Hbbadd2 Hencr Hencand2r Haddr Hcsadd2 Hszand2).
    + rewrite /=. case => _ <- <-. move => Hsz12 Hgt02 Henc1 Henc2.
      rewrite 6!add_prelude_catrev /smodB. move/andP => [Hcssdiv Hcsu]; move/andP : Hcsu => [Hcseq Hcsu]; move/andP : Hcsu => [Hcseq2 Hcsu]; move/andP : Hcsu => [Hcsor Hcsu]; move/andP : Hcsu => [Hcsnot Hcsu]; move/andP : Hcsu => [Hcsand Hcsadd2].
      have Hszmsl12 : size [:: (splitmsl ls1).2] = size [:: (splitmsl ls2).2] by done.
      move : (add_prelude_tt Hcssdiv) => Htt. move : (add_prelude_ff Hcssdiv) => Hff. 
      move/andP : (enc_bits_splitmsb Htt Henc1) => [Henc1r Hencmsb1].
      move/andP : (enc_bits_splitmsb Htt Henc2) => [Henc2r Hencmsb2].
      have Hencmsb1nil : enc_bits E [::(splitmsl ls1).2] [::(splitmsb bs1).2] by rewrite enc_bits_cons Hencmsb1 enc_bits_nil.
      have Hencmsb2nil : enc_bits E [::(splitmsl ls2).2] [::(splitmsb bs2).2] by rewrite enc_bits_cons Hencmsb2 enc_bits_nil.
      move : (bit_blast_eq_correct Hbbeq Hszmsl12 Hencmsb1nil Hencmsb2nil Hcseq) => Henceqr.
      have Hszcprdiv : size r_div = size (copy (size r_div) lit_ff) by rewrite size_nseq.
      move : (add_prelude_enc_bit_ff Hcssdiv) => Hencff.
      move : (enc_bits_copy (size r_div) Hencff) => Henccpff.
      move : (bit_blast_sdiv_correct Hbbsdiv Hsz12 Hgt02 Henc1 Henc2 Hcssdiv) => [Hencq Hencr].
      move : (bit_blast_eq_correct Hbbeq2 Hszcprdiv Hencr Henccpff Hcseq2) => Henceq2r.
      case Hmsbeq : (msb bs1 == msb bs2); last case Hmsbeq2 : ((sdivB bs1 bs2).2 == zeros (size (sdivB bs1 bs2).2)).
      * rewrite/=.
        have Hszcpeq : (size (copy (size ls2) r_eq)= size (copy (size ls2) r_eq2)) by rewrite 2!size_nseq.
        move : (bit_blast_or_correct Hbbor (enc_bits_copy (size ls2) Henceqr) (enc_bits_copy (size ls2) Henceq2r) Hcsor).
        have {1}-> :(size ls2 = size (copy (size ls2) ((sdivB bs1 bs2).2 == copy (size r_div) false))) by rewrite size_nseq.
        rewrite -/(msb bs1) -/(msb bs2) Seqs.singleton_eq Hmsbeq (enc_bits_size Hencr).
        rewrite -/b1 -/(ones (size (copy (size ls2) ((sdivB bs1 bs2).2 == copy (size (sdivB bs1 bs2).2) false)))) or1B size_nseq.
        move => Hencorr.
        move : (bit_blast_not_correct Hbbnot Hencorr Hcsnot). rewrite invB_ones. move => Hencnotr.
        move : (bit_blast_and_correct Hbband2 Henc2 Hencnotr Hcsand). rewrite (enc_bits_size Henc2) -from_natn0 andB0.
        move => Hencand2r.
        have Haddr :(addB  (sdivB bs1 bs2).2 ((size bs2) -bits of (0)%bits) = (sdivB bs1 bs2).2).
        rewrite from_natn0 addB0 unzip1_zip; first done.
        by rewrite size_sdivB size_zeros -(enc_bits_size Henc2)-Hsz12 (enc_bits_size Henc1).
        move : (bit_blast_sdiv_size_ss Hbbsdiv) => Hszsdiv.
        move : (bit_blast_or_size_ss Hbbor) => Hszor. rewrite size_nseq in Hszor.
        move : (bit_blast_not_size_ss Hbbnot) => Hsznot. rewrite Hszor in Hsznot.
        move : (bit_blast_and_size_ss Hbband2 Hsznot) => Hszand2. rewrite -Hsz12 -Hszsdiv in Hszand2.
        exact : (bit_blast_add_correct Hbbadd2 Hencr Hencand2r Haddr Hcsadd2 Hszand2).
      * rewrite/=.
        have Hszcpeq : (size (copy (size ls2) r_eq)= size (copy (size ls2) r_eq2)) by rewrite 2!size_nseq.
        move : (bit_blast_or_correct Hbbor (enc_bits_copy (size ls2) Henceqr) (enc_bits_copy (size ls2) Henceq2r) Hcsor).
        rewrite -/(msb bs1) -/(msb bs2) Seqs.singleton_eq Hmsbeq (enc_bits_size Hencr).
        rewrite /zeros in Hmsbeq2. rewrite Hmsbeq2 -/b0 -/(zeros (size ls2)) or0B -/b1 -/(ones (size ls2)). 
        move => Hencorr.
        move : (bit_blast_not_correct Hbbnot Hencorr Hcsnot). rewrite invB_ones. move => Hencnotr.
        move : (bit_blast_and_correct Hbband2 Henc2 Hencnotr Hcsand). rewrite (enc_bits_size Henc2) -from_natn0 andB0.
        move => Hencand2r.
        have Haddr :(addB  (sdivB bs1 bs2).2 ((size bs2) -bits of (0)%bits) = (sdivB bs1 bs2).2).
        rewrite from_natn0 addB0 unzip1_zip; first done.
        by rewrite size_sdivB size_zeros -(enc_bits_size Henc2)-Hsz12 (enc_bits_size Henc1).
        move : (bit_blast_sdiv_size_ss Hbbsdiv) => Hszsdiv.
        move : (bit_blast_or_size_ss Hbbor) => Hszor. rewrite size_nseq in Hszor.
        move : (bit_blast_not_size_ss Hbbnot) => Hsznot. rewrite Hszor in Hsznot.
        move : (bit_blast_and_size_ss Hbband2 Hsznot) => Hszand2. rewrite -Hsz12 -Hszsdiv in Hszand2.
        exact : (bit_blast_add_correct Hbbadd2 Hencr Hencand2r Haddr Hcsadd2 Hszand2).
      * rewrite/=.
        have Hszcpeq : (size (copy (size ls2) r_eq)= size (copy (size ls2) r_eq2)) by rewrite 2!size_nseq.
        move : (bit_blast_or_correct Hbbor (enc_bits_copy (size ls2) Henceqr) (enc_bits_copy (size ls2) Henceq2r) Hcsor).
        rewrite -/(msb bs1) -/(msb bs2) Seqs.singleton_eq Hmsbeq (enc_bits_size Hencr) Hmsbeq2 orB0.
        move => Hencorr.
        move : (bit_blast_not_correct Hbbnot Hencorr Hcsnot). rewrite invB_zeros. move => Hencnotr.
        move : (bit_blast_and_correct Hbband2 Henc2 Hencnotr Hcsand). rewrite (enc_bits_size Henc2) andB1.
        move => Hencand2r.
        have Haddr :(addB  (sdivB bs1 bs2).2 bs2 = addB (sdivB bs1 bs2).2 bs2) by done.
        move : (bit_blast_sdiv_size_ss Hbbsdiv) => Hszsdiv.
        move : (bit_blast_or_size_ss Hbbor) => Hszor. rewrite size_nseq in Hszor.
        move : (bit_blast_not_size_ss Hbbnot) => Hsznot. rewrite Hszor in Hsznot.
        move : (bit_blast_and_size_ss Hbband2 Hsznot) => Hszand2. rewrite -Hsz12 -Hszsdiv in Hszand2.
        exact : (bit_blast_add_correct Hbbadd2 Hencr Hencand2r Haddr Hcsadd2 Hszand2).
Qed.


  