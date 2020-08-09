From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBConst BBXor BBEq BBZeroExtend BBNeg BBAnd BBAdd BBShl BBSub BBMul BBAshr BBUge BBUdiv BBLneg BBSdiv BBOr BBNot BBNeg.
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition smodB bs1 bs2 : bits :=
  let r_sdiv := sremB bs1 bs2 in 
  if (msb bs1 == msb bs2) || (r_sdiv == (zeros (size r_sdiv))) then
    r_sdiv
  else addB r_sdiv bs2.

(* ===== bit_blast_smod ===== *)

Definition bit_blast_smod g ls1 ls2 : generator * cnf * word :=
  let (ls1_tl, ls1_sign) := eta_expand (splitmsl ls1) in
  let (ls2_tl, ls2_sign) := eta_expand (splitmsl ls2) in
  let '(g_srem, cs_srem, lrs_srem) := bit_blast_srem g ls1 ls2 in
  let '(g_eq, cs_eq, r_eq) := bit_blast_eq g_srem (ls1_sign::nil) (ls2_sign::nil) in
  let '(g_eq2, cs_eq2, r_eq2) := bit_blast_eq g_eq lrs_srem (copy (size lrs_srem) lit_ff) in
  if (r_eq == lit_tt) || (r_eq2 == lit_tt) then
    (g_eq, catrev cs_srem (catrev cs_eq2 cs_eq), lrs_srem)
  else if (r_eq == lit_ff) && (r_eq2 == lit_ff) then
    let '(g_add, cs_add, lrs_add) := bit_blast_add g_eq2 lrs_srem ls2 in
    (g_add, catrev cs_srem (catrev cs_eq (catrev cs_eq2 cs_add)), lrs_add)
       else let '(g_or, cs_or, lrs_or) := bit_blast_or g_eq2 (copy (size ls2) r_eq) (copy (size ls2) r_eq2) in
            let '(g_not, cs_not, lrs_not) := bit_blast_not g_or lrs_or in
            let '(g_and2, cs_and2, lrs_and2) := bit_blast_and g_not ls2 lrs_not in
            let '(g_add2, cs_add2, lrs_add2) := bit_blast_add g_and2 lrs_srem lrs_and2 in
            (g_add2, catrev cs_srem (catrev cs_eq (catrev cs_eq2 (catrev cs_or (catrev cs_not (catrev cs_and2 cs_add2))))), lrs_add2).

Lemma size_sremB : forall bs1 bs2, size (sremB bs1 bs2) = size bs1.
Proof.
  intros. rewrite /sremB /absB.
  case (msb bs1); case (msb bs2); try rewrite size_negB size_uremB size_negB//;
                                      try rewrite size_uremB//.
Qed.

Lemma bit_blast_srem_size_ss g ls1 ls2 g' cs lrs_r:
  bit_blast_srem g ls1 ls2 = (g', cs, lrs_r) ->
  size lrs_r = size ls1.
Proof. Admitted.

Lemma bit_blast_or_size_ss g ls1 ls2 g' cs lrs_r:
  bit_blast_or g ls1 ls2 = (g', cs, lrs_r) ->
  size lrs_r = size ls1.
Proof. Admitted.

(*
Lemma or1B: forall (bs : bits), (ones (size bs) ||# bs)%bits = ones (size bs).
Proof. Admitted.

Lemma orB0: forall (n : nat) (bs : bits), (bs||# zeros n)%bits = bs.
Proof. Admitted.
 *)

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
  dcase (bit_blast_srem g ls1 ls2) => [[[g_srem] cs_srem] r_rem] Hbbsrem.
  dcase (bit_blast_eq g_srem [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[g_eq] cs_eq] r_eq] Hbbeq.
  dcase (bit_blast_eq g_eq r_rem (copy (size r_rem) lit_ff)) => [[[g_eq2] cs_eq2] r_eq2] Hbbeq2.
  dcase (bit_blast_add g_eq2 r_rem ls2) => [[[g_add] cs_add] r_add] Hbbadd.
  dcase (bit_blast_or g_eq2 (copy (size ls2) r_eq) (copy (size ls2) r_eq2)) => [[[g_or] cs_or] lrs_or] Hbbor.
  dcase (bit_blast_not g_or lrs_or)  => [[[g_not] cs_not] lrs_not] Hbbnot.
  dcase (bit_blast_and g_not ls2 lrs_not) => [[[g_and2] cs_and2] r_and2] Hbband2.
  dcase (bit_blast_add g_and2 r_rem r_and2) => [[[g_add2] cs_add2] r_add2] Hbbadd2.
  case Heq :(r_eq == lit_tt); last case Heq2 : (r_eq2 == lit_tt).
  - rewrite/=; case => _ <- <-.
    move => Hsz12 Hgt02 Henc1 Henc2.
    rewrite 2!add_prelude_catrev. move/andP => [Hcssrem Hcsu]; move/andP : Hcsu => [Hcseq2 Hcseq].
    rewrite/smodB.
    move : (add_prelude_tt Hcssrem) => Htt. 
    have Hszmsl12 : size [:: (splitmsl ls1).2] = size [:: (splitmsl ls2).2] by done.
    move/andP : (enc_bits_splitmsb Htt Henc1) => [Henc1r Hencmsb1].
    move/andP : (enc_bits_splitmsb Htt Henc2) => [Henc2r Hencmsb2].
    have Hencmsb1nil : enc_bits E [::(splitmsl ls1).2] [::(splitmsb bs1).2] by rewrite enc_bits_cons Hencmsb1 enc_bits_nil.
    have Hencmsb2nil : enc_bits E [::(splitmsl ls2).2] [::(splitmsb bs2).2] by rewrite enc_bits_cons Hencmsb2 enc_bits_nil.
    move : (bit_blast_eq_correct Hbbeq Hszmsl12 Hencmsb1nil Hencmsb2nil Hcseq). (*=> Henceqr.*)
    rewrite (eqP Heq). (*in Henceqr. generalize Henceqr.*)
    rewrite (add_prelude_enc_bit_true ([:: (splitmsb bs1).2] == [:: (splitmsb bs2).2]) Hcseq) Seqs.singleton_eq-/(msb bs1) -/(msb bs2).
    move => Hmsb12. rewrite Hmsb12 orTb. 
    move : (bit_blast_srem_correct Hbbsrem Hsz12 Hgt02 Henc1 Henc2 Hcssrem) => Hencr; done.
  - rewrite /=; case => _ <- <-. move => Hsz12 Hgt02 Henc1 Henc2.
    rewrite 2!add_prelude_catrev /smodB. move/andP => [Hcssrem Hcsu]; move/andP : Hcsu => [Hcseq2 Hcseq].
    have Hszcprrem : size r_rem = size (copy (size r_rem) lit_ff) by rewrite size_nseq.
    move : (add_prelude_enc_bit_ff Hcssrem) => Hencff.
    move : (enc_bits_copy (size r_rem) Hencff) => Henccpff.
    move : (bit_blast_srem_correct Hbbsrem Hsz12 Hgt02 Henc1 Henc2 Hcssrem) => Hencr.
    move : (bit_blast_eq_correct Hbbeq2 Hszcprrem Hencr Henccpff Hcseq2).
    rewrite (eqP Heq2) (add_prelude_enc_bit_true ((sremB bs1 bs2) == copy (size r_rem) false) Hcseq2). move => HsremB.
    rewrite (eqP HsremB) size_copy {1}/zeros {1}/b0 eq_refl orbT.
    rewrite (eqP HsremB) in Hencr. done.
  - case Heqf: (r_eq == lit_ff); case Heqf2: (r_eq2 == lit_ff).
    + rewrite/=; case => _ <- <-. move => Hsz12 Hgt02 Henc1 Henc2.
      rewrite 3!add_prelude_catrev /smodB. move/andP => [Hcssrem Hcsu]; move/andP : Hcsu => [Hcseq Hcsu]; move/andP : Hcsu => [Hcseq2 Hcsadd].
      have Hszmsl12 : size [:: (splitmsl ls1).2] = size [:: (splitmsl ls2).2] by done.
      move : (add_prelude_tt Hcssrem) => Htt. move : (add_prelude_ff Hcssrem) => Hff. 
      move/andP : (enc_bits_splitmsb Htt Henc1) => [Henc1r Hencmsb1].
      move/andP : (enc_bits_splitmsb Htt Henc2) => [Henc2r Hencmsb2].
      have Hencmsb1nil : enc_bits E [::(splitmsl ls1).2] [::(splitmsb bs1).2] by rewrite enc_bits_cons Hencmsb1 enc_bits_nil.
      have Hencmsb2nil : enc_bits E [::(splitmsl ls2).2] [::(splitmsb bs2).2] by rewrite enc_bits_cons Hencmsb2 enc_bits_nil.
      move : (bit_blast_eq_correct Hbbeq Hszmsl12 Hencmsb1nil Hencmsb2nil Hcseq).
      rewrite (eqP Heqf).
      rewrite (add_prelude_enc_bit_is_not_true ([:: (splitmsb bs1).2] == [:: (splitmsb bs2).2]) Hcseq) Seqs.singleton_eq-/(msb bs1) -/(msb bs2).
      move/negP/eqP/eqP => Hmsb12. move : (Bool.not_true_is_false (msb bs1 == msb bs2) Hmsb12) => Hmsb12f.
      rewrite Hmsb12f orFb.
      move : (bit_blast_srem_correct Hbbsrem Hsz12 Hgt02 Henc1 Henc2 Hcssrem) => Hencr.
      have Hszcprrem : size r_rem = size (copy (size r_rem) lit_ff) by rewrite size_nseq.
      move : (add_prelude_enc_bit_ff Hcssrem) => Hencff.
      move : (enc_bits_copy (size r_rem) Hencff) => Henccpff.
      move : (bit_blast_eq_correct Hbbeq2 Hszcprrem Hencr Henccpff Hcseq2).
      rewrite (eqP Heqf2) (add_prelude_enc_bit_is_not_true ((sremB bs1 bs2) == copy (size r_rem) false) Hcseq2).
      move/negP/eqP/eqP => HsremB. move : (Bool.not_true_is_false ((sremB bs1 bs2) == copy (size r_rem) false) HsremB) => HsremBnot0.
      move : (enc_bits_size Hencr) => Hszencr.
      rewrite -Hszencr HsremBnot0.
      generalize Hszencr. rewrite size_sremB -(enc_bits_size Henc1) Hsz12. move => Hszrrem.
      move/eqP : (eq_refl (addB (sremB bs1 bs2) bs2)) => Haddr.
      exact : (bit_blast_add_correct Hbbadd Hencr Henc2 Haddr Hcsadd Hszrrem).
    + rewrite/=. case => _ <- <-. move => Hsz12 Hgt02 Henc1 Henc2.
      rewrite 6!add_prelude_catrev /smodB. move/andP => [Hcssrem Hcsu]; move/andP : Hcsu => [Hcseq Hcsu]; move/andP : Hcsu => [Hcseq2 Hcsu]; move/andP : Hcsu => [Hcsor Hcsu]; move/andP : Hcsu => [Hcsnot Hcsu]; move/andP : Hcsu => [Hcsand Hcsadd2].
      have Hszmsl12 : size [:: (splitmsl ls1).2] = size [:: (splitmsl ls2).2] by done.
      move : (add_prelude_tt Hcssrem) => Htt. move : (add_prelude_ff Hcssrem) => Hff. 
      move/andP : (enc_bits_splitmsb Htt Henc1) => [Henc1r Hencmsb1].
      move/andP : (enc_bits_splitmsb Htt Henc2) => [Henc2r Hencmsb2].
      have Hencmsb1nil : enc_bits E [::(splitmsl ls1).2] [::(splitmsb bs1).2] by rewrite enc_bits_cons Hencmsb1 enc_bits_nil.
      have Hencmsb2nil : enc_bits E [::(splitmsl ls2).2] [::(splitmsb bs2).2] by rewrite enc_bits_cons Hencmsb2 enc_bits_nil.
      move : (bit_blast_eq_correct Hbbeq Hszmsl12 Hencmsb1nil Hencmsb2nil Hcseq) => Henceqr.
      generalize Henceqr. rewrite (eqP Heqf).
      rewrite (add_prelude_enc_bit_is_not_true ([:: (splitmsb bs1).2] == [:: (splitmsb bs2).2]) Hcseq) Seqs.singleton_eq-/(msb bs1) -/(msb bs2).
      move/negP/eqP/eqP => Hmsb12. move : (Bool.not_true_is_false (msb bs1 == msb bs2) Hmsb12) => Hmsb12f.
      rewrite Hmsb12f orFb.
      move : (bit_blast_srem_correct Hbbsrem Hsz12 Hgt02 Henc1 Henc2 Hcssrem) => Hencr.
      have Hszcprrem : size r_rem = size (copy (size r_rem) lit_ff) by rewrite size_nseq.
      move : (add_prelude_enc_bit_ff Hcssrem) => Hencff.
      move : (enc_bits_copy (size r_rem) Hencff) => Henccpff.
      move : (bit_blast_eq_correct Hbbeq2 Hszcprrem Hencr Henccpff Hcseq2) => Henceq2r.
      case HsremB0: (sremB bs1 bs2 == zeros (size (sremB bs1 bs2))).
      * move : (bit_blast_or_correct Hbbor (enc_bits_copy (size ls2) Henceqr) (enc_bits_copy (size ls2) Henceq2r) Hcsor).
        rewrite -/(msb bs1) -/(msb bs2) Seqs.singleton_eq Hmsb12f (enc_bits_size Hencr) (eqP HsremB0) size_sremB size_zeros -/(zeros (size ls2)) eq_refl.
        have {1}-> : (size ls2 = size (copy (size ls2) true)) by rewrite size_nseq. rewrite or0B. 
        move => Hencorr.
        move : (bit_blast_not_correct Hbbnot Hencorr Hcsnot). rewrite invB_ones. move => Hencnotr.
        move : (bit_blast_and_correct Hbband2 Henc2 Hencnotr Hcsand). rewrite (enc_bits_size Henc2) andB0.
        move => Hencand2r.
        have Haddr :(addB (zeros (size (sremB bs1 bs2))) (zeros (size bs2)) = zeros (size bs1)).
        rewrite size_sremB add0B unzip2_zip; first by rewrite -(enc_bits_size Henc2) -Hsz12 (enc_bits_size Henc1).
        by rewrite 2!size_zeros -(enc_bits_size Henc2) -Hsz12 (enc_bits_size Henc1).
        rewrite -(eqP HsremB0) in Haddr.
        move : (bit_blast_srem_size_ss Hbbsrem) => Hszsrem.
        move : (bit_blast_or_size_ss Hbbor) => Hszor. rewrite size_nseq in Hszor.
        move : (bit_blast_not_size_ss Hbbnot) => Hsznot. rewrite Hszor in Hsznot.
        move : (bit_blast_and_size_ss Hbband2 Hsznot) => Hszand2. rewrite -Hsz12 -Hszsrem in Hszand2.
        exact : (bit_blast_add_correct Hbbadd2 Hencr Hencand2r Haddr Hcsadd2 Hszand2).
      * move : (bit_blast_or_correct Hbbor (enc_bits_copy (size ls2) Henceqr) (enc_bits_copy (size ls2) Henceq2r) Hcsor).
        rewrite -/(msb bs1) -/(msb bs2) Seqs.singleton_eq Hmsb12f (enc_bits_size Hencr) HsremB0 -/(zeros (size ls2)).
        have {1}-> : (size ls2 = size (zeros (size ls2))) by rewrite size_nseq. rewrite or0B. 
        move => Hencorr.
        move : (bit_blast_not_correct Hbbnot Hencorr Hcsnot). rewrite invB_zeros. move => Hencnotr.
        move : (bit_blast_and_correct Hbband2 Henc2 Hencnotr Hcsand). rewrite (enc_bits_size Henc2) andB1.
        move => Hencand2r.
        move/eqP : (eq_refl (addB  (sremB bs1 bs2) bs2)) => Haddr.
        move : (bit_blast_srem_size_ss Hbbsrem) => Hszsrem.
        move : (bit_blast_or_size_ss Hbbor) => Hszor. rewrite size_nseq in Hszor.
        move : (bit_blast_not_size_ss Hbbnot) => Hsznot. rewrite Hszor in Hsznot.
        move : (bit_blast_and_size_ss Hbband2 Hsznot) => Hszand2. rewrite -Hsz12 -Hszsrem in Hszand2.
        exact : (bit_blast_add_correct Hbbadd2 Hencr Hencand2r Haddr Hcsadd2 Hszand2).
    + rewrite /=. case => _ <- <-. move => Hsz12 Hgt02 Henc1 Henc2.
      rewrite 6!add_prelude_catrev /smodB. move/andP => [Hcssrem Hcsu]; move/andP : Hcsu => [Hcseq Hcsu]; move/andP : Hcsu => [Hcseq2 Hcsu]; move/andP : Hcsu => [Hcsor Hcsu]; move/andP : Hcsu => [Hcsnot Hcsu]; move/andP : Hcsu => [Hcsand Hcsadd2].
      have Hszmsl12 : size [:: (splitmsl ls1).2] = size [:: (splitmsl ls2).2] by done.
      move : (add_prelude_tt Hcssrem) => Htt. move : (add_prelude_ff Hcssrem) => Hff. 
      move/andP : (enc_bits_splitmsb Htt Henc1) => [Henc1r Hencmsb1].
      move/andP : (enc_bits_splitmsb Htt Henc2) => [Henc2r Hencmsb2].
      have Hencmsb1nil : enc_bits E [::(splitmsl ls1).2] [::(splitmsb bs1).2] by rewrite enc_bits_cons Hencmsb1 enc_bits_nil.
      have Hencmsb2nil : enc_bits E [::(splitmsl ls2).2] [::(splitmsb bs2).2] by rewrite enc_bits_cons Hencmsb2 enc_bits_nil.
      move : (bit_blast_eq_correct Hbbeq Hszmsl12 Hencmsb1nil Hencmsb2nil Hcseq) => Henceqr.
      have Hszcprrem : size r_rem = size (copy (size r_rem) lit_ff) by rewrite size_nseq.
      move : (add_prelude_enc_bit_ff Hcssrem) => Hencff.
      move : (enc_bits_copy (size r_rem) Hencff) => Henccpff.
      move : (bit_blast_srem_correct Hbbsrem Hsz12 Hgt02 Henc1 Henc2 Hcssrem) => Hencr.
      move : (bit_blast_eq_correct Hbbeq2 Hszcprrem Hencr Henccpff Hcseq2) => Henceq2r.
      generalize Henceq2r.
      rewrite (eqP Heqf2) (add_prelude_enc_bit_is_not_true ((sremB bs1 bs2) == copy (size r_rem) false) Hcseq2). move => HsremB.
      generalize HsremB.
      move/negP/eqP/eqP => HsremB0. move : (Bool.not_true_is_false ((sremB bs1 bs2) == copy (size r_rem) false) HsremB0) => HsremB0f.
      rewrite (enc_bits_size Hencr) -/(zeros (size (sremB bs1 bs2))) in HsremB0f.
      rewrite HsremB0f orbF.
      case Hmsbeq : (msb bs1 == msb bs2).
      * move : (bit_blast_or_correct Hbbor (enc_bits_copy (size ls2) Henceqr) (enc_bits_copy (size ls2) Henceq2r) Hcsor).
        rewrite -/(msb bs1) -/(msb bs2) Seqs.singleton_eq Hmsbeq (enc_bits_size Hencr) HsremB0f.
        have ->: (copy (size ls2) false = zeros (size (copy (size ls2) true))) by rewrite size_nseq.
        rewrite orB0.
        move => Hencorr.
        move : (bit_blast_not_correct Hbbnot Hencorr Hcsnot). rewrite invB_ones. move => Hencnotr.
        move : (bit_blast_and_correct Hbband2 Henc2 Hencnotr Hcsand). rewrite (enc_bits_size Henc2) andB0.
        move => Hencand2r.
        have Haddr :(addB  (sremB bs1 bs2) (zeros (size bs2)) = (sremB bs1 bs2)).
        rewrite addB0 unzip1_zip; first done.
        by rewrite size_sremB size_zeros -(enc_bits_size Henc2)-Hsz12 (enc_bits_size Henc1).
        move : (bit_blast_srem_size_ss Hbbsrem) => Hszsrem.
        move : (bit_blast_or_size_ss Hbbor) => Hszor. rewrite size_nseq in Hszor.
        move : (bit_blast_not_size_ss Hbbnot) => Hsznot. rewrite Hszor in Hsznot.
        move : (bit_blast_and_size_ss Hbband2 Hsznot) => Hszand2. rewrite -Hsz12 -Hszsrem in Hszand2.
        exact : (bit_blast_add_correct Hbbadd2 Hencr Hencand2r Haddr Hcsadd2 Hszand2).
      * move : (bit_blast_or_correct Hbbor (enc_bits_copy (size ls2) Henceqr) (enc_bits_copy (size ls2) Henceq2r) Hcsor).
        rewrite -/(msb bs1) -/(msb bs2) Seqs.singleton_eq Hmsbeq (enc_bits_size Hencr) HsremB0f.
        have {2}-> : copy (size ls2) false  = zeros (size (copy (size ls2) false)) by rewrite size_nseq.
        rewrite orB0.
        move => Hencorr.
        move : (bit_blast_not_correct Hbbnot Hencorr Hcsnot). rewrite invB_zeros. move => Hencnotr.
        move : (bit_blast_and_correct Hbband2 Henc2 Hencnotr Hcsand). rewrite (enc_bits_size Henc2) andB1.
        move => Hencand2r.
        move/eqP :(eq_refl (addB  (sremB bs1 bs2) bs2)) => Haddr.
        move : (bit_blast_srem_size_ss Hbbsrem) => Hszsrem.
        move : (bit_blast_or_size_ss Hbbor) => Hszor. rewrite size_nseq in Hszor.
        move : (bit_blast_not_size_ss Hbbnot) => Hsznot. rewrite Hszor in Hsznot.
        move : (bit_blast_and_size_ss Hbband2 Hsznot) => Hszand2. rewrite -Hsz12 -Hszsrem in Hszand2.
        exact : (bit_blast_add_correct Hbbadd2 Hencr Hencand2r Haddr Hcsadd2 Hszand2).
    + rewrite /=. case => _ <- <-. move => Hsz12 Hgt02 Henc1 Henc2.
      rewrite 6!add_prelude_catrev /smodB. move/andP => [Hcssrem Hcsu]; move/andP : Hcsu => [Hcseq Hcsu]; move/andP : Hcsu => [Hcseq2 Hcsu]; move/andP : Hcsu => [Hcsor Hcsu]; move/andP : Hcsu => [Hcsnot Hcsu]; move/andP : Hcsu => [Hcsand Hcsadd2].
      have Hszmsl12 : size [:: (splitmsl ls1).2] = size [:: (splitmsl ls2).2] by done.
      move : (add_prelude_tt Hcssrem) => Htt. move : (add_prelude_ff Hcssrem) => Hff. 
      move/andP : (enc_bits_splitmsb Htt Henc1) => [Henc1r Hencmsb1].
      move/andP : (enc_bits_splitmsb Htt Henc2) => [Henc2r Hencmsb2].
      have Hencmsb1nil : enc_bits E [::(splitmsl ls1).2] [::(splitmsb bs1).2] by rewrite enc_bits_cons Hencmsb1 enc_bits_nil.
      have Hencmsb2nil : enc_bits E [::(splitmsl ls2).2] [::(splitmsb bs2).2] by rewrite enc_bits_cons Hencmsb2 enc_bits_nil.
      move : (bit_blast_eq_correct Hbbeq Hszmsl12 Hencmsb1nil Hencmsb2nil Hcseq) => Henceqr.
      have Hszcprrem : size r_rem = size (copy (size r_rem) lit_ff) by rewrite size_nseq.
      move : (add_prelude_enc_bit_ff Hcssrem) => Hencff.
      move : (enc_bits_copy (size r_rem) Hencff) => Henccpff.
      move : (bit_blast_srem_correct Hbbsrem Hsz12 Hgt02 Henc1 Henc2 Hcssrem) => [Hencr].
      move : (bit_blast_eq_correct Hbbeq2 Hszcprrem Hencr Henccpff Hcseq2) => Henceq2r.
      case Hmsbeq : (msb bs1 == msb bs2); last case Hmsbeq2 : ((sremB bs1 bs2) == zeros (size (sremB bs1 bs2))).
      * rewrite/=.
        have Hszcpeq : (size (copy (size ls2) r_eq)= size (copy (size ls2) r_eq2)) by rewrite 2!size_nseq.
        move : (bit_blast_or_correct Hbbor (enc_bits_copy (size ls2) Henceqr) (enc_bits_copy (size ls2) Henceq2r) Hcsor).
        have {1}-> :(size ls2 = size (copy (size ls2) ((sremB bs1 bs2) == copy (size r_rem) false))) by rewrite size_nseq.
        rewrite -/(msb bs1) -/(msb bs2) Seqs.singleton_eq Hmsbeq (enc_bits_size Hencr).
        rewrite -/b1 -/(ones (size (copy (size ls2) ((sremB bs1 bs2) == copy (size (sremB bs1 bs2)) false)))) or1B size_nseq.
        move => Hencorr.
        move : (bit_blast_not_correct Hbbnot Hencorr Hcsnot). rewrite invB_ones. move => Hencnotr.
        move : (bit_blast_and_correct Hbband2 Henc2 Hencnotr Hcsand).
        rewrite (enc_bits_size Henc2) andB0.
        move => Hencand2r.
        have Haddr :(addB  (sremB bs1 bs2) (zeros (size bs2)) = (sremB bs1 bs2)).
        rewrite addB0 unzip1_zip; first done.
        by rewrite size_sremB -(enc_bits_size Henc2) -Hsz12 (enc_bits_size Henc1) size_zeros.
        move : (bit_blast_srem_size_ss Hbbsrem) => Hszsrem.
        move : (bit_blast_or_size_ss Hbbor) => Hszor. rewrite size_nseq in Hszor.
        move : (bit_blast_not_size_ss Hbbnot) => Hsznot. rewrite Hszor in Hsznot.
        move : (bit_blast_and_size_ss Hbband2 Hsznot) => Hszand2. rewrite -Hsz12 -Hszsrem in Hszand2.
        exact : (bit_blast_add_correct Hbbadd2 Hencr Hencand2r Haddr Hcsadd2 Hszand2).
      * rewrite/=.
        have Hszcpeq : (size (copy (size ls2) r_eq)= size (copy (size ls2) r_eq2)) by rewrite 2!size_nseq.
        move : (bit_blast_or_correct Hbbor (enc_bits_copy (size ls2) Henceqr) (enc_bits_copy (size ls2) Henceq2r) Hcsor).
        rewrite -/(msb bs1) -/(msb bs2) Seqs.singleton_eq Hmsbeq (enc_bits_size Hencr).
        rewrite /zeros in Hmsbeq2.
        have {1}->: (size ls2 = size (copy (size ls2) true)) by rewrite size_nseq.
        rewrite Hmsbeq2 -/b0 -/(zeros (size (copy (size ls2) true))) or0B -/b1 -/(ones (size ls2)). 
        move => Hencorr.
        move : (bit_blast_not_correct Hbbnot Hencorr Hcsnot). rewrite invB_ones. move => Hencnotr.
        move : (bit_blast_and_correct Hbband2 Henc2 Hencnotr Hcsand). rewrite (enc_bits_size Henc2) andB0.
        move => Hencand2r.
        have Haddr :(addB  (sremB bs1 bs2) (zeros (size bs2)) = (sremB bs1 bs2)).
        rewrite addB0 unzip1_zip; first done.
        by rewrite size_sremB size_zeros -(enc_bits_size Henc2)-Hsz12 (enc_bits_size Henc1).
        move : (bit_blast_srem_size_ss Hbbsrem) => Hszsrem.
        move : (bit_blast_or_size_ss Hbbor) => Hszor. rewrite size_nseq in Hszor.
        move : (bit_blast_not_size_ss Hbbnot) => Hsznot. rewrite Hszor in Hsznot.
        move : (bit_blast_and_size_ss Hbband2 Hsznot) => Hszand2. rewrite -Hsz12 -Hszsrem in Hszand2.
        exact : (bit_blast_add_correct Hbbadd2 Hencr Hencand2r Haddr Hcsadd2 Hszand2).
      * rewrite/=.
        have Hszcpeq : (size (copy (size ls2) r_eq)= size (copy (size ls2) r_eq2)) by rewrite 2!size_nseq.
        move : (bit_blast_or_correct Hbbor (enc_bits_copy (size ls2) Henceqr) (enc_bits_copy (size ls2) Henceq2r) Hcsor).
        rewrite -/(msb bs1) -/(msb bs2) Seqs.singleton_eq Hmsbeq (enc_bits_size Hencr) Hmsbeq2.
        have {2} -> : (copy (size ls2) false = zeros (size (copy (size ls2) false))) by rewrite size_nseq.
        rewrite orB0.
        move => Hencorr.
        move : (bit_blast_not_correct Hbbnot Hencorr Hcsnot). rewrite invB_zeros. move => Hencnotr.
        move : (bit_blast_and_correct Hbband2 Henc2 Hencnotr Hcsand). rewrite (enc_bits_size Henc2) andB1.
        move => Hencand2r.
        have Haddr :(addB  (sremB bs1 bs2) bs2 = addB (sremB bs1 bs2) bs2) by done.
        move : (bit_blast_srem_size_ss Hbbsrem) => Hszsrem.
        move : (bit_blast_or_size_ss Hbbor) => Hszor. rewrite size_nseq in Hszor.
        move : (bit_blast_not_size_ss Hbbnot) => Hsznot. rewrite Hszor in Hsznot.
        move : (bit_blast_and_size_ss Hbband2 Hsznot) => Hszand2. rewrite -Hsz12 -Hszsrem in Hszand2.
        exact : (bit_blast_add_correct Hbbadd2 Hencr Hencand2r Haddr Hcsadd2 Hszand2).
Qed.


  