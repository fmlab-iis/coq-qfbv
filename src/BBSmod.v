From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBConst BBXor BBEq BBZeroExtend BBNeg BBAnd BBAdd BBShl BBSub BBMul BBAshr BBUge BBUdiv BBLneg BBSdiv BBOr BBNot BBNeg.
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Definition smodB bs1 bs2 : bits := *)
(*   let r_sdiv := sremB' bs1 bs2 in  *)
(*   if (msb bs1 == msb bs2) || (r_sdiv == (zeros (size r_sdiv))) then *)
(*     r_sdiv *)
(*   else addB r_sdiv bs2. *)

(* ===== bit_blast_smod ===== *)

Definition bit_blast_smod g ls1 ls2 : generator * cnf * word :=
  let (ls1_tl, ls1_sign) := eta_expand (splitmsl ls1) in
  let (ls2_tl, ls2_sign) := eta_expand (splitmsl ls2) in
  let '(g_srem, cs_srem, lrs_srem) := bit_blast_srem g ls1 ls2 in
  let '(g_eq, cs_eq, r_eq) := bit_blast_eq g_srem (ls1_sign::nil) (ls2_sign::nil) in
  let '(g_eq2, cs_eq2, r_eq2) := bit_blast_eq g_eq lrs_srem (copy (size lrs_srem) lit_ff) in
  if (r_eq == lit_tt) || (r_eq2 == lit_tt) then
    (g_eq2, catrev cs_srem (catrev cs_eq2 cs_eq), lrs_srem)
  else if (r_eq == lit_ff) && (r_eq2 == lit_ff) then
    let '(g_add, cs_add, lrs_add) := bit_blast_add g_eq2 lrs_srem ls2 in
    (g_add, catrev cs_srem (catrev cs_eq (catrev cs_eq2 cs_add)), lrs_add)
       else let '(g_or, cs_or, lrs_or) := bit_blast_or g_eq2 (copy (size ls2) r_eq) (copy (size ls2) r_eq2) in
            let '(g_not, cs_not, lrs_not) := bit_blast_not g_or lrs_or in
            let '(g_and2, cs_and2, lrs_and2) := bit_blast_and g_not ls2 lrs_not in
            let '(g_add2, cs_add2, lrs_add2) := bit_blast_add g_and2 lrs_srem lrs_and2 in
            (g_add2, catrev cs_srem (catrev cs_eq (catrev cs_eq2 (catrev cs_or (catrev cs_not (catrev cs_and2 cs_add2))))), lrs_add2).


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
  0 < size ls1 ->
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
    exact : (bit_blast_srem_correct Hbbsrem Hsz12 Hgt02 Henc1 Henc2 Hcssrem) => Hencr. 
  - rewrite /=; case => _ <- <-. move => Hsz12 Hgt02 Henc1 Henc2.
    rewrite 2!add_prelude_catrev /smodB. move/andP => [Hcssrem Hcsu]; move/andP : Hcsu => [Hcseq2 Hcseq].
    have Hszcprrem : size r_rem = size (copy (size r_rem) lit_ff) by rewrite size_nseq.
    move : (add_prelude_enc_bit_ff Hcssrem) => Hencff.
    move : (enc_bits_copy (size r_rem) Hencff) => Henccpff.
    move : (bit_blast_srem_correct Hbbsrem Hsz12 Hgt02 Henc1 Henc2 Hcssrem) => Hencr.
    move : (bit_blast_eq_correct Hbbeq2 Hszcprrem Hencr Henccpff Hcseq2).
    rewrite (eqP Heq2) (add_prelude_enc_bit_true ((sremB bs1 bs2) == copy (size r_rem) false) Hcseq2). move => HsremB.
    rewrite (eqP HsremB) size_copy {1}/zeros {1}/b0 eq_refl orbT.
    rewrite (eqP HsremB)// in Hencr.
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

Lemma bit_blast_smod_correct' g ls1 ls2 g' cs rlrs E bs1 bs2 :
  bit_blast_smod g ls1 ls2 = (g', cs, rlrs) ->
  size ls1 = size ls2 ->
  0 < size ls1 ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E rlrs (smodB' bs1 bs2).
Proof.
  rewrite -smodB_is_smodB'. exact: bit_blast_smod_correct.
Qed.

Definition mk_env_smod E g ls1 ls2 : env * generator * cnf * word :=
  let (ls1_tl, ls1_sign) := eta_expand (splitmsl ls1) in
  let (ls2_tl, ls2_sign) := eta_expand (splitmsl ls2) in
  let '(E_srem, g_srem, cs_srem, lrs_srem) := mk_env_srem E g ls1 ls2 in
  let '(E_eq, g_eq, cs_eq, r_eq) := mk_env_eq E_srem g_srem (ls1_sign::nil) (ls2_sign::nil) in
  let '(E_eq2, g_eq2, cs_eq2, r_eq2) := mk_env_eq E_eq g_eq lrs_srem (copy (size lrs_srem) lit_ff) in
  if (r_eq == lit_tt) || (r_eq2 == lit_tt) then
    (E_eq2, g_eq2, catrev cs_srem (catrev cs_eq2 cs_eq), lrs_srem)
  else if (r_eq == lit_ff) && (r_eq2 == lit_ff) then
    let '(E_add, g_add, cs_add, lrs_add) := mk_env_add E_eq2 g_eq2 lrs_srem ls2 in
    (E_add, g_add, catrev cs_srem (catrev cs_eq (catrev cs_eq2 cs_add)), lrs_add)
       else let '(E_or, g_or, cs_or, lrs_or) := mk_env_or E_eq2 g_eq2 (copy (size ls2) r_eq) (copy (size ls2) r_eq2) in
            let '(E_not, g_not, cs_not, lrs_not) := mk_env_not E_or g_or lrs_or in
            let '(E_and2, g_and2, cs_and2, lrs_and2) := mk_env_and E_not g_not ls2 lrs_not in
            let '(E_add2, g_add2, cs_add2, lrs_add2) := mk_env_add E_and2 g_and2 lrs_srem lrs_and2 in
            (E_add2, g_add2, catrev cs_srem (catrev cs_eq (catrev cs_eq2 (catrev cs_or (catrev cs_not (catrev cs_and2 cs_add2))))), lrs_add2).

  
Lemma mk_env_smod_is_bit_blast_smod E g ls1 ls2 E' g' cs lrs :
  mk_env_smod E g ls1 ls2 = (E', g', cs, lrs) ->
  bit_blast_smod g ls1 ls2  = (g', cs, lrs).
Proof.
  rewrite /mk_env_smod /bit_blast_smod.
  dcase (mk_env_srem E g ls1 ls2) => [[[[E_srem] g_srem] cs_srem] lrs_srem] Hmksrem.
  dcase (mk_env_eq E_srem g_srem [:: (splitmsl ls1).2] [:: (splitmsl ls2).2])
  => [[[[E_eq] g_eq] cs_eq] lr_eq] Hmkeq.
  dcase (mk_env_eq E_eq g_eq lrs_srem (copy (size lrs_srem) lit_ff))
  => [[[[E_eq2] g_eq2] cs_eq2] lr_eq2] Hmkeq2.
  rewrite (mk_env_srem_is_bit_blast_srem Hmksrem).
  rewrite (mk_env_eq_is_bit_blast_eq Hmkeq) (mk_env_eq_is_bit_blast_eq Hmkeq2).
  case ((lr_eq == lit_tt) || (lr_eq2 == lit_tt)); 
    last case ((lr_eq == lit_ff) && (lr_eq2 == lit_ff)).
  - by case=> _ <- <- <-.
  - dcase (mk_env_add E_eq2 g_eq2 lrs_srem ls2) 
    => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    rewrite (mk_env_add_is_bit_blast_add Hmkadd). by case=> _ <- <- <-.
  - dcase (mk_env_or E_eq2 g_eq2 (copy (size ls2) lr_eq) (copy (size ls2) lr_eq2))
    => [[[[E_or] g_or] cs_or] lrs_or] Hmkor.
    dcase (mk_env_not E_or g_or lrs_or) => [[[[E_not] g_not] cs_not] lrs_not] Hmknot.
    dcase (mk_env_and E_not g_not ls2 lrs_not)
    => [[[[E_and] g_and] cs_and] lrs_and] Hmkand.
    dcase (mk_env_add E_and g_and lrs_srem lrs_and)
    => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    rewrite (mk_env_or_is_bit_blast_or Hmkor) (mk_env_not_is_bit_blast_not Hmknot)
      (mk_env_and_is_bit_blast_and Hmkand) (mk_env_add_is_bit_blast_add Hmkadd).
    by case=> _ <- <- <-.
Qed.


Lemma mk_env_smod_newer_gen E g ls1 ls2 E' g' cs lrs :
  mk_env_smod E g ls1 ls2 = (E', g', cs, lrs) ->
  (g <=? g')%positive.
Proof.
  rewrite /mk_env_smod.
  dcase (mk_env_srem E g ls1 ls2) => [[[[E_srem] g_srem] cs_srem] lrs_srem] Hmksrem.
  dcase (mk_env_eq E_srem g_srem [:: (splitmsl ls1).2] [:: (splitmsl ls2).2])
  => [[[[E_eq] g_eq] cs_eq] lr_eq] Hmkeq.
  dcase (mk_env_eq E_eq g_eq lrs_srem (copy (size lrs_srem) lit_ff))
  => [[[[E_eq2] g_eq2] cs_eq2] lr_eq2] Hmkeq2.
  move: (mk_env_srem_newer_gen Hmksrem) => Hggsrem.
  move: (mk_env_eq_newer_gen Hmkeq) => Hgsremgeq.
  move: (mk_env_eq_newer_gen Hmkeq2) => Hgeqgeq2.
  case ((lr_eq == lit_tt) || (lr_eq2 == lit_tt)); 
    last case ((lr_eq == lit_ff) && (lr_eq2 == lit_ff)).
  - case=> _ <- _ _. 
    exact: (pos_leb_trans Hggsrem (pos_leb_trans Hgsremgeq Hgeqgeq2)).
  - dcase (mk_env_add E_eq2 g_eq2 lrs_srem ls2) 
    => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    case=> _ <- _ _.
    move: (mk_env_add_newer_gen Hmkadd) => Hgeq2gadd.
    exact: (pos_leb_trans Hggsrem (pos_leb_trans Hgsremgeq
           (pos_leb_trans Hgeqgeq2 Hgeq2gadd))).
  - dcase (mk_env_or E_eq2 g_eq2 (copy (size ls2) lr_eq) (copy (size ls2) lr_eq2))
    => [[[[E_or] g_or] cs_or] lrs_or] Hmkor.
    dcase (mk_env_not E_or g_or lrs_or) => [[[[E_not] g_not] cs_not] lrs_not] Hmknot.
    dcase (mk_env_and E_not g_not ls2 lrs_not)
    => [[[[E_and] g_and] cs_and] lrs_and] Hmkand.
    dcase (mk_env_add E_and g_and lrs_srem lrs_and)
    => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    case=> _ <- _ _.
    move: (mk_env_or_newer_gen Hmkor) => Hgeq2gor.
    move: (mk_env_not_newer_gen Hmknot) => Hgorgnot.
    move: (mk_env_and_newer_gen Hmkand) => Hgnotgand.
    move: (mk_env_add_newer_gen Hmkadd) => Hgandgadd.
    by apply (pos_leb_trans Hggsrem), (pos_leb_trans Hgsremgeq), 
       (pos_leb_trans Hgeqgeq2), (pos_leb_trans Hgeq2gor), (pos_leb_trans Hgorgnot),
       (pos_leb_trans Hgnotgand).
Qed.

Lemma mk_env_smod_newer_res E g ls1 ls2 E' g' cs lrs :
  mk_env_smod E g ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 ->
  newer_than_lits g ls2 ->
  newer_than_lits g' lrs.
Proof.
  move=> Hmk Hgtt Hgls1 Hgls2. move: Hmk. rewrite /mk_env_smod.
  dcase (mk_env_srem E g ls1 ls2) => [[[[E_srem] g_srem] cs_srem] lrs_srem] Hmksrem.
  dcase (mk_env_eq E_srem g_srem [:: (splitmsl ls1).2] [:: (splitmsl ls2).2])
  => [[[[E_eq] g_eq] cs_eq] lr_eq] Hmkeq.
  dcase (mk_env_eq E_eq g_eq lrs_srem (copy (size lrs_srem) lit_ff))
  => [[[[E_eq2] g_eq2] cs_eq2] lr_eq2] Hmkeq2.
  case ((lr_eq == lit_tt) || (lr_eq2 == lit_tt)); 
    last case ((lr_eq == lit_ff) && (lr_eq2 == lit_ff)).
  - case=> _ <- _ <-. 
    move: (mk_env_srem_newer_res Hmksrem Hgtt Hgls1 Hgls2) => Hgsremlsrem.
    move: (mk_env_eq_newer_gen Hmkeq) => Hgsremgeq.
    move: (mk_env_eq_newer_gen Hmkeq2) => Hgeqgeq2.
    exact: (newer_than_lits_le_newer Hgsremlsrem (pos_leb_trans Hgsremgeq Hgeqgeq2)).
  - dcase (mk_env_add E_eq2 g_eq2 lrs_srem ls2) 
    => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    case=> _ <- _ <-. exact: (mk_env_add_newer_res Hmkadd).
  - dcase (mk_env_or E_eq2 g_eq2 (copy (size ls2) lr_eq) (copy (size ls2) lr_eq2))
    => [[[[E_or] g_or] cs_or] lrs_or] Hmkor.
    dcase (mk_env_not E_or g_or lrs_or) => [[[[E_not] g_not] cs_not] lrs_not] Hmknot.
    dcase (mk_env_and E_not g_not ls2 lrs_not)
    => [[[[E_and] g_and] cs_and] lrs_and] Hmkand.
    dcase (mk_env_add E_and g_and lrs_srem lrs_and)
    => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    case=> _ <- _ <-. exact: (mk_env_add_newer_res Hmkadd).
Qed.

Lemma mk_env_smod_newer_cnf E g ls1 ls2 E' g' cs lrs :
  mk_env_smod E g ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 ->
  newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  move=> Hmk Hgtt Hgls1 Hgls2. move: Hmk. rewrite /mk_env_smod.
  dcase (mk_env_srem E g ls1 ls2) => [[[[E_srem] g_srem] cs_srem] lrs_srem] Hmksrem.
  dcase (mk_env_eq E_srem g_srem [:: (splitmsl ls1).2] [:: (splitmsl ls2).2])
  => [[[[E_eq] g_eq] cs_eq] lr_eq] Hmkeq.
  dcase (mk_env_eq E_eq g_eq lrs_srem (copy (size lrs_srem) lit_ff))
  => [[[[E_eq2] g_eq2] cs_eq2] lr_eq2] Hmkeq2.
  move: (mk_env_srem_newer_gen Hmksrem) => Hggsrem.
  move: (mk_env_eq_newer_gen Hmkeq) => Hgsremgeq.
  move: (mk_env_eq_newer_gen Hmkeq2) => Hgeqgeq2.
  move: (mk_env_srem_newer_cnf Hmksrem Hgtt Hgls1 Hgls2) => Hgsremcssrem.
  move: (newer_than_lit_le_newer Hgtt Hggsrem) => Hgsremtt.
  move: (newer_than_lits_le_newer Hgls1 Hggsrem) => Hgsremls1.
  move: (newer_than_lits_msl Hgsremtt Hgsremls1) => Hgsremmsl1.
  move: (newer_than_lits_copy 1 Hgsremmsl1) => Hgsrem1msl1.
  move: (newer_than_lits_le_newer Hgls2 Hggsrem) => Hgsremls2.
  move: (newer_than_lits_msl Hgsremtt Hgsremls2) => Hgsremmsl2.
  move: (newer_than_lits_copy 1 Hgsremmsl2) => Hgsrem1msl2.
  move: (mk_env_eq_newer_cnf Hmkeq Hgsremtt Hgsrem1msl1 Hgsrem1msl2) => Hgeqcseq.
  move: (newer_than_lit_le_newer Hgsremtt Hgsremgeq) => Hgeqtt.
  move: (mk_env_srem_newer_res Hmksrem Hgtt Hgls1 Hgls2) => Hgsremlsrem.
  move: (newer_than_lits_le_newer Hgsremlsrem Hgsremgeq) => Hgeqlsrem.
  rewrite newer_than_lit_tt_ff in Hgeqtt.
  move: (newer_than_lits_copy (size lrs_srem) Hgeqtt) => Hgeqcopy.
  move: (mk_env_eq_newer_cnf Hmkeq2 Hgeqtt Hgeqlsrem Hgeqcopy) => Hgeq2cseq2.
  move: (newer_than_cnf_le_newer Hgsremcssrem (pos_leb_trans Hgsremgeq Hgeqgeq2)) => Hgeq2cssrem.
  move: (newer_than_cnf_le_newer Hgeqcseq Hgeqgeq2) => Hgeq2cseq.
  case ((lr_eq == lit_tt) || (lr_eq2 == lit_tt)); 
    last case ((lr_eq == lit_ff) && (lr_eq2 == lit_ff)).
  - case=> _ <- <- _. 
    by rewrite !newer_than_cnf_catrev Hgeq2cssrem Hgeq2cseq2 Hgeq2cseq.
  - dcase (mk_env_add E_eq2 g_eq2 lrs_srem ls2) 
    => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    case=> _ <- <- _. 
    move: (newer_than_lits_le_newer Hgeqlsrem Hgeqgeq2) => Hgeq2lsrem.
    move: (newer_than_lits_le_newer Hgsremls2 (pos_leb_trans Hgsremgeq Hgeqgeq2)) => Hgeq2ls2.
    move: (newer_than_lit_le_newer Hgeqtt Hgeqgeq2) => Hgeq2tt.
    move: (mk_env_add_newer_cnf Hmkadd Hgeq2lsrem Hgeq2ls2 Hgeq2tt) => Hgaddcsadd.
    move: (mk_env_add_newer_gen Hmkadd) => Hgeq2gadd.
    move: (newer_than_cnf_le_newer Hgeq2cssrem Hgeq2gadd) => Hgaddcssrem.
    move: (newer_than_cnf_le_newer Hgeq2cseq Hgeq2gadd) => Hgaddcseq.
    move: (newer_than_cnf_le_newer Hgeq2cseq2 Hgeq2gadd) => Hgaddcseq2.
    by rewrite !newer_than_cnf_catrev Hgaddcssrem Hgaddcseq2 Hgaddcseq Hgaddcsadd.
  - dcase (mk_env_or E_eq2 g_eq2 (copy (size ls2) lr_eq) (copy (size ls2) lr_eq2))
    => [[[[E_or] g_or] cs_or] lrs_or] Hmkor.
    dcase (mk_env_not E_or g_or lrs_or) => [[[[E_not] g_not] cs_not] lrs_not] Hmknot.
    dcase (mk_env_and E_not g_not ls2 lrs_not)
    => [[[[E_and] g_and] cs_and] lrs_and] Hmkand.
    dcase (mk_env_add E_and g_and lrs_srem lrs_and)
    => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    case=> _ <- <- _.
    move: (mk_env_or_newer_gen Hmkor) => Hgeq2gor.
    move: (mk_env_not_newer_gen Hmknot) => Hgorgnot.
    move: (mk_env_and_newer_gen Hmkand) => Hgnotgand.
    move: (mk_env_add_newer_gen Hmkadd) => Hgandgadd.
    move: (pos_leb_trans Hgnotgand Hgandgadd) => Hgnotgadd.
    move: (pos_leb_trans Hgorgnot Hgnotgadd) => Hgorgadd.
    move: (pos_leb_trans Hgeq2gor Hgorgadd) => Hgeq2gadd.
    move: (newer_than_cnf_le_newer Hgeq2cssrem Hgeq2gadd) => Hgaddcssrem.
    move: (newer_than_cnf_le_newer Hgeq2cseq Hgeq2gadd) => Hgaddcseq.
    move: (newer_than_cnf_le_newer Hgeq2cseq2 Hgeq2gadd) => Hgaddcseq2.
    move: (newer_than_lit_le_newer Hgeqtt Hgeqgeq2) => Hgeq2tt.
    rewrite -newer_than_lit_tt_ff in Hgeq2tt.
    move: (mk_env_eq_newer_res Hmkeq) => Hgeqleq.
    move: (newer_than_lit_le_newer Hgeqleq Hgeqgeq2) => Hgeq2leq.
    move: (newer_than_lits_copy (size ls2) Hgeq2leq) => Hgeq2leqs.
    move: (mk_env_eq_newer_res Hmkeq2) => Hgeq2leq2.
    move: (newer_than_lits_copy (size ls2) Hgeq2leq2) => Hgeq2leq2s.
    move: (mk_env_or_newer_cnf Hmkor Hgeq2tt Hgeq2leqs Hgeq2leq2s) => Hgorcsor.
    move: (newer_than_cnf_le_newer Hgorcsor Hgorgadd) => Hgaddcsor.
    move: (mk_env_or_newer_res Hmkor Hgeq2tt Hgeq2leqs Hgeq2leq2s) => Hgorlor.
    move: (mk_env_not_newer_cnf Hmknot Hgorlor) => Hgnotcsnot.
    move: (newer_than_cnf_le_newer Hgnotcsnot Hgnotgadd) => Hgaddcsnot.
    move: (newer_than_lit_le_newer Hgeq2tt (pos_leb_trans Hgeq2gor Hgorgnot)) => Hgnottt.
    move: (newer_than_lits_le_newer Hgsremls2 (pos_leb_trans Hgsremgeq 
          (pos_leb_trans Hgeqgeq2 (pos_leb_trans Hgeq2gor Hgorgnot)))) => Hgnotls2.
    move: (mk_env_not_newer_res Hmknot Hgorlor) => Hgnotlnot.
    move: (mk_env_and_newer_cnf Hmkand Hgnottt Hgnotls2 Hgnotlnot) => Hgandcsand.
    move: (newer_than_cnf_le_newer Hgandcsand Hgandgadd) => Hgaddcsand.
    move: (newer_than_lits_le_newer Hgeqlsrem (pos_leb_trans Hgeqgeq2 
          (pos_leb_trans Hgeq2gor (pos_leb_trans Hgorgnot Hgnotgand)))) => Hgandlsrem.
    move: (mk_env_and_newer_res Hmkand Hgnottt Hgnotls2 Hgnotlnot) => Hgandland.
    move: (newer_than_lit_le_newer Hgnottt Hgnotgand) => Hgandtt.
    rewrite newer_than_lit_tt_ff in Hgandtt.
    move: (mk_env_add_newer_cnf Hmkadd Hgandlsrem Hgandland Hgandtt) => Hgaddcsadd.
    by rewrite !newer_than_cnf_catrev Hgaddcssrem Hgaddcseq Hgaddcseq2 Hgaddcsor
               Hgaddcsnot Hgaddcsand Hgaddcsadd.
Qed.

Lemma mk_env_smod_preserve E g ls1 ls2 E' g' cs lrs :
  mk_env_smod E g ls1 ls2 = (E', g', cs, lrs) ->
  env_preserve E E' g.
Proof.
  rewrite /mk_env_smod.
  dcase (mk_env_srem E g ls1 ls2) => [[[[E_srem] g_srem] cs_srem] lrs_srem] Hmksrem.
  dcase (mk_env_eq E_srem g_srem [:: (splitmsl ls1).2] [:: (splitmsl ls2).2])
  => [[[[E_eq] g_eq] cs_eq] lr_eq] Hmkeq.
  dcase (mk_env_eq E_eq g_eq lrs_srem (copy (size lrs_srem) lit_ff))
  => [[[[E_eq2] g_eq2] cs_eq2] lr_eq2] Hmkeq2.
  move: (mk_env_srem_newer_gen Hmksrem) => Hggsrem.
  move: (mk_env_eq_newer_gen Hmkeq) => Hgsremgeq.
  move: (mk_env_eq_newer_gen Hmkeq2) => Hgeqgeq2.
  move: (pos_leb_trans Hggsrem Hgsremgeq) => Hggeq.
  move: (pos_leb_trans Hggeq Hgeqgeq2) => Hggeq2.
  move: (mk_env_srem_preserve Hmksrem) => HEEsremg.
  move: (mk_env_eq_preserve Hmkeq) => HEsremEeqgsrem.
  move: (mk_env_eq_preserve Hmkeq2) => HEeqEeq2geq.
  move: (env_preserve_le HEsremEeqgsrem Hggsrem) => {HEsremEeqgsrem} HEsremEeqg.
  move: (env_preserve_le HEeqEeq2geq Hggeq) => {HEeqEeq2geq} HEeqEeq2g.
  move: (env_preserve_trans HEEsremg (env_preserve_trans HEsremEeqg HEeqEeq2g)) => HEEeq2g.
  case ((lr_eq == lit_tt) || (lr_eq2 == lit_tt)); 
    last case ((lr_eq == lit_ff) && (lr_eq2 == lit_ff)).
  - by case=> <- _ _ _. 
  - dcase (mk_env_add E_eq2 g_eq2 lrs_srem ls2) 
    => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    case=> <- _ _ _. 
    move: (mk_env_add_preserve Hmkadd) => HEeq2Eaddgeq2.
    move: (env_preserve_le HEeq2Eaddgeq2 Hggeq2) => {HEeq2Eaddgeq2} HEeq2Eaddg.
    by apply (env_preserve_trans HEEeq2g).
  - dcase (mk_env_or E_eq2 g_eq2 (copy (size ls2) lr_eq) (copy (size ls2) lr_eq2))
    => [[[[E_or] g_or] cs_or] lrs_or] Hmkor.
    dcase (mk_env_not E_or g_or lrs_or) => [[[[E_not] g_not] cs_not] lrs_not] Hmknot.
    dcase (mk_env_and E_not g_not ls2 lrs_not)
    => [[[[E_and] g_and] cs_and] lrs_and] Hmkand.
    dcase (mk_env_add E_and g_and lrs_srem lrs_and)
    => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    case=> <- _ _ _.
    move: (mk_env_or_newer_gen Hmkor) => Hgeq2gor.
    move: (mk_env_not_newer_gen Hmknot) => Hgorgnot.
    move: (mk_env_and_newer_gen Hmkand) => Hgnotgand.
    move: (pos_leb_trans Hggeq2 Hgeq2gor) => Hggor.
    move: (pos_leb_trans Hggor Hgorgnot) => Hggnot.
    move: (pos_leb_trans Hggnot Hgnotgand) => Hggand.
    move: (mk_env_or_preserve Hmkor) => HEeq2Eorgeq2.
    move: (mk_env_not_preserve Hmknot) => HEorEnotgor.
    move: (mk_env_and_preserve Hmkand) => HEnotEandgnot.
    move: (mk_env_add_preserve Hmkadd) => HEandEaddgand.
    move: (env_preserve_le HEeq2Eorgeq2 Hggeq2) => {HEeq2Eorgeq2} HEeq2Eorg.
    move: (env_preserve_le HEorEnotgor Hggor) => {HEorEnotgor} HEorEnotg.
    move: (env_preserve_le HEnotEandgnot Hggnot) => {HEnotEandgnot} HEnotEandg.
    move: (env_preserve_le HEandEaddgand Hggand) => {HEandEaddgand} HEandEaddg.
    by apply (env_preserve_trans HEEeq2g), (env_preserve_trans HEeq2Eorg),
       (env_preserve_trans HEorEnotg), (env_preserve_trans HEnotEandg).
Qed.

Lemma mk_env_smod_sat E g ls1 ls2 E' g' cs lrs :
  mk_env_smod E g ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls1 ->
  newer_than_lits g ls2 ->
  interp_cnf E' cs.
Proof.
  rewrite /mk_env_smod.
  dcase (mk_env_srem E g ls1 ls2) => [[[[E_srem] g_srem] cs_srem] lrs_srem] Hmksrem.
  dcase (mk_env_eq E_srem g_srem [:: (splitmsl ls1).2] [:: (splitmsl ls2).2]) => [[[[E_eq] g_eq] cs_eq] r_eq] Hmkeq.
  dcase (mk_env_eq E_eq g_eq lrs_srem (copy (size lrs_srem) lit_ff))  => [[[[E_eq2] g_eq2] cs_eq2] r_eq2] Hmkeq2.
    move : (mk_env_srem_newer_gen Hmksrem) => Hnewsrem.
    move : (mk_env_eq_newer_gen Hmkeq) => Hneweq.
    move : (mk_env_eq_newer_gen Hmkeq2) => Hneweq2.
  case Htt1 : (r_eq == lit_tt) ; case Hff1 : (r_eq == lit_ff); case Htt2 : (r_eq2 == lit_tt); case Hff2 : (r_eq2 == lit_ff);
    try rewrite (eqP Htt1)// in Hff1; try rewrite (eqP Htt2)// in Hff2.
  - rewrite /=. case => <- _ <- _; move => Htt Hls1 Hls2; generalize Htt; rewrite newer_than_lit_tt_ff; move => Hff.
    rewrite !interp_cnf_catrev.
    move : (mk_env_srem_newer_res Hmksrem Htt Hls1 Hls2) => Hgsrem.
    move : (mk_env_srem_newer_cnf Hmksrem Htt Hls1 Hls2) => Hcssrem.
    move : (mk_env_srem_sat Hmksrem Htt Hls1 Hls2) => Hcnfsrem.
    move : (mk_env_eq_newer_res Hmkeq ) => Hgeq.
    have Hnewcp : (newer_than_lits g (copy (size lrs_srem) lit_ff)).
    {
      exact : (newer_than_lits_copy (size lrs_srem) Hff).
    }
    have Hnewmsl: (newer_than_lits g [:: (splitmsl ls1).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls1) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc).
    }
    have Hnewmsl2 : (newer_than_lits g [:: (splitmsl ls2).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls2) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc) .
    }
    move : (mk_env_eq_sat Hmkeq (newer_than_lit_le_newer Htt Hnewsrem) (newer_than_lits_le_newer Hnewmsl Hnewsrem) (newer_than_lits_le_newer Hnewmsl2 Hnewsrem)) => Hcnfeq.
    move : (mk_env_eq_newer_cnf Hmkeq (newer_than_lit_le_newer Htt Hnewsrem) (newer_than_lits_le_newer Hnewmsl Hnewsrem) (newer_than_lits_le_newer Hnewmsl2 Hnewsrem)) => Hcseq.
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq2) (newer_than_cnf_le_newer Hcssrem Hneweq)).
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq) Hcssrem) Hcnfsrem.
    rewrite (mk_env_eq_sat Hmkeq2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem Hneweq)) (newer_than_lits_le_newer Hgsrem Hneweq) (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnewsrem Hneweq))) .
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq2) Hcseq) Hcnfeq//.
  - rewrite /=. case => <- _ <- _; move => Htt Hls1 Hls2; generalize Htt; rewrite newer_than_lit_tt_ff; move => Hff.
    rewrite !interp_cnf_catrev.
    move : (mk_env_srem_newer_res Hmksrem Htt Hls1 Hls2) => Hgsrem.
    move : (mk_env_srem_newer_cnf Hmksrem Htt Hls1 Hls2) => Hcssrem.
    move : (mk_env_srem_sat Hmksrem Htt Hls1 Hls2) => Hcnfsrem.
    move : (mk_env_eq_newer_res Hmkeq ) => Hgeq.
    have Hnewcp : (newer_than_lits g (copy (size lrs_srem) lit_ff)).
    {
      exact : (newer_than_lits_copy (size lrs_srem) Hff).
    }
    have Hnewmsl: (newer_than_lits g [:: (splitmsl ls1).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls1) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc).
    }
    have Hnewmsl2 : (newer_than_lits g [:: (splitmsl ls2).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls2) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc) .
    }
    move : (mk_env_eq_sat Hmkeq2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem Hneweq)) (newer_than_lits_le_newer Hgsrem Hneweq) (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnewsrem Hneweq))) => Hcnfeq2.
    move : (mk_env_eq_sat Hmkeq (newer_than_lit_le_newer Htt Hnewsrem) (newer_than_lits_le_newer Hnewmsl Hnewsrem) (newer_than_lits_le_newer Hnewmsl2 Hnewsrem)) => Hcnfeq.
    move : (mk_env_eq_newer_cnf Hmkeq (newer_than_lit_le_newer Htt Hnewsrem) (newer_than_lits_le_newer Hnewmsl Hnewsrem) (newer_than_lits_le_newer Hnewmsl2 Hnewsrem)) => Hcseq.
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq2) (newer_than_cnf_le_newer Hcssrem Hneweq)).
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq) Hcssrem) Hcnfsrem.
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq2) Hcseq) Hcnfeq Hcnfeq2//.
  - rewrite /=. case => <- _ <- _; move => Htt Hls1 Hls2; generalize Htt; rewrite newer_than_lit_tt_ff; move => Hff.
    rewrite !interp_cnf_catrev.
    move : (mk_env_srem_newer_res Hmksrem Htt Hls1 Hls2) => Hgsrem.
    move : (mk_env_srem_newer_cnf Hmksrem Htt Hls1 Hls2) => Hcssrem.
    move : (mk_env_srem_sat Hmksrem Htt Hls1 Hls2) => Hcnfsrem.
    move : (mk_env_eq_newer_res Hmkeq ) => Hgeq.
    have Hnewcp : (newer_than_lits g (copy (size lrs_srem) lit_ff)).
    {
      exact : (newer_than_lits_copy (size lrs_srem) Hff).
    }
    have Hnewmsl: (newer_than_lits g [:: (splitmsl ls1).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls1) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc).
    }
    have Hnewmsl2 : (newer_than_lits g [:: (splitmsl ls2).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls2) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc) .
    }
    move : (mk_env_eq_sat Hmkeq2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem Hneweq)) (newer_than_lits_le_newer Hgsrem Hneweq) (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnewsrem Hneweq))) => Hcnfeq2.
    move : (mk_env_eq_sat Hmkeq (newer_than_lit_le_newer Htt Hnewsrem) (newer_than_lits_le_newer Hnewmsl Hnewsrem) (newer_than_lits_le_newer Hnewmsl2 Hnewsrem)) => Hcnfeq.
    move : (mk_env_eq_newer_cnf Hmkeq (newer_than_lit_le_newer Htt Hnewsrem) (newer_than_lits_le_newer Hnewmsl Hnewsrem) (newer_than_lits_le_newer Hnewmsl2 Hnewsrem)) => Hcseq.
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq2) (newer_than_cnf_le_newer Hcssrem Hneweq)).
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq) Hcssrem) Hcnfsrem.
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq2) Hcseq) Hcnfeq Hcnfeq2//.
  - rewrite /=. case => <- _ <- _; move => Htt Hls1 Hls2; generalize Htt; rewrite newer_than_lit_tt_ff; move => Hff.
    rewrite !interp_cnf_catrev.
    move : (mk_env_srem_newer_res Hmksrem Htt Hls1 Hls2) => Hgsrem.
    move : (mk_env_srem_newer_cnf Hmksrem Htt Hls1 Hls2) => Hcssrem.
    move : (mk_env_srem_sat Hmksrem Htt Hls1 Hls2) => Hcnfsrem.
    move : (mk_env_eq_newer_res Hmkeq ) => Hgeq.
    have Hnewcp : (newer_than_lits g (copy (size lrs_srem) lit_ff)).
    {
      exact : (newer_than_lits_copy (size lrs_srem) Hff).
    }
    have Hnewmsl: (newer_than_lits g [:: (splitmsl ls1).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls1) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc).
    }
    have Hnewmsl2 : (newer_than_lits g [:: (splitmsl ls2).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls2) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc) .
    }
    move : (mk_env_eq_sat Hmkeq2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem Hneweq)) (newer_than_lits_le_newer Hgsrem Hneweq) (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnewsrem Hneweq))) => Hcnfeq2.
    move : (mk_env_eq_sat Hmkeq (newer_than_lit_le_newer Htt Hnewsrem) (newer_than_lits_le_newer Hnewmsl Hnewsrem) (newer_than_lits_le_newer Hnewmsl2 Hnewsrem)) => Hcnfeq.
    move : (mk_env_eq_newer_cnf Hmkeq (newer_than_lit_le_newer Htt Hnewsrem) (newer_than_lits_le_newer Hnewmsl Hnewsrem) (newer_than_lits_le_newer Hnewmsl2 Hnewsrem)) => Hcseq.
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq2) (newer_than_cnf_le_newer Hcssrem Hneweq)).
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq) Hcssrem) Hcnfsrem.
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq2) Hcseq) Hcnfeq Hcnfeq2//.
  - rewrite /=.
    dcase (mk_env_add E_eq2 g_eq2 lrs_srem ls2) => [[[[E_add] g_add] cs_add] lrs_add] Hmkaddr.
    case => <- _ <- _; move => Htt Hls1 Hls2; generalize Htt; rewrite newer_than_lit_tt_ff; move => Hff.
    rewrite !interp_cnf_catrev.
    move : (mk_env_srem_newer_res Hmksrem Htt Hls1 Hls2) => Hgsrem.
    move : (mk_env_srem_newer_cnf Hmksrem Htt Hls1 Hls2) => Hcssrem.
    move : (mk_env_srem_sat Hmksrem Htt Hls1 Hls2) => Hcnfsrem.
    move : (mk_env_eq_newer_res Hmkeq ) => Hgeq.
    have Hnewcp : (newer_than_lits g (copy (size lrs_srem) lit_ff)).
    {
      exact : (newer_than_lits_copy (size lrs_srem) Hff).
    }
    have Hnewmsl: (newer_than_lits g [:: (splitmsl ls1).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls1) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc).
    }
    have Hnewmsl2 : (newer_than_lits g [:: (splitmsl ls2).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls2) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc) .
    }
    move : (mk_env_eq_sat Hmkeq2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem Hneweq)) (newer_than_lits_le_newer Hgsrem Hneweq) (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnewsrem Hneweq))) => Hcnfeq2.
    move : (mk_env_eq_newer_cnf Hmkeq2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem Hneweq)) (newer_than_lits_le_newer Hgsrem Hneweq) (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnewsrem Hneweq))) => Hcseq2.
    move : (mk_env_eq_sat Hmkeq (newer_than_lit_le_newer Htt Hnewsrem) (newer_than_lits_le_newer Hnewmsl Hnewsrem) (newer_than_lits_le_newer Hnewmsl2 Hnewsrem)) => Hcnfeq.
    move : (mk_env_eq_newer_cnf Hmkeq (newer_than_lit_le_newer Htt Hnewsrem) (newer_than_lits_le_newer Hnewmsl Hnewsrem) (newer_than_lits_le_newer Hnewmsl2 Hnewsrem)) => Hcseq.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer Hcssrem (pos_leb_trans Hneweq Hneweq2))).
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq2) (newer_than_cnf_le_newer Hcssrem Hneweq)).
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq) Hcssrem) Hcnfsrem.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) (newer_than_cnf_le_newer Hcseq Hneweq2)).
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq2) Hcseq) Hcnfeq.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkaddr) Hcseq2) Hcnfeq2.
    rewrite (mk_env_add_sat Hmkaddr (newer_than_lits_le_newer Hgsrem (pos_leb_trans Hneweq Hneweq2)) (newer_than_lits_le_newer Hls2 (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq Hneweq2))) (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq Hneweq2))))//.
  - rewrite /=.
    dcase (mk_env_or E_eq2 g_eq2 (copy (size ls2) r_eq) (copy (size ls2) r_eq2)) => [[[[E_or] g_or] cs_or] lrs_or] Hmkor.
    dcase (mk_env_not E_or g_or lrs_or) => [[[[E_not] g_not] cs_not ] lrs_not] Hmknot.
    dcase (mk_env_and E_not g_not ls2 lrs_not) => [[[[E_and] g_and] cs_and] lrs_and] Hmkand.
    dcase (mk_env_add E_and g_and lrs_srem lrs_and) => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    case => <- _ <- _; move => Htt Hls1 Hls2; generalize Htt; rewrite newer_than_lit_tt_ff; move => Hff.
    rewrite !interp_cnf_catrev.
    move : (mk_env_srem_newer_res Hmksrem Htt Hls1 Hls2) => Hgsrem.
    move : (mk_env_srem_newer_cnf Hmksrem Htt Hls1 Hls2) => Hcssrem.
    move : (mk_env_srem_sat Hmksrem Htt Hls1 Hls2) => Hcnfsrem.
    move : (mk_env_eq_newer_res Hmkeq ) => Hgeq.
    move : (mk_env_eq_newer_res Hmkeq2) => Hgeq2.
    have Hnewcp : (newer_than_lits g (copy (size lrs_srem) lit_ff)).
    {
      exact : (newer_than_lits_copy (size lrs_srem) Hff).
    }
    have Hnewcp2 : (newer_than_lits g_eq (copy (size ls2) r_eq)).
    {
      exact : (newer_than_lits_copy (size ls2) Hgeq).
    }
    have Hnewcp22 : (newer_than_lits g_eq2 (copy (size ls2) r_eq2)).
    {
      exact : (newer_than_lits_copy (size ls2) Hgeq2).
    }
    have Hnewmsl: (newer_than_lits g [:: (splitmsl ls1).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls1) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc).
    }
    have Hnewmsl2 : (newer_than_lits g [:: (splitmsl ls2).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls2) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc) .
    }
    move : (mk_env_eq_sat Hmkeq2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem Hneweq)) (newer_than_lits_le_newer Hgsrem Hneweq) (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnewsrem Hneweq))) => Hcnfeq2.
    move : (mk_env_eq_newer_cnf Hmkeq2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem Hneweq)) (newer_than_lits_le_newer Hgsrem Hneweq) (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnewsrem Hneweq))) => Hcseq2.
    move : (mk_env_eq_sat Hmkeq (newer_than_lit_le_newer Htt Hnewsrem) (newer_than_lits_le_newer Hnewmsl Hnewsrem) (newer_than_lits_le_newer Hnewmsl2 Hnewsrem)) => Hcnfeq.
    move : (mk_env_eq_newer_cnf Hmkeq (newer_than_lit_le_newer Htt Hnewsrem) (newer_than_lits_le_newer Hnewmsl Hnewsrem) (newer_than_lits_le_newer Hnewmsl2 Hnewsrem)) => Hcseq.
    move : (mk_env_or_newer_gen Hmkor) => Hnewor.
    move : (mk_env_or_newer_res Hmkor (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq Hneweq2))) (newer_than_lits_le_newer Hnewcp2 Hneweq2) Hnewcp22) => Hgor.
    move : (mk_env_or_sat Hmkor (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq Hneweq2))) (newer_than_lits_le_newer Hnewcp2 Hneweq2) Hnewcp22) => Hcnfor.
    move : (mk_env_or_newer_cnf Hmkor (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq Hneweq2))) (newer_than_lits_le_newer Hnewcp2 Hneweq2) Hnewcp22) => Hcsor.
    move : (mk_env_not_newer_gen Hmknot) => Hnewnot.
    move : (mk_env_not_newer_res Hmknot Hgor) => Hgnot.
    move : (mk_env_not_sat Hmknot Hgor) => Hcnfnot.
    move : (mk_env_not_newer_cnf Hmknot Hgor) => Hcsnot.
    move : (mk_env_and_newer_gen Hmkand) => Hnewand.
    move : (mk_env_and_newer_res Hmkand (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))) (newer_than_lits_le_newer Hls2 (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))) Hgnot) => Hgand.
    move : (mk_env_and_newer_cnf Hmkand (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))) (newer_than_lits_le_newer Hls2 (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))) Hgnot) => Hcsand.
    move : (mk_env_and_sat Hmkand (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))) (newer_than_lits_le_newer Hls2 (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))) Hgnot) => Hcnfand.
    move : (mk_env_add_newer_gen Hmkadd) => Hnewadd.
    move : (mk_env_add_newer_res Hmkadd) => Hgadd.
    move : (mk_env_add_sat Hmkadd (newer_than_lits_le_newer Hgsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))) Hgand (newer_than_lit_le_newer Hff (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))))) => Hcnfadd.
    move : (mk_env_add_newer_cnf Hmkadd (newer_than_lits_le_newer Hgsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))) Hgand (newer_than_lit_le_newer Hff (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))))) => Hcsadd.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) (newer_than_cnf_le_newer Hcssrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand)))))).
    rewrite (env_preserve_cnf (mk_env_and_preserve Hmkand) (newer_than_cnf_le_newer Hcssrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))).
    rewrite (env_preserve_cnf (mk_env_not_preserve Hmknot) (newer_than_cnf_le_newer Hcssrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 Hnewor)))).
    rewrite (env_preserve_cnf (mk_env_or_preserve Hmkor) (newer_than_cnf_le_newer Hcssrem (pos_leb_trans Hneweq Hneweq2))).
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq2) (newer_than_cnf_le_newer Hcssrem Hneweq)).
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq) Hcssrem) Hcnfsrem.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) (newer_than_cnf_le_newer Hcseq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))).
    rewrite (env_preserve_cnf (mk_env_and_preserve Hmkand) (newer_than_cnf_le_newer Hcseq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot)))).
    rewrite (env_preserve_cnf (mk_env_not_preserve Hmknot) (newer_than_cnf_le_newer Hcseq (pos_leb_trans Hneweq2 Hnewor))). 
    rewrite (env_preserve_cnf (mk_env_or_preserve Hmkor) (newer_than_cnf_le_newer Hcseq Hneweq2)).
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq2) Hcseq) Hcnfeq.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) (newer_than_cnf_le_newer Hcseq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand)))).
    rewrite (env_preserve_cnf (mk_env_and_preserve Hmkand) (newer_than_cnf_le_newer Hcseq2 (pos_leb_trans Hnewor Hnewnot))).
    rewrite (env_preserve_cnf (mk_env_not_preserve Hmknot) (newer_than_cnf_le_newer Hcseq2 Hnewor)).
    rewrite (env_preserve_cnf (mk_env_or_preserve Hmkor) Hcseq2) Hcnfeq2.
    rewrite (mk_env_add_sat Hmkadd (newer_than_lits_le_newer Hgsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))) Hgand (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))))).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) (newer_than_cnf_le_newer Hcsor (pos_leb_trans Hnewnot Hnewand))).
    rewrite (env_preserve_cnf (mk_env_and_preserve Hmkand) (newer_than_cnf_le_newer Hcsor Hnewnot)).
    rewrite (env_preserve_cnf (mk_env_not_preserve Hmknot) Hcsor) Hcnfor.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) (newer_than_cnf_le_newer Hcsnot Hnewand)).
    rewrite (env_preserve_cnf (mk_env_and_preserve Hmkand) Hcsnot) Hcnfnot.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) Hcsand) Hcnfand//.
  - rewrite /=.
    dcase (mk_env_add E_eq2 g_eq2 lrs_srem ls2) => [[[[E_add] g_add] cs_add] lrs_add] Hmkaddr.
    case => <- _ <- _; move => Htt Hls1 Hls2; generalize Htt; rewrite newer_than_lit_tt_ff; move => Hff.
    rewrite !interp_cnf_catrev.
    move : (mk_env_srem_newer_res Hmksrem Htt Hls1 Hls2) => Hgsrem.
    move : (mk_env_srem_newer_cnf Hmksrem Htt Hls1 Hls2) => Hcssrem.
    move : (mk_env_srem_sat Hmksrem Htt Hls1 Hls2) => Hcnfsrem.
    move : (mk_env_eq_newer_res Hmkeq ) => Hgeq.
    have Hnewcp : (newer_than_lits g (copy (size lrs_srem) lit_ff)).
    {
      exact : (newer_than_lits_copy (size lrs_srem) Hff).
    }
    have Hnewmsl: (newer_than_lits g [:: (splitmsl ls1).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls1) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc).
    }
    have Hnewmsl2 : (newer_than_lits g [:: (splitmsl ls2).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls2) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc) .
    }
    move : (mk_env_eq_sat Hmkeq2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem Hneweq)) (newer_than_lits_le_newer Hgsrem Hneweq) (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnewsrem Hneweq))) => Hcnfeq2.
    move : (mk_env_eq_newer_cnf Hmkeq2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem Hneweq)) (newer_than_lits_le_newer Hgsrem Hneweq) (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnewsrem Hneweq))) => Hcseq2.
    move : (mk_env_eq_sat Hmkeq (newer_than_lit_le_newer Htt Hnewsrem) (newer_than_lits_le_newer Hnewmsl Hnewsrem) (newer_than_lits_le_newer Hnewmsl2 Hnewsrem)) => Hcnfeq.
    move : (mk_env_eq_newer_cnf Hmkeq (newer_than_lit_le_newer Htt Hnewsrem) (newer_than_lits_le_newer Hnewmsl Hnewsrem) (newer_than_lits_le_newer Hnewmsl2 Hnewsrem)) => Hcseq.
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq2) (newer_than_cnf_le_newer Hcssrem Hneweq)).
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq) Hcssrem) Hcnfsrem.
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq2) Hcseq) Hcnfeq Hcnfeq2//.
  - rewrite /=.
    dcase (mk_env_or E_eq2 g_eq2 (copy (size ls2) r_eq) (copy (size ls2) r_eq2)) => [[[[E_or] g_or] cs_or] lrs_or] Hmkor.
    dcase (mk_env_not E_or g_or lrs_or) => [[[[E_not] g_not] cs_not ] lrs_not] Hmknot.
    dcase (mk_env_and E_not g_not ls2 lrs_not) => [[[[E_and] g_and] cs_and] lrs_and] Hmkand.
    dcase (mk_env_add E_and g_and lrs_srem lrs_and) => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    case => <- _ <- _; move => Htt Hls1 Hls2; generalize Htt; rewrite newer_than_lit_tt_ff; move => Hff.
    rewrite !interp_cnf_catrev.
    move : (mk_env_srem_newer_res Hmksrem Htt Hls1 Hls2) => Hgsrem.
    move : (mk_env_srem_newer_cnf Hmksrem Htt Hls1 Hls2) => Hcssrem.
    move : (mk_env_srem_sat Hmksrem Htt Hls1 Hls2) => Hcnfsrem.
    move : (mk_env_eq_newer_res Hmkeq ) => Hgeq.
    move : (mk_env_eq_newer_res Hmkeq2) => Hgeq2.
    have Hnewcp : (newer_than_lits g (copy (size lrs_srem) lit_ff)).
    {
      exact : (newer_than_lits_copy (size lrs_srem) Hff).
    }
    have Hnewcp2 : (newer_than_lits g_eq (copy (size ls2) r_eq)).
    {
      exact : (newer_than_lits_copy (size ls2) Hgeq).
    }
    have Hnewcp22 : (newer_than_lits g_eq2 (copy (size ls2) r_eq2)).
    {
      exact : (newer_than_lits_copy (size ls2) Hgeq2).
    }
    have Hnewmsl: (newer_than_lits g [:: (splitmsl ls1).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls1) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc).
    }
    have Hnewmsl2 : (newer_than_lits g [:: (splitmsl ls2).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls2) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc) .
    }
    move : (mk_env_eq_sat Hmkeq2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem Hneweq)) (newer_than_lits_le_newer Hgsrem Hneweq) (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnewsrem Hneweq))) => Hcnfeq2.
    move : (mk_env_eq_newer_cnf Hmkeq2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem Hneweq)) (newer_than_lits_le_newer Hgsrem Hneweq) (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnewsrem Hneweq))) => Hcseq2.
    move : (mk_env_eq_sat Hmkeq (newer_than_lit_le_newer Htt Hnewsrem) (newer_than_lits_le_newer Hnewmsl Hnewsrem) (newer_than_lits_le_newer Hnewmsl2 Hnewsrem)) => Hcnfeq.
    move : (mk_env_eq_newer_cnf Hmkeq (newer_than_lit_le_newer Htt Hnewsrem) (newer_than_lits_le_newer Hnewmsl Hnewsrem) (newer_than_lits_le_newer Hnewmsl2 Hnewsrem)) => Hcseq.
    move : (mk_env_or_newer_gen Hmkor) => Hnewor.
    move : (mk_env_or_newer_res Hmkor (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq Hneweq2))) (newer_than_lits_le_newer Hnewcp2 Hneweq2) Hnewcp22) => Hgor.
    move : (mk_env_or_sat Hmkor (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq Hneweq2))) (newer_than_lits_le_newer Hnewcp2 Hneweq2) Hnewcp22) => Hcnfor.
    move : (mk_env_or_newer_cnf Hmkor (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq Hneweq2))) (newer_than_lits_le_newer Hnewcp2 Hneweq2) Hnewcp22) => Hcsor.
    move : (mk_env_not_newer_gen Hmknot) => Hnewnot.
    move : (mk_env_not_newer_res Hmknot Hgor) => Hgnot.
    move : (mk_env_not_sat Hmknot Hgor) => Hcnfnot.
    move : (mk_env_not_newer_cnf Hmknot Hgor) => Hcsnot.
    move : (mk_env_and_newer_gen Hmkand) => Hnewand.
    move : (mk_env_and_newer_res Hmkand (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))) (newer_than_lits_le_newer Hls2 (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))) Hgnot) => Hgand.
    move : (mk_env_and_newer_cnf Hmkand (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))) (newer_than_lits_le_newer Hls2 (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))) Hgnot) => Hcsand.
    move : (mk_env_and_sat Hmkand (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))) (newer_than_lits_le_newer Hls2 (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))) Hgnot) => Hcnfand.
    move : (mk_env_add_newer_gen Hmkadd) => Hnewadd.
    move : (mk_env_add_newer_res Hmkadd) => Hgadd.
    move : (mk_env_add_sat Hmkadd (newer_than_lits_le_newer Hgsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))) Hgand (newer_than_lit_le_newer Hff (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))))) => Hcnfadd.
    move : (mk_env_add_newer_cnf Hmkadd (newer_than_lits_le_newer Hgsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))) Hgand (newer_than_lit_le_newer Hff (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))))) => Hcsadd.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) (newer_than_cnf_le_newer Hcssrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand)))))).
    rewrite (env_preserve_cnf (mk_env_and_preserve Hmkand) (newer_than_cnf_le_newer Hcssrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))).
    rewrite (env_preserve_cnf (mk_env_not_preserve Hmknot) (newer_than_cnf_le_newer Hcssrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 Hnewor)))).
    rewrite (env_preserve_cnf (mk_env_or_preserve Hmkor) (newer_than_cnf_le_newer Hcssrem (pos_leb_trans Hneweq Hneweq2))).
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq2) (newer_than_cnf_le_newer Hcssrem Hneweq)).
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq) Hcssrem) Hcnfsrem.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) (newer_than_cnf_le_newer Hcseq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))).
    rewrite (env_preserve_cnf (mk_env_and_preserve Hmkand) (newer_than_cnf_le_newer Hcseq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot)))).
    rewrite (env_preserve_cnf (mk_env_not_preserve Hmknot) (newer_than_cnf_le_newer Hcseq (pos_leb_trans Hneweq2 Hnewor))). 
    rewrite (env_preserve_cnf (mk_env_or_preserve Hmkor) (newer_than_cnf_le_newer Hcseq Hneweq2)).
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq2) Hcseq) Hcnfeq.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) (newer_than_cnf_le_newer Hcseq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand)))).
    rewrite (env_preserve_cnf (mk_env_and_preserve Hmkand) (newer_than_cnf_le_newer Hcseq2 (pos_leb_trans Hnewor Hnewnot))).
    rewrite (env_preserve_cnf (mk_env_not_preserve Hmknot) (newer_than_cnf_le_newer Hcseq2 Hnewor)).
    rewrite (env_preserve_cnf (mk_env_or_preserve Hmkor) Hcseq2) Hcnfeq2.
    rewrite (mk_env_add_sat Hmkadd (newer_than_lits_le_newer Hgsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))) Hgand (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))))).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) (newer_than_cnf_le_newer Hcsor (pos_leb_trans Hnewnot Hnewand))).
    rewrite (env_preserve_cnf (mk_env_and_preserve Hmkand) (newer_than_cnf_le_newer Hcsor Hnewnot)).
    rewrite (env_preserve_cnf (mk_env_not_preserve Hmknot) Hcsor) Hcnfor.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) (newer_than_cnf_le_newer Hcsnot Hnewand)).
    rewrite (env_preserve_cnf (mk_env_and_preserve Hmkand) Hcsnot) Hcnfnot.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) Hcsand) Hcnfand//.
  - rewrite /=.
    dcase (mk_env_or E_eq2 g_eq2 (copy (size ls2) r_eq) (copy (size ls2) r_eq2)) => [[[[E_or] g_or] cs_or] lrs_or] Hmkor.
    dcase (mk_env_not E_or g_or lrs_or) => [[[[E_not] g_not] cs_not ] lrs_not] Hmknot.
    dcase (mk_env_and E_not g_not ls2 lrs_not) => [[[[E_and] g_and] cs_and] lrs_and] Hmkand.
    dcase (mk_env_add E_and g_and lrs_srem lrs_and) => [[[[E_add] g_add] cs_add] lrs_add] Hmkadd.
    case => <- _ <- _; move => Htt Hls1 Hls2; generalize Htt; rewrite newer_than_lit_tt_ff; move => Hff.
    rewrite !interp_cnf_catrev.
    move : (mk_env_srem_newer_res Hmksrem Htt Hls1 Hls2) => Hgsrem.
    move : (mk_env_srem_newer_cnf Hmksrem Htt Hls1 Hls2) => Hcssrem.
    move : (mk_env_srem_sat Hmksrem Htt Hls1 Hls2) => Hcnfsrem.
    move : (mk_env_eq_newer_res Hmkeq ) => Hgeq.
    move : (mk_env_eq_newer_res Hmkeq2) => Hgeq2.
    have Hnewcp : (newer_than_lits g (copy (size lrs_srem) lit_ff)).
    {
      exact : (newer_than_lits_copy (size lrs_srem) Hff).
    }
    have Hnewcp2 : (newer_than_lits g_eq (copy (size ls2) r_eq)).
    {
      exact : (newer_than_lits_copy (size ls2) Hgeq).
    }
    have Hnewcp22 : (newer_than_lits g_eq2 (copy (size ls2) r_eq2)).
    {
      exact : (newer_than_lits_copy (size ls2) Hgeq2).
    }
    have Hnewmsl: (newer_than_lits g [:: (splitmsl ls1).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls1) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc).
    }
    have Hnewmsl2 : (newer_than_lits g [:: (splitmsl ls2).2]).
    {
      move/andP : (newer_than_lits_splitmsl Htt Hls2) => [_ Hnewc].
      exact : (newer_than_lits_copy 1 Hnewc) .
    }
    move : (mk_env_eq_sat Hmkeq2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem Hneweq)) (newer_than_lits_le_newer Hgsrem Hneweq) (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnewsrem Hneweq))) => Hcnfeq2.
    move : (mk_env_eq_newer_cnf Hmkeq2 (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem Hneweq)) (newer_than_lits_le_newer Hgsrem Hneweq) (newer_than_lits_le_newer Hnewcp (pos_leb_trans Hnewsrem Hneweq))) => Hcseq2.
    move : (mk_env_eq_sat Hmkeq (newer_than_lit_le_newer Htt Hnewsrem) (newer_than_lits_le_newer Hnewmsl Hnewsrem) (newer_than_lits_le_newer Hnewmsl2 Hnewsrem)) => Hcnfeq.
    move : (mk_env_eq_newer_cnf Hmkeq (newer_than_lit_le_newer Htt Hnewsrem) (newer_than_lits_le_newer Hnewmsl Hnewsrem) (newer_than_lits_le_newer Hnewmsl2 Hnewsrem)) => Hcseq.
    move : (mk_env_or_newer_gen Hmkor) => Hnewor.
    move : (mk_env_or_newer_res Hmkor (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq Hneweq2))) (newer_than_lits_le_newer Hnewcp2 Hneweq2) Hnewcp22) => Hgor.
    move : (mk_env_or_sat Hmkor (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq Hneweq2))) (newer_than_lits_le_newer Hnewcp2 Hneweq2) Hnewcp22) => Hcnfor.
    move : (mk_env_or_newer_cnf Hmkor (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq Hneweq2))) (newer_than_lits_le_newer Hnewcp2 Hneweq2) Hnewcp22) => Hcsor.
    move : (mk_env_not_newer_gen Hmknot) => Hnewnot.
    move : (mk_env_not_newer_res Hmknot Hgor) => Hgnot.
    move : (mk_env_not_sat Hmknot Hgor) => Hcnfnot.
    move : (mk_env_not_newer_cnf Hmknot Hgor) => Hcsnot.
    move : (mk_env_and_newer_gen Hmkand) => Hnewand.
    move : (mk_env_and_newer_res Hmkand (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))) (newer_than_lits_le_newer Hls2 (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))) Hgnot) => Hgand.
    move : (mk_env_and_newer_cnf Hmkand (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))) (newer_than_lits_le_newer Hls2 (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))) Hgnot) => Hcsand.
    move : (mk_env_and_sat Hmkand (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))) (newer_than_lits_le_newer Hls2 (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))) Hgnot) => Hcnfand.
    move : (mk_env_add_newer_gen Hmkadd) => Hnewadd.
    move : (mk_env_add_newer_res Hmkadd) => Hgadd.
    move : (mk_env_add_sat Hmkadd (newer_than_lits_le_newer Hgsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))) Hgand (newer_than_lit_le_newer Hff (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))))) => Hcnfadd.
    move : (mk_env_add_newer_cnf Hmkadd (newer_than_lits_le_newer Hgsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))) Hgand (newer_than_lit_le_newer Hff (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))))) => Hcsadd.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) (newer_than_cnf_le_newer Hcssrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand)))))).
    rewrite (env_preserve_cnf (mk_env_and_preserve Hmkand) (newer_than_cnf_le_newer Hcssrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot))))).
    rewrite (env_preserve_cnf (mk_env_not_preserve Hmknot) (newer_than_cnf_le_newer Hcssrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 Hnewor)))).
    rewrite (env_preserve_cnf (mk_env_or_preserve Hmkor) (newer_than_cnf_le_newer Hcssrem (pos_leb_trans Hneweq Hneweq2))).
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq2) (newer_than_cnf_le_newer Hcssrem Hneweq)).
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq) Hcssrem) Hcnfsrem.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) (newer_than_cnf_le_newer Hcseq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))).
    rewrite (env_preserve_cnf (mk_env_and_preserve Hmkand) (newer_than_cnf_le_newer Hcseq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor Hnewnot)))).
    rewrite (env_preserve_cnf (mk_env_not_preserve Hmknot) (newer_than_cnf_le_newer Hcseq (pos_leb_trans Hneweq2 Hnewor))). 
    rewrite (env_preserve_cnf (mk_env_or_preserve Hmkor) (newer_than_cnf_le_newer Hcseq Hneweq2)).
    rewrite (env_preserve_cnf (mk_env_eq_preserve Hmkeq2) Hcseq) Hcnfeq.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) (newer_than_cnf_le_newer Hcseq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand)))).
    rewrite (env_preserve_cnf (mk_env_and_preserve Hmkand) (newer_than_cnf_le_newer Hcseq2 (pos_leb_trans Hnewor Hnewnot))).
    rewrite (env_preserve_cnf (mk_env_not_preserve Hmknot) (newer_than_cnf_le_newer Hcseq2 Hnewor)).
    rewrite (env_preserve_cnf (mk_env_or_preserve Hmkor) Hcseq2) Hcnfeq2.
    rewrite (mk_env_add_sat Hmkadd (newer_than_lits_le_newer Hgsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))) Hgand (newer_than_lit_le_newer Htt (pos_leb_trans Hnewsrem (pos_leb_trans Hneweq (pos_leb_trans Hneweq2 (pos_leb_trans Hnewor (pos_leb_trans Hnewnot Hnewand))))))).
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) (newer_than_cnf_le_newer Hcsor (pos_leb_trans Hnewnot Hnewand))).
    rewrite (env_preserve_cnf (mk_env_and_preserve Hmkand) (newer_than_cnf_le_newer Hcsor Hnewnot)).
    rewrite (env_preserve_cnf (mk_env_not_preserve Hmknot) Hcsor) Hcnfor.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) (newer_than_cnf_le_newer Hcsnot Hnewand)).
    rewrite (env_preserve_cnf (mk_env_and_preserve Hmkand) Hcsnot) Hcnfnot.
    rewrite (env_preserve_cnf (mk_env_add_preserve Hmkadd) Hcsand) Hcnfand//.
Qed.
  
