From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBConst BBAnd BBOr BBAdd BBShl BBSub BBMul BBLshr BBUle BBUge BBEq BBNot BBIte.
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== bit_blast_udiv ===== *)


Fixpoint bit_blast_udiv_rec g ls1 ls2 qs rs :  generator * cnf * word * word :=
  match ls1 with
  | [::] => (g, [::], qs, rs)
  | ls1_hd :: ls1_tl =>
    let di := dropmsl (joinlsl ls1_hd rs) in
    let '(g_uge, cs_uge, lrs_uge) := bit_blast_uge g di ls2 in
    let qi := dropmsl (joinlsl lrs_uge qs) in
    if (lrs_uge == lit_tt) then
      let '(g_sub, cs_sub, lrs_sub) := bit_blast_sub g_uge di ls2 in
      let '(g_tl, cs_tl, lqs_tl, lrs_tl) := bit_blast_udiv_rec g_sub ls1_tl ls2 qi lrs_sub in
      (g_tl, (catrev (catrev cs_tl cs_sub) cs_uge), lqs_tl, lrs_tl)
    else if (lrs_uge == lit_ff) then
           let '(g_tl, cs_tl, lqs_tl, lrs_tl) := bit_blast_udiv_rec g_uge ls1_tl ls2 qi di in
           (g_tl, catrev cs_tl cs_uge, lqs_tl, lrs_tl)
         else let '(g_and, cs_and, lrs_and) := bit_blast_and g_uge (copy (size ls2) lrs_uge) ls2 in
              let '(g_sub2, cs_sub2, lrs_sub2) := bit_blast_sub g_and di lrs_and in
              let '(g_tl, cs_tl, lrs_tl, lqs_tl) := bit_blast_udiv_rec g_sub2 ls1_tl ls2 qi lrs_sub2 in
              (g_tl, (catrev (catrev (catrev cs_tl cs_sub2) cs_and) cs_uge), lrs_tl, lqs_tl)
  end.

Definition bit_blast_udiv g ls1' ls2 :=
  let ls1 := rev ls1' in
  let '(g_eq, cs_eq, lrs_eq) := bit_blast_eq g ls2 (copy (size ls2) lit_ff) in
  if lrs_eq == lit_tt then
    (g_eq, cs_eq, copy (size ls2) lit_tt, ls1')
  else if lrs_eq == lit_ff then
    let '(g_udivr, cs_udivr, lqs_udivr, lrs_udivr) :=
        bit_blast_udiv_rec g_eq ls1 ls2 (copy (size ls1) lit_ff) (copy (size ls1) lit_ff)
    in (g_udivr, catrev cs_udivr cs_eq, lqs_udivr, lrs_udivr)
       else
         let '(g_udivr, cs_udivr, lqs_udivr, lrs_udivr) :=
             bit_blast_udiv_rec g_eq ls1 ls2 (copy (size ls1) lit_ff) (copy (size ls1) lit_ff) in 
         let '(g_or, cs_or, lrs_or) := bit_blast_or g_udivr (copy (size lqs_udivr) (lrs_eq)) lqs_udivr  in
         let '(g_ite, cs_ite, lrs_ite) := bit_blast_ite g_or lrs_eq ls1' lrs_udivr in
         (g_ite, catrev (catrev (catrev cs_ite cs_or) cs_udivr) cs_eq, lrs_or, lrs_ite).

Definition bit_blast_udiv' g ls1 ls2 :=
  let '(g_udiv, cs_udiv, q_udiv, r_udiv) := bit_blast_udiv g ls1 ls2 in (g_udiv, cs_udiv, q_udiv).

Fixpoint mk_env_udiv_rec E g ls1 ls2 qs rs : env * generator * cnf * word * word :=
  match ls1 with
  | [::] => (E, g, [::], qs, rs)
  | ls1_hd :: ls1_tl =>
    let di := dropmsl (joinlsl ls1_hd rs) in
    let '(E_uge, g_uge, cs_uge, lrs_uge) := mk_env_uge E g di ls2 in
    let qi := dropmsl (joinlsl lrs_uge qs) in
    if (lrs_uge == lit_tt) then
      let '(E_sub, g_sub, cs_sub, lrs_sub) := mk_env_sub E_uge g_uge di ls2 in
      let '(E_tl, g_tl, cs_tl, lqs_tl, lrs_tl) := mk_env_udiv_rec E_sub g_sub ls1_tl ls2 qi lrs_sub in
      (E_tl, g_tl, (catrev (catrev cs_tl cs_sub) cs_uge), lqs_tl, lrs_tl)
    else if (lrs_uge == lit_ff) then
           let '(E_tl, g_tl, cs_tl, lqs_tl, lrs_tl) := mk_env_udiv_rec E_uge g_uge ls1_tl ls2 qi di in
           (E_tl, g_tl, catrev cs_tl cs_uge, lqs_tl, lrs_tl)
         else let '(E_and, g_and, cs_and, lrs_and) := mk_env_and E_uge g_uge (copy (size ls2) lrs_uge) ls2 in
              let '(E_sub2, g_sub2, cs_sub2, lrs_sub2) := mk_env_sub E_and g_and di lrs_and in
              let '(E_tl, g_tl, cs_tl, lrs_tl, lqs_tl) := mk_env_udiv_rec E_sub2 g_sub2 ls1_tl ls2 qi lrs_sub2 in
              (E_tl, g_tl, (catrev (catrev (catrev cs_tl cs_sub2) cs_and) cs_uge), lrs_tl, lqs_tl)
  end.

Definition mk_env_udiv E g ls1' ls2 :=
  let ls1 := rev ls1' in
  let '(E_eq, g_eq, cs_eq, lrs_eq) := mk_env_eq E g ls2 (copy (size ls2) lit_ff) in
  if lrs_eq == lit_tt then
    (E_eq, g_eq, cs_eq, copy (size ls2) lit_tt, ls1')
  else if lrs_eq == lit_ff then
    let '(E_udivr, g_udivr, cs_udivr, lqs_udivr, lrs_udivr) :=
        mk_env_udiv_rec E_eq g_eq ls1 ls2 (copy (size ls1) lit_ff) (copy (size ls1) lit_ff)
    in (E_udivr, g_udivr, catrev cs_udivr cs_eq, lqs_udivr, lrs_udivr)
       else
         let '(E_udivr, g_udivr, cs_udivr, lqs_udivr, lrs_udivr) :=
             mk_env_udiv_rec E_eq g_eq ls1 ls2 (copy (size ls1) lit_ff) (copy (size ls1) lit_ff) in
         let '(E_or, g_or, cs_or, lrs_or) := mk_env_or E_udivr g_udivr (copy (size lqs_udivr) (lrs_eq)) lqs_udivr  in
         let '(E_ite, g_ite, cs_ite, lrs_ite) := mk_env_ite E_or g_or lrs_eq ls1' lrs_udivr in
         (E_ite, g_ite, catrev (catrev (catrev cs_ite cs_or) cs_udivr) cs_eq, lrs_or, lrs_ite).

Definition mk_env_udiv' E g ls1 ls2 :=
  let '(E_udiv, g_udiv, cs_udiv, q_udiv, r_udiv) := mk_env_udiv E g ls1 ls2 in (E_udiv, g_udiv, cs_udiv, q_udiv).

Lemma bit_blast_sub_size_ss : forall g ls1 ls2 g' cs' lrs,
    bit_blast_sub g ls1 ls2  = (g', cs', lrs) -> size ls1 = size ls2 -> size lrs = size ls2.
Proof.
  move => g ls1 ls2 g' cs lrs. rewrite/bit_blast_sub.
  case Hbbneg : (BBNeg.bit_blast_neg g ls2) => [[g_neg cs_neg] lrs_neg].
  case Hbbadd : (bit_blast_add g_neg ls1 lrs_neg) => [[ g_add cs_add] lrs_add].
  case => _ _ <- Hsz12. move: (bit_blast_neg_size_ss Hbbneg)=>Hszneg; rewrite Hszneg in Hsz12. rewrite-( bit_blast_add_size_ss Hbbadd Hsz12). by rewrite Hszneg Hsz12.
Qed.

Lemma bit_blast_udiv_rec_size_ss : forall g ls1 ls2 g' qs rs cs' qlrs rlrs  ,
    bit_blast_udiv_rec g ls1 ls2 qs rs = (g', cs', qlrs, rlrs) ->
    size qs = size ls2 -> size rs = size ls2 ->
    (size qlrs = size ls2 /\ size rlrs = size ls2).
Proof.
  move => g ls1; move : g.
  elim ls1 => [|ls1hd ls1tl IH] g ls2 g' qs rs cs' qlrs rlrs  Hbbdiv Hszqs Hszrs ; move : Hbbdiv; rewrite/bit_blast_udiv/=.
  case => _ _ <- <-; done.
  case Hbbuge: (bit_blast_uge g (dropmsl (joinlsl ls1hd rs)) ls2)=> [[g_hd cs_hd] lrs_hd].
  case Hbbsub : (bit_blast_sub g_hd (dropmsl (joinlsl ls1hd rs)) ls2) => [[g_sub cs_sub] lrs_sub].
  case Hbband : (bit_blast_and g_hd (copy (size ls2) lrs_hd) ls2) => [[g_and cs_and] lrs_and].
  case Hbbsub2 : (bit_blast_sub g_and (dropmsl (joinlsl ls1hd rs)) lrs_and) => [[g_sub2 cs_sub2] lrs_sub2].
  case Hbbdiv : (bit_blast_udiv_rec g_sub ls1tl ls2 (dropmsl (joinlsl lrs_hd qs)) lrs_sub) => [[[g_tl cs_tl] lrs_tl] lqs_tl].
  case Hbbdiv2 : (bit_blast_udiv_rec g_hd ls1tl ls2 (dropmsl (joinlsl lrs_hd qs)) (dropmsl (joinlsl ls1hd rs))) => [[[g_tl2 cs_tl2] lrs_tl2] lqs_tl2].
  case Hbbdiv3 : (bit_blast_udiv_rec g_sub2 ls1tl ls2 (dropmsl (joinlsl lrs_hd qs)) lrs_sub2)=> [[[g_tl3 cs_tl3] lrs_tl3] lqs_tl3].
  have Hszdj : (size (dropmsl (joinlsl lrs_hd qs)) = size ls2) by rewrite size_dropmsl size_joinlsl addnK Hszqs.
  have Hszdj2: (size (dropmsl (joinlsl ls1hd rs)) = size ls2) by rewrite size_dropmsl size_joinlsl addnK Hszrs.
  move : (bit_blast_sub_size_ss Hbbsub Hszdj2) => Hszsub.
  have Hszcp : (size (copy (size ls2) lrs_hd) = size ls2 ) by rewrite size_nseq.
  move : (bit_blast_and_size_ss Hbband Hszcp) => Hszand.
  have Hszdj3 : (size (dropmsl (joinlsl ls1hd rs)) = size lrs_and) by rewrite size_dropmsl size_joinlsl addnK Hszrs -Hszand size_nseq.
  move : (bit_blast_sub_size_ss Hbbsub2 Hszdj3) => Hszsub2. generalize Hszsub2; move => Hszsub3. rewrite -Hszdj3 size_dropmsl size_joinlsl addnK Hszrs in Hszsub3.
  move : (IH _ _ _ _ _ _ _ _ Hbbdiv Hszdj Hszsub) => [Hszlrstl Hszlqstl].
  move : (IH _ _ _ _ _ _ _ _ Hbbdiv2 Hszdj Hszdj2) => [Hszlrstl2 Hszlqstl2].
  move : (IH _ _ _ _ _ _ _ _ Hbbdiv3 Hszdj Hszsub3) => [Hszlrstl3 Hszlqstl3].
  case Hhdtt : (lrs_hd == lit_tt). (case => _ _ <- <-). done.
  case Hhdff :(lrs_hd == lit_ff); case => _ _ <- <-; done.
Qed.

Lemma bit_blast_udiv_size_ss : forall g ls1 ls2 g' cs qlrs rlrs ,
    bit_blast_udiv g ls1 ls2 = (g', cs, qlrs, rlrs) -> size ls1 = size ls2->
    (size qlrs = size ls2 /\ size rlrs = size ls2).
Proof.
  move => g ls1 ls2 g' cs qlrs rlrs .
  rewrite/bit_blast_udiv.
  dcase (bit_blast_eq g ls2 (copy (size ls2) lit_ff)) => [[[g_eq] cs_eq] lrs_eq] Hbbeq.
  case Hbbudivr: (bit_blast_udiv_rec g_eq (rev ls1) ls2 (copy (size (rev ls1)) lit_ff)
        (copy (size (rev ls1)) lit_ff) ) => [[[g_udivr cs_udivr] lqs_udivr] lrs_udir].
  dcase (bit_blast_or g_udivr (copy (size lqs_udivr) (lrs_eq)) lqs_udivr) => [[[g_or] cs_or] lrs_or] Hbbor.
  dcase (bit_blast_ite g_or lrs_eq (ls1) lrs_udir) => [[[g_ite] cs_ite] lrs_ite] Hbbite.
  case Hls2t : (lrs_eq == lit_tt).
  case => _ _ <- <-. move => Hsz . by rewrite size_nseq Hsz.
  case Hls2f : (lrs_eq == lit_ff).
  case => _ _ <- <-.
  move => Hsz12. have Hszcp : size (copy (size (rev ls1)) lit_ff) = size ls2 by rewrite size_nseq size_rev.
  exact : (bit_blast_udiv_rec_size_ss Hbbudivr Hszcp Hszcp).
  case => _ _ <- <-.
  move => Hsz12.
  have Hszcp : size (copy (size (rev ls1)) lit_ff) = size ls2 by rewrite size_nseq size_rev.
  move : (bit_blast_udiv_rec_size_ss Hbbudivr Hszcp Hszcp) => [Hszuq Hszur].
  have Hszaux :size (copy (size lqs_udivr) lrs_eq) = size lqs_udivr by rewrite size_nseq.
  have Hszaux' : size ls1 = size lrs_udir by rewrite Hszur.
  move : (bit_blast_ite_size_ss Hbbite Hszaux') => Hszite.
  move : (bit_blast_or_size_ss Hbbor Hszaux) => Hszn. rewrite Hszn size_nseq Hszite //.
Qed.

Lemma bit_blast_udiv_size_ss' g ls1 ls2 g' cs qlrs :
    bit_blast_udiv' g ls1 ls2 = (g', cs, qlrs) -> size ls1 = size ls2->
    size qlrs = size ls2.
Proof.
  rewrite /bit_blast_udiv'. dcase (bit_blast_udiv g ls1 ls2) => [[[[g_u cs_u] q_u] r_u] Hbbu].
  case => _ _ <- Hsz. by move : (bit_blast_udiv_size_ss Hbbu Hsz) => [H _].
Qed.

Lemma bit_blast_udiv_rec_correct : forall ls1 g ls2 g' cs' lqs lrs qlrs rlrs E bs1 bs2 bsq bsr,
    bit_blast_udiv_rec g ls1 ls2 lqs lrs = (g', cs', qlrs, rlrs) ->
    size lqs = size ls2 -> size lrs = size ls2 ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    enc_bits E lqs bsq->
    enc_bits E lrs bsr ->
    interp_cnf E (add_prelude cs') ->
    enc_bits E qlrs (udivB_rec bs1 bs2 bsq bsr).1 /\
    enc_bits E rlrs (udivB_rec bs1 bs2 bsq bsr).2.
Proof.
  elim => [| ls1hd ls1tl IH] g ls2 g' cs' lqs lrs qlrs rlrs E bs1 bs2 bsq bsr.
  rewrite/bit_blast_udiv_rec. case => _ <- <- <-.
  rewrite enc_bits_nil_l.
  move => Hsz1 Hsz2. move => Hnil; rewrite (eqP Hnil)/=. done.
  rewrite /bit_blast_udiv_rec. rewrite-/bit_blast_udiv_rec.
  dcase (bit_blast_uge g (dropmsl (joinlsl ls1hd lrs)) ls2) => [[[guge] csuge] lrsuge] Hbbuge.
  dcase (bit_blast_sub guge (dropmsl (joinlsl ls1hd lrs)) ls2) =>[[[gsub] cssub] lrssub] Hbbsub.
  dcase (bit_blast_udiv_rec gsub ls1tl ls2 (dropmsl (joinlsl lrsuge lqs)) lrssub)=> [[[[gudivr] csudivr] lqrudivr] lrsudivr] Hbbudivr.
  case Hbbudivr2 : (bit_blast_udiv_rec guge ls1tl ls2 (dropmsl (joinlsl lrsuge lqs))) => [[[gudivr2 csudivr2] lqrudivr2] lrsudivr2].
  dcase (bit_blast_and guge (copy (size ls2) lrsuge) ls2) =>[[[gand] csand] lrsand] Hbband.
  dcase (bit_blast_sub gand (dropmsl (joinlsl ls1hd lrs)) lrsand) => [[[gsub2] cssub2] lrssub2] Hbbsub2.
  dcase (bit_blast_udiv_rec gsub2 ls1tl ls2 (dropmsl (joinlsl lrsuge lqs)) lrssub2) => [[[[gudivr3] csudivr3] lqrudivr3] lrsudivr3] Hudivr3.
  case bs1 => [| bs1hd bs1tl ]; first by rewrite enc_bits_nil_r.
  case Hlrsuget : (lrsuge == lit_tt).
  - case => _ <- <- <-.
    rewrite enc_bits_cons.
    move => Hszlqs Hszlrs. move/andP => [Hencls1hd Hencls1tl].
    move => Henc2 Hencq Hencr.
    rewrite add_prelude_expand !interp_cnf_catrev.
    move/andP => [Htt Hand]. move/andP : Hand => [Hcsudivr Hcsuge]. move/andP: Hcsudivr => [Hcsudivr Hcssub].
    rewrite/=.
    have Hszuge : size (dropmsl (joinlsl ls1hd lrs)) = size ls2 by rewrite size_dropmsl size_joinlsl addnK Hszlrs.
    have Hencjl : enc_bits E (joinlsl ls1hd lrs) (joinlsb bs1hd bsr) by rewrite enc_bits_joinlsb Hencls1hd Hencr.
    have Hencuge1 : enc_bits E (dropmsl (joinlsl ls1hd lrs)) (dropmsb (joinlsb bs1hd bsr)) by rewrite (enc_bits_dropmsb Htt Hencjl).
    have Hevar : E var_tt. done.
    move : (add_prelude_to Hevar Hcsuge) => Haddcsuge.
    move : (bit_blast_uge_correct Hbbuge Hszuge Hencuge1 Henc2 Haddcsuge) => Hencugers.
    rewrite (eqP Hlrsuget) in Hencugers.
    move : (add_prelude_enc_bit_true  (dropmsb (joinlsb bs1hd bsr) >=# bs2)%bits Haddcsuge) .
    have Hszbs2 : size bs2 = size (dropmsb (joinlsb bs1hd bsr))
      by rewrite (enc_bits_size Henc2) (enc_bits_size Hencuge1) in Hszuge.
    rewrite Hencugers /geB (leBNlt Hszbs2) => {Hszbs2}.
    move => HnotltB. symmetry in HnotltB. rewrite ->Bool.negb_true_iff in HnotltB.
    (* rewrite to_nat_ltB in HnotltB.  *) rewrite HnotltB/=.
    have Hszudiv1 : size (dropmsl (joinlsl lrsuge lqs)) = size ls2 by rewrite size_dropmsl size_joinlsl addnK Hszlqs.
    move : (bit_blast_sub_size_ss Hbbsub Hszuge) => Hszsub.
    move : (add_prelude_to Hevar Hcssub) => Haddcssub.
    move : (bit_blast_sub_correct Hbbsub Hencuge1 Henc2 Haddcssub Hszuge) => Hencsublrs.
    have Hencjtq : (enc_bits E (joinlsl lit_tt lqs) (joinlsb true bsq)) by rewrite enc_bits_joinlsb (add_prelude_enc_bit_true _ Haddcssub) Hencq.
    have Hencdjlqs : enc_bits E (dropmsl (joinlsl lrsuge lqs)) (dropmsb (joinlsb true bsq)) by rewrite (eqP Hlrsuget) (enc_bits_dropmsb Htt Hencjtq).
    move : (add_prelude_to Hevar Hcsudivr) => Haddcsudivr.
    exact : (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Hbbudivr Hszudiv1 Hszsub Hencls1tl Henc2 Hencdjlqs Hencsublrs Haddcsudivr).
  - case Hlrsugef : (lrsuge == lit_ff).
    + case => _ <- <- <-.
      rewrite enc_bits_cons.
      move => Hszlqs Hszlrs. move/andP => [Hencls1hd Hencls1tl].
      move => Henc2 Hencq Hencr.
      rewrite add_prelude_expand !interp_cnf_catrev.
      move/andP => [Htt Hudivr]. move/andP : Hudivr => [Hcsudivr Hcsuge].
      rewrite/=.
      have Hszuge : size (dropmsl (joinlsl lrsuge lqs)) = size ls2 by rewrite size_dropmsl size_joinlsl addnK Hszlqs.
      have Hszudivr : size (dropmsl (joinlsl ls1hd lrs)) = size ls2 by rewrite size_dropmsl size_joinlsl addnK Hszlrs.
      have Hencjl : enc_bits E (joinlsl ls1hd lrs) (joinlsb bs1hd bsr) by rewrite enc_bits_joinlsb Hencls1hd Hencr.
      have Hencuge1 : enc_bits E (dropmsl (joinlsl ls1hd lrs)) (dropmsb (joinlsb bs1hd bsr)) by rewrite (enc_bits_dropmsb Htt Hencjl).
      have Hevar : E var_tt. done.
      move : (add_prelude_to Hevar Hcsuge) => Haddcsuge.
      move : (bit_blast_uge_correct Hbbuge Hszudivr Hencuge1 Henc2 Haddcsuge) => Hencugers.
      rewrite (eqP Hlrsugef) in Hencugers.
      move : (add_prelude_enc_bit_is_not_true (dropmsb (joinlsb bs1hd bsr) >=# bs2)%bits Haddcsuge) .
      have Hszbs2 : size bs2 = size (dropmsb (joinlsb bs1hd bsr))
        by rewrite (enc_bits_size Henc2) (enc_bits_size Hencuge1) in Hszudivr.
      rewrite Hencugers /geB (leBNlt Hszbs2) Bool.negb_involutive => {Hszbs2}. 
      move => HnotltB. 
      (* rewrite to_nat_ltB in HnotltB. *) rewrite -HnotltB/=.
      have Hencjtq : (enc_bits E (joinlsl lrsuge lqs) (joinlsb false bsq)) by rewrite enc_bits_joinlsb (eqP Hlrsugef) (add_prelude_enc_bit_is_not_true _ Haddcsuge) Hencq. 
      have Hencdjlqs : enc_bits E (dropmsl (joinlsl lrsuge lqs)) (dropmsb (joinlsb false bsq)) by rewrite (enc_bits_dropmsb Htt Hencjtq).
      move : (add_prelude_to Hevar Hcsudivr) => Haddcsudivr.
      exact : (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Hbbudivr2 Hszuge Hszudivr Hencls1tl Henc2 Hencdjlqs Hencuge1 Haddcsudivr).
    + case => _ <- <- <-.
      rewrite enc_bits_cons.
      move => Hszlqs Hszlrs. move/andP => [Hencls1hd Hencls1tl].
      move => Henc2 Hencq Hencr.
      rewrite add_prelude_expand !interp_cnf_catrev.
      move/andP => [Htt Hudivr]. move/andP : Hudivr => [Hcsudivr Hcsuge].
      move/andP : Hcsudivr => [Hcsudivr Hcsand].
      move/andP : Hcsudivr => [Hcsudivr Hcssub].
      rewrite/=.
      have Hszuge : size (dropmsl (joinlsl ls1hd lrs)) = size ls2 by rewrite size_dropmsl size_joinlsl addnK Hszlrs.
      have Hencjl : enc_bits E (joinlsl ls1hd lrs) (joinlsb bs1hd bsr) by rewrite enc_bits_joinlsb Hencls1hd Hencr.
      have Hencuge1 : enc_bits E (dropmsl (joinlsl ls1hd lrs)) (dropmsb (joinlsb bs1hd bsr)) by rewrite (enc_bits_dropmsb Htt Hencjl).
      have Hevar : E var_tt by done.
      move : (add_prelude_to Hevar Hcsuge) => Haddcsuge.
      move : (bit_blast_uge_correct Hbbuge Hszuge Hencuge1 Henc2 Haddcsuge) => Hencugers.
      have Hszbs2 : size bs2 = size (dropmsb (joinlsb bs1hd bsr))
        by rewrite (enc_bits_size Henc2) (enc_bits_size Hencuge1) in Hszuge.
      rewrite /geB (leBNlt Hszbs2) (*to_nat_ltB*) in Hencugers => {Hszbs2}.
      have Hszand : size (copy (size ls2) lrsuge) = size ls2 by rewrite size_nseq.
      have Hszbs2 : size bs2 = size (dropmsb (joinlsb bs1hd bsr)) by rewrite size_dropmsb size_joinlsb addnK -(enc_bits_size Henc2) -(enc_bits_size Hencr)//.
      have Henccp : enc_bits E (copy (size ls2) lrsuge) (copy (size ls2) ((bs2 <=# (dropmsb (joinlsb bs1hd bsr)))%bits)). rewrite leBNlt// (enc_bits_copy (size ls2) Hencugers)//.
      move : (add_prelude_to Hevar Hcsand) => Haddcsand.
      move : (bit_blast_and_correct Hbband Henccp Henc2 Haddcsand) => Hencandrs.
      move : (bit_blast_and_size_ss Hbband Hszand) => Hszandrs.
      have Hszsub : size (dropmsl (joinlsl ls1hd lrs)) = size lrsand by rewrite size_dropmsl size_joinlsl addnK -Hszandrs size_nseq Hszlrs.
      move : (add_prelude_to Hevar Hcssub) => Haddcssub.
      move : (bit_blast_sub_correct Hbbsub2 Hencuge1 Hencandrs Haddcssub Hszsub) => Hencsubrs.
      have Hencjlqs : enc_bits E (joinlsl lrsuge lqs) (joinlsb (~~ ((dropmsb (joinlsb bs1hd bsr)) <# bs2)%bits) bsq) by rewrite enc_bits_joinlsb Hencugers Hencq.
      have Hdjlqs : enc_bits E (dropmsl (joinlsl lrsuge lqs)) (dropmsb (joinlsb ((bs2<=#(dropmsb (joinlsb bs1hd bsr)))%bits) bsq)). rewrite leBNlt// (enc_bits_dropmsb Htt Hencjlqs)//.
      have Hszudivr : size (dropmsl (joinlsl lrsuge lqs)) = size ls2 by rewrite size_dropmsl size_joinlsl addnK Hszlqs.
      move : (bit_blast_sub_size_ss Hbbsub2 Hszsub) => Hszsubrs.
      have Hszlrssub2 : size lrssub2 = size ls2 by rewrite Hszsubrs -Hszandrs size_nseq.
      move : (add_prelude_to Hevar Hcsudivr) => Haddcsudivr.
      move : (IH _ _ _ _ _ _ _ _ _ _ _ _ _ Hudivr3 Hszudivr Hszlrssub2 Hencls1tl Henc2 Hdjlqs Hencsubrs Haddcsudivr).
      move : (enc_bits_size Henc2) => Hszlsbs2. rewrite Hszlsbs2 andB_copy_case.
      case ((bs2 <=# (dropmsb (joinlsb bs1hd bsr)))%bits); first done.
      have {1 2}->: (size bs2 = size (dropmsb (joinlsb bs1hd bsr))) by rewrite size_dropmsb size_joinlsb addnK -(enc_bits_size Hencr) - Hszlsbs2 Hszlrs.
      by rewrite from_natn0 subB0.
Qed.

Lemma enc_bits_ff : forall E cs n, interp_cnf E (add_prelude cs) -> enc_bits E (copy n lit_ff) (zeros n).
Proof.
  intros. apply enc_bits_copy. apply add_prelude_enc_bit_ff with cs. done.
Qed.

Lemma bit_blast_udiv_correct g ls1 ls2 g' cs qlrs rlrs E bs1 bs2 :
  bit_blast_udiv g ls1 ls2 = (g', cs, qlrs, rlrs) ->
  size ls1 = size ls2 ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E qlrs (udivB bs1 bs2).1 /\
  enc_bits E rlrs (udivB bs1 bs2).2.
Proof.
  rewrite/bit_blast_udiv.
  dcase (bit_blast_eq g ls2 (copy (size ls2) lit_ff)) => [[[g_eq] cs_eq] lrs_eq] Hbbeq.
  dcase (bit_blast_udiv_rec g_eq (rev ls1) ls2 (copy (size (rev ls1)) lit_ff) (copy (size (rev ls1)) lit_ff)) => [[[[g_udivr cs_udivr] lqs_udivr] lrs_udivr] Hbbudiv].
  dcase (bit_blast_or g_udivr (copy (size lqs_udivr) (lrs_eq)) lqs_udivr) => [[[g_or] cs_or] lrs_or] Hbbor.
  dcase (bit_blast_ite g_or lrs_eq ls1 lrs_udivr) => [[[g_ite] cs_ite] lrs_ite] Hbbite.
  have Hszcp :  size ls2 = size (copy (size ls2) lit_ff) by rewrite size_nseq.
  case Hlrseqt : (lrs_eq == lit_tt).
  - case => _ <- <- <- .
    move => Hsz12 Henc1 Henc2 Hcnf.
    move : (add_prelude_enc_bit_tt Hcnf) => Htt.
    move : (add_prelude_enc_bit_ff Hcnf) => Hff.
    move : (enc_bits_copy (size ls2) Htt) => Henctt.
    move : (enc_bits_copy (size ls2) Hff) => Hencff.
    move : (bit_blast_eq_correct Hbbeq Hszcp Henc2 Hencff Hcnf).
    rewrite/udivB (eqP Hlrseqt) (add_prelude_enc_bit_true (bs2 == copy (size ls2) false) Hcnf). move => Hbs20.
    rewrite (eqP Hbs20) size_rev -/b0 -/(zeros (size ls2)) to_Zpos_zeros zeros_from_Zpos eq_refl.
    move : (enc_bits_size Henc1) => Hszls1bs1.
    rewrite/= -Hszls1bs1 Hsz12 /ones (enc_bits_copy _ Htt) Henc1//.
  - case Hlrseqf : (lrs_eq == lit_ff).
    + case => _ <- <- <- .
      move => Hsz12 Henc1 Henc2. rewrite add_prelude_catrev.
      move/andP => [Hcsudivr Hcseq].
      move : (add_prelude_enc_bit_ff Hcseq) => Hff.
      move : (enc_bits_copy (size ls2) Hff) => Hencff.
      move : (bit_blast_eq_correct Hbbeq Hszcp Henc2 Hencff Hcseq).
      move : (enc_bits_size Henc1) => Hszlsbs1.
      move : (enc_bits_size Henc2) => Hszlsbs2.
      rewrite/udivB (eqP Hlrseqf) size_rev/= -Hszlsbs1 Hsz12 Hszlsbs2 -/b0 -/(zeros (size bs2)).
      move => Hencbs20.
      move : (add_prelude_enc_bit_is_not_true (bs2 == copy (size ls2) false) Hcseq).
      rewrite -/(zeros (size ls2)) Hszlsbs2 Hencbs20. move => Hbs2not0; symmetry in Hbs2not0.
      rewrite<-Bool.negb_false_iff in Hbs2not0. rewrite Bool.negb_involutive in Hbs2not0.
      rewrite from_Zpos_to_Zpos Hbs2not0.
      move : (enc_bits_rev Henc1) => Hencrev1.
      generalize Hencff. rewrite -Hsz12 -(size_rev ls1). move => Hencffrev.
      generalize Hszcp. move => Hszcprev; symmetry in Hszcprev. rewrite -{1}Hsz12 -{1}(size_rev ls1) in Hszcprev.
      move : (bit_blast_udiv_rec_correct Hbbudiv Hszcprev Hszcprev Hencrev1 Henc2 Hencffrev Hencffrev Hcsudivr).
        by rewrite size_rev -/b0 Hsz12 Hszlsbs2 -/(zeros (size bs2)).
    + case => _ <- <- <- .
      move => Hsz12 Henc1 Henc2. rewrite !add_prelude_catrev.
      move => /andP [/andP [/andP [Hcsite Hcsor] Hcsudivr] Hcseq].
      move : (add_prelude_enc_bit_ff Hcseq) => Hff.
      move : (enc_bits_copy (size ls2) Hff) => Hencff.
      move : (bit_blast_eq_correct Hbbeq Hszcp Henc2 Hencff Hcseq).
      move : (enc_bits_size Henc1) => Hszlsbs1.
      move : (enc_bits_size Henc2) => Hszlsbs2.
      rewrite -/(zeros (size ls2)) Hszlsbs2.
      move => Hencbs20t.
      move : (enc_bits_rev Henc1) => Hencrev1.
      generalize Hencff. rewrite -Hsz12 -(size_rev ls1). move => Hencffrev.
      generalize Hszcp. move => Hszcprev; symmetry in Hszcprev. rewrite -{1}Hsz12 -{1}(size_rev ls1) in Hszcprev.
      move : (bit_blast_udiv_rec_correct Hbbudiv Hszcprev Hszcprev Hencrev1 Henc2 Hencffrev Hencffrev Hcsudivr).
      rewrite size_rev -/b0 -/(zeros (size ls1)) Hsz12 Hszlsbs2.
      move => [Hencq Hencr].
      generalize Hencff. rewrite -Hsz12. move => Hencff1.
      move : (enc_bits_copy (size lqs_udivr)  Hencbs20t) => Henccp.
      move : (bit_blast_or_correct Hbbor Henccp Hencq Hcsor).
      move : (bit_blast_udiv_rec_size_ss Hbbudiv Hszcprev Hszcprev)=> [Hszq Hszr].
      move : (size_udivB_rec (rev bs1) bs2 (zeros (size bs2)) (zeros (size bs2))).
      rewrite size_zeros -Hszlsbs2 -{3}Hszq. move => Hszudivr.
      rewrite -{1}Hszudivr orB_copy_case.
      have Hszls1 : size ls1 == size lrs_udivr by rewrite Hszr Hsz12 eq_refl.
      case Hbs20 : (bs2 == zeros (size ls2)).
      * rewrite (eqP Hbs20) size_udivB_rec udivB0 size_zeros -Hsz12 Hszlsbs1.
        move : (bit_blast_ite_correct Hszls1 Hbbite Hencbs20t Henc1 Hencr Hcsite). by rewrite -Hszlsbs2 Hbs20.
      * move : (size_rev lrs_udivr) => /eqP Hszrev.
        move : (enc_bits_rev Hencr) => Hencrrev.
        move : (bit_blast_ite_correct Hszls1 Hbbite Hencbs20t Henc1 Hencr Hcsite).
        rewrite /udivB size_rev -Hszlsbs1 Hsz12 Hszlsbs2 from_Zpos_to_Zpos -Hszlsbs2 Hbs20//.
Qed.

Lemma bit_blast_udiv_correct' g ls1 ls2 g' cs qlrs E bs1 bs2 :
  bit_blast_udiv' g ls1 ls2 = (g', cs, qlrs) ->
  size ls1 = size ls2 ->
  enc_bits E ls1 bs1 ->
  enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E qlrs (udivB bs1 bs2).1.
Proof.
  rewrite /bit_blast_udiv'. case Hbb : (bit_blast_udiv g ls1 ls2) => [[[g_u cs_u] q_u] r_u].
  case => _ <- <-. move => Hs He1 He2 Hi. move : (bit_blast_udiv_correct Hbb Hs He1 He2 Hi) => [Hl Hr].
  done.
Qed.

Lemma mk_env_udiv_rec_is_bit_blast_udiv_rec: forall ls1 E g ls2 lq lr g' cs qlrs rlrs E',
  mk_env_udiv_rec E g ls1 ls2 lq lr = (E', g', cs, qlrs, rlrs) ->
  bit_blast_udiv_rec g ls1 ls2 lq lr = (g', cs, qlrs, rlrs).
Proof.
  elim => [| ls1hd ls1tl IH] E g ls2 lq lr g' cs qlrs rlrs E'.
  - rewrite/=. by case => _ <- <- <- <-.
  - rewrite/=.
    dcase (mk_env_uge E g (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lr)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    dcase (mk_env_udiv_rec E_sub g_sub ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_udiv_rec E_hd g_hd ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) (dropmsl (joinlsl ls1hd lr))) => [[[[[E_tl2 g_tl2] cs_tl2] lrs_tl2] lqs_tl2] Hmkudiv2].
    dcase (mk_env_udiv_rec E_sub2 g_sub2 ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub2) => [[[[[E_tl3 g_tl3] cs_tl3] lrs_tl3] lqs_tl3] Hmkudiv3].
    rewrite (mk_env_uge_is_bit_blast_uge Hmkuge) (mk_env_sub_is_bit_blast_sub Hmksub) (mk_env_and_is_bit_blast_and Hmkand) (mk_env_sub_is_bit_blast_sub Hmksub2) (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv) (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv2) (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv3).
    case (lrs_hd == lit_tt); case (lrs_hd == lit_ff); by  move => [] _<- <- <- <-.
Qed.

Lemma mk_env_udiv_is_bit_blast_udiv : forall ls1 E g ls2 g' cs qlrs rlrs E',
  mk_env_udiv E g ls1 ls2 = (E', g', cs, qlrs, rlrs) ->
  bit_blast_udiv g ls1 ls2  = (g', cs, qlrs, rlrs).
Proof.
  rewrite/mk_env_udiv/bit_blast_udiv/=. move => ls1 E g ls2 g' cs qlrs rlrs E'.
  dcase (mk_env_eq E g ls2 (copy (size ls2) lit_ff)) => [[[[E_eq] g_eq] cs_eq] lrs_eq] Hmkeq.
  dcase (mk_env_udiv_rec E_eq g_eq (rev ls1) ls2 (copy (size (rev ls1)) lit_ff) (copy (size (rev ls1)) lit_ff)) => [[[[[E_udivr] g_udivr] cs_udivr] lqs_udivr] lrs_udivr] Hmkudivr.
  dcase (mk_env_or E_udivr g_udivr (copy (size lqs_udivr) (lrs_eq)) lqs_udivr)=> [[[[E_or] g_or] cs_or] lrs_or] Hmkor.
  dcase (mk_env_ite E_or g_or lrs_eq ls1 lrs_udivr) =>[[[[E_ite] g_ite] cs_ite] lrs_ite] Hmkite.
  rewrite (mk_env_eq_is_bit_blast_eq Hmkeq) (mk_env_udiv_rec_is_bit_blast_udiv_rec Hmkudivr) (mk_env_or_is_bit_blast_or Hmkor) (mk_env_ite_is_bit_blast_ite Hmkite).
  case (lrs_eq == lit_tt);
  case (lrs_eq == lit_ff); by case => _ <- <- <- <- .
Qed.

Lemma mk_env_udiv_is_bit_blast_udiv' : forall ls1 E g ls2 g' cs qlrs E',
  mk_env_udiv' E g ls1 ls2 = (E', g', cs, qlrs) ->
  bit_blast_udiv' g ls1 ls2  = (g', cs, qlrs).
Proof.
  move => ls1 E g ls2 g' cs qlrs E'. rewrite /mk_env_udiv' /bit_blast_udiv'.
  case Hmk : (mk_env_udiv E g ls1 ls2) => [[[[Emk gmk] csmk] qmk] rmk].
  case => _ <- <- <-. by rewrite (mk_env_udiv_is_bit_blast_udiv Hmk).
Qed.

Lemma mk_env_udiv_rec_newer_gen :
  forall ls1 E g ls2 lq lr E' g' cs lqs lrs,
    mk_env_udiv_rec E g ls1 ls2 lq lr = (E', g', cs, lqs, lrs) ->
    (g <=? g')%positive.
Proof.
  elim  => [| ls1hd ls1tl IH] E g ls2 lq lr E' g' cs lqs lrs.
  - move => [] _ <- _ _ _. exact: Pos.leb_refl.
  - rewrite/=.
    (*dcase (mk_env_udiv_rec E g ls1tl ls2 lq lr) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].*)
    dcase (mk_env_uge E g (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lr)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    dcase (mk_env_udiv_rec E_sub g_sub ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_udiv_rec E_hd g_hd ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) (dropmsl (joinlsl ls1hd lr))) => [[[[[E_tl2 g_tl2] cs_tl2] lrs_tl2] lqs_tl2] Hmkudiv2].
    dcase (mk_env_udiv_rec E_sub2 g_sub2 ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub2) => [[[[[E_tl3 g_tl3] cs_tl3] lrs_tl3] lqs_tl3] Hmkudiv3].
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv) => Hg2g5.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv2) => Hg0g5.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv3) => Hg4g5.
    move : (mk_env_uge_newer_gen Hmkuge) => Hgg0.
    move : (mk_env_sub_newer_gen Hmksub) => Hg0g2.
    move : (mk_env_and_newer_gen Hmkand) => Hg0g3.
    move : (mk_env_sub_newer_gen Hmksub2) => Hg3g4.
    move : (pos_leb_trans Hgg0 Hg0g5) => Hgg5.
    move : (pos_leb_trans Hgg0 (pos_leb_trans Hg0g2 Hg2g5)) => Hgg52.
    move : (pos_leb_trans (pos_leb_trans Hgg0 Hg0g3) (pos_leb_trans Hg3g4 Hg4g5)) => Hgg53.
    case (lrs_hd == lit_tt); case (lrs_hd == lit_ff); (move => [] _ <- _ _ _; try exact).
Qed.

Lemma mk_env_udiv_newer_gen :
  forall ls1 E g ls2 E' g' cs lqs lrs,
    mk_env_udiv E g ls1 ls2 = (E', g', cs, lqs, lrs) ->
    (g <=? g')%positive.
Proof.
  rewrite/mk_env_udiv/bit_blast_udiv/=. move => ls1 E g ls2 E' g' cs qlrs rlrs .
  dcase (mk_env_eq E g ls2 (copy (size ls2) lit_ff)) => [[[[E_eq] g_eq] cs_eq] lrs_eq] Hmkeq.
  dcase (mk_env_udiv_rec E_eq g_eq (rev ls1) ls2 (copy (size (rev ls1)) lit_ff) (copy (size (rev ls1)) lit_ff)) => [[[[[E_udivr] g_udivr] cs_udivr] lqs_udivr] lrs_udivr] Hmkudivr.
  dcase (mk_env_or E_udivr g_udivr (copy (size lqs_udivr) (lrs_eq)) lqs_udivr)=> [[[[E_or] g_or] cs_or] lrs_or] Hmkor.
  dcase (mk_env_ite E_or g_or lrs_eq ls1 lrs_udivr) =>[[[[E_ite] g_ite] cs_ite] lrs_ite] Hmkite.
  case (lrs_eq == lit_tt); case (lrs_eq == lit_ff); case => _ <- _ _ _ ; try apply (mk_env_eq_newer_gen Hmkeq).
  move: (mk_env_udiv_rec_newer_gen Hmkudivr) => Hnewudivr. move : (mk_env_eq_newer_gen Hmkeq) => Hneweq.
  exact : (pos_leb_trans Hneweq Hnewudivr).
  move : (mk_env_ite_newer_gen Hmkite) => Hnewite. move : (mk_env_or_newer_gen Hmkor) => Hnewor. move: (mk_env_udiv_rec_newer_gen Hmkudivr) => Hnewudivr. move : (mk_env_eq_newer_gen Hmkeq) => Hneweq.
  exact : (pos_leb_trans (pos_leb_trans Hneweq Hnewudivr) (pos_leb_trans Hnewor Hnewite)).
Qed.

Lemma mk_env_udiv_newer_gen' :
  forall ls1 E g ls2 E' g' cs lqs,
    mk_env_udiv' E g ls1 ls2 = (E', g', cs, lqs) ->
    (g <=? g')%positive.
Proof.
  move => ls1 E g ls2 E' g' cs lqs. rewrite /mk_env_udiv'.
  dcase (mk_env_udiv E g ls1 ls2) => [[[[[E_u] g_u] cs_u] lqs_u] lrs_u] Hmku.
  case => _ <- _ _. rewrite (mk_env_udiv_newer_gen Hmku)//.
Qed.

Lemma mk_env_udiv_rec_newer_res :
  forall ls1 E g ls2 lq lr E' g' cs lqs lrs,
    mk_env_udiv_rec E g ls1 ls2 lq lr = (E', g', cs, lqs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_lits g lq ->
    newer_than_lits g lr ->
    newer_than_lits g' lrs && newer_than_lits g' lqs.
Proof.
  elim  => [| ls1hd ls1tl IH] E g ls2 lq lr E' g' cs lqs lrs.
  - rewrite /=. case => _ <- _ <- <-.  move => Htt Hls1 Hls2 Hlq Hlr. by rewrite Hlq Hlr.
  - rewrite/=.
    dcase (mk_env_uge E g (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lr)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    dcase (mk_env_udiv_rec E_sub g_sub ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_udiv_rec E_hd g_hd ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) (dropmsl (joinlsl ls1hd lr))) => [[[[[E_tl2 g_tl2] cs_tl2] lrs_tl2] lqs_tl2] Hmkudiv2].
    dcase (mk_env_udiv_rec E_sub2 g_sub2 ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub2) => [[[[[E_tl3 g_tl3] cs_tl3] lrs_tl3] lqs_tl3] Hmkudiv3].
    (*
    dcase (mk_env_udiv_rec E g ls1tl ls2 lq lr) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_uge E_tl g_tl (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lrs_tl)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].*)
    move => Hres Htt Hls1 Hls2 Hlq Hlr.  move/andP: Hls1 => [Hls1hd Hls1tl].
    generalize Hres.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv) => Hg2g5.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv2) => Hg0g5.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv3) => Hg4g5.
    move : (mk_env_uge_newer_gen Hmkuge) => Hgg0.
    move : (mk_env_sub_newer_gen Hmksub) => Hg0g2.
    move : (mk_env_and_newer_gen Hmkand) => Hg0g3.
    move : (mk_env_sub_newer_gen Hmksub2) => Hg3g4.
    move : (pos_leb_trans Hgg0 Hg0g5) => Hgg5.
    move : (pos_leb_trans Hgg0 (pos_leb_trans Hg0g2 Hg2g5)) => Hgg52.
    move : (pos_leb_trans (pos_leb_trans Hgg0 Hg0g3) (pos_leb_trans Hg3g4 Hg4g5)) => Hgg53.
    move : (pos_leb_trans Hgg0 (pos_leb_trans Hg0g3 Hg3g4 )) => Hgg4.
    move : ((pos_leb_trans Hg0g3 Hg3g4 )) => Hg0g4.
    move : (mk_env_uge_newer_res Hmkuge) => Hg0ls2.
    move : (mk_env_sub_newer_res Hmksub) => Hg2ls3.
    move : (mk_env_sub_newer_res Hmksub2) => Hg4ls5.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl Hg0ls2 (newer_than_lits_le_newer Hlq Hgg0))) => Hdjlq.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl Hls1hd ( Hlr ))) => Hdjlr.
    move : (newer_than_lits_le_newer Hdjlr Hgg0) => Hdjlrg0.
    move/andP : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv (newer_than_lit_le_newer Htt (pos_leb_trans Hgg0 Hg0g2)) (newer_than_lits_le_newer Hls1tl (pos_leb_trans Hgg0 Hg0g2)) (newer_than_lits_le_newer Hls2 (pos_leb_trans Hgg0 Hg0g2)) (newer_than_lits_le_newer Hdjlq Hg0g2)   Hg2ls3) => [Hg0lq Hg0lr].
    move/andP : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv2 (newer_than_lit_le_newer Htt  Hgg0) (newer_than_lits_le_newer Hls1tl (Hgg0 )) (newer_than_lits_le_newer Hls2 ( Hgg0 )) (Hdjlq ) Hdjlrg0  ) => [Hgtl2lq Hgtl2lr].
    move/andP : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv3 (newer_than_lit_le_newer Htt  Hgg4) (newer_than_lits_le_newer Hls1tl (Hgg4 )) (newer_than_lits_le_newer Hls2 ( Hgg4 )) (newer_than_lits_le_newer Hdjlq Hg0g4) Hg4ls5) => [Hgtl3lq Hgtl3lr].
    move : (newer_than_lit_le_newer Hg0ls2 Hg0g2) => Hg5ls6.
    move : (newer_than_lit_le_newer Hg0ls2 Hg0g3) => Hg8ls9.
    move : (newer_than_lit_le_newer Hls1hd Hgg0) => Hg9ls0.
    case (lrs_hd == lit_tt); case (lrs_hd == lit_ff); move => [] _ <- _ <- <-.
    by rewrite Hg0lq Hg0lr. by rewrite Hg0lq Hg0lr.
    by rewrite Hgtl2lq Hgtl2lr. by rewrite Hgtl3lq Hgtl3lr.
Qed.

Lemma mk_env_udiv_newer_res :
  forall ls1 E g ls2 E' g' cs lqs lrs,
    mk_env_udiv E g ls1 ls2  = (E', g', cs, lqs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_lits g' lrs && newer_than_lits g' lqs.
Proof.
  rewrite/mk_env_udiv/bit_blast_udiv/=. move => ls1 E g ls2 E' g' cs qlrs rlrs .
  dcase (mk_env_eq E g ls2 (copy (size ls2) lit_ff)) => [[[[E_eq] g_eq] cs_eq] lrs_eq] Hmkeq.
  dcase (mk_env_udiv_rec E_eq g_eq (rev ls1) ls2 (copy (size (rev ls1)) lit_ff) (copy (size (rev ls1)) lit_ff)) => [[[[[E_udivr] g_udivr] cs_udivr] lqs_udivr] lrs_udivr] Hmkudivr.
  dcase (mk_env_or E_udivr g_udivr (copy (size lqs_udivr) (lrs_eq)) lqs_udivr)=> [[[[E_or] g_or] cs_or] lrs_or] Hmkor.
  dcase (mk_env_ite E_or g_or lrs_eq ls1 lrs_udivr) =>[[[[E_ite] g_ite] cs_ite] lrs_ite] Hmkite.
  move : (mk_env_ite_newer_gen Hmkite) => Hnewite. move : (mk_env_or_newer_gen Hmkor) => Hnewor.
  move: (mk_env_udiv_rec_newer_gen Hmkudivr) => Hnewudivr. move : (mk_env_eq_newer_gen Hmkeq) => Hneweq.
  case (lrs_eq == lit_tt); case (lrs_eq == lit_ff); case => _ <- _ <- <- ; move => Htt Hls1 Hls2.
  rewrite (newer_than_lits_le_newer Hls1 Hneweq) newer_than_lits_copy// (newer_than_lit_le_newer Htt Hneweq)//.
  rewrite (newer_than_lits_le_newer Hls1 Hneweq) newer_than_lits_copy// (newer_than_lit_le_newer Htt Hneweq)//.
  have Hnewcp : (newer_than_lits g_eq (copy (size (rev ls1)) lit_ff)) by (rewrite newer_than_lits_copy; last by rewrite -newer_than_lit_tt_ff (newer_than_lit_le_newer Htt Hneweq)).
  exact : (mk_env_udiv_rec_newer_res Hmkudivr (newer_than_lit_le_newer Htt Hneweq) (newer_than_lits_le_newer (newer_than_lits_rev Hls1) Hneweq) (newer_than_lits_le_newer Hls2 Hneweq) Hnewcp Hnewcp).
  rewrite (mk_env_ite_newer_res Hmkite).
  move : (pos_leb_trans Hneweq Hnewudivr) => Hgudivr.
  have Hnewcp : (newer_than_lits g_udivr (copy (size lqs_udivr) (lrs_eq))) by rewrite newer_than_lits_copy// (newer_than_lit_le_newer (mk_env_eq_newer_res Hmkeq) Hnewudivr).
  have Hnewrev : (newer_than_lits g_eq (rev ls1)) by rewrite (newer_than_lits_rev (newer_than_lits_le_newer Hls1 Hneweq)).
  have Hnewcpeq : (newer_than_lits g_eq (copy (size (rev ls1)) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite -newer_than_lit_tt_ff (newer_than_lit_le_newer Htt Hneweq).
  move/andP : (mk_env_udiv_rec_newer_res Hmkudivr (newer_than_lit_le_newer Htt Hneweq) Hnewrev (newer_than_lits_le_newer Hls2 Hneweq) Hnewcpeq Hnewcpeq) => [Hnewq Hnewr].
  by rewrite (newer_than_lits_le_newer (mk_env_or_newer_res Hmkor (newer_than_lit_le_newer Htt Hgudivr) Hnewcp Hnewr) Hnewite).
Qed.

Lemma mk_env_udiv_newer_res' :
  forall ls1 E g ls2 E' g' cs lqs,
    mk_env_udiv' E g ls1 ls2  = (E', g', cs, lqs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_lits g' lqs.
Proof.
  move => ls1 E g ls2 E' g' cs lqs Hmk Hnlt Hnl1 Hnl2. move : Hmk; rewrite /mk_env_udiv'.
  dcase (mk_env_udiv E g ls1 ls2) => [[[[[E_u] g_u] cs_u] lqs_u] lrs_u] Hmku.
  case => _ <- _ <-. by move :(mk_env_udiv_newer_res Hmku Hnlt Hnl1 Hnl2) => /andP [Hl Hr].
Qed.

Lemma mk_env_udiv_rec_newer_cnf :
  forall ls1 E g ls2 lq lr E' g' cs lqs lrs,
    mk_env_udiv_rec E g ls1 ls2 lq lr = (E', g', cs, lqs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_lits g lq ->
    newer_than_lits g lr ->
    newer_than_cnf g' cs.
Proof.
    elim  => [| ls1hd ls1tl IH] E g ls2 lq lr E' g' cs lqs lrs.
  - rewrite /=. case => _ <- <- _ _.  move => Htt Hls1 Hls2 Hlq Hlr. done.
  - rewrite/=.
    dcase (mk_env_uge E g (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_udiv_rec E_sub g_sub ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub) =>[[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_udiv_rec E_hd g_hd ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) (dropmsl (joinlsl ls1hd lr))) =>
    [[[[[E_tl2 g_tl2] cs_tl2] lrs_tl2] lqs_tl2] Hmkudiv2].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lr)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    dcase (mk_env_udiv_rec E_sub2 g_sub2 ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub2) =>
    [[[[[E_tl3 g_tl3] cs_tl3] lrs_tl3] lqs_tl3] Hmkudiv3].
    move => Hres Htt Hls1 Hls2 Hlq Hlr.  move/andP: Hls1 => [Hls1hd Hls1tl].
    move : (mk_env_uge_newer_gen Hmkuge) => Hg0g1.
    move : (mk_env_sub_newer_gen Hmksub) => Hg1g2.
    move : (pos_leb_trans Hg0g1  Hg1g2) => Hg0g2.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv) => Hg2g3.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv2) => Hg2g3'.
    move : (mk_env_and_newer_gen Hmkand) => Hg1g2''.
    move : (mk_env_sub_newer_gen Hmksub2) => Hg2''g3''.
    move : (pos_leb_trans Hg0g1 (pos_leb_trans Hg1g2 Hg2g3)) => Hg0g3.
    move : (pos_leb_trans Hg1g2'' Hg2''g3'') => Hg1g3''.
    move : (pos_leb_trans Hg0g1 Hg1g3'') => Hg0g3''.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv3) => Hg3''g4''.
    move : (pos_leb_trans Hg1g3'' Hg3''g4'') => Hg1g4''.
    move: (newer_than_lit_le_newer Htt Hg0g1) => Httg1. rewrite newer_than_lit_tt_ff in Httg1.
    move : (mk_env_uge_newer_res Hmkuge) => Hlrshd.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl (newer_than_lit_le_newer Hlrshd Hg1g2) (newer_than_lits_le_newer Hlq Hg0g2))) => Hdjlq.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl ( Hlrshd ) (newer_than_lits_le_newer Hlq Hg0g1))) => Hdjlq0.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl ( Hls1hd ) ( Hlr ))) => Hdjlr0.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl (newer_than_lit_le_newer Hls1hd Hg0g2) (newer_than_lits_le_newer Hlr Hg0g2))) => Hdjlr.
    move : (mk_env_sub_newer_res Hmksub) => Hlrssub.
    move : (mk_env_sub_newer_res Hmksub2) => Hlrssub2.
    move/andP : (mk_env_udiv_rec_newer_res Hmkudiv (newer_than_lit_le_newer Htt Hg0g2) (newer_than_lits_le_newer Hls1tl Hg0g2) (newer_than_lits_le_newer Hls2 Hg0g2) Hdjlq Hlrssub) => [Hlqstl Hlrstl].
    move : (mk_env_sub_newer_cnf Hmksub Httg1 (newer_than_lits_le_newer Hdjlr0 Hg0g1) (newer_than_lits_le_newer Hls2 Hg0g1)) => Hg2ls3.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv (newer_than_lit_le_newer Htt Hg0g2) (newer_than_lits_le_newer Hls1tl Hg0g2) (newer_than_lits_le_newer Hls2 Hg0g2) Hdjlq Hlrssub) => Hg0cs0.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv2 (newer_than_lit_le_newer Htt Hg0g1) (newer_than_lits_le_newer Hls1tl Hg0g1) (newer_than_lits_le_newer Hls2 Hg0g1) Hdjlq0 (newer_than_lits_le_newer Hdjlr0 Hg0g1)) => Hg1cs1.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv3 (newer_than_lit_le_newer Htt (Hg0g3'' )) (newer_than_lits_le_newer Hls1tl Hg0g3'') (newer_than_lits_le_newer Hls2 Hg0g3'') (newer_than_lits_le_newer Hdjlq0 Hg1g3'') Hlrssub2) => Hg3cs3.
    move : (mk_env_uge_newer_cnf Hmkuge (Htt ) Hdjlr0 (Hls2 )) => Hg1cs2.
    move : (mk_env_uge_newer_res Hmkuge) => Hg1rs1.
    move : (newer_than_cnf_le_newer Hg1cs2 Hg1g2) => Hg2cs2.
    move : (mk_env_and_newer_res Hmkand (newer_than_lit_le_newer Htt Hg0g1) (newer_than_lits_copy (size ls2) Hg1rs1) (newer_than_lits_le_newer Hls2 Hg0g1)) => Hg3ls3.
    move : (mk_env_sub_newer_cnf Hmksub2 (newer_than_lit_le_newer Httg1 Hg1g2'') (newer_than_lits_le_newer Hdjlr0 (pos_leb_trans Hg0g1 Hg1g2'')) Hg3ls3) => Hg4cs5.
    move : (mk_env_and_newer_cnf Hmkand (newer_than_lit_le_newer Htt Hg0g1) (newer_than_lits_copy (size ls2) Hg1rs1) (newer_than_lits_le_newer Hls2 Hg0g1)) => Hg4cs4.
    generalize Hres.
    case (lrs_hd == lit_tt); case (lrs_hd == lit_ff); move => [] _ <- <- _ _; rewrite !newer_than_cnf_catrev;
    try by rewrite Hg0cs0 (newer_than_cnf_le_newer Hg2ls3 Hg2g3) (newer_than_cnf_le_newer Hg2cs2 Hg2g3).
    by rewrite Hg1cs1 (newer_than_cnf_le_newer Hg1cs2 Hg2g3').
    by rewrite Hg3cs3 (newer_than_cnf_le_newer Hg4cs5 Hg3''g4'') (newer_than_cnf_le_newer Hg4cs4 (pos_leb_trans Hg2''g3'' Hg3''g4'')) (newer_than_cnf_le_newer Hg1cs2 Hg1g4'').
Qed.

(* This is a deprecated version of the above lemma that requires no size assumptions. *)
(*
Lemma mk_env_udiv_rec_newer_cnf :
  forall ls1 E g ls2 lq lr E' g' cs lqs lrs,
    mk_env_udiv_rec E g ls1 ls2 lq lr = (E', g', cs, lqs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_lits g lq ->
    newer_than_lits g lr ->
    size lq = size ls2 -> size lr = size ls2 ->
    newer_than_cnf g' cs.
Proof.
    elim  => [| ls1hd ls1tl IH] E g ls2 lq lr E' g' cs lqs lrs.
  - rewrite /=. case => _ <- <- _ _.  move => Htt Hls1 Hls2 Hlq Hlr Hszq Hszr. done.
  - rewrite/=.
    (*dcase (mk_env_udiv_rec E g ls1tl ls2 lq lr) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_uge E_tl g_tl (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lrs_tl)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].*)
    dcase (mk_env_uge E g (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_udiv_rec E_sub g_sub ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub) =>[[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_udiv_rec E_hd g_hd ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) (dropmsl (joinlsl ls1hd lr))) =>
    [[[[[E_tl2 g_tl2] cs_tl2] lrs_tl2] lqs_tl2] Hmkudiv2].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lr)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    dcase (mk_env_udiv_rec E_sub2 g_sub2 ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub2) =>
    [[[[[E_tl3 g_tl3] cs_tl3] lrs_tl3] lqs_tl3] Hmkudiv3].
    move => Hres Htt Hls1 Hls2 Hlq Hlr Hszq Hszr.  move/andP: Hls1 => [Hls1hd Hls1tl].
    move : (mk_env_uge_newer_gen Hmkuge) => Hg0g1.
    move : (mk_env_sub_newer_gen Hmksub) => Hg1g2.
    move : (pos_leb_trans Hg0g1  Hg1g2) => Hg0g2.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv) => Hg2g3.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv2) => Hg2g3'.
    move : (mk_env_and_newer_gen Hmkand) => Hg1g2''.
    move : (mk_env_sub_newer_gen Hmksub2) => Hg2''g3''.
    move : (pos_leb_trans Hg0g1 (pos_leb_trans Hg1g2 Hg2g3)) => Hg0g3.
    move : (pos_leb_trans Hg1g2'' Hg2''g3'') => Hg1g3''.
    move : (pos_leb_trans Hg0g1 Hg1g3'') => Hg0g3''.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv3) => Hg3''g4''.
    move : (pos_leb_trans Hg1g3'' Hg3''g4'') => Hg1g4''.
    move: (newer_than_lit_le_newer Htt Hg0g1) => Httg1. rewrite newer_than_lit_tt_ff in Httg1.
    move : (mk_env_uge_newer_res Hmkuge) => Hlrshd.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl (newer_than_lit_le_newer Hlrshd Hg1g2) (newer_than_lits_le_newer Hlq Hg0g2))) => Hdjlq.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl ( Hlrshd ) (newer_than_lits_le_newer Hlq Hg0g1))) => Hdjlq0.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl ( Hls1hd ) ( Hlr ))) => Hdjlr0.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl (newer_than_lit_le_newer Hls1hd Hg0g2) (newer_than_lits_le_newer Hlr Hg0g2))) => Hdjlr.
    move : (mk_env_sub_newer_res Hmksub) => Hlrssub.
    move : (mk_env_sub_newer_res Hmksub2) => Hlrssub2.
    move/andP : (mk_env_udiv_rec_newer_res Hmkudiv (newer_than_lit_le_newer Htt Hg0g2) (newer_than_lits_le_newer Hls1tl Hg0g2) (newer_than_lits_le_newer Hls2 Hg0g2) Hdjlq Hlrssub) => [Hlqstl Hlrstl].
    (*move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl (newer_than_lit_le_newer Hls1hd Hg0g1) (newer_than_lits_le_newer Hlrstl Hg0g1))) => Hdj.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl (newer_than_lit_le_newer Hls1hd Hgg0) Hlrstl)) => Hdjtl.
    move : (newer_than_lits_le_newer Hls2 Hgg1) => Hg1ls2hd.*)
    have Hszdjq : (size (dropmsl (joinlsl lrs_hd lq)) = size  ls2) by rewrite size_dropmsl size_joinlsl addnK.
    have Hszdjr : (size (dropmsl (joinlsl ls1hd lr)) = size ls2) by rewrite size_dropmsl size_joinlsl addnK.
    move : (bit_blast_sub_size_ss (mk_env_sub_is_bit_blast_sub Hmksub) Hszdjr) => Hsz1.
    have Hszcp : size (copy (size ls2) lrs_hd) = size ls2 by rewrite size_nseq.
    move : (bit_blast_and_size_ss (mk_env_and_is_bit_blast_and Hmkand) Hszcp) => Hszcp0.
    have  Hdjand : (size (dropmsl (joinlsl ls1hd lr)) = size lrs_and) by rewrite size_dropmsl size_joinlsl addnK Hszr -Hszcp0 size_nseq.
    move : (bit_blast_sub_size_ss (mk_env_sub_is_bit_blast_sub Hmksub2) Hdjand) => Hsz2.
    rewrite -Hszcp0 size_nseq in Hsz2.
    move : (bit_blast_udiv_rec_size_ss (mk_env_udiv_rec_is_bit_blast_udiv_rec Hmkudiv) Hszdjq Hsz1) => [Hszrtl Hszqtl].
    have Hszdj : (size (dropmsl (joinlsl ls1hd lrs_tl)) = size ls2) by rewrite size_dropmsl size_joinlsl addnK Hszrtl.
    move : (mk_env_sub_newer_cnf Hmksub Httg1 (newer_than_lits_le_newer Hdjlr0 Hg0g1) (newer_than_lits_le_newer Hls2 Hg0g1)) => Hg2ls3.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv (newer_than_lit_le_newer Htt Hg0g2) (newer_than_lits_le_newer Hls1tl Hg0g2) (newer_than_lits_le_newer Hls2 Hg0g2) Hdjlq Hlrssub Hszdjq Hsz1) => Hg0cs0.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv2 (newer_than_lit_le_newer Htt Hg0g1) (newer_than_lits_le_newer Hls1tl Hg0g1) (newer_than_lits_le_newer Hls2 Hg0g1) Hdjlq0 (newer_than_lits_le_newer Hdjlr0 Hg0g1) Hszdjq Hszdjr) => Hg1cs1.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv3 (newer_than_lit_le_newer Htt (Hg0g3'' )) (newer_than_lits_le_newer Hls1tl Hg0g3'') (newer_than_lits_le_newer Hls2 Hg0g3'') (newer_than_lits_le_newer Hdjlq0 Hg1g3'') Hlrssub2 Hszdjq Hsz2) => Hg3cs3.
    move : (mk_env_uge_newer_cnf Hmkuge (Htt ) Hdjlr0 (Hls2 )) => Hg1cs2.
    move : (mk_env_uge_newer_res Hmkuge) => Hg1rs1.
    move : (newer_than_cnf_le_newer Hg1cs2 Hg1g2) => Hg2cs2.
    move : (mk_env_and_newer_res Hmkand (newer_than_lit_le_newer Htt Hg0g1) (newer_than_lits_copy (size ls2) Hg1rs1) (newer_than_lits_le_newer Hls2 Hg0g1)) => Hg3ls3.
    move : (mk_env_sub_newer_cnf Hmksub2 (newer_than_lit_le_newer Httg1 Hg1g2'') (newer_than_lits_le_newer Hdjlr0 (pos_leb_trans Hg0g1 Hg1g2'')) Hg3ls3) => Hg4cs5. (*rewrite Hszdj in Hg4cs5.*)
    move : (mk_env_and_newer_cnf Hmkand (newer_than_lit_le_newer Htt Hg0g1) (newer_than_lits_copy (size ls2) Hg1rs1) (newer_than_lits_le_newer Hls2 Hg0g1)) => Hg4cs4.
    generalize Hres.
    case (lrs_hd == lit_tt); case (lrs_hd == lit_ff); move => [] _ <- <- _ _; rewrite !newer_than_cnf_catrev;
    try by rewrite Hg0cs0 (newer_than_cnf_le_newer Hg2ls3 Hg2g3) (newer_than_cnf_le_newer Hg2cs2 Hg2g3).
    by rewrite Hg1cs1 (newer_than_cnf_le_newer Hg1cs2 Hg2g3').
    by rewrite Hg3cs3 (newer_than_cnf_le_newer Hg4cs5 Hg3''g4'') (newer_than_cnf_le_newer Hg4cs4 (pos_leb_trans Hg2''g3'' Hg3''g4'')) (newer_than_cnf_le_newer Hg1cs2 Hg1g4'').
Qed.
*)

Lemma mk_env_udiv_newer_cnf :
  forall ls1 E g ls2 E' g' cs lqs lrs,
    mk_env_udiv E g ls1 ls2 = (E', g', cs, lqs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  rewrite/mk_env_udiv/bit_blast_udiv/=. move => ls1 E g ls2 E' g' cs qlrs rlrs .
  dcase (mk_env_eq E g ls2 (copy (size ls2) lit_ff)) => [[[[E_eq] g_eq] cs_eq] lrs_eq] Hmkeq.
  dcase (mk_env_udiv_rec E_eq g_eq (rev ls1) ls2 (copy (size (rev ls1)) lit_ff) (copy (size (rev ls1)) lit_ff)) => [[[[[E_udivr] g_udivr] cs_udivr] lqs_udivr] lrs_udivr] Hmkudivr.
  dcase (mk_env_or E_udivr g_udivr (copy (size lqs_udivr) (lrs_eq)) lqs_udivr)=> [[[[E_or] g_or] cs_or] lrs_or] Hmkor.
  dcase (mk_env_ite E_or g_or lrs_eq ls1 lrs_udivr) =>[[[[E_ite] g_ite] cs_ite] lrs_ite] Hmkite.
  move : (mk_env_ite_newer_gen Hmkite) => Hnewite. move : (mk_env_or_newer_gen Hmkor) => Hnewor.
  move: (mk_env_udiv_rec_newer_gen Hmkudivr) => Hnewudivr. move : (mk_env_eq_newer_gen Hmkeq) => Hneweq.
  case (lrs_eq == lit_tt); case (lrs_eq == lit_ff); case => _ <- <- _ _; move => Htt Hls1 Hls2.
  - have Hcp2: (newer_than_lits g (copy (size ls2) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    exact: (mk_env_eq_newer_cnf Hmkeq Htt Hls2 Hcp2).
  - have Hcp2: (newer_than_lits g (copy (size ls2) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    exact: (mk_env_eq_newer_cnf Hmkeq Htt Hls2 Hcp2).
  - rewrite newer_than_cnf_catrev.
    have Hrev1 : (newer_than_lits g (rev ls1)) by rewrite (newer_than_lits_rev Hls1).
    have Hcp2: (newer_than_lits g (copy (size (rev ls1)) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    rewrite (mk_env_udiv_rec_newer_cnf Hmkudivr (newer_than_lit_le_newer Htt Hneweq) (newer_than_lits_le_newer Hrev1 Hneweq) (newer_than_lits_le_newer Hls2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq)).
    have Hcpf : (newer_than_lits g (copy (size ls2) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    by rewrite (newer_than_cnf_le_newer (mk_env_eq_newer_cnf Hmkeq Htt Hls2 Hcpf) Hnewudivr).
  - rewrite 3!newer_than_cnf_catrev.
    have Hrev1 : (newer_than_lits g (rev ls1)) by rewrite (newer_than_lits_rev Hls1).
    have Hcp2: (newer_than_lits g (copy (size (rev ls1)) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    move: (mk_env_udiv_rec_newer_cnf Hmkudivr (newer_than_lit_le_newer Htt Hneweq) (newer_than_lits_le_newer Hrev1 Hneweq) (newer_than_lits_le_newer Hls2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq)).
    have Hcpf : (newer_than_lits g (copy (size ls2) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    move : (newer_than_cnf_le_newer (mk_env_eq_newer_cnf Hmkeq Htt Hls2 Hcpf) Hnewudivr).
    move => Hncnfeq Hncnfudivr.
    move : (pos_leb_trans Hnewor Hnewite) => Hgnewite.
    rewrite (newer_than_cnf_le_newer Hncnfeq Hgnewite) (newer_than_cnf_le_newer Hncnfudivr Hgnewite).
    move : (pos_leb_trans (pos_leb_trans Hneweq Hnewudivr) Hnewor) => Hgor.
    move : (pos_leb_trans Hnewudivr Hnewor) => Hgeqor.
    move : (mk_env_eq_newer_res Hmkeq ) => Hnlrseq.
    move/andP : (mk_env_udiv_rec_newer_res Hmkudivr (newer_than_lit_le_newer Htt Hneweq) (newer_than_lits_le_newer Hrev1 Hneweq) (newer_than_lits_le_newer Hls2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq)) => [Hnewq Hnewr].
    (* have Hnewerv : newer_than_lits g_or (rev lrs_udivr) by rewrite newer_than_lits_rev; last rewrite (newer_than_lits_le_newer Hnewq Hnewor). *)
    move : (mk_env_ite_newer_cnf Hmkite (newer_than_lit_le_newer Htt Hgor) (newer_than_lit_le_newer Hnlrseq Hgeqor) (newer_than_lits_le_newer Hls1 Hgor) (newer_than_lits_le_newer Hnewq Hnewor)) => Hncnfite.
    rewrite Hncnfite.
    move : (pos_leb_trans Hneweq Hnewudivr) => Hgudivr.
    have Hnewcp : (newer_than_lits g_udivr (copy (size lqs_udivr) (lrs_eq))) by rewrite newer_than_lits_copy// (newer_than_lit_le_newer (mk_env_eq_newer_res Hmkeq) Hnewudivr).
    move : (mk_env_or_newer_cnf Hmkor (newer_than_lit_le_newer Htt Hgudivr) Hnewcp Hnewr) => Hncnfand.
    by rewrite (newer_than_cnf_le_newer Hncnfand Hnewite).
Qed.

Lemma mk_env_udiv_newer_cnf' :
  forall ls1 E g ls2 E' g' cs lqs,
    mk_env_udiv' E g ls1 ls2 = (E', g', cs, lqs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  move => ls1 E g ls2 E' g' cs lqs.
  rewrite /mk_env_udiv'. case Hmk : (mk_env_udiv E g ls1 ls2) => [[[[E_u g_u] cs_u] lqs_u] lrs_u].
  case => _ <- <- _. apply : (mk_env_udiv_newer_cnf Hmk).
Qed.

(* This is a deprecated version of the above lemma that requires no size assumptions. *)
(*
Lemma mk_env_udiv_newer_cnf :
  forall ls1 E g ls2 E' g' cs lqs lrs,
    mk_env_udiv E g ls1 ls2 = (E', g', cs, lqs, lrs) ->
    newer_than_lit g lit_tt ->
    size ls1 = size ls2 ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  rewrite/mk_env_udiv/bit_blast_udiv/=. move => ls1 E g ls2 E' g' cs qlrs rlrs .
  dcase (mk_env_eq E g ls2 (copy (size ls2) lit_ff)) => [[[[E_eq] g_eq] cs_eq] lrs_eq] Hmkeq.
  dcase (mk_env_udiv_rec E_eq g_eq (rev ls1) ls2 (copy (size (rev ls1)) lit_ff) (copy (size (rev ls1)) lit_ff)) => [[[[[E_udivr] g_udivr] cs_udivr] lqs_udivr] lrs_udivr] Hmkudivr.
  dcase (mk_env_and E_udivr g_udivr (copy (size lqs_udivr) (neg_lit lrs_eq)) lqs_udivr)=> [[[[E_and] g_and] cs_and] lrs_and] Hmkand.
  dcase (mk_env_ite E_and g_and lrs_eq (rev lrs_udivr) lrs_udivr) =>[[[[E_ite] g_ite] cs_ite] lrs_ite] Hmkite.
  move : (mk_env_ite_newer_gen Hmkite) => Hnewite. move : (mk_env_and_newer_gen Hmkand) => Hnewand. move: (mk_env_udiv_rec_newer_gen Hmkudivr) => Hnewudivr. move : (mk_env_eq_newer_gen Hmkeq) => Hneweq. 
  case (lrs_eq == lit_tt); case (lrs_eq == lit_ff); case => _ <- <- _ _; move => Htt Hsz Hls1 Hls2.
  - have Hcp2: (newer_than_lits g (copy (size ls2) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    exact: (mk_env_eq_newer_cnf Hmkeq Htt Hls2 Hcp2).
  - have Hcp2: (newer_than_lits g (copy (size ls2) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    exact: (mk_env_eq_newer_cnf Hmkeq Htt Hls2 Hcp2).
  - rewrite newer_than_cnf_catrev. 
    have Hrev1 : (newer_than_lits g (rev ls1)) by rewrite (newer_than_lits_rev Hls1).
    have Hcp2: (newer_than_lits g (copy (size (rev ls1)) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    have Hszcp : (size (copy (size (rev ls1)) lit_ff) = size ls2) by rewrite size_nseq size_rev.
    rewrite (mk_env_udiv_rec_newer_cnf Hmkudivr (newer_than_lit_le_newer Htt Hneweq) (newer_than_lits_le_newer Hrev1 Hneweq) (newer_than_lits_le_newer Hls2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) Hszcp Hszcp).
    have Hcpf : (newer_than_lits g (copy (size ls2) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    by rewrite (newer_than_cnf_le_newer (mk_env_eq_newer_cnf Hmkeq Htt Hls2 Hcpf) Hnewudivr).
  - rewrite 3!newer_than_cnf_catrev. 
    have Hrev1 : (newer_than_lits g (rev ls1)) by rewrite (newer_than_lits_rev Hls1).
    have Hcp2: (newer_than_lits g (copy (size (rev ls1)) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    have Hszcp : (size (copy (size (rev ls1)) lit_ff) = size ls2) by rewrite size_nseq size_rev.
    move: (mk_env_udiv_rec_newer_cnf Hmkudivr (newer_than_lit_le_newer Htt Hneweq) (newer_than_lits_le_newer Hrev1 Hneweq) (newer_than_lits_le_newer Hls2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) Hszcp Hszcp).
    have Hcpf : (newer_than_lits g (copy (size ls2) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    move : (newer_than_cnf_le_newer (mk_env_eq_newer_cnf Hmkeq Htt Hls2 Hcpf) Hnewudivr).
    move => Hncnfeq Hncnfudivr.
    move : (pos_leb_trans Hnewand Hnewite) => Hgnewite.
    rewrite (newer_than_cnf_le_newer Hncnfeq Hgnewite) (newer_than_cnf_le_newer Hncnfudivr Hgnewite).
    move : (pos_leb_trans (pos_leb_trans Hneweq Hnewudivr) Hnewand) => Hgand.
    move : (pos_leb_trans Hnewudivr Hnewand) => Hgeqand.
    move : (mk_env_eq_newer_res Hmkeq ) => Hnlrseq.
    move/andP : (mk_env_udiv_rec_newer_res Hmkudivr (newer_than_lit_le_newer Htt Hneweq) (newer_than_lits_le_newer Hrev1 Hneweq) (newer_than_lits_le_newer Hls2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq)) => [Hnewq Hnewr].
    have Hnewerv : newer_than_lits g_and (rev lrs_udivr) by rewrite newer_than_lits_rev; last rewrite (newer_than_lits_le_newer Hnewq Hnewand).
    move : (mk_env_ite_newer_cnf Hmkite (newer_than_lit_le_newer Htt Hgand) (newer_than_lit_le_newer Hnlrseq Hgeqand) Hnewerv (newer_than_lits_le_newer Hnewq Hnewand)) => Hncnfite.
    rewrite Hncnfite.
    move : (pos_leb_trans Hneweq Hnewudivr) => Hgudivr.
    have Hnewcp : (newer_than_lits g_udivr (copy (size lqs_udivr) (neg_lit lrs_eq))) by rewrite newer_than_lits_copy; last by rewrite newer_than_lit_neg (newer_than_lit_le_newer (mk_env_eq_newer_res Hmkeq) Hnewudivr).
    move : (mk_env_and_newer_cnf Hmkand (newer_than_lit_le_newer Htt Hgudivr) Hnewcp Hnewr) => Hncnfand.
    by rewrite (newer_than_cnf_le_newer Hncnfand Hnewite).
Qed.
*)

Lemma mk_env_udiv_rec_preserve :
  forall ls1 E g ls2 lq lr E' g' cs lqs lrs,
    mk_env_udiv_rec E g ls1 ls2 lq lr = (E', g', cs, lqs, lrs) ->
    env_preserve E E' g.
Proof.
  elim => [|ls1hd ls1tl IH] E g ls2 lq lr E' g' cs lqs lrs.
  - by case => <- _ _ _.
  - rewrite/=.
    dcase (mk_env_uge E g (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_udiv_rec E_sub g_sub ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub) =>[[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_udiv_rec E_hd g_hd ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) (dropmsl (joinlsl ls1hd lr))) =>
    [[[[[E_tl2 g_tl2] cs_tl2] lrs_tl2] lqs_tl2] Hmkudiv2].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lr)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    dcase (mk_env_udiv_rec E_sub2 g_sub2 ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub2) =>
    [[[[[E_tl3 g_tl3] cs_tl3] lrs_tl3] lqs_tl3] Hmkudiv3].
    move => Hres .
    move : (mk_env_uge_preserve Hmkuge) => HE0E1g0.
    move : (mk_env_sub_preserve Hmksub) => HE1E2g1.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv ) => HE2E3g.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv2 ) => HE2E3'g.
    move : (mk_env_and_preserve Hmkand) => HE1E2''g1.
    move : (mk_env_sub_preserve Hmksub2) => HE2''E3''g3.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv3 ) => HE3''E4''g.
    move : (mk_env_uge_newer_gen Hmkuge) => Hg0g1.
    move : (mk_env_sub_newer_gen Hmksub) => Hg1g2.
    move : (pos_leb_trans Hg0g1  Hg1g2) => Hg0g2.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv) => Hg2g3.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv2) => Hg2g3'.
    move : (mk_env_and_newer_gen Hmkand) => Hg1g2''.
    move : (mk_env_sub_newer_gen Hmksub2) => Hg2''g3''.
    move : (pos_leb_trans Hg0g1 (pos_leb_trans Hg1g2 Hg2g3)) => Hg0g3.
    move : (pos_leb_trans Hg1g2'' Hg2''g3'') => Hg1g3''.
    move : (pos_leb_trans Hg0g1 Hg1g3'') => Hg0g3''.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv3) => Hg3''g4''.
    move : (pos_leb_trans Hg1g3'' Hg3''g4'') => Hg1g4''.
    generalize Hres.
    case (lrs_hd == lit_tt); case (lrs_hd == lit_ff); move => [] <- _ _ _ _;
    try by (move : (env_preserve_trans HE0E1g0 (env_preserve_le HE1E2g1 Hg0g1)) => HE0E2g0;
    exact : (env_preserve_trans HE0E2g0 (env_preserve_le HE2E3g Hg0g2))).
    exact : (env_preserve_trans HE0E1g0 (env_preserve_le HE2E3'g Hg0g1)).
    move : (env_preserve_trans HE0E1g0 (env_preserve_le HE1E2''g1 Hg0g1)) => HE0E2''g0.
    move : (env_preserve_trans HE0E2''g0 (env_preserve_le HE2''E3''g3 (pos_leb_trans Hg0g1 Hg1g2''))) => HE0E3''g0.
    exact : (env_preserve_trans HE0E3''g0 (env_preserve_le HE3''E4''g Hg0g3'')).
Qed.

Lemma mk_env_udiv_preserve :
  forall E g ls1 ls2 E' g' cs lqs lrs,
    mk_env_udiv E g ls1 ls2 = (E', g', cs, lqs, lrs) ->
    env_preserve E E' g.
Proof.
  move => E g ls1 ls2 E' g' cs lqs lrs.
  rewrite /mk_env_udiv.
  dcase (mk_env_eq E g ls2 (copy (size ls2) lit_ff)) => [[[[E_eq] g_eq] cs_eq] lrs_eq] Hmkeq.
  dcase (mk_env_udiv_rec E_eq g_eq (rev ls1) ls2 (copy (size (rev ls1)) lit_ff) (copy (size (rev ls1)) lit_ff)) => [[[[[E_udivr] g_udivr] cs_udivr] lqs_udivr] lrs_udivr] Hmkudivr.
  dcase (mk_env_or E_udivr g_udivr (copy (size lqs_udivr) (lrs_eq)) lqs_udivr)=> [[[[E_or] g_or] cs_or] lrs_or] Hmkor.
  dcase (mk_env_ite E_or g_or lrs_eq ls1 lrs_udivr) =>[[[[E_ite] g_ite] cs_ite] lrs_ite] Hmkite.
  move : (mk_env_ite_newer_gen Hmkite) => Hnewite. move : (mk_env_or_newer_gen Hmkor) => Hnewor.
  move: (mk_env_udiv_rec_newer_gen Hmkudivr) => Hnewudivr. move : (mk_env_eq_newer_gen Hmkeq) => Hneweq.
  case (lrs_eq == lit_tt); case (lrs_eq == lit_ff); case => <- _ _ _ _; try (exact : (mk_env_eq_preserve Hmkeq)).
  - move : (mk_env_udiv_rec_preserve Hmkudivr) => HEEudivrgeq.
    move : (mk_env_eq_preserve Hmkeq) => HEEeq.
    move : (env_preserve_le HEEudivrgeq Hneweq) => HEEudivr.
    exact : (env_preserve_trans HEEeq HEEudivr).
  - move : (mk_env_ite_preserve Hmkite) => HEandEitegand.
    move : (mk_env_or_preserve Hmkor) => HEuEorgu.
    move : (mk_env_udiv_rec_preserve Hmkudivr) => HEEudivrgeq.
    move : (mk_env_eq_preserve Hmkeq) => HEEeq.
    move : (env_preserve_trans HEEeq (env_preserve_le HEEudivrgeq Hneweq)) => HEEu.
    move : (pos_leb_trans Hneweq Hnewudivr) => Hggu.
    move : (env_preserve_trans HEEu (env_preserve_le HEuEorgu Hggu)) => HEEor.
    move : (pos_leb_trans Hneweq (pos_leb_trans Hnewudivr Hnewor)) => Hggor.
    exact : (env_preserve_trans HEEor (env_preserve_le HEandEitegand Hggor)).
Qed.

Lemma mk_env_udiv_preserve' :
  forall E g ls1 ls2 E' g' cs lqs,
    mk_env_udiv' E g ls1 ls2 = (E', g', cs, lqs) ->
    env_preserve E E' g.
Proof.
  move => E g ls1 ls2 E' g' cs lqs. rewrite /mk_env_udiv'.
  case Hmk : (mk_env_udiv E g ls1 ls2) => [[[[E_u g_u] cs_u] lqs_u] lrs_u].
  case => <- _ _ _. apply : (mk_env_udiv_preserve Hmk).
Qed.

Lemma mk_env_udiv_rec_sat :
  forall ls1 E g ls2 lq lr E' g' cs lqs lrs,
    mk_env_udiv_rec E g ls1 ls2 lq lr = (E', g', cs, lqs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g lq ->
    newer_than_lits g lr ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  elim => [|ls1hd ls1tl IH] E g ls2 lq lr E' g' cs lqs lrs.
  - by case => _ _ <- _ _ _ _.
  - rewrite/=.
    dcase (mk_env_uge E g (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_udiv_rec E_sub g_sub ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub) =>[[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_udiv_rec E_hd g_hd ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) (dropmsl (joinlsl ls1hd lr))) =>
    [[[[[E_tl2 g_tl2] cs_tl2] lrs_tl2] lqs_tl2] Hmkudiv2].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lr)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    dcase (mk_env_udiv_rec E_sub2 g_sub2 ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub2) =>
    [[[[[E_tl3 g_tl3] cs_tl3] lrs_tl3] lqs_tl3] Hmkudiv3].
    (*
    dcase (mk_env_udiv_rec E g ls1tl ls2 lq lr) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_uge E_tl g_tl (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lrs_tl)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
     *)
    move=> Hres Htt Hlq Hlr Hls1 Hls2. move/andP : Hls1 => [Hls1hd Hls1tl].
    move : (mk_env_uge_preserve Hmkuge) => HE0E1g0.
    move : (mk_env_sub_preserve Hmksub) => HE1E2g1.
    move : (mk_env_uge_newer_gen Hmkuge) => Hg0g1.
    move : (mk_env_sub_newer_gen Hmksub) => Hg1g2.
    move : (pos_leb_trans Hg0g1  Hg1g2) => Hg0g2.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv) => Hg2g3.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv2) => Hg2g3'.
    move : (mk_env_and_newer_gen Hmkand) => Hg1g2''.
    move : (mk_env_sub_newer_gen Hmksub2) => Hg2''g3''.
    move : (pos_leb_trans Hg0g1 (pos_leb_trans Hg1g2 Hg2g3)) => Hg0g3.
    move : (pos_leb_trans Hg1g2'' Hg2''g3'') => Hg1g3''.
    move : (pos_leb_trans Hg0g1 Hg1g3'') => Hg0g3''.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv3) => Hg3''g4''.
    move : (pos_leb_trans Hg1g3'' Hg3''g4'') => Hg1g4''.
    move : (mk_env_uge_newer_res Hmkuge) => Hlrshd.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl (newer_than_lit_le_newer Hlrshd Hg1g2) (newer_than_lits_le_newer Hlq Hg0g2))) => Hdjlq.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl ( Hlrshd ) (newer_than_lits_le_newer Hlq Hg0g1))) => Hdjlq0.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl ( Hls1hd ) ( Hlr ))) => Hdjlr0.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl (newer_than_lit_le_newer Hls1hd Hg0g2) (newer_than_lits_le_newer Hlr Hg0g2))) => Hdjlr.
    move : (mk_env_sub_newer_res Hmksub) => Hlrssub.
    move : (mk_env_sub_newer_res Hmksub2) => Hlrssub2.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv (newer_than_lit_le_newer Htt Hg0g2) Hdjlq Hlrssub (newer_than_lits_le_newer Hls1tl Hg0g2) (newer_than_lits_le_newer Hls2 Hg0g2) )=> HE2E3g.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv2 (newer_than_lit_le_newer Htt Hg0g1) Hdjlq0 (newer_than_lits_le_newer Hdjlr0 Hg0g1) (newer_than_lits_le_newer Hls1tl Hg0g1) (newer_than_lits_le_newer Hls2 Hg0g1)) => HE2E3'g.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv3 (newer_than_lit_le_newer Htt Hg0g3'') (newer_than_lits_le_newer Hdjlq0 Hg1g3'' ) Hlrssub2 (newer_than_lits_le_newer Hls1tl Hg0g3'') (newer_than_lits_le_newer Hls2 Hg0g3'')) => HE2E3'g3''.
    move : (mk_env_and_preserve Hmkand) => HEhdEandg1.
    move : (mk_env_sub_preserve Hmksub2) => HEandEsub2g3.
    move : (mk_env_uge_preserve Hmkuge) => HEEhdg0.
    move : (mk_env_udiv_rec_preserve Hmkudiv)=>HEsubEtlg3.
    have Hff : (newer_than_lit g lit_ff) by rewrite -newer_than_lit_tt_ff; done.
    move : (mk_env_sub_preserve Hmksub) => HEhdEsub.
    move : (mk_env_sub_newer_cnf Hmksub (newer_than_lit_le_newer Hff Hg0g1) (newer_than_lits_le_newer Hdjlr0 Hg0g1) (newer_than_lits_le_newer Hls2 Hg0g1)) => Hntcsub.
    move : (mk_env_uge_sat Hmkuge Htt Hdjlr0 Hls2) => HEhdcshd.
    move : (mk_env_uge_newer_cnf Hmkuge Htt Hdjlr0 Hls2) => Hghdcshd.
    move : (env_preserve_cnf (env_preserve_trans HEhdEsub (env_preserve_le HEsubEtlg3 Hg1g2)) Hghdcshd) => Hcshdeq. rewrite HEhdcshd in Hcshdeq.
    move : (env_preserve_cnf HEsubEtlg3 Hntcsub) => Hcssubeq.
    move : (mk_env_sub_sat Hmksub (newer_than_lit_le_newer Hff Hg0g1) (newer_than_lits_le_newer Hdjlr0 Hg0g1) (newer_than_lits_le_newer Hls2 Hg0g1)) =>HEsubcssub.
    rewrite HEsubcssub in Hcssubeq.
    move : (mk_env_udiv_rec_preserve Hmkudiv2) => HEhdEtl2ghd.
    move : (env_preserve_cnf HEhdEtl2ghd Hghdcshd) => HEtl2cshdeq.
    rewrite HEhdcshd in HEtl2cshdeq.
    move : (mk_env_and_newer_res Hmkand (newer_than_lit_le_newer Htt Hg0g1) (newer_than_lits_copy _ Hlrshd) (newer_than_lits_le_newer Hls2 Hg0g1)) => Hgandlrsand.
    move : (mk_env_sub_sat Hmksub2 (newer_than_lit_le_newer Hff (pos_leb_trans Hg0g1 Hg1g2'')) (newer_than_lits_le_newer Hdjlr0 (pos_leb_trans Hg0g1 Hg1g2'')) Hgandlrsand) => HEsub2cssub2.
    move :Hres;
      case : (lrs_hd == lit_tt); case :(lrs_hd == lit_ff); move => [] <- _ <- _ _; rewrite !interp_cnf_catrev; try by rewrite HE2E3g Hcssubeq Hcshdeq.
    by rewrite HE2E3'g HEtl2cshdeq.
    rewrite HE2E3'g3''.
    move : (mk_env_udiv_rec_preserve Hmkudiv3)=> HEsub2Etl3.
    move : (mk_env_and_sat Hmkand (newer_than_lit_le_newer Htt Hg0g1) (newer_than_lits_copy _ Hlrshd) (newer_than_lits_le_newer Hls2 Hg0g1)) => HEandcsand.
    move : (mk_env_and_newer_cnf Hmkand (newer_than_lit_le_newer Htt Hg0g1) (newer_than_lits_copy _ Hlrshd) (newer_than_lits_le_newer Hls2 Hg0g1)) => Hgandcsand.
    move : (env_preserve_cnf HEsub2Etl3 (newer_than_cnf_le_newer Hgandcsand Hg2''g3'')) => Hcsandeq.
    move : (env_preserve_cnf HEandEsub2g3 Hgandcsand ) => Hcsandeq2.
    rewrite HEandcsand in Hcsandeq2. rewrite Hcsandeq2 in Hcsandeq.
    rewrite Hcsandeq.
    move : (mk_env_sub_newer_cnf Hmksub2 (newer_than_lit_le_newer Hff (pos_leb_trans Hg0g1 Hg1g2'') ) (newer_than_lits_le_newer Hdjlr0 (pos_leb_trans Hg0g1 Hg1g2'')) Hgandlrsand) => Hgsub2cssub2.
    move : (env_preserve_cnf HEsub2Etl3 Hgsub2cssub2) => Hcssub2eq.
    rewrite HEsub2cssub2 in Hcssub2eq. rewrite Hcssub2eq.
    move : (env_preserve_trans HEhdEandg1 (env_preserve_le HEandEsub2g3 Hg1g2'')) => HEhdEsub2.
    move : (env_preserve_trans HEhdEsub2 (env_preserve_le HEsub2Etl3 Hg1g3'')) => HEhdEtl3.
    by rewrite (env_preserve_cnf HEhdEtl3 Hghdcshd) HEhdcshd.
Qed.

(* This is a deprecated version of the above lemma that requires no size assumptions. *)
(*
Lemma mk_env_udiv_rec_sat :
  forall ls1 E g ls2 lq lr E' g' cs lqs lrs,
    mk_env_udiv_rec E g ls1 ls2 lq lr = (E', g', cs, lqs, lrs) ->
    size lq = size ls2 -> size lr = size ls2 ->
    newer_than_lit g lit_tt ->
    newer_than_lits g lq ->
    newer_than_lits g lr ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  elim => [|ls1hd ls1tl IH] E g ls2 lq lr E' g' cs lqs lrs.
  - by case => _ _ <- _ _ _ _.
  - rewrite/=.
    dcase (mk_env_uge E g (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lr)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_udiv_rec E_sub g_sub ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub) =>[[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_udiv_rec E_hd g_hd ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) (dropmsl (joinlsl ls1hd lr))) =>
    [[[[[E_tl2 g_tl2] cs_tl2] lrs_tl2] lqs_tl2] Hmkudiv2].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lr)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
    dcase (mk_env_udiv_rec E_sub2 g_sub2 ls1tl ls2 (dropmsl (joinlsl lrs_hd lq)) lrs_sub2) =>
    [[[[[E_tl3 g_tl3] cs_tl3] lrs_tl3] lqs_tl3] Hmkudiv3].
    (*
    dcase (mk_env_udiv_rec E g ls1tl ls2 lq lr) => [[[[[E_tl g_tl] cs_tl] lrs_tl] lqs_tl] Hmkudiv].
    dcase (mk_env_uge E_tl g_tl (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkuge].
    dcase (mk_env_sub E_hd g_hd (dropmsl (joinlsl ls1hd lrs_tl)) ls2) => [[[[E_sub g_sub] cs_sub] lrs_sub] Hmksub].
    dcase (mk_env_and E_hd g_hd (copy (size ls2) lrs_hd) ls2) => [[[[E_and g_and] cs_and] lrs_and] Hmkand].
    dcase (mk_env_sub E_and g_and (dropmsl (joinlsl ls1hd lrs_tl)) lrs_and) => [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hmksub2].
     *)
    move=> Hres Hszq Hszr Htt Hlq Hlr Hls1 Hls2. move/andP : Hls1 => [Hls1hd Hls1tl].
    have Hszdjq : (size (dropmsl (joinlsl lrs_hd lq)) = size  ls2) by rewrite size_dropmsl size_joinlsl addnK.
    have Hszdjr : (size (dropmsl (joinlsl ls1hd lr)) = size ls2) by rewrite size_dropmsl size_joinlsl addnK.
    move : (bit_blast_sub_size_ss (mk_env_sub_is_bit_blast_sub Hmksub) Hszdjr) => Hsz1.
    have Hszcp : size (copy (size ls2) lrs_hd) = size ls2 by rewrite size_nseq.
    move : (bit_blast_and_size_ss (mk_env_and_is_bit_blast_and Hmkand) Hszcp) => Hszcp0.
    have  Hdjand : (size (dropmsl (joinlsl ls1hd lr)) = size lrs_and) by rewrite size_dropmsl size_joinlsl addnK Hszr -Hszcp0 size_nseq.
    move : (bit_blast_sub_size_ss (mk_env_sub_is_bit_blast_sub Hmksub2) Hdjand) => Hsz2.
    rewrite -Hszcp0 size_nseq in Hsz2.
    move : (bit_blast_udiv_rec_size_ss (mk_env_udiv_rec_is_bit_blast_udiv_rec Hmkudiv) Hszdjq Hsz1) => [Hszrtl Hszqtl].
    have Hszdj : (size (dropmsl (joinlsl ls1hd lrs_tl)) = size ls2) by rewrite size_dropmsl size_joinlsl addnK Hszrtl.
    move : (mk_env_uge_preserve Hmkuge) => HE0E1g0.
    move : (mk_env_sub_preserve Hmksub) => HE1E2g1.
    move : (mk_env_uge_newer_gen Hmkuge) => Hg0g1.
    move : (mk_env_sub_newer_gen Hmksub) => Hg1g2.
    move : (pos_leb_trans Hg0g1  Hg1g2) => Hg0g2.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv) => Hg2g3.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv2) => Hg2g3'.
    move : (mk_env_and_newer_gen Hmkand) => Hg1g2''.
    move : (mk_env_sub_newer_gen Hmksub2) => Hg2''g3''.
    move : (pos_leb_trans Hg0g1 (pos_leb_trans Hg1g2 Hg2g3)) => Hg0g3.
    move : (pos_leb_trans Hg1g2'' Hg2''g3'') => Hg1g3''.
    move : (pos_leb_trans Hg0g1 Hg1g3'') => Hg0g3''.
    move : (mk_env_udiv_rec_newer_gen Hmkudiv3) => Hg3''g4''.
    move : (pos_leb_trans Hg1g3'' Hg3''g4'') => Hg1g4''.
    move : (mk_env_uge_newer_res Hmkuge) => Hlrshd.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl (newer_than_lit_le_newer Hlrshd Hg1g2) (newer_than_lits_le_newer Hlq Hg0g2))) => Hdjlq.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl ( Hlrshd ) (newer_than_lits_le_newer Hlq Hg0g1))) => Hdjlq0.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl ( Hls1hd ) ( Hlr ))) => Hdjlr0.
    move : (newer_than_lits_dropmsl (newer_than_lits_joinlsl (newer_than_lit_le_newer Hls1hd Hg0g2) (newer_than_lits_le_newer Hlr Hg0g2))) => Hdjlr.
    move : (mk_env_sub_newer_res Hmksub) => Hlrssub.
    move : (mk_env_sub_newer_res Hmksub2) => Hlrssub2.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv Hszdjq Hsz1 (newer_than_lit_le_newer Htt Hg0g2) Hdjlq Hlrssub (newer_than_lits_le_newer Hls1tl Hg0g2) (newer_than_lits_le_newer Hls2 Hg0g2) )=> HE2E3g.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv2 Hszdjq Hszdjr (newer_than_lit_le_newer Htt Hg0g1) Hdjlq0 (newer_than_lits_le_newer Hdjlr0 Hg0g1) (newer_than_lits_le_newer Hls1tl Hg0g1) (newer_than_lits_le_newer Hls2 Hg0g1)) => HE2E3'g.
    move : (IH _ _ _ _ _ _ _ _ _ _ Hmkudiv3 Hszdjq Hsz2 (newer_than_lit_le_newer Htt Hg0g3'') (newer_than_lits_le_newer Hdjlq0 Hg1g3'' ) Hlrssub2 (newer_than_lits_le_newer Hls1tl Hg0g3'') (newer_than_lits_le_newer Hls2 Hg0g3'')) => HE2E3'g3''.
    move : (mk_env_and_preserve Hmkand) => HEhdEandg1.
    move : (mk_env_sub_preserve Hmksub2) => HEandEsub2g3.
    move : (mk_env_uge_preserve Hmkuge) => HEEhdg0.
    move : (mk_env_udiv_rec_preserve Hmkudiv)=>HEsubEtlg3.
    have Hff : (newer_than_lit g lit_ff) by rewrite -newer_than_lit_tt_ff; done.
    move : (mk_env_sub_preserve Hmksub) => HEhdEsub.
    move : (mk_env_sub_newer_cnf Hmksub (newer_than_lit_le_newer Hff Hg0g1) (newer_than_lits_le_newer Hdjlr0 Hg0g1) (newer_than_lits_le_newer Hls2 Hg0g1)) => Hntcsub.
    move : (mk_env_uge_sat Hmkuge Htt Hdjlr0 Hls2) => HEhdcshd.
    move : (mk_env_uge_newer_cnf Hmkuge Htt Hdjlr0 Hls2) => Hghdcshd.
    move : (env_preserve_cnf (env_preserve_trans HEhdEsub (env_preserve_le HEsubEtlg3 Hg1g2)) Hghdcshd) => Hcshdeq. rewrite HEhdcshd in Hcshdeq.
    move : (env_preserve_cnf HEsubEtlg3 Hntcsub) => Hcssubeq.
    move : (mk_env_sub_sat Hmksub (newer_than_lit_le_newer Hff Hg0g1) (newer_than_lits_le_newer Hdjlr0 Hg0g1) (newer_than_lits_le_newer Hls2 Hg0g1)) =>HEsubcssub.
    rewrite HEsubcssub in Hcssubeq.
    move : (mk_env_udiv_rec_preserve Hmkudiv2) => HEhdEtl2ghd.
    move : (env_preserve_cnf HEhdEtl2ghd Hghdcshd) => HEtl2cshdeq.
    rewrite HEhdcshd in HEtl2cshdeq.
    move : (mk_env_and_newer_res Hmkand (newer_than_lit_le_newer Htt Hg0g1) (newer_than_lits_copy _ Hlrshd) (newer_than_lits_le_newer Hls2 Hg0g1)) => Hgandlrsand.
    move : (mk_env_sub_sat Hmksub2 (newer_than_lit_le_newer Hff (pos_leb_trans Hg0g1 Hg1g2'')) (newer_than_lits_le_newer Hdjlr0 (pos_leb_trans Hg0g1 Hg1g2'')) Hgandlrsand) => HEsub2cssub2.
    move :Hres;
      case : (lrs_hd == lit_tt); case :(lrs_hd == lit_ff); move => [] <- _ <- _ _; rewrite !interp_cnf_catrev; try by rewrite HE2E3g Hcssubeq Hcshdeq.
    by rewrite HE2E3'g HEtl2cshdeq.
    rewrite HE2E3'g3''.
    move : (mk_env_udiv_rec_preserve Hmkudiv3)=> HEsub2Etl3.
    move : (mk_env_and_sat Hmkand (newer_than_lit_le_newer Htt Hg0g1) (newer_than_lits_copy _ Hlrshd) (newer_than_lits_le_newer Hls2 Hg0g1)) => HEandcsand.
    move : (mk_env_and_newer_cnf Hmkand (newer_than_lit_le_newer Htt Hg0g1) (newer_than_lits_copy _ Hlrshd) (newer_than_lits_le_newer Hls2 Hg0g1)) => Hgandcsand.
    move : (env_preserve_cnf HEsub2Etl3 (newer_than_cnf_le_newer Hgandcsand Hg2''g3'')) => Hcsandeq.
    move : (env_preserve_cnf HEandEsub2g3 Hgandcsand ) => Hcsandeq2.
    rewrite HEandcsand in Hcsandeq2. rewrite Hcsandeq2 in Hcsandeq.
    rewrite Hcsandeq.
    move : (mk_env_sub_newer_cnf Hmksub2 (newer_than_lit_le_newer Hff (pos_leb_trans Hg0g1 Hg1g2'') ) (newer_than_lits_le_newer Hdjlr0 (pos_leb_trans Hg0g1 Hg1g2'')) Hgandlrsand) => Hgsub2cssub2.
    move : (env_preserve_cnf HEsub2Etl3 Hgsub2cssub2) => Hcssub2eq.
    rewrite HEsub2cssub2 in Hcssub2eq. rewrite Hcssub2eq.
    move : (env_preserve_trans HEhdEandg1 (env_preserve_le HEandEsub2g3 Hg1g2'')) => HEhdEsub2.
    move : (env_preserve_trans HEhdEsub2 (env_preserve_le HEsub2Etl3 Hg1g3'')) => HEhdEtl3.
    by rewrite (env_preserve_cnf HEhdEtl3 Hghdcshd) HEhdcshd.
Qed.
*)

Lemma mk_env_udiv_sat :
  forall E g ls1 ls2 E' g' cs lqs lrs,
    mk_env_udiv E g ls1 ls2 = (E', g', cs, lqs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move => E g ls1 ls2 E' g' cs lqs lrs.
  rewrite /mk_env_udiv.
  dcase (mk_env_eq E g ls2 (copy (size ls2) lit_ff)) => [[[[E_eq] g_eq] cs_eq] lrs_eq] Hmkeq.
  dcase (mk_env_udiv_rec E_eq g_eq (rev ls1) ls2 (copy (size (rev ls1)) lit_ff) (copy (size (rev ls1)) lit_ff)) => [[[[[E_udivr] g_udivr] cs_udivr] lqs_udivr] lrs_udivr] Hmkudivr.
  dcase (mk_env_or E_udivr g_udivr (copy (size lqs_udivr) (lrs_eq)) lqs_udivr)=> [[[[E_or] g_or] cs_or] lrs_or] Hmkor.
  dcase (mk_env_ite E_or g_or lrs_eq ls1 lrs_udivr) =>[[[[E_ite] g_ite] cs_ite] lrs_ite] Hmkite.
  move : (mk_env_ite_newer_gen Hmkite) => Hnewite. move : (mk_env_or_newer_gen Hmkor) => Hnewor.
  move: (mk_env_udiv_rec_newer_gen Hmkudivr) => Hnewudivr. move : (mk_env_eq_newer_gen Hmkeq) => Hneweq.
  case (lrs_eq == lit_tt); case (lrs_eq == lit_ff); case => <- _ <- _ _; move => Htt Hls1 Hls2.
  - have Hnewcp :newer_than_lits g (copy (size ls2) lit_ff). by rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff Htt.
    exact : (mk_env_eq_sat Hmkeq Htt Hls2 Hnewcp).
  - have Hnewcp :newer_than_lits g (copy (size ls2) lit_ff). by rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff Htt.
    exact : (mk_env_eq_sat Hmkeq Htt Hls2 Hnewcp).
  - rewrite interp_cnf_catrev.
    have Hnewcp :newer_than_lits g (copy (size ls2) lit_ff). by rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff Htt.
    have Hnrev1 : newer_than_lits g_eq (rev ls1) by rewrite newer_than_lits_rev; last rewrite (newer_than_lits_le_newer Hls1 Hneweq).
    have Hncprev1: newer_than_lits g_eq (copy (size (rev ls1)) lit_ff) by rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff (newer_than_lit_le_newer Htt Hneweq).
    move : (mk_env_udiv_rec_sat Hmkudivr (newer_than_lit_le_newer Htt Hneweq) Hncprev1 Hncprev1 Hnrev1 (newer_than_lits_le_newer Hls2 Hneweq)) => HEucsu.
    rewrite HEucsu.
    move: (mk_env_eq_sat Hmkeq Htt Hls2 Hnewcp) => Hcnfeq.
    move : (mk_env_udiv_rec_preserve Hmkudivr) => HEeqEugeq.
    move : (mk_env_eq_newer_cnf Hmkeq Htt Hls2 Hnewcp) => Hncnfeq.
    by rewrite  (env_preserve_cnf HEeqEugeq Hncnfeq) Hcnfeq.
  - rewrite 3!interp_cnf_catrev.
    have Hnewcp :newer_than_lits g (copy (size ls2) lit_ff). by rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff Htt.
    have Hnrev1 : newer_than_lits g_eq (rev ls1) by rewrite newer_than_lits_rev; last rewrite (newer_than_lits_le_newer Hls1 Hneweq).
    have Hncprev1: newer_than_lits g_eq (copy (size (rev ls1)) lit_ff) by rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff (newer_than_lit_le_newer Htt Hneweq).
    move : (mk_env_udiv_rec_sat Hmkudivr (newer_than_lit_le_newer Htt Hneweq) Hncprev1 Hncprev1 Hnrev1 (newer_than_lits_le_newer Hls2 Hneweq)) => HEucsu.
    move : (mk_env_ite_preserve Hmkite) => HEandEitegor.
    move : (mk_env_or_preserve Hmkor) => HEuEorgu.
    move: (mk_env_eq_sat Hmkeq Htt Hls2 Hnewcp) => Hcnfeq.
    move : (mk_env_udiv_rec_preserve Hmkudivr) => HEeqEugeq.
    move : (mk_env_eq_newer_cnf Hmkeq Htt Hls2 Hnewcp) => Hncnfeq.
    move : (env_preserve_trans HEeqEugeq (env_preserve_le HEuEorgu Hnewudivr)) => HEeqEorgeq.
    move : (env_preserve_trans HEeqEorgeq (env_preserve_le HEandEitegor (pos_leb_trans Hnewudivr Hnewor))) => HEeqEitegeq.
    rewrite (env_preserve_cnf HEeqEitegeq Hncnfeq) Hcnfeq.
    move : (env_preserve_trans HEuEorgu (env_preserve_le HEandEitegor Hnewor)) => HEuEitegu.
    have Hrev1 : (newer_than_lits g (rev ls1)) by rewrite (newer_than_lits_rev Hls1).
    have Hcp2: (newer_than_lits g (copy (size (rev ls1)) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    move: (mk_env_udiv_rec_newer_cnf Hmkudivr (newer_than_lit_le_newer Htt Hneweq) (newer_than_lits_le_newer Hrev1 Hneweq) (newer_than_lits_le_newer Hls2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq)) => Hncsu.
    rewrite (env_preserve_cnf HEuEitegu Hncsu) HEucsu.
    move : (pos_leb_trans Hneweq Hnewudivr) => Hggu.
    have Hnewcpneg : (newer_than_lits g_udivr (copy (size lqs_udivr) (lrs_eq))) by rewrite newer_than_lits_copy// (newer_than_lit_le_newer (mk_env_eq_newer_res Hmkeq) Hnewudivr).
    move/andP : (mk_env_udiv_rec_newer_res Hmkudivr (newer_than_lit_le_newer Htt Hneweq) (newer_than_lits_le_newer Hrev1 Hneweq) (newer_than_lits_le_newer Hls2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq)) => [Hnewq Hnewr].
    move : (mk_env_or_sat Hmkor (newer_than_lit_le_newer Htt Hggu) Hnewcpneg Hnewr) => HEandcsor.
    move : (mk_env_or_newer_cnf Hmkor (newer_than_lit_le_newer Htt Hggu) Hnewcpneg Hnewr) => Hncnfor.
    rewrite (env_preserve_cnf HEandEitegor Hncnfor) HEandcsor.
    move : (pos_leb_trans (pos_leb_trans Hneweq Hnewudivr) Hnewor) => Hggor.
    move : (mk_env_eq_newer_res Hmkeq) => Hgeqlrseq.
    (* have Hnewerv : newer_than_lits g_or (rev lrs_udivr) by rewrite newer_than_lits_rev; last rewrite (newer_than_lits_le_newer Hnewq Hnewor). *)
    by rewrite (mk_env_ite_sat Hmkite (newer_than_lit_le_newer Htt Hggor) (newer_than_lit_le_newer Hgeqlrseq (pos_leb_trans Hnewudivr Hnewor)) (newer_than_lits_le_newer Hls1 Hggor) (newer_than_lits_le_newer Hnewq Hnewor)).
Qed.

Lemma mk_env_udiv_sat' :
  forall E g ls1 ls2 E' g' cs lqs,
    mk_env_udiv' E g ls1 ls2 = (E', g', cs, lqs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move => E g ls1 ls2 E' g' cs lqs. rewrite /mk_env_udiv'.
  case Hmk : (mk_env_udiv E g ls1 ls2) => [[[[E_u g_u] cs_u] lqs_u] lrs_u].
  case => <- _ <- _. apply : (mk_env_udiv_sat Hmk).
Qed.

(* This is a deprecated version of the above lemma that requires no size assumptions. *)
(*
Lemma mk_env_udiv_sat :
  forall E g ls1 ls2 E' g' cs lqs lrs,
    mk_env_udiv E g ls1 ls2 = (E', g', cs, lqs, lrs) ->
    size ls1 = size ls2 ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move => E g ls1 ls2 E' g' cs lqs lrs.
  rewrite /mk_env_udiv.
  dcase (mk_env_eq E g ls2 (copy (size ls2) lit_ff)) => [[[[E_eq] g_eq] cs_eq] lrs_eq] Hmkeq.
  dcase (mk_env_udiv_rec E_eq g_eq (rev ls1) ls2 (copy (size (rev ls1)) lit_ff) (copy (size (rev ls1)) lit_ff)) => [[[[[E_udivr] g_udivr] cs_udivr] lqs_udivr] lrs_udivr] Hmkudivr.
  dcase (mk_env_and E_udivr g_udivr (copy (size lqs_udivr) (neg_lit lrs_eq)) lqs_udivr)=> [[[[E_and] g_and] cs_and] lrs_and] Hmkand.
  dcase (mk_env_ite E_and g_and lrs_eq (rev lrs_udivr) lrs_udivr) =>[[[[E_ite] g_ite] cs_ite] lrs_ite] Hmkite.
  move : (mk_env_ite_newer_gen Hmkite) => Hnewite. move : (mk_env_and_newer_gen Hmkand) => Hnewand. move: (mk_env_udiv_rec_newer_gen Hmkudivr) => Hnewudivr. move : (mk_env_eq_newer_gen Hmkeq) => Hneweq. 
  case (lrs_eq == lit_tt); case (lrs_eq == lit_ff); case => <- _ <- _ _; move => Hsz Htt Hls1 Hls2.
  - have Hnewcp :newer_than_lits g (copy (size ls2) lit_ff). by rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff Htt.
    exact : (mk_env_eq_sat Hmkeq Htt Hls2 Hnewcp).
  - have Hnewcp :newer_than_lits g (copy (size ls2) lit_ff). by rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff Htt.
    exact : (mk_env_eq_sat Hmkeq Htt Hls2 Hnewcp).
  - rewrite interp_cnf_catrev.
    have Hnewcp :newer_than_lits g (copy (size ls2) lit_ff). by rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff Htt.
    have Hszcp : size (copy (size (rev ls1)) lit_ff) = size ls2 by rewrite size_nseq size_rev Hsz.
    have Hnrev1 : newer_than_lits g_eq (rev ls1) by rewrite newer_than_lits_rev; last rewrite (newer_than_lits_le_newer Hls1 Hneweq).
    have Hncprev1: newer_than_lits g_eq (copy (size (rev ls1)) lit_ff) by rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff (newer_than_lit_le_newer Htt Hneweq).
    move : (mk_env_udiv_rec_sat Hmkudivr Hszcp Hszcp (newer_than_lit_le_newer Htt Hneweq) Hncprev1 Hncprev1 Hnrev1 (newer_than_lits_le_newer Hls2 Hneweq)) => HEucsu.
    rewrite HEucsu.
    move: (mk_env_eq_sat Hmkeq Htt Hls2 Hnewcp) => Hcnfeq.
    move : (mk_env_udiv_rec_preserve Hmkudivr) => HEeqEugeq.
    move : (mk_env_eq_newer_cnf Hmkeq Htt Hls2 Hnewcp) => Hncnfeq.
    by rewrite  (env_preserve_cnf HEeqEugeq Hncnfeq) Hcnfeq.
  - rewrite 3!interp_cnf_catrev.
    have Hnewcp :newer_than_lits g (copy (size ls2) lit_ff). by rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff Htt.
    have Hszcp : size (copy (size (rev ls1)) lit_ff) = size ls2 by rewrite size_nseq size_rev Hsz.
    have Hnrev1 : newer_than_lits g_eq (rev ls1) by rewrite newer_than_lits_rev; last rewrite (newer_than_lits_le_newer Hls1 Hneweq).
    have Hncprev1: newer_than_lits g_eq (copy (size (rev ls1)) lit_ff) by rewrite newer_than_lits_copy; last rewrite -newer_than_lit_tt_ff (newer_than_lit_le_newer Htt Hneweq).
    move : (mk_env_udiv_rec_sat Hmkudivr Hszcp Hszcp (newer_than_lit_le_newer Htt Hneweq) Hncprev1 Hncprev1 Hnrev1 (newer_than_lits_le_newer Hls2 Hneweq)) => HEucsu.
    move : (mk_env_ite_preserve Hmkite) => HEandEitegand.
    move : (mk_env_and_preserve Hmkand) => HEuEandgu.
    move: (mk_env_eq_sat Hmkeq Htt Hls2 Hnewcp) => Hcnfeq.
    move : (mk_env_udiv_rec_preserve Hmkudivr) => HEeqEugeq.
    move : (mk_env_eq_newer_cnf Hmkeq Htt Hls2 Hnewcp) => Hncnfeq.
    move : (env_preserve_trans HEeqEugeq (env_preserve_le HEuEandgu Hnewudivr)) => HEeqEandgeq.
    move : ( env_preserve_trans HEeqEandgeq (env_preserve_le HEandEitegand (pos_leb_trans Hnewudivr Hnewand))) => HEeqEitegeq.
    rewrite (env_preserve_cnf HEeqEitegeq Hncnfeq) Hcnfeq.
    move : (env_preserve_trans HEuEandgu (env_preserve_le HEandEitegand Hnewand)) => HEuEitegu.
    have Hrev1 : (newer_than_lits g (rev ls1)) by rewrite (newer_than_lits_rev Hls1).
    have Hcp2: (newer_than_lits g (copy (size (rev ls1)) lit_ff)) by rewrite newer_than_lits_copy; last by rewrite-newer_than_lit_tt_ff Htt.
    move: (mk_env_udiv_rec_newer_cnf Hmkudivr (newer_than_lit_le_newer Htt Hneweq) (newer_than_lits_le_newer Hrev1 Hneweq) (newer_than_lits_le_newer Hls2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) Hszcp Hszcp) => Hncsu.
    rewrite (env_preserve_cnf HEuEitegu Hncsu) HEucsu.
    move : (pos_leb_trans Hneweq Hnewudivr) => Hggu.
    have Hnewcpneg : (newer_than_lits g_udivr (copy (size lqs_udivr) (neg_lit lrs_eq))) by rewrite newer_than_lits_copy; last by rewrite newer_than_lit_neg (newer_than_lit_le_newer (mk_env_eq_newer_res Hmkeq) Hnewudivr).
    move/andP : (mk_env_udiv_rec_newer_res Hmkudivr (newer_than_lit_le_newer Htt Hneweq) (newer_than_lits_le_newer Hrev1 Hneweq) (newer_than_lits_le_newer Hls2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq) (newer_than_lits_le_newer Hcp2 Hneweq)) => [Hnewq Hnewr].
    move : (mk_env_and_sat Hmkand (newer_than_lit_le_newer Htt Hggu) Hnewcpneg Hnewr) => HEandcsand.
    move : (mk_env_and_newer_cnf Hmkand (newer_than_lit_le_newer Htt Hggu) Hnewcpneg Hnewr) => Hncnfand.
    rewrite (env_preserve_cnf HEandEitegand Hncnfand) HEandcsand .
    move : (pos_leb_trans (pos_leb_trans Hneweq Hnewudivr) Hnewand) => Hggand.
    move : (mk_env_eq_newer_res Hmkeq) => Hgeqlrseq.
    have Hnewerv : newer_than_lits g_and (rev lrs_udivr) by rewrite newer_than_lits_rev; last rewrite (newer_than_lits_le_newer Hnewq Hnewand).
    by rewrite (mk_env_ite_sat Hmkite (newer_than_lit_le_newer Htt Hggand) (newer_than_lit_le_newer Hgeqlrseq (pos_leb_trans Hnewudivr Hnewand)) Hnewerv (newer_than_lits_le_newer Hnewq Hnewand)).
Qed.
*)

Lemma mk_env_udiv_rec_env_equal E1 E2 g ls1 ls2 qs rs E1' E2' g1' g2' cs1 cs2 lqs1 lqs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_udiv_rec E1 g ls1 ls2 qs rs = (E1', g1', cs1, lqs1, lrs1) ->
  mk_env_udiv_rec E2 g ls1 ls2 qs rs = (E2', g2', cs2, lqs2, lrs2) ->
  env_equal E1' E2' /\ g1' = g2' /\ cs1 = cs2 /\ lqs1 = lqs2 /\ lrs1 = lrs2.
Proof.
  elim: ls1 E1 E2 g ls2 qs rs E1' E2' g1' g2' cs1 cs2 lqs1 lqs2 lrs1 lrs2 =>
  [| l1 ls1 IH] //= E1 E2 g ls2 qs rs E1' E2' g1' g2' cs1 cs2 lqs1 lqs2 lrs1 lrs2 Heq.
  - case=> ? ? ? ? ?; case=> ? ? ? ? ?; subst. done.
  - dcase (mk_env_uge E1 g (dropmsl (joinlsl l1 rs)) ls2) =>
    [[[[E_uge1 g_uge1] cs_uge1] lrs_uge1] Hv_uge1].
    dcase (mk_env_uge E2 g (dropmsl (joinlsl l1 rs)) ls2) =>
    [[[[E_uge2 g_uge2] cs_uge2] lrs_uge2] Hv_uge2].
    move: (mk_env_uge_env_equal Heq Hv_uge1 Hv_uge2) => [Heq1 [? [? ?]]]; subst.
    case: (lrs_uge2 == lit_tt); last case: (lrs_uge2 == lit_ff).
    + dcase (mk_env_sub E_uge1 g_uge2 (dropmsl (joinlsl l1 rs)) ls2) =>
      [[[[E_sub1 g_sub1] cs_sub1] lrs_sub1] Hv_sub1].
      dcase (mk_env_sub E_uge2 g_uge2 (dropmsl (joinlsl l1 rs)) ls2) =>
      [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hv_sub2].
      move: (mk_env_sub_env_equal Heq1 Hv_sub1 Hv_sub2) => [Heq2 [? [? ?]]]; subst.
      dcase (mk_env_udiv_rec E_sub1 g_sub2 ls1 ls2 (dropmsl (joinlsl lrs_uge2 qs)) lrs_sub2)
      => [[[[[E_div1 g_div1] cs_div1] lqs_div1] lrs_div1] Hv_div1].
      dcase (mk_env_udiv_rec E_sub2 g_sub2 ls1 ls2 (dropmsl (joinlsl lrs_uge2 qs)) lrs_sub2)
      => [[[[[E_div2 g_div2] cs_div2] lqs_div2] lrs_div2] Hv_div2].
      move: (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heq2 Hv_div1 Hv_div2) =>
      [Heq3 [? [? [? ?]]]]; subst.
      case=> ? ? ? ? ?; case=> ? ? ? ? ?; subst. done.
    + dcase (mk_env_udiv_rec E_uge1 g_uge2 ls1 ls2 (dropmsl (joinlsl lrs_uge2 qs))
                             (dropmsl (joinlsl l1 rs))) =>
      [[[[[E_div1 g_div1] cs_div1] lqs_div1] lrs_div1] Hv_div1].
      dcase (mk_env_udiv_rec E_uge2 g_uge2 ls1 ls2 (dropmsl (joinlsl lrs_uge2 qs))
                             (dropmsl (joinlsl l1 rs))) =>
      [[[[[E_div2 g_div2] cs_div2] lqs_div2] lrs_div2] Hv_div2].
      move: (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heq1 Hv_div1 Hv_div2) =>
      [Heq3 [? [? [? ?]]]]; subst.
      case=> ? ? ? ? ?; case=> ? ? ? ? ?; subst. done.
    + dcase (mk_env_and E_uge1 g_uge2 (copy (size ls2) lrs_uge2) ls2) =>
      [[[[E_and1 g_and1] cs_and1] lrs_and1] Hv_and1].
      dcase (mk_env_and E_uge2 g_uge2 (copy (size ls2) lrs_uge2) ls2) =>
      [[[[E_and2 g_and2] cs_and2] lrs_and2] Hv_and2].
      move: (mk_env_and_env_equal Heq1 Hv_and1 Hv_and2) => [Heq2 [? [? ?]]]; subst.
      dcase (mk_env_sub E_and1 g_and2 (dropmsl (joinlsl l1 rs)) lrs_and2) =>
      [[[[E_sub1 g_sub1] cs_sub1] lrs_sub1] Hv_sub1].
      dcase (mk_env_sub E_and2 g_and2 (dropmsl (joinlsl l1 rs)) lrs_and2) =>
      [[[[E_sub2 g_sub2] cs_sub2] lrs_sub2] Hv_sub2].
      move: (mk_env_sub_env_equal Heq2 Hv_sub1 Hv_sub2) => [Heq3 [? [? ?]]]; subst.
      dcase (mk_env_udiv_rec E_sub1 g_sub2 ls1 ls2 (dropmsl (joinlsl lrs_uge2 qs)) lrs_sub2)
      => [[[[[E_div1 g_div1] cs_div1] lqs_div1] lrs_div1] Hv_div1].
      dcase (mk_env_udiv_rec E_sub2 g_sub2 ls1 ls2 (dropmsl (joinlsl lrs_uge2 qs)) lrs_sub2)
      => [[[[[E_div2 g_div2] cs_div2] lqs_div2] lrs_div2] Hv_div2].
      move: (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heq3 Hv_div1 Hv_div2) =>
      [Heq4 [? [? [? ?]]]]; subst.
      case=> ? ? ? ? ?; case=> ? ? ? ? ?; subst. done.
Qed.

Lemma mk_env_udiv_env_equal E1 E2 g ls1 ls2 E1' E2' g1' g2' cs1 cs2 lqs1 lqs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_udiv E1 g ls1 ls2 = (E1', g1', cs1, lqs1, lrs1) ->
  mk_env_udiv E2 g ls1 ls2 = (E2', g2', cs2, lqs2, lrs2) ->
  env_equal E1' E2' /\ g1' = g2' /\ cs1 = cs2 /\ lqs1 = lqs2 /\ lrs1 = lrs2.
Proof.
  rewrite /mk_env_udiv => Heq.
  dcase (mk_env_eq E1 g ls2 (copy (size ls2) lit_ff)) => [[[[E_eq1 g_eq1] cs_eq1] lrs_eq1] Hv_eq1].
  dcase (mk_env_eq E2 g ls2 (copy (size ls2) lit_ff)) => [[[[E_eq2 g_eq2] cs_eq2] lrs_eq2] Hv_eq2].
  move: (mk_env_eq_env_equal Heq Hv_eq1 Hv_eq2) => [Heq1 [? [? ?]]]; subst.
  case: (lrs_eq2 == lit_tt); last case: (lrs_eq2 == lit_ff).
  - case=> ? ? ? ? ?; case=> ? ? ? ? ?; subst. done.
  - dcase (mk_env_udiv_rec E_eq1 g_eq2 (rev ls1) ls2 (copy (size (rev ls1)) lit_ff)
                           (copy (size (rev ls1)) lit_ff))
    => [[[[[E_div1 g_div1] cs_div1] lqs_div1] lrs_div1] Hv_div1].
    dcase (mk_env_udiv_rec E_eq2 g_eq2 (rev ls1) ls2 (copy (size (rev ls1)) lit_ff)
                           (copy (size (rev ls1)) lit_ff))
    => [[[[[E_div2 g_div2] cs_div2] lqs_div2] lrs_div2] Hv_div2].
    move: (mk_env_udiv_rec_env_equal Heq1 Hv_div1 Hv_div2) => [Heq2 [? [? [? ?]]]]; subst.
    case=> ? ? ? ? ?; case=> ? ? ? ? ?; subst. done.
  - dcase (mk_env_udiv_rec E_eq1 g_eq2 (rev ls1) ls2 (copy (size (rev ls1)) lit_ff)
                           (copy (size (rev ls1)) lit_ff))
    => [[[[[E_div1 g_div1] cs_div1] lqs_div1] lrs_div1] Hv_div1].
    dcase (mk_env_udiv_rec E_eq2 g_eq2 (rev ls1) ls2 (copy (size (rev ls1)) lit_ff)
                           (copy (size (rev ls1)) lit_ff))
    => [[[[[E_div2 g_div2] cs_div2] lqs_div2] lrs_div2] Hv_div2].
    move: (mk_env_udiv_rec_env_equal Heq1 Hv_div1 Hv_div2) => [Heq2 [? [? [? ?]]]]; subst.
    dcase (mk_env_or E_div1 g_div2 (copy (size lqs_div2) lrs_eq2) lqs_div2)
    => [[[[E_or1 g_or1] cs_or1] lrs_or1] Hv_or1].
    dcase (mk_env_or E_div2 g_div2 (copy (size lqs_div2) lrs_eq2) lqs_div2)
    => [[[[E_or2 g_or2] cs_or2] lrs_or2] Hv_or2].
    move: (mk_env_or_env_equal Heq2 Hv_or1 Hv_or2) => [Heq3 [? [? ?]]]; subst.
    dcase (mk_env_ite E_or1 g_or2 lrs_eq2 ls1 lrs_div2)
    => [[[[E_ite1 g_ite1] cs_ite1] lrs_ite1] Hv_ite1].
    dcase (mk_env_ite E_or2 g_or2 lrs_eq2 ls1 lrs_div2)
    => [[[[E_ite2 g_ite2] cs_ite2] lrs_ite2] Hv_ite2].
    move: (mk_env_ite_env_equal Heq3 Hv_ite1 Hv_ite2) => [Heq4 [? [? ?]]]; subst.
    case=> ? ? ? ? ?; case=> ? ? ? ? ?; subst. done.
Qed.

Lemma mk_env_udiv'_env_equal E1 E2 g ls1 ls2 E1' E2' g1' g2' cs1 cs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_udiv' E1 g ls1 ls2 = (E1', g1', cs1, lrs1) ->
  mk_env_udiv' E2 g ls1 ls2 = (E2', g2', cs2, lrs2) ->
  env_equal E1' E2' /\ g1' = g2' /\ cs1 = cs2 /\ lrs1 = lrs2.
Proof.
  rewrite /mk_env_udiv' => Heq.
  dcase (mk_env_udiv E1 g ls1 ls2) => [[[[[Ed1 gd1] csd1] qsd1] lrsd1] Hvd1].
  dcase (mk_env_udiv E2 g ls1 ls2) => [[[[[Ed2 gd2] csd2] qsd2] lrsd2] Hvd2].
  move: (mk_env_udiv_env_equal Heq Hvd1 Hvd2) => [Heq1 [? [? [? ?]]]]; subst.
  case=> ? ? ? ?; case=> ? ? ? ?; subst. done.
Qed.



(* ===== bit_blast_umod ===== *)

Definition bit_blast_umod g ls1 ls2 :=
  let '(g', cs, qlrs, rlrs) := bit_blast_udiv g ls1 ls2 in (g', cs, rlrs).

Definition mk_env_umod E g ls1 ls2 :=
  let '(E', g', cs, qlrs, rlrs) := mk_env_udiv E g ls1 ls2 in (E', g', cs, rlrs).

Lemma bit_blast_umod_correct g ls1 ls2 g' cs lrs E bs1 bs2 :
  bit_blast_umod g ls1 ls2 = (g', cs, lrs) ->
  size ls1 = size ls2 ->
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 -> interp_cnf E (add_prelude cs) ->
  enc_bits E lrs (uremB bs1 bs2).
Proof.
  rewrite /bit_blast_umod /uremB.
  dcase (bit_blast_udiv g ls1 ls2) => [[[[gd] csd] qlrs] rlrs] Hbb.
  case=> _ <- <- Hsz Henc1 Henc2 Hics.
  by apply (bit_blast_udiv_correct Hbb).
Qed.

Lemma mk_env_umod_is_bit_blast_umod E g ls1 ls2 E' g' cs lrs :
  mk_env_umod E g ls1 ls2 = (E', g', cs, lrs) ->
  bit_blast_umod g ls1 ls2  = (g', cs, lrs).
Proof.
  rewrite /mk_env_umod /bit_blast_umod.
  dcase (mk_env_udiv E g ls1 ls2) => [[[[[Ed] gd] csd] qlrs] rlrs] Hmk [] _ <- <- <-.
  by rewrite (mk_env_udiv_is_bit_blast_udiv Hmk).
Qed.

Lemma mk_env_umod_newer_gen E g ls1 ls2 E' g' cs lrs :
  mk_env_umod E g ls1 ls2 = (E', g', cs, lrs) ->
  (g <=? g')%positive.
Proof.
  rewrite /mk_env_umod.
  dcase (mk_env_udiv E g ls1 ls2) => [[[[[Ed] gd] csd] qlrs] rlrs] Hmk [] _ <- _ _.
  exact: (mk_env_udiv_newer_gen Hmk).
Qed.

Lemma mk_env_umod_newer_res E g ls1 ls2 E' g' cs lrs :
  mk_env_umod E g ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_lits g' lrs.
Proof.
  rewrite /mk_env_umod.
  dcase (mk_env_udiv E g ls1 ls2) => [[[[[Ed] gd] csd] qlrs] rlrs] Hmk [] _ <- _ <-.
  move=> Hgtt Hgls1 Hgls2.
  move: (mk_env_udiv_newer_res Hmk Hgtt Hgls1 Hgls2) => /andP [H _]. exact: H.
Qed.

Lemma mk_env_umod_newer_cnf E g ls1 ls2 E' g' cs lrs :
  mk_env_umod E g ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_umod.
  dcase (mk_env_udiv E g ls1 ls2) => [[[[[Ed] gd] csd] qlrs] rlrs] Hmk [] _ <- <- _.
  exact: (mk_env_udiv_newer_cnf Hmk).
Qed.

Lemma mk_env_umod_preserve E g ls1 ls2 E' g' cs lrs :
  mk_env_umod E g ls1 ls2 = (E', g', cs, lrs) ->
  env_preserve E E' g.
Proof.
  rewrite /mk_env_umod.
  dcase (mk_env_udiv E g ls1 ls2) => [[[[[Ed] gd] csd] qlrs] rlrs] Hmk [] <- _ _ _.
  exact: (mk_env_udiv_preserve Hmk).
Qed.

Lemma mk_env_umod_sat E g ls1 ls2 E' g' cs lrs :
  mk_env_umod E g ls1 ls2 = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt -> newer_than_lits g ls1 -> newer_than_lits g ls2 ->
  interp_cnf E' cs.
Proof.
  rewrite /mk_env_umod.
  dcase (mk_env_udiv E g ls1 ls2) => [[[[[Ed] gd] csd] qlrs] rlrs] Hmk [] <- _ <- _.
  exact: (mk_env_udiv_sat Hmk).
Qed.

Lemma mk_env_umod_env_equal E1 E2 g ls1 ls2 E1' E2' g1' g2' cs1 cs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_umod E1 g ls1 ls2 = (E1', g1', cs1, lrs1) ->
  mk_env_umod E2 g ls1 ls2 = (E2', g2', cs2, lrs2) ->
  env_equal E1' E2' /\ g1' = g2' /\ cs1 = cs2 /\ lrs1 = lrs2.
Proof.
  rewrite /mk_env_umod => Heq.
  dcase (mk_env_udiv E1 g ls1 ls2) => [[[[[Ed1 gd1] csd1] qsd1] lrsd1] Hvd1].
  dcase (mk_env_udiv E2 g ls1 ls2) => [[[[[Ed2 gd2] csd2] qsd2] lrsd2] Hvd2].
  move: (mk_env_udiv_env_equal Heq Hvd1 Hvd2) => [Heq1 [? [? [? ?]]]]; subst.
  case=> ? ? ? ?; case=> ? ? ? ?; subst. done.
Qed.
