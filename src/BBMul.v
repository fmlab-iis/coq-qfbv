From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBConst BBAnd BBAdd BBShl.
From ssrlib Require Import Var ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Lemma mulB0 p: mulB p (from_nat (size p) 0) = (from_nat (size p) 0).
Proof.
Admitted.

Lemma mulB1 p: mulB p (from_nat (size p) 1) = p.
Proof.
Admitted.

Lemma shlB_mul2exp i (p: bits) : iter i shlB1 p = mulB p (from_nat (size p ) (2^i)).
Proof.
Admitted.

Lemma mulB_addn p m1 m2: mulB p (from_nat (size p) (m1 + m2)) = addB (mulB p (from_nat (size p) m1)) (mulB p (from_nat (size p) m2)). 
Proof.
Admitted.

Lemma addBC : commutative (addB).
Proof.
Admitted.

Lemma and1B n : left_id (ones n) andB.
Proof.
Admitted.

Lemma and0B n : left_zero (from_nat n 0) andB.
Proof.
Admitted.

Lemma mulB_muln p m1 m2 : mulB p (from_nat (size p) (m1*m2)) = mulB (mulB p (from_nat (size p) m1)) (from_nat (size p) m2).
Proof.
Admitted.
  
Lemma andB_copy_case :
  forall b (bs : bits),
    andB (copy (size bs) b) bs = if b then bs else (from_nat (size bs) 0).
Proof.
  move=> [] bs.
  - exact: and1B.
  - rewrite -/(zeros (size bs)) -from_natn0. exact: and0B.
Qed.

Lemma andB_copy_mul :
  forall b (bs : bits),
    andB (copy (size bs) b) bs = mulB bs (from_nat (size bs) b).
Proof.
  move=> b bs. rewrite andB_copy_case. case: b.
  - rewrite mulB1; reflexivity.
  - rewrite mulB0; reflexivity.
Qed.

Lemma bit_blast_shl_int_size_ss :
  forall n ls g g' cs lrs, bit_blast_shl_int g ls n = (g', cs, lrs) -> size ls = size lrs.
Proof.    
  elim => [| n IH] ls g g' cs lrs.
  - by case => _ _ <-.
  - rewrite /=. dcase (bit_blast_shl_int g ls n) => [[[ g_m cs_m] ls_m] Hbbshlint].
    rewrite (IH _ _ _ _ _ Hbbshlint). case => _ _ <-.
    by rewrite size_dropmsl size_joinlsl addnK.
Qed.

Lemma bit_blast_full_adder_size_ss :
  forall ls1 ls2 lcin g g' cs lrs lcout, bit_blast_full_adder g lcin ls1 ls2 = (g', cs, lcout, lrs) -> size ls1 = size ls2 -> size ls1 = size lrs.
Proof.
  elim => [| ls1_hd ls1_tl IH] ls2 lcin g g' cs lrs lcout.
  - move => /=Hbbadd Hnil. symmetry in Hnil; rewrite (size0nil Hnil) in Hbbadd. by case :Hbbadd => _ _ _ <-.
  -
    rewrite /bit_blast_full_adder/bit_blast_full_adder_zip (lock bit_blast_full_adder1) /= -!lock -/bit_blast_full_adder_zip.
    case ls2 =>[|ls2_ht ls2_tl]; try discriminate.
    rewrite /bit_blast_full_adder_zip (lock bit_blast_full_adder1) /= -!lock -/bit_blast_full_adder_zip. 
    dcase (bit_blast_full_adder1 g ls1_hd ls2_ht lcin) => [[[[g_hd cs_hd] lcout_hd] lrs_hd] Hbbfa1].
    dcase (bit_blast_full_adder_zip g_hd lcout_hd (extzip_ff ls1_tl ls2_tl)) => [[[[g_tl cs_tl] lcout_tl] lrs_tl] Hbbfaz].
    move => Hres Hsz. rewrite -addn1 in Hsz; symmetry in Hsz; rewrite -addn1 in Hsz. move : (addIn Hsz) => Hszeq; symmetry in Hszeq. 
    rewrite /bit_blast_full_adder in IH; rewrite (IH _ _ _ _ _ _ _ Hbbfaz Hszeq).
    by case : Hres => _ _ _ <-.
Qed.

Lemma bit_blast_add_size_ss ls1 ls2 g g' cs lrs :
  bit_blast_add g ls1 ls2 = (g', cs, lrs) -> size ls1 = size ls2 -> size ls1 = size lrs.
Proof.
  rewrite /bit_blast_add.
  dcase (bit_blast_full_adder g lit_ff ls1 ls2) => [[[[ga csa] couta] lrsa] Hbbfa].
  case => _ _ <-. 
  exact : (bit_blast_full_adder_size_ss Hbbfa).
Qed.

Lemma bit_blast_and_size_ss :
      forall ls1 ls2 g g' cs lrs,
  bit_blast_and g ls1 ls2 = (g', cs, lrs) -> size ls1 = size ls2 -> size ls1 = size lrs.
Proof.
  elim => [|ls1_hd ls1_tl IH] ls2 g g' cs lrs.
  - move => /=Hbband Hsz0. move : Hbband. symmetry in Hsz0; rewrite (size0nil Hsz0). by case => _ _ <-.
  - rewrite/bit_blast_and /=. case ls2 => [|ls2_hd ls2_tl]; try discriminate.
    rewrite /bit_blast_and_zip (lock bit_blast_and1) /= -!lock -/bit_blast_and_zip. 
    dcase (bit_blast_and1 g ls1_hd ls2_hd) => [[[g_hd cs_hd] lrs_hd] Hbband1]. 
    dcase (bit_blast_and_zip g_hd (extzip_ff ls1_tl ls2_tl)) => [[[g_tl cs_tl] lrs_tl] Hbbandzip].
    move => Hres Hsz. rewrite -addn1 in Hsz; symmetry in Hsz; rewrite -addn1 in Hsz. move : (addIn Hsz) => Hszeq; symmetry in Hszeq. 
    rewrite /bit_blast_and in IH; rewrite (IH _ _ _ _ _ Hbbandzip Hszeq).
    by case : Hres =>  _ _ <-.
Qed.
    
(* ===== bit_blast_mul ===== *)

Fixpoint bit_blast_mul_rec g ls1 ls2 i : generator * cnf * word :=
  match ls2 with
  | [::] => bit_blast_const g (from_nat (size ls1) 0)
  | ls2_hd :: ls2_tl => 
    let '(g_tl, cs_tl, lrs_tl) := bit_blast_mul_rec g ls1 ls2_tl (i + 1) in
    let '(g_hd, cs_hd, lrs_hd) := bit_blast_shl_int g_tl ls1 i in
    if ls2_hd == lit_tt then
      let '(g_add, cs_add, lrs_add) := bit_blast_add g_hd lrs_tl lrs_hd in
      (g_add, catrev (catrev cs_tl cs_hd) cs_add, lrs_add)
    else if ls2_hd == lit_ff then
           (g_tl, cs_tl, lrs_tl)
         else
           let '(g_and, cs_and, lrs_and) := bit_blast_and g_hd (copy (size ls1) ls2_hd) lrs_hd in
           let '(g_add, cs_add, lrs_add) := bit_blast_add g_and lrs_tl lrs_and in
           (g_add, catrev (catrev (catrev cs_tl cs_hd) cs_and) cs_add, lrs_add)
  end.

Fixpoint mk_env_mul_rec E g ls1 ls2 i : env * generator * cnf * word :=
  match ls2 with
  | [::] => mk_env_const E g (from_nat (size ls1) 0)
  | ls2_hd :: ls2_tl =>
    let '(E_tl, g_tl, cs_tl, lrs_tl) := mk_env_mul_rec E g ls1 ls2_tl (i+1) in
    let '(E_hd, g_hd, cs_hd, lrs_hd) := mk_env_shl_int E_tl g_tl ls1 i in
    if ls2_hd == lit_tt then
      let '(E_add, g_add, cs_add, lrs_add) := mk_env_add E_hd g_hd lrs_tl lrs_hd in
      (E_add, g_add, catrev (catrev cs_tl cs_hd) cs_add, lrs_add)
    else if ls2_hd == lit_ff then
           (E_tl, g_tl, cs_tl, lrs_tl)
         else
           let '(E_and, g_and, cs_and, lrs_and) := mk_env_and E_hd g_hd (copy (size ls1) ls2_hd) lrs_hd in
           let '(E_add, g_add, cs_add, lrs_add) := mk_env_add E_and g_and lrs_tl lrs_and in
           (E_add, g_add, catrev (catrev (catrev cs_tl cs_hd) cs_and) cs_add, lrs_add)
  end.
  
Definition bit_blast_mul g ls1 ls2 : generator * cnf * word :=
  bit_blast_mul_rec g ls1 ls2 0.

Definition mk_env_mul E g ls1 ls2 :env * generator * cnf * word :=
  mk_env_mul_rec E g ls1 ls2 0.

Lemma size_copy_literal n (l: literal) : size (copy n l) = n.
Proof.
  exact : size_nseq. Qed.

Lemma bit_blast_mul_rec_size_ss :
  forall ls2 g ls1 i g' cs lrs, bit_blast_mul_rec g ls1 ls2 i = (g', cs, lrs) -> size ls1 = size lrs.
Proof.
  elim => [| ls2_hd ls2_tl IH] g ls1 g' i cs lrs.
  - case => _ _ <-. by rewrite size_map size_from_nat/=.
  - rewrite/=. 
    dcase (bit_blast_mul_rec g ls1 ls2_tl (g' + 1)) => [[[g_tl cs_tl] lrs_tl] Hbbmul].
    dcase (bit_blast_shl_int g_tl ls1 g') => [[[g_hd cs_hd] lrs_hd] Hbbshlint].
    dcase (bit_blast_add g_hd lrs_tl lrs_hd) => [[[g_add cs_add] lrs_add] Hbbadd].
    case Hbband: (bit_blast_and g_hd (copy (size ls1) ls2_hd) lrs_hd) => [[g_and cs_and] lrs_and].
    dcase (bit_blast_add g_and lrs_tl lrs_and) => [[[g_add2 cs_add2] lrs_add2] Hbbadd2] Hres. 
    move : (IH _ _ _ _ _ _ Hbbmul) => Hszmul. rewrite Hszmul.
    move : (bit_blast_shl_int_size_ss Hbbshlint) => Hszshlint.
    move : (size_nseq (size lrs_hd) ls2_hd) => Hszcopy.
    move : (bit_blast_and_size_ss Hbband). rewrite Hszshlint. move => Hszand.
    apply  Hszand in Hszcopy. rewrite size_nseq in Hszand. move : Hres.
    rewrite Hszmul in Hszshlint.
    case (ls2_hd == lit_tt); case (ls2_hd == lit_ff); case => _ _ <-; try done; try by rewrite (bit_blast_add_size_ss Hbbadd Hszshlint). 
    rewrite (bit_blast_add_size_ss Hbbadd2); [done| by rewrite -Hszand].
Qed.

Lemma bit_blast_mul_size_ss :
  forall ls2 g ls1 g' cs lrs, bit_blast_mul g ls1 ls2 = (g', cs, lrs) -> size ls1 = size lrs.
Proof.
  intros. rewrite /bit_blast_mul. exact: (bit_blast_mul_rec_size_ss H).
Qed.

Lemma mk_env_mul_rec_is_bit_blast_mul_rec :
  forall ls2 E g ls1 i E' g' cs lrs,
    mk_env_mul_rec E g ls1 ls2 i = (E', g', cs, lrs) ->
    bit_blast_mul_rec g ls1 ls2 i = (g', cs, lrs).
Proof.
  elim  => [| ls2_hd ls2_tl IH] E g ls1 i E' g' cs lrs.
  - rewrite /=/bit_blast_const. by case => _ <- <- <-. 
  - rewrite /=.  
    dcase (mk_env_mul_rec E g ls1 ls2_tl (i + 1)) => [[[[E_tl g_tl] cs_tl] lrs_tl] Hmkmul].
    dcase (mk_env_shl_int E_tl g_tl ls1 i) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkshlint].
    dcase (mk_env_add E_hd g_hd lrs_tl lrs_hd) => [[[[E_add g_add] cs_add] lrs_add] Hmkadd].
    case Hmkand : (mk_env_and E_hd g_hd (copy (size ls1) ls2_hd) lrs_hd) => [[[E_and g_and] cs_and] lrs_and].
    dcase (mk_env_add E_and g_and lrs_tl lrs_and) => [[[[E_add2 g_add2] cs_add2] lrs_add2] Hmkadd2].
    rewrite (IH _ _ _ _ _ _ _ _ Hmkmul) (mk_env_shl_int_is_bit_blast_shl_int Hmkshlint) (mk_env_add_is_bit_blast_add Hmkadd) (mk_env_and_is_bit_blast_and Hmkand) (mk_env_add_is_bit_blast_add Hmkadd2).
    case (ls2_hd == lit_tt); case (ls2_hd == lit_ff); by  move => [] _<- <- <-.
Qed.

Lemma mk_env_mul_is_bit_blast_mul :
  forall E g ls1 ls2 E' g' cs lrs,
    mk_env_mul E g ls1 ls2 = (E', g', cs, lrs) ->
    bit_blast_mul g ls1 ls2 = (g', cs, lrs).
Proof.
  intros.
  rewrite /mk_env_mul/bit_blast_mul (mk_env_mul_rec_is_bit_blast_mul_rec H). done.
Qed.

Lemma mk_env_mul_rec_newer_gen :
  forall ls2 E g ls1 i E' g' cs lrs,
    mk_env_mul_rec E g ls1 ls2 i = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  elim  => [| ls2_hd ls2_tl IH] E g ls1 i E' g' cs lrs.
  - move => [] _ <- _ _.
    exact: Pos.leb_refl.
  - rewrite /=.  
    dcase (mk_env_mul_rec E g ls1 ls2_tl (i + 1)) => [[[[E_tl g_tl] cs_tl] lrs_tl] Hmkmul].
    dcase (mk_env_shl_int E_tl g_tl ls1 i) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkshlint].
    dcase (mk_env_add E_hd g_hd lrs_tl lrs_hd) => [[[[E_add g_add] cs_add] lrs_add] Hmkadd].
    case Hmkand : (mk_env_and E_hd g_hd (copy (size ls1) ls2_hd) lrs_hd) => [[[E_and g_and] cs_and] lrs_and].
    dcase (mk_env_add E_and g_and lrs_tl lrs_and) => [[[[E_add2 g_add2] cs_add2] lrs_add2] Hmkadd2].
    move : (IH _ _ _ _ _ _ _ _ Hmkmul) => Hgg0.
    move : (mk_env_shl_int_newer_gen Hmkshlint) => Hg0g1.
    move : (mk_env_add_newer_gen Hmkadd) => Hg1g2.
    move : (mk_env_and_newer_gen Hmkand) => Hg1g3.
    move : (mk_env_add_newer_gen Hmkadd2) => Hg3g4.
    move : (pos_leb_trans Hgg0 (pos_leb_trans Hg0g1 Hg1g2)) => Hgg2.
    move : (pos_leb_trans (pos_leb_trans Hgg0 Hg0g1) (pos_leb_trans Hg1g3 Hg3g4)) => Hgg4.
    case (ls2_hd == lit_tt); case (ls2_hd == lit_ff); (move => [] _ <- _ _; try exact).
Qed.

Lemma mk_env_mul_newer_gen:
  forall E g ls1 ls2 E' g' cs lrs,
    mk_env_mul E g ls1 ls2 = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  rewrite/mk_env_mul. intros. exact: (mk_env_mul_rec_newer_gen H).
Qed.

Lemma mk_env_mul_rec_newer_res :
  forall ls2 E g ls1 i E' g' cs lrs,
    mk_env_mul_rec E g ls1 ls2 i = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g' lrs.
Proof.
  elim => [| ls2_hd ls2_tl IH] E g ls1 i E' g' cs lrs.
  - rewrite /=.  move => IH Htt.
    rewrite (mk_env_const_newer_res IH); done.
  - rewrite /mk_env_mul/=.
    dcase (mk_env_mul_rec E g ls1 ls2_tl (i + 1)) => [[[[E_tl g_tl] cs_tl] lrs_tl] Hmkmul].
    dcase (mk_env_shl_int E_tl g_tl ls1 i) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkshlint].
    dcase (mk_env_add E_hd g_hd lrs_tl lrs_hd) => [[[[E_add g_add] cs_add] lrs_add] Hmkadd].
    case Hmkand : (mk_env_and E_hd g_hd (copy (size ls1) ls2_hd) lrs_hd) => [[[E_and g_and] cs_and] lrs_and].
    dcase (mk_env_add E_and g_and lrs_tl lrs_and) => [[[[E_add2 g_add2] cs_add2] lrs_add2] Hmkadd2]. move => Hres Htt. 
    move : (IH _ _ _ _ _ _ _ _ Hmkmul Htt) => Hg0ls.
    move : (mk_env_add_newer_res Hmkadd) => Hg2ls4.
    move : (mk_env_add_newer_res Hmkadd2) => Hg4ls6.
    move : Hres.
    case (ls2_hd == lit_tt); case (ls2_hd == lit_ff); move => [] _ <- _ <-; try exact.
Qed.

Lemma mk_env_mul_newer_res :
  forall E g ls1 ls2 E' g' cs lrs,
    mk_env_mul E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g' lrs.
Proof.
  move => E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_mul. exact : (mk_env_mul_rec_newer_res).
Qed.

Lemma mk_env_mul_rec_newer_cnf :
  forall ls2 E g ls1 i E' g' cs lrs,
    mk_env_mul_rec E g ls1 ls2 i = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  elim => [| ls2_hd ls2_tl IH] E g ls1 i E' g' cs lrs.
  - move => [] _ <- <- _ _ _. done.
  - rewrite /mk_env_mul/=.
    dcase (mk_env_mul_rec E g ls1 ls2_tl (i + 1)) => [[[[E_tl g_tl] cs_tl] lrs_tl] Hmkmul].
    dcase (mk_env_shl_int E_tl g_tl ls1 i) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkshlint].
    dcase (mk_env_add E_hd g_hd lrs_tl lrs_hd) => [[[[E_add g_add] cs_add] lrs_add] Hmkadd].
    case Hmkand : (mk_env_and E_hd g_hd (copy (size ls1) ls2_hd) lrs_hd) => [[[E_and g_and] cs_and] lrs_and].
    dcase (mk_env_add E_and g_and lrs_tl lrs_and) => [[[[E_add2 g_add2] cs_add2] lrs_add2] Hmkadd2]. move => Hres Htt Hgls1 Hgls2. 
    move/andP : Hgls2 => [Hgls2hd Hgls2tl].
    move : (IH _ _ _ _ _ _ _ _ Hmkmul Htt Hgls1 Hgls2tl) => Hg0cs0.
    move : (mk_env_mul_rec_newer_gen Hmkmul) => Hgg0.
    move : (mk_env_shl_int_newer_gen Hmkshlint) => Hg0g1.
    move : (mk_env_add_newer_gen Hmkadd) => Hg1g2.
    move : (mk_env_and_newer_gen Hmkand) => Hg1g3.
    move : (mk_env_add_newer_gen Hmkadd2) => Hg3g4.
    move : (mk_env_mul_rec_newer_res Hmkmul Htt) => Hg0ls.
    move : (mk_env_shl_int_newer_res (newer_than_lit_le_newer Htt Hgg0) (newer_than_lits_le_newer Hgls1 Hgg0) Hmkshlint) => Hg1ls3.
    move : (bit_blast_mul_rec_size_ss (mk_env_mul_rec_is_bit_blast_mul_rec Hmkmul)) => Hszmul.
    move : (bit_blast_shl_int_size_ss (mk_env_shl_int_is_bit_blast_shl_int Hmkshlint)) => Hszshl; rewrite Hszmul in Hszshl.
    move : (bit_blast_add_size_ss (mk_env_add_is_bit_blast_add Hmkadd) Hszshl) => Hszadd.
    move : (mk_env_add_newer_cnf Hmkadd (newer_than_lits_le_newer Hg0ls Hg0g1) Hg1ls3 (newer_than_lit_le_newer Htt (pos_leb_trans Hgg0 Hg0g1)) Hszshl) => Hg2cs2.
    move : (pos_leb_trans Hgg0 Hg0g1) => Hgg1.
    move : (pos_leb_trans Hg0g1 Hg1g2) => Hg0g2.
    move : (pos_leb_trans Hg1g3 Hg3g4) => Hg1g4.
    move : (pos_leb_trans Hgg0 (pos_leb_trans Hg0g1 Hg1g3)) => Hgg3.
    move : (pos_leb_trans Hg0g1 Hg1g3) => Hg0g3.
    move : (mk_env_shl_int_newer_cnf Hmkshlint (newer_than_lits_le_newer Hgls1 Hgg0)) => Hg1cs1.
    move : (mk_env_and_newer_res Hmkand) => Hg3ls5.
    move : (Hg3ls5 (newer_than_lit_le_newer Htt Hgg1) (newer_than_lits_copy (size ls1)  (newer_than_lit_le_newer Hgls2hd Hgg1)) Hg1ls3) => {Hg3ls5}Hg3ls5.
    move : (bit_blast_and_size_ss (mk_env_and_is_bit_blast_and Hmkand))=> Hszand.
    rewrite size_nseq Hszmul in Hszand. move : (Hszand Hszshl) => {Hszand}Hszand.
    move : (mk_env_add_newer_cnf Hmkadd2 (newer_than_lits_le_newer Hg0ls Hg0g3) Hg3ls5 (newer_than_lit_le_newer Htt Hgg3) Hszand) => Hg4cs4.
    move : (mk_env_and_newer_cnf Hmkand) => Hg3cs3.
    move: (Hg3cs3 (newer_than_lit_le_newer Htt Hgg1) (newer_than_lits_copy (size ls1) (newer_than_lit_le_newer Hgls2hd Hgg1)) Hg1ls3) => {Hg3cs3}Hg3cs3.
    move : Hres.
    case (ls2_hd == lit_tt); case (ls2_hd == lit_ff); move => [] _ <- <- _; try exact; rewrite !newer_than_cnf_catrev.
    by rewrite (newer_than_cnf_le_newer Hg0cs0 Hg0g2) (newer_than_cnf_le_newer Hg1cs1 Hg1g2) Hg2cs2.
    by rewrite (newer_than_cnf_le_newer Hg0cs0 Hg0g2) (newer_than_cnf_le_newer Hg1cs1 Hg1g2) Hg2cs2.
    by rewrite (newer_than_cnf_le_newer Hg0cs0 (pos_leb_trans Hg0g3 Hg3g4)) (newer_than_cnf_le_newer Hg1cs1 Hg1g4) (newer_than_cnf_le_newer Hg3cs3 Hg3g4) Hg4cs4.
Qed.

Lemma mk_env_mul_newer_cnf :
  forall E g ls1 ls2 E' g' cs lrs,
    mk_env_mul E g ls1 ls2 = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  move => E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_mul. exact : (mk_env_mul_rec_newer_cnf).
Qed.

    
Lemma bit_blast_mul_rec_correct :
  forall ls2 g bs1 bs2 i E ls1 g' cs lrs,
    bit_blast_mul_rec g ls1 ls2 i = (g', cs, lrs) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) -> (size ls1)>0 ->
    enc_bits E lrs (mulB bs1 (from_nat (size bs1) (to_nat bs2 * (2^i)))).
Proof.
  elim => [|ls2_hd ls2_tl IH] g bs1 bs2 i E ls1 g' cs lrs.
  - rewrite /bit_blast_mul_rec/bit_blast_const. rewrite enc_bits_nil_l.
    case => _ <- <- Henc1 Henc2 Hcnf Hsz1 /=. rewrite (eqP Henc2)/=mul0n.
    rewrite (enc_bits_size Henc1) mulB0. rewrite (enc_bits_map_lit_of_bool_nonempty). exact (add_prelude_enc_bit_tt Hcnf).
    by rewrite -(enc_bits_size Henc1) size_from_nat. 
  - rewrite /bit_blast_mul_rec -/bit_blast_mul_rec
            (lock interp_cnf) (lock bit_blast_add) (lock bit_blast_and)
            (lock bit_blast_shl_int) (lock enc_bits) /= -!lock.
    dcase (bit_blast_mul_rec g ls1 ls2_tl (i + 1)) => [[[g_tl cs_tl] lrs_tl] Hbbmul].
    dcase (bit_blast_shl_int g_tl ls1 i) => [[[g_hd cs_hd] lrs_hd] Hbbshl].
    dcase (bit_blast_add g_hd lrs_tl lrs_hd) => [[[g_add cs_add] lrs_add] Hbbadd].
    case Hbband : (bit_blast_and g_hd (copy (size ls1) ls2_hd) lrs_hd) => [[g_and cs_and] lrs_and].
    dcase (bit_blast_add g_and lrs_tl lrs_and) => [[[g_add2 cs_add2] lrs_add2] Hbbadd2].
    case Htt: (ls2_hd == lit_tt); last case Hff: (ls2_hd == lit_ff).
    + rewrite (eqP Htt). case => _ <- <- Henc1 Henc2.
      rewrite 2!add_prelude_catrev. move => Hcnf Hsz1; split_andb_hyps.
      move : (enc_bits_splitlsb (add_prelude_tt H) Henc2) => /andP[Hls2hd Hls2tl].
      rewrite /splitlsl/= in Hls2tl; rewrite /splitlsl/= in Hls2hd.
      move : (IH _ _ _ _ _ _ _ _ _ Hbbmul Henc1 Hls2tl H Hsz1) => Henclrstl.
      move : (ltn0Sn ((size ls2_tl))) => Hsz2; move : (enc_bits_size Henc2) => /=Hsz2'.
      rewrite Hsz2' in Hsz2.
      move : (joinlsb_splitlsb  Hsz2) => Hsplitbs2.
      rewrite /splitlsb/= in Hsplitbs2; rewrite -Hsplitbs2.
      rewrite (add_prelude_enc_bit_true (head b0 bs2) H) in Hls2hd.
      rewrite Hls2hd/=.
      apply : (bit_blast_add_correct Hbbadd Henclrstl (bit_blast_shl_int_correct Hbbshl Henc1 H1) _ H0).
      rewrite mulnDl mul1n -muln2 -mulnA -expnS.
      by rewrite /shlB shlB_mul2exp mulB_addn addBC addn1.
        by rewrite -(bit_blast_mul_rec_size_ss Hbbmul) -(bit_blast_shl_int_size_ss Hbbshl).
    + rewrite (eqP Hff). case => _ <- <- Henc1 Henc2 Hcnf Hsz1.
      move : (enc_bits_splitlsb (add_prelude_tt Hcnf) Henc2) => /andP[Hls2hd Hls2tl].
      rewrite /splitlsl/= in Hls2tl; rewrite /splitlsl/= in Hls2hd.
      rewrite (add_prelude_enc_bit_is_false _ Hcnf) in Hls2hd. 
      move : (ltn0Sn ((size ls2_tl))) => Hsz2; move : (enc_bits_size Henc2) => /=Hsz2'.
      rewrite Hsz2' in Hsz2.
      move : (joinlsb_splitlsb  Hsz2) => Hsplitbs2.
      rewrite /splitlsb/= in Hsplitbs2; rewrite -Hsplitbs2 (eqP Hls2hd)/=.
      rewrite add0n -muln2 -mulnA -expnS -(addn1 i).
      exact : (IH _ _ _ _ _ _ _ _ _ Hbbmul Henc1 Hls2tl Hcnf Hsz1).
    + case => _ <- <- Henc1 Henc2. rewrite 3!add_prelude_catrev; move => Hcnf Hsz1; split_andb_hyps.
      move : (enc_bits_splitlsb (add_prelude_tt H) Henc2) => /andP[Hls2hd Hls2tl].
      rewrite /splitlsl/= in Hls2tl; rewrite /splitlsl/= in Hls2hd.
      move : (ltn0Sn ((size ls2_tl))) => Hsz2; move : (enc_bits_size Henc2) => /=Hsz2'.
      rewrite Hsz2' in Hsz2.
      move : (joinlsb_splitlsb  Hsz2) => Hsplitbs2.
      rewrite /splitlsb/= in Hsplitbs2; rewrite -Hsplitbs2.
      move : (IH _ _ _ _ _ _ _ _ _ Hbbmul Henc1 Hls2tl H Hsz1) => Henclrstl.
      move : (bit_blast_shl_int_correct Hbbshl Henc1 H2) => Henclrshd.
      move : (enc_bits_copy (size ls1) Hls2hd) => Hcopy.
      move : (bit_blast_and_correct Hbband Hcopy Henclrshd H1) => Henclrsand.
      apply : (bit_blast_add_correct Hbbadd2 Henclrstl Henclrsand _ H0).
      rewrite /shlB shlB_mul2exp. rewrite (enc_bits_size Henc1).
      have ->: ((copy (size bs1) (head b0 bs2) &&# (bs1 *# (size bs1) -bits of (2 ^ i)))%bits=(mulB (bs1 *# (size bs1) -bits of (2 ^ i)) (from_nat (size bs1) (head b0 bs2)))%bits).
      move: (andB_copy_mul (head b0 bs2) (bs1 *# (size bs1) -bits of (2 ^ i))%bits);
      by rewrite size_low.
      rewrite to_nat_cons -mulB_muln -mulB_addn.
      replace (to_nat (behead bs2) * 2 ^ (i + 1) + 2 ^ i * head b0 bs2)
        with ((head b0 bs2) * 2 ^ i + to_nat (behead bs2) * 2^ (i+ 1)) by ring.
      by rewrite mulnDl -muln2 -mulnA -expnS addn1.
      rewrite -(bit_blast_mul_rec_size_ss Hbbmul) -(bit_blast_and_size_ss Hbband) size_nseq; try done. by rewrite (bit_blast_shl_int_size_ss Hbbshl).
Qed.

Lemma bit_blast_mul_correct :
  forall g (bs1 bs2 : bits) E ls1 ls2 g' cs lrs,
    bit_blast_mul g ls1 ls2 = (g', cs, lrs) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    size ls1 >0 ->
    size ls1 = size ls2 ->
    enc_bits E lrs (mulB bs1 bs2).
Proof.
  move => g bs1 bs2 E ls1 ls2 g' cs lrs Hmul Henc_bs1 Henc_bs2 Hcnf Hsz1 Hszeq.
  rewrite -(from_nat_to_nat bs2). replace (to_nat bs2) with (to_nat bs2 * (2^ 0)) by ring.
  rewrite -(enc_bits_size Henc_bs2) -Hszeq (enc_bits_size Henc_bs1).
  exact : (bit_blast_mul_rec_correct Hmul Henc_bs1 Henc_bs2 Hcnf Hsz1). 
Qed.


Lemma mk_env_mul_rec_preserve :
  forall ls2 E g ls1 i E' g' cs lrs,
    mk_env_mul_rec E g ls1 ls2 i = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  elim => [|ls2_hd ls2_tl IH] E g ls1 i E' g' cs lrs.
  - by case => <- _ _ _. 
  - rewrite /mk_env_mul_rec -/mk_env_mul_rec (lock mk_env_add) (lock mk_env_and) (lock mk_env_shl_int) /= -!lock.
    dcase (mk_env_mul_rec E g ls1 ls2_tl (i + 1)) => [[[[E_tl g_tl] cs_tl] lrs_tl] Hmkmul].
    dcase (mk_env_shl_int E_tl g_tl ls1 i) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkshl].
    dcase (mk_env_add E_hd g_hd lrs_tl lrs_hd) => [[[[E_add g_add] cs_add] lrs_add] Hmkadd].
    case Hmkand :(mk_env_and E_hd g_hd (copy (size ls1) ls2_hd) lrs_hd)=> [[[E_and g_and] cs_and] lrs_and].
    dcase (mk_env_add E_and g_and lrs_tl lrs_and) => [[[[E_add2 g_add2] cs_add2] lrs_add2] Hmkadd2].
    move : (IH _ _ _ _ _ _ _ _ Hmkmul) => HEE0g.
    move : (mk_env_add_preserve Hmkadd2) => HE3E4g3.
    move : (mk_env_add_preserve Hmkadd) => HE1E2g1.
    move : (mk_env_and_preserve Hmkand) => HE1E3g1.
    move : (mk_env_shl_int_preserve Hmkshl) => HE0E1g1.
    move : (mk_env_mul_rec_newer_gen Hmkmul) => Hgg0.
    move : (mk_env_shl_int_newer_gen Hmkshl) => Hg0g1.
    move : (env_preserve_le HE1E2g1 (pos_leb_trans Hgg0 Hg0g1)) => HE1E2g.
    move : (env_preserve_le HE0E1g1 Hgg0) => HE0E1g.
    move : (env_preserve_le HE1E3g1 (pos_leb_trans Hgg0 Hg0g1)) => HE1E3g.
    move : (mk_env_and_newer_gen Hmkand) => Hg1g3.
    move : (env_preserve_le HE3E4g3 (pos_leb_trans Hgg0 (pos_leb_trans Hg0g1 Hg1g3))) => HE3E4g.
    move : (env_preserve_trans HEE0g (env_preserve_trans HE0E1g (env_preserve_trans HE1E3g HE3E4g))) => HEE4g.
    move : (env_preserve_trans HEE0g (env_preserve_trans HE0E1g HE1E2g)) => HEE2g.
    case (ls2_hd == lit_tt); case (ls2_hd == lit_ff);
      move => [] <- _ _ _; try exact.
Qed.

Lemma mk_env_mul_preserve :
  forall E g ls1 ls2 E' g' cs lrs,
    mk_env_mul E g ls1 ls2 = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move => E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_mul. move => Hmk. exact (mk_env_mul_rec_preserve Hmk).
Qed.

Lemma mk_env_mul_rec_sat :
  forall ls2 E g ls1 i E' g' cs lrs,
    mk_env_mul_rec E g ls1 ls2 i = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  elim => [|ls2_hd ls2_tl IH] E g ls1 i E' g' cs lrs.
  - by case => _ _ <- _ _ _ _.
  - rewrite /mk_env_mul_rec -/mk_env_mul_rec (lock mk_env_add) (lock mk_env_and) (lock mk_env_shl_int) /= -!lock.
    dcase (mk_env_mul_rec E g ls1 ls2_tl (i + 1)) => [[[[E_tl g_tl] cs_tl] lrs_tl] Hmkmul].
    dcase (mk_env_shl_int E_tl g_tl ls1 i) => [[[[E_hd g_hd] cs_hd] lrs_hd] Hmkshl].
    dcase (mk_env_add E_hd g_hd lrs_tl lrs_hd) => [[[[E_add g_add] cs_add] lrs_add] Hmkadd].
    case Hmkand :(mk_env_and E_hd g_hd (copy (size ls1) ls2_hd) lrs_hd)=> [[[E_and g_and] cs_and] lrs_and].
    dcase (mk_env_add E_and g_and lrs_tl lrs_and) => [[[[E_add2 g_add2] cs_add2] lrs_add2] Hmkadd2].
    move => Hres Htt Hgls1 /andP [Hgls2hd Hgls2tl].
    move : (IH _ _ _ _ _ _ _ _ Hmkmul Htt Hgls1 Hgls2tl) => HE0cs0.
    move : (mk_env_shl_int_preserve Hmkshl) => HE0E1g0.
    move : (mk_env_mul_rec_newer_gen Hmkmul) => Hgg0.
    move : (mk_env_add_preserve Hmkadd) => HE1E2g1.
    move : (mk_env_shl_int_newer_gen Hmkshl) => Hg0g1.
    move : (env_preserve_le HE1E2g1 Hg0g1) => HE1E2g0.
    move : (env_preserve_trans HE0E1g0 HE1E2g0) => HE0E2g0.
    move : (mk_env_mul_rec_newer_cnf Hmkmul Htt Hgls1 Hgls2tl) => Hcnfg0cs0.
    move : (newer_than_cnf_le_newer Hcnfg0cs0 Hg0g1) => Hcnfg1cs0.
    move : (mk_env_mul_rec_newer_res Hmkmul Htt) => Hg0ls.
    move : (newer_than_lits_le_newer Hg0ls Hg0g1) => Hg1ls.
    move : (mk_env_shl_int_newer_res (newer_than_lit_le_newer Htt Hgg0) (newer_than_lits_le_newer Hgls1 Hgg0) Hmkshl) => Hg1ls3.
    move : (bit_blast_mul_rec_size_ss (mk_env_mul_rec_is_bit_blast_mul_rec Hmkmul)). rewrite (bit_blast_shl_int_size_ss (mk_env_shl_int_is_bit_blast_shl_int Hmkshl)) => Hsz; symmetry in Hsz.
    move : (mk_env_add_sat Hmkadd Hg1ls Hg1ls3 (newer_than_lit_le_newer Htt (pos_leb_trans Hgg0 Hg0g1)) Hsz) => HcnfE2cs2.
    move : (mk_env_shl_int_sat Hmkshl (newer_than_lits_le_newer Hgls1 Hgg0)) => HcnfE1cs1.
    move : (mk_env_shl_int_newer_cnf Hmkshl (newer_than_lits_le_newer Hgls1 Hgg0)) => Hg1cs1. move : Hres.
    case (ls2_hd == lit_tt); case (ls2_hd == lit_ff);
    move =>[] <- _ <- _; try rewrite !interp_cnf_catrev;
    try (exact||
         rewrite (env_preserve_cnf HE0E2g0 Hcnfg0cs0) HE0cs0 HcnfE2cs2 (env_preserve_cnf HE1E2g1 Hg1cs1) HcnfE1cs1; done).
    move : (mk_env_and_newer_gen Hmkand) => Hg1g3.
    move : (mk_env_add_newer_gen Hmkadd2) => Hg3g4.
    move : (pos_leb_trans Hgg0 Hg0g1) => Hgg1.
    move : (pos_leb_trans Hg1g3 Hg3g4) => Hg1g4.
    move : (newer_than_lits_le_newer Hg1ls Hg1g3) => Hg3ls.
    move : (newer_than_lits_copy (size ls1) Hgls2hd) => Hgcopyls2.
    move : (mk_env_and_newer_res Hmkand (newer_than_lit_le_newer Htt Hgg1) (newer_than_lits_le_newer Hgcopyls2 Hgg1) Hg1ls3) => Hg3ls5.
    move : (mk_env_add_sat Hmkadd2 Hg3ls Hg3ls5 (newer_than_lit_le_newer Htt (pos_leb_trans Hgg1 Hg1g3))) => HE4cs4.
    move : (mk_env_and_preserve Hmkand) => HE1E3g1.
    move : (mk_env_add_preserve Hmkadd2) => HE3E4g3.
    move : (env_preserve_le HE1E3g1 Hg0g1) => HE1E3g0.
    move : (env_preserve_le HE3E4g3 (pos_leb_trans Hg0g1 Hg1g3)) => HE3E4g0.
    move : (env_preserve_le HE3E4g3 Hg1g3) => HE3E4g1.
    move : (env_preserve_trans HE0E1g0 (env_preserve_trans HE1E3g0 HE3E4g0)) => HE0E4g0.
    rewrite (env_preserve_cnf HE0E4g0 Hcnfg0cs0) HE0cs0 /=.
    move : (env_preserve_trans HE1E3g1 HE3E4g1) => HE1E4g1.
    rewrite (env_preserve_cnf HE1E4g1 Hg1cs1) HcnfE1cs1 /=.
    move : (mk_env_and_newer_cnf Hmkand (newer_than_lit_le_newer Htt Hgg1) (newer_than_lits_le_newer Hgcopyls2 Hgg1) Hg1ls3) => Hg3cs3.
    rewrite (env_preserve_cnf HE3E4g3 Hg3cs3) (mk_env_and_sat Hmkand (newer_than_lit_le_newer Htt Hgg1) (newer_than_lits_le_newer Hgcopyls2 Hgg1) Hg1ls3) HE4cs4.
    done.
    by rewrite -(bit_blast_and_size_ss (mk_env_and_is_bit_blast_and Hmkand)) size_nseq (bit_blast_mul_rec_size_ss (mk_env_mul_rec_is_bit_blast_mul_rec Hmkmul)).
Qed.

Lemma mk_env_mul_sat :
  forall E g ls1 ls2 E' g' cs lrs,
    mk_env_mul E g ls1 ls2  = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 ->
    newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move => E g ls1 ls2 E' g' cs lrs.
  rewrite /mk_env_mul. move => Hmk Hgtt Hgls1 Hgls2.
  exact : (mk_env_mul_rec_sat Hmk Hgtt Hgls1 Hgls2).
Qed.
