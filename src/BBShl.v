
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBIte.
From ssrlib Require Import ZAriths Seqs Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* shl lemmas *)
Lemma shlB_add bs i j :
  shlB i (shlB j bs) = shlB (i + j) bs .
Proof .
  by rewrite /shlB iter_add .
Qed .

Lemma size_joinlsb T b (bs : seq T) :
  size (joinlsb b bs) = (size bs) + 1 .
Proof .
  by rewrite /= addn1 .
Qed .

Lemma shlB1_size bs :
  size (shlB1 bs) = size bs .
Proof .
  rewrite /shlB1 size_dropmsb size_joinlsb .
  rewrite subn1 addn1 .
  reflexivity .
Qed .

Lemma size_joinlsl T l (ls : seq T) :
  size (joinlsl l ls) = size ls + 1 .
Proof .
  exact : size_joinlsb .
Qed .

Lemma size_dropmsl ls :
  size (dropmsl ls) = size ls - 1 .
Proof .
  destruct ls => /= .
  - reflexivity .
  - by rewrite subn1 -pred_Sn size_belast .
Qed .

Lemma shlB_size n bs :
  size (shlB n bs) = size bs .
Proof .
  rewrite /shlB /iter .
  elim: n; first done .
  move => n IH .
  by rewrite shlB1_size .
Qed .

(* ===== bit_blast_shl ===== *)

Definition bit_blast_shl_int1 g ls : generator * cnf * word :=
  (g, [::], dropmsl (joinlsl lit_ff ls)) .

Fixpoint bit_blast_shl_int g ls n : generator * cnf * word :=
  match n with
  | O => (g, [::], ls)
  | S m => let '(g_m, cs_m, ls_m) := bit_blast_shl_int g ls m in
           let '(g1, cs1, ls1) := bit_blast_shl_int1 g_m ls_m in
           (g1, catrev cs_m cs1, ls1)
  end.

Definition mk_env_shl_int1 E g ls : env * generator * cnf * word :=
  (E, g, [::], dropmsl (joinlsl lit_ff ls)) .

Fixpoint mk_env_shl_int E g ls n : env * generator * cnf * word :=
  match n with
  | O => (E, g, [::], ls)
  | S m => let: (E_m, g_m, cs_m, ls_m) := mk_env_shl_int E g ls m in
           let: (E', g', cs, ls') := mk_env_shl_int1 E_m g_m ls_m in
           (E', g', catrev cs_m cs, ls')
  end .

Lemma bit_blast_shl_int1_correct :
  forall g bs E ls g' cs lrs,
    bit_blast_shl_int1 g ls = (g', cs, lrs) ->
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (shlB1 bs).
Proof.
  move => g bs E ls g' cs lrs .
  rewrite /bit_blast_shl_int1 .
  case => _ _ <- Henc_bits Hcs .
  rewrite /shlB1 /= .
  apply: enc_bits_dropmsb; first apply: (add_prelude_tt Hcs) .
  rewrite enc_bits_joinlsb Henc_bits (add_prelude_enc_bit_ff Hcs) // .
Qed .

Lemma bit_blast_shl_int_correct :
  forall g bs n E ls g' cs lrs,
    bit_blast_shl_int g ls n = (g', cs, lrs) ->
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (shlB n bs).
Proof.
  move => g bs .
  elim .
  - move => E ls g' cs lrs .
    rewrite /bit_blast_shl_int /= .
    case => _ _ <- // .
  - move => n IH E ls g' cs lrs .
    rewrite /bit_blast_shl_int (lock interp_cnf) /=
            -!lock -/bit_blast_shl_int .
    case Hm: (bit_blast_shl_int g ls n) => [[g_m cs_m] ls_m] .
    case => _ <- <- .
    move => Hlsbs Hcsm .
    rewrite add_prelude_catrev in Hcsm .
    move : Hcsm => /andP [Hcsm _] .
    move : (IH _ _ _ _ _ Hm Hlsbs Hcsm) => Hls_mbs .
    rewrite /shlB1 .
    apply : enc_bits_dropmsb; first apply: (add_prelude_tt Hcsm) .
    rewrite enc_bits_joinlsb Hls_mbs (add_prelude_enc_bit_ff Hcsm) // .
Qed .

Lemma size_bit_blast_shl_int1 g ls g' cs lrs :
  bit_blast_shl_int1 g ls = (g', cs, lrs) ->
  size ls = size lrs .
Proof .
  rewrite /bit_blast_shl_int1 .
  case => _ _ <- .
  rewrite size_dropmsl size_joinlsl .
  rewrite subn1 addn1.
  reflexivity .
Qed .

Lemma size_bit_blast_shl_int g n ls g' cs lrs :
  bit_blast_shl_int g ls n = (g', cs, lrs) ->
  size ls = size lrs .
Proof .
  rewrite /bit_blast_shl_int /= .
  elim : n g' cs lrs => [|n IH] g' cs lrs .
  - by case => _ _ <- .
  - move: IH; rewrite -/bit_blast_shl_int => IH .
    dcase (bit_blast_shl_int g ls n) => [[[g_m cs_m] ls_m] Hrec] .
    case => _ _ <- .
    move : (IH _ _ _ Hrec) => Hlslsm .
    rewrite size_dropmsl size_joinlsl .
    rewrite addn1 subn1 Hlslsm .
    reflexivity .
Qed .

Fixpoint bit_blast_shl_rec g ls ns i : generator * cnf * word :=
  match ns with
  | [::] => (g, [::], ls)
  | ns_hd::ns_tl =>
    let '(g_tl, cs_tl, ls_tl) := bit_blast_shl_rec g ls ns_tl (2 * i) in
    let '(g_hd, cs_hd, ls_hd) := bit_blast_shl_int g_tl ls_tl i in
    if ns_hd == lit_tt then
      (g_hd, cs_tl++cs_hd, ls_hd)
    else if ns_hd == lit_ff then
           (g_tl, cs_tl, ls_tl)
         else
           let '(g_ite, cs_ite, ls_ite) := bit_blast_ite g_hd ns_hd ls_hd ls_tl in
           (g_ite, cs_tl++cs_hd++cs_ite, ls_ite)
  end .

Definition bit_blast_shl g ls ns : generator * cnf * word :=
  bit_blast_shl_rec g ls ns 1 .

Lemma bit_blast_shl_rec_correct g bs ns i E ls lns g' cs lrs :
  bit_blast_shl_rec g ls lns i = (g', cs, lrs) ->
  enc_bits E ls bs ->
  enc_bits E lns ns ->
  interp_cnf E (add_prelude cs) ->
  enc_bits E lrs (shlB (to_nat ns * i) bs) .
Proof .
  move => Hshlrec Hlsbs Hlnsns .
  move : (enc_bits_size Hlnsns) => Hsizelnsns .
  move : lns ns Hsizelnsns i g' cs lrs Hshlrec Hlsbs Hlnsns.
  apply : seq_ind2 => [|lns_hd ns_hd lns_tl ns_tl Hsizelnns IH] i g' cs lrs .
  - by case => _ <- <- .
  - rewrite /= .
    dcase (bit_blast_shl_rec g ls lns_tl (2*i)) => [[[g_tl cs_tl] ls_tl] Hshlrec] .
    dcase (bit_blast_shl_int g_tl ls_tl i) => [[[g_hd cs_hd] ls_hd] Hshlint] /= .
    case Hlnshdtt : (lns_hd == lit_tt) .
    + case => _ <- <- Hlsbs Hlnsns Hcnf .
      move : Hlnsns; rewrite enc_bits_cons => /andP [Hlnsns_hd Hlnsns_tl] .
      move : Hcnf; rewrite add_prelude_cat => /andP [Hcnfcs_tl Hcnfcs_hd] .
      move : (IH _ _ _ _ Hshlrec Hlsbs Hlnsns_tl Hcnfcs_tl) => Hlstlnstl .
      move : (bit_blast_shl_int_correct Hshlint Hlstlnstl Hcnfcs_hd) .
      rewrite shlB_add .
      move/eqP : Hlnshdtt => Hlnshdtt .
      rewrite Hlnshdtt in Hlnsns_hd .
      rewrite (add_prelude_enc_bit_true ns_hd Hcnfcs_tl) in Hlnsns_hd .
      replace ns_hd with true .
      rewrite mulnA muln2 /= .
      by rewrite -[(1+ (to_nat ns_tl).*2)*i]/(i + ((to_nat ns_tl).*2)*i) .
    + case Hlnshdff : (lns_hd == lit_ff) .
      * case => _ <- <- Hlsbs Hlnsns Hcnfcs_tl .
        move : Hlnsns; rewrite enc_bits_cons => /andP [Hlnsns_hd Hlnsns_tl] .
        move : (IH _ _ _ _ Hshlrec Hlsbs Hlnsns_tl Hcnfcs_tl) .
        move/eqP : Hlnshdff => Hlnshdff .
        rewrite Hlnshdff in Hlnsns_hd .
        rewrite (add_prelude_enc_bit_is_not_true ns_hd Hcnfcs_tl) in Hlnsns_hd .
        rewrite (negbTE Hlnsns_hd) .
        by rewrite mulnA muln2 /= .
      * dcase (bit_blast_ite g_hd lns_hd ls_hd ls_tl) => [[[g_ite cs_ite] ls_ite] Hite] .
        case => _ <- <- Hlsbs Hlnsns Hcnf .
        move : Hcnf; rewrite add_prelude_cat => /andP [Hcnfcs_tl Hcnfcs_others] .
        move : Hcnfcs_others; rewrite add_prelude_cat => /andP [Hcnfcs_hd Hcnfcs_ite] .
        move : Hlnsns; rewrite enc_bits_cons => /andP [Hlnsns_hd Hlnsns_tl] .
        move : (IH _ _ _ _ Hshlrec Hlsbs Hlnsns_tl Hcnfcs_tl) => Hlstlbs .
        move : (bit_blast_shl_int_correct Hshlint Hlstlbs Hcnfcs_hd) => Hlshdbs .
        rewrite shlB_add in Hlshdbs .
        move : (size_bit_blast_shl_int Hshlint) => /eqP Hlshdtl .
        rewrite eq_sym in Hlshdtl .
        move : (bit_blast_ite_correct Hlshdtl Hite Hlnsns_hd Hlshdbs Hlstlbs Hcnfcs_ite) .
        destruct ns_hd .
        + rewrite mulnA muln2 .
          by rewrite -[(i+(to_nat ns_tl).*2 * i)]/((true + (to_nat ns_tl).*2)*i) .
        + rewrite mulnA muln2 .
          by rewrite -[(false + (to_nat ns_tl).*2) * i]/((to_nat ns_tl).*2 *i) .
Qed .

Corollary bit_blast_shl_correct g bs ns E ls lns g' cs lrs :
    bit_blast_shl g ls lns = (g', cs, lrs) ->
    enc_bits E ls bs ->
    enc_bits E lns ns ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (shlB (to_nat ns) bs) .
Proof .
  move => Hshl Hlsbs Hlnsns Hcnf .
  rewrite -(muln1 (to_nat ns)) .
  exact : (bit_blast_shl_rec_correct Hshl Hlsbs Hlnsns Hcnf) .
Qed .

Lemma mk_env_shl_int1_is_bit_blast_shl_int1 E g ls E' g' cs lrs :
    mk_env_shl_int1 E g ls = (E', g', cs, lrs) ->
    bit_blast_shl_int1 g ls = (g', cs, lrs) .
Proof .
  rewrite /mk_env_shl_int1 /bit_blast_shl_int1 .
  by case => _ <- <- <- .
Qed .

Lemma mk_env_shl_int_is_bit_blast_shl_int E g ls i E' g' cs lrs :
    mk_env_shl_int E g ls i = (E', g', cs, lrs) ->
    bit_blast_shl_int g ls i = (g', cs, lrs) .
Proof .
  elim: i E' g' cs lrs => [| i IH ] E' g' cs lrs .
  - rewrite /mk_env_shl_int /bit_blast_shl_int /= .
    by case => _ <- <- <- .
  - rewrite /mk_env_shl_int /= -/mk_env_shl_int .
    dcase (mk_env_shl_int E g ls i) => [[[[E_m g_m] cs_m] ls_m] Henv] .
    rewrite (IH _ _ _ _ Henv) .
    by case => _ <- <- <- .
Qed .

Lemma size_mk_env_shl_int1 E g ls E' g' cs lrs :
  mk_env_shl_int1 E g ls = (E', g', cs, lrs) ->
  size ls = size lrs .
Proof .
  rewrite /mk_env_shl_int1 .
  case => _ _ _ <- .
  rewrite size_dropmsl size_joinlsl .
  rewrite subn1 addn1.
  reflexivity .
Qed .

Lemma size_mk_env_shl_int E g n ls E' g' cs lrs :
  mk_env_shl_int E g ls n = (E', g', cs, lrs) ->
  size ls = size lrs .
Proof .
  rewrite /mk_env_shl_int /= .
  elim : n E' g' cs ls lrs => [|n IH] E' g' cs ls lrs .
  - by case => _ _ _ <- .
  - move: IH; rewrite -/mk_env_shl_int => IH .
    dcase (mk_env_shl_int E g ls n) => [[[[E_m g_m] cs_m] ls_m] Hrec] .
    case => _ _ _ <- .
    move : (IH _ _ _ _ _ Hrec) => Hlslsm .
    rewrite size_dropmsl size_joinlsl .
    rewrite addn1 subn1 Hlslsm .
    reflexivity .
Qed .

Fixpoint mk_env_shl_rec E g ls ns i : env * generator * cnf * word :=
  match ns with
  | [::] => (E, g, [::], ls)
  | ns_hd::ns_tl =>
    let '(E_tl, g_tl, cs_tl, ls_tl) := mk_env_shl_rec E g ls ns_tl (2 * i) in
    let '(E_hd, g_hd, cs_hd, ls_hd) := mk_env_shl_int E_tl g_tl ls_tl i in
    if ns_hd == lit_tt then
      (E_hd, g_hd, cs_tl++cs_hd, ls_hd)
    else if ns_hd == lit_ff then
           (E_tl, g_tl, cs_tl, ls_tl)
         else
           let '(E_ite, g_ite, cs_ite, ls_ite) := mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl in
           (E_ite, g_ite, cs_tl++cs_hd++cs_ite, ls_ite)
  end .

Definition mk_env_shl E g ls ns : env * generator * cnf * word :=
  mk_env_shl_rec E g ls ns 1.

Lemma mk_env_shl_rec_is_bit_blast_shl_rec E g ls ns i E' g' cs lrs :
    mk_env_shl_rec E g ls ns i = (E', g', cs, lrs) ->
    bit_blast_shl_rec g ls ns i = (g', cs, lrs) .
Proof .
  elim : ns i E' g' cs lrs => [|ns_hd ns_tl IH] i E' g' cs lrs .
  - rewrite /mk_env_shl_rec /= -/mk_env_shl_rec .
    by case => _ <- <- <- .
  - rewrite /mk_env_shl_rec /= -/mk_env_shl_rec .
    dcase (mk_env_shl_rec E g ls ns_tl (2*i)) => [[[[E_tl g_tl] cs_tl] ls_tl] Hrec] .
    rewrite (IH _ _ _ _ _ Hrec) .
    dcase (mk_env_shl_int E_tl g_tl ls_tl i) => [[[[E_hd g_hd] cs_hd] ls_hd] Hint] .
    rewrite (mk_env_shl_int_is_bit_blast_shl_int Hint) .
    dcase (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl) => [[[[E_ite g_ite] cs_ite] ls_ite] Hite] .
    rewrite (mk_env_ite_is_bit_blast_ite Hite) /= .
    case Hnshdtt : (ns_hd == lit_tt) .
    + by case => _ <- <- <- .
    + case Hnshdff : (ns_hd == lit_ff); by case => _ <- <- <- .
Qed .

Lemma mk_env_shl_is_bit_blast_shl E g ls ns E' g' cs lrs :
    mk_env_shl E g ls ns = (E', g', cs, lrs) ->
    bit_blast_shl g ls ns = (g', cs, lrs) .
Proof .
  apply mk_env_shl_rec_is_bit_blast_shl_rec .
Qed .

Lemma mk_env_shl_int_newer_gen E g ls n E' g' cs lrs :
    mk_env_shl_int E g ls n = (E', g', cs, lrs) ->
    (g <=? g')%positive .
Proof .
  elim : n E' g' cs lrs => [ | n IH] E' g' cs lrs .
  - rewrite /mk_env_shl_int /=; by t_auto_newer .
  - rewrite /mk_env_shl_int /= -/mk_env_shl_int .
    dcase (mk_env_shl_int E g ls n) => [[[[E_m g_m] cs_m] ls_m] Hint] .
    move : (IH _ _ _ _ Hint) => Hind .
    t_auto_newer .
Qed .

Lemma mk_env_shl_rec_newer_gen E g ls ns i E' g' cs lrs :
    mk_env_shl_rec E g ls ns i = (E', g', cs, lrs) ->
    (g <=? g')%positive .
Proof .
  elim : ns E' g' cs lrs i => [|ns_hd ns_tl IH] E' g' cs lrs i .
  - rewrite /mk_env_shl_rec /=; by t_auto_newer .
  - rewrite /mk_env_shl_rec /= -/mk_env_shl_rec .
    dcase (mk_env_shl_rec E g ls ns_tl (2*i)) => [[[[E_tl g_tl] cs_tl] ls_tl] Hrec] .
    move : (IH _ _ _ _ _ Hrec) => Hggtl .
    dcase (mk_env_shl_int E_tl g_tl ls_tl i) => [[[[E_hd g_hd] cs_hd] ls_hd] Hint] .
    move : (mk_env_shl_int_newer_gen Hint) => Hgtlghd .
    dcase (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl) => [[[[E_ite g_ite] cs_ite] ls_ite] Hite] .
    move : (mk_env_ite_newer_gen Hite) => Hghdgite .
    move : (pos_leb_trans Hggtl Hgtlghd) => Hgghd .
    move : (pos_leb_trans Hgghd Hghdgite) => Hggite .
    case : (ns_hd == lit_tt) .
    + by case => _ <- _ _ .
    + case : (ns_hd == lit_ff); by case => _ <- _ _ .
Qed .

Lemma mk_env_shl_newer_gen E g ls ns E' g' cs lrs :
  mk_env_shl E g ls ns = (E', g', cs, lrs) ->
  (g <=? g')%positive .
Proof .
  exact : mk_env_shl_rec_newer_gen .
Qed .

Lemma mk_env_shl_int_newer_res E g n E' g' ls cs lrs :
  newer_than_lit g lit_tt ->
  newer_than_lits g ls ->
  mk_env_shl_int E g ls n = (E', g', cs, lrs) ->
  newer_than_lits g' lrs .
Proof .
  move => Htt Hls .
  elim : n E' g' cs lrs => [|n IH] E' g' cs lrs .
  - rewrite /mk_env_shl_int /=; by t_auto_newer .
  - rewrite /mk_env_shl_int /= -/mk_env_shl_int .
    dcase (mk_env_shl_int E g ls n) => [[[[E_m g_m] cs_m] ls_m] Hint] .
    case => _ <- _ <- .
    move : (IH _ _ _ _ Hint) => Hlsm .
    move : (mk_env_shl_int_newer_gen Hint) => Hggm .
    move : (newer_than_lit_le_newer Htt Hggm) => Hgmtt .
    generalize Hgmtt .
    rewrite newer_than_lit_tt_ff => Hgmff .
    move : (newer_than_lits_joinlsl Hgmff Hlsm) => Hgmjoinlsl .
    move : (newer_than_lits_splitmsl Hgmtt Hgmjoinlsl) => /andP [Hsplit1 _] .
    by rewrite /dropmsl .
Qed .

Lemma mk_env_shl_rec_newer_res E g i E' g' ls ns cs lrs :
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g ns ->
  mk_env_shl_rec E g ls ns i = (E', g', cs, lrs) ->
  newer_than_lits g' lrs .
Proof .
  move => Hgtt Hgls .
  elim : ns E' g' cs lrs i => [|ns_hd ns_tl IH] E' g' cs lrs i Hgns .
  - rewrite /mk_env_shl_rec /=; by t_auto_newer .
  - rewrite /mk_env_shl_rec /= -/mk_env_shl_rec .
    move : Hgns; rewrite newer_than_lits_cons => /andP [Hgnshd Hgnstl] .
    dcase (mk_env_shl_rec E g ls ns_tl (2*i)) => [[[[E_tl g_tl] cs_tl] ls_tl] Hrec] .
    move : (IH _ _ _ _ _ Hgnstl Hrec) => Hgtllstl .
    move : (mk_env_shl_rec_newer_gen Hrec) => Hggtl .
    dcase (mk_env_shl_int E_tl g_tl ls_tl i) => [[[[E_hd g_hd] cs_hd] ls_hd] Hint] .
    move : (mk_env_shl_int_newer_res (newer_than_lit_le_newer Hgtt Hggtl) Hgtllstl Hint) => Hghdlshd .
    dcase (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl) => [[[[E_ite g_ite] cs_ite] ls_ite] Hite] .
    move : (mk_env_ite_newer_res Hite) => Hgitelsite .
    case : (ns_hd == lit_tt) .
    + by case => _ <- _ <- .
    + case : (ns_hd == lit_ff); by case => _ <- _ <- .
Qed .

Lemma mk_env_shl_newer_res E g ls ns E' g' cs lrs :
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g ns ->
  mk_env_shl E g ls ns = (E', g', cs, lrs) ->
  newer_than_lits g' lrs .
Proof .
  apply mk_env_shl_rec_newer_res .
Qed .

Lemma mk_env_shl_int_newer_cnf E g ls n E' g' cs lr :
    mk_env_shl_int E g ls n = (E', g', cs, lr) ->
    newer_than_lits g ls ->
    newer_than_cnf g' cs .
Proof .
  elim : n E' g' cs lr => [|n IH] E' g' cs lr .
  - rewrite /mk_env_shl_int /=; by case => _ <- <- _ _ .
  - rewrite /mk_env_shl_int /= -/mk_env_shl_int .
    dcase (mk_env_shl_int E g ls n) => [[[[E_m g_m] cs_m] ls_m] Hint] .
    case => _ <- <- _ Hgls .
    move : (IH _ _ _ _ Hint Hgls) => Hgmcsm .
    by rewrite newer_than_cnf_catrev Hgmcsm /= .
Qed .

Lemma mk_env_shl_rec_newer_cnf E g ls ns i E' g' cs lr :
  mk_env_shl_rec E g ls ns i = (E', g', cs, lr) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g ns ->
  newer_than_cnf g' cs .
Proof .
  elim : ns E' g' cs lr i => [|ns_hd ns_tl IH] E' g' cs lr i .
  - rewrite /mk_env_shl_rec /=; by case => _ <- <- _ .
  - rewrite /mk_env_shl_rec /= -/mk_env_shl_rec .
    dcase (mk_env_shl_rec E g ls ns_tl (2*i)) => [[[[E_tl g_tl] cs_tl] ls_tl] Hrec] .
    dcase (mk_env_shl_int E_tl g_tl ls_tl i) => [[[[E_hd g_hd] cs_hd] ls_hd] Hint] .
    dcase (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl) => [[[[E_ite g_ite] cs_ite] ls_ite] Hite] .
    move => Htemp Hgtt Hgls /andP [Hgnshd Hgnstl] .
    move : Htemp .
    move : (IH _ _ _ _ _ Hrec Hgtt Hgls Hgnstl) => Hgtlcstl .
    move : (mk_env_shl_rec_newer_res Hgtt Hgls Hgnstl Hrec) => Hgtllstl .
    move : (mk_env_shl_int_newer_cnf Hint Hgtllstl) => Hghdcshd .
    move : (mk_env_shl_int_newer_gen Hint) => Hgtlghd .
     case : (ns_hd == lit_tt) .
    + case => _ <- <- _ .
      by rewrite newer_than_cnf_cat Hghdcshd (newer_than_cnf_le_newer Hgtlcstl Hgtlghd) .
    + case : (ns_hd == lit_ff) .
      * by case => _ <- <- _ .
      * case => _ <- <- _ .
        rewrite !newer_than_cnf_cat .
        move : (mk_env_ite_newer_gen Hite) => Hghdgite .
        move : (mk_env_shl_rec_newer_gen Hrec) => Hggtl .
        move : (newer_than_lit_le_newer Hgnshd (pos_leb_trans Hggtl Hgtlghd)) => Hghdnshd .
        move : (mk_env_shl_int_newer_res (newer_than_lit_le_newer Hgtt Hggtl) Hgtllstl Hint) => Hghdlshd .
        move : (size_mk_env_shl_int Hint) => -/eqP Hlstllshd .
        rewrite eq_sym in Hlstllshd .
        move : (mk_env_ite_newer_cnf Hlstllshd Hite Hghdnshd Hghdlshd (newer_than_lits_le_newer Hgtllstl Hgtlghd)) => Hgitecsite .
        by rewrite (newer_than_cnf_le_newer Hgtlcstl (pos_leb_trans Hgtlghd Hghdgite)) (newer_than_cnf_le_newer Hghdcshd Hghdgite) Hgitecsite .
Qed .

Lemma mk_env_shl_newer_cnf E g ls ns E' g' cs lrs :
  mk_env_shl E g ls ns = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g ns ->
  newer_than_cnf g' cs .
Proof .
  rewrite /mk_env_shl .
  exact : mk_env_shl_rec_newer_cnf .
Qed .

Lemma mk_env_shl_int_preserve E g ls n E' g' cs lrs :
    mk_env_shl_int E g ls n = (E', g', cs, lrs) ->
    env_preserve E E' g .
Proof .
  elim : n E' g' cs lrs => [| n IH] E' g' cs lrs .
  - rewrite /mk_env_shl_int /=; by case => <- _ _ _ .
  - rewrite /mk_env_shl_int /= -/mk_env_shl_int .
    dcase (mk_env_shl_int E g ls n) => [[[[E_m g_m] cs_m] ls_m] Hint] .
    case => <- _ _ _ .
    by apply : (IH _ _ _ _ Hint) .
Qed .

Lemma mk_env_shl_rec_preserve E g ls ns i E' g' cs lrs :
  mk_env_shl_rec E g ls ns i = (E', g', cs, lrs) ->
  env_preserve E E' g .
Proof .
  elim : ns E' g' cs lrs i => [| ns_hd ns_tl IH] E' g' cs lrs i .
  - rewrite /mk_env_shl_rec /=; by case => <- _ _ _ .
  - rewrite /mk_env_shl_rec /= -/mk_env_shl_rec .
    dcase (mk_env_shl_rec E g ls ns_tl (2*i)) => [[[[E_tl g_tl] cs_tl] ls_tl] Hrec] .
    dcase (mk_env_shl_int E_tl g_tl ls_tl i) => [[[[E_hd g_hd] cs_hd] ls_hd] Hint] .
    dcase (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl) => [[[[E_ite g_ite] cs_ite] ls_ite] Hite] .
    move : (IH _ _ _ _ _ Hrec) => HEEtl .
    move : (mk_env_shl_int_preserve Hint) => HEtlEhd .
    move : (mk_env_ite_preserve Hite) => HEhdEite .
    move : (mk_env_shl_rec_newer_gen Hrec) => Hggtl .
    move : (mk_env_shl_int_newer_gen Hint) => Hgtlghd .
    move : (mk_env_ite_newer_gen Hite) => Hghdgite .
    move : (env_preserve_le HEtlEhd Hggtl) => HEtlEhdg .
    move : (env_preserve_le HEhdEite (pos_leb_trans Hggtl Hgtlghd)) => HEhdEiteg .
    case : (ns_hd == lit_tt) .
    + case => <- _ _ _; by t_auto_preserve .
    + case : (ns_hd == lit_ff); case => <- _ _ _; by t_auto_preserve .
Qed .

Lemma mk_env_shl_preserve E g ls ns E' g' cs lrs :
  mk_env_shl E g ls ns = (E', g', cs, lrs) ->
  env_preserve E E' g .
Proof .
  rewrite /mk_env_shl. exact : mk_env_shl_rec_preserve .
Qed .

Lemma mk_env_shl_int_sat E g ls n E' g' cs lrs :
  mk_env_shl_int E g ls n = (E', g', cs, lrs) ->
  newer_than_lits g ls ->
  interp_cnf E' cs .
Proof .
  elim : n E' g' cs lrs => [|n IH] E' g' cs lrs .
  - rewrite /mk_env_shl_int /= .
    by case => <- _ <- _ .
  - rewrite /mk_env_shl_int /= -/mk_env_shl_int .
    dcase (mk_env_shl_int E g ls n) => [[[[E_m g_m] cs_m] ls_m] Hint] .
    case => <- _ <- _ .
    rewrite interp_cnf_catrev => Hgls .
    move : (IH _ _ _ _ Hint Hgls) .
    by t_auto_newer .
Qed .

Lemma mk_env_shl_rec_sat E g ls ns i E' g' cs lrs :
    mk_env_shl_rec E g ls ns i = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls -> newer_than_lits g ns ->
    interp_cnf E' cs .
Proof .
  elim : ns E' g' cs lrs i => [|ns_hd ns_tl IH] E' g' cs lrs i .
  - rewrite /mk_env_shl_rec /= .
    by case => <- _ <- _ .
  - rewrite /mk_env_shl_rec /= -/mk_env_shl_rec .
    dcase (mk_env_shl_rec E g ls ns_tl (2*i)) => [[[[E_tl g_tl] cs_tl] ls_tl] Hrec] .
    dcase (mk_env_shl_int E_tl g_tl ls_tl i) => [[[[E_hd g_hd] cs_hd] ls_hd] Hint] .
    dcase (mk_env_ite E_hd g_hd ns_hd ls_hd ls_tl) => [[[[E_ite g_ite] cs_ite] ls_ite] Hite] .
    move => Htmp Hgtt Hgls /andP [Hgnshd Hgnstl] .
    move : Htmp .
    move : (mk_env_shl_rec_newer_gen Hrec) => Hggtl .
    move : (mk_env_shl_int_newer_gen Hint) => Hgtlghd .
    move : (IH _ _ _ _ _ Hrec Hgtt Hgls Hgnstl) => HEtlcstl .
    move : (mk_env_shl_rec_newer_res Hgtt Hgls Hgnstl Hrec) => Hgtllstl .
    move : (mk_env_shl_int_newer_res (newer_than_lit_le_newer Hgtt Hggtl) Hgtllstl Hint) => Hghdlshd .
    move : (mk_env_shl_int_sat Hint Hgtllstl) => HEhdcshd .
    move : (mk_env_shl_int_preserve Hint) => HEtlEhd .
    move : (mk_env_ite_preserve Hite) => HEhdEite .
    move : (mk_env_shl_rec_newer_cnf Hrec Hgtt Hgls Hgnstl) => Hgtlcstl .
    move : (mk_env_shl_int_newer_cnf Hint Hgtllstl) => Hghdcshd .
    case : (ns_hd == lit_tt) .
    + case => <- _ <- _ .
      rewrite interp_cnf_cat (env_preserve_cnf HEtlEhd Hgtlcstl) .
        by t_auto_newer .
    + case : (ns_hd == lit_ff) .
      * by case => <- _ <- _ .
      * case => <- _ <- _ .
        rewrite !interp_cnf_cat .
        move : (size_mk_env_shl_int Hint) => -/eqP Hlstllshd .
        rewrite eq_sym in Hlstllshd .
        move : (mk_env_ite_sat Hlstllshd Hite (newer_than_lit_le_newer Hgnshd (pos_leb_trans Hggtl Hgtlghd)) Hghdlshd (newer_than_lits_le_newer Hgtllstl Hgtlghd)) => HEitecsite .
        rewrite (env_preserve_cnf HEhdEite Hghdcshd) .
        rewrite (env_preserve_cnf HEhdEite (newer_than_cnf_le_newer Hgtlcstl Hgtlghd)) .
        rewrite (env_preserve_cnf HEtlEhd Hgtlcstl) .
        by t_auto_newer .
Qed .

Lemma mk_env_shl_sat E g ls ns E' g' cs lrs :
  mk_env_shl E g ls ns = (E', g', cs, lrs) ->
  newer_than_lit g lit_tt ->
  newer_than_lits g ls -> newer_than_lits g ns ->
  interp_cnf E' cs.
Proof .
  rewrite /mk_env_shl; exact : mk_env_shl_rec_sat .
Qed .
