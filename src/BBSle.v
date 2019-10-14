From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBEq BBDisj BBSlt.
From ssrlib Require Import ZAriths Seqs Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ===== bit_blast_sle ===== *)

Definition bit_blast_sle g ls1 ls2: generator * cnf * literal :=
  let '(g_eq, cs_eq, r_eq) := bit_blast_eq g ls1 ls2 in
  let '(g_slt, cs_slt, r_slt) := bit_blast_slt g_eq ls1 ls2 in
  let '(g_disj, cs_disj, r_disj) := bit_blast_disj g_slt r_eq r_slt in
  (g_disj, catrev cs_eq (catrev cs_slt cs_disj), r_disj).

Lemma bit_blast_sle_correct g bs1 bs2 E ls1 ls2 g' cs lr:
  bit_blast_sle g ls1 ls2 = (g', cs, lr) ->
  size ls1 = size ls2 ->
  enc_bits E ls1 bs1 -> enc_bits E ls2 bs2 ->
  interp_cnf E (add_prelude cs) ->
  enc_bit E lr (sleB bs1 bs2).
Proof.
  rewrite /bit_blast_sle.
  case Hbb_eq : (bit_blast_eq g ls1 ls2) => [[g_eq cs_eq] r_eq].
  case Hbb_slt : (bit_blast_slt g_eq ls1 ls2) => [[g_slt cs_slt] r_slt].
  case Hbb_disj : (bit_blast_disj g_slt r_eq r_slt) => [[g_disj cs_disj] r_disj].
  case=> _ <- <- Hsz Henc1 Henc2.
  rewrite !add_prelude_catrev => /andP [Hics_eq /andP [Hics_slt Hics_disj]].
  rewrite /sleB.
  move: (bit_blast_eq_correct Hbb_eq Hsz Henc1 Henc2 Hics_eq) => HeEr_eq.
  move: (bit_blast_slt_correct Hbb_slt Henc1 Henc2 Hics_slt) => HeEr_slt.
  exact: (bit_blast_disj_correct Hbb_disj HeEr_eq HeEr_slt Hics_disj).
Qed.

Definition mk_env_sle E g ls1 ls2: env * generator * cnf * literal :=
  let '(E_eq, g_eq, cs_eq, r_eq) := mk_env_eq E g ls1 ls2 in
  let '(E_slt, g_slt, cs_slt, r_slt) := mk_env_slt E_eq g_eq ls1 ls2 in
  let '(E_disj, g_disj, cs_disj, r_disj) := mk_env_disj E_slt g_slt r_eq r_slt in
  (E_disj, g_disj, catrev cs_eq (catrev cs_slt cs_disj), r_disj).

Lemma mk_env_sle_is_bit_blast_sle E g ls1 ls2 E' g' cs lr:
    mk_env_sle E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_sle g ls1 ls2 = (g', cs, lr).
Proof.
  rewrite /mk_env_sle /bit_blast_sle. 
  case Hmkeq : (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] r_eq].
  case Hmkslt : (mk_env_slt E_eq g_eq ls1 ls2) => [[[E_slt g_slt] cs_slt] r_slt].
  case Hmkdisj : (mk_env_disj E_slt g_slt r_eq r_slt) => [[[E_disj g_disj] cs_disj] r_disj].
  rewrite (mk_env_eq_is_bit_blast_eq Hmkeq) {Hmkeq}.
  rewrite (mk_env_slt_is_bit_blast_slt Hmkslt) {Hmkslt}.
  rewrite (mk_env_disj_is_bit_blast_disj Hmkdisj) {Hmkdisj}.
  by case=> _ <- <- <-.
Qed.

Lemma mk_env_sle_newer_gen E g ls1 ls2 E' g' cs lr:
    mk_env_sle E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  rewrite /mk_env_sle.
  case Hmkeq : (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] r_eq].
  case Hmkslt : (mk_env_slt E_eq g_eq ls1 ls2) => [[[E_slt g_slt] cs_slt] r_slt].
  case Hmkdisj : (mk_env_disj E_slt g_slt r_eq r_slt) => [[[E_disj g_disj] cs_disj] r_disj].
  case=> _ <- _ _.
  move: (mk_env_eq_newer_gen Hmkeq) => {Hmkeq} Hgge.
  move: (mk_env_slt_newer_gen Hmkslt) => {Hmkslt} Hgegs.
  move: (mk_env_disj_newer_gen Hmkdisj) => {Hmkdisj} Hgsgd.
  move : (pos_leb_trans Hgge Hgegs) => Hggs {Hgge Hgegs}.
  exact: (pos_leb_trans Hggs Hgsgd).
Qed.

Lemma mk_env_sle_newer_res E g ls1 ls2 E' g' cs lr:
    mk_env_sle E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g' lr.
Proof.
  rewrite /mk_env_sle.
  case Hmkeq : (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] r_eq].
  case Hmkslt : (mk_env_slt E_eq g_eq ls1 ls2) => [[[E_slt g_slt] cs_slt] r_slt].
  case Hmkdisj : (mk_env_disj E_slt g_slt r_eq r_slt) => [[[E_disj g_disj] cs_disj] r_disj].
  case=> _ <- _ <-.
  exact: (mk_env_disj_newer_res Hmkdisj).
Qed.

Lemma mk_env_sle_newer_cnf E g ls1 ls2 E' g' cs lr:
    mk_env_sle E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  rewrite /mk_env_sle.
  case Hmkeq : (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] r_eq].
  case Hmkslt : (mk_env_slt E_eq g_eq ls1 ls2) => [[[E_slt g_slt] cs_slt] r_slt].
  case Hmkdisj : (mk_env_disj E_slt g_slt r_eq r_slt) => [[[E_disj g_disj] cs_disj] r_disj].
  case=> _ <- <- _ Hgt Hgl1 Hgl2. rewrite /= !newer_than_cnf_catrev.
  (* newer_than_cnf g_disj cs_eq *)
  move : (mk_env_eq_newer_cnf Hmkeq Hgt Hgl1 Hgl2) => Hgece.
  move : (mk_env_slt_newer_gen Hmkslt) => Hgegs.
  move : (mk_env_disj_newer_gen Hmkdisj) => Hgsgd.
  move : (pos_leb_trans Hgegs Hgsgd) => Hgegd.
  rewrite (newer_than_cnf_le_newer Hgece Hgegd) /=.  
  (* newer_than_cnf g_disj cs_slt *)
  move : (mk_env_eq_newer_gen Hmkeq) => Hgge.
  move : (newer_than_lit_le_newer Hgt Hgge) => Hget.
  move : (newer_than_lits_le_newer Hgl1 Hgge) => Hgel1.
  move : (newer_than_lits_le_newer Hgl2 Hgge) => Hgel2.
  move : (mk_env_slt_newer_cnf Hmkslt Hget Hgel1 Hgel2) => Hgscs.
  rewrite (newer_than_cnf_le_newer Hgscs Hgsgd) /=.  
  (* newer_than_cnf g_disj cs_disj *)
  move : (mk_env_eq_newer_res Hmkeq) => Hgere.
  move : (mk_env_slt_newer_res Hmkslt) => Hgsrs.
  move : (newer_than_lit_le_newer Hgere Hgegs) => Hgsre.
  exact: (mk_env_disj_newer_cnf Hmkdisj Hgsre Hgsrs).
Qed.

Lemma mk_env_sle_preserve E g ls1 ls2 E' g' cs lr:
    mk_env_sle E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  rewrite /mk_env_sle.
  case Hmkeq : (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] r_eq].
  case Hmkslt : (mk_env_slt E_eq g_eq ls1 ls2) => [[[E_slt g_slt] cs_slt] r_slt].
  case Hmkdisj : (mk_env_disj E_slt g_slt r_eq r_slt) => [[[E_disj g_disj] cs_disj] r_disj].
  case=> <- _ _ _.
  move : (mk_env_eq_preserve Hmkeq) => HpEEeg.
  move : (mk_env_slt_preserve Hmkslt) => HpEeEsge.
  move : (mk_env_disj_preserve Hmkdisj) => HpEsEdgs.
  move : (mk_env_eq_newer_gen Hmkeq) => {Hmkeq} Hgge.
  move : (mk_env_slt_newer_gen Hmkslt) => {Hmkslt} Hgegs.
  move : (env_preserve_le HpEeEsge Hgge) => HpEeEsg.
  move : (pos_leb_trans Hgge Hgegs) => Hggs.
  move : (env_preserve_le HpEsEdgs Hggs) => HpEsEdg.
  move: (env_preserve_trans HpEEeg HpEeEsg) => HpEEsg.
  exact: (env_preserve_trans HpEEsg HpEsEdg).
Qed.

Lemma mk_env_sle_sat E g ls1 ls2 E' g' cs lr:
    mk_env_sle E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  rewrite /mk_env_sle.
  case Hmkeq : (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] r_eq].
  case Hmkslt : (mk_env_slt E_eq g_eq ls1 ls2) => [[[E_slt g_slt] cs_slt] r_slt].
  case Hmkdisj : (mk_env_disj E_slt g_slt r_eq r_slt) => [[[E_disj g_disj] cs_disj] r_disj].
  case=> <- _ <- _ Hgt Hgl1 Hgl2.
  rewrite !interp_cnf_catrev.
  (* interp_cnf E_disj cs_eq *)
  move : (mk_env_eq_sat Hmkeq Hgt Hgl1 Hgl2) => HiEece.
  move : (mk_env_slt_preserve Hmkslt) => HpEeEsge.
  move : (mk_env_disj_preserve Hmkdisj) => HpEsEdgs.
  move : (mk_env_slt_newer_gen Hmkslt) => Hgegs.
  move : (env_preserve_le HpEsEdgs Hgegs) => HpEsEdge.
  move : (env_preserve_trans HpEeEsge HpEsEdge) => HpEeEdge.
  move : (mk_env_eq_newer_cnf Hmkeq Hgt Hgl1 Hgl2) => Hgece.
  rewrite (env_preserve_cnf HpEeEdge Hgece).
  rewrite HiEece /=.
  (* interp_cnf E_disj cs_slt *)
  move : (mk_env_eq_newer_gen Hmkeq) => Hgge.
  move : (newer_than_lit_le_newer Hgt Hgge) => Hget.
  move : (newer_than_lits_le_newer Hgl1 Hgge) => Hgel1.
  move : (newer_than_lits_le_newer Hgl2 Hgge) => Hgel2.
  move : (mk_env_slt_sat Hmkslt Hget Hgel1 Hgel2) => HiEscs.
  move : (mk_env_slt_newer_cnf Hmkslt Hget Hgel1 Hgel2) => Hgscs.
  rewrite (env_preserve_cnf HpEsEdgs Hgscs).
  rewrite HiEscs /=.
  (* interp_cnf E_disj cs_disj *)
  move : (mk_env_eq_newer_res Hmkeq) => Hgere.
  move : (newer_than_lit_le_newer Hgere Hgegs) => Hgsre.
  move : (mk_env_slt_newer_res Hmkslt) => Hgsrs.
  exact : (mk_env_disj_sat Hmkdisj Hgsre Hgsrs).
Qed.


(*
Lemma toZK n : cancel (@toZ n) (@fromZ n.+1).
Proof.
  induction n.
  - case/tupleP => b x.
    case b.
    + by rewrite tuple0 /toZ !tupleE/= /joinlsb/=.
    + rewrite tuple0 /toZ !tupleE/=. by apply val_inj.
  - case/tupleP => b x.
    move : (IHn x) => Hx.
    case b;
      rewrite /toZ/= beheadCons theadCons/=;
      case Hsplitx : (splitmsb x) => [c bs].
      case Hc: c; rewrite Hc in Hsplitx.
      * rewrite /joinlsb/= toNegZCons.
        rewrite -Hx /toZ/= Hsplitx/=.
        rewrite Z.double_spec toNegZ_toNat.
        assert (0<=(Z.of_nat (2 ^ n - 1 - toNat bs)))%Z as Hge0 by omega.
        case Hofnat: (Z.of_nat (2 ^ n - 1 - toNat bs))=>[|p|p].
        by apply val_inj.
        Local Opaque fromNegZ.
        rewrite /fromZ 2!Z.opp_involutive -!Zpred_succ/=.
        by apply val_inj.
        rewrite Hofnat in Hge0.
        move: (Pos2Z.neg_is_neg p)=> Hneg ; omega.
      * rewrite /joinlsb/= toPosZCons.
        rewrite -Hx /toZ/= Hsplitx/=.
        rewrite toPosZ_toNat.
        assert (0<=(Z.of_nat (toNat bs)))%Z as Hge0 by omega.
        case Hofnat: (Z.of_nat (toNat bs)) => [|p|p].
        rewrite /=fromPosZ_fromNat/= /joinlsb/=.
        rewrite fromNat0. by apply val_inj.
        omega.
        Local Opaque fromPosZ.
        rewrite /fromZ/=. by apply val_inj.
        rewrite Hofnat in Hge0.
        move: (Pos2Z.neg_is_neg p)=> Hneg ; omega.
    + case Hc: c; rewrite Hc in Hsplitx.
      * rewrite /joinlsb/=toNegZCons.
        rewrite -Hx/toZ/=Hsplitx/=.
        rewrite Z.double_spec toNegZ_toNat.
        assert (0<=Z.of_nat (2 ^ n - 1 - toNat bs))%Z as Hge0 by omega.
        case Hofnat: (Z.of_nat (2 ^ n - 1 - toNat bs))=>[|p|p].
        by apply val_inj.
        rewrite /fromZ 2!Z.opp_involutive -!Zpred_succ/=.
        by apply val_inj.
        rewrite Hofnat in Hge0.
        move: (Pos2Z.neg_is_neg p)=> Hneg ; omega.
      * rewrite /joinlsb/= toPosZCons.
        rewrite -Hx /toZ/= Hsplitx/=.
        rewrite toPosZ_toNat.
        assert (0<=(Z.of_nat (toNat bs)))%Z as Hge0 by omega.
        case Hofnat: (Z.of_nat (toNat bs)) => [|p|p].
        by apply val_inj.
        rewrite /fromZ/=. by apply val_inj.
        rewrite Hofnat in Hge0.
        move: (Pos2Z.neg_is_neg p)=> Hneg ; omega.
Qed.

Definition toZ_inj n := can_inj (@toZK n).

Lemma toZ_eq n : forall (x y : BITS n.+1), (x == y) = (toZ x == toZ y).
Proof.
  induction n.
  - case/tupleP => [x1 bs1]; case/tupleP => [x2 bs2].
    rewrite !tupleE.
    case E: (toZ (cons_tuple x1 bs1) == toZ (cons_tuple x2 bs2)).
    rewrite (toZ_inj (eqP E)). by rewrite eq_refl.
    apply (contraFF (b:=false)) => // => H.
    rewrite (eqP H) (eq_refl) in E. done.
  - case/tupleP => [x1 bs1]; case/tupleP => [x2 bs2].
    case E: (toZ [tuple of x1 :: bs1] == toZ [tuple of x2 :: bs2]).
    rewrite (toZ_inj (eqP E)). by rewrite eq_refl.
    apply (contraFF (b:=false)) => // => H.
    rewrite (eqP H) (eq_refl) in E. done.
Qed.

Corollary toZ_neq n (x y : BITS n.+1): (x != y) = (toZ x != toZ y).
Proof. by rewrite toZ_eq. Qed.
*)
