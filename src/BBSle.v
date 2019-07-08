
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From BitBlasting Require Import QFBVSimple CNF BBCommon BBEq BBDisj BBSlt.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_sle ===== *)

(*Parameter bit_blast_sle : forall w : nat, generator -> w.+1.-tuple literal -> w.+1.-tuple literal -> generator * cnf * literal.
 *)
Definition bit_blast_sle (w: nat) g (ls1 ls2: w.+1.-tuple literal) : generator * cnf * literal :=
  let '(g_eq, cs_eq, r_eq) := bit_blast_eq g ls1 ls2 in
  let '(g_slt, cs_slt, r_slt) := bit_blast_slt g_eq ls1 ls2 in
  let '(g_disj, cs_disj, r_disj) := bit_blast_disj g_slt r_eq r_slt in
  (g_disj, cs_eq++cs_slt++cs_disj, r_disj).

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

Lemma bit_blast_sle_correct_iff :
  forall w g (bs1 bs2 : BITS w.+1) E g' ls1 ls2 cs lr,
    bit_blast_sle g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    interp_lit E lr <-> (toZ bs1 <= toZ bs2)%Z.
Proof.
  move => w g ibs1 ibs2 E og ils1 ils2 cs olr.
  rewrite /bit_blast_sle.
  case Heq: (bit_blast_eq g ils1 ils2) => [[g_eq cs_eq] r_eq].
  case Hslt : (bit_blast_slt g_eq ils1 ils2) => [[g_slt cs_slt] r_slt].
  case Hdisj : (bit_blast_disj g_slt r_eq r_slt) => [[g_disj cs_disj] r_disj].
  case => _ <- <- Henc1 Henc2.
  rewrite 2!add_prelude_append.
  move/andP => [Hcnf_eq Hcnf].
  move/andP : Hcnf => [Hcnf_slt Hcnf_disj].
  move : (bit_blast_eq_correct Heq Henc1 Henc2 Hcnf_eq) => Hreq.
  move : (bit_blast_slt_correct_iff Hslt Henc1 Henc2 Hcnf_slt) => Hrslt.
  split.
  - move => Hrdisj1.
    (*apply /Z.lt_le_incl.*)
    assert (enc_bit E r_slt (Z.ltb (toZ ibs1) (toZ ibs2))) as Henc_slt.

      by (rewrite /enc_bit; apply iffBool; rewrite Hrslt -Z.ltb_lt; done).
    move : (bit_blast_disj_correct Hdisj Hreq Henc_slt Hcnf_disj) => Hrdisj.
    rewrite /enc_bit in Hreq.
    move/eqP: Hreq => Hreq. rewrite /enc_bit/=Hrdisj1 -Hreq in Hrdisj.
    case Hr: (interp_lit E r_eq); rewrite Hr /=in Hreq;
      symmetry in Hreq; move/eqP : Hreq => Hreq.
    + rewrite Hreq; omega.
    + rewrite Hr orFb in Hrdisj.
      move/eqP: Hrdisj => Hrdisj; symmetry in Hrdisj.
      apply Z.lt_le_incl; by apply Z.ltb_lt.
  - move => Hle.
    assert (enc_bit E r_slt (Z.ltb (toZ ibs1) (toZ ibs2))) as Henc_slt
        by (rewrite /enc_bit; apply iffBool; rewrite Hrslt -Z.ltb_lt; done).
    move : (bit_blast_disj_correct Hdisj Hreq Henc_slt Hcnf_disj) => Hrdisj.
    rewrite /enc_bit in Hreq; move/eqP: Hreq => Hreq.
    rewrite /enc_bit/= in Hrdisj; move/eqP: Hrdisj => Hrdisj.
    rewrite Hrdisj; apply/orP.
    case Hr: (interp_lit E r_eq); rewrite Hr /=in Hreq;
      symmetry in Hreq; move/eqP : Hreq => Hreq.
    left; by rewrite Hreq.
    right. apply Z.ltb_lt.
    apply Z.Private_Tac.le_neq_lt in Hle; try exact.
    move/eqP : Hreq => Hreq.
    apply/eqP. rewrite -toZ_neq. exact.
Qed.

Lemma bit_blast_sle_correct :
  forall w g (bs1 bs2 : BITS (w.+1)) E g' ls1 ls2 cs lr,
    bit_blast_sle g ls1 ls2 = (g', cs, lr) ->
    enc_bits E ls1 bs1 ->
    enc_bits E ls2 bs2 ->
    interp_cnf E (add_prelude cs) ->
    enc_bit E lr (Z.leb (toZ bs1) (toZ bs2)).
Proof.
  move=> w g bs1 bs2 E g' ls1 ls2 cs lr Hslt Hl1b1 Hl2b2 HiEcs.
  move : (bit_blast_sle_correct_iff Hslt Hl1b1 Hl2b2 HiEcs) => H.
  rewrite /enc_bit. apply iffBool. rewrite H -Z.leb_le.
  done.
Qed.

Definition mk_env_sle w (E : env) g (ls1 ls2 : w.+1.-tuple literal) : env * generator * cnf * literal :=
  let '(E_eq, g_eq, cs_eq, r_eq) := mk_env_eq E g ls1 ls2 in
  let '(E_slt, g_slt, cs_slt, r_slt) := mk_env_slt E_eq g_eq ls1 ls2 in
  let '(E_disj, g_disj, cs_disj, r_disj) := mk_env_disj E_slt g_slt r_eq r_slt in
  (E_disj, g_disj, cs_eq++cs_slt++cs_disj, r_disj).

Lemma mk_env_sle_is_bit_blast_sle :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_sle E g ls1 ls2 = (E', g', cs, lr) ->
    bit_blast_sle g ls1 ls2 = (g', cs, lr).
Proof.
  move=> w E g ls1 ls2 E' g' cs lr.
  rewrite /mk_env_sle /bit_blast_sle. 
  case Hmkeq : (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] r_eq].
  case Hmkslt : (mk_env_slt E_eq g_eq ls1 ls2) => [[[E_slt g_slt] cs_slt] r_slt].
  case Hmkdisj : (mk_env_disj E_slt g_slt r_eq r_slt) => [[[E_disj g_disj] cs_disj] r_disj].
  rewrite (mk_env_eq_is_bit_blast_eq Hmkeq) {Hmkeq}.
  rewrite (mk_env_slt_is_bit_blast_slt Hmkslt) {Hmkslt}.
  rewrite (mk_env_disj_is_bit_blast_disj Hmkdisj) {Hmkdisj}.
  by case=> _ <- <- <-.
Qed.

Lemma mk_env_sle_newer_gen :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_sle E g ls1 ls2 = (E', g', cs, lr) ->
    (g <=? g')%positive.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_sle.
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

Lemma mk_env_sle_newer_res :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_sle E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g' lr.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_sle.
  case Hmkeq : (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] r_eq].
  case Hmkslt : (mk_env_slt E_eq g_eq ls1 ls2) => [[[E_slt g_slt] cs_slt] r_slt].
  case Hmkdisj : (mk_env_disj E_slt g_slt r_eq r_slt) => [[[E_disj g_disj] cs_disj] r_disj].
  case=> _ <- _ <-.
  exact: (mk_env_disj_newer_res Hmkdisj).
Qed.

Lemma mk_env_sle_newer_cnf :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_sle E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    newer_than_cnf g' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_sle.
  case Hmkeq : (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] r_eq].
  case Hmkslt : (mk_env_slt E_eq g_eq ls1 ls2) => [[[E_slt g_slt] cs_slt] r_slt].
  case Hmkdisj : (mk_env_disj E_slt g_slt r_eq r_slt) => [[[E_disj g_disj] cs_disj] r_disj].
  case=> _ <- <- _ Hgt Hgl1 Hgl2. rewrite /= !newer_than_cnf_append.
  (* newer_than_cnf g_disj cs_eq *)
  move : (mk_env_eq_newer_cnf Hmkeq Hgl1 Hgl2) => Hgece.
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

Lemma mk_env_sle_preserve :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_sle E g ls1 ls2 = (E', g', cs, lr) ->
    env_preserve E E' g.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_sle.
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

Lemma mk_env_sle_sat :
  forall w E g (ls1 ls2 : w.+1.-tuple literal) E' g' cs lr,
    mk_env_sle E g ls1 ls2 = (E', g', cs, lr) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls1 -> newer_than_lits g ls2 ->
    interp_cnf E' cs.
Proof.
  move=> w E g ls1 ls2 E' g' cs lr. rewrite /mk_env_sle.
  case Hmkeq : (mk_env_eq E g ls1 ls2) => [[[E_eq g_eq] cs_eq] r_eq].
  case Hmkslt : (mk_env_slt E_eq g_eq ls1 ls2) => [[[E_slt g_slt] cs_slt] r_slt].
  case Hmkdisj : (mk_env_disj E_slt g_slt r_eq r_slt) => [[[E_disj g_disj] cs_disj] r_disj].
  case=> <- _ <- _ Hgt Hgl1 Hgl2.
  rewrite !interp_cnf_append.
  (* interp_cnf E_disj cs_eq *)
  move : (mk_env_eq_sat Hmkeq Hgl1 Hgl2) => HiEece.
  move : (mk_env_slt_preserve Hmkslt) => HpEeEsge.
  move : (mk_env_disj_preserve Hmkdisj) => HpEsEdgs.
  move : (mk_env_slt_newer_gen Hmkslt) => Hgegs.
  move : (env_preserve_le HpEsEdgs Hgegs) => HpEsEdge.
  move : (env_preserve_trans HpEeEsge HpEsEdge) => HpEeEdge.
  move : (mk_env_eq_newer_cnf Hmkeq Hgl1 Hgl2) => Hgece.
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
