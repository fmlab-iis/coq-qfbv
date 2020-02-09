From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport 
     AdhereConform.
From BBCache Require Import Cache BitBlastingCacheDef.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* = bit_blast_exp_cache_adhere and bit_blast_bexp_cache_adhere = *)

Lemma size_bit_blast_var' g n g' vs' :
  bit_blast_var' g n = (g', vs') -> size vs' = n .
Proof .
  elim : n g g' vs' => [ |n IH] g g' vs' .
  - case => _ <- // .
  - rewrite /bit_blast_var' /= -/bit_blast_var' .
    dcase (bit_blast_var' (g+1)%positive n) => [[g'' tl] Hbbr] .
    case => _ <- /= .
    rewrite (IH _ _ _ Hbbr) // .
Qed .


Lemma bit_blast_exp_cache_adhere :
  forall e te m m' ca ca' g g' cs' lrs',
    AdhereConform.adhere m te ->
    bit_blast_exp_cache te m ca g e = (m', ca', g', cs', lrs') ->
    AdhereConform.adhere m' te
with
bit_blast_bexp_cache_adhere :
  forall e te m m' ca ca' g g' cs' lr',
    AdhereConform.adhere m te ->
    bit_blast_bexp_cache te m ca g e = (m', ca', g', cs', lr') ->
    AdhereConform.adhere m' te .
Proof .
  (* bit_blast_exp_cache_adhere *)
  set IHe := bit_blast_exp_cache_adhere.
  set IHb := bit_blast_bexp_cache_adhere.
  move=> e te m m' ca ca' g g' cs' lrs' Hadm.
  case Hfcet: (find_cet e ca) => [ls|]. 
  - rewrite bit_blast_exp_cache_equation Hfcet /=.
    by case=> <- _ _ _ _. 
  - case Hfhet: (find_het e ca) => [[csh lsh]|].
    + rewrite bit_blast_exp_cache_equation Hfcet Hfhet /=. 
      by case=> <- _ _ _ _. 
    + move: Hfcet Hfhet. 
      case: e => [v | bs | unop e | binop e1 e2 | b e1 e2]; 
                   move=> Hfcet Hfhet; rewrite /= Hfcet Hfhet {Hfcet Hfhet}.
      * case : (SSAVM.find v m) .
        -- move => a; case => <- _ _ _ // .
        -- rewrite /bit_blast_var .
           dcase (bit_blast_var' g (SSATE.vsize v te)) => [[g'0 vs] Hbbr ] .
           case => <- _ _ _ _ .
           rewrite /adhere => u .
           case Heq : (u == v) .
           ++ rewrite (eqP Heq) => _ .
              have Hfind : (SSAVM.M.find v (SSAVM.M.add v vs m) = Some vs) .
              { apply : SSAVM.Lemmas.find_add_eq; done . }
              exists vs .
              rewrite Hfind (size_bit_blast_var' Hbbr) // .
           ++ have Hneq : ~(SSAVM.E.eq u v) .
              { rewrite /SSAVM.E.eq Heq // . }
              rewrite (SSAVM.Lemmas.mem_add_neq Hneq) => Hmem .
              rewrite (SSAVM.Lemmas.find_add_neq Hneq) .
              apply : (Hadm u Hmem) .
      * case => <- _ _ _ _ // .
      * elim: unop => /= [ | | i j | n | n | n | n ];
                        dcase (bit_blast_exp_cache te m ca g e) 
                          => [[[[[m1 ca1] g1] cs1] ls1] Hbbe] ;
                        move : (IHe _ _ _ _ _ _ _ _ _ _ Hadm Hbbe) => Hadm1.
        -- dcase (bit_blast_not g1 ls1) => [[[gr csr] lsr] _]; by case => <- _ _ _ _. 
        -- dcase (bit_blast_neg g1 ls1) => [[[gr csr] lsr] _]; by case => <- _ _ _ _.
        -- by case => <- _ _ _ _. 
        -- by case => <- _ _ _ _.
        -- by case => <- _ _ _ _.
        -- by case => <- _ _ _ _.
        -- by case => <- _ _ _ _.
      * elim: binop;
          dcase (bit_blast_exp_cache te m ca g e1) 
            => [[[[[m1 ca1] g1] cs1] ls1] Hbbe1];
          dcase (bit_blast_exp_cache te m1 ca1 g1 e2) 
            => [[[[[m2 ca2] g2] cs2] ls2] Hbbe2];
          move : (IHe _ _ _ _ _ _ _ _ _ _ Hadm Hbbe1) => {Hadm Hbbe1} Hadm1;
          move : (IHe _ _ _ _ _ _ _ _ _ _ Hadm1 Hbbe2) => {Hadm1 Hbbe2} Hadm2 .
        -- dcase (bit_blast_and g2 ls1 ls2) => [[[gr csr] lsr] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_or g2 ls1 ls2) => [[[gr csr] lsr] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_xor g2 ls1 ls2) => [[[gr csr] lsr] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_add g2 ls1 ls2) => [[[gr csr] lsr] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_sub g2 ls1 ls2) => [[[gr csr] lsr] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_mul g2 ls1 ls2) => [[[gr csr] lsr] _]; by case => <- _ _ _ _.
        -- by case => <- _ _ _ _. 
        -- by case => <- _ _ _ _.
        -- by case => <- _ _ _ _.
        -- dcase (bit_blast_shl g2 ls1 ls2) => [[[gr csr] lsr] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_lshr g2 ls1 ls2) => [[[gr csr] lsr] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_ashr g2 ls1 ls2) => [[[gr csr] lsr] _]; by case => <- _ _ _ _.
        -- by case => <- _ _ _ _.
      * (* move => b e0 IH0 e1 IH1 te m m' g g' cs' lr' Hadm . *)
        dcase (bit_blast_bexp_cache te m ca g b) => [[[[[mc cac] gc] csc] lc] Hbbc] .
        move : (IHb b _ _ _ _ _ _ _ _ _ Hadm Hbbc) => {Hadm Hbbc} Hadmc .
        dcase (bit_blast_exp_cache te mc cac gc e1) => [[[[[m1 ca1] g1] cs1] ls1] Hbbe1] .
        move : (IHe _ _ _ _ _ _ _ _ _ _ Hadmc Hbbe1) => {Hadmc Hbbe1} Hadm1 .
        dcase (bit_blast_exp_cache te m1 ca1 g1 e2) => [[[[[m2 ca2] g2] cs2] ls2] Hbbe2] .
        move : (IHe _ _ _ _ _ _ _ _ _ _ Hadm1 Hbbe2) => {Hadm1 Hbbe2} Hadm2 .
        dcase (bit_blast_ite g2 lc ls1 ls2) => [[[gr csr] lsr] _ ] .
        by case => <- _ _ _ _.
  (* bit_blast_bexp_cache_adhere *)
  set IHe := bit_blast_exp_cache_adhere.
  set IHb := bit_blast_bexp_cache_adhere.
  move=> e te m m' ca ca' g g' cs' lr' Hadm.
  case Hfcbt: (find_cbt e ca) => [l|]. 
  - rewrite bit_blast_bexp_cache_equation Hfcbt /=.
    by case=> <- _ _ _ _. 
  - case Hfhbt: (find_hbt e ca) => [[csh lh]|].
    + rewrite bit_blast_bexp_cache_equation Hfcbt Hfhbt /=. 
      by case=> <- _ _ _ _. 
    + move: Hfcbt Hfhbt. 
      case: e => [ | | binop e1 e2 | e | e1 e2 | e1 e2]; 
                   move=> Hfcbt Hfhbt; rewrite /= Hfcbt Hfhbt {Hfcbt Hfhbt}.
      * by case => <- _ _ _ _.
      * by case => <- _ _ _ _.
      * elim: binop;
        dcase (bit_blast_exp_cache te m ca g e1) => [[[[[m1 ca1] g1] cs1] ls1] Hbbe1];
        move : (IHe _ _ _ _ _ _ _ _ _ _ Hadm Hbbe1) => {Hadm Hbbe1} Hadm1;
        dcase (bit_blast_exp_cache te m1 ca1 g1 e2) => [[[[[m2 ca2] g2] cs2] ls2] Hbbe2];
        move : (IHe _ _ _ _ _ _ _ _ _ _ Hadm1 Hbbe2) => {Hadm1 Hbbe2} Hadm2 .
        -- dcase (bit_blast_eq g2 ls1 ls2) => [[[g'0 cs] r] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_ult g2 ls1 ls2) => [[[g'0 cs] r] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_ule g2 ls1 ls2) => [[[g'0 cs] r] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_ugt g2 ls1 ls2) => [[[g'0 cs] r] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_uge g2 ls1 ls2) => [[[g'0 cs] r] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_slt g2 ls1 ls2) => [[[g'0 cs] r] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_sle g2 ls1 ls2) => [[[g'0 cs] r] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_sgt g2 ls1 ls2) => [[[g'0 cs] r] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_sge g2 ls1 ls2) => [[[g'0 cs] r] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_uaddo g2 ls1 ls2) => [[[g'0 cs] r] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_usubo g2 ls1 ls2) => [[[g'0 cs] r] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_umulo g2 ls1 ls2) => [[[g'0 cs] r] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_saddo g2 ls1 ls2) => [[[g'0 cs] r] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_ssubo g2 ls1 ls2) => [[[g'0 cs] r] _]; by case => <- _ _ _ _.
        -- dcase (bit_blast_smulo g2 ls1 ls2) => [[[g'0 cs] r] _]; by case => <- _ _ _ _.
      * dcase (bit_blast_bexp_cache te m ca g e) => [[[[[m1 ca1] g1] cs1] l1] Hbbe] .
        case => <- _ _ _ _ .
        apply : (IHb e _ _ _ _ _ _ _ _ _ Hadm Hbbe) .
      * dcase (bit_blast_bexp_cache te m ca g e1) => [[[[[m1 ca1] g1] cs1] l1] Hbbe1] .
        move : (IHb _ _ _ _ _ _ _ _ _ _ Hadm Hbbe1) => {Hadm Hbbe1} Hadm1 .
        dcase (bit_blast_bexp_cache te m1 ca1 g1 e2) => [[[[[m2 ca2] g2] cs2] l2] Hbbe2] .
        move : (IHb _ _ _ _ _ _ _ _ _ _ Hadm1 Hbbe2) => {Hadm1 Hbbe2} Hadm2 .
        by case => <- _ _ _ _ .
      * dcase (bit_blast_bexp_cache te m ca g e1) => [[[[[m1 ca1] g1] cs1] l1] Hbbe1] .
        move : (IHb _ _ _ _ _ _ _ _ _ _ Hadm Hbbe1) => {Hadm Hbbe1} Hadm1 .
        dcase (bit_blast_bexp_cache te m1 ca1 g1 e2) => [[[[[m2 ca2] g2] cs2] l2] Hbbe2] .
        move : (IHb _ _ _ _ _ _ _ _ _ _ Hadm1 Hbbe2) => {Hadm1 Hbbe2} Hadm2 .
        by case => <- _ _ _ _ .
Qed.
