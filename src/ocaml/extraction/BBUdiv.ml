open BBAnd
open BBCommon
open BBEq
open BBIte
open BBOr
open BBSub
open BBUge
open CNF
open Eqtype
open Seq

(** val bit_blast_udiv_rec :
    generator -> literal list -> literal list -> word -> word ->
    ((generator * cnf) * word) * word **)

let rec bit_blast_udiv_rec g ls1 ls2 qs rs =
  match ls1 with
  | [] -> (((g, []), qs), rs)
  | ls1_hd :: ls1_tl ->
    let di = dropmsl (joinlsl ls1_hd rs) in
    let (p, lrs_uge) = bit_blast_uge g di ls2 in
    let (g_uge, cs_uge) = p in
    let qi = dropmsl (joinlsl lrs_uge qs) in
    if eq_op lit_eqType (Obj.magic lrs_uge) (Obj.magic lit_tt)
    then let (p0, lrs_sub) = bit_blast_sub g_uge di ls2 in
         let (g_sub, cs_sub) = p0 in
         let (p1, lrs_tl) = bit_blast_udiv_rec g_sub ls1_tl ls2 qi lrs_sub in
         let (p2, lqs_tl) = p1 in
         let (g_tl, cs_tl) = p2 in
         (((g_tl, (catrev (catrev cs_tl cs_sub) cs_uge)), lqs_tl), lrs_tl)
    else if eq_op lit_eqType (Obj.magic lrs_uge) (Obj.magic lit_ff)
         then let (p0, lrs_tl) = bit_blast_udiv_rec g_uge ls1_tl ls2 qi di in
              let (p1, lqs_tl) = p0 in
              let (g_tl, cs_tl) = p1 in
              (((g_tl, (catrev cs_tl cs_uge)), lqs_tl), lrs_tl)
         else let (p0, lrs_and) =
                bit_blast_and g_uge (nseq (size ls2) lrs_uge) ls2
              in
              let (g_and, cs_and) = p0 in
              let (p1, lrs_sub2) = bit_blast_sub g_and di lrs_and in
              let (g_sub2, cs_sub2) = p1 in
              let (p2, lqs_tl) =
                bit_blast_udiv_rec g_sub2 ls1_tl ls2 qi lrs_sub2
              in
              let (p3, lrs_tl) = p2 in
              let (g_tl, cs_tl) = p3 in
              (((g_tl,
              (catrev (catrev (catrev cs_tl cs_sub2) cs_and) cs_uge)),
              lrs_tl), lqs_tl)

(** val bit_blast_udiv :
    generator -> literal list -> literal list -> ((generator * cnf) * literal
    list) * literal list **)

let bit_blast_udiv g ls1' ls2 =
  let ls1 = rev ls1' in
  let (p, lrs_eq) = bit_blast_eq g ls2 (nseq (size ls2) lit_ff) in
  let (g_eq, cs_eq) = p in
  if eq_op lit_eqType (Obj.magic lrs_eq) (Obj.magic lit_tt)
  then (((g_eq, cs_eq), (nseq (size ls2) lit_tt)), ls1')
  else if eq_op lit_eqType (Obj.magic lrs_eq) (Obj.magic lit_ff)
       then let (p0, lrs_udivr) =
              bit_blast_udiv_rec g_eq ls1 ls2 (nseq (size ls1) lit_ff)
                (nseq (size ls1) lit_ff)
            in
            let (p1, lqs_udivr) = p0 in
            let (g_udivr, cs_udivr) = p1 in
            (((g_udivr, (catrev cs_udivr cs_eq)), lqs_udivr), lrs_udivr)
       else let (p0, lrs_udivr) =
              bit_blast_udiv_rec g_eq ls1 ls2 (nseq (size ls1) lit_ff)
                (nseq (size ls1) lit_ff)
            in
            let (p1, lqs_udivr) = p0 in
            let (g_udivr, cs_udivr) = p1 in
            let (p2, lrs_or) =
              bit_blast_or g_udivr (nseq (size lqs_udivr) lrs_eq) lqs_udivr
            in
            let (g_or, cs_or) = p2 in
            let (p3, lrs_ite) = bit_blast_ite g_or lrs_eq ls1' lrs_udivr in
            let (g_ite, cs_ite) = p3 in
            (((g_ite,
            (catrev (catrev (catrev cs_ite cs_or) cs_udivr) cs_eq)), lrs_or),
            lrs_ite)

(** val bit_blast_udiv' :
    generator -> literal list -> literal list -> (generator * cnf) * literal
    list **)

let bit_blast_udiv' g ls1 ls2 =
  let (p, _) = bit_blast_udiv g ls1 ls2 in p

(** val bit_blast_umod :
    generator -> literal list -> literal list -> (generator * cnf) * literal
    list **)

let bit_blast_umod g ls1 ls2 =
  let (p, rlrs) = bit_blast_udiv g ls1 ls2 in let (p0, _) = p in (p0, rlrs)
