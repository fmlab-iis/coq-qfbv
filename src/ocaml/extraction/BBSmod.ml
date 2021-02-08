open BBAdd
open BBAnd
open BBCommon
open BBEq
open BBNot
open BBOr
open BBSdiv
open CNF
open Datatypes
open Eqtype
open Seq

(** val bit_blast_smod :
    generator -> word -> word -> (generator * cnf) * word **)

let bit_blast_smod g ls1 ls2 =
  let ls1_sign = snd (splitmsl ls1) in
  let ls2_sign = snd (splitmsl ls2) in
  let (p, lrs_srem) = bit_blast_srem g ls1 ls2 in
  let (g_srem, cs_srem) = p in
  let (p0, r_eq) = bit_blast_eq g_srem (ls1_sign :: []) (ls2_sign :: []) in
  let (g_eq, cs_eq) = p0 in
  let (p1, r_eq2) = bit_blast_eq g_eq lrs_srem (nseq (size lrs_srem) lit_ff)
  in
  let (g_eq2, cs_eq2) = p1 in
  if (||) (eq_op lit_eqType (Obj.magic r_eq) (Obj.magic lit_tt))
       (eq_op lit_eqType (Obj.magic r_eq2) (Obj.magic lit_tt))
  then ((g_eq2, (catrev cs_srem (catrev cs_eq2 cs_eq))), lrs_srem)
  else if (&&) (eq_op lit_eqType (Obj.magic r_eq) (Obj.magic lit_ff))
            (eq_op lit_eqType (Obj.magic r_eq2) (Obj.magic lit_ff))
       then let (p2, lrs_add) = bit_blast_add g_eq2 lrs_srem ls2 in
            let (g_add, cs_add) = p2 in
            ((g_add, (catrev cs_srem (catrev cs_eq (catrev cs_eq2 cs_add)))),
            lrs_add)
       else let (p2, lrs_or) =
              bit_blast_or g_eq2 (nseq (size ls2) r_eq)
                (nseq (size ls2) r_eq2)
            in
            let (g_or, cs_or) = p2 in
            let (p3, lrs_not) = bit_blast_not g_or lrs_or in
            let (g_not, cs_not) = p3 in
            let (p4, lrs_and2) = bit_blast_and g_not ls2 lrs_not in
            let (g_and2, cs_and2) = p4 in
            let (p5, lrs_add2) = bit_blast_add g_and2 lrs_srem lrs_and2 in
            let (g_add2, cs_add2) = p5 in
            ((g_add2,
            (catrev cs_srem
              (catrev cs_eq
                (catrev cs_eq2
                  (catrev cs_or (catrev cs_not (catrev cs_and2 cs_add2))))))),
            lrs_add2)
