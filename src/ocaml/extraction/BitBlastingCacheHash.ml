open BBCommon
open BBConj
open BBConst
open BBDisj
open BBIte
open BBLneg
open BBVar
open BitBlastingCCacheDef
open BitBlastingInit
open CNF
open CacheHash
open QFBVHash
open Seqs
open Var
open Seq

(** val bit_blast_exp_hcache :
    TypEnv.SSATE.env -> vm -> cache -> generator -> hexp ->
    (((vm * cache) * generator) * cnf list) * word **)

let rec bit_blast_exp_hcache e m c g e0 =
  let bit_blast_exp_nocet = fun e1 m0 c0 g0 e2 ->
    let Coq_epair (h, _) = e2 in
    (match h with
     | HEvar v ->
       (match find_het (Obj.magic e2) c0 with
        | Some p -> let (cs, ls) = p in ((((m0, c0), g0), cs), ls)
        | None ->
          (match SSAVM.find v m0 with
           | Some rs ->
             ((((m0, (add_het (Obj.magic e2) [] rs c0)), g0), []), rs)
           | None ->
             let (p, rs) = bit_blast_var e1 g0 v in
             let (g', cs) = p in
             (((((SSAVM.add v rs m0),
             (add_het (Obj.magic e2) (cs :: []) rs c0)), g'), (cs :: [])), rs)))
     | HEconst bs ->
       (match find_het (Obj.magic e2) c0 with
        | Some p -> let (cs, ls) = p in ((((m0, c0), g0), cs), ls)
        | None ->
          let (p, rs) = bit_blast_const g0 bs in
          let (g', cs) = p in
          ((((m0, (add_het (Obj.magic e2) (cs :: []) rs c0)), g'),
          (cs :: [])), rs))
     | HEunop (op, e3) ->
       let (p, ls1) = bit_blast_exp_hcache e1 m0 c0 g0 e3 in
       let (p0, cs1) = p in
       let (p1, g1) = p0 in
       let (m1, c1) = p1 in
       (match find_het (Obj.magic e2) c1 with
        | Some p2 ->
          let (csop, lsop) = p2 in ((((m1, c1), g1), (catrev cs1 csop)), lsop)
        | None ->
          let (p2, lsop) = bit_blast_eunop op g1 ls1 in
          let (gop, csop) = p2 in
          ((((m1, (add_het (Obj.magic e2) (csop :: []) lsop c1)), gop),
          (catrev cs1 (csop :: []))), lsop))
     | HEbinop (op, e3, e4) ->
       let (p, ls1) = bit_blast_exp_hcache e1 m0 c0 g0 e3 in
       let (p0, cs1) = p in
       let (p1, g1) = p0 in
       let (m1, c1) = p1 in
       let (p2, ls2) = bit_blast_exp_hcache e1 m1 c1 g1 e4 in
       let (p3, cs2) = p2 in
       let (p4, g2) = p3 in
       let (m2, c2) = p4 in
       (match find_het (Obj.magic e2) c2 with
        | Some p5 ->
          let (csop, lsop) = p5 in
          ((((m2, c2), g2), (catrev cs1 (catrev cs2 csop))), lsop)
        | None ->
          let (p5, lsop) = bit_blast_ebinop op g2 ls1 ls2 in
          let (gop, csop) = p5 in
          ((((m2, (add_het (Obj.magic e2) (csop :: []) lsop c2)), gop),
          (catrev cs1 (catrev cs2 (csop :: [])))), lsop))
     | HEite (b, e3, e4) ->
       let (p, lb) = bit_blast_bexp_hcache e1 m0 c0 g0 b in
       let (p0, csb) = p in
       let (p1, gb) = p0 in
       let (mb, cb) = p1 in
       let (p2, ls1) = bit_blast_exp_hcache e1 mb cb gb e3 in
       let (p3, cs1) = p2 in
       let (p4, g1) = p3 in
       let (m1, c1) = p4 in
       let (p5, ls2) = bit_blast_exp_hcache e1 m1 c1 g1 e4 in
       let (p6, cs2) = p5 in
       let (p7, g2) = p6 in
       let (m2, c2) = p7 in
       (match find_het (Obj.magic e2) c2 with
        | Some p8 ->
          let (csop, lsop) = p8 in
          ((((m2, c2), g2), (catrev csb (catrev cs1 (catrev cs2 csop)))),
          lsop)
        | None ->
          let (p8, lsop) = bit_blast_ite g2 lb ls1 ls2 in
          let (gop, csop) = p8 in
          ((((m2, (add_het (Obj.magic e2) (csop :: []) lsop c2)), gop),
          (catrev csb (catrev cs1 (catrev cs2 (csop :: []))))), lsop)))
  in
  (match find_cet (Obj.magic e0) c with
   | Some ls -> ((((m, c), g), []), ls)
   | None ->
     let (p, lrs) = bit_blast_exp_nocet e m c g e0 in
     let (p0, cs) = p in
     let (p1, g') = p0 in
     let (m', c') = p1 in
     ((((m', (add_cet (Obj.magic e0) lrs c')), g'), cs), lrs))

(** val bit_blast_bexp_hcache :
    TypEnv.SSATE.env -> vm -> cache -> generator -> hbexp ->
    (((vm * cache) * generator) * cnf list) * literal **)

and bit_blast_bexp_hcache e m c g e0 =
  let bit_blast_bexp_nocbt = fun e1 m0 c0 g0 e2 ->
    let Coq_bpair (h, _) = e2 in
    (match h with
     | HBfalse ->
       (match find_hbt (Obj.magic e2) c0 with
        | Some p -> let (cs, l) = p in ((((m0, c0), g0), cs), l)
        | None ->
          ((((m0, (add_hbt (Obj.magic e2) [] lit_ff c0)), g0), []), lit_ff))
     | HBtrue ->
       (match find_hbt (Obj.magic e2) c0 with
        | Some p -> let (cs, l) = p in ((((m0, c0), g0), cs), l)
        | None ->
          ((((m0, (add_hbt (Obj.magic e2) [] lit_tt c0)), g0), []), lit_tt))
     | HBbinop (op, e3, e4) ->
       let (p, ls1) = bit_blast_exp_hcache e1 m0 c0 g0 e3 in
       let (p0, cs1) = p in
       let (p1, g1) = p0 in
       let (m1, c1) = p1 in
       let (p2, ls2) = bit_blast_exp_hcache e1 m1 c1 g1 e4 in
       let (p3, cs2) = p2 in
       let (p4, g2) = p3 in
       let (m2, c2) = p4 in
       (match find_hbt (Obj.magic e2) c2 with
        | Some p5 ->
          let (csop, lop) = p5 in
          ((((m2, c2), g2), (catrev cs1 (catrev cs2 csop))), lop)
        | None ->
          let (p5, lop) = bit_blast_bbinop op g2 ls1 ls2 in
          let (gop, csop) = p5 in
          ((((m2, (add_hbt (Obj.magic e2) (csop :: []) lop c2)), gop),
          (catrev cs1 (catrev cs2 (csop :: [])))), lop))
     | HBlneg e3 ->
       let (p, l1) = bit_blast_bexp_hcache e1 m0 c0 g0 e3 in
       let (p0, cs1) = p in
       let (p1, g1) = p0 in
       let (m1, c1) = p1 in
       (match find_hbt (Obj.magic e2) c1 with
        | Some p2 ->
          let (csop, lop) = p2 in ((((m1, c1), g1), (catrev cs1 csop)), lop)
        | None ->
          let (p2, lop) = bit_blast_lneg g1 l1 in
          let (gop, csop) = p2 in
          ((((m1, (add_hbt (Obj.magic e2) (csop :: []) lop c1)), gop),
          (catrev cs1 (csop :: []))), lop))
     | HBconj (e3, e4) ->
       let (p, l1) = bit_blast_bexp_hcache e1 m0 c0 g0 e3 in
       let (p0, cs1) = p in
       let (p1, g1) = p0 in
       let (m1, c1) = p1 in
       let (p2, l2) = bit_blast_bexp_hcache e1 m1 c1 g1 e4 in
       let (p3, cs2) = p2 in
       let (p4, g2) = p3 in
       let (m2, c2) = p4 in
       (match find_hbt (Obj.magic e2) c2 with
        | Some p5 ->
          let (csop, lop) = p5 in
          ((((m2, c2), g2), (catrev cs1 (catrev cs2 csop))), lop)
        | None ->
          let (p5, lop) = bit_blast_conj g2 l1 l2 in
          let (gop, csop) = p5 in
          ((((m2, (add_hbt (Obj.magic e2) (csop :: []) lop c2)), gop),
          (catrev cs1 (catrev cs2 (csop :: [])))), lop))
     | HBdisj (e3, e4) ->
       let (p, l1) = bit_blast_bexp_hcache e1 m0 c0 g0 e3 in
       let (p0, cs1) = p in
       let (p1, g1) = p0 in
       let (m1, c1) = p1 in
       let (p2, l2) = bit_blast_bexp_hcache e1 m1 c1 g1 e4 in
       let (p3, cs2) = p2 in
       let (p4, g2) = p3 in
       let (m2, c2) = p4 in
       (match find_hbt (Obj.magic e2) c2 with
        | Some p5 ->
          let (csop, lop) = p5 in
          ((((m2, c2), g2), (catrev cs1 (catrev cs2 csop))), lop)
        | None ->
          let (p5, lop) = bit_blast_disj g2 l1 l2 in
          let (gop, csop) = p5 in
          ((((m2, (add_hbt (Obj.magic e2) (csop :: []) lop c2)), gop),
          (catrev cs1 (catrev cs2 (csop :: [])))), lop)))
  in
  (match find_cbt (Obj.magic e0) c with
   | Some l -> ((((m, c), g), []), l)
   | None ->
     let (p, lr) = bit_blast_bexp_nocbt e m c g e0 in
     let (p0, cs) = p in
     let (p1, g') = p0 in
     let (m', c') = p1 in
     ((((m', (add_cbt (Obj.magic e0) lr c')), g'), cs), lr))

(** val init_hcache : cache **)

let init_hcache =
  empty

(** val bit_blast_bexp_hcache_tflatten :
    TypEnv.SSATE.env -> vm -> cache -> generator -> hbexp ->
    (((vm * cache) * generator) * clause list) * literal **)

let bit_blast_bexp_hcache_tflatten e m c g e0 =
  let (p, lr') = bit_blast_bexp_hcache e m c g e0 in
  let (p0, css') = p in ((p0, (tflatten css')), lr')

(** val bit_blast_hbexps_hcache_conjs_rec :
    TypEnv.SSATE.env -> vm -> cache -> generator -> cnf list -> cnf -> hbexp
    list -> (((vm * cache) * generator) * cnf list) * cnf **)

let rec bit_blast_hbexps_hcache_conjs_rec e m c g rcs rlrs = function
| [] -> ((((m, c), g), rcs), rlrs)
| hd :: tl ->
  let (p, lr) = bit_blast_bexp_hcache e m c g hd in
  let (p0, cs) = p in
  let (p1, g') = p0 in
  let (m', c') = p1 in
  bit_blast_hbexps_hcache_conjs_rec e m' c' g' (catrev cs rcs)
    ((lr :: []) :: rlrs) tl

(** val bit_blast_hbexps_hcache_conjs :
    TypEnv.SSATE.env -> vm -> cache -> generator -> hbexp list ->
    (((vm * cache) * generator) * cnf list) * cnf **)

let bit_blast_hbexps_hcache_conjs e m c g es =
  bit_blast_hbexps_hcache_conjs_rec e m c g [] [] es

(** val bit_blast_bexps_hcache_conjs :
    TypEnv.SSATE.env -> QFBV.QFBV.bexp list -> cnf **)

let bit_blast_bexps_hcache_conjs tE es =
  let (p, lrs) =
    bit_blast_hbexps_hcache_conjs tE init_vm init_hcache init_gen
      (mapr hash_bexp es)
  in
  let (_, cs) = p in add_prelude (tflatten (lrs :: cs))
