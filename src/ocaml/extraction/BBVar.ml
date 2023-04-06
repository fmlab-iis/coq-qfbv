open BBCommon
open CNF
open EqVar

(** val bit_blast_var' : generator -> int -> generator * word **)

let rec bit_blast_var' g w =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (g, []))
    (fun n ->
    let (g', hd) = gen g in
    let (g'', tl) = bit_blast_var' g' n in (g'', (hd :: tl)))
    w

(** val bit_blast_var :
    TypEnv.SSATE.env -> generator -> ssavar -> (generator * cnf) * word **)

let bit_blast_var tenv g v =
  let (g', vs) = bit_blast_var' g (TypEnv.SSATE.vsize v tenv) in
  ((g', []), vs)
