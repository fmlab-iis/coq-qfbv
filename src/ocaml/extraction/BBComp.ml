open BBCommon
open BBEq
open CNF

(** val bit_blast_comp :
    generator -> literal list -> literal list -> (generator * cnf) * word **)

let bit_blast_comp g ls1 ls2 =
  let (p, lr) = bit_blast_eq g ls1 ls2 in (p, (lr :: []))
