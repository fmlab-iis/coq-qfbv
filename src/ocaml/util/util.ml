
(** General purpose functions *)

let (|>) f g x = g(f(x))

let id x = x

(* combinations n xs returns all subsets of xs with size n *)
let rec combinations n xs =
  if n <= 0 then [[]]
  else match xs with
       | [] -> []
       | y::ys -> (List.map (fun l -> y::l) (combinations (n-1) ys)) @ (combinations n ys)
