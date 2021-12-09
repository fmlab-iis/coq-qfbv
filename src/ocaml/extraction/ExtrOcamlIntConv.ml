open BinNums

(** val int_of_nat : int -> int **)

let int_of_nat =
  let rec loop acc n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> acc)
      (fun n0 -> loop (succ acc) n0)
      n
  in loop 0

(** val int_of_pos : positive -> int **)

let rec int_of_pos = function
| Coq_xI p0 -> succ (2 * (int_of_pos p0))
| Coq_xO p0 -> 2 * (int_of_pos p0)
| Coq_xH -> succ 0

(** val int_of_n : coq_N -> int **)

let int_of_n = function
| N0 -> 0
| Npos p -> int_of_pos p

(** val int_natlike_rec : 'a1 -> ('a1 -> 'a1) -> int -> 'a1 **)

let int_natlike_rec = fun fO fS ->
 let rec loop acc i = if i <= 0 then acc else loop (fS acc) (i-1)
 in loop fO

(** val nat_of_int : int -> int **)

let nat_of_int =
  int_natlike_rec 0 (fun x -> Pervasives.succ x)

(** val int_poslike_rec :
    'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1) -> int -> 'a1 **)

let int_poslike_rec = fun f1 f2x f2x1 ->
 let rec loop i = if i <= 1 then f1 else
  if i land 1 = 0 then f2x (loop (i lsr 1)) else f2x1 (loop (i lsr 1))
 in loop

(** val pos_of_int : int -> positive **)

let pos_of_int =
  int_poslike_rec Coq_xH (fun x -> Coq_xO x) (fun x -> Coq_xI x)

(** val int_zlike_case : 'a1 -> (int -> 'a1) -> (int -> 'a1) -> int -> 'a1 **)

let int_zlike_case = fun f0 fpos fneg i ->
 if i = 0 then f0 else if i>0 then fpos i else fneg (-i)

(** val n_of_int : int -> coq_N **)

let n_of_int =
  int_zlike_case N0 (fun i -> Npos (pos_of_int i)) (fun _ -> N0)
