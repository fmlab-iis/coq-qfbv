
(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

(** val get : int -> char list -> char option **)

let rec get n = function
| [] -> None
| c::s' ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> Some c)
     (fun n' -> get n' s')
     n)

(** val prefix : char list -> char list -> bool **)

let rec prefix s1 s2 =
  match s1 with
  | [] -> true
  | a::s1' ->
    (match s2 with
     | [] -> false
     | b::s2' -> if (=) a b then prefix s1' s2' else false)

(** val index : int -> char list -> char list -> int option **)

let rec index n s1 s2 = match s2 with
| [] ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> match s1 with
               | [] -> Some 0
               | _::_ -> None)
     (fun _ -> None)
     n)
| _::s2' ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ ->
     if prefix s1 s2
     then Some 0
     else (match index 0 s1 s2' with
           | Some n0 -> Some (Pervasives.succ n0)
           | None -> None))
     (fun n' ->
     match index n' s1 s2' with
     | Some n0 -> Some (Pervasives.succ n0)
     | None -> None)
     n)

(** val findex : int -> char list -> char list -> int **)

let findex n s1 s2 =
  match index n s1 s2 with
  | Some n0 -> n0
  | None -> 0
