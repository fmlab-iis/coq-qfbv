open Bool
open Datatypes
open FMaps
open FSets
open List0
open Typ
open Var
open Eqtype
open Ssreflect

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module type TypEnv =
 sig
  module SE :
   SsrOrder.SsrOrder

  module E :
   OrderedType.OrderedType with type t = SE.t

  type key = SE.t

  type 'x t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  type env = typ t

  val deftyp : typ

  val vtyp : SE.t -> env -> typ

  val vsize : SE.t -> env -> int

  val eequal : env -> env -> bool
 end

module TypEnvLemmas =
 functor (TE:TypEnv) ->
 struct
  module F =
   struct
    (** val eqb : TE.SE.t -> TE.SE.t -> bool **)

    let eqb x y =
      if TE.E.eq_dec x y then true else false

    (** val coq_In_dec : 'a1 TE.t -> TE.key -> bool **)

    let coq_In_dec m x =
      let b = TE.mem x m in if b then true else false
   end

  module OP =
   struct
    module ME = OrderedType.OrderedTypeFacts(TE.E)

    module O = OrderedType.KeyOrderedType(TE.E)

    module P =
     struct
      module F =
       struct
        (** val eqb : TE.SE.t -> TE.SE.t -> bool **)

        let eqb x y =
          if TE.E.eq_dec x y then true else false

        (** val coq_In_dec : 'a1 TE.t -> TE.key -> bool **)

        let coq_In_dec m x =
          let b = TE.mem x m in if b then true else false
       end

      (** val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3 **)

      let uncurry f p =
        f (fst p) (snd p)

      (** val of_list : (TE.key * 'a1) list -> 'a1 TE.t **)

      let of_list l =
        fold_right (uncurry TE.add) TE.empty l

      (** val to_list : 'a1 TE.t -> (TE.key * 'a1) list **)

      let to_list =
        TE.elements

      (** val fold_rec :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t -> __
          -> 'a3) -> (TE.key -> 'a1 -> 'a2 -> 'a1 TE.t -> 'a1 TE.t -> __ ->
          __ -> __ -> 'a3 -> 'a3) -> 'a3 **)

      let fold_rec f i m hempty hstep =
        let f0 = uncurry f in
        let l = rev (TE.elements m) in
        let hstep' = fun k e a m' m'' x ->
          hstep (fst (k, e)) (snd (k, e)) a m' m'' __ __ __ x
        in
        let rec f1 l0 hstep'0 m0 =
          match l0 with
          | [] -> hempty m0 __
          | y :: l1 ->
            let (a, b) = y in
            hstep'0 a b (fold_right f0 i l1) (of_list l1) m0 __ __ __
              (f1 l1 (fun k0 e0 a0 m' m'' _ _ _ x ->
                hstep'0 k0 e0 a0 m' m'' __ __ __ x) (of_list l1))
        in f1 l (fun k e a m' m'' _ _ _ x -> hstep' k e a m' m'' x) m

      (** val fold_rec_bis :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t ->
          'a1 TE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 ->
          'a2 -> 'a1 TE.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3 **)

      let fold_rec_bis f i m pmorphism pempty pstep =
        fold_rec f i m (fun m0 _ -> pmorphism TE.empty m0 i __ pempty)
          (fun k e a m' m'' _ _ _ x ->
          pmorphism (TE.add k e m') m'' (f k e a) __ (pstep k e a m' __ __ x))

      (** val fold_rec_nodep :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> 'a3 -> (TE.key
          -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 **)

      let fold_rec_nodep f i m x x0 =
        fold_rec_bis f i m (fun _ _ _ _ x1 -> x1) x (fun k e a _ _ _ x1 ->
          x0 k e a __ x1)

      (** val fold_rec_weak :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TE.t -> 'a1 TE.t ->
          'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 -> 'a2 -> 'a1
          TE.t -> __ -> 'a3 -> 'a3) -> 'a1 TE.t -> 'a3 **)

      let fold_rec_weak f i x x0 x1 m =
        fold_rec_bis f i m x x0 (fun k e a m' _ _ x2 -> x1 k e a m' __ x2)

      (** val fold_rel :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> (TE.key -> 'a1 -> 'a3 -> 'a3) ->
          'a2 -> 'a3 -> 'a1 TE.t -> 'a4 -> (TE.key -> 'a1 -> 'a2 -> 'a3 -> __
          -> 'a4 -> 'a4) -> 'a4 **)

      let fold_rel f g i j m rempty rstep =
        let l = rev (TE.elements m) in
        let rstep' = fun k e a b x -> rstep k e a b __ x in
        let rec f0 l0 rstep'0 =
          match l0 with
          | [] -> rempty
          | y :: l1 ->
            rstep'0 (fst y) (snd y) (fold_right (uncurry f) i l1)
              (fold_right (uncurry g) j l1) __
              (f0 l1 (fun k e a0 b _ x -> rstep'0 k e a0 b __ x))
        in f0 l (fun k e a b _ x -> rstep' k e a b x)

      (** val map_induction :
          ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.key
          -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2 **)

      let map_induction x x0 m =
        fold_rec (fun _ _ _ -> ()) () m x (fun k e _ m' m'' _ _ _ x1 ->
          x0 m' m'' x1 k e __ __)

      (** val map_induction_bis :
          ('a1 TE.t -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (TE.key -> 'a1
          -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a1 TE.t -> 'a2 **)

      let map_induction_bis x x0 x1 m =
        fold_rec_bis (fun _ _ _ -> ()) () m (fun m0 m' _ _ x2 ->
          x m0 m' __ x2) x0 (fun k e _ m' _ _ x2 -> x1 k e m' __ x2)

      (** val cardinal_inv_2 : 'a1 TE.t -> int -> (TE.key * 'a1) **)

      let cardinal_inv_2 m _ =
        let l = TE.elements m in
        (match l with
         | [] -> assert false (* absurd case *)
         | a :: _ -> a)

      (** val cardinal_inv_2b : 'a1 TE.t -> (TE.key * 'a1) **)

      let cardinal_inv_2b m =
        let n = TE.cardinal m in
        let x = fun x -> cardinal_inv_2 m x in
        ((fun fO fS n -> if n=0 then fO () else fS (n-1))
           (fun _ -> assert false (* absurd case *))
           (fun n0 -> x n0)
           n)

      (** val filter : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t **)

      let filter f m =
        TE.fold (fun k e m0 -> if f k e then TE.add k e m0 else m0) m TE.empty

      (** val for_all : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool **)

      let for_all f m =
        TE.fold (fun k e b -> if f k e then b else false) m true

      (** val exists_ : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool **)

      let exists_ f m =
        TE.fold (fun k e b -> if f k e then true else b) m false

      (** val partition :
          (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t **)

      let partition f m =
        ((filter f m), (filter (fun k e -> negb (f k e)) m))

      (** val update : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t **)

      let update m1 m2 =
        TE.fold TE.add m2 m1

      (** val restrict : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t **)

      let restrict m1 m2 =
        filter (fun k _ -> TE.mem k m2) m1

      (** val diff : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t **)

      let diff m1 m2 =
        filter (fun k _ -> negb (TE.mem k m2)) m1

      (** val coq_Partition_In :
          'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t -> TE.key -> bool **)

      let coq_Partition_In _ m1 _ k =
        F.coq_In_dec m1 k

      (** val update_dec : 'a1 TE.t -> 'a1 TE.t -> TE.key -> 'a1 -> bool **)

      let update_dec _ m' k _ =
        F.coq_In_dec m' k

      (** val filter_dom : (TE.key -> bool) -> 'a1 TE.t -> 'a1 TE.t **)

      let filter_dom f =
        filter (fun k _ -> f k)

      (** val filter_range : ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t **)

      let filter_range f =
        filter (fun _ -> f)

      (** val for_all_dom : (TE.key -> bool) -> 'a1 TE.t -> bool **)

      let for_all_dom f =
        for_all (fun k _ -> f k)

      (** val for_all_range : ('a1 -> bool) -> 'a1 TE.t -> bool **)

      let for_all_range f =
        for_all (fun _ -> f)

      (** val exists_dom : (TE.key -> bool) -> 'a1 TE.t -> bool **)

      let exists_dom f =
        exists_ (fun k _ -> f k)

      (** val exists_range : ('a1 -> bool) -> 'a1 TE.t -> bool **)

      let exists_range f =
        exists_ (fun _ -> f)

      (** val partition_dom :
          (TE.key -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t **)

      let partition_dom f =
        partition (fun k _ -> f k)

      (** val partition_range :
          ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t **)

      let partition_range f =
        partition (fun _ -> f)
     end

    (** val gtb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool **)

    let gtb p p' =
      match TE.E.compare (fst p) (fst p') with
      | OrderedType.GT -> true
      | _ -> false

    (** val leb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool **)

    let leb p p' =
      negb (gtb p p')

    (** val elements_lt :
        (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list **)

    let elements_lt p m =
      filter (gtb p) (TE.elements m)

    (** val elements_ge :
        (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list **)

    let elements_ge p m =
      filter (leb p) (TE.elements m)

    (** val max_elt_aux : (TE.key * 'a1) list -> (TE.key * 'a1) option **)

    let rec max_elt_aux = function
    | [] -> None
    | p :: l0 -> (match l0 with
                  | [] -> Some p
                  | _ :: _ -> max_elt_aux l0)

    (** val max_elt : 'a1 TE.t -> (TE.key * 'a1) option **)

    let max_elt m =
      max_elt_aux (TE.elements m)

    (** val min_elt : 'a1 TE.t -> (TE.key * 'a1) option **)

    let min_elt m =
      match TE.elements m with
      | [] -> None
      | p :: _ -> Some p

    (** val map_induction_max :
        ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2 **)

    let map_induction_max x x0 m =
      let n = TE.cardinal m in
      let rec f n0 m0 =
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> x m0 __)
          (fun n1 ->
          match max_elt m0 with
          | Some a ->
            let (a0, b) = a in
            x0 (TE.remove a0 m0) m0 (f n1 (TE.remove a0 m0)) a0 b __ __
          | None -> x m0 __)
          n0
      in f n m

    (** val map_induction_min :
        ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2 **)

    let map_induction_min x x0 m =
      let n = TE.cardinal m in
      let rec f n0 m0 =
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> x m0 __)
          (fun n1 ->
          match min_elt m0 with
          | Some a ->
            let (a0, b) = a in
            x0 (TE.remove a0 m0) m0 (f n1 (TE.remove a0 m0)) a0 b __ __
          | None -> x m0 __)
          n0
      in f n m
   end

  (** val eqb : TE.SE.t -> TE.SE.t -> bool **)

  let eqb x y =
    if TE.E.eq_dec x y then true else false

  (** val coq_In_dec : 'a1 TE.t -> TE.key -> bool **)

  let coq_In_dec =
    F.coq_In_dec

  module ME = OP.ME

  module O = OP.O

  module P = OP.P

  (** val gtb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool **)

  let gtb p p' =
    match TE.E.compare (fst p) (fst p') with
    | OrderedType.GT -> true
    | _ -> false

  (** val leb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool **)

  let leb p p' =
    negb (gtb p p')

  (** val elements_lt : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list **)

  let elements_lt p m =
    filter (gtb p) (TE.elements m)

  (** val elements_ge : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list **)

  let elements_ge p m =
    filter (leb p) (TE.elements m)

  (** val max_elt_aux : (TE.key * 'a1) list -> (TE.key * 'a1) option **)

  let rec max_elt_aux = function
  | [] -> None
  | p :: l0 -> (match l0 with
                | [] -> Some p
                | _ :: _ -> max_elt_aux l0)

  (** val max_elt : 'a1 TE.t -> (TE.key * 'a1) option **)

  let max_elt m =
    max_elt_aux (TE.elements m)

  (** val min_elt : 'a1 TE.t -> (TE.key * 'a1) option **)

  let min_elt m =
    match TE.elements m with
    | [] -> None
    | p :: _ -> Some p

  (** val map_induction_max :
      ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
      'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2 **)

  let map_induction_max =
    OP.map_induction_max

  (** val map_induction_min :
      ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
      'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2 **)

  let map_induction_min =
    OP.map_induction_min

  (** val memP : TE.key -> 'a1 TE.t -> reflect **)

  let memP k m =
    let _evar_0_ = fun _ -> ReflectT in
    let _evar_0_0 = fun _ -> ReflectF in
    if TE.mem k m then _evar_0_ __ else _evar_0_0 __

  (** val split : ('a1 * 'a2) TE.t -> 'a1 TE.t * 'a2 TE.t **)

  let split m =
    ((TE.fold (fun k e m1 -> TE.add k (fst e) m1) m TE.empty),
      (TE.fold (fun k e m2 -> TE.add k (snd e) m2) m TE.empty))

  module EFacts = OrderedType.OrderedTypeFacts(TE.E)

  (** val max_opt : TE.key -> TE.key option -> TE.key **)

  let max_opt k = function
  | Some k' -> (match TE.E.compare k k' with
                | OrderedType.LT -> k'
                | _ -> k)
  | None -> k

  (** val max_key_elements : (TE.key * 'a1) list -> TE.key option **)

  let rec max_key_elements = function
  | [] -> None
  | p :: tl -> let (k, _) = p in Some (max_opt k (max_key_elements tl))

  (** val max_key : 'a1 TE.t -> TE.key option **)

  let max_key m =
    max_key_elements (TE.elements m)

  (** val min_opt : TE.key -> TE.key option -> TE.key **)

  let min_opt k = function
  | Some k' -> (match TE.E.compare k k' with
                | OrderedType.GT -> k'
                | _ -> k)
  | None -> k

  (** val min_key_elements : (TE.key * 'a1) list -> TE.key option **)

  let rec min_key_elements = function
  | [] -> None
  | p :: tl -> let (k, _) = p in Some (min_opt k (min_key_elements tl))

  (** val min_key : 'a1 TE.t -> TE.key option **)

  let min_key m =
    min_key_elements (TE.elements m)

  (** val equalP : typ TE.t -> typ TE.t -> reflect **)

  let equalP x y =
    ssr_have __ (fun _ ->
      let _evar_0_ = fun _ -> ReflectT in
      let _evar_0_0 = fun _ -> ReflectF in
      if TE.equal typ_eqn x y then _evar_0_ __ else _evar_0_0 __)

  (** val eequalP : typ TE.t -> typ TE.t -> reflect **)

  let eequalP =
    equalP
 end

module MakeTypEnv =
 functor (V:SsrOrder.SsrOrder) ->
 functor (VM:SsrFMap with module SE = V) ->
 struct
  module SE = V

  module E = VM.E

  type key = SE.t

  type 'x t = 'x VM.t

  (** val empty : 'a1 t **)

  let empty =
    VM.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty =
    VM.is_empty

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add =
    VM.add

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find =
    VM.find

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove =
    VM.remove

  (** val mem : key -> 'a1 t -> bool **)

  let mem =
    VM.mem

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map =
    VM.map

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi =
    VM.mapi

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 =
    VM.map2

  (** val elements : 'a1 t -> (key * 'a1) list **)

  let elements =
    VM.elements

  (** val cardinal : 'a1 t -> int **)

  let cardinal =
    VM.cardinal

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold =
    VM.fold

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal =
    VM.equal

  module Lemmas = FMapLemmas(VM)

  type env = typ t

  (** val deftyp : typ **)

  let deftyp =
    Tuint 0

  (** val vtyp : V.t -> env -> typ **)

  let vtyp v e =
    match VM.find v e with
    | Some ty -> ty
    | None -> deftyp

  (** val vsize : V.t -> env -> int **)

  let vsize v e =
    sizeof_typ (vtyp v e)

  (** val eequal : typ t -> typ t -> bool **)

  let eequal =
    equal typ_eqn
 end

module SSATE = MakeTypEnv(SSAVarOrder)(SSAVM)

module TypEnvAgree =
 functor (V:SsrOrder.SsrOrder) ->
 functor (TE:TypEnv with module SE = V) ->
 functor (VS:SsrFSet with module SE = V) ->
 struct
  module MA = MapAgree(V)(TE)(VS)

  module VSLemmas = MA.VSLemmas

  module VMLemmas = MA.VMLemmas
 end
