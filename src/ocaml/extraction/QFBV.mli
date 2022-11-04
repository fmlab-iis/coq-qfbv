open Bool
open Datatypes
open FMaps
open FSets
open NBitsDef
open NBitsOp
open State
open Typ
open Var
open Eqtype
open Seq
open Ssrbool
open Ssrnat

type __ = Obj.t

module MakeQFBV :
 functor (V:SsrOrder.SsrOrder) ->
 functor (VS:SsrFSet with module SE = V) ->
 functor (TE:TypEnv.TypEnv with module SE = V) ->
 functor (S:sig
  type t

  val acc : V.t -> t -> bits

  val upd : V.t -> bits -> t -> t

  val upd2 : V.t -> bits -> V.t -> bits -> t -> t

  module Lemmas :
   sig
    module F :
     sig
      val eqb : TE.SE.t -> TE.SE.t -> bool

      val coq_In_dec : 'a1 TE.t -> TE.key -> bool
     end

    module OP :
     sig
      module ME :
       sig
        module TO :
         sig
          type t = TE.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TE.SE.t -> TE.SE.t -> bool

        val lt_dec : TE.SE.t -> TE.SE.t -> bool

        val eqb : TE.SE.t -> TE.SE.t -> bool
       end

      module O :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = TE.SE.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : TE.SE.t -> TE.SE.t -> bool

          val lt_dec : TE.SE.t -> TE.SE.t -> bool

          val eqb : TE.SE.t -> TE.SE.t -> bool
         end
       end

      module P :
       sig
        module F :
         sig
          val eqb : TE.SE.t -> TE.SE.t -> bool

          val coq_In_dec : 'a1 TE.t -> TE.key -> bool
         end

        val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

        val of_list : (TE.key * 'a1) list -> 'a1 TE.t

        val to_list : 'a1 TE.t -> (TE.key * 'a1) list

        val fold_rec :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t -> __
          -> 'a3) -> (TE.key -> 'a1 -> 'a2 -> 'a1 TE.t -> 'a1 TE.t -> __ ->
          __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_bis :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t ->
          'a1 TE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 ->
          'a2 -> 'a1 TE.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_nodep :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> 'a3 -> (TE.key
          -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_weak :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TE.t -> 'a1 TE.t ->
          'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 -> 'a2 -> 'a1
          TE.t -> __ -> 'a3 -> 'a3) -> 'a1 TE.t -> 'a3

        val fold_rel :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> (TE.key -> 'a1 -> 'a3 -> 'a3) ->
          'a2 -> 'a3 -> 'a1 TE.t -> 'a4 -> (TE.key -> 'a1 -> 'a2 -> 'a3 -> __
          -> 'a4 -> 'a4) -> 'a4

        val map_induction :
          ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.key
          -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

        val map_induction_bis :
          ('a1 TE.t -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (TE.key -> 'a1
          -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a1 TE.t -> 'a2

        val cardinal_inv_2 : 'a1 TE.t -> int -> (TE.key * 'a1)

        val cardinal_inv_2b : 'a1 TE.t -> (TE.key * 'a1)

        val filter : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t

        val for_all : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool

        val exists_ : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool

        val partition :
          (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t

        val update : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

        val restrict : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

        val diff : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

        val coq_Partition_In :
          'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t -> TE.key -> bool

        val update_dec : 'a1 TE.t -> 'a1 TE.t -> TE.key -> 'a1 -> bool

        val filter_dom : (TE.key -> bool) -> 'a1 TE.t -> 'a1 TE.t

        val filter_range : ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t

        val for_all_dom : (TE.key -> bool) -> 'a1 TE.t -> bool

        val for_all_range : ('a1 -> bool) -> 'a1 TE.t -> bool

        val exists_dom : (TE.key -> bool) -> 'a1 TE.t -> bool

        val exists_range : ('a1 -> bool) -> 'a1 TE.t -> bool

        val partition_dom :
          (TE.key -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t

        val partition_range : ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t
       end

      val gtb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool

      val leb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool

      val elements_lt : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list

      val elements_ge : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list

      val max_elt_aux : (TE.key * 'a1) list -> (TE.key * 'a1) option

      val max_elt : 'a1 TE.t -> (TE.key * 'a1) option

      val min_elt : 'a1 TE.t -> (TE.key * 'a1) option

      val map_induction_max :
        ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

      val map_induction_min :
        ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2
     end

    val eqb : TE.SE.t -> TE.SE.t -> bool

    val coq_In_dec : 'a1 TE.t -> TE.key -> bool

    module ME :
     sig
      module TO :
       sig
        type t = TE.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : TE.SE.t -> TE.SE.t -> bool

      val lt_dec : TE.SE.t -> TE.SE.t -> bool

      val eqb : TE.SE.t -> TE.SE.t -> bool
     end

    module O :
     sig
      module MO :
       sig
        module TO :
         sig
          type t = TE.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TE.SE.t -> TE.SE.t -> bool

        val lt_dec : TE.SE.t -> TE.SE.t -> bool

        val eqb : TE.SE.t -> TE.SE.t -> bool
       end
     end

    module P :
     sig
      module F :
       sig
        val eqb : TE.SE.t -> TE.SE.t -> bool

        val coq_In_dec : 'a1 TE.t -> TE.key -> bool
       end

      val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

      val of_list : (TE.key * 'a1) list -> 'a1 TE.t

      val to_list : 'a1 TE.t -> (TE.key * 'a1) list

      val fold_rec :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t -> __
        -> 'a3) -> (TE.key -> 'a1 -> 'a2 -> 'a1 TE.t -> 'a1 TE.t -> __ -> __
        -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_bis :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t -> 'a1
        TE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 -> 'a2 ->
        'a1 TE.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_nodep :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> 'a3 -> (TE.key ->
        'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_weak :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TE.t -> 'a1 TE.t -> 'a2
        -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 -> 'a2 -> 'a1 TE.t ->
        __ -> 'a3 -> 'a3) -> 'a1 TE.t -> 'a3

      val fold_rel :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> (TE.key -> 'a1 -> 'a3 -> 'a3) -> 'a2
        -> 'a3 -> 'a1 TE.t -> 'a4 -> (TE.key -> 'a1 -> 'a2 -> 'a3 -> __ ->
        'a4 -> 'a4) -> 'a4

      val map_induction :
        ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.key ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

      val map_induction_bis :
        ('a1 TE.t -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (TE.key -> 'a1
        -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a1 TE.t -> 'a2

      val cardinal_inv_2 : 'a1 TE.t -> int -> (TE.key * 'a1)

      val cardinal_inv_2b : 'a1 TE.t -> (TE.key * 'a1)

      val filter : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t

      val for_all : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool

      val exists_ : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool

      val partition :
        (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t

      val update : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

      val restrict : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

      val diff : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

      val coq_Partition_In :
        'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t -> TE.key -> bool

      val update_dec : 'a1 TE.t -> 'a1 TE.t -> TE.key -> 'a1 -> bool

      val filter_dom : (TE.key -> bool) -> 'a1 TE.t -> 'a1 TE.t

      val filter_range : ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t

      val for_all_dom : (TE.key -> bool) -> 'a1 TE.t -> bool

      val for_all_range : ('a1 -> bool) -> 'a1 TE.t -> bool

      val exists_dom : (TE.key -> bool) -> 'a1 TE.t -> bool

      val exists_range : ('a1 -> bool) -> 'a1 TE.t -> bool

      val partition_dom : (TE.key -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t

      val partition_range : ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t
     end

    val gtb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool

    val leb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool

    val elements_lt : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list

    val elements_ge : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list

    val max_elt_aux : (TE.key * 'a1) list -> (TE.key * 'a1) option

    val max_elt : 'a1 TE.t -> (TE.key * 'a1) option

    val min_elt : 'a1 TE.t -> (TE.key * 'a1) option

    val map_induction_max :
      ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
      'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

    val map_induction_min :
      ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
      'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

    val memP : TE.key -> 'a1 TE.t -> reflect

    val split : ('a1 * 'a2) TE.t -> 'a1 TE.t * 'a2 TE.t

    module EFacts :
     sig
      module TO :
       sig
        type t = TE.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : TE.SE.t -> TE.SE.t -> bool

      val lt_dec : TE.SE.t -> TE.SE.t -> bool

      val eqb : TE.SE.t -> TE.SE.t -> bool
     end

    val max_opt : TE.key -> TE.key option -> TE.key

    val max_key_elements : (TE.key * 'a1) list -> TE.key option

    val max_key : 'a1 TE.t -> TE.key option

    val min_opt : TE.key -> TE.key option -> TE.key

    val min_key_elements : (TE.key * 'a1) list -> TE.key option

    val min_key : 'a1 TE.t -> TE.key option

    val equalP : typ TE.t -> typ TE.t -> reflect

    val eequalP : typ TE.t -> typ TE.t -> reflect
   end
 end) ->
 sig
  module VSLemmas :
   sig
    module F :
     sig
      val eqb : VS.SE.t -> VS.SE.t -> bool
     end

    module OP :
     sig
      module ME :
       sig
        module TO :
         sig
          type t = VS.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : VS.SE.t -> VS.SE.t -> bool

        val lt_dec : VS.SE.t -> VS.SE.t -> bool

        val eqb : VS.SE.t -> VS.SE.t -> bool
       end

      module P :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : VS.SE.t -> VS.SE.t -> bool
           end

          module FSetLogicalFacts :
           sig
           end

          module FSetDecideAuxiliary :
           sig
           end

          module FSetDecideTestCases :
           sig
           end
         end

        module FM :
         sig
          val eqb : VS.SE.t -> VS.SE.t -> bool
         end

        val coq_In_dec : VS.elt -> VS.t -> bool

        val of_list : VS.elt list -> VS.t

        val to_list : VS.t -> VS.elt list

        val fold_rec :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> __ -> 'a2) ->
          (VS.elt -> 'a1 -> VS.t -> VS.t -> __ -> __ -> __ -> 'a2 -> 'a2) ->
          'a2

        val fold_rec_bis :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> VS.t -> 'a1 -> __
          -> 'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> __ -> 'a2
          -> 'a2) -> 'a2

        val fold_rec_nodep :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> 'a2 -> (VS.elt -> 'a1 ->
          __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (VS.elt -> 'a1 -> 'a1) -> 'a1 -> (VS.t -> VS.t -> 'a1 -> __ -> 'a2
          -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> 'a2 -> 'a2) ->
          VS.t -> 'a2

        val fold_rel :
          (VS.elt -> 'a1 -> 'a1) -> (VS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
          VS.t -> 'a3 -> (VS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val set_induction :
          (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.elt -> __ -> __
          -> 'a1) -> VS.t -> 'a1

        val set_induction_bis :
          (VS.t -> VS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VS.elt -> VS.t -> __
          -> 'a1 -> 'a1) -> VS.t -> 'a1

        val cardinal_inv_2 : VS.t -> int -> VS.elt

        val cardinal_inv_2b : VS.t -> VS.elt
       end

      val gtb : VS.SE.t -> VS.SE.t -> bool

      val leb : VS.SE.t -> VS.SE.t -> bool

      val elements_lt : VS.SE.t -> VS.t -> VS.SE.t list

      val elements_ge : VS.SE.t -> VS.t -> VS.SE.t list

      val set_induction_max :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
        'a1) -> VS.t -> 'a1

      val set_induction_min :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
        'a1) -> VS.t -> 'a1
     end

    val eqb : VS.SE.t -> VS.SE.t -> bool

    module ME :
     sig
      module TO :
       sig
        type t = VS.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : VS.SE.t -> VS.SE.t -> bool

      val lt_dec : VS.SE.t -> VS.SE.t -> bool

      val eqb : VS.SE.t -> VS.SE.t -> bool
     end

    module P :
     sig
      module Dec :
       sig
        module F :
         sig
          val eqb : VS.SE.t -> VS.SE.t -> bool
         end

        module FSetLogicalFacts :
         sig
         end

        module FSetDecideAuxiliary :
         sig
         end

        module FSetDecideTestCases :
         sig
         end
       end

      module FM :
       sig
        val eqb : VS.SE.t -> VS.SE.t -> bool
       end

      val coq_In_dec : VS.elt -> VS.t -> bool

      val of_list : VS.elt list -> VS.t

      val to_list : VS.t -> VS.elt list

      val fold_rec :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> __ -> 'a2) ->
        (VS.elt -> 'a1 -> VS.t -> VS.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_bis :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> (VS.t -> VS.t -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> __ -> 'a2 ->
        'a2) -> 'a2

      val fold_rec_nodep :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> VS.t -> 'a2 -> (VS.elt -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2

      val fold_rec_weak :
        (VS.elt -> 'a1 -> 'a1) -> 'a1 -> (VS.t -> VS.t -> 'a1 -> __ -> 'a2 ->
        'a2) -> 'a2 -> (VS.elt -> 'a1 -> VS.t -> __ -> 'a2 -> 'a2) -> VS.t ->
        'a2

      val fold_rel :
        (VS.elt -> 'a1 -> 'a1) -> (VS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
        VS.t -> 'a3 -> (VS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val set_induction :
        (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.elt -> __ -> __ ->
        'a1) -> VS.t -> 'a1

      val set_induction_bis :
        (VS.t -> VS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (VS.elt -> VS.t -> __ ->
        'a1 -> 'a1) -> VS.t -> 'a1

      val cardinal_inv_2 : VS.t -> int -> VS.elt

      val cardinal_inv_2b : VS.t -> VS.elt
     end

    val gtb : VS.SE.t -> VS.SE.t -> bool

    val leb : VS.SE.t -> VS.SE.t -> bool

    val elements_lt : VS.SE.t -> VS.t -> VS.SE.t list

    val elements_ge : VS.SE.t -> VS.t -> VS.SE.t list

    val set_induction_max :
      (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
      'a1) -> VS.t -> 'a1

    val set_induction_min :
      (VS.t -> __ -> 'a1) -> (VS.t -> VS.t -> 'a1 -> VS.SE.t -> __ -> __ ->
      'a1) -> VS.t -> 'a1

    val memP : VS.elt -> VS.t -> reflect

    val equalP : VS.t -> VS.t -> reflect

    val subsetP : VS.t -> VS.t -> reflect

    val emptyP : VS.t -> reflect

    val disjoint : VS.t -> VS.t -> bool

    val proper_subset : VS.t -> VS.t -> bool
   end

  type eunop =
  | Unot
  | Uneg
  | Uextr of int * int
  | Uhigh of int
  | Ulow of int
  | Uzext of int
  | Usext of int
  | Urepeat of int
  | Urotl of int
  | Urotr of int

  val eunop_rect :
    'a1 -> 'a1 -> (int -> int -> 'a1) -> (int -> 'a1) -> (int -> 'a1) -> (int
    -> 'a1) -> (int -> 'a1) -> (int -> 'a1) -> (int -> 'a1) -> (int -> 'a1)
    -> eunop -> 'a1

  val eunop_rec :
    'a1 -> 'a1 -> (int -> int -> 'a1) -> (int -> 'a1) -> (int -> 'a1) -> (int
    -> 'a1) -> (int -> 'a1) -> (int -> 'a1) -> (int -> 'a1) -> (int -> 'a1)
    -> eunop -> 'a1

  type ebinop =
  | Band
  | Bor
  | Bxor
  | Badd
  | Bsub
  | Bmul
  | Bdiv
  | Bmod
  | Bsdiv
  | Bsrem
  | Bsmod
  | Bshl
  | Blshr
  | Bashr
  | Bconcat
  | Bcomp

  val ebinop_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> ebinop -> 'a1

  val ebinop_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> ebinop -> 'a1

  type bbinop =
  | Beq
  | Bult
  | Bule
  | Bugt
  | Buge
  | Bslt
  | Bsle
  | Bsgt
  | Bsge
  | Buaddo
  | Busubo
  | Bumulo
  | Bsaddo
  | Bssubo
  | Bsmulo

  val bbinop_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bbinop -> 'a1

  val bbinop_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bbinop -> 'a1

  type exp =
  | Evar of V.t
  | Econst of bits
  | Eunop of eunop * exp
  | Ebinop of ebinop * exp * exp
  | Eite of bexp * exp * exp
  and bexp =
  | Bfalse
  | Btrue
  | Bbinop of bbinop * exp * exp
  | Blneg of bexp
  | Bconj of bexp * bexp
  | Bdisj of bexp * bexp

  val exp_rect :
    (V.t -> 'a1) -> (bits -> 'a1) -> (eunop -> exp -> 'a1 -> 'a1) -> (ebinop
    -> exp -> 'a1 -> exp -> 'a1 -> 'a1) -> (bexp -> exp -> 'a1 -> exp -> 'a1
    -> 'a1) -> exp -> 'a1

  val exp_rec :
    (V.t -> 'a1) -> (bits -> 'a1) -> (eunop -> exp -> 'a1 -> 'a1) -> (ebinop
    -> exp -> 'a1 -> exp -> 'a1 -> 'a1) -> (bexp -> exp -> 'a1 -> exp -> 'a1
    -> 'a1) -> exp -> 'a1

  val bexp_rect :
    'a1 -> 'a1 -> (bbinop -> exp -> exp -> 'a1) -> (bexp -> 'a1 -> 'a1) ->
    (bexp -> 'a1 -> bexp -> 'a1 -> 'a1) -> (bexp -> 'a1 -> bexp -> 'a1 ->
    'a1) -> bexp -> 'a1

  val bexp_rec :
    'a1 -> 'a1 -> (bbinop -> exp -> exp -> 'a1) -> (bexp -> 'a1 -> 'a1) ->
    (bexp -> 'a1 -> bexp -> 'a1 -> 'a1) -> (bexp -> 'a1 -> bexp -> 'a1 ->
    'a1) -> bexp -> 'a1

  val eunop_eqn : eunop -> eunop -> bool

  val eunop_eqP : eunop -> eunop -> reflect

  val eunop_eqMixin : eunop Equality.mixin_of

  val eunop_eqType : Equality.coq_type

  val ebinop_eqn : ebinop -> ebinop -> bool

  val ebinop_eqP : ebinop -> ebinop -> reflect

  val ebinop_eqMixin : ebinop Equality.mixin_of

  val ebinop_eqType : Equality.coq_type

  val bbinop_eqn : bbinop -> bbinop -> bool

  val bbinop_eqP : bbinop -> bbinop -> reflect

  val bbinop_eqMixin : bbinop Equality.mixin_of

  val bbinop_eqType : Equality.coq_type

  val exp_eqn : exp -> exp -> bool

  val bexp_eqn : bexp -> bexp -> bool

  val exp_eqP : exp -> exp -> reflect

  val bexp_eqP : bexp -> bexp -> reflect

  val exp_eqMixin : exp Equality.mixin_of

  val bexp_eqMixin : bexp Equality.mixin_of

  val exp_eqType : Equality.coq_type

  val bexp_eqType : Equality.coq_type

  val qfbv_true : bexp

  val qfbv_false : bexp

  val qfbv_var : V.t -> exp

  val qfbv_const : int -> int -> exp

  val qfbv_zero : int -> exp

  val qfbv_one : int -> exp

  val qfbv_not : exp -> exp

  val qfbv_neg : exp -> exp

  val qfbv_extr : int -> int -> exp -> exp

  val qfbv_high : int -> exp -> exp

  val qfbv_low : int -> exp -> exp

  val qfbv_zext : int -> exp -> exp

  val qfbv_sext : int -> exp -> exp

  val qfbv_and : exp -> exp -> exp

  val qfbv_or : exp -> exp -> exp

  val qfbv_xor : exp -> exp -> exp

  val qfbv_add : exp -> exp -> exp

  val qfbv_sub : exp -> exp -> exp

  val qfbv_mul : exp -> exp -> exp

  val qfbv_mod : exp -> exp -> exp

  val qfbv_srem : exp -> exp -> exp

  val qfbv_smod : exp -> exp -> exp

  val qfbv_shl : exp -> exp -> exp

  val qfbv_lshr : exp -> exp -> exp

  val qfbv_ashr : exp -> exp -> exp

  val qfbv_concat : exp -> exp -> exp

  val qfbv_eq : exp -> exp -> bexp

  val qfbv_ult : exp -> exp -> bexp

  val qfbv_ule : exp -> exp -> bexp

  val qfbv_ugt : exp -> exp -> bexp

  val qfbv_uge : exp -> exp -> bexp

  val qfbv_slt : exp -> exp -> bexp

  val qfbv_sle : exp -> exp -> bexp

  val qfbv_sgt : exp -> exp -> bexp

  val qfbv_sge : exp -> exp -> bexp

  val qfbv_uaddo : exp -> exp -> bexp

  val qfbv_usubo : exp -> exp -> bexp

  val qfbv_umulo : exp -> exp -> bexp

  val qfbv_saddo : exp -> exp -> bexp

  val qfbv_ssubo : exp -> exp -> bexp

  val qfbv_smulo : exp -> exp -> bexp

  val qfbv_lneg : bexp -> bexp

  val qfbv_conj : bexp -> bexp -> bexp

  val qfbv_disj : bexp -> bexp -> bexp

  val qfbv_ite : bexp -> exp -> exp -> exp

  val qfbv_imp : bexp -> bexp -> bexp

  val eunop_denote : eunop -> bits -> bits

  val ebinop_denote : ebinop -> bits -> bits -> bits

  val bbinop_denote : bbinop -> bits -> bits -> bool

  val eval_exp : exp -> S.t -> bits

  val eval_bexp : bexp -> S.t -> bool

  val vars_exp : exp -> VS.t

  val vars_bexp : bexp -> VS.t

  val vars_bexps : bexp list -> VS.t

  val id_eunop : eunop -> int

  val eunop_ltn : eunop -> eunop -> bool

  val id_ebinop : ebinop -> int

  val ebinop_ltn : ebinop -> ebinop -> bool

  val id_bbinop : bbinop -> int

  val bbinop_ltn : bbinop -> bbinop -> bool

  val id_exp : exp -> int

  val id_bexp : bexp -> int

  val exp_ltn : exp -> exp -> bool

  val bexp_ltn : bexp -> bexp -> bool

  val exp_compare : exp -> exp -> exp OrderedType.coq_Compare

  val bexp_compare : bexp -> bexp -> bexp OrderedType.coq_Compare

  module ExpOrderMinimal :
   sig
    val t : Equality.coq_type

    val eqn : Equality.sort -> Equality.sort -> bool

    val ltn : Equality.sort -> Equality.sort -> bool

    val compare :
      Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare
   end

  module ExpOrder :
   sig
    val coq_T : Equality.coq_type

    type t = Equality.sort

    val ltn : t -> t -> bool

    val compare : t -> t -> t OrderedType.coq_Compare

    val eq_dec : t -> t -> bool
   end

  module BexpOrderMinimal :
   sig
    val t : Equality.coq_type

    val eqn : Equality.sort -> Equality.sort -> bool

    val ltn : Equality.sort -> Equality.sort -> bool

    val compare :
      Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare
   end

  module BexpOrder :
   sig
    val coq_T : Equality.coq_type

    type t = Equality.sort

    val ltn : t -> t -> bool

    val compare : t -> t -> t OrderedType.coq_Compare

    val eq_dec : t -> t -> bool
   end

  val len_exp : exp -> int

  val len_bexp : bexp -> int

  val subee : exp -> exp -> bool

  val subeb : exp -> bexp -> bool

  val subbe : bexp -> exp -> bool

  val subbb : bexp -> bexp -> bool

  module TELemmas :
   sig
    module F :
     sig
      val eqb : TE.SE.t -> TE.SE.t -> bool

      val coq_In_dec : 'a1 TE.t -> TE.key -> bool
     end

    module OP :
     sig
      module ME :
       sig
        module TO :
         sig
          type t = TE.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TE.SE.t -> TE.SE.t -> bool

        val lt_dec : TE.SE.t -> TE.SE.t -> bool

        val eqb : TE.SE.t -> TE.SE.t -> bool
       end

      module O :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = TE.SE.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : TE.SE.t -> TE.SE.t -> bool

          val lt_dec : TE.SE.t -> TE.SE.t -> bool

          val eqb : TE.SE.t -> TE.SE.t -> bool
         end
       end

      module P :
       sig
        module F :
         sig
          val eqb : TE.SE.t -> TE.SE.t -> bool

          val coq_In_dec : 'a1 TE.t -> TE.key -> bool
         end

        val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

        val of_list : (TE.key * 'a1) list -> 'a1 TE.t

        val to_list : 'a1 TE.t -> (TE.key * 'a1) list

        val fold_rec :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t -> __
          -> 'a3) -> (TE.key -> 'a1 -> 'a2 -> 'a1 TE.t -> 'a1 TE.t -> __ ->
          __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_bis :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t ->
          'a1 TE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 ->
          'a2 -> 'a1 TE.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_nodep :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> 'a3 -> (TE.key
          -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_weak :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TE.t -> 'a1 TE.t ->
          'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 -> 'a2 -> 'a1
          TE.t -> __ -> 'a3 -> 'a3) -> 'a1 TE.t -> 'a3

        val fold_rel :
          (TE.key -> 'a1 -> 'a2 -> 'a2) -> (TE.key -> 'a1 -> 'a3 -> 'a3) ->
          'a2 -> 'a3 -> 'a1 TE.t -> 'a4 -> (TE.key -> 'a1 -> 'a2 -> 'a3 -> __
          -> 'a4 -> 'a4) -> 'a4

        val map_induction :
          ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.key
          -> 'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

        val map_induction_bis :
          ('a1 TE.t -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (TE.key -> 'a1
          -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a1 TE.t -> 'a2

        val cardinal_inv_2 : 'a1 TE.t -> int -> (TE.key * 'a1)

        val cardinal_inv_2b : 'a1 TE.t -> (TE.key * 'a1)

        val filter : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t

        val for_all : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool

        val exists_ : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool

        val partition :
          (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t

        val update : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

        val restrict : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

        val diff : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

        val coq_Partition_In :
          'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t -> TE.key -> bool

        val update_dec : 'a1 TE.t -> 'a1 TE.t -> TE.key -> 'a1 -> bool

        val filter_dom : (TE.key -> bool) -> 'a1 TE.t -> 'a1 TE.t

        val filter_range : ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t

        val for_all_dom : (TE.key -> bool) -> 'a1 TE.t -> bool

        val for_all_range : ('a1 -> bool) -> 'a1 TE.t -> bool

        val exists_dom : (TE.key -> bool) -> 'a1 TE.t -> bool

        val exists_range : ('a1 -> bool) -> 'a1 TE.t -> bool

        val partition_dom :
          (TE.key -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t

        val partition_range : ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t
       end

      val gtb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool

      val leb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool

      val elements_lt : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list

      val elements_ge : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list

      val max_elt_aux : (TE.key * 'a1) list -> (TE.key * 'a1) option

      val max_elt : 'a1 TE.t -> (TE.key * 'a1) option

      val min_elt : 'a1 TE.t -> (TE.key * 'a1) option

      val map_induction_max :
        ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

      val map_induction_min :
        ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2
     end

    val eqb : TE.SE.t -> TE.SE.t -> bool

    val coq_In_dec : 'a1 TE.t -> TE.key -> bool

    module ME :
     sig
      module TO :
       sig
        type t = TE.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : TE.SE.t -> TE.SE.t -> bool

      val lt_dec : TE.SE.t -> TE.SE.t -> bool

      val eqb : TE.SE.t -> TE.SE.t -> bool
     end

    module O :
     sig
      module MO :
       sig
        module TO :
         sig
          type t = TE.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TE.SE.t -> TE.SE.t -> bool

        val lt_dec : TE.SE.t -> TE.SE.t -> bool

        val eqb : TE.SE.t -> TE.SE.t -> bool
       end
     end

    module P :
     sig
      module F :
       sig
        val eqb : TE.SE.t -> TE.SE.t -> bool

        val coq_In_dec : 'a1 TE.t -> TE.key -> bool
       end

      val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

      val of_list : (TE.key * 'a1) list -> 'a1 TE.t

      val to_list : 'a1 TE.t -> (TE.key * 'a1) list

      val fold_rec :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t -> __
        -> 'a3) -> (TE.key -> 'a1 -> 'a2 -> 'a1 TE.t -> 'a1 TE.t -> __ -> __
        -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_bis :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> ('a1 TE.t -> 'a1
        TE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 -> 'a2 ->
        'a1 TE.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_nodep :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TE.t -> 'a3 -> (TE.key ->
        'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_weak :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TE.t -> 'a1 TE.t -> 'a2
        -> __ -> 'a3 -> 'a3) -> 'a3 -> (TE.key -> 'a1 -> 'a2 -> 'a1 TE.t ->
        __ -> 'a3 -> 'a3) -> 'a1 TE.t -> 'a3

      val fold_rel :
        (TE.key -> 'a1 -> 'a2 -> 'a2) -> (TE.key -> 'a1 -> 'a3 -> 'a3) -> 'a2
        -> 'a3 -> 'a1 TE.t -> 'a4 -> (TE.key -> 'a1 -> 'a2 -> 'a3 -> __ ->
        'a4 -> 'a4) -> 'a4

      val map_induction :
        ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.key ->
        'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

      val map_induction_bis :
        ('a1 TE.t -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a2 -> (TE.key -> 'a1
        -> 'a1 TE.t -> __ -> 'a2 -> 'a2) -> 'a1 TE.t -> 'a2

      val cardinal_inv_2 : 'a1 TE.t -> int -> (TE.key * 'a1)

      val cardinal_inv_2b : 'a1 TE.t -> (TE.key * 'a1)

      val filter : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t

      val for_all : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool

      val exists_ : (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> bool

      val partition :
        (TE.key -> 'a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t

      val update : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

      val restrict : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

      val diff : 'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t

      val coq_Partition_In :
        'a1 TE.t -> 'a1 TE.t -> 'a1 TE.t -> TE.key -> bool

      val update_dec : 'a1 TE.t -> 'a1 TE.t -> TE.key -> 'a1 -> bool

      val filter_dom : (TE.key -> bool) -> 'a1 TE.t -> 'a1 TE.t

      val filter_range : ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t

      val for_all_dom : (TE.key -> bool) -> 'a1 TE.t -> bool

      val for_all_range : ('a1 -> bool) -> 'a1 TE.t -> bool

      val exists_dom : (TE.key -> bool) -> 'a1 TE.t -> bool

      val exists_range : ('a1 -> bool) -> 'a1 TE.t -> bool

      val partition_dom : (TE.key -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t

      val partition_range : ('a1 -> bool) -> 'a1 TE.t -> 'a1 TE.t * 'a1 TE.t
     end

    val gtb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool

    val leb : (TE.key * 'a1) -> (TE.key * 'a1) -> bool

    val elements_lt : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list

    val elements_ge : (TE.key * 'a1) -> 'a1 TE.t -> (TE.key * 'a1) list

    val max_elt_aux : (TE.key * 'a1) list -> (TE.key * 'a1) option

    val max_elt : 'a1 TE.t -> (TE.key * 'a1) option

    val min_elt : 'a1 TE.t -> (TE.key * 'a1) option

    val map_induction_max :
      ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
      'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

    val map_induction_min :
      ('a1 TE.t -> __ -> 'a2) -> ('a1 TE.t -> 'a1 TE.t -> 'a2 -> TE.SE.t ->
      'a1 -> __ -> __ -> 'a2) -> 'a1 TE.t -> 'a2

    val memP : TE.key -> 'a1 TE.t -> reflect

    val split : ('a1 * 'a2) TE.t -> 'a1 TE.t * 'a2 TE.t

    module EFacts :
     sig
      module TO :
       sig
        type t = TE.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : TE.SE.t -> TE.SE.t -> bool

      val lt_dec : TE.SE.t -> TE.SE.t -> bool

      val eqb : TE.SE.t -> TE.SE.t -> bool
     end

    val max_opt : TE.key -> TE.key option -> TE.key

    val max_key_elements : (TE.key * 'a1) list -> TE.key option

    val max_key : 'a1 TE.t -> TE.key option

    val min_opt : TE.key -> TE.key option -> TE.key

    val min_key_elements : (TE.key * 'a1) list -> TE.key option

    val min_key : 'a1 TE.t -> TE.key option
   end

  val exp_size : exp -> TE.env -> int

  val well_formed_exp : exp -> TE.env -> bool

  val well_formed_bexp : bexp -> TE.env -> bool

  val well_formed_bexps : bexp list -> TE.env -> bool

  val split_conj : bexp -> bexp list

  val qfbv_conjs : bexp list -> bexp

  val qfbv_conjs_rec : bexp -> bexp list -> bexp

  val qfbv_conjs_la : bexp list -> bexp

  val eval_bexps : bexp list -> S.t -> bool

  val simplify_bexp : bexp -> bexp

  val bexp_is_implied : bexp -> bool

  val simplify_bexp2 : bexp -> bexp
 end

module QFBV :
 sig
  module VSLemmas :
   sig
    module F :
     sig
      val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
     end

    module OP :
     sig
      module ME :
       sig
        module TO :
         sig
          type t = SSAVS.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : SSAVS.SE.t -> SSAVS.SE.t -> bool

        val lt_dec : SSAVS.SE.t -> SSAVS.SE.t -> bool

        val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
       end

      module P :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
           end

          module FSetLogicalFacts :
           sig
           end

          module FSetDecideAuxiliary :
           sig
           end

          module FSetDecideTestCases :
           sig
           end
         end

        module FM :
         sig
          val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
         end

        val coq_In_dec : SSAVS.elt -> SSAVS.t -> bool

        val of_list : SSAVS.elt list -> SSAVS.t

        val to_list : SSAVS.t -> SSAVS.elt list

        val fold_rec :
          (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> SSAVS.t -> (SSAVS.t -> __ ->
          'a2) -> (SSAVS.elt -> 'a1 -> SSAVS.t -> SSAVS.t -> __ -> __ -> __
          -> 'a2 -> 'a2) -> 'a2

        val fold_rec_bis :
          (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> SSAVS.t -> (SSAVS.t -> SSAVS.t
          -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (SSAVS.elt -> 'a1 -> SSAVS.t
          -> __ -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_nodep :
          (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> SSAVS.t -> 'a2 -> (SSAVS.elt ->
          'a1 -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> (SSAVS.t -> SSAVS.t -> 'a1 ->
          __ -> 'a2 -> 'a2) -> 'a2 -> (SSAVS.elt -> 'a1 -> SSAVS.t -> __ ->
          'a2 -> 'a2) -> SSAVS.t -> 'a2

        val fold_rel :
          (SSAVS.elt -> 'a1 -> 'a1) -> (SSAVS.elt -> 'a2 -> 'a2) -> 'a1 ->
          'a2 -> SSAVS.t -> 'a3 -> (SSAVS.elt -> 'a1 -> 'a2 -> __ -> 'a3 ->
          'a3) -> 'a3

        val set_induction :
          (SSAVS.t -> __ -> 'a1) -> (SSAVS.t -> SSAVS.t -> 'a1 -> SSAVS.elt
          -> __ -> __ -> 'a1) -> SSAVS.t -> 'a1

        val set_induction_bis :
          (SSAVS.t -> SSAVS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (SSAVS.elt ->
          SSAVS.t -> __ -> 'a1 -> 'a1) -> SSAVS.t -> 'a1

        val cardinal_inv_2 : SSAVS.t -> int -> SSAVS.elt

        val cardinal_inv_2b : SSAVS.t -> SSAVS.elt
       end

      val gtb : SSAVS.SE.t -> SSAVS.SE.t -> bool

      val leb : SSAVS.SE.t -> SSAVS.SE.t -> bool

      val elements_lt : SSAVS.SE.t -> SSAVS.t -> SSAVS.SE.t list

      val elements_ge : SSAVS.SE.t -> SSAVS.t -> SSAVS.SE.t list

      val set_induction_max :
        (SSAVS.t -> __ -> 'a1) -> (SSAVS.t -> SSAVS.t -> 'a1 -> SSAVS.SE.t ->
        __ -> __ -> 'a1) -> SSAVS.t -> 'a1

      val set_induction_min :
        (SSAVS.t -> __ -> 'a1) -> (SSAVS.t -> SSAVS.t -> 'a1 -> SSAVS.SE.t ->
        __ -> __ -> 'a1) -> SSAVS.t -> 'a1
     end

    val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool

    module ME :
     sig
      module TO :
       sig
        type t = SSAVS.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : SSAVS.SE.t -> SSAVS.SE.t -> bool

      val lt_dec : SSAVS.SE.t -> SSAVS.SE.t -> bool

      val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
     end

    module P :
     sig
      module Dec :
       sig
        module F :
         sig
          val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
         end

        module FSetLogicalFacts :
         sig
         end

        module FSetDecideAuxiliary :
         sig
         end

        module FSetDecideTestCases :
         sig
         end
       end

      module FM :
       sig
        val eqb : SSAVS.SE.t -> SSAVS.SE.t -> bool
       end

      val coq_In_dec : SSAVS.elt -> SSAVS.t -> bool

      val of_list : SSAVS.elt list -> SSAVS.t

      val to_list : SSAVS.t -> SSAVS.elt list

      val fold_rec :
        (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> SSAVS.t -> (SSAVS.t -> __ -> 'a2)
        -> (SSAVS.elt -> 'a1 -> SSAVS.t -> SSAVS.t -> __ -> __ -> __ -> 'a2
        -> 'a2) -> 'a2

      val fold_rec_bis :
        (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> SSAVS.t -> (SSAVS.t -> SSAVS.t ->
        'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (SSAVS.elt -> 'a1 -> SSAVS.t -> __
        -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_nodep :
        (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> SSAVS.t -> 'a2 -> (SSAVS.elt ->
        'a1 -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_weak :
        (SSAVS.elt -> 'a1 -> 'a1) -> 'a1 -> (SSAVS.t -> SSAVS.t -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2 -> (SSAVS.elt -> 'a1 -> SSAVS.t -> __ -> 'a2 ->
        'a2) -> SSAVS.t -> 'a2

      val fold_rel :
        (SSAVS.elt -> 'a1 -> 'a1) -> (SSAVS.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2
        -> SSAVS.t -> 'a3 -> (SSAVS.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) ->
        'a3

      val set_induction :
        (SSAVS.t -> __ -> 'a1) -> (SSAVS.t -> SSAVS.t -> 'a1 -> SSAVS.elt ->
        __ -> __ -> 'a1) -> SSAVS.t -> 'a1

      val set_induction_bis :
        (SSAVS.t -> SSAVS.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (SSAVS.elt ->
        SSAVS.t -> __ -> 'a1 -> 'a1) -> SSAVS.t -> 'a1

      val cardinal_inv_2 : SSAVS.t -> int -> SSAVS.elt

      val cardinal_inv_2b : SSAVS.t -> SSAVS.elt
     end

    val gtb : SSAVS.SE.t -> SSAVS.SE.t -> bool

    val leb : SSAVS.SE.t -> SSAVS.SE.t -> bool

    val elements_lt : SSAVS.SE.t -> SSAVS.t -> SSAVS.SE.t list

    val elements_ge : SSAVS.SE.t -> SSAVS.t -> SSAVS.SE.t list

    val set_induction_max :
      (SSAVS.t -> __ -> 'a1) -> (SSAVS.t -> SSAVS.t -> 'a1 -> SSAVS.SE.t ->
      __ -> __ -> 'a1) -> SSAVS.t -> 'a1

    val set_induction_min :
      (SSAVS.t -> __ -> 'a1) -> (SSAVS.t -> SSAVS.t -> 'a1 -> SSAVS.SE.t ->
      __ -> __ -> 'a1) -> SSAVS.t -> 'a1

    val memP : SSAVS.elt -> SSAVS.t -> reflect

    val equalP : SSAVS.t -> SSAVS.t -> reflect

    val subsetP : SSAVS.t -> SSAVS.t -> reflect

    val emptyP : SSAVS.t -> reflect

    val disjoint : SSAVS.t -> SSAVS.t -> bool

    val proper_subset : SSAVS.t -> SSAVS.t -> bool
   end

  type eunop =
  | Unot
  | Uneg
  | Uextr of int * int
  | Uhigh of int
  | Ulow of int
  | Uzext of int
  | Usext of int
  | Urepeat of int
  | Urotl of int
  | Urotr of int

  val eunop_rect :
    'a1 -> 'a1 -> (int -> int -> 'a1) -> (int -> 'a1) -> (int -> 'a1) -> (int
    -> 'a1) -> (int -> 'a1) -> (int -> 'a1) -> (int -> 'a1) -> (int -> 'a1)
    -> eunop -> 'a1

  val eunop_rec :
    'a1 -> 'a1 -> (int -> int -> 'a1) -> (int -> 'a1) -> (int -> 'a1) -> (int
    -> 'a1) -> (int -> 'a1) -> (int -> 'a1) -> (int -> 'a1) -> (int -> 'a1)
    -> eunop -> 'a1

  type ebinop =
  | Band
  | Bor
  | Bxor
  | Badd
  | Bsub
  | Bmul
  | Bdiv
  | Bmod
  | Bsdiv
  | Bsrem
  | Bsmod
  | Bshl
  | Blshr
  | Bashr
  | Bconcat
  | Bcomp

  val ebinop_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> ebinop -> 'a1

  val ebinop_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> ebinop -> 'a1

  type bbinop =
  | Beq
  | Bult
  | Bule
  | Bugt
  | Buge
  | Bslt
  | Bsle
  | Bsgt
  | Bsge
  | Buaddo
  | Busubo
  | Bumulo
  | Bsaddo
  | Bssubo
  | Bsmulo

  val bbinop_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bbinop -> 'a1

  val bbinop_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bbinop -> 'a1

  type exp =
  | Evar of SSAVarOrder.t
  | Econst of bits
  | Eunop of eunop * exp
  | Ebinop of ebinop * exp * exp
  | Eite of bexp * exp * exp
  and bexp =
  | Bfalse
  | Btrue
  | Bbinop of bbinop * exp * exp
  | Blneg of bexp
  | Bconj of bexp * bexp
  | Bdisj of bexp * bexp

  val exp_rect :
    (SSAVarOrder.t -> 'a1) -> (bits -> 'a1) -> (eunop -> exp -> 'a1 -> 'a1)
    -> (ebinop -> exp -> 'a1 -> exp -> 'a1 -> 'a1) -> (bexp -> exp -> 'a1 ->
    exp -> 'a1 -> 'a1) -> exp -> 'a1

  val exp_rec :
    (SSAVarOrder.t -> 'a1) -> (bits -> 'a1) -> (eunop -> exp -> 'a1 -> 'a1)
    -> (ebinop -> exp -> 'a1 -> exp -> 'a1 -> 'a1) -> (bexp -> exp -> 'a1 ->
    exp -> 'a1 -> 'a1) -> exp -> 'a1

  val bexp_rect :
    'a1 -> 'a1 -> (bbinop -> exp -> exp -> 'a1) -> (bexp -> 'a1 -> 'a1) ->
    (bexp -> 'a1 -> bexp -> 'a1 -> 'a1) -> (bexp -> 'a1 -> bexp -> 'a1 ->
    'a1) -> bexp -> 'a1

  val bexp_rec :
    'a1 -> 'a1 -> (bbinop -> exp -> exp -> 'a1) -> (bexp -> 'a1 -> 'a1) ->
    (bexp -> 'a1 -> bexp -> 'a1 -> 'a1) -> (bexp -> 'a1 -> bexp -> 'a1 ->
    'a1) -> bexp -> 'a1

  val eunop_eqn : eunop -> eunop -> bool

  val eunop_eqP : eunop -> eunop -> reflect

  val eunop_eqMixin : eunop Equality.mixin_of

  val eunop_eqType : Equality.coq_type

  val ebinop_eqn : ebinop -> ebinop -> bool

  val ebinop_eqP : ebinop -> ebinop -> reflect

  val ebinop_eqMixin : ebinop Equality.mixin_of

  val ebinop_eqType : Equality.coq_type

  val bbinop_eqn : bbinop -> bbinop -> bool

  val bbinop_eqP : bbinop -> bbinop -> reflect

  val bbinop_eqMixin : bbinop Equality.mixin_of

  val bbinop_eqType : Equality.coq_type

  val exp_eqn : exp -> exp -> bool

  val bexp_eqn : bexp -> bexp -> bool

  val exp_eqP : exp -> exp -> reflect

  val bexp_eqP : bexp -> bexp -> reflect

  val exp_eqMixin : exp Equality.mixin_of

  val bexp_eqMixin : bexp Equality.mixin_of

  val exp_eqType : Equality.coq_type

  val bexp_eqType : Equality.coq_type

  val qfbv_true : bexp

  val qfbv_false : bexp

  val qfbv_var : SSAVarOrder.t -> exp

  val qfbv_const : int -> int -> exp

  val qfbv_zero : int -> exp

  val qfbv_one : int -> exp

  val qfbv_not : exp -> exp

  val qfbv_neg : exp -> exp

  val qfbv_extr : int -> int -> exp -> exp

  val qfbv_high : int -> exp -> exp

  val qfbv_low : int -> exp -> exp

  val qfbv_zext : int -> exp -> exp

  val qfbv_sext : int -> exp -> exp

  val qfbv_and : exp -> exp -> exp

  val qfbv_or : exp -> exp -> exp

  val qfbv_xor : exp -> exp -> exp

  val qfbv_add : exp -> exp -> exp

  val qfbv_sub : exp -> exp -> exp

  val qfbv_mul : exp -> exp -> exp

  val qfbv_mod : exp -> exp -> exp

  val qfbv_srem : exp -> exp -> exp

  val qfbv_smod : exp -> exp -> exp

  val qfbv_shl : exp -> exp -> exp

  val qfbv_lshr : exp -> exp -> exp

  val qfbv_ashr : exp -> exp -> exp

  val qfbv_concat : exp -> exp -> exp

  val qfbv_eq : exp -> exp -> bexp

  val qfbv_ult : exp -> exp -> bexp

  val qfbv_ule : exp -> exp -> bexp

  val qfbv_ugt : exp -> exp -> bexp

  val qfbv_uge : exp -> exp -> bexp

  val qfbv_slt : exp -> exp -> bexp

  val qfbv_sle : exp -> exp -> bexp

  val qfbv_sgt : exp -> exp -> bexp

  val qfbv_sge : exp -> exp -> bexp

  val qfbv_uaddo : exp -> exp -> bexp

  val qfbv_usubo : exp -> exp -> bexp

  val qfbv_umulo : exp -> exp -> bexp

  val qfbv_saddo : exp -> exp -> bexp

  val qfbv_ssubo : exp -> exp -> bexp

  val qfbv_smulo : exp -> exp -> bexp

  val qfbv_lneg : bexp -> bexp

  val qfbv_conj : bexp -> bexp -> bexp

  val qfbv_disj : bexp -> bexp -> bexp

  val qfbv_ite : bexp -> exp -> exp -> exp

  val qfbv_imp : bexp -> bexp -> bexp

  val eunop_denote : eunop -> bits -> bits

  val ebinop_denote : ebinop -> bits -> bits -> bits

  val bbinop_denote : bbinop -> bits -> bits -> bool

  val eval_exp : exp -> SSAStore.t -> bits

  val eval_bexp : bexp -> SSAStore.t -> bool

  val vars_exp : exp -> SSAVS.t

  val vars_bexp : bexp -> SSAVS.t

  val vars_bexps : bexp list -> SSAVS.t

  val id_eunop : eunop -> int

  val eunop_ltn : eunop -> eunop -> bool

  val id_ebinop : ebinop -> int

  val ebinop_ltn : ebinop -> ebinop -> bool

  val id_bbinop : bbinop -> int

  val bbinop_ltn : bbinop -> bbinop -> bool

  val id_exp : exp -> int

  val id_bexp : bexp -> int

  val exp_ltn : exp -> exp -> bool

  val bexp_ltn : bexp -> bexp -> bool

  val exp_compare : exp -> exp -> exp OrderedType.coq_Compare

  val bexp_compare : bexp -> bexp -> bexp OrderedType.coq_Compare

  module ExpOrderMinimal :
   sig
    val t : Equality.coq_type

    val eqn : Equality.sort -> Equality.sort -> bool

    val ltn : Equality.sort -> Equality.sort -> bool

    val compare :
      Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare
   end

  module ExpOrder :
   sig
    val coq_T : Equality.coq_type

    type t = Equality.sort

    val ltn : t -> t -> bool

    val compare : t -> t -> t OrderedType.coq_Compare

    val eq_dec : t -> t -> bool
   end

  module BexpOrderMinimal :
   sig
    val t : Equality.coq_type

    val eqn : Equality.sort -> Equality.sort -> bool

    val ltn : Equality.sort -> Equality.sort -> bool

    val compare :
      Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare
   end

  module BexpOrder :
   sig
    val coq_T : Equality.coq_type

    type t = Equality.sort

    val ltn : t -> t -> bool

    val compare : t -> t -> t OrderedType.coq_Compare

    val eq_dec : t -> t -> bool
   end

  val len_exp : exp -> int

  val len_bexp : bexp -> int

  val subee : exp -> exp -> bool

  val subeb : exp -> bexp -> bool

  val subbe : bexp -> exp -> bool

  val subbb : bexp -> bexp -> bool

  module TELemmas :
   sig
    module F :
     sig
      val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

      val coq_In_dec : 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key -> bool
     end

    module OP :
     sig
      module ME :
       sig
        module TO :
         sig
          type t = TypEnv.SSATE.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

        val lt_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

        val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool
       end

      module O :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = TypEnv.SSATE.SE.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

          val lt_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

          val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool
         end
       end

      module P :
       sig
        module F :
         sig
          val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

          val coq_In_dec : 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key -> bool
         end

        val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

        val of_list : (TypEnv.SSATE.key * 'a1) list -> 'a1 TypEnv.SSATE.t

        val to_list : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1) list

        val fold_rec :
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1
          TypEnv.SSATE.t -> ('a1 TypEnv.SSATE.t -> __ -> 'a3) ->
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_bis :
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1
          TypEnv.SSATE.t -> ('a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a2
          -> __ -> 'a3 -> 'a3) -> 'a3 -> (TypEnv.SSATE.key -> 'a1 -> 'a2 ->
          'a1 TypEnv.SSATE.t -> __ -> __ -> 'a3 -> 'a3) -> 'a3

        val fold_rec_nodep :
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1
          TypEnv.SSATE.t -> 'a3 -> (TypEnv.SSATE.key -> 'a1 -> 'a2 -> __ ->
          'a3 -> 'a3) -> 'a3

        val fold_rec_weak :
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1
          TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a2 -> __ -> 'a3 -> 'a3) ->
          'a3 -> (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.SSATE.t -> __
          -> 'a3 -> 'a3) -> 'a1 TypEnv.SSATE.t -> 'a3

        val fold_rel :
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> (TypEnv.SSATE.key -> 'a1
          -> 'a3 -> 'a3) -> 'a2 -> 'a3 -> 'a1 TypEnv.SSATE.t -> 'a4 ->
          (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

        val map_induction :
          ('a1 TypEnv.SSATE.t -> __ -> 'a2) -> ('a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t -> 'a2 -> TypEnv.SSATE.key -> 'a1 -> __ -> __ ->
          'a2) -> 'a1 TypEnv.SSATE.t -> 'a2

        val map_induction_bis :
          ('a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> __ -> 'a2 -> 'a2) ->
          'a2 -> (TypEnv.SSATE.key -> 'a1 -> 'a1 TypEnv.SSATE.t -> __ -> 'a2
          -> 'a2) -> 'a1 TypEnv.SSATE.t -> 'a2

        val cardinal_inv_2 :
          'a1 TypEnv.SSATE.t -> int -> (TypEnv.SSATE.key * 'a1)

        val cardinal_inv_2b : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1)

        val filter :
          (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t

        val for_all :
          (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

        val exists_ :
          (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

        val partition :
          (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t * 'a1 TypEnv.SSATE.t

        val update :
          'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

        val restrict :
          'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

        val diff :
          'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

        val coq_Partition_In :
          'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t ->
          TypEnv.SSATE.key -> bool

        val update_dec :
          'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key -> 'a1
          -> bool

        val filter_dom :
          (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t

        val filter_range :
          ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

        val for_all_dom :
          (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> bool

        val for_all_range : ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

        val exists_dom :
          (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> bool

        val exists_range : ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

        val partition_dom :
          (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
          TypEnv.SSATE.t * 'a1 TypEnv.SSATE.t

        val partition_range :
          ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t * 'a1
          TypEnv.SSATE.t
       end

      val gtb : (TypEnv.SSATE.key * 'a1) -> (TypEnv.SSATE.key * 'a1) -> bool

      val leb : (TypEnv.SSATE.key * 'a1) -> (TypEnv.SSATE.key * 'a1) -> bool

      val elements_lt :
        (TypEnv.SSATE.key * 'a1) -> 'a1 TypEnv.SSATE.t ->
        (TypEnv.SSATE.key * 'a1) list

      val elements_ge :
        (TypEnv.SSATE.key * 'a1) -> 'a1 TypEnv.SSATE.t ->
        (TypEnv.SSATE.key * 'a1) list

      val max_elt_aux :
        (TypEnv.SSATE.key * 'a1) list -> (TypEnv.SSATE.key * 'a1) option

      val max_elt : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1) option

      val min_elt : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1) option

      val map_induction_max :
        ('a1 TypEnv.SSATE.t -> __ -> 'a2) -> ('a1 TypEnv.SSATE.t -> 'a1
        TypEnv.SSATE.t -> 'a2 -> TypEnv.SSATE.SE.t -> 'a1 -> __ -> __ -> 'a2)
        -> 'a1 TypEnv.SSATE.t -> 'a2

      val map_induction_min :
        ('a1 TypEnv.SSATE.t -> __ -> 'a2) -> ('a1 TypEnv.SSATE.t -> 'a1
        TypEnv.SSATE.t -> 'a2 -> TypEnv.SSATE.SE.t -> 'a1 -> __ -> __ -> 'a2)
        -> 'a1 TypEnv.SSATE.t -> 'a2
     end

    val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

    val coq_In_dec : 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key -> bool

    module ME :
     sig
      module TO :
       sig
        type t = TypEnv.SSATE.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

      val lt_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

      val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool
     end

    module O :
     sig
      module MO :
       sig
        module TO :
         sig
          type t = TypEnv.SSATE.SE.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

        val lt_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

        val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool
       end
     end

    module P :
     sig
      module F :
       sig
        val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

        val coq_In_dec : 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key -> bool
       end

      val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1 * 'a2) -> 'a3

      val of_list : (TypEnv.SSATE.key * 'a1) list -> 'a1 TypEnv.SSATE.t

      val to_list : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1) list

      val fold_rec :
        (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.SSATE.t
        -> ('a1 TypEnv.SSATE.t -> __ -> 'a3) -> (TypEnv.SSATE.key -> 'a1 ->
        'a2 -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> __ -> __ -> __ ->
        'a3 -> 'a3) -> 'a3

      val fold_rec_bis :
        (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.SSATE.t
        -> ('a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a2 -> __ -> 'a3 ->
        'a3) -> 'a3 -> (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.SSATE.t
        -> __ -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_nodep :
        (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 TypEnv.SSATE.t
        -> 'a3 -> (TypEnv.SSATE.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val fold_rec_weak :
        (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 TypEnv.SSATE.t
        -> 'a1 TypEnv.SSATE.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
        (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a1 TypEnv.SSATE.t -> __ -> 'a3 ->
        'a3) -> 'a1 TypEnv.SSATE.t -> 'a3

      val fold_rel :
        (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a2) -> (TypEnv.SSATE.key -> 'a1
        -> 'a3 -> 'a3) -> 'a2 -> 'a3 -> 'a1 TypEnv.SSATE.t -> 'a4 ->
        (TypEnv.SSATE.key -> 'a1 -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

      val map_induction :
        ('a1 TypEnv.SSATE.t -> __ -> 'a2) -> ('a1 TypEnv.SSATE.t -> 'a1
        TypEnv.SSATE.t -> 'a2 -> TypEnv.SSATE.key -> 'a1 -> __ -> __ -> 'a2)
        -> 'a1 TypEnv.SSATE.t -> 'a2

      val map_induction_bis :
        ('a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> __ -> 'a2 -> 'a2) -> 'a2
        -> (TypEnv.SSATE.key -> 'a1 -> 'a1 TypEnv.SSATE.t -> __ -> 'a2 ->
        'a2) -> 'a1 TypEnv.SSATE.t -> 'a2

      val cardinal_inv_2 :
        'a1 TypEnv.SSATE.t -> int -> (TypEnv.SSATE.key * 'a1)

      val cardinal_inv_2b : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1)

      val filter :
        (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
        TypEnv.SSATE.t

      val for_all :
        (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

      val exists_ :
        (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

      val partition :
        (TypEnv.SSATE.key -> 'a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
        TypEnv.SSATE.t * 'a1 TypEnv.SSATE.t

      val update :
        'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

      val restrict :
        'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

      val diff :
        'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

      val coq_Partition_In :
        'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t ->
        TypEnv.SSATE.key -> bool

      val update_dec :
        'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key -> 'a1
        -> bool

      val filter_dom :
        (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

      val filter_range :
        ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t

      val for_all_dom :
        (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> bool

      val for_all_range : ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

      val exists_dom :
        (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> bool

      val exists_range : ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> bool

      val partition_dom :
        (TypEnv.SSATE.key -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1
        TypEnv.SSATE.t * 'a1 TypEnv.SSATE.t

      val partition_range :
        ('a1 -> bool) -> 'a1 TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t * 'a1
        TypEnv.SSATE.t
     end

    val gtb : (TypEnv.SSATE.key * 'a1) -> (TypEnv.SSATE.key * 'a1) -> bool

    val leb : (TypEnv.SSATE.key * 'a1) -> (TypEnv.SSATE.key * 'a1) -> bool

    val elements_lt :
      (TypEnv.SSATE.key * 'a1) -> 'a1 TypEnv.SSATE.t ->
      (TypEnv.SSATE.key * 'a1) list

    val elements_ge :
      (TypEnv.SSATE.key * 'a1) -> 'a1 TypEnv.SSATE.t ->
      (TypEnv.SSATE.key * 'a1) list

    val max_elt_aux :
      (TypEnv.SSATE.key * 'a1) list -> (TypEnv.SSATE.key * 'a1) option

    val max_elt : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1) option

    val min_elt : 'a1 TypEnv.SSATE.t -> (TypEnv.SSATE.key * 'a1) option

    val map_induction_max :
      ('a1 TypEnv.SSATE.t -> __ -> 'a2) -> ('a1 TypEnv.SSATE.t -> 'a1
      TypEnv.SSATE.t -> 'a2 -> TypEnv.SSATE.SE.t -> 'a1 -> __ -> __ -> 'a2)
      -> 'a1 TypEnv.SSATE.t -> 'a2

    val map_induction_min :
      ('a1 TypEnv.SSATE.t -> __ -> 'a2) -> ('a1 TypEnv.SSATE.t -> 'a1
      TypEnv.SSATE.t -> 'a2 -> TypEnv.SSATE.SE.t -> 'a1 -> __ -> __ -> 'a2)
      -> 'a1 TypEnv.SSATE.t -> 'a2

    val memP : TypEnv.SSATE.key -> 'a1 TypEnv.SSATE.t -> reflect

    val split :
      ('a1 * 'a2) TypEnv.SSATE.t -> 'a1 TypEnv.SSATE.t * 'a2 TypEnv.SSATE.t

    module EFacts :
     sig
      module TO :
       sig
        type t = TypEnv.SSATE.SE.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

      val lt_dec : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool

      val eqb : TypEnv.SSATE.SE.t -> TypEnv.SSATE.SE.t -> bool
     end

    val max_opt :
      TypEnv.SSATE.key -> TypEnv.SSATE.key option -> TypEnv.SSATE.key

    val max_key_elements :
      (TypEnv.SSATE.key * 'a1) list -> TypEnv.SSATE.key option

    val max_key : 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key option

    val min_opt :
      TypEnv.SSATE.key -> TypEnv.SSATE.key option -> TypEnv.SSATE.key

    val min_key_elements :
      (TypEnv.SSATE.key * 'a1) list -> TypEnv.SSATE.key option

    val min_key : 'a1 TypEnv.SSATE.t -> TypEnv.SSATE.key option
   end

  val exp_size : exp -> TypEnv.SSATE.env -> int

  val well_formed_exp : exp -> TypEnv.SSATE.env -> bool

  val well_formed_bexp : bexp -> TypEnv.SSATE.env -> bool

  val well_formed_bexps : bexp list -> TypEnv.SSATE.env -> bool

  val split_conj : bexp -> bexp list

  val qfbv_conjs : bexp list -> bexp

  val qfbv_conjs_rec : bexp -> bexp list -> bexp

  val qfbv_conjs_la : bexp list -> bexp

  val eval_bexps : bexp list -> SSAStore.t -> bool

  val simplify_bexp : bexp -> bexp

  val bexp_is_implied : bexp -> bool

  val simplify_bexp2 : bexp -> bexp
 end

val eunop_eqType : Equality.coq_type

val ebinop_eqType : Equality.coq_type

val bbinop_eqType : Equality.coq_type
