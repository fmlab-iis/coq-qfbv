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
let __ = let rec f _ = Obj.repr f in Obj.repr f

module MakeQFBV =
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
 struct
  module VSLemmas = FSetLemmas(VS)

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

  (** val eunop_rect :
      'a1 -> 'a1 -> (int -> int -> 'a1) -> (int -> 'a1) -> (int -> 'a1) ->
      (int -> 'a1) -> (int -> 'a1) -> (int -> 'a1) -> (int -> 'a1) -> (int ->
      'a1) -> eunop -> 'a1 **)

  let eunop_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 = function
  | Unot -> f
  | Uneg -> f0
  | Uextr (n, n0) -> f1 n n0
  | Uhigh n -> f2 n
  | Ulow n -> f3 n
  | Uzext n -> f4 n
  | Usext n -> f5 n
  | Urepeat n -> f6 n
  | Urotl n -> f7 n
  | Urotr n -> f8 n

  (** val eunop_rec :
      'a1 -> 'a1 -> (int -> int -> 'a1) -> (int -> 'a1) -> (int -> 'a1) ->
      (int -> 'a1) -> (int -> 'a1) -> (int -> 'a1) -> (int -> 'a1) -> (int ->
      'a1) -> eunop -> 'a1 **)

  let eunop_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 = function
  | Unot -> f
  | Uneg -> f0
  | Uextr (n, n0) -> f1 n n0
  | Uhigh n -> f2 n
  | Ulow n -> f3 n
  | Uzext n -> f4 n
  | Usext n -> f5 n
  | Urepeat n -> f6 n
  | Urotl n -> f7 n
  | Urotr n -> f8 n

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

  (** val ebinop_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> ebinop -> 'a1 **)

  let ebinop_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 = function
  | Band -> f
  | Bor -> f0
  | Bxor -> f1
  | Badd -> f2
  | Bsub -> f3
  | Bmul -> f4
  | Bdiv -> f5
  | Bmod -> f6
  | Bsdiv -> f7
  | Bsrem -> f8
  | Bsmod -> f9
  | Bshl -> f10
  | Blshr -> f11
  | Bashr -> f12
  | Bconcat -> f13
  | Bcomp -> f14

  (** val ebinop_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> ebinop -> 'a1 **)

  let ebinop_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 = function
  | Band -> f
  | Bor -> f0
  | Bxor -> f1
  | Badd -> f2
  | Bsub -> f3
  | Bmul -> f4
  | Bdiv -> f5
  | Bmod -> f6
  | Bsdiv -> f7
  | Bsrem -> f8
  | Bsmod -> f9
  | Bshl -> f10
  | Blshr -> f11
  | Bashr -> f12
  | Bconcat -> f13
  | Bcomp -> f14

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

  (** val bbinop_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bbinop -> 'a1 **)

  let bbinop_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 = function
  | Beq -> f
  | Bult -> f0
  | Bule -> f1
  | Bugt -> f2
  | Buge -> f3
  | Bslt -> f4
  | Bsle -> f5
  | Bsgt -> f6
  | Bsge -> f7
  | Buaddo -> f8
  | Busubo -> f9
  | Bumulo -> f10
  | Bsaddo -> f11
  | Bssubo -> f12
  | Bsmulo -> f13

  (** val bbinop_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bbinop -> 'a1 **)

  let bbinop_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 = function
  | Beq -> f
  | Bult -> f0
  | Bule -> f1
  | Bugt -> f2
  | Buge -> f3
  | Bslt -> f4
  | Bsle -> f5
  | Bsgt -> f6
  | Bsge -> f7
  | Buaddo -> f8
  | Busubo -> f9
  | Bumulo -> f10
  | Bsaddo -> f11
  | Bssubo -> f12
  | Bsmulo -> f13

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

  (** val exp_rect :
      (V.t -> 'a1) -> (bits -> 'a1) -> (eunop -> exp -> 'a1 -> 'a1) ->
      (ebinop -> exp -> 'a1 -> exp -> 'a1 -> 'a1) -> (bexp -> exp -> 'a1 ->
      exp -> 'a1 -> 'a1) -> exp -> 'a1 **)

  let rec exp_rect f f0 f1 f2 f3 = function
  | Evar t0 -> f t0
  | Econst b -> f0 b
  | Eunop (e0, e1) -> f1 e0 e1 (exp_rect f f0 f1 f2 f3 e1)
  | Ebinop (e0, e1, e2) ->
    f2 e0 e1 (exp_rect f f0 f1 f2 f3 e1) e2 (exp_rect f f0 f1 f2 f3 e2)
  | Eite (b, e0, e1) ->
    f3 b e0 (exp_rect f f0 f1 f2 f3 e0) e1 (exp_rect f f0 f1 f2 f3 e1)

  (** val exp_rec :
      (V.t -> 'a1) -> (bits -> 'a1) -> (eunop -> exp -> 'a1 -> 'a1) ->
      (ebinop -> exp -> 'a1 -> exp -> 'a1 -> 'a1) -> (bexp -> exp -> 'a1 ->
      exp -> 'a1 -> 'a1) -> exp -> 'a1 **)

  let rec exp_rec f f0 f1 f2 f3 = function
  | Evar t0 -> f t0
  | Econst b -> f0 b
  | Eunop (e0, e1) -> f1 e0 e1 (exp_rec f f0 f1 f2 f3 e1)
  | Ebinop (e0, e1, e2) ->
    f2 e0 e1 (exp_rec f f0 f1 f2 f3 e1) e2 (exp_rec f f0 f1 f2 f3 e2)
  | Eite (b, e0, e1) ->
    f3 b e0 (exp_rec f f0 f1 f2 f3 e0) e1 (exp_rec f f0 f1 f2 f3 e1)

  (** val bexp_rect :
      'a1 -> 'a1 -> (bbinop -> exp -> exp -> 'a1) -> (bexp -> 'a1 -> 'a1) ->
      (bexp -> 'a1 -> bexp -> 'a1 -> 'a1) -> (bexp -> 'a1 -> bexp -> 'a1 ->
      'a1) -> bexp -> 'a1 **)

  let rec bexp_rect f f0 f1 f2 f3 f4 = function
  | Bfalse -> f
  | Btrue -> f0
  | Bbinop (b0, e, e0) -> f1 b0 e e0
  | Blneg b0 -> f2 b0 (bexp_rect f f0 f1 f2 f3 f4 b0)
  | Bconj (b0, b1) ->
    f3 b0 (bexp_rect f f0 f1 f2 f3 f4 b0) b1 (bexp_rect f f0 f1 f2 f3 f4 b1)
  | Bdisj (b0, b1) ->
    f4 b0 (bexp_rect f f0 f1 f2 f3 f4 b0) b1 (bexp_rect f f0 f1 f2 f3 f4 b1)

  (** val bexp_rec :
      'a1 -> 'a1 -> (bbinop -> exp -> exp -> 'a1) -> (bexp -> 'a1 -> 'a1) ->
      (bexp -> 'a1 -> bexp -> 'a1 -> 'a1) -> (bexp -> 'a1 -> bexp -> 'a1 ->
      'a1) -> bexp -> 'a1 **)

  let rec bexp_rec f f0 f1 f2 f3 f4 = function
  | Bfalse -> f
  | Btrue -> f0
  | Bbinop (b0, e, e0) -> f1 b0 e e0
  | Blneg b0 -> f2 b0 (bexp_rec f f0 f1 f2 f3 f4 b0)
  | Bconj (b0, b1) ->
    f3 b0 (bexp_rec f f0 f1 f2 f3 f4 b0) b1 (bexp_rec f f0 f1 f2 f3 f4 b1)
  | Bdisj (b0, b1) ->
    f4 b0 (bexp_rec f f0 f1 f2 f3 f4 b0) b1 (bexp_rec f f0 f1 f2 f3 f4 b1)

  (** val eunop_eqn : eunop -> eunop -> bool **)

  let eunop_eqn o1 o2 =
    match o1 with
    | Unot -> (match o2 with
               | Unot -> true
               | _ -> false)
    | Uneg -> (match o2 with
               | Uneg -> true
               | _ -> false)
    | Uextr (i1, j1) ->
      (match o2 with
       | Uextr (i2, j2) ->
         (&&) (eq_op nat_eqType (Obj.magic i1) (Obj.magic i2))
           (eq_op nat_eqType (Obj.magic j1) (Obj.magic j2))
       | _ -> false)
    | Uhigh n1 ->
      (match o2 with
       | Uhigh n2 -> eq_op nat_eqType (Obj.magic n1) (Obj.magic n2)
       | _ -> false)
    | Ulow n1 ->
      (match o2 with
       | Ulow n2 -> eq_op nat_eqType (Obj.magic n1) (Obj.magic n2)
       | _ -> false)
    | Uzext n1 ->
      (match o2 with
       | Uzext n2 -> eq_op nat_eqType (Obj.magic n1) (Obj.magic n2)
       | _ -> false)
    | Usext n1 ->
      (match o2 with
       | Usext n2 -> eq_op nat_eqType (Obj.magic n1) (Obj.magic n2)
       | _ -> false)
    | Urepeat n1 ->
      (match o2 with
       | Urepeat n2 -> eq_op nat_eqType (Obj.magic n1) (Obj.magic n2)
       | _ -> false)
    | Urotl n1 ->
      (match o2 with
       | Urotl n2 -> eq_op nat_eqType (Obj.magic n1) (Obj.magic n2)
       | _ -> false)
    | Urotr n1 ->
      (match o2 with
       | Urotr n2 -> eq_op nat_eqType (Obj.magic n1) (Obj.magic n2)
       | _ -> false)

  (** val eunop_eqP : eunop -> eunop -> reflect **)

  let eunop_eqP o1 o2 =
    let _evar_0_ = fun _ -> ReflectT in
    let _evar_0_0 = fun _ -> ReflectF in
    if eunop_eqn o1 o2 then _evar_0_ __ else _evar_0_0 __

  (** val eunop_eqMixin : eunop Equality.mixin_of **)

  let eunop_eqMixin =
    { Equality.op = eunop_eqn; Equality.mixin_of__1 = eunop_eqP }

  (** val eunop_eqType : Equality.coq_type **)

  let eunop_eqType =
    Obj.magic eunop_eqMixin

  (** val ebinop_eqn : ebinop -> ebinop -> bool **)

  let ebinop_eqn o1 o2 =
    match o1 with
    | Band -> (match o2 with
               | Band -> true
               | _ -> false)
    | Bor -> (match o2 with
              | Bor -> true
              | _ -> false)
    | Bxor -> (match o2 with
               | Bxor -> true
               | _ -> false)
    | Badd -> (match o2 with
               | Badd -> true
               | _ -> false)
    | Bsub -> (match o2 with
               | Bsub -> true
               | _ -> false)
    | Bmul -> (match o2 with
               | Bmul -> true
               | _ -> false)
    | Bdiv -> (match o2 with
               | Bdiv -> true
               | _ -> false)
    | Bmod -> (match o2 with
               | Bmod -> true
               | _ -> false)
    | Bsdiv -> (match o2 with
                | Bsdiv -> true
                | _ -> false)
    | Bsrem -> (match o2 with
                | Bsrem -> true
                | _ -> false)
    | Bsmod -> (match o2 with
                | Bsmod -> true
                | _ -> false)
    | Bshl -> (match o2 with
               | Bshl -> true
               | _ -> false)
    | Blshr -> (match o2 with
                | Blshr -> true
                | _ -> false)
    | Bashr -> (match o2 with
                | Bashr -> true
                | _ -> false)
    | Bconcat -> (match o2 with
                  | Bconcat -> true
                  | _ -> false)
    | Bcomp -> (match o2 with
                | Bcomp -> true
                | _ -> false)

  (** val ebinop_eqP : ebinop -> ebinop -> reflect **)

  let ebinop_eqP o1 o2 =
    let _evar_0_ = fun _ -> ReflectT in
    let _evar_0_0 = fun _ -> ReflectF in
    if ebinop_eqn o1 o2 then _evar_0_ __ else _evar_0_0 __

  (** val ebinop_eqMixin : ebinop Equality.mixin_of **)

  let ebinop_eqMixin =
    { Equality.op = ebinop_eqn; Equality.mixin_of__1 = ebinop_eqP }

  (** val ebinop_eqType : Equality.coq_type **)

  let ebinop_eqType =
    Obj.magic ebinop_eqMixin

  (** val bbinop_eqn : bbinop -> bbinop -> bool **)

  let bbinop_eqn o1 o2 =
    match o1 with
    | Beq -> (match o2 with
              | Beq -> true
              | _ -> false)
    | Bult -> (match o2 with
               | Bult -> true
               | _ -> false)
    | Bule -> (match o2 with
               | Bule -> true
               | _ -> false)
    | Bugt -> (match o2 with
               | Bugt -> true
               | _ -> false)
    | Buge -> (match o2 with
               | Buge -> true
               | _ -> false)
    | Bslt -> (match o2 with
               | Bslt -> true
               | _ -> false)
    | Bsle -> (match o2 with
               | Bsle -> true
               | _ -> false)
    | Bsgt -> (match o2 with
               | Bsgt -> true
               | _ -> false)
    | Bsge -> (match o2 with
               | Bsge -> true
               | _ -> false)
    | Buaddo -> (match o2 with
                 | Buaddo -> true
                 | _ -> false)
    | Busubo -> (match o2 with
                 | Busubo -> true
                 | _ -> false)
    | Bumulo -> (match o2 with
                 | Bumulo -> true
                 | _ -> false)
    | Bsaddo -> (match o2 with
                 | Bsaddo -> true
                 | _ -> false)
    | Bssubo -> (match o2 with
                 | Bssubo -> true
                 | _ -> false)
    | Bsmulo -> (match o2 with
                 | Bsmulo -> true
                 | _ -> false)

  (** val bbinop_eqP : bbinop -> bbinop -> reflect **)

  let bbinop_eqP o1 o2 =
    let _evar_0_ = fun _ -> ReflectT in
    let _evar_0_0 = fun _ -> ReflectF in
    if bbinop_eqn o1 o2 then _evar_0_ __ else _evar_0_0 __

  (** val bbinop_eqMixin : bbinop Equality.mixin_of **)

  let bbinop_eqMixin =
    { Equality.op = bbinop_eqn; Equality.mixin_of__1 = bbinop_eqP }

  (** val bbinop_eqType : Equality.coq_type **)

  let bbinop_eqType =
    Obj.magic bbinop_eqMixin

  (** val exp_eqn : exp -> exp -> bool **)

  let rec exp_eqn e1 e2 =
    match e1 with
    | Evar v1 -> (match e2 with
                  | Evar v2 -> eq_op V.coq_T v1 v2
                  | _ -> false)
    | Econst n1 ->
      (match e2 with
       | Econst n2 -> eq_op bitseq_eqType (Obj.magic n1) (Obj.magic n2)
       | _ -> false)
    | Eunop (op1, e3) ->
      (match e2 with
       | Eunop (op2, e4) ->
         (&&) (eq_op eunop_eqType (Obj.magic op1) (Obj.magic op2))
           (exp_eqn e3 e4)
       | _ -> false)
    | Ebinop (op1, e3, e4) ->
      (match e2 with
       | Ebinop (op2, e5, e6) ->
         (&&)
           ((&&) (eq_op ebinop_eqType (Obj.magic op1) (Obj.magic op2))
             (exp_eqn e3 e5)) (exp_eqn e4 e6)
       | _ -> false)
    | Eite (c1, e3, e4) ->
      (match e2 with
       | Eite (c2, e5, e6) ->
         (&&) ((&&) (bexp_eqn c1 c2) (exp_eqn e3 e5)) (exp_eqn e4 e6)
       | _ -> false)

  (** val bexp_eqn : bexp -> bexp -> bool **)

  and bexp_eqn e1 e2 =
    match e1 with
    | Bfalse -> (match e2 with
                 | Bfalse -> true
                 | _ -> false)
    | Btrue -> (match e2 with
                | Btrue -> true
                | _ -> false)
    | Bbinop (op1, e3, e4) ->
      (match e2 with
       | Bbinop (op2, e5, e6) ->
         (&&)
           ((&&) (eq_op bbinop_eqType (Obj.magic op1) (Obj.magic op2))
             (exp_eqn e3 e5)) (exp_eqn e4 e6)
       | _ -> false)
    | Blneg e3 -> (match e2 with
                   | Blneg e4 -> bexp_eqn e3 e4
                   | _ -> false)
    | Bconj (e3, e4) ->
      (match e2 with
       | Bconj (e5, e6) -> (&&) (bexp_eqn e3 e5) (bexp_eqn e4 e6)
       | _ -> false)
    | Bdisj (e3, e4) ->
      (match e2 with
       | Bdisj (e5, e6) -> (&&) (bexp_eqn e3 e5) (bexp_eqn e4 e6)
       | _ -> false)

  (** val exp_eqP : exp -> exp -> reflect **)

  let exp_eqP e1 e2 =
    let _evar_0_ = fun _ -> ReflectT in
    let _evar_0_0 = fun _ -> ReflectF in
    if exp_eqn e1 e2 then _evar_0_ __ else _evar_0_0 __

  (** val bexp_eqP : bexp -> bexp -> reflect **)

  let bexp_eqP e1 e2 =
    let _evar_0_ = fun _ -> ReflectT in
    let _evar_0_0 = fun _ -> ReflectF in
    if bexp_eqn e1 e2 then _evar_0_ __ else _evar_0_0 __

  (** val exp_eqMixin : exp Equality.mixin_of **)

  let exp_eqMixin =
    { Equality.op = exp_eqn; Equality.mixin_of__1 = exp_eqP }

  (** val bexp_eqMixin : bexp Equality.mixin_of **)

  let bexp_eqMixin =
    { Equality.op = bexp_eqn; Equality.mixin_of__1 = bexp_eqP }

  (** val exp_eqType : Equality.coq_type **)

  let exp_eqType =
    Obj.magic exp_eqMixin

  (** val bexp_eqType : Equality.coq_type **)

  let bexp_eqType =
    Obj.magic bexp_eqMixin

  (** val qfbv_true : bexp **)

  let qfbv_true =
    Btrue

  (** val qfbv_false : bexp **)

  let qfbv_false =
    Bfalse

  (** val qfbv_var : V.t -> exp **)

  let qfbv_var v =
    Evar v

  (** val qfbv_const : int -> int -> exp **)

  let qfbv_const w n =
    Econst (from_nat w n)

  (** val qfbv_zero : int -> exp **)

  let qfbv_zero w =
    Econst (from_nat w 0)

  (** val qfbv_one : int -> exp **)

  let qfbv_one w =
    Econst (from_nat w (Pervasives.succ 0))

  (** val qfbv_not : exp -> exp **)

  let qfbv_not qe =
    Eunop (Unot, qe)

  (** val qfbv_neg : exp -> exp **)

  let qfbv_neg qe =
    Eunop (Uneg, qe)

  (** val qfbv_extr : int -> int -> exp -> exp **)

  let qfbv_extr i j qe =
    Eunop ((Uextr (i, j)), qe)

  (** val qfbv_high : int -> exp -> exp **)

  let qfbv_high n qe =
    Eunop ((Uhigh n), qe)

  (** val qfbv_low : int -> exp -> exp **)

  let qfbv_low n qe =
    Eunop ((Ulow n), qe)

  (** val qfbv_zext : int -> exp -> exp **)

  let qfbv_zext n qe =
    Eunop ((Uzext n), qe)

  (** val qfbv_sext : int -> exp -> exp **)

  let qfbv_sext n qe =
    Eunop ((Usext n), qe)

  (** val qfbv_and : exp -> exp -> exp **)

  let qfbv_and qe0 qe1 =
    Ebinop (Band, qe0, qe1)

  (** val qfbv_or : exp -> exp -> exp **)

  let qfbv_or qe0 qe1 =
    Ebinop (Bor, qe0, qe1)

  (** val qfbv_xor : exp -> exp -> exp **)

  let qfbv_xor qe0 qe1 =
    Ebinop (Bxor, qe0, qe1)

  (** val qfbv_add : exp -> exp -> exp **)

  let qfbv_add qe0 qe1 =
    Ebinop (Badd, qe0, qe1)

  (** val qfbv_sub : exp -> exp -> exp **)

  let qfbv_sub qe0 qe1 =
    Ebinop (Bsub, qe0, qe1)

  (** val qfbv_mul : exp -> exp -> exp **)

  let qfbv_mul qe0 qe1 =
    Ebinop (Bmul, qe0, qe1)

  (** val qfbv_mod : exp -> exp -> exp **)

  let qfbv_mod qe0 qe1 =
    Ebinop (Bmod, qe0, qe1)

  (** val qfbv_srem : exp -> exp -> exp **)

  let qfbv_srem qe0 qe1 =
    Ebinop (Bsrem, qe0, qe1)

  (** val qfbv_smod : exp -> exp -> exp **)

  let qfbv_smod qe0 qe1 =
    Ebinop (Bsmod, qe0, qe1)

  (** val qfbv_shl : exp -> exp -> exp **)

  let qfbv_shl qe0 qe1 =
    Ebinop (Bshl, qe0, qe1)

  (** val qfbv_lshr : exp -> exp -> exp **)

  let qfbv_lshr qe0 qe1 =
    Ebinop (Blshr, qe0, qe1)

  (** val qfbv_ashr : exp -> exp -> exp **)

  let qfbv_ashr qe0 qe1 =
    Ebinop (Bashr, qe0, qe1)

  (** val qfbv_concat : exp -> exp -> exp **)

  let qfbv_concat qe0 qe1 =
    Ebinop (Bconcat, qe0, qe1)

  (** val qfbv_eq : exp -> exp -> bexp **)

  let qfbv_eq qe0 qe1 =
    Bbinop (Beq, qe0, qe1)

  (** val qfbv_ult : exp -> exp -> bexp **)

  let qfbv_ult qe0 qe1 =
    Bbinop (Bult, qe0, qe1)

  (** val qfbv_ule : exp -> exp -> bexp **)

  let qfbv_ule qe0 qe1 =
    Bbinop (Bule, qe0, qe1)

  (** val qfbv_ugt : exp -> exp -> bexp **)

  let qfbv_ugt qe0 qe1 =
    Bbinop (Bugt, qe0, qe1)

  (** val qfbv_uge : exp -> exp -> bexp **)

  let qfbv_uge qe0 qe1 =
    Bbinop (Buge, qe0, qe1)

  (** val qfbv_slt : exp -> exp -> bexp **)

  let qfbv_slt qe0 qe1 =
    Bbinop (Bslt, qe0, qe1)

  (** val qfbv_sle : exp -> exp -> bexp **)

  let qfbv_sle qe0 qe1 =
    Bbinop (Bsle, qe0, qe1)

  (** val qfbv_sgt : exp -> exp -> bexp **)

  let qfbv_sgt qe0 qe1 =
    Bbinop (Bsgt, qe0, qe1)

  (** val qfbv_sge : exp -> exp -> bexp **)

  let qfbv_sge qe0 qe1 =
    Bbinop (Bsge, qe0, qe1)

  (** val qfbv_uaddo : exp -> exp -> bexp **)

  let qfbv_uaddo qe0 qe1 =
    Bbinop (Buaddo, qe0, qe1)

  (** val qfbv_usubo : exp -> exp -> bexp **)

  let qfbv_usubo qe0 qe1 =
    Bbinop (Busubo, qe0, qe1)

  (** val qfbv_umulo : exp -> exp -> bexp **)

  let qfbv_umulo qe0 qe1 =
    Bbinop (Bumulo, qe0, qe1)

  (** val qfbv_saddo : exp -> exp -> bexp **)

  let qfbv_saddo qe0 qe1 =
    Bbinop (Bsaddo, qe0, qe1)

  (** val qfbv_ssubo : exp -> exp -> bexp **)

  let qfbv_ssubo qe0 qe1 =
    Bbinop (Bssubo, qe0, qe1)

  (** val qfbv_smulo : exp -> exp -> bexp **)

  let qfbv_smulo qe0 qe1 =
    Bbinop (Bsmulo, qe0, qe1)

  (** val qfbv_lneg : bexp -> bexp **)

  let qfbv_lneg qb =
    Blneg qb

  (** val qfbv_conj : bexp -> bexp -> bexp **)

  let qfbv_conj qb0 qb1 =
    Bconj (qb0, qb1)

  (** val qfbv_disj : bexp -> bexp -> bexp **)

  let qfbv_disj qb0 qb1 =
    Bdisj (qb0, qb1)

  (** val qfbv_ite : bexp -> exp -> exp -> exp **)

  let qfbv_ite qb qe0 qe1 =
    Eite (qb, qe0, qe1)

  (** val qfbv_imp : bexp -> bexp -> bexp **)

  let qfbv_imp f g =
    qfbv_disj (qfbv_lneg f) g

  (** val eunop_denote : eunop -> bits -> bits **)

  let eunop_denote = function
  | Unot -> invB
  | Uneg -> negB
  | Uextr (i, j) -> extract i j
  | Uhigh n -> high n
  | Ulow n -> low n
  | Uzext n -> zext n
  | Usext n -> sext n
  | Urepeat n -> repeat n
  | Urotl n -> rolB n
  | Urotr n -> rorB n

  (** val ebinop_denote : ebinop -> bits -> bits -> bits **)

  let ebinop_denote = function
  | Band -> andB
  | Bor -> orB
  | Bxor -> xorB
  | Badd -> addB
  | Bsub -> subB
  | Bmul -> mulB
  | Bdiv -> udivB'
  | Bmod -> uremB
  | Bsdiv -> sdivB
  | Bsrem -> sremB
  | Bsmod -> smodB
  | Bshl -> shlBB
  | Blshr -> shrBB
  | Bashr -> sarBB
  | Bconcat -> (fun b1 b2 -> cat b2 b1)
  | Bcomp ->
    (fun b1 b2 -> (eq_op bitseq_eqType (Obj.magic b1) (Obj.magic b2)) :: [])

  (** val bbinop_denote : bbinop -> bits -> bits -> bool **)

  let bbinop_denote = function
  | Beq -> Obj.magic eq_op bitseq_eqType
  | Bult -> ltB_lsb
  | Bule -> leB
  | Bugt -> gtB
  | Buge -> geB
  | Bslt -> sltB
  | Bsle -> sleB
  | Bsgt -> sgtB
  | Bsge -> sgeB
  | Buaddo -> carry_addB
  | Busubo -> borrow_subB
  | Bumulo -> coq_Umulo
  | Bsaddo -> coq_Saddo
  | Bssubo -> coq_Ssubo
  | Bsmulo -> coq_Smulo

  (** val eval_exp : exp -> S.t -> bits **)

  let rec eval_exp e s =
    match e with
    | Evar v -> S.acc v s
    | Econst n -> n
    | Eunop (op0, e0) -> eunop_denote op0 (eval_exp e0 s)
    | Ebinop (op0, e1, e2) ->
      ebinop_denote op0 (eval_exp e1 s) (eval_exp e2 s)
    | Eite (b, e1, e2) ->
      if eval_bexp b s then eval_exp e1 s else eval_exp e2 s

  (** val eval_bexp : bexp -> S.t -> bool **)

  and eval_bexp e s =
    match e with
    | Bfalse -> false
    | Btrue -> true
    | Bbinop (op0, e1, e2) ->
      bbinop_denote op0 (eval_exp e1 s) (eval_exp e2 s)
    | Blneg e0 -> negb (eval_bexp e0 s)
    | Bconj (e1, e2) -> (&&) (eval_bexp e1 s) (eval_bexp e2 s)
    | Bdisj (e1, e2) -> (||) (eval_bexp e1 s) (eval_bexp e2 s)

  (** val vars_exp : exp -> VS.t **)

  let rec vars_exp = function
  | Evar v -> VS.singleton v
  | Econst _ -> VS.empty
  | Eunop (_, e0) -> vars_exp e0
  | Ebinop (_, e1, e2) -> VS.union (vars_exp e1) (vars_exp e2)
  | Eite (b, e1, e2) ->
    VS.union (vars_bexp b) (VS.union (vars_exp e1) (vars_exp e2))

  (** val vars_bexp : bexp -> VS.t **)

  and vars_bexp = function
  | Bbinop (_, e1, e2) -> VS.union (vars_exp e1) (vars_exp e2)
  | Blneg e0 -> vars_bexp e0
  | Bconj (e1, e2) -> VS.union (vars_bexp e1) (vars_bexp e2)
  | Bdisj (e1, e2) -> VS.union (vars_bexp e1) (vars_bexp e2)
  | _ -> VS.empty

  (** val vars_bexps : bexp list -> VS.t **)

  let rec vars_bexps = function
  | [] -> VS.empty
  | e :: es0 -> VS.union (vars_bexp e) (vars_bexps es0)

  (** val id_eunop : eunop -> int **)

  let id_eunop = function
  | Unot -> 0
  | Uneg -> Pervasives.succ 0
  | Uextr (_, _) -> Pervasives.succ (Pervasives.succ 0)
  | Uhigh _ ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
  | Ulow _ ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))
  | Uzext _ ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0)))))
  | Usext _ ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))
  | Urepeat _ ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))
  | Urotl _ ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))))))
  | Urotr _ ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0)))))))))

  (** val eunop_ltn : eunop -> eunop -> bool **)

  let eunop_ltn o1 o2 =
    match o1 with
    | Uextr (i1, j1) ->
      (match o2 with
       | Uextr (i2, j2) ->
         (||) (leq (Pervasives.succ i1) i2)
           ((&&) (eq_op nat_eqType (Obj.magic i1) (Obj.magic i2))
             (leq (Pervasives.succ j1) j2))
       | _ -> leq (Pervasives.succ (id_eunop o1)) (id_eunop o2))
    | Uhigh n1 ->
      (match o2 with
       | Uhigh n2 -> leq (Pervasives.succ n1) n2
       | _ -> leq (Pervasives.succ (id_eunop o1)) (id_eunop o2))
    | Ulow n1 ->
      (match o2 with
       | Ulow n2 -> leq (Pervasives.succ n1) n2
       | _ -> leq (Pervasives.succ (id_eunop o1)) (id_eunop o2))
    | Uzext n1 ->
      (match o2 with
       | Uzext n2 -> leq (Pervasives.succ n1) n2
       | _ -> leq (Pervasives.succ (id_eunop o1)) (id_eunop o2))
    | Usext n1 ->
      (match o2 with
       | Usext n2 -> leq (Pervasives.succ n1) n2
       | _ -> leq (Pervasives.succ (id_eunop o1)) (id_eunop o2))
    | Urepeat n1 ->
      (match o2 with
       | Urepeat n2 -> leq (Pervasives.succ n1) n2
       | _ -> leq (Pervasives.succ (id_eunop o1)) (id_eunop o2))
    | Urotl n1 ->
      (match o2 with
       | Urotl n2 -> leq (Pervasives.succ n1) n2
       | _ -> leq (Pervasives.succ (id_eunop o1)) (id_eunop o2))
    | Urotr n1 ->
      (match o2 with
       | Urotr n2 -> leq (Pervasives.succ n1) n2
       | _ -> leq (Pervasives.succ (id_eunop o1)) (id_eunop o2))
    | _ -> leq (Pervasives.succ (id_eunop o1)) (id_eunop o2)

  (** val id_ebinop : ebinop -> int **)

  let id_ebinop = function
  | Band -> 0
  | Bor -> Pervasives.succ 0
  | Bxor -> Pervasives.succ (Pervasives.succ 0)
  | Badd -> Pervasives.succ (Pervasives.succ (Pervasives.succ 0))
  | Bsub ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
  | Bmul ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))
  | Bdiv ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0)))))
  | Bmod ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))
  | Bsdiv ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))
  | Bsrem ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))))))
  | Bsmod ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0)))))))))
  | Bshl ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))
  | Blshr ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))))
  | Bashr ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))))))))))
  | Bconcat ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0)))))))))))))
  | Bcomp ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))))))

  (** val ebinop_ltn : ebinop -> ebinop -> bool **)

  let ebinop_ltn o1 o2 =
    leq (Pervasives.succ (id_ebinop o1)) (id_ebinop o2)

  (** val id_bbinop : bbinop -> int **)

  let id_bbinop = function
  | Beq -> 0
  | Bult -> Pervasives.succ 0
  | Bule -> Pervasives.succ (Pervasives.succ 0)
  | Bugt -> Pervasives.succ (Pervasives.succ (Pervasives.succ 0))
  | Buge ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
  | Bslt ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))
  | Bsle ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0)))))
  | Bsgt ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))
  | Bsge ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))
  | Buaddo ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))))))
  | Busubo ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0)))))))))
  | Bumulo ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))))))))
  | Bsaddo ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      0)))))))))))
  | Bssubo ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))))))))))
  | Bsmulo ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0)))))))))))))

  (** val bbinop_ltn : bbinop -> bbinop -> bool **)

  let bbinop_ltn o1 o2 =
    leq (Pervasives.succ (id_bbinop o1)) (id_bbinop o2)

  (** val id_exp : exp -> int **)

  let id_exp = function
  | Evar _ -> 0
  | Econst _ -> Pervasives.succ 0
  | Eunop (_, _) -> Pervasives.succ (Pervasives.succ 0)
  | Ebinop (_, _, _) -> Pervasives.succ (Pervasives.succ (Pervasives.succ 0))
  | Eite (_, _, _) ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))

  (** val id_bexp : bexp -> int **)

  let id_bexp = function
  | Bfalse -> 0
  | Btrue -> Pervasives.succ 0
  | Bbinop (_, _, _) -> Pervasives.succ (Pervasives.succ 0)
  | Blneg _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ 0))
  | Bconj (_, _) ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
  | Bdisj (_, _) ->
    Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0))))

  (** val exp_ltn : exp -> exp -> bool **)

  let rec exp_ltn e1 e2 =
    match e1 with
    | Evar v1 ->
      (match e2 with
       | Evar v2 -> V.ltn v1 v2
       | _ -> leq (Pervasives.succ (id_exp e1)) (id_exp e2))
    | Econst n1 ->
      (match e2 with
       | Econst n2 ->
         (||) (leq (Pervasives.succ (size n1)) (size n2))
           ((&&) (eq_op nat_eqType (Obj.magic size n1) (Obj.magic size n2))
             (ltB_lsb n1 n2))
       | _ -> leq (Pervasives.succ (id_exp e1)) (id_exp e2))
    | Eunop (o1, e3) ->
      (match e2 with
       | Eunop (o2, e4) ->
         (||) (eunop_ltn o1 o2)
           ((&&) (eq_op eunop_eqType (Obj.magic o1) (Obj.magic o2))
             (exp_ltn e3 e4))
       | _ -> leq (Pervasives.succ (id_exp e1)) (id_exp e2))
    | Ebinop (o1, e3, e4) ->
      (match e2 with
       | Ebinop (o2, e5, e6) ->
         (||)
           ((||) (ebinop_ltn o1 o2)
             ((&&) (eq_op ebinop_eqType (Obj.magic o1) (Obj.magic o2))
               (exp_ltn e3 e5)))
           ((&&)
             ((&&) (eq_op ebinop_eqType (Obj.magic o1) (Obj.magic o2))
               (eq_op exp_eqType (Obj.magic e3) (Obj.magic e5)))
             (exp_ltn e4 e6))
       | _ -> leq (Pervasives.succ (id_exp e1)) (id_exp e2))
    | Eite (c1, e3, e4) ->
      (match e2 with
       | Eite (c2, e5, e6) ->
         (||)
           ((||) (bexp_ltn c1 c2)
             ((&&) (eq_op bexp_eqType (Obj.magic c1) (Obj.magic c2))
               (exp_ltn e3 e5)))
           ((&&)
             ((&&) (eq_op bexp_eqType (Obj.magic c1) (Obj.magic c2))
               (eq_op exp_eqType (Obj.magic e3) (Obj.magic e5)))
             (exp_ltn e4 e6))
       | _ -> leq (Pervasives.succ (id_exp e1)) (id_exp e2))

  (** val bexp_ltn : bexp -> bexp -> bool **)

  and bexp_ltn e1 e2 =
    match e1 with
    | Bbinop (o1, e3, e4) ->
      (match e2 with
       | Bbinop (o2, e5, e6) ->
         (||)
           ((||) (bbinop_ltn o1 o2)
             ((&&) (eq_op bbinop_eqType (Obj.magic o1) (Obj.magic o2))
               (exp_ltn e3 e5)))
           ((&&)
             ((&&) (eq_op bbinop_eqType (Obj.magic o1) (Obj.magic o2))
               (eq_op exp_eqType (Obj.magic e3) (Obj.magic e5)))
             (exp_ltn e4 e6))
       | _ -> leq (Pervasives.succ (id_bexp e1)) (id_bexp e2))
    | Blneg e3 ->
      (match e2 with
       | Blneg e4 -> bexp_ltn e3 e4
       | _ -> leq (Pervasives.succ (id_bexp e1)) (id_bexp e2))
    | Bconj (e3, e4) ->
      (match e2 with
       | Bconj (e5, e6) ->
         (||) (bexp_ltn e3 e5)
           ((&&) (eq_op bexp_eqType (Obj.magic e3) (Obj.magic e5))
             (bexp_ltn e4 e6))
       | _ -> leq (Pervasives.succ (id_bexp e1)) (id_bexp e2))
    | Bdisj (e3, e4) ->
      (match e2 with
       | Bdisj (e5, e6) ->
         (||) (bexp_ltn e3 e5)
           ((&&) (eq_op bexp_eqType (Obj.magic e3) (Obj.magic e5))
             (bexp_ltn e4 e6))
       | _ -> leq (Pervasives.succ (id_bexp e1)) (id_bexp e2))
    | _ -> leq (Pervasives.succ (id_bexp e1)) (id_bexp e2)

  (** val exp_compare : exp -> exp -> exp OrderedType.coq_Compare **)

  let rec exp_compare e1 e2 =
    let _evar_0_ = fun _ _ -> OrderedType.EQ in
    let _evar_0_0 = fun _ ->
      let _evar_0_0 = fun _ _ -> OrderedType.LT in
      let _evar_0_1 = fun _ _ -> OrderedType.GT in
      if exp_ltn e1 e2 then _evar_0_0 __ else _evar_0_1 __
    in
    if eq_op exp_eqType (Obj.magic e1) (Obj.magic e2)
    then _evar_0_ __ __
    else _evar_0_0 __ __

  (** val bexp_compare : bexp -> bexp -> bexp OrderedType.coq_Compare **)

  and bexp_compare e1 e2 =
    let _evar_0_ = fun _ _ -> OrderedType.EQ in
    let _evar_0_0 = fun _ ->
      let _evar_0_0 = fun _ _ -> OrderedType.LT in
      let _evar_0_1 = fun _ _ -> OrderedType.GT in
      if bexp_ltn e1 e2 then _evar_0_0 __ else _evar_0_1 __
    in
    if eq_op bexp_eqType (Obj.magic e1) (Obj.magic e2)
    then _evar_0_ __ __
    else _evar_0_0 __ __

  module ExpOrderMinimal =
   struct
    (** val t : Equality.coq_type **)

    let t =
      exp_eqType

    (** val eqn : Equality.sort -> Equality.sort -> bool **)

    let eqn e1 e2 =
      eq_op t e1 e2

    (** val ltn : Equality.sort -> Equality.sort -> bool **)

    let ltn e1 e2 =
      exp_ltn (Obj.magic e1) (Obj.magic e2)

    (** val compare :
        Equality.sort -> Equality.sort -> Equality.sort
        OrderedType.coq_Compare **)

    let compare e1 e2 =
      Obj.magic exp_compare e1 e2
   end

  module ExpOrder = SsrOrder.MakeSsrOrder(ExpOrderMinimal)

  module BexpOrderMinimal =
   struct
    (** val t : Equality.coq_type **)

    let t =
      bexp_eqType

    (** val eqn : Equality.sort -> Equality.sort -> bool **)

    let eqn e1 e2 =
      eq_op t e1 e2

    (** val ltn : Equality.sort -> Equality.sort -> bool **)

    let ltn e1 e2 =
      bexp_ltn (Obj.magic e1) (Obj.magic e2)

    (** val compare :
        Equality.sort -> Equality.sort -> Equality.sort
        OrderedType.coq_Compare **)

    let compare e1 e2 =
      Obj.magic bexp_compare e1 e2
   end

  module BexpOrder = SsrOrder.MakeSsrOrder(BexpOrderMinimal)

  (** val len_exp : exp -> int **)

  let rec len_exp = function
  | Eunop (_, e0) -> Pervasives.succ (len_exp e0)
  | Ebinop (_, e1, e2) -> Pervasives.succ (addn (len_exp e1) (len_exp e2))
  | Eite (b, e1, e2) ->
    Pervasives.succ (addn (addn (len_bexp b) (len_exp e1)) (len_exp e2))
  | _ -> Pervasives.succ 0

  (** val len_bexp : bexp -> int **)

  and len_bexp = function
  | Bbinop (_, e1, e2) -> Pervasives.succ (addn (len_exp e1) (len_exp e2))
  | Blneg e0 -> Pervasives.succ (len_bexp e0)
  | Bconj (e1, e2) -> Pervasives.succ (addn (len_bexp e1) (len_bexp e2))
  | Bdisj (e1, e2) -> Pervasives.succ (addn (len_bexp e1) (len_bexp e2))
  | _ -> Pervasives.succ 0

  (** val subee : exp -> exp -> bool **)

  let rec subee c p =
    (||) (eq_op exp_eqType (Obj.magic c) (Obj.magic p))
      (match p with
       | Eunop (_, e) -> subee c e
       | Ebinop (_, e1, e2) -> (||) (subee c e1) (subee c e2)
       | Eite (b, e1, e2) -> (||) ((||) (subeb c b) (subee c e1)) (subee c e2)
       | _ -> false)

  (** val subeb : exp -> bexp -> bool **)

  and subeb e = function
  | Bbinop (_, e1, e2) -> (||) (subee e e1) (subee e e2)
  | Blneg b0 -> subeb e b0
  | Bconj (b1, b2) -> (||) (subeb e b1) (subeb e b2)
  | Bdisj (b1, b2) -> (||) (subeb e b1) (subeb e b2)
  | _ -> false

  (** val subbe : bexp -> exp -> bool **)

  let rec subbe c = function
  | Eunop (_, e) -> subbe c e
  | Ebinop (_, e1, e2) -> (||) (subbe c e1) (subbe c e2)
  | Eite (b, e1, e2) -> (||) ((||) (subbb c b) (subbe c e1)) (subbe c e2)
  | _ -> false

  (** val subbb : bexp -> bexp -> bool **)

  and subbb c p =
    (||) (eq_op bexp_eqType (Obj.magic c) (Obj.magic p))
      (match p with
       | Bbinop (_, e1, e2) -> (||) (subbe c e1) (subbe c e2)
       | Blneg b -> subbb c b
       | Bconj (b1, b2) -> (||) (subbb c b1) (subbb c b2)
       | Bdisj (b1, b2) -> (||) (subbb c b1) (subbb c b2)
       | _ -> false)

  module TELemmas = FMapLemmas(TE)

  (** val exp_size : exp -> TE.env -> int **)

  let rec exp_size e te =
    match e with
    | Evar v -> TE.vsize v te
    | Econst n -> size n
    | Eunop (op0, e0) ->
      (match op0 with
       | Uextr (i, j) -> addn (subn i j) (Pervasives.succ 0)
       | Uhigh n -> n
       | Ulow n -> n
       | Uzext n -> addn (exp_size e0 te) n
       | Usext n -> addn (exp_size e0 te) n
       | Urepeat n -> muln n (exp_size e0 te)
       | _ -> exp_size e0 te)
    | Ebinop (op0, e1, e2) ->
      (match op0 with
       | Band -> maxn (exp_size e1 te) (exp_size e2 te)
       | Bor -> maxn (exp_size e1 te) (exp_size e2 te)
       | Bxor -> maxn (exp_size e1 te) (exp_size e2 te)
       | Badd -> minn (exp_size e1 te) (exp_size e2 te)
       | Bsub -> minn (exp_size e1 te) (exp_size e2 te)
       | Bconcat -> addn (exp_size e1 te) (exp_size e2 te)
       | Bcomp -> Pervasives.succ 0
       | _ -> exp_size e1 te)
    | Eite (_, e1, e2) -> maxn (exp_size e1 te) (exp_size e2 te)

  (** val well_formed_exp : exp -> TE.env -> bool **)

  let rec well_formed_exp e te =
    match e with
    | Evar v -> TE.mem v te
    | Econst _ -> true
    | Eunop (_, e0) -> well_formed_exp e0 te
    | Ebinop (op0, e1, e2) ->
      (&&)
        ((&&) ((&&) (well_formed_exp e1 te) (well_formed_exp e2 te))
          (leq (Pervasives.succ 0) (exp_size e1 te)))
        (if eq_op ebinop_eqType (Obj.magic op0) (Obj.magic Bconcat)
         then true
         else eq_op nat_eqType (Obj.magic exp_size e1 te)
                (Obj.magic exp_size e2 te))
    | Eite (b, e1, e2) ->
      (&&)
        ((&&) ((&&) (well_formed_bexp b te) (well_formed_exp e1 te))
          (well_formed_exp e2 te))
        (eq_op nat_eqType (Obj.magic exp_size e1 te)
          (Obj.magic exp_size e2 te))

  (** val well_formed_bexp : bexp -> TE.env -> bool **)

  and well_formed_bexp b te =
    match b with
    | Bbinop (_, e1, e2) ->
      (&&) ((&&) (well_formed_exp e1 te) (well_formed_exp e2 te))
        (eq_op nat_eqType (Obj.magic exp_size e1 te)
          (Obj.magic exp_size e2 te))
    | Blneg b0 -> well_formed_bexp b0 te
    | Bconj (b1, b2) -> (&&) (well_formed_bexp b1 te) (well_formed_bexp b2 te)
    | Bdisj (b1, b2) -> (&&) (well_formed_bexp b1 te) (well_formed_bexp b2 te)
    | _ -> true

  (** val well_formed_bexps : bexp list -> TE.env -> bool **)

  let rec well_formed_bexps bs te =
    match bs with
    | [] -> true
    | b :: bs' -> (&&) (well_formed_bexp b te) (well_formed_bexps bs' te)

  (** val split_conj : bexp -> bexp list **)

  let rec split_conj e = match e with
  | Bconj (e1, e2) -> cat (split_conj e1) (split_conj e2)
  | _ -> e :: []

  (** val qfbv_conjs : bexp list -> bexp **)

  let rec qfbv_conjs = function
  | [] -> Btrue
  | hd :: tl -> qfbv_conj hd (qfbv_conjs tl)

  (** val qfbv_conjs_rec : bexp -> bexp list -> bexp **)

  let rec qfbv_conjs_rec pre_es = function
  | [] -> pre_es
  | hd :: tl -> qfbv_conjs_rec (qfbv_conj pre_es hd) tl

  (** val qfbv_conjs_la : bexp list -> bexp **)

  let qfbv_conjs_la = function
  | [] -> Btrue
  | e :: es0 -> qfbv_conjs_rec (qfbv_conj Btrue e) es0

  (** val eval_bexps : bexp list -> S.t -> bool **)

  let eval_bexps es s =
    all (fun x -> eval_bexp x s) es

  (** val simplify_bexp : bexp -> bexp **)

  let rec simplify_bexp e = match e with
  | Blneg e0 ->
    (match simplify_bexp e0 with
     | Bfalse -> Btrue
     | Btrue -> Bfalse
     | Blneg e1 -> e1
     | x -> Blneg x)
  | Bconj (e1, e2) ->
    (match simplify_bexp e1 with
     | Bfalse -> Bfalse
     | Btrue -> simplify_bexp e2
     | x ->
       (match simplify_bexp e2 with
        | Bfalse -> Bfalse
        | Btrue -> x
        | x0 -> Bconj (x, x0)))
  | Bdisj (e1, e2) ->
    (match simplify_bexp e1 with
     | Bfalse -> simplify_bexp e2
     | Btrue -> Btrue
     | x ->
       (match simplify_bexp e2 with
        | Bfalse -> x
        | Btrue -> Btrue
        | x0 -> Bdisj (x, x0)))
  | _ -> e

  (** val bexp_is_implied : bexp -> bool **)

  let bexp_is_implied = function
  | Bdisj (b, e2) ->
    (match b with
     | Blneg e1 ->
       in_mem (Obj.magic e2)
         (mem (seq_predType bexp_eqType) (Obj.magic split_conj e1))
     | _ -> false)
  | _ -> false

  (** val simplify_bexp2 : bexp -> bexp **)

  let rec simplify_bexp2 e = match e with
  | Blneg e0 ->
    (match simplify_bexp2 e0 with
     | Bfalse -> Btrue
     | Btrue -> Bfalse
     | Blneg e1 -> e1
     | x -> Blneg x)
  | Bconj (e1, e2) ->
    (match simplify_bexp2 e1 with
     | Bfalse -> Bfalse
     | Btrue -> simplify_bexp2 e2
     | x ->
       (match simplify_bexp2 e2 with
        | Bfalse -> Bfalse
        | Btrue -> x
        | x0 -> Bconj (x, x0)))
  | Bdisj (e1, e2) ->
    (match simplify_bexp2 e1 with
     | Bfalse -> simplify_bexp2 e2
     | Btrue -> Btrue
     | x ->
       (match simplify_bexp2 e2 with
        | Bfalse -> x
        | Btrue -> Btrue
        | x0 ->
          if bexp_is_implied (Bdisj (x, x0)) then Btrue else Bdisj (x, x0)))
  | _ -> e
 end

module QFBV = MakeQFBV(SSAVarOrder)(SSAVS)(TypEnv.SSATE)(SSAStore)

(** val eunop_eqType : Equality.coq_type **)

let eunop_eqType =
  Obj.magic QFBV.eunop_eqMixin

(** val ebinop_eqType : Equality.coq_type **)

let ebinop_eqType =
  Obj.magic QFBV.ebinop_eqMixin

(** val bbinop_eqType : Equality.coq_type **)

let bbinop_eqType =
  Obj.magic QFBV.bbinop_eqMixin
