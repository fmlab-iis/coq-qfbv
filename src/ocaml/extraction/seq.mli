open Bool
open Datatypes
open Eqtype
open Ssrbool
open Ssrbool0
open Ssreflect
open Ssrnat

val size : 'a1 list -> int

val head : 'a1 -> 'a1 list -> 'a1

val behead : 'a1 list -> 'a1 list

val ncons : int -> 'a1 -> 'a1 list -> 'a1 list

val nseq : int -> 'a1 -> 'a1 list

val cat : 'a1 list -> 'a1 list -> 'a1 list

val rcons : 'a1 list -> 'a1 -> 'a1 list

val last : 'a1 -> 'a1 list -> 'a1

val belast : 'a1 -> 'a1 list -> 'a1 list

val all : 'a1 pred -> 'a1 list -> bool

val drop : int -> 'a1 list -> 'a1 list

val take : int -> 'a1 list -> 'a1 list

val catrev : 'a1 list -> 'a1 list -> 'a1 list

val rev : 'a1 list -> 'a1 list

val eqseq :
  Equality.coq_type -> Equality.sort list -> Equality.sort list -> bool

val eqseqP : Equality.coq_type -> Equality.sort list Equality.axiom

val seq_eqMixin : Equality.coq_type -> Equality.sort list Equality.mixin_of

val seq_eqType : Equality.coq_type -> Equality.coq_type

val mem_seq : Equality.coq_type -> Equality.sort list -> Equality.sort -> bool

type seq_eqclass = Equality.sort list

val pred_of_seq : Equality.coq_type -> seq_eqclass -> Equality.sort pred_sort

val seq_predType : Equality.coq_type -> Equality.sort predType

type bitseq = bool list

val bitseq_eqType : Equality.coq_type

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2

val foldl : ('a2 -> 'a1 -> 'a2) -> 'a2 -> 'a1 list -> 'a2

val zip : 'a1 list -> 'a2 list -> ('a1 * 'a2) list

val unzip1 : ('a1 * 'a2) list -> 'a1 list

val unzip2 : ('a1 * 'a2) list -> 'a2 list
