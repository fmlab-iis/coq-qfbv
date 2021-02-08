open BinInt
open BinNat
open BinNums
open Bool
open Datatypes
open NBitsDef
open NBitsOp
open Var
open ZAriths
open Eqtype
open Seq
open Ssrnat

type hashed_exp =
| HEvar of SSAVarOrder.t
| HEconst of bits
| HEunop of QFBV.QFBV.eunop * hexp
| HEbinop of QFBV.QFBV.ebinop * hexp * hexp
| HEite of hbexp * hexp * hexp
and hashed_bexp =
| HBfalse
| HBtrue
| HBbinop of QFBV.QFBV.bbinop * hexp * hexp
| HBlneg of hbexp
| HBconj of hbexp * hbexp
| HBdisj of hbexp * hbexp
and hexp =
| Coq_epair of hashed_exp * coq_Z
and hbexp =
| Coq_bpair of hashed_bexp * coq_Z

val ehval : hexp -> coq_Z

val bhval : hbexp -> coq_Z

val unhash_hashed_exp : hashed_exp -> QFBV.QFBV.exp

val unhash_hashed_bexp : hashed_bexp -> QFBV.QFBV.bexp

val unhash_hexp : hexp -> QFBV.QFBV.exp

val unhash_hbexp : hbexp -> QFBV.QFBV.bexp

val hash_exp : QFBV.QFBV.exp -> hexp

val hash_bexp : QFBV.QFBV.bexp -> hbexp

val hashed_exp_eqn : hashed_exp -> hashed_exp -> bool

val hashed_bexp_eqn : hashed_bexp -> hashed_bexp -> bool

val hexp_eqn : hexp -> hexp -> bool

val hbexp_eqn : hbexp -> hbexp -> bool

val hexp_eqP : hexp -> hexp -> reflect

val hbexp_eqP : hbexp -> hbexp -> reflect

val hexp_eqMixin : hexp Equality.mixin_of

val hexp_eqType : Equality.coq_type

val hbexp_eqMixin : hbexp Equality.mixin_of

val hbexp_eqType : Equality.coq_type

val id_hashed_exp : hashed_exp -> int

val id_hashed_bexp : hashed_bexp -> int

val sizen : bits -> coq_N

val hashed_exp_ltn : hashed_exp -> hashed_exp -> bool

val hashed_bexp_ltn : hashed_bexp -> hashed_bexp -> bool

val hexp_ltn : hexp -> hexp -> bool

val hbexp_ltn : hbexp -> hbexp -> bool

val hashed_exp_compare :
  hashed_exp -> hashed_exp -> hashed_exp OrderedType.coq_Compare

val hashed_bexp_compare :
  hashed_bexp -> hashed_bexp -> hashed_bexp OrderedType.coq_Compare

val hexp_compare : hexp -> hexp -> hexp OrderedType.coq_Compare

val hbexp_compare : hbexp -> hbexp -> hbexp OrderedType.coq_Compare

module HexpOrderMinimal :
 sig
  val t : Equality.coq_type

  val eqn : Equality.sort -> Equality.sort -> bool

  val ltn : Equality.sort -> Equality.sort -> bool

  val compare :
    Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare
 end

module HbexpOrderMinimal :
 sig
  val t : Equality.coq_type

  val eqn : Equality.sort -> Equality.sort -> bool

  val ltn : Equality.sort -> Equality.sort -> bool

  val compare :
    Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare
 end

module HexpOrder :
 sig
  val coq_T : Equality.coq_type

  type t = Equality.sort

  val ltn : t -> t -> bool

  val compare : t -> t -> t OrderedType.coq_Compare

  val eq_dec : t -> t -> bool
 end

module HbexpOrder :
 sig
  val coq_T : Equality.coq_type

  type t = Equality.sort

  val ltn : t -> t -> bool

  val compare : t -> t -> t OrderedType.coq_Compare

  val eq_dec : t -> t -> bool
 end
