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

let __ = let rec f _ = Obj.repr f in Obj.repr f

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

(** val ehval : hexp -> coq_Z **)

let ehval = function
| Coq_epair (_, h) -> h

(** val bhval : hbexp -> coq_Z **)

let bhval = function
| Coq_bpair (_, h) -> h

(** val unhash_hashed_exp : hashed_exp -> QFBV.QFBV.exp **)

let rec unhash_hashed_exp = function
| HEvar v -> QFBV.QFBV.Evar v
| HEconst bs -> QFBV.QFBV.Econst bs
| HEunop (op0, e0) -> QFBV.QFBV.Eunop (op0, (unhash_hexp e0))
| HEbinop (op0, e1, e2) ->
  QFBV.QFBV.Ebinop (op0, (unhash_hexp e1), (unhash_hexp e2))
| HEite (b, e1, e2) ->
  QFBV.QFBV.Eite ((unhash_hbexp b), (unhash_hexp e1), (unhash_hexp e2))

(** val unhash_hashed_bexp : hashed_bexp -> QFBV.QFBV.bexp **)

and unhash_hashed_bexp = function
| HBfalse -> QFBV.QFBV.Bfalse
| HBtrue -> QFBV.QFBV.Btrue
| HBbinop (op0, e1, e2) ->
  QFBV.QFBV.Bbinop (op0, (unhash_hexp e1), (unhash_hexp e2))
| HBlneg e0 -> QFBV.QFBV.Blneg (unhash_hbexp e0)
| HBconj (e1, e2) -> QFBV.QFBV.Bconj ((unhash_hbexp e1), (unhash_hbexp e2))
| HBdisj (e1, e2) -> QFBV.QFBV.Bdisj ((unhash_hbexp e1), (unhash_hbexp e2))

(** val unhash_hexp : hexp -> QFBV.QFBV.exp **)

and unhash_hexp = function
| Coq_epair (e0, _) -> unhash_hashed_exp e0

(** val unhash_hbexp : hbexp -> QFBV.QFBV.bexp **)

and unhash_hbexp = function
| Coq_bpair (e0, _) -> unhash_hashed_bexp e0

(** val hash_exp : QFBV.QFBV.exp -> hexp **)

let rec hash_exp = function
| QFBV.QFBV.Evar v -> Coq_epair ((HEvar v), (Zpos Coq_xH))
| QFBV.QFBV.Econst bs -> Coq_epair ((HEconst bs), (Zpos Coq_xH))
| QFBV.QFBV.Eunop (op0, e0) ->
  let he = hash_exp e0 in
  Coq_epair ((HEunop (op0, he)), (Z.add (ehval he) (Zpos Coq_xH)))
| QFBV.QFBV.Ebinop (op0, e1, e2) ->
  let he1 = hash_exp e1 in
  let he2 = hash_exp e2 in
  Coq_epair ((HEbinop (op0, he1, he2)),
  (Z.add (Z.add (ehval he1) (ehval he2)) (Zpos Coq_xH)))
| QFBV.QFBV.Eite (b, e1, e2) ->
  let hb = hash_bexp b in
  let he1 = hash_exp e1 in
  let he2 = hash_exp e2 in
  Coq_epair ((HEite (hb, he1, he2)),
  (Z.add (Z.add (Z.add (bhval hb) (ehval he1)) (ehval he2)) (Zpos Coq_xH)))

(** val hash_bexp : QFBV.QFBV.bexp -> hbexp **)

and hash_bexp = function
| QFBV.QFBV.Bfalse -> Coq_bpair (HBfalse, (Zpos Coq_xH))
| QFBV.QFBV.Btrue -> Coq_bpair (HBtrue, (Zpos Coq_xH))
| QFBV.QFBV.Bbinop (op0, e1, e2) ->
  let he1 = hash_exp e1 in
  let he2 = hash_exp e2 in
  Coq_bpair ((HBbinop (op0, he1, he2)),
  (Z.add (Z.add (ehval he1) (ehval he2)) (Zpos Coq_xH)))
| QFBV.QFBV.Blneg e0 ->
  let he = hash_bexp e0 in
  Coq_bpair ((HBlneg he), (Z.add (bhval he) (Zpos Coq_xH)))
| QFBV.QFBV.Bconj (e1, e2) ->
  let he1 = hash_bexp e1 in
  let he2 = hash_bexp e2 in
  Coq_bpair ((HBconj (he1, he2)),
  (Z.add (Z.add (bhval he1) (bhval he2)) (Zpos Coq_xH)))
| QFBV.QFBV.Bdisj (e1, e2) ->
  let he1 = hash_bexp e1 in
  let he2 = hash_bexp e2 in
  Coq_bpair ((HBdisj (he1, he2)),
  (Z.add (Z.add (bhval he1) (bhval he2)) (Zpos Coq_xH)))

(** val hashed_exp_eqn : hashed_exp -> hashed_exp -> bool **)

let rec hashed_exp_eqn e1 e2 =
  match e1 with
  | HEvar v1 ->
    (match e2 with
     | HEvar v2 -> eq_op SSAVarOrder.coq_T v1 v2
     | _ -> false)
  | HEconst n1 ->
    (match e2 with
     | HEconst n2 -> eq_op bitseq_eqType (Obj.magic n1) (Obj.magic n2)
     | _ -> false)
  | HEunop (op1, e3) ->
    (match e2 with
     | HEunop (op2, e4) ->
       (&&) (eq_op QFBV.eunop_eqType (Obj.magic op1) (Obj.magic op2))
         (hexp_eqn e3 e4)
     | _ -> false)
  | HEbinop (op1, e11, e12) ->
    (match e2 with
     | HEbinop (op2, e21, e22) ->
       (&&)
         ((&&) (eq_op QFBV.ebinop_eqType (Obj.magic op1) (Obj.magic op2))
           (hexp_eqn e11 e21)) (hexp_eqn e12 e22)
     | _ -> false)
  | HEite (b1, e11, e12) ->
    (match e2 with
     | HEite (b2, e21, e22) ->
       (&&) ((&&) (hbexp_eqn b1 b2) (hexp_eqn e11 e21)) (hexp_eqn e12 e22)
     | _ -> false)

(** val hashed_bexp_eqn : hashed_bexp -> hashed_bexp -> bool **)

and hashed_bexp_eqn e1 e2 =
  match e1 with
  | HBfalse -> (match e2 with
                | HBfalse -> true
                | _ -> false)
  | HBtrue -> (match e2 with
               | HBtrue -> true
               | _ -> false)
  | HBbinop (op1, e11, e12) ->
    (match e2 with
     | HBbinop (op2, e21, e22) ->
       (&&)
         ((&&) (eq_op QFBV.bbinop_eqType (Obj.magic op1) (Obj.magic op2))
           (hexp_eqn e11 e21)) (hexp_eqn e12 e22)
     | _ -> false)
  | HBlneg e3 -> (match e2 with
                  | HBlneg e4 -> hbexp_eqn e3 e4
                  | _ -> false)
  | HBconj (e11, e12) ->
    (match e2 with
     | HBconj (e21, e22) -> (&&) (hbexp_eqn e11 e21) (hbexp_eqn e12 e22)
     | _ -> false)
  | HBdisj (e11, e12) ->
    (match e2 with
     | HBdisj (e21, e22) -> (&&) (hbexp_eqn e11 e21) (hbexp_eqn e12 e22)
     | _ -> false)

(** val hexp_eqn : hexp -> hexp -> bool **)

and hexp_eqn e1 e2 =
  let Coq_epair (f1, h1) = e1 in
  let Coq_epair (f2, h2) = e2 in
  if negb (eq_op coq_Z_eqType (Obj.magic h1) (Obj.magic h2))
  then false
  else hashed_exp_eqn f1 f2

(** val hbexp_eqn : hbexp -> hbexp -> bool **)

and hbexp_eqn e1 e2 =
  let Coq_bpair (e3, h1) = e1 in
  let Coq_bpair (e4, h2) = e2 in
  if negb (eq_op coq_Z_eqType (Obj.magic h1) (Obj.magic h2))
  then false
  else hashed_bexp_eqn e3 e4

(** val hexp_eqP : hexp -> hexp -> reflect **)

let hexp_eqP x y =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if hexp_eqn x y then _evar_0_ __ else _evar_0_0 __

(** val hbexp_eqP : hbexp -> hbexp -> reflect **)

let hbexp_eqP x y =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if hbexp_eqn x y then _evar_0_ __ else _evar_0_0 __

(** val hexp_eqMixin : hexp Equality.mixin_of **)

let hexp_eqMixin =
  { Equality.op = hexp_eqn; Equality.mixin_of__1 = hexp_eqP }

(** val hexp_eqType : Equality.coq_type **)

let hexp_eqType =
  Obj.magic hexp_eqMixin

(** val hbexp_eqMixin : hbexp Equality.mixin_of **)

let hbexp_eqMixin =
  { Equality.op = hbexp_eqn; Equality.mixin_of__1 = hbexp_eqP }

(** val hbexp_eqType : Equality.coq_type **)

let hbexp_eqType =
  Obj.magic hbexp_eqMixin

(** val id_hashed_exp : hashed_exp -> int **)

let id_hashed_exp = function
| HEvar _ -> 0
| HEconst _ -> Pervasives.succ 0
| HEunop (_, _) -> Pervasives.succ (Pervasives.succ 0)
| HEbinop (_, _, _) -> Pervasives.succ (Pervasives.succ (Pervasives.succ 0))
| HEite (_, _, _) ->
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))

(** val id_hashed_bexp : hashed_bexp -> int **)

let id_hashed_bexp = function
| HBfalse -> 0
| HBtrue -> Pervasives.succ 0
| HBbinop (_, _, _) -> Pervasives.succ (Pervasives.succ 0)
| HBlneg _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ 0))
| HBconj (_, _) ->
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
| HBdisj (_, _) ->
  Pervasives.succ (Pervasives.succ (Pervasives.succ (Pervasives.succ
    (Pervasives.succ 0))))

(** val sizen : bits -> coq_N **)

let rec sizen = function
| [] -> N0
| _ :: tl -> N.succ (sizen tl)

(** val hashed_exp_ltn : hashed_exp -> hashed_exp -> bool **)

let rec hashed_exp_ltn e1 e2 =
  match e1 with
  | HEvar v1 ->
    (match e2 with
     | HEvar v2 -> SSAVarOrder.ltn v1 v2
     | _ -> leq (Pervasives.succ (id_hashed_exp e1)) (id_hashed_exp e2))
  | HEconst n1 ->
    (match e2 with
     | HEconst n2 ->
       (||) (N.ltb (sizen n1) (sizen n2))
         ((&&)
           (eq_op bin_nat_eqType (Obj.magic sizen n1) (Obj.magic sizen n2))
           (ltB_lsb n1 n2))
     | _ -> leq (Pervasives.succ (id_hashed_exp e1)) (id_hashed_exp e2))
  | HEunop (o1, f1) ->
    (match e2 with
     | HEunop (o2, f2) ->
       (||) (QFBV.QFBV.eunop_ltn o1 o2)
         ((&&) (eq_op QFBV.eunop_eqType (Obj.magic o1) (Obj.magic o2))
           (hexp_ltn f1 f2))
     | _ -> leq (Pervasives.succ (id_hashed_exp e1)) (id_hashed_exp e2))
  | HEbinop (o1, f1, f2) ->
    (match e2 with
     | HEbinop (o2, f3, f4) ->
       (||)
         ((||) (QFBV.QFBV.ebinop_ltn o1 o2)
           ((&&) (eq_op QFBV.ebinop_eqType (Obj.magic o1) (Obj.magic o2))
             (hexp_ltn f1 f3)))
         ((&&)
           ((&&) (eq_op QFBV.ebinop_eqType (Obj.magic o1) (Obj.magic o2))
             (eq_op hexp_eqType (Obj.magic f1) (Obj.magic f3)))
           (hexp_ltn f2 f4))
     | _ -> leq (Pervasives.succ (id_hashed_exp e1)) (id_hashed_exp e2))
  | HEite (c1, f1, f2) ->
    (match e2 with
     | HEite (c2, f3, f4) ->
       (||)
         ((||) (hbexp_ltn c1 c2)
           ((&&) (eq_op hbexp_eqType (Obj.magic c1) (Obj.magic c2))
             (hexp_ltn f1 f3)))
         ((&&)
           ((&&) (eq_op hbexp_eqType (Obj.magic c1) (Obj.magic c2))
             (eq_op hexp_eqType (Obj.magic f1) (Obj.magic f3)))
           (hexp_ltn f2 f4))
     | _ -> leq (Pervasives.succ (id_hashed_exp e1)) (id_hashed_exp e2))

(** val hashed_bexp_ltn : hashed_bexp -> hashed_bexp -> bool **)

and hashed_bexp_ltn e1 e2 =
  match e1 with
  | HBbinop (o1, f1, f2) ->
    (match e2 with
     | HBbinop (o2, f3, f4) ->
       (||)
         ((||) (QFBV.QFBV.bbinop_ltn o1 o2)
           ((&&) (eq_op QFBV.bbinop_eqType (Obj.magic o1) (Obj.magic o2))
             (hexp_ltn f1 f3)))
         ((&&)
           ((&&) (eq_op QFBV.bbinop_eqType (Obj.magic o1) (Obj.magic o2))
             (eq_op hexp_eqType (Obj.magic f1) (Obj.magic f3)))
           (hexp_ltn f2 f4))
     | _ -> leq (Pervasives.succ (id_hashed_bexp e1)) (id_hashed_bexp e2))
  | HBlneg f1 ->
    (match e2 with
     | HBlneg f2 -> hbexp_ltn f1 f2
     | _ -> leq (Pervasives.succ (id_hashed_bexp e1)) (id_hashed_bexp e2))
  | HBconj (f1, f2) ->
    (match e2 with
     | HBconj (f3, f4) ->
       (||) (hbexp_ltn f1 f3)
         ((&&) (eq_op hbexp_eqType (Obj.magic f1) (Obj.magic f3))
           (hbexp_ltn f2 f4))
     | _ -> leq (Pervasives.succ (id_hashed_bexp e1)) (id_hashed_bexp e2))
  | HBdisj (f1, f2) ->
    (match e2 with
     | HBdisj (f3, f4) ->
       (||) (hbexp_ltn f1 f3)
         ((&&) (eq_op hbexp_eqType (Obj.magic f1) (Obj.magic f3))
           (hbexp_ltn f2 f4))
     | _ -> leq (Pervasives.succ (id_hashed_bexp e1)) (id_hashed_bexp e2))
  | _ -> leq (Pervasives.succ (id_hashed_bexp e1)) (id_hashed_bexp e2)

(** val hexp_ltn : hexp -> hexp -> bool **)

and hexp_ltn e1 e2 =
  let Coq_epair (f1, h1) = e1 in
  let Coq_epair (f2, h2) = e2 in
  (||) (Z.ltb h1 h2)
    ((&&) (eq_op coq_Z_eqType (Obj.magic h1) (Obj.magic h2))
      (hashed_exp_ltn f1 f2))

(** val hbexp_ltn : hbexp -> hbexp -> bool **)

and hbexp_ltn e1 e2 =
  let Coq_bpair (f1, h1) = e1 in
  let Coq_bpair (f2, h2) = e2 in
  (||) (Z.ltb h1 h2)
    ((&&) (eq_op coq_Z_eqType (Obj.magic h1) (Obj.magic h2))
      (hashed_bexp_ltn f1 f2))

(** val hashed_exp_compare :
    hashed_exp -> hashed_exp -> hashed_exp OrderedType.coq_Compare **)

let rec hashed_exp_compare e1 e2 =
  let _evar_0_ = fun v1 ->
    let _evar_0_ = fun v2 ->
      let _evar_0_ = fun _ -> OrderedType.LT in
      let _evar_0_0 = fun _ -> OrderedType.EQ in
      let _evar_0_1 = fun _ -> OrderedType.GT in
      (match SSAVarOrder.compare v1 v2 with
       | OrderedType.LT -> _evar_0_ __
       | OrderedType.EQ -> _evar_0_0 __
       | OrderedType.GT -> _evar_0_1 __)
    in
    let _evar_0_0 = fun _ -> OrderedType.LT in
    let _evar_0_1 = fun _ _ -> OrderedType.LT in
    let _evar_0_2 = fun _ _ _ -> OrderedType.LT in
    let _evar_0_3 = fun _ _ _ -> OrderedType.LT in
    (match e2 with
     | HEvar t0 -> _evar_0_ t0
     | HEconst b -> _evar_0_0 b
     | HEunop (e, h) -> _evar_0_1 e h
     | HEbinop (e, h, h0) -> _evar_0_2 e h h0
     | HEite (h, h0, h1) -> _evar_0_3 h h0 h1)
  in
  let _evar_0_0 = fun bs1 ->
    let _evar_0_0 = fun _ -> OrderedType.GT in
    let _evar_0_1 = fun bs2 ->
      let _evar_0_1 = fun _ -> OrderedType.EQ in
      let _evar_0_2 = fun _ ->
        let _evar_0_2 = fun _ -> OrderedType.LT in
        let _evar_0_3 = fun _ ->
          let _evar_0_3 = fun _ -> OrderedType.LT in
          let _evar_0_4 = fun _ -> OrderedType.GT in
          if (&&)
               (eq_op bin_nat_eqType (Obj.magic sizen bs1)
                 (Obj.magic sizen bs2)) (ltB_lsb bs1 bs2)
          then _evar_0_3 __
          else _evar_0_4 __
        in
        if N.ltb (sizen bs1) (sizen bs2) then _evar_0_2 __ else _evar_0_3 __
      in
      if eq_op bitseq_eqType (Obj.magic bs1) (Obj.magic bs2)
      then _evar_0_1 __
      else _evar_0_2 __
    in
    let _evar_0_2 = fun _ _ -> OrderedType.LT in
    let _evar_0_3 = fun _ _ _ -> OrderedType.LT in
    let _evar_0_4 = fun _ _ _ -> OrderedType.LT in
    (match e2 with
     | HEvar t0 -> _evar_0_0 t0
     | HEconst b -> _evar_0_1 b
     | HEunop (e, h) -> _evar_0_2 e h
     | HEbinop (e, h, h0) -> _evar_0_3 e h h0
     | HEite (h, h0, h1) -> _evar_0_4 h h0 h1)
  in
  let _evar_0_1 = fun op1 e3 ->
    let _evar_0_1 = fun _ -> OrderedType.GT in
    let _evar_0_2 = fun _ -> OrderedType.GT in
    let _evar_0_3 = fun op2 e4 ->
      let _evar_0_3 = fun _ ->
        let _evar_0_3 = fun _ -> OrderedType.LT in
        let _evar_0_4 = fun _ -> OrderedType.EQ in
        let _evar_0_5 = fun _ -> OrderedType.GT in
        (match hexp_compare e3 e4 with
         | OrderedType.LT -> _evar_0_3 __
         | OrderedType.EQ -> _evar_0_4 __
         | OrderedType.GT -> _evar_0_5 __)
      in
      let _evar_0_4 = fun _ ->
        let _evar_0_4 = fun _ -> OrderedType.LT in
        let _evar_0_5 = fun _ -> OrderedType.GT in
        if QFBV.QFBV.eunop_ltn op1 op2 then _evar_0_4 __ else _evar_0_5 __
      in
      if eq_op QFBV.eunop_eqType (Obj.magic op1) (Obj.magic op2)
      then _evar_0_3 __
      else _evar_0_4 __
    in
    let _evar_0_4 = fun _ _ _ -> OrderedType.LT in
    let _evar_0_5 = fun _ _ _ -> OrderedType.LT in
    (match e2 with
     | HEvar t0 -> _evar_0_1 t0
     | HEconst b -> _evar_0_2 b
     | HEunop (e, h) -> _evar_0_3 e h
     | HEbinop (e, h, h0) -> _evar_0_4 e h h0
     | HEite (h, h0, h1) -> _evar_0_5 h h0 h1)
  in
  let _evar_0_2 = fun op1 e3 e4 ->
    let _evar_0_2 = fun _ -> OrderedType.GT in
    let _evar_0_3 = fun _ -> OrderedType.GT in
    let _evar_0_4 = fun _ _ -> OrderedType.GT in
    let _evar_0_5 = fun op2 e5 e6 ->
      let _evar_0_5 = fun _ ->
        let _evar_0_5 = fun _ -> OrderedType.LT in
        let _evar_0_6 = fun _ ->
          let _evar_0_6 = fun _ -> OrderedType.LT in
          let _evar_0_7 = fun _ -> OrderedType.EQ in
          let _evar_0_8 = fun _ -> OrderedType.GT in
          (match hexp_compare e4 e6 with
           | OrderedType.LT -> _evar_0_6 __
           | OrderedType.EQ -> _evar_0_7 __
           | OrderedType.GT -> _evar_0_8 __)
        in
        let _evar_0_7 = fun _ -> OrderedType.GT in
        (match hexp_compare e3 e5 with
         | OrderedType.LT -> _evar_0_5 __
         | OrderedType.EQ -> _evar_0_6 __
         | OrderedType.GT -> _evar_0_7 __)
      in
      let _evar_0_6 = fun _ ->
        let _evar_0_6 = fun _ -> OrderedType.LT in
        let _evar_0_7 = fun _ -> OrderedType.GT in
        if QFBV.QFBV.ebinop_ltn op1 op2 then _evar_0_6 __ else _evar_0_7 __
      in
      if eq_op QFBV.ebinop_eqType (Obj.magic op1) (Obj.magic op2)
      then _evar_0_5 __
      else _evar_0_6 __
    in
    let _evar_0_6 = fun _ _ _ -> OrderedType.LT in
    (match e2 with
     | HEvar t0 -> _evar_0_2 t0
     | HEconst b -> _evar_0_3 b
     | HEunop (e, h) -> _evar_0_4 e h
     | HEbinop (e, h, h0) -> _evar_0_5 e h h0
     | HEite (h, h0, h1) -> _evar_0_6 h h0 h1)
  in
  let _evar_0_3 = fun b1 e3 e4 ->
    let _evar_0_3 = fun _ -> OrderedType.GT in
    let _evar_0_4 = fun _ -> OrderedType.GT in
    let _evar_0_5 = fun _ _ -> OrderedType.GT in
    let _evar_0_6 = fun _ _ _ -> OrderedType.GT in
    let _evar_0_7 = fun b2 e5 e6 ->
      let _evar_0_7 = fun _ -> OrderedType.LT in
      let _evar_0_8 = fun _ ->
        let _evar_0_8 = fun _ -> OrderedType.LT in
        let _evar_0_9 = fun _ ->
          let _evar_0_9 = fun _ -> OrderedType.LT in
          let _evar_0_10 = fun _ -> OrderedType.EQ in
          let _evar_0_11 = fun _ -> OrderedType.GT in
          (match hexp_compare e4 e6 with
           | OrderedType.LT -> _evar_0_9 __
           | OrderedType.EQ -> _evar_0_10 __
           | OrderedType.GT -> _evar_0_11 __)
        in
        let _evar_0_10 = fun _ -> OrderedType.GT in
        (match hexp_compare e3 e5 with
         | OrderedType.LT -> _evar_0_8 __
         | OrderedType.EQ -> _evar_0_9 __
         | OrderedType.GT -> _evar_0_10 __)
      in
      let _evar_0_9 = fun _ -> OrderedType.GT in
      (match hbexp_compare b1 b2 with
       | OrderedType.LT -> _evar_0_7 __
       | OrderedType.EQ -> _evar_0_8 __
       | OrderedType.GT -> _evar_0_9 __)
    in
    (match e2 with
     | HEvar t0 -> _evar_0_3 t0
     | HEconst b -> _evar_0_4 b
     | HEunop (e, h) -> _evar_0_5 e h
     | HEbinop (e, h, h0) -> _evar_0_6 e h h0
     | HEite (h, h0, h1) -> _evar_0_7 h h0 h1)
  in
  (match e1 with
   | HEvar t0 -> _evar_0_ t0
   | HEconst b -> _evar_0_0 b
   | HEunop (e, h) -> _evar_0_1 e h
   | HEbinop (e, h, h0) -> _evar_0_2 e h h0
   | HEite (h, h0, h1) -> _evar_0_3 h h0 h1)

(** val hashed_bexp_compare :
    hashed_bexp -> hashed_bexp -> hashed_bexp OrderedType.coq_Compare **)

and hashed_bexp_compare e1 e2 =
  let _evar_0_ =
    let _evar_0_ = OrderedType.EQ in
    let _evar_0_0 = OrderedType.LT in
    let _evar_0_1 = fun _ _ _ -> OrderedType.LT in
    let _evar_0_2 = fun _ -> OrderedType.LT in
    let _evar_0_3 = fun _ _ -> OrderedType.LT in
    let _evar_0_4 = fun _ _ -> OrderedType.LT in
    (match e2 with
     | HBfalse -> _evar_0_
     | HBtrue -> _evar_0_0
     | HBbinop (b, h, h0) -> _evar_0_1 b h h0
     | HBlneg h -> _evar_0_2 h
     | HBconj (h, h0) -> _evar_0_3 h h0
     | HBdisj (h, h0) -> _evar_0_4 h h0)
  in
  let _evar_0_0 =
    let _evar_0_0 = OrderedType.GT in
    let _evar_0_1 = OrderedType.EQ in
    let _evar_0_2 = fun _ _ _ -> OrderedType.LT in
    let _evar_0_3 = fun _ -> OrderedType.LT in
    let _evar_0_4 = fun _ _ -> OrderedType.LT in
    let _evar_0_5 = fun _ _ -> OrderedType.LT in
    (match e2 with
     | HBfalse -> _evar_0_0
     | HBtrue -> _evar_0_1
     | HBbinop (b, h, h0) -> _evar_0_2 b h h0
     | HBlneg h -> _evar_0_3 h
     | HBconj (h, h0) -> _evar_0_4 h h0
     | HBdisj (h, h0) -> _evar_0_5 h h0)
  in
  let _evar_0_1 = fun op1 e3 e4 ->
    let _evar_0_1 = OrderedType.GT in
    let _evar_0_2 = OrderedType.GT in
    let _evar_0_3 = fun op2 e5 e6 ->
      let _evar_0_3 = fun _ ->
        let _evar_0_3 = fun _ -> OrderedType.LT in
        let _evar_0_4 = fun _ ->
          let _evar_0_4 = fun _ -> OrderedType.LT in
          let _evar_0_5 = fun _ -> OrderedType.EQ in
          let _evar_0_6 = fun _ -> OrderedType.GT in
          (match hexp_compare e4 e6 with
           | OrderedType.LT -> _evar_0_4 __
           | OrderedType.EQ -> _evar_0_5 __
           | OrderedType.GT -> _evar_0_6 __)
        in
        let _evar_0_5 = fun _ -> OrderedType.GT in
        (match hexp_compare e3 e5 with
         | OrderedType.LT -> _evar_0_3 __
         | OrderedType.EQ -> _evar_0_4 __
         | OrderedType.GT -> _evar_0_5 __)
      in
      let _evar_0_4 = fun _ ->
        let _evar_0_4 = fun _ -> OrderedType.LT in
        let _evar_0_5 = fun _ -> OrderedType.GT in
        if QFBV.QFBV.bbinop_ltn op1 op2 then _evar_0_4 __ else _evar_0_5 __
      in
      if eq_op QFBV.bbinop_eqType (Obj.magic op1) (Obj.magic op2)
      then _evar_0_3 __
      else _evar_0_4 __
    in
    let _evar_0_4 = fun _ -> OrderedType.LT in
    let _evar_0_5 = fun _ _ -> OrderedType.LT in
    let _evar_0_6 = fun _ _ -> OrderedType.LT in
    (match e2 with
     | HBfalse -> _evar_0_1
     | HBtrue -> _evar_0_2
     | HBbinop (b, h, h0) -> _evar_0_3 b h h0
     | HBlneg h -> _evar_0_4 h
     | HBconj (h, h0) -> _evar_0_5 h h0
     | HBdisj (h, h0) -> _evar_0_6 h h0)
  in
  let _evar_0_2 = fun e3 ->
    let _evar_0_2 = OrderedType.GT in
    let _evar_0_3 = OrderedType.GT in
    let _evar_0_4 = fun _ _ _ -> OrderedType.GT in
    let _evar_0_5 = fun e4 ->
      let _evar_0_5 = fun _ -> OrderedType.LT in
      let _evar_0_6 = fun _ -> OrderedType.EQ in
      let _evar_0_7 = fun _ -> OrderedType.GT in
      (match hbexp_compare e3 e4 with
       | OrderedType.LT -> _evar_0_5 __
       | OrderedType.EQ -> _evar_0_6 __
       | OrderedType.GT -> _evar_0_7 __)
    in
    let _evar_0_6 = fun _ _ -> OrderedType.LT in
    let _evar_0_7 = fun _ _ -> OrderedType.LT in
    (match e2 with
     | HBfalse -> _evar_0_2
     | HBtrue -> _evar_0_3
     | HBbinop (b, h, h0) -> _evar_0_4 b h h0
     | HBlneg h -> _evar_0_5 h
     | HBconj (h, h0) -> _evar_0_6 h h0
     | HBdisj (h, h0) -> _evar_0_7 h h0)
  in
  let _evar_0_3 = fun e3 e4 ->
    let _evar_0_3 = OrderedType.GT in
    let _evar_0_4 = OrderedType.GT in
    let _evar_0_5 = fun _ _ _ -> OrderedType.GT in
    let _evar_0_6 = fun _ -> OrderedType.GT in
    let _evar_0_7 = fun e5 e6 ->
      let _evar_0_7 = fun _ -> OrderedType.LT in
      let _evar_0_8 = fun _ ->
        let _evar_0_8 = fun _ -> OrderedType.LT in
        let _evar_0_9 = fun _ -> OrderedType.EQ in
        let _evar_0_10 = fun _ -> OrderedType.GT in
        (match hbexp_compare e4 e6 with
         | OrderedType.LT -> _evar_0_8 __
         | OrderedType.EQ -> _evar_0_9 __
         | OrderedType.GT -> _evar_0_10 __)
      in
      let _evar_0_9 = fun _ -> OrderedType.GT in
      (match hbexp_compare e3 e5 with
       | OrderedType.LT -> _evar_0_7 __
       | OrderedType.EQ -> _evar_0_8 __
       | OrderedType.GT -> _evar_0_9 __)
    in
    let _evar_0_8 = fun _ _ -> OrderedType.LT in
    (match e2 with
     | HBfalse -> _evar_0_3
     | HBtrue -> _evar_0_4
     | HBbinop (b, h, h0) -> _evar_0_5 b h h0
     | HBlneg h -> _evar_0_6 h
     | HBconj (h, h0) -> _evar_0_7 h h0
     | HBdisj (h, h0) -> _evar_0_8 h h0)
  in
  let _evar_0_4 = fun e3 e4 ->
    let _evar_0_4 = OrderedType.GT in
    let _evar_0_5 = OrderedType.GT in
    let _evar_0_6 = fun _ _ _ -> OrderedType.GT in
    let _evar_0_7 = fun _ -> OrderedType.GT in
    let _evar_0_8 = fun _ _ -> OrderedType.GT in
    let _evar_0_9 = fun e5 e6 ->
      let _evar_0_9 = fun _ -> OrderedType.LT in
      let _evar_0_10 = fun _ ->
        let _evar_0_10 = fun _ -> OrderedType.LT in
        let _evar_0_11 = fun _ -> OrderedType.EQ in
        let _evar_0_12 = fun _ -> OrderedType.GT in
        (match hbexp_compare e4 e6 with
         | OrderedType.LT -> _evar_0_10 __
         | OrderedType.EQ -> _evar_0_11 __
         | OrderedType.GT -> _evar_0_12 __)
      in
      let _evar_0_11 = fun _ -> OrderedType.GT in
      (match hbexp_compare e3 e5 with
       | OrderedType.LT -> _evar_0_9 __
       | OrderedType.EQ -> _evar_0_10 __
       | OrderedType.GT -> _evar_0_11 __)
    in
    (match e2 with
     | HBfalse -> _evar_0_4
     | HBtrue -> _evar_0_5
     | HBbinop (b, h, h0) -> _evar_0_6 b h h0
     | HBlneg h -> _evar_0_7 h
     | HBconj (h, h0) -> _evar_0_8 h h0
     | HBdisj (h, h0) -> _evar_0_9 h h0)
  in
  (match e1 with
   | HBfalse -> _evar_0_
   | HBtrue -> _evar_0_0
   | HBbinop (b, h, h0) -> _evar_0_1 b h h0
   | HBlneg h -> _evar_0_2 h
   | HBconj (h, h0) -> _evar_0_3 h h0
   | HBdisj (h, h0) -> _evar_0_4 h h0)

(** val hexp_compare : hexp -> hexp -> hexp OrderedType.coq_Compare **)

and hexp_compare e1 e2 =
  let _evar_0_ = fun e3 h1 ->
    let _evar_0_ = fun e4 h2 ->
      let _evar_0_ = fun _ -> OrderedType.LT in
      let _evar_0_0 = fun _ ->
        let _evar_0_0 = fun _ ->
          let _evar_0_0 = fun _ -> OrderedType.LT in
          let _evar_0_1 = fun _ -> OrderedType.EQ in
          let _evar_0_2 = fun _ -> OrderedType.GT in
          (match hashed_exp_compare e3 e4 with
           | OrderedType.LT -> _evar_0_0 __
           | OrderedType.EQ -> _evar_0_1 __
           | OrderedType.GT -> _evar_0_2 __)
        in
        let _evar_0_1 = fun _ -> OrderedType.GT in
        if eq_op coq_Z_eqType h1 h2 then _evar_0_0 __ else _evar_0_1 __
      in
      if Z.ltb (Obj.magic h1) (Obj.magic h2)
      then _evar_0_ __
      else _evar_0_0 __
    in
    let Coq_epair (h, z) = e2 in Obj.magic _evar_0_ h z
  in
  let Coq_epair (h, z) = e1 in Obj.magic _evar_0_ h z

(** val hbexp_compare : hbexp -> hbexp -> hbexp OrderedType.coq_Compare **)

and hbexp_compare e1 e2 =
  let _evar_0_ = fun e3 h1 ->
    let _evar_0_ = fun e4 h2 ->
      let _evar_0_ = fun _ -> OrderedType.LT in
      let _evar_0_0 = fun _ ->
        let _evar_0_0 = fun _ ->
          let _evar_0_0 = fun _ -> OrderedType.LT in
          let _evar_0_1 = fun _ -> OrderedType.EQ in
          let _evar_0_2 = fun _ -> OrderedType.GT in
          (match hashed_bexp_compare e3 e4 with
           | OrderedType.LT -> _evar_0_0 __
           | OrderedType.EQ -> _evar_0_1 __
           | OrderedType.GT -> _evar_0_2 __)
        in
        let _evar_0_1 = fun _ -> OrderedType.GT in
        if eq_op coq_Z_eqType h1 h2 then _evar_0_0 __ else _evar_0_1 __
      in
      if Z.ltb (Obj.magic h1) (Obj.magic h2)
      then _evar_0_ __
      else _evar_0_0 __
    in
    let Coq_bpair (h, z) = e2 in Obj.magic _evar_0_ h z
  in
  let Coq_bpair (h, z) = e1 in Obj.magic _evar_0_ h z

module HexpOrderMinimal =
 struct
  (** val t : Equality.coq_type **)

  let t =
    hexp_eqType

  (** val eqn : Equality.sort -> Equality.sort -> bool **)

  let eqn e1 e2 =
    eq_op t e1 e2

  (** val ltn : Equality.sort -> Equality.sort -> bool **)

  let ltn e1 e2 =
    hexp_ltn (Obj.magic e1) (Obj.magic e2)

  (** val compare :
      Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare **)

  let compare x y =
    Obj.magic hexp_compare x y
 end

module HbexpOrderMinimal =
 struct
  (** val t : Equality.coq_type **)

  let t =
    hbexp_eqType

  (** val eqn : Equality.sort -> Equality.sort -> bool **)

  let eqn e1 e2 =
    eq_op t e1 e2

  (** val ltn : Equality.sort -> Equality.sort -> bool **)

  let ltn e1 e2 =
    hbexp_ltn (Obj.magic e1) (Obj.magic e2)

  (** val compare :
      Equality.sort -> Equality.sort -> Equality.sort OrderedType.coq_Compare **)

  let compare x y =
    Obj.magic hbexp_compare x y
 end

module HexpOrder = SsrOrder.MakeSsrOrder(HexpOrderMinimal)

module HbexpOrder = SsrOrder.MakeSsrOrder(HbexpOrderMinimal)
