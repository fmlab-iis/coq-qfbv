
(** Syntax *)

type numeral = Z.t

type decimal = string

(* A hexadecimal number is a string with MSB at the beginning *)
type hex = string

(* A binary number is a string of 0's and 1's with MSB at the head *)
type binary = string

type symbol = string

type spec_constant =
  | CNumeral of numeral
  | CDecimal of decimal
  | CHexDecimal of hex
  | CBinary of binary
  | CString of string

(* A keyword always starts with a ":" *)
type keyword = string

type attribute =
  | AKeyword of keyword
  | AConstant of keyword * spec_constant
  | ASymbol of keyword * symbol

type solver_option =
  | OKeyword of keyword
  | OConstant of keyword * spec_constant
  | OSymbol of keyword * symbol

type index =
  | INumeral of numeral
  | ISymbol of symbol

type identifier =
  | ISimple of symbol                             (* Simple Identifier *)
  | IIndexed of symbol * index list               (* Indexed Identifier *)

type sort =
  | SIdentifier of identifier
  | SApplication of identifier * sort list

type qual_identifier =
  | QIdentifier of identifier
  | QAnnotated of identifier * sort

type var_binding = symbol * term

and term =
  | TConstant of spec_constant
  | TVariable of qual_identifier
  | TApplication of qual_identifier * term list
  | TLet of var_binding list * term

type sorted_var = symbol * sort

type command =
  | CSetLogic of symbol
  | CSetInfo of attribute
  | CSetOption of solver_option
  | CDeclareFun of symbol * sort list * sort
  | CDefineFun of symbol * sorted_var list * sort * term
  | CAssert of term
  | CCheckSat
  | CExit
  | CComment of string

type script = command list

type file = script



(** String outputs *)

let string_of_numeral = Z.to_string

let string_of_decimal d = d

let string_of_hex h = h

let string_of_binary bin = bin

let string_of_symbol s = s

let string_of_spec_constant c =
  match c with
  | CNumeral n -> string_of_numeral n
  | CDecimal d -> string_of_decimal d
  | CHexDecimal h -> "#x" ^ string_of_hex h
  | CBinary b -> "#b" ^ string_of_binary b
  | CString s -> "\"" ^ s ^ "\""

let string_of_keyword k = k

let string_of_attribute a =
  match a with
  | AKeyword k -> string_of_keyword k
  | AConstant (k, c) -> string_of_keyword k ^ " " ^ string_of_spec_constant c
  | ASymbol (k, s) -> string_of_keyword k ^ " " ^ string_of_symbol s

let string_of_solver_option o =
  match o with
  | OKeyword k -> string_of_keyword k
  | OConstant (k, c) -> string_of_keyword k ^ " " ^ string_of_spec_constant c
  | OSymbol (k, s) -> string_of_keyword k ^ " " ^ string_of_symbol s

let string_of_index i =
  match i with
  | INumeral n -> string_of_numeral n
  | ISymbol s -> string_of_symbol s

let string_of_identifier i =
  match i with
  | ISimple s -> string_of_symbol s
  | IIndexed (s, is) -> "(_ " ^ string_of_symbol s ^ " " ^ String.concat " " (List.map string_of_index is) ^ ")"

let rec string_of_sort s =
  match s with
  | SIdentifier i -> string_of_identifier i
  | SApplication (i, ss) -> "(" ^ string_of_identifier i ^ " " ^ String.concat " " (List.map string_of_sort ss) ^ ")"

let string_of_qual_identifier i =
  match i with
  | QIdentifier i -> string_of_identifier i
  | QAnnotated (i, s) -> "(as " ^ string_of_identifier i ^ " " ^ string_of_sort s ^ ")"

let rec string_of_var_binding b =
  "(" ^ string_of_symbol (fst b) ^ " " ^ string_of_term (snd b) ^ ")"

and string_of_term t =
  match t with
  | TConstant sc -> string_of_spec_constant sc
  | TVariable qi -> string_of_qual_identifier qi
  | TApplication (qi, ts) -> "(" ^ string_of_qual_identifier qi ^ " " ^ String.concat " " (List.rev (List.rev_map string_of_term ts)) ^ ")"
  | TLet (bs, t) -> "(let (" ^ String.concat " " (List.rev (List.rev_map string_of_var_binding bs)) ^ ") " ^ string_of_term t ^ ")"

let string_of_sorted_var sv =
  "(" ^ string_of_symbol (fst sv) ^ " " ^ string_of_sort (snd sv) ^ ")"

let string_of_command c =
  match c with
  | CSetLogic s -> "(set-logic " ^ string_of_symbol s ^ ")"
  | CSetInfo a -> "(set-info " ^ string_of_attribute a ^ ")"
  | CSetOption o -> "(set-option " ^ string_of_solver_option o ^ ")"
  | CDeclareFun (fn, fargs, fsort) -> "(declare-fun " ^ string_of_symbol fn
                                      ^ " (" ^ String.concat " " (List.map string_of_sort fargs) ^ ") "
                                      ^ string_of_sort fsort ^ ")"
  | CDefineFun (fn, fargs, fsort, fterm) -> "(define-fun " ^ string_of_symbol fn
                                            ^ " (" ^ String.concat " " (List.map string_of_sorted_var fargs) ^ ") "
                                            ^ string_of_sort fsort ^ " " ^ string_of_term fterm ^ ")"
  | CAssert t -> "(assert " ^ string_of_term t ^ ")"
  | CCheckSat -> "(check-sat)"
  | CExit -> "(exit)"
  | CComment s -> ";" ^ s

let string_of_script s = String.concat "\n" (List.rev (List.rev_map string_of_command s))

let string_of_file = string_of_script



let rec pp_var_binding out (v, t) =
  output_string out "(";
  output_string out (string_of_symbol v);
  output_string out " ";
  pp_term out t;
  output_string out ")"

and pp_term out term =
  match term with
  | TConstant sc -> output_string out (string_of_spec_constant sc)
  | TVariable qi -> output_string out (string_of_qual_identifier qi)
  | TApplication (qi, ts) -> output_string out "(";
                             output_string out (string_of_qual_identifier qi);
                             List.iter (fun t -> output_string out " "; pp_term out t) ts;
                             output_string out ")"
  | TLet (bs, t) -> output_string out "(let (";
                    List.iter (fun vb -> pp_var_binding out vb; output_string out " ") bs;
                    output_string out ") ";
                    pp_term out t;
                    output_string out ")"

let pp_command out c =
  match c with
  | CSetLogic s -> output_string out "(set-logic "; output_string out (string_of_symbol s); output_string out ")"
  | CSetInfo a -> output_string out "(set-info "; output_string out (string_of_attribute a); output_string out ")"
  | CSetOption o -> output_string out "(set-option "; output_string out (string_of_solver_option o); output_string out ")"
  | CDeclareFun (fn, fargs, fsort) ->
     output_string out "(declare-fun ";
     output_string out (string_of_symbol fn);
     output_string out " (";
     output_string out (String.concat " " (List.map string_of_sort fargs));
     output_string out ") ";
     output_string out (string_of_sort fsort);
     output_string out ")";
  | CDefineFun (fn, fargs, fsort, fterm) ->
     output_string out "(define-fun ";
     output_string out (string_of_symbol fn);
     output_string out " (";
     output_string out (String.concat " " (List.map string_of_sorted_var fargs));
     output_string out ") ";
     output_string out (string_of_sort fsort);
     output_string out " ";
     pp_term out fterm;
     output_string out ")";
  | CAssert t -> output_string out "(assert "; pp_term out t; output_string out ")"
  | CCheckSat -> output_string out "(check-sat)"
  | CExit -> output_string out "(exit)"
  | CComment s -> output_string out ";"; output_string out s

let pp_script out script = List.iter (fun c -> pp_command out c; output_string out "\n") script

let pp_file = pp_script



(** Some predefined symbols *)

let fn_not = "not"
let fn_imp = "=>"
let fn_and = "and"
let fn_or = "or"
let fn_xor = "xor"
let fn_eq = "="
let fn_distinct = "distinct"
let fn_ite = "ite"

let fn_concat = "concat"
let fn_extract = "extract"
let fn_bvnot = "bvnot"
let fn_bvand = "bvand"
let fn_bvor = "bvor"
let fn_bvneg = "bvneg"
let fn_bvadd = "bvadd"
let fn_bvmul = "bvmul"
let fn_bvudiv = "bvudiv"
let fn_bvurem = "bvurem"
let fn_bvshl = "bvshl"
let fn_bvlshr = "bvlshr"
let fn_bvult = "bvult"

let fn_bvnand = "bvnand"
let fn_bvnor = "bvnor"
let fn_bvxor = "bvxor"
let fn_bvxnor = "bvxnor"
let fn_bvcomp = "bvcomp"
let fn_bvsub = "bvsub"
let fn_bvsdiv = "bvsdiv"
let fn_bvsrem = "bvsrem"
let fn_bvsmod = "bvsmod"
let fn_bvashr = "bvashr"
let fn_repeat = "repeat"
let fn_zero_extend = "zero_extend"
let fn_sign_extend = "sign_extend"
let fn_rotate_left = "rotate_left"
let fn_rotate_right = "rotate_right"
let fn_bvule = "bvule"
let fn_bvugt = "bvugt"
let fn_bvuge = "bvuge"
let fn_bvslt = "bvslt"
let fn_bvsle = "bvsle"
let fn_bvsgt = "bvsgt"
let fn_bvsge = "bvsge"



(** Utility functions *)

let bool_type_name = "Bool"

let explode s = List.init (String.length s) (String.get s)

let binary_as_list str =
  List.map (fun c -> if c = '0' then false else true) (explode str)

let symbol_of_identifier i =
  match i with
  | ISimple s
    | IIndexed (s, _) -> s

let symbol_of_qual_identifier qi =
  match qi with
  | QIdentifier i
    | QAnnotated (i, _) -> symbol_of_identifier i

let is_symbol_in_var_bindings (v : symbol) (vbs : var_binding list) : bool =
  List.mem v (fst (List.split vbs))

let rec subst_term (v : symbol) (p : term) (t : term) : term =
  match t with
  | TConstant _ -> t
  | TVariable qi -> if symbol_of_qual_identifier qi = v then p
                    else t
  | TApplication (qi, ts) -> TApplication (qi, List.rev (List.rev_map (subst_term v p) ts))
  | TLet (vbs, t') ->
     let (bounded, vbs_rev) = List.fold_left (
                                  fun (bounded, res) (s, t) ->
                                  if bounded || v = s then (true, (s, t)::res)
                                  else (false, (s, subst_term v p t)::res)
                                ) (false, []) vbs in
     if bounded then TLet (List.rev vbs_rev, t')
     else TLet (List.rev vbs_rev, subst_term v p t')

let is_eq_term t : bool =
  match t with
  | TApplication (QIdentifier (ISimple v), _) when v = fn_eq -> true
  | _ -> false

let make_bitvec_sort n : sort = SIdentifier (IIndexed ("BitVec", [INumeral n]))
let make_var vn : term = TVariable (QIdentifier (ISimple vn))
let true_t : term = make_var "true"
let false_t : term = make_var "false"
let make_binary_constant b : term = TConstant (CBinary b)
(* n: number, w: bit-width*)
let make_bv n w : term = TVariable (QIdentifier (IIndexed ("bv" ^ Z.to_string n, [INumeral w])))
let make_unop op t : term = TApplication (QIdentifier (ISimple op), [t])
let make_binop op t1 t2 : term = TApplication (QIdentifier (ISimple op), [t1; t2])
let make_op op ts : term = TApplication (QIdentifier (ISimple op), ts)

let make_not t : term = make_unop fn_not t
let make_imp t1 t2 : term = make_binop fn_imp t1 t2
let make_and t1 t2 : term = make_binop fn_and t1 t2
let make_ands ts : term =
  match ts with
  | [] -> false_t
  | t::[] -> t
  | _ -> make_op fn_and ts
let make_or t1 t2 : term = make_binop fn_or t1 t2
let make_ors ts : term =
  match ts with
  | [] -> true_t
  | t::[] -> t
  | _ -> make_op fn_or ts
let make_xor t1 t2 : term = make_binop fn_xor t1 t2
let make_eq t1 t2 : term = make_binop fn_eq t1 t2
let make_distinct t1 t2 : term = make_binop fn_distinct t1 t2
let make_distincts ts : term =
  match ts with
  | [] -> true_t
  | t::[] -> true_t
  | _ -> make_op fn_distinct ts
let make_ite b t1 t2 : term = make_op fn_ite [b; t1; t2]

let make_concat t1 t2 : term = make_binop fn_concat t1 t2
let make_extract i j t : term = TApplication (QIdentifier (IIndexed (fn_extract, (INumeral i)::(INumeral j)::[])), [t])
let make_bvnot t : term = make_unop fn_bvnot t
let make_bvand t1 t2 : term = make_binop fn_bvand t1 t2
let make_bvands ts : term =
  let rec helper res ts =
    match ts with
    | [] -> res
    | t::tl -> helper (make_bvand res t) tl in
  match ts with
  | [] -> failwith("The arguments passed to make_bvands must be nonempty.")
  | t::ts -> helper t ts
let make_bvor t1 t2 : term = make_binop fn_bvor t1 t2
let make_bvors ts : term =
  let rec helper res ts =
    match ts with
    | [] -> res
    | t::tl -> helper (make_bvor res t) tl in
  match ts with
  | [] -> failwith("The arguments passed to make_bvors must be nonempty.")
  | t::ts -> helper t ts
let make_bvneg t : term = make_unop fn_bvneg t
let make_bvadd t1 t2 : term = make_binop fn_bvadd t1 t2
let make_bvadds ts : term = make_op fn_bvadd ts
let make_bvmul t1 t2 : term = make_binop fn_bvmul t1 t2
let make_bvudiv t1 t2 : term = make_binop fn_bvudiv t1 t2
let make_bvurem t1 t2 : term = make_binop fn_bvurem t1 t2
let make_bvshl t1 t2 : term = make_binop fn_bvshl t1 t2
let make_bvlshr t1 t2 : term = make_binop fn_bvlshr t1 t2
let make_bvult t1 t2 : term = make_binop fn_bvult t1 t2

let make_bvnand t1 t2 : term = make_binop fn_bvnand t1 t2
let make_bvnor t1 t2 : term = make_binop fn_bvnor t1 t2
let make_bvxor t1 t2 : term = make_binop fn_bvxor t1 t2
let make_bvxors ts : term =
  let rec helper res ts =
    match ts with
    | [] -> res
    | t::tl -> helper (make_bvxor res t) tl in
  match ts with
  | [] -> failwith("The arguments passed to make_bvxors must be nonempty.")
  | t::ts -> helper t ts
let make_bvxnor t1 t2 : term = make_binop fn_bvxnor t1 t2
let make_bvcomp t1 t2 : term = make_binop fn_bvcomp t1 t2
let make_bvsub t1 t2 : term = make_binop fn_bvsub t1 t2
let make_bvsdiv t1 t2 : term = make_binop fn_bvsdiv t1 t2
let make_bvsrem t1 t2 : term = make_binop fn_bvsrem t1 t2
let make_bvsmod t1 t2 : term = make_binop fn_bvsmod t1 t2
let make_bvashr t1 t2 : term = make_binop fn_bvashr t1 t2
let make_repeat i t : term = TApplication (QIdentifier (IIndexed (fn_repeat, (INumeral i)::[])), [t])
let make_zero_extend i t : term = TApplication (QIdentifier (IIndexed (fn_zero_extend, (INumeral i)::[])), [t])
let make_sign_extend i t : term = TApplication (QIdentifier (IIndexed (fn_sign_extend, (INumeral i)::[])), [t])
let make_rotate_left i t : term = TApplication (QIdentifier (IIndexed (fn_rotate_left, (INumeral i)::[])), [t])
let make_rotate_right i t : term = TApplication (QIdentifier (IIndexed (fn_rotate_right, (INumeral i)::[])), [t])
let make_bvule t1 t2 : term = make_binop fn_bvule t1 t2
let make_bvugt t1 t2 : term = make_binop fn_bvugt t1 t2
let make_bvuge t1 t2 : term = make_binop fn_bvuge t1 t2
let make_bvslt t1 t2 : term = make_binop fn_bvslt t1 t2
let make_bvsle t1 t2 : term = make_binop fn_bvsle t1 t2
let make_bvsgt t1 t2 : term = make_binop fn_bvsgt t1 t2
let make_bvsge t1 t2 : term = make_binop fn_bvsge t1 t2

let make_let vbs t : term = TLet (vbs, t)


let bin0 : term = make_binary_constant "0"
let bin1 : term = make_binary_constant "1"



(** Typing terms *)

type ttyp =
  | TBool
  | TNumeral
  | TBitVec of int

let size_of_ttyp t : int =
  match t with
  | TBool -> 1
  | TNumeral -> 0 (* ? *)
  | TBitVec n -> n

module StringOrder =
  struct
    type t = string
    let compare = Stdlib.compare
  end

module M = Map.Make(StringOrder)

(* A map from a variable symbol to its type *)
type tm = ttyp M.t

(* A map from a function symbol to its definition *)
type fm = (sorted_var list * sort * term) M.t

let ttyp_of_sort s : ttyp =
  match s with
  | SIdentifier (ISimple s) when s = bool_type_name -> TBool
  | SIdentifier (IIndexed (s, [INumeral n])) when s = "BitVec" -> TBitVec (Z.to_int n)
  | _ -> failwith ("Unsupported sort: " ^ string_of_sort s)

let ttyp_of_spec_constant sc =
  match sc with
  | CNumeral _ -> TNumeral
  | CDecimal _ -> TNumeral
  | CHexDecimal h -> TBitVec (String.length h * 4)
  | CBinary b -> TBitVec (String.length b)
  | CString _ -> TNumeral

let ttyp_of_identifier tm i : ttyp =
  match i with
  | ISimple s ->
     begin
       if s = "true" || s = "false"
       then TBool
       else
         try
           M.find s tm
         with Not_found ->
           failwith ("Undefined variable: " ^ s)
     end
  | IIndexed (s, is) ->
     if Str.string_match (Str.regexp "bv\\([0-9]+\\)") s 0
     then match is with
          | [INumeral n] -> TBitVec (Z.to_int n)
          | _ -> failwith ("Failed to determine the type of " ^ string_of_identifier i)
     else failwith ("Failed to determine the type of " ^ string_of_identifier i)

let ttyp_of_qual_identifier tm qi : ttyp =
  match qi with
  | QIdentifier i -> ttyp_of_identifier tm i
  | QAnnotated (_, s) -> ttyp_of_sort s

let rec ttyp_of_term (tm : tm) (fm : fm) (t : term) : ttyp =
  let fail () = failwith ("Failed to determine the type of " ^ string_of_term t) in
  match t with
  | TConstant sc -> ttyp_of_spec_constant sc
  | TVariable qi -> ttyp_of_qual_identifier tm qi
  | TApplication (qi, ts) -> let fn = symbol_of_qual_identifier qi in
                             begin
                               match qi, ts with
                               | QIdentifier (ISimple v), _ when v = fn_not -> TBool
                               | QIdentifier (ISimple v), _ when v = fn_imp -> TBool
                               | QIdentifier (ISimple v), _ when v = fn_and -> TBool
                               | QIdentifier (ISimple v), _ when v = fn_or -> TBool
                               | QIdentifier (ISimple v), _ when v = fn_xor -> TBool
                               | QIdentifier (ISimple v), _ when v = fn_eq -> TBool
                               | QIdentifier (ISimple v), _ when v = fn_distinct -> TBool
                               | QIdentifier (ISimple v), _::a1::a2::[] when v = fn_ite -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_concat -> (match ttyp_of_term tm fm a1, ttyp_of_term tm fm a2 with
                                                                                            | TBitVec n1, TBitVec n2 -> TBitVec (n1 + n2)
                                                                                            | TBool, TBitVec n
                                                                                              | TBitVec n, TBool -> TBitVec (n + 1)
                                                                                            | _, _ -> fail())
                               | QIdentifier (IIndexed (v, (INumeral i)::(INumeral j)::[])), a1::[] when v = fn_extract -> TBitVec (Z.to_int i - Z.to_int j + 1)
                               | QIdentifier (ISimple v), a1::[] when v = fn_bvnot -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvand -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvor -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::[] when v = fn_bvneg -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::_ when v = fn_bvadd -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvmul -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvudiv -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvurem -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvshl -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvlshr -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvult -> TBool
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvnand -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvnor -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvxor -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvxnor -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvcomp -> TBitVec 1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvsub -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvsdiv -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvsrem -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvsmod -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvashr -> ttyp_of_term tm fm a1
                               | QIdentifier (IIndexed (v, [INumeral n])), a1::[] when v = fn_repeat -> (match ttyp_of_term tm fm a1 with
                                                                                                         | TBitVec m -> TBitVec (Z.to_int n * m)
                                                                                                         | _ -> fail())
                               | QIdentifier (IIndexed (v, [INumeral n])), a1::[] when v = fn_zero_extend -> (match ttyp_of_term tm fm a1 with
                                                                                                              | TBitVec m -> TBitVec (Z.to_int n + m)
                                                                                                              | _ -> fail())
                               | QIdentifier (IIndexed (v, [INumeral n])), a1::[] when v = fn_sign_extend -> (match ttyp_of_term tm fm a1 with
                                                                                                              | TBitVec m -> TBitVec (Z.to_int n + m)
                                                                                                              | _ -> fail())
                               | QIdentifier (IIndexed (v, [INumeral n])), a1::[] when v = fn_rotate_left -> ttyp_of_term tm fm a1
                               | QIdentifier (IIndexed (v, [INumeral n])), a1::[] when v = fn_rotate_right -> ttyp_of_term tm fm a1
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvule -> TBool
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvugt -> TBool
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvuge -> TBool
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvslt -> TBool
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvsle -> TBool
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvsgt -> TBool
                               | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvsge -> TBool
                               | _, _ -> (try
                                            let (fargs, fsort, fterm) = M.find fn fm in
                                            ttyp_of_sort fsort
                                          with Not_found ->
                                            fail())
                             end
  | TLet (vbs, t') ->
     let tm' = List.fold_left (
                   fun tm (s, t) ->
                   M.add s (ttyp_of_term tm fm t) tm
                 ) tm vbs in
     ttyp_of_term tm' fm t'

let is_bool_term tm fm t =
  match ttyp_of_term tm fm t with
  | TBool -> true
  | _ -> false



(** Convert extensions to core functions *)

module SS = Set.Make(StringOrder)

let rec convert_defined_extensions_term ?skip:(ops=SS.empty) tm fm term =
  match term with
  | TConstant _ -> term
  | TVariable _ -> term
  | TApplication (QIdentifier (ISimple v), ts)
       when v = fn_distinct && not (SS.mem v ops) -> let ts = List.rev (List.rev_map (convert_defined_extensions_term ~skip:ops tm fm) ts) in
                                                     let res = List.rev (List.rev_map (
                                                                             fun es ->
                                                                             match es with
                                                                             | s::t::[] -> make_not (make_eq s t)
                                                                             | _ -> failwith("Never happen")
                                                                           ) (Util.combinations 2 ts)) in
                                                     make_ands res
  | TApplication (QIdentifier (ISimple v), s::t::[])
       when v = fn_bvnand && not (SS.mem v ops) -> let s = convert_defined_extensions_term ~skip:ops tm fm s in
                                                   let t = convert_defined_extensions_term ~skip:ops tm fm t in
                                                   make_bvnot (make_bvand s t)
  | TApplication (QIdentifier (ISimple v), s::t::[])
       when v = fn_bvnor && not (SS.mem v ops) -> let s = convert_defined_extensions_term ~skip:ops tm fm s in
                                                  let t = convert_defined_extensions_term ~skip:ops tm fm t in
                                                  make_bvnot (make_bvor s t)
  | TApplication (QIdentifier (ISimple v), s::t::[])
       when v = fn_bvxor && not (SS.mem v ops) -> let s = convert_defined_extensions_term ~skip:ops tm fm s in
                                                  let t = convert_defined_extensions_term ~skip:ops tm fm t in
                                                  make_bvor (make_bvand s (make_bvnot t)) (make_bvand (make_bvnot s) t)
  | TApplication (QIdentifier (ISimple v), s::t::[])
       when v = fn_bvxnor && not (SS.mem v ops) -> let s = convert_defined_extensions_term ~skip:ops tm fm s in
                                                   let t = convert_defined_extensions_term ~skip:ops tm fm t in
                                                   make_bvor (make_bvand s t) (make_bvand (make_bvnot s) (make_bvnot t))
  | TApplication (QIdentifier (ISimple v), s::t::[])
       when v = fn_bvcomp && not (SS.mem v ops) -> let m = size_of_ttyp (ttyp_of_term tm fm s) in
                                                   let res =
                                                     if m = 1
                                                     then (make_bvxnor s t)
                                                     else let rec helper res m =
                                                            let m_minus_one = Z.of_int (m - 1) in
                                                            let b = (make_bvxnor
                                                                       (make_extract m_minus_one m_minus_one s)
                                                                       (make_extract m_minus_one m_minus_one t)) in
                                                            if m <= 1
                                                            then b::res
                                                            else helper (b::res) (m - 1) in
                                                          make_bvands (List.rev (helper [] m)) in
                                                   convert_defined_extensions_term ~skip:ops tm fm res
  | TApplication (QIdentifier (ISimple v), s::t::[])
       when v = fn_bvsub && not (SS.mem v ops) -> let s = convert_defined_extensions_term ~skip:ops tm fm s in
                                                  let t = convert_defined_extensions_term ~skip:ops tm fm t in
                                                  make_bvadd s (make_bvneg t)
  | TApplication (QIdentifier (ISimple v), s::t::[])
       when v = fn_bvsdiv && not (SS.mem v ops) -> let m = size_of_ttyp (ttyp_of_term tm fm s) in
                                                   let m_minus_one = Z.of_int (m - 1) in
                                                   let msb_s = "|__msb_s__|" in
                                                   let msb_t = "|__msb_t__|" in
                                                   let s = convert_defined_extensions_term ~skip:ops tm fm s in
                                                   let t = convert_defined_extensions_term ~skip:ops tm fm t in
                                                   make_let [(msb_s, make_extract m_minus_one m_minus_one s);
                                                             (msb_t, make_extract m_minus_one m_minus_one t)]
                                                     (make_ite (make_and (make_eq (make_var msb_s) bin0) (make_eq (make_var msb_t) bin0))
                                                        (make_bvudiv s t)
                                                        (make_ite (make_and (make_eq (make_var msb_s) bin1) (make_eq (make_var msb_t) bin0))
                                                           (make_bvneg (make_bvudiv (make_bvneg s) t))
                                                           (make_ite (make_and (make_eq (make_var msb_s) bin0) (make_eq (make_var msb_t) bin1))
                                                              (make_bvneg (make_bvudiv s (make_bvneg t)))
                                                              (make_bvudiv (make_bvneg s) (make_bvneg t)))))
  | TApplication (QIdentifier (ISimple v), s::t::[])
       when v = fn_bvsrem && not (SS.mem v ops) -> let m = size_of_ttyp (ttyp_of_term tm fm s) in
                                                   let m_minus_one = Z.of_int (m - 1) in
                                                   let msb_s = "|__msb_s__|" in
                                                   let msb_t = "|__msb_t__|" in
                                                   let s = convert_defined_extensions_term ~skip:ops tm fm s in
                                                   let t = convert_defined_extensions_term ~skip:ops tm fm t in
                                                   make_let [(msb_s, make_extract m_minus_one m_minus_one s);
                                                             (msb_t, make_extract m_minus_one m_minus_one t)]
                                                     (make_ite (make_and (make_eq (make_var msb_s) bin0) (make_eq (make_var msb_t) bin0))
                                                        (make_bvurem s t)
                                                        (make_ite (make_and (make_eq (make_var msb_s) bin1) (make_eq (make_var msb_t) bin0))
                                                           (make_bvneg (make_bvurem (make_bvneg s) t))
                                                           (make_ite (make_and (make_eq (make_var msb_s) bin0) (make_eq (make_var msb_t) bin1))
                                                              (make_bvurem s (make_bvneg t))
                                                              (make_bvneg (make_bvurem (make_bvneg s) (make_bvneg t))))))
  | TApplication (QIdentifier (ISimple v), s::t::[])
       when v = fn_bvsmod && not (SS.mem v ops) -> let m = size_of_ttyp (ttyp_of_term tm fm s) in
                                                   let m_minus_one = Z.of_int (m - 1) in
                                                   let msb_s = "|__msb_s__|" in
                                                   let msb_t = "|__msb_t__|" in
                                                   let abs_s = "|__abs_s__|" in
                                                   let abs_t = "|__abs_t__|" in
                                                   let u = "|__u__|" in
                                                   let s = convert_defined_extensions_term ~skip:ops tm fm s in
                                                   let t = convert_defined_extensions_term ~skip:ops tm fm t in
                                                   make_let [(msb_s, make_extract m_minus_one m_minus_one s);
                                                             (msb_t, make_extract m_minus_one m_minus_one t)]
                                                     (make_let [(abs_s, make_ite (make_eq (make_var msb_s) bin0) s (make_bvneg s));
                                                                (abs_t, make_ite (make_eq (make_var msb_t) bin0) t (make_bvneg t))]
                                                        (make_let [(u, make_bvurem (make_var abs_s) (make_var abs_t))]
                                                           (make_ite (make_eq (make_var u) (make_bv Z.zero (Z.of_int m)))
                                                              (make_var u)
                                                              (make_ite (make_and (make_eq (make_var msb_s) bin0) (make_eq (make_var msb_t) bin0))
                                                                 (make_var u)
                                                                 (make_ite (make_and (make_eq (make_var msb_s) bin1) (make_eq (make_var msb_t) bin0))
                                                                    (make_bvadd (make_bvneg (make_var u)) t)
                                                                    (make_ite (make_and (make_eq (make_var msb_s) bin0) (make_eq (make_var msb_t) bin1))
                                                                       (make_bvadd (make_var u) t)
                                                                       (make_bvneg (make_var u))))))))
  | TApplication (QIdentifier (ISimple v), s::t::[])
       when v = fn_bvule && not (SS.mem v ops) -> let s = convert_defined_extensions_term ~skip:ops tm fm s in
                                                  let t = convert_defined_extensions_term ~skip:ops tm fm t in
                                                  make_or (make_bvult s t) (make_eq s t)
  | TApplication (QIdentifier (ISimple v), s::t::[])
       when v = fn_bvugt && not (SS.mem v ops) -> let s = convert_defined_extensions_term ~skip:ops tm fm s in
                                                  let t = convert_defined_extensions_term ~skip:ops tm fm t in
                                                  make_bvult t s
  | TApplication (QIdentifier (ISimple v), s::t::[])
       when v = fn_bvuge && not (SS.mem v ops) -> let s = convert_defined_extensions_term ~skip:ops tm fm s in
                                                  let t = convert_defined_extensions_term ~skip:ops tm fm t in
                                                  make_or (make_bvult t s) (make_eq s t)
  | TApplication (QIdentifier (ISimple v), s::t::[])
       when v = fn_bvslt && not (SS.mem v ops) -> let m = size_of_ttyp (ttyp_of_term tm fm s) in
                                                  let m_minus_one = Z.of_int (m - 1) in
                                                  let s = convert_defined_extensions_term ~skip:ops tm fm s in
                                                  let t = convert_defined_extensions_term ~skip:ops tm fm t in
                                                  make_or (make_and (make_eq (make_extract m_minus_one m_minus_one s) bin1)
                                                             (make_eq (make_extract m_minus_one m_minus_one t) bin0))
                                                    (make_and (make_eq (make_extract m_minus_one m_minus_one s) (make_extract m_minus_one m_minus_one t))
                                                       (make_bvult s t))
  | TApplication (QIdentifier (ISimple v), s::t::[])
       when v = fn_bvsle && not (SS.mem v ops) -> let m = size_of_ttyp (ttyp_of_term tm fm s) in
                                                  let m_minus_one = Z.of_int (m - 1) in
                                                  let res =
                                                    make_or (make_and (make_eq (make_extract m_minus_one m_minus_one s) bin1)
                                                               (make_eq (make_extract m_minus_one m_minus_one t) bin0))
                                                      (make_and (make_eq (make_extract m_minus_one m_minus_one s) (make_extract m_minus_one m_minus_one t))
                                                         (make_bvule s t)) in
                                                  convert_defined_extensions_term ~skip:ops tm fm res
  | TApplication (QIdentifier (ISimple v), s::t::[])
       when v = fn_bvsgt && not (SS.mem v ops) -> let res = make_bvslt t s in
                                                  convert_defined_extensions_term ~skip:ops tm fm res
  | TApplication (QIdentifier (ISimple v), s::t::[])
       when v = fn_bvsge && not (SS.mem v ops) -> let res = make_bvsle t s in
                                                  convert_defined_extensions_term ~skip:ops tm fm res
  | TApplication (QIdentifier (ISimple v), s::t::[])
       when v = fn_bvashr && not (SS.mem v ops) -> let m = size_of_ttyp (ttyp_of_term tm fm s) in
                                                   let m_minus_one = Z.of_int (m - 1) in
                                                   let s = convert_defined_extensions_term ~skip:ops tm fm s in
                                                   let t = convert_defined_extensions_term ~skip:ops tm fm t in
                                                   make_ite (make_eq (make_extract m_minus_one m_minus_one s) bin0)
                                                     (make_bvlshr s t)
                                                     (make_bvnot (make_bvlshr (make_bvnot s) t))
  | TApplication (QIdentifier (IIndexed (v, [INumeral i])), t::[])
       when v = fn_repeat && not (SS.mem v ops) -> let rec helper i =
                                                     if i <= 0 then failwith("The repeat number must be positive")
                                                     else if i = 1 then t
                                                     else make_concat t (helper (i - 1)) in
                                                   helper (Z.to_int i)
  | TApplication (QIdentifier (IIndexed (v, [INumeral i])), t::[])
       when v = fn_zero_extend && not (SS.mem v ops) -> if Z.to_int i <= 0 then t
                                                        else let res = make_concat (make_repeat i bin0) t in
                                                             convert_defined_extensions_term ~skip:ops tm fm res
  | TApplication (QIdentifier (IIndexed (v, [INumeral i])), t::[])
       when v = fn_sign_extend && not (SS.mem v ops) -> let m = size_of_ttyp (ttyp_of_term tm fm t) in
                                                        let m_minus_one = Z.of_int (m - 1) in
                                                        if Z.to_int i <= 0 then t
                                                        else let res =
                                                               make_concat (make_repeat i (make_extract m_minus_one m_minus_one t)) t in
                                                             convert_defined_extensions_term ~skip:ops tm fm res
  | TApplication (QIdentifier (IIndexed (v, [INumeral i])), t::[])
       when v = fn_rotate_left && not (SS.mem v ops) -> let m = size_of_ttyp (ttyp_of_term tm fm t) in
                                                        let m_minus_one = Z.of_int (m - 1) in
                                                        let m_minus_two = Z.of_int (m - 2) in
                                                        if Z.to_int i <= 0 then t
                                                        else if m = 1 then t
                                                        else let res =
                                                               make_rotate_left (Z.sub i Z.one)
                                                                 (make_concat
                                                                    ((make_extract m_minus_two Z.zero) t)
                                                                    ((make_extract m_minus_one m_minus_one) t)) in
                                                             convert_defined_extensions_term ~skip:ops tm fm res
  | TApplication (QIdentifier (IIndexed (v, [INumeral i])), t::[])
       when v = fn_rotate_right && not (SS.mem v ops) -> let m = size_of_ttyp (ttyp_of_term tm fm t) in
                                                         let m_minus_one = Z.of_int (m - 1) in
                                                         if Z.to_int i <= 0 then t
                                                         else if m = 1 then t
                                                         else let res =
                                                                make_rotate_right (Z.sub i Z.one)
                                                                  (make_concat
                                                                     ((make_extract Z.zero Z.zero) t)
                                                                     ((make_extract m_minus_one Z.one) t)) in
                                                              convert_defined_extensions_term ~skip:ops tm fm res
  | TApplication (fn, ts) -> TApplication (fn, List.rev (List.rev_map (convert_defined_extensions_term ~skip:ops tm fm) ts))
  | TLet (vbs, t) -> let (tm', vbs_rev) =
                       List.fold_left (
                           fun (tm, vbs_rev) (v, vt) ->
                           let ty = ttyp_of_term tm fm vt in
                           let tm' = M.add v ty tm in
                           (tm', (v, convert_defined_extensions_term ~skip:ops tm fm vt)::vbs_rev)
                         ) (tm, []) vbs in
                     let t' = convert_defined_extensions_term ~skip:ops tm' fm t in
                     TLet (List.rev vbs_rev, t')

let convert_defined_extensions_command ?skip:(ops=SS.empty) tm fm c =
  match c with
  | CSetLogic _ -> (tm, fm, c)
  | CSetInfo _ -> (tm, fm, c)
  | CSetOption _ -> (tm, fm, c)
  | CDeclareFun (fn, fargs, fsort) ->
     (* Only update maps *)
     begin
       match fargs with
       | [] -> (M.add fn (ttyp_of_sort fsort) tm, fm, c)
       | _ -> failwith("Function declaration with nonempty arguments is not supported.")
     end
  | CDefineFun (fn, fargs, fsort, fterm) ->
     begin
       match fargs with
       | [] -> let ty = ttyp_of_sort fsort in
               let tm' = M.add fn ty tm in
               let fterm' = convert_defined_extensions_term ~skip:ops tm' fm fterm in
               (tm', fm, CDefineFun (fn, fargs, fsort, fterm'))
       | _ -> let fm' = M.add fn (fargs, fsort, fterm) fm in
              let fterm' = convert_defined_extensions_term ~skip:ops tm fm' fterm in
              (tm, fm', CDefineFun (fn, fargs, fsort, fterm'))
     end
  | CAssert t -> (tm, fm, CAssert (convert_defined_extensions_term ~skip:ops tm fm t))
  | CCheckSat -> (tm, fm, c)
  | CExit -> (tm, fm, c)
  | CComment _ -> (tm, fm, c)

let convert_defined_extensions_script ?skip:(ops=SS.empty) tm fm script =
  let (tm', fm', cmds_rev) =
    List.fold_left
      (fun (tm, fm, res) c ->
        let (tm', fm', c') = convert_defined_extensions_command ~skip:ops tm fm c in
        (tm', fm', c'::res)
      ) (tm, fm, []) script in
  (tm', fm', List.rev cmds_rev)

let convert_defined_extensions_file ?skip:(ops=[fn_distinct]) file =
  let ops = List.fold_left (fun res op -> SS.add op res) SS.empty ops in
  let tm = M.empty in
  let fm = M.empty in
  let (_, _, file') = convert_defined_extensions_script ~skip:ops tm fm file in
  file'
