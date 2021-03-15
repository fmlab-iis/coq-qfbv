
open Extraction.ExtrOcamlIntConv
open Extraction.Datatypes
open Extraction.BinNums
open Extraction
open Extraction.QFBV
open Extraction.Var
open Extraction.Typ
open Extraction.TypEnv
open Extraction.NBitsDef
open Extraction.Seqs
open Extraction.QFBVHash
open Extraction.BitBlastingInit
open Extraction.BitBlastingCacheHash
open Extraction.State
open Util
open Smtlib.Ast




(** Options and exceptions *)

let option_kissat_path = ref "kissat"

let option_gratgen_path = ref "gratgen"

let option_gratchk_path = ref "gratchk"

let option_debug = ref false

let option_split_conjs = ref false

let option_expand_let = ref false

let option_verbose = ref false

let option_keep_temp_files = ref false

let option_cnf_file = ref None
let option_drat_file = ref None
let option_sat_log_file = ref None
let option_gratl_file = ref None
let option_gratp_file = ref None
let option_grat_log_file = ref None

let option_tmpdir = ref None

let tmpfile prefix suffix =
  match !option_tmpdir with
  | None -> Filename.temp_file prefix suffix
  | Some dir -> Filename.temp_file ~temp_dir:dir prefix suffix

let unlink' file = if Sys.file_exists file then Unix.unlink file

let cleanup files = if not !option_keep_temp_files then List.iter unlink' files


exception IllFormedException



(** Basic numbers conversion *)

let string_of_bits bs =
  String.concat "" (List.map (fun b -> if b then "1" else "0") (List.rev bs))

let explode s = List.init (String.length s) (String.get s)

let bits_of_z (size : int) (z : Z.t) : bits =
  let binstr =
    if z >= Z.zero then
      Z.format ("%0" ^ (string_of_int size) ^ "b") z
    else
      Z.format ("%0" ^ (string_of_int size) ^ "b")
        (Z.add (Z.pow (Z.of_int 2) size) z) in
  let rec helper i max str res =
    if i >= max then res
    else match String.get str i with
    | '0' -> helper (succ i) max str (false::res)
    | '1' -> helper (succ i) max str (true::res)
    | _ -> assert false in
  helper 0 (String.length binstr) binstr []

let pos_of_z z =
  let str = Z.format "b" z in
  let str = String.sub str 1 (String.length str - 1) in
  List.fold_left (
  fun p c ->
	if c = '1' then Coq_xI p
	else Coq_xO p) Coq_xH (explode str)

let rec z_of_pos n =
  match n with
  | Coq_xH -> Z.succ Z.zero
  | Coq_xO p -> Z.shift_left (z_of_pos p) 1
  | Coq_xI p -> Z.succ (Z.shift_left (z_of_pos p) 1)

let coq_z_of_z z =
  if Z.equal z Z.zero then Z0
  else if Z.lt z Z.zero then Zneg (pos_of_z (Z.neg z))
  else Zpos (pos_of_z z)

let z_of_coq_z n =
  match n with
  | Z0 -> Z.zero
  | Zpos p -> z_of_pos p
  | Zneg p -> Z.neg (z_of_pos p)



(** QFBV string outputs *)

let string_of_ty ty =
  match ty with
  | Tuint n
  | Tsint n -> string_of_int n

let string_of_eunop (op : QFBV.eunop) =
  match op with
  | QFBV.Unot -> "!"
  | QFBV.Uneg -> "-"
  | QFBV.Uextr (i, j) -> "extr " ^ string_of_int i ^ " " ^ string_of_int j
  | QFBV.Uhigh n -> "high " ^ string_of_int n
  | QFBV.Ulow n -> "low " ^ string_of_int n
  | QFBV.Uzext n -> "zext " ^ string_of_int n
  | QFBV.Usext n -> "sext " ^ string_of_int n
  | QFBV.Urepeat n -> "repeat " ^ string_of_int n
  | QFBV.Urotl n -> "rotate_left " ^ string_of_int n
  | QFBV.Urotr n -> "rotate_right " ^ string_of_int n

let string_of_ebinop (op : QFBV.ebinop) =
  match op with
  | QFBV.Band -> "&"
  | QFBV.Bor -> "|"
  | QFBV.Bxor -> "^"
  | QFBV.Badd -> "+"
  | QFBV.Bsub -> "-"
  | QFBV.Bmul -> "*"
  | QFBV.Bdiv -> "div"
  | QFBV.Bmod -> "mod"
  | QFBV.Bsdiv -> "sdiv"
  | QFBV.Bsrem -> "srem"
  | QFBV.Bsmod -> "smod"
  | QFBV.Bshl -> ">>"
  | QFBV.Blshr -> "<<l"
  | QFBV.Bashr -> "<<a"
  | QFBV.Bconcat -> "++"
  | QFBV.Bcomp -> "comp"

let string_of_bbinop (op : QFBV.bbinop) =
  match op with
  | QFBV.Beq -> "="
  | QFBV.Bult -> "<"
  | QFBV.Bule -> "<="
  | QFBV.Bugt -> ">"
  | QFBV.Buge -> ">="
  | QFBV.Bslt -> "<s"
  | QFBV.Bsle -> "<=s"
  | QFBV.Bsgt -> ">s"
  | QFBV.Bsge -> ">=s"
  | QFBV.Buaddo -> "uaddo"
  | QFBV.Busubo -> "usubo"
  | QFBV.Bumulo -> "umulo"
  | QFBV.Bsaddo -> "saddo"
  | QFBV.Bssubo -> "ssubo"
  | QFBV.Bsmulo -> "smulo"

let rec string_of_exp (e : QFBV.exp) : string =
  match e with
  | QFBV.Evar v -> let (vn, vi) = Obj.magic v in
                   "(" ^ string_of_int (int_of_n vn) ^ ", " ^ string_of_int (int_of_n vi) ^ ")"
  | QFBV.Econst n -> string_of_bits n
  | QFBV.Eunop (op, e) -> string_of_eunop op ^ " (" ^ string_of_exp e ^ ")"
  | QFBV.Ebinop (op, e1, e2) -> "(" ^ string_of_exp e1 ^ ") " ^ string_of_ebinop op ^ " (" ^ string_of_exp e2 ^ ")"
  | QFBV.Eite (c, e1, e2) -> "(" ^ string_of_bexp c ^ "  " ^ string_of_exp e1 ^ " : " ^ string_of_exp e2 ^ ")"
and string_of_bexp (e : QFBV.bexp) : string =
  match e with
  | QFBV.Bfalse -> "false"
  | QFBV.Btrue -> "true"
  | QFBV.Bbinop (op, e1, e2) -> "(" ^ string_of_exp e1 ^ ") " ^ string_of_bbinop op ^ " (" ^ string_of_exp e2 ^ ")"
  | QFBV.Blneg e -> "~ (" ^ string_of_bexp e ^ ")"
  | QFBV.Bconj (e1, e2) -> "(" ^ string_of_bexp e1 ^ ") /\\ (" ^ string_of_bexp e2 ^ ")"
  | QFBV.Bdisj (e1, e2) -> "(" ^ string_of_bexp e1 ^ ") \\/ (" ^ string_of_bexp e2 ^ ")"


(** QFBV helper functions *)

let make_qfbv_bvadds es =
  let rec helper res es =
    match es with
    | [] -> res
    | e::tl -> helper (QFBV.Ebinop (QFBV.Badd, res, e)) tl in
  match es with
  | [] -> failwith ("Apply bvadd with 0 argument")
  | e::tl -> helper e tl

let make_qfbv_conjs es =
  let rec helper res es =
    match es with
    | [] -> res
    | e::tl -> helper (QFBV.Bconj (res, e)) tl in
  match es with
  | [] -> QFBV.Bfalse
  | e::tl -> helper e tl

let make_qfbv_disjs es =
  let rec helper res es =
    match es with
    | [] -> res
    | e::tl -> helper (QFBV.Bdisj (res, e)) tl in
  match es with
  | [] -> QFBV.Btrue
  | e::tl -> helper e tl

let make_qfbv_imp e1 e2 = QFBV.Bdisj (QFBV.Blneg e1, e2)

let make_qfbv_iff e1 e2 = QFBV.Bconj (make_qfbv_imp e1 e2, make_qfbv_imp e2 e1)

let make_qfbv_diff e1 e2 = QFBV.Bdisj (QFBV.Bconj (e1, QFBV.Blneg e2), QFBV.Bconj (QFBV.Blneg e1, e2))

let coq_typ_of_ttyp t : typ =
  match t with
  | TBool -> Tuint 1
  | TNumeral -> failwith ("Conversion from TNumeral to Coq Typ.t is not allowed")
  | TBitVec n -> Tuint n



(** Conversion from SMT file to QFBV expressions *)

(* A map from a variable symbol to its ssavar *)
type vm = ssavar M.t

let gen_ssavar (svar : int) : ssavar * int =
  (Obj.repr (n_of_int svar, n_of_int 0), svar + 1)

(*
let get_sort_type (s : sort) : typ =
  match s with
  | SIdentifier (ISimple s) when s = "Bool" -> Tuint 1
  | SIdentifier (IIndexed (s, [INumeral n])) when s = "BitVec" -> Tuint (Z.to_int n)
  | _ -> failwith ("Unsupported sort: " ^ string_of_sort s)
 *)




let convert_exp_spec_constant sc : QFBV.exp =
  match sc with
  | CNumeral n -> failwith ("Conversion from numeral to QFBV exp is not supported.")
  | CDecimal _ -> failwith ("Conversion from decimal to QFBV exp is not supported.")
  | CHexDecimal h ->
     (try
        QFBV.Econst (bits_of_z (String.length h * 4) (Z.of_string ("0x" ^ h)))
      with Invalid_argument _ ->
        failwith ("Failed to convert hex decimal: " ^ h))
  | CBinary b ->
     (try
        QFBV.Econst (bits_of_z (String.length b) (Z.of_string ("0b" ^ b)))
      with Invalid_argument _ ->
        failwith ("Failed to convert binary: " ^ b))
  | CString _ -> failwith ("Conversion from string to QFBV exp is not supported.")

let convert_bexp_spec_constant sc : QFBV.bexp =
  failwith ("Conversion from spec_constant to QFBV bexp is not supported")

let convert_exp_identifier vm tm i : QFBV.exp =
  match i with
  | ISimple v ->
     (
       try
         QFBV.Evar (M.find v vm)
       with Not_found ->
         failwith("Variable " ^ v ^ " is not declared.")
     )
  | IIndexed (v, [INumeral n]) ->
     if Str.string_match (Str.regexp "bv\\([0-9]+\\)") v 0
     then QFBV.Econst (bits_of_z (Z.to_int n) (Z.of_string (Str.matched_group 1 v)))
     else failwith ("Unrecognized identifier " ^ string_of_identifier i)
  | _ -> failwith ("Unrecognized identifier " ^ string_of_identifier i)

let convert_bexp_identifier vm tm i : QFBV.bexp =
  match i with
  | ISimple v -> if v = "true" then QFBV.Btrue
                 else if v = "false" then QFBV.Bfalse
                 else (try
                         QFBV.Bbinop (QFBV.Beq, QFBV.Evar (M.find v vm), QFBV.Econst ([b1]))
                       with Not_found ->
                         failwith("Variable " ^ v ^ " is not declared.")
                      )
  | IIndexed (v, is) -> failwith ("Conversion from indexed variables to QFBV boolean expressions is not supported.")

let convert_exp_qual_identifier vm tm qi : QFBV.exp =
  match qi with
  | QIdentifier i -> convert_exp_identifier vm tm i
  | QAnnotated (i, s) -> convert_exp_identifier vm tm i

let convert_bexp_qual_identifier vm tm qi : QFBV.bexp =
  match qi with
  | QIdentifier i -> convert_bexp_identifier vm tm i
  | QAnnotated (i, s) -> convert_bexp_identifier vm tm i

let rec convert_exp_application es vm tm fm env g fqi factuals : SSATE.env * int * QFBV.bexp list * QFBV.exp =
  let fn = symbol_of_qual_identifier fqi in
  match fqi, factuals with
  (* Core *)
  | QIdentifier (ISimple v), a1::a2::a3::[] when v = fn_ite -> let (env1, g1, es1, e1) = convert_bexp_term es vm tm fm env g a1 in
                                                               let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                               let (env3, g3, es3, e3) = convert_exp_term es2 vm tm fm env2 g2 a3 in
                                                               (env3, g3, es3, QFBV.Eite (e1, e2, e3))
  (* FixedSizeBitvectors *)
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_concat -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                              let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                              (env2, g2, es2, QFBV.Ebinop (QFBV.Bconcat, e1, e2))
  | QIdentifier (IIndexed (v, (INumeral i)::(INumeral j)::[])), a1::[] when v = fn_extract -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                                                              (env1, g1, es1, QFBV.Eunop (QFBV.Uextr (Z.to_int i, Z.to_int j), e1))
  | QIdentifier (ISimple v), a1::[] when v = fn_bvnot -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                         (env1, g1, es1, QFBV.Eunop (QFBV.Unot, e1))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvand -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                             let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                             (env2, g2, es2, QFBV.Ebinop (QFBV.Band, e1, e2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvor -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                            let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                            (env2, g2, es2, QFBV.Ebinop (QFBV.Bor, e1, e2))
  | QIdentifier (ISimple v), a1::[] when v = fn_bvneg -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                         (env1, g1, es1, QFBV.Eunop (QFBV.Uneg, e1))
  | QIdentifier (ISimple v), _ when v = fn_bvadd -> let (env', g', bs, es_rev) = List.fold_left (
                                                                                     fun (env, g, bs, es) a ->
                                                                                     let (env', g', bs', e) = convert_exp_term bs vm tm fm env g a in
                                                                                     (env', g', bs', e::es)
                                                                                   ) (env, g, es, []) factuals in
                                                    (env', g', bs, make_qfbv_bvadds (List.rev es_rev))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvmul -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                             let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                             (env2, g2, es2, QFBV.Ebinop (QFBV.Bmul, e1, e2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvudiv -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                              let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                              (env2, g2, es2, QFBV.Ebinop (QFBV.Bdiv, e1, e2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvurem -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                              let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                              (env2, g2, es2, QFBV.Ebinop (QFBV.Bmod, e1, e2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvshl -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                             let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                             (env2, g2, es2, QFBV.Ebinop (QFBV.Bshl, e1, e2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvlshr -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                              let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                              (env2, g2, es2, QFBV.Ebinop (QFBV.Blshr, e1, e2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvnand -> failwith ("bvnand is not supported")
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvnor -> failwith ("bvnor is not supported")
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvxor -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                             let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                             (env2, g2, es2, QFBV.Ebinop (QFBV.Bxor, e1, e2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvxnor -> failwith ("bvxnor is not supported")
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvcomp -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                              let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                              (env2, g2, es2, QFBV.Ebinop (QFBV.Bcomp, e1, e2))
  (* TODO: add bvcomp in QFBV or add a constructor to convert bexp to 1-bit exp *)
  (*let (env1, g1, es1, e1) = convert_exp_term vm tm fm env g a1 in
    let (env2, g2, es2, e2) = convert_exp_term vm tm fm env1 g1 a2 in
    (env2, g2, List.rev_append es1 es2, QFBV.Bbinop (QFBV.Beq, e1, e2))*)
  (* Extensions *)
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvsub -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                             let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                             (env2, g2, es2, QFBV.Ebinop (QFBV.Bsub, e1, e2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvsdiv -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                              let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                              (env2, g2, es2, QFBV.Ebinop (QFBV.Bsdiv, e1, e2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvsrem -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                              let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                              (env2, g2, es2, QFBV.Ebinop (QFBV.Bsrem, e1, e2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvsmod -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                              let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                              (env2, g2, es2, QFBV.Ebinop (QFBV.Bsmod, e1, e2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvashr -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                              let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                              (env2, g2, es2, QFBV.Ebinop (QFBV.Bashr, e1, e2))
  | QIdentifier (IIndexed (v, [INumeral n])), a1::[] when v = fn_repeat -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                                           (env1, g1, es1, QFBV.Eunop (QFBV.Urepeat (Z.to_int n), e1))
  | QIdentifier (IIndexed (v, [INumeral n])), a1::[] when v = fn_zero_extend -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                                                (env1, g1, es1, QFBV.Eunop (QFBV.Uzext (Z.to_int n), e1))
  | QIdentifier (IIndexed (v, [INumeral n])), a1::[] when v = fn_sign_extend -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                                                (env1, g1, es1, QFBV.Eunop (QFBV.Usext (Z.to_int n), e1))
  | QIdentifier (IIndexed (v, [INumeral n])), a1::[] when v = fn_rotate_left -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                                                (env1, g1, es1, QFBV.Eunop (QFBV.Urotl (Z.to_int n), e1))
  | QIdentifier (IIndexed (v, [INumeral n])), a1::[] when v = fn_rotate_right -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                                                 (env1, g1, es1, QFBV.Eunop (QFBV.Urotr (Z.to_int n), e1))
  (* User-defined functions *)
  | _ ->
    try
      let (fargs, fsort, fterm) = M.find fn fm in
      let fargs = fst (List.split fargs) in
      if List.length fargs <> List.length factuals then failwith ("Number of arguments mismatch in function application: " ^ fn)
      else convert_exp_term es vm tm fm env g (List.fold_left2 (fun t arg actual -> subst_term arg actual t) fterm fargs factuals)
    with Not_found ->
      failwith ("Undefined exp function in function application: " ^ string_of_term (TApplication (fqi, factuals)))

and convert_exp_let es vm tm fm env g vbs t : SSATE.env * int * QFBV.bexp list * QFBV.exp =
  if !option_expand_let then
    begin
      let t' = List.fold_left (
                   fun t (v, p) -> subst_term v p t
                 ) t vbs in
      convert_exp_term es vm tm fm env g t'
    end
  else
    match vbs with
    | [] -> convert_exp_term es vm tm fm env g t
    | (v, vt)::vbs -> let ty = ttyp_of_term tm fm vt in
                      let coq_ty = coq_typ_of_ttyp ty in
                      let (coq_v, g') = gen_ssavar g in
                      let vm' = M.add v coq_v vm in
                      let tm' = M.add v ty tm in
                      let env' = SSATE.add coq_v coq_ty env in
                      let (env'', g'', es', e) = convert_bexp_term es vm' tm' fm env' g' (make_eq (make_var v) vt) in
                      convert_exp_let (e::es') vm' tm' fm env'' g'' vbs t

and convert_exp_term es vm tm fm env g t : SSATE.env * int * QFBV.bexp list * QFBV.exp =
  match t with
  | TConstant sc -> (env, g, es, convert_exp_spec_constant sc)
  | TVariable qi -> (env, g, es, convert_exp_qual_identifier vm tm qi)
  | TApplication (fqi, factuals) -> convert_exp_application es vm tm fm env g fqi factuals
  | TLet (vbs, t) -> convert_exp_let es vm tm fm env g vbs t

and convert_bexp_application es vm tm fm env g fqi factuals : SSATE.env * int * QFBV.bexp list * QFBV.bexp =
  let fn = symbol_of_qual_identifier fqi in
  match fqi, factuals with
  (* Core *)
  | QIdentifier (ISimple v), a::[] when v = fn_not -> let (env1, g1, es1, e1) = convert_bexp_term es vm tm fm env g a in
                                                      (env1, g1, es1, QFBV.Blneg e1)
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_imp -> let (env1, g1, es1, e1) = convert_bexp_term es vm tm fm env g a1 in
                                                           let (env2, g2, es2, e2) = convert_bexp_term es1 vm tm fm env1 g1 a2 in
                                                           (env2, g2, es2, make_qfbv_imp e1 e2)
  | QIdentifier (ISimple v), _ when v = fn_and -> let (env', g', es, es_a) = List.fold_left (
                                                                                 fun (env, g, es, es_a) a ->
                                                                                 let (env1, g1, es1, e1) = convert_bexp_term es vm tm fm env g a in
                                                                                 (env1, g1, es1, e1::es_a)
                                                                               ) (env, g, es, []) factuals in
                                                  (env', g', es, make_qfbv_conjs (List.rev es_a))
  | QIdentifier (ISimple v), _ when v = fn_or -> let (env', g', es, es_a) = List.fold_left (
                                                                                fun (env, g, es, es_a) a ->
                                                                                let (env1, g1, es1, e1) = convert_bexp_term es vm tm fm env g a in
                                                                                (env1, g1, es1, e1::es_a)
                                                                              ) (env, g, es, []) factuals in
                                                 (env', g', es, make_qfbv_disjs (List.rev es_a))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_xor -> failwith ("xor is not supported")
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_eq -> if is_bool_term tm fm a1 || is_bool_term tm fm a2
                                                          then let (env1, g1, es1, e1) = convert_bexp_term es vm tm fm env g a1 in
                                                               let (env2, g2, es2, e2) = convert_bexp_term es1 vm tm fm env1 g1 a2 in
                                                               (env2, g2, es2, make_qfbv_iff e1 e2)
                                                          else let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                               let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                               (env2, g2, es2, QFBV.Bbinop (QFBV.Beq, e1, e2))
  | QIdentifier (ISimple v), _ when v = fn_distinct -> if List.exists (is_bool_term tm fm) factuals
                                                       then let (env', g', es, es_as) = List.fold_left (
                                                                                            fun (env, g, es, es_as) a ->
                                                                                            let (env1, g1, es1, e1) = convert_bexp_term es vm tm fm env g a in
                                                                                            (env1, g, es1, e1::es_as)
                                                                                          ) (env, g, es, []) factuals in
                                                            (env', g', es, make_qfbv_conjs (List.map (fun es -> match es with
                                                                                                                | e1::e2::[] -> make_qfbv_diff e1 e2
                                                                                                                | _ -> failwith("Never happen")) (Util.combinations 2 es_as)))
                                                       else let (env', g', es, es_as) = List.fold_left (
                                                                                            fun (env, g, es, es_as) a ->
                                                                                            let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a in
                                                                                            (env1, g, es1, e1::es_as)
                                                                                          ) (env, g, es, []) factuals in
                                                            (env', g', es, make_qfbv_conjs (List.map (fun es -> match es with
                                                                                                                | e1::e2::[] -> QFBV.Blneg (QFBV.Bbinop (QFBV.Beq, e1, e2))
                                                                                                                | _ -> failwith("Never happen")) (Util.combinations 2 es_as)))
  | QIdentifier (ISimple v), a1::a2::a3::[] when v = fn_ite -> let (env1, g1, es1, e1) = convert_bexp_term es vm tm fm env g a1 in
                                                               let (env2, g2, es2, e2) = convert_bexp_term es1 vm tm fm env1 g1 a2 in
                                                               let (env3, g3, es3, e3) = convert_bexp_term es2 vm tm fm env2 g2 a3 in
                                                               (env3, g3, es3, QFBV.Bdisj (QFBV.Bconj (e1, e2), QFBV.Bconj (QFBV.Blneg e1, e3)))
  (* FixedSizeBitvectors *)
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvult -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                             let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                             (env2, g2, es2, QFBV.Bbinop (QFBV.Bult, e1, e2))

  (* Extensions *)
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvule -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                             let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                             (env2, g2, es2, QFBV.Bbinop (QFBV.Bule, e1, e2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvugt -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                             let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                             (env2, g2, es2, QFBV.Bbinop (QFBV.Bugt, e1, e2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvuge -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                             let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                             (env2, g2, es2, QFBV.Bbinop (QFBV.Buge, e1, e2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvslt -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                             let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                             (env2, g2, es2, QFBV.Bbinop (QFBV.Bslt, e1, e2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvsle -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                             let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                             (env2, g2, es2, QFBV.Bbinop (QFBV.Bsle, e1, e2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvsgt -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                             let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                             (env2, g2, es2, QFBV.Bbinop (QFBV.Bsgt, e1, e2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_bvsge -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm env g a1 in
                                                             let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm env1 g1 a2 in
                                                             (env2, g2, es2, QFBV.Bbinop (QFBV.Bsge, e1, e2))
  (* User-defined functions *)
  | _ ->
    try
      let (fargs, fsort, fterm) = M.find fn fm in
      let fargs = fst (List.split fargs) in
      if List.length fargs <> List.length factuals then failwith ("Number of arguments mismatch in function application: " ^ fn)
      else convert_bexp_term es vm tm fm env g (List.fold_left2 (fun t arg actual -> subst_term arg actual t) fterm fargs factuals)
    with Not_found ->
      failwith ("Undefined bexp function in function application: " ^ fn)

and convert_bexp_let es vm tm fm env g vbs t : SSATE.env * int * QFBV.bexp list * QFBV.bexp =
  if !option_expand_let then
    begin
      let t' = List.fold_left (
                   fun t (v, p) -> subst_term v p t
                 ) t vbs in
      convert_bexp_term es vm tm fm env g t'
    end
  else
    match vbs with
    | [] -> convert_bexp_term es vm tm fm env g t
    | (v, vt)::vbs -> let ty = ttyp_of_term tm fm vt in
                      let coq_ty = coq_typ_of_ttyp ty in
                      let (coq_v, g') = gen_ssavar g in
                      let vm' = M.add v coq_v vm in
                      let tm' = M.add v ty tm in
                      let env' = SSATE.add coq_v coq_ty env in
                      let (env'', g'', es', e) = convert_bexp_term es vm' tm' fm env' g' (make_eq (make_var v) vt) in
                      convert_bexp_let (e::es') vm' tm' fm env'' g'' vbs t

and convert_bexp_term es vm tm fm env g t : SSATE.env * int * QFBV.bexp list * QFBV.bexp =
  match t with
  | TConstant sc -> (env, g, es, convert_bexp_spec_constant sc)
  | TVariable qi -> (env, g, es, convert_bexp_qual_identifier vm tm qi)
  | TApplication (fqi, factuals) -> convert_bexp_application es vm tm fm env g fqi factuals
  | TLet (vbs, t) -> convert_bexp_let es vm tm fm env g vbs t

let declare_fun vm tm fm env g fn fargs fsort : vm * tm * fm * SSATE.env * int =
  match fargs with
  | [] -> let ty = ttyp_of_sort fsort in
          let coq_ty = coq_typ_of_ttyp ty in
          let (coq_v, g') = gen_ssavar g in
          (M.add fn coq_v vm, M.add fn ty tm, fm, SSATE.add coq_v coq_ty env, g')
  | _ -> failwith ("Function declaration with nonempty arguments is not supported.")

let define_fun es vm tm fm env g fn fargs fsort fterm : vm * tm * fm * SSATE.env * int * QFBV.bexp list =
  match fargs with
  | [] -> let ty = ttyp_of_sort fsort in
          let coq_ty = coq_typ_of_ttyp ty in
          let (coq_v, g') = gen_ssavar g in
          let vm' = M.add fn coq_v vm in
          let tm' = M.add fn ty tm in
          let env' = SSATE.add coq_v coq_ty env in
          let (env'', g'', es', e) = convert_bexp_term es vm' tm' fm env' g' (make_eq (make_var fn) fterm) in
          (vm', tm', fm, env'', g'', List.rev (e::es'))
  | _ -> (vm, tm, M.add fn (fargs, fsort, fterm) fm, env, g, es)

let bexps_of_command es vm tm fm env g c : vm * tm * fm * SSATE.env * int * QFBV.bexp list =
  match c with
  | CSetLogic _ -> (vm, tm, fm, env, g, es)
  | CSetInfo _ -> (vm, tm, fm, env, g, es)
  | CSetOption _ -> (vm, tm, fm, env, g, es)
  | CDeclareFun (fn, fargs, fsort) ->
     let (vm', tm', fm', env', g') = declare_fun vm tm fm env g fn fargs fsort in
     (vm', tm', fm', env', g', es)
  | CDefineFun (fn, fargs, fsort, fterm) ->
     let (vm', tm', fm', env', g', es') = define_fun es vm tm fm env g fn fargs fsort fterm in
     (vm', tm', fm', env', g', es')
  | CAssert (TApplication (QIdentifier (ISimple v), factuals)) when v = fn_and ->
     let (env', g', es) = List.fold_left (
                              fun (env, g, es) a ->
                              let (env1, g1, es1, e1) = convert_bexp_term es vm tm fm env g a in
                              (env1, g1, e1::es1)
                            ) (env, g, es) factuals in
     (vm, tm, fm, env', g', es)
  | CAssert t -> let (env', g', es', e) = convert_bexp_term es vm tm fm env g t in
                 (vm, tm, fm, env', g', e::es')
  | CCheckSat -> (vm, tm, fm, env, g, es)
  | CGetModel -> (vm, tm, fm, env, g, es)
  | CExit -> (vm, tm, fm, env, g, es)
  | CComment _ -> (vm, tm, fm, env, g, es)

let is_check_sat c =
  match c with
  | CCheckSat -> true
  | _ -> false

let is_exit c =
  match c with
  | CExit -> true
  | _ -> false

let bexps_of_script vm tm fm env g script : vm * tm * fm * SSATE.env * int * QFBV.bexp list =
  let (cs', ex', vm', tm', fm', env', g', es_rev) =
    List.fold_left (
        fun (cs, ex, vm, tm, fm, env, g, res) c ->
        let cs_c = is_check_sat c in
        if ex then (cs, ex, vm, tm, fm, env, g, res)
        else if cs && cs_c then failwith("Multiple check-sat is not supported.")
        else let (vm', tm', fm', env', g', es) = bexps_of_command res vm tm fm env g c in
             (cs || cs_c, is_exit c, vm', tm', fm', env', g', es)
      ) (false, false, vm, tm, fm, env, g, []) script in
  (vm', tm', fm', env', g', List.rev es_rev)

let bexps_of_file file : vm * tm * SSATE.env * QFBV.bexp list =
  let vm = M.empty in
  let tm = M.empty in
  let fm = M.empty in
  let env = SSATE.empty in
  let g = 0 in
  let (vm', tm', fm', env', g', es) = bexps_of_script vm tm fm env g file in
  (vm', tm', env', es)



(** Bit-blasting *)

let string_of_ssavar v =
  let (svar, sidx) = Obj.magic v in
  string_of_int (int_of_n svar) ^ " " ^ string_of_int (int_of_n sidx)

(*
 * vm: from var in SMTLIB to var in Coq QFBV
 * env: typing environment in Coq
 * returns a map from QFBV var to its corresponding literals
 *)
let bb_bexps_conj vm env es =
  let _ =
    if !option_debug then
      let _ = List.iter (
                  fun (v, ty) ->
                  print_endline (string_of_ssavar v ^ ": BitVec " ^ string_of_ty ty)
                ) (SSATE.elements env) in
      let _ = M.iter (
                  fun v ssav ->
                  print_endline (v ^ " => " ^ string_of_ssavar ssav)
                ) vm in
      let _ = print_endline (String.concat "\n" (List.map string_of_bexp es)) in
      () in
  if QFBV.well_formed_bexps es env then
    if !option_split_conjs then
      let (((m, c), g), cnf) = bit_blast_bexps_hcache_conjs env es in
      (m, cnf)
    else
      let e = make_qfbv_conjs es in
      let ((((m, c), g), cnf), lr) = bit_blast_bexp_hcache_tflatten env init_vm init_hcache init_gen (hash_bexp e) in
      let cnf = CNF.add_prelude ([lr]::cnf) in
      (m, cnf)
  else
    raise IllFormedException

let bb_file file =
  (* vm: from var in SMTLIB to var in Coq QFBV *)
  let (vm, tm, env, es) = bexps_of_file file in
  let (_, cnf) = bb_bexps_conj vm env es in
  cnf


(** Output to DIMACS *)

let coq_string_of_literal l =
  match l with
  | CNF.Pos v -> string_of_int (int_of_pos v)
  | CNF.Neg v -> "-" ^ string_of_int (int_of_pos v)

let coq_output_clause ch c = output_string ch (String.concat " " (List.map coq_string_of_literal c) ^ " 0")

let coq_output_cnf ch cs = List.iter (fun c -> coq_output_clause ch c; output_string ch "\n") cs

let coq_output_dimacs ch cs =
  let nvars = int_of_pos (CNF.max_var_of_cnf cs) in
  let nclauses = int_of_n (CNF.num_clauses cs) in
  let _ = output_string ch ("p cnf " ^ string_of_int nvars ^ " " ^ string_of_int nclauses ^ "\n") in
  let _ = coq_output_cnf ch cs in
  let _ = flush ch in
  (nvars, nclauses)



(** Check SAT *)

type literal_assignments = bool array

type qfbv_assignments = SSAStore.t

type smtlib_assignments = (ttyp * string) M.t

type sat_solving_result = SAT of literal_assignments | UNSAT

type check_sat_result = CERTIFIED_SAT of smtlib_assignments | CERTIFIED_UNSAT

type 'a result = OK of 'a | ERROR of string

let string_of_check_sat_result res =
  match res with
  | CERTIFIED_UNSAT -> "unsat"
  | CERTIFIED_SAT m -> "sat"

(*
 * vm: from var in SMTLIB to var in Coq QFBV
 * env: typing environment in Coq
 *)
let check_sat_bexps_conj vm tm env es =
  let base_file = tmpfile "coqqfbv_" "" in
  let cnf_file =
    match !option_cnf_file with
    | None -> base_file ^ ".cnf"
    | Some fn -> fn in
  let drat_file =
    match !option_drat_file with
    | None -> base_file ^ ".drat"
    | Some fn -> fn in
  let sat_log_file =
    match !option_sat_log_file with
    | None -> base_file ^ ".sat.log"
    | Some fn -> fn in
  let gratl_file =
    match !option_gratl_file with
    | None -> base_file ^ ".gratl"
    | Some fn -> fn in
  let gratp_file =
    match !option_gratp_file with
    | None -> base_file ^ ".gratp"
    | Some fn -> fn in
  let grat_log_file =
    match !option_grat_log_file with
    | None -> base_file ^ ".grat.log"
    | Some fn -> fn in
  let _ = cleanup [base_file] in
  let do_bit_blasting vm env es =
    let _ = if !option_verbose then print_string ("Bit-blasting: ") in
    let t1 = Unix.gettimeofday() in
    let (lm, cnf) = bb_bexps_conj vm env es in
    let t2 = Unix.gettimeofday() in
    let _ = if !option_verbose then print_endline ("done [" ^ string_of_float (t2 -. t1) ^ " seconds]") in
    (lm, cnf) in
  let do_output_cnf_file cnf =
    let _ = if !option_verbose then print_string ("Saving CNF file: ") in
    let t1 = Unix.gettimeofday() in
    let (nvars, nclauses) =
      let outch = open_out cnf_file in
      let (nvars, nclauses) = coq_output_dimacs outch cnf in
      let _ = close_out outch in
      (nvars, nclauses) in
    let t2 = Unix.gettimeofday() in
    let _ =
      if !option_verbose then
        let _ = print_endline ("done [" ^ string_of_float (t2 -. t1) ^ " seconds]") in
        let _ = print_endline ("CNF file: " ^ cnf_file) in
        let _ = print_endline ("Size of CNF file: " ^ Int64.to_string (Unix.LargeFile.stat cnf_file).Unix.LargeFile.st_size ^ " bytes") in
        let _ = print_endline ("Number of variables in CNF file: " ^ string_of_int nvars) in
        let _ = print_endline ("Number of clauses in CNF file: " ^ string_of_int nclauses) in
        () in
    nvars in
  let do_sat_solving () =
    let _ = if !option_verbose then print_string ("Solving CNF file: ") in
    let t1 = Unix.gettimeofday() in
    let _ =
      let cmd = !option_kissat_path ^ " -q " ^ cnf_file ^ " " ^ drat_file ^ " 2>&1 1>" ^ sat_log_file in
      match Unix.system cmd with
      | Unix.WEXITED 10 -> () (* sat *)
      | Unix.WEXITED 20 -> () (* unsat *)
      | _ -> raise (Failure "Failed to solve CNF file") in
    let t2 = Unix.gettimeofday() in
    let _ =
      if !option_verbose then
        let _ = print_endline ("done [" ^ string_of_float (t2 -. t1) ^ " seconds]") in
        let _ = if Sys.file_exists drat_file then print_endline ("DRAT file: " ^ drat_file ^ "\n"
                                                                 ^ "Size of DRAT file: " ^ Int64.to_string (Unix.LargeFile.stat drat_file).Unix.LargeFile.st_size ^ " bytes") in
        () in
    () in
  let do_parse_sat_result nvars =
    let literal_assignments = ref (Array.make 1 false) in
    let is_unsat =
      let is_unsat = ref None in
      let line = ref "" in
      let inch = open_in sat_log_file in
      let _ =
        try
          while true do
            let _ = line := input_line inch in
            let _ = if !option_debug then print_endline ("DEBUG: SAT result line: " ^ !line) in
            if !line = "s SATISFIABLE" then (literal_assignments := Array.make (nvars + 1) false; is_unsat := Some false)
            else if !line = "s UNSATISFIABLE" then is_unsat := Some true
            else if Str.string_match (Str.regexp "v ") !line 0 then
              let assignments = List.map int_of_string (String.split_on_char ' ' (String.sub !line 2 (String.length !line - 2))) in
              let _ = List.iter (fun v -> !literal_assignments.(abs v) <- (v > 0)) assignments in
              ()
            else raise End_of_file
          done
        with End_of_file -> ()
           | _ -> failwith "Failed to read the SAT solver output file." in
      let _ = close_in inch in
      !is_unsat in
    match is_unsat with
    | None ->
       let _ = Unix.system ("cat " ^ sat_log_file) in
       raise (Failure "Error in SAT solving")
    | Some true -> UNSAT
    | Some false -> SAT !literal_assignments in
  let do_certify_unsat () =
    let _ = if !option_verbose then print_string ("Certifying UNSAT proof: ") in
    let t1 = Unix.gettimeofday() in
    let _ =
      let cmd = !option_gratgen_path ^ " " ^ cnf_file ^ " " ^ drat_file ^ " -b -l " ^ gratl_file ^ " -o " ^ gratp_file ^ " 2>&1 | grep 's VERIFIED' 2>&1 1>/dev/null" in (* &>/dev/null does not work on Linux *)
      match Unix.system cmd with
      | Unix.WEXITED 0 -> () (* grep found *)
      | _ -> raise (Failure "Failed to generate auxiliary lemmas from UNSAT proof") in
    let certified =
      let cmd = !option_gratchk_path ^ " unsat " ^ cnf_file ^ " " ^ gratl_file ^ " " ^ gratp_file ^ " 2>&1 | grep 's VERIFIED UNSAT' 2>&1 1>/dev/null" in (* &>/dev/null does not work on Linux *)
      match Unix.system cmd with
      | Unix.WEXITED 0 -> true (* grep found *)
      | _ -> false in
    let t2 = Unix.gettimeofday() in
    let _ =
      if !option_verbose then
        let _ = print_endline ("done [" ^ string_of_float (t2 -. t1) ^ " seconds]") in
        let _ = if Sys.file_exists gratl_file then print_endline ("GRATL file: " ^ gratl_file ^ "\n"
                                                                  ^ "Size of GRATL file: " ^ Int64.to_string (Unix.LargeFile.stat gratl_file).Unix.LargeFile.st_size ^ " bytes") in
        let _ = if Sys.file_exists gratp_file then print_endline ("GRATP file: " ^ gratp_file ^ "\n"
                                                                  ^ "Size of GRATP file: " ^ Int64.to_string (Unix.LargeFile.stat gratp_file).Unix.LargeFile.st_size ^ " bytes") in
        let _ = print_endline ("UNSAT proof certified: " ^ string_of_bool certified) in
        () in
    certified in
  let qfbv_assignments_of_literal_assignments lm literal_assignments =
    let _ = if !option_debug then Array.iteri (fun i b -> print_endline ("DEBUG: " ^ "cnf var " ^ string_of_int i ^ ": " ^ string_of_bool b)) literal_assignments in
    let int_of_lit l = int_of_pos (CNF.var_of_lit l) in
    SSAVM.fold
      (fun ssavar lits store ->
        let bv = List.map (fun l -> literal_assignments.(int_of_lit l)) (lits) in
        let _ = if !option_debug then print_endline ("DEBUG: ssavar " ^ string_of_ssavar ssavar ^ " -> lits "
                                                     ^ (String.concat " " (List.map string_of_int (List.map int_of_lit lits))) ^ ": value " ^ string_of_bits bv) in
        SSAStore.upd ssavar bv store
      ) lm (SSAStore.empty) in
  let smtlib_assignments_of_qfbv_assignments vm tm qfbv_assignments =
    M.mapi (
        fun v coq_v ->
        let ty = M.find v tm in
        let bv = SSAStore.acc coq_v qfbv_assignments in
        let _ = if !option_debug then print_endline ("DEBUG: smtlib var " ^ v ^ " -> ssavar " ^ string_of_ssavar coq_v ^ ": value " ^ string_of_bits bv) in
        (ty, match ty with
             | TBool -> string_of_bool (List.hd bv)
             | TNumeral -> Z.to_string (Z.of_string ("0b" ^ string_of_bits bv))
             | TBitVec w -> "#b" ^ string_of_bits bv)
      ) vm
  in
  let do_certify_sat es qfbv_assignments =
    let _ = if !option_verbose then print_string ("Certifying SAT assignments: ") in
    let t1 = Unix.gettimeofday() in
    let certified = List.for_all (fun e -> QFBV.eval_bexp e qfbv_assignments) es in
    let t2 = Unix.gettimeofday() in
    let _ =
      if !option_verbose then
        let _ = print_endline ("done [" ^ string_of_float (t2 -. t1) ^ " seconds]") in
        let _ = print_endline ("SAT assignments certified: " ^ string_of_bool certified) in
        () in
    certified in
  let res =
    try
      (* == Bit-blasting == *)
      let (lm, cnf) = do_bit_blasting vm env es in
      (* == Output CNF file == *)
      let nvars = do_output_cnf_file cnf in
      (* == Run SAT solver == *)
      let _ = do_sat_solving () in
      (* == Parse SAT solving results == *)
      let sat_res = do_parse_sat_result nvars in
      (* == Certify unsat proof or sat assignments == *)
      match sat_res with
      | UNSAT -> if do_certify_unsat ()
                 then OK CERTIFIED_UNSAT
                 else raise (Failure "Failed to certify UNSAT proof")
      | SAT literal_assignments -> let qfbv_assignments = qfbv_assignments_of_literal_assignments lm literal_assignments in
                                   if do_certify_sat es qfbv_assignments
                                   then OK (CERTIFIED_SAT (smtlib_assignments_of_qfbv_assignments vm tm qfbv_assignments))
                                   else raise (Failure "Failed to certify SAT assignments")
    with (Failure msg) -> ERROR msg
       | _ -> ERROR "Error" in
  let _ = cleanup [cnf_file; drat_file; sat_log_file; gratl_file; gratp_file; grat_log_file] in
  match res with
  | OK r -> r
  | ERROR msg -> failwith msg

let check_sat_command sat_res_rev es vm tm fm env g c : check_sat_result list * vm * tm * fm * SSATE.env * int * QFBV.bexp list =
  match c with
  | CSetLogic _ -> (sat_res_rev, vm, tm, fm, env, g, es)
  | CSetInfo _ -> (sat_res_rev, vm, tm, fm, env, g, es)
  | CSetOption _ -> (sat_res_rev, vm, tm, fm, env, g, es)
  | CDeclareFun (fn, fargs, fsort) ->
     let (vm', tm', fm', env', g') = declare_fun vm tm fm env g fn fargs fsort in
     (sat_res_rev, vm', tm', fm', env', g', es)
  | CDefineFun (fn, fargs, fsort, fterm) ->
     let (vm', tm', fm', env', g', es') = define_fun es vm tm fm env g fn fargs fsort fterm in
     (sat_res_rev, vm', tm', fm', env', g', es')
  | CAssert (TApplication (QIdentifier (ISimple v), factuals)) when v = fn_and ->
     let (env', g', es) = List.fold_left (
                              fun (env, g, es) a ->
                              let (env1, g1, es1, e1) = convert_bexp_term es vm tm fm env g a in
                              (env1, g1, e1::es1)
                            ) (env, g, es) factuals in
     (sat_res_rev, vm, tm, fm, env', g', es)
  | CAssert t -> let (env', g', es', e) = convert_bexp_term es vm tm fm env g t in
                 (sat_res_rev, vm, tm, fm, env', g', e::es')
  | CCheckSat ->
     let sat_res = check_sat_bexps_conj vm tm env (List.rev es) in
     let _ = print_endline (string_of_check_sat_result sat_res) in
     (sat_res::sat_res_rev, vm, tm, fm, env, g, es)
  | CGetModel ->
     begin
       match sat_res_rev with
       | (CERTIFIED_SAT model)::_ ->
          let _ = print_string ("(model\n") in
          let _ = M.iter (
                      fun var (typ, value) ->
                      let typ_str =
                        match typ with
                        | TBool -> "Bool"
                        | TNumeral -> "Int"
                        | TBitVec w -> "(_ BitVec " ^ string_of_int w ^ ")" in
                      print_endline ("(define-fun " ^ var ^ " () " ^ typ_str ^ " " ^ value ^ ")")
                    ) model in
          let _ = print_string (")\n") in
          (sat_res_rev, vm, tm, fm, env, g, es)
       | _ -> (sat_res_rev, vm, tm, fm, env, g, es)
     end
  | CExit -> (sat_res_rev, vm, tm, fm, env, g, es)
  | CComment _ -> (sat_res_rev, vm, tm, fm, env, g, es)

let check_sat_script vm tm fm env g script =
  let (sat_res_rev, ex', vm', tm', fm', env', g', es_rev) =
    List.fold_left (
        fun (sat_res_rev, ex, vm, tm, fm, env, g, res) c ->
        if ex then (sat_res_rev, ex, vm, tm, fm, env, g, res)
        else let (sat_res_rev', vm', tm', fm', env', g', es) = check_sat_command sat_res_rev res vm tm fm env g c in
             (sat_res_rev', is_exit c, vm', tm', fm', env', g', es)
      ) ([], false, vm, tm, fm, env, g, []) script in
  (List.rev sat_res_rev, vm', tm', fm', env', g', List.rev es_rev)

let check_sat_file file =
  let vm = M.empty in
  let tm = M.empty in
  let fm = M.empty in
  let env = SSATE.empty in
  let g = 0 in
  let (sat_res, vm', tm', fm', env', g', es) = check_sat_script vm tm fm env g file in
  (sat_res, vm', tm', env', es)
