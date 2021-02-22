
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
  | CGetModel
  | CExit
  | CComment of string

type script = command list

type file = script



(** String outputs *)

val string_of_numeral : numeral -> string
val string_of_decimal : decimal -> string
val string_of_hex : hex -> string
val string_of_binary : binary -> string
val string_of_symbol : symbol -> string
val string_of_spec_constant : spec_constant -> string
val string_of_keyword : keyword -> string
val string_of_attribute : attribute -> string
val string_of_solver_option : solver_option -> string
val string_of_index : index -> string
val string_of_identifier : identifier -> string
val string_of_sort : sort -> string
val string_of_qual_identifier : qual_identifier -> string
val string_of_var_binding : var_binding -> string
val string_of_term : term -> string
val string_of_sorted_var : sorted_var -> string
val string_of_command : command -> string
val string_of_script : script -> string
val string_of_file : file -> string


val pp_term : out_channel -> term -> unit
val pp_command : out_channel -> command -> unit
val pp_script : out_channel -> script -> unit
val pp_file : out_channel -> file -> unit



(** Some predefined symbols *)

val fn_not : string
val fn_imp : string
val fn_and : string
val fn_or : string
val fn_xor : string
val fn_eq : string
val fn_distinct : string
val fn_ite : string

val fn_concat : string
val fn_extract : string
val fn_bvnot : string
val fn_bvand : string
val fn_bvor : string
val fn_bvneg : string
val fn_bvadd : string
val fn_bvmul : string
val fn_bvudiv : string
val fn_bvurem : string
val fn_bvshl : string
val fn_bvlshr : string
val fn_bvult : string

val fn_bvnand : string
val fn_bvnor : string
val fn_bvxor : string
val fn_bvxnor : string
val fn_bvcomp : string
val fn_bvsub : string
val fn_bvsdiv : string
val fn_bvsrem : string
val fn_bvsmod : string
val fn_bvashr : string
val fn_repeat : string
val fn_zero_extend : string
val fn_sign_extend : string
val fn_rotate_left : string
val fn_rotate_right : string
val fn_bvule : string
val fn_bvugt : string
val fn_bvuge : string
val fn_bvslt : string
val fn_bvsle : string
val fn_bvsgt : string
val fn_bvsge : string



(** Utility functions *)

val bool_type_name : string

val binary_as_list : string -> bool list

val symbol_of_identifier : identifier -> symbol

val symbol_of_qual_identifier : qual_identifier -> symbol

val subst_term : symbol -> term -> term -> term

val is_eq_term : term -> bool

val make_bitvec_sort : numeral -> sort
val make_var : symbol -> term
val make_binary_constant : string -> term
val make_bv : numeral -> numeral -> term
val make_unop : string -> term -> term
val make_binop : string -> term -> term -> term
val make_op : string -> term list -> term

val make_not : term -> term
val make_imp : term -> term -> term
val make_and : term -> term -> term
val make_ands : term list -> term
val make_or : term -> term -> term
val make_ors : term list -> term
val make_xor : term -> term -> term
val make_eq : term -> term -> term
val make_distinct : term -> term -> term
val make_distincts : term list -> term
val make_ite : term -> term -> term -> term

val make_concat : term -> term -> term
val make_extract : numeral -> numeral -> term -> term
val make_bvnot : term -> term
val make_bvand : term -> term -> term
val make_bvands : term list -> term
val make_bvor : term -> term -> term
val make_bvors : term list -> term
val make_bvneg : term -> term
val make_bvadd : term -> term -> term
val make_bvadds : term list -> term
val make_bvmul : term -> term -> term
val make_bvudiv : term -> term -> term
val make_bvurem : term -> term -> term
val make_bvshl : term -> term -> term
val make_bvlshr : term -> term -> term
val make_bvult : term -> term -> term

val make_bvnand : term -> term -> term
val make_bvnor : term -> term -> term
val make_bvxor : term -> term -> term
val make_bvxors : term list -> term
val make_bvxnor : term -> term -> term
val make_bvcomp : term -> term -> term
val make_bvsub : term -> term -> term
val make_bvsdiv : term -> term -> term
val make_bvsrem : term -> term -> term
val make_bvsmod : term -> term -> term
val make_bvashr : term -> term -> term
val make_repeat : numeral -> term -> term
val make_zero_extend : numeral -> term -> term
val make_sign_extend : numeral -> term -> term
val make_rotate_left : numeral -> term -> term
val make_rotate_right : numeral -> term -> term
val make_bvule : term -> term -> term
val make_bvugt : term -> term -> term
val make_bvuge : term -> term -> term
val make_bvslt : term -> term -> term
val make_bvsle : term -> term -> term
val make_bvsgt : term -> term -> term
val make_bvsge : term -> term -> term

val make_let : var_binding list -> term -> term


(** Typing terms *)

type ttyp =
  | TBool
  | TNumeral
  | TBitVec of int

val size_of_ttyp : ttyp -> int

module M : Map.S with type key = string

type tm = ttyp M.t

type fm = (sorted_var list * sort * term) M.t

val ttyp_of_sort : sort -> ttyp
val ttyp_of_spec_constant : spec_constant -> ttyp
val ttyp_of_identifier : tm -> identifier -> ttyp
val ttyp_of_qual_identifier : tm -> qual_identifier -> ttyp
val ttyp_of_term : tm -> fm -> term -> ttyp
val is_bool_term : tm -> fm -> term -> bool



(** Convert extensions to core functions *)

val convert_defined_extensions_file : ?skip:string list -> file -> file
