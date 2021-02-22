
open Smtlib.Ast
open Extraction.Var
open Extraction.CNF
open Extraction.TypEnv
open Extraction.QFBV
open Extraction.State

(* Options *)

val option_debug : bool ref

val option_split_conjs : bool ref

val option_expand_let : bool ref

val option_kissat_path : string ref
val option_gratgen_path : string ref
val option_gratchk_path : string ref

val option_verbose : bool ref

val option_cnf_file : string option ref
val option_drat_file : string option ref
val option_sat_log_file : string option ref
val option_gratl_file : string option ref
val option_gratp_file : string option ref
val option_grat_log_file : string option ref

val option_tmpdir : string option ref
val option_keep_temp_files : bool ref

(* Bit-blasting *)

type vm = ssavar M.t

val string_of_exp : QFBV.exp -> string

val string_of_bexp : QFBV.bexp -> string

val bexps_of_file : file -> vm * tm * SSATE.env * QFBV.bexp list

val bb_file : file -> cnf

(* return the number of variables and the number of clauses *)
val coq_output_dimacs : out_channel -> cnf -> int * int

(* Check SAT *)

type literal_assignments = bool array

type qfbv_assignments = SSAStore.t

type smtlib_assignments = (ttyp * string) M.t

type sat_solving_result = SAT of literal_assignments | UNSAT

type check_sat_result = CERTIFIED_SAT of smtlib_assignments | CERTIFIED_UNSAT

val string_of_check_sat_result : check_sat_result -> string

val check_sat_file : file -> check_sat_result list * vm * tm * SSATE.env * QFBV.bexp list

