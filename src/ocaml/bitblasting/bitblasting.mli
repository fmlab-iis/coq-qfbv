
open Smtlib.Ast
open Extraction.Var
open Extraction.CNF
open Extraction.TypEnv
open Extraction.QFBV

type vm = ssavar M.t

val option_debug : bool ref

val string_of_exp : QFBV.exp -> string

val string_of_bexp : QFBV.bexp -> string

val bexp_of_file : file -> vm * tm * SSATE.env * QFBV.bexp

val bb_file : file -> cnf

val coq_output_dimacs : out_channel -> cnf -> unit
