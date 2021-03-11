open Arg
open Smtlib
open Extraction
open Extraction.ExtrOcamlIntConv
open Extraction.QFBV
open Bitblasting

let args = [
    ("-cnf", String (fun str -> option_cnf_file := Some str), "FILE\tOutput CNF to a specified file");
    ("-drat", String (fun str -> option_drat_file := Some str), "FILE\tOutput DRAT (unsat proof) to a specified file");
    ("-grat-log", String (fun str -> option_grat_log_file := Some str), "FILE\n\t\tOutput log of GRAT to a specified file");
    ("-gratchk", String (fun str -> option_gratchk_path := str), "PATH\n\t\tSpecify path to gratchk (default is " ^ !option_gratchk_path ^ ")");
    ("-gratgen", String (fun str -> option_gratgen_path := str), "PATH\n\t\tSpecify path to gratgen (default is " ^ !option_gratgen_path ^ ")");
    ("-gratl", String (fun str -> option_gratl_file := Some str), "FILE\tOutput GRATL to a specified file");
    ("-gratp", String (fun str -> option_gratp_file := Some str), "FILE\tOutput GRATP to a specified file");
    ("-kissat", String (fun str -> option_kissat_path := str), "PATH\tSpecify path to kissat (default is " ^ !option_kissat_path ^ ")");
    ("-keep-temps", Set option_keep_temp_files, "\tKeep temporary files");
    ("-sat-log", String (fun str -> option_sat_log_file := Some str), "FILE\n\t\tOutput log of SAT solver to a specified file");
    ("-split-conjs", Set option_split_conjs, "\tBit-blast top-level conjunctions separately");
    ("-tmpdir", String (fun str -> option_tmpdir := Some str), "PATH\tSpecify tmp directory");
    ("-unfold-let", Set option_expand_let, "\tUnfold let expressions during bit-blasting");
    ("-verbose", Unit (fun () -> option_verbose := true), "\tPrint verbose messages")
  ]

let usage = "Usage: coqQFBV OPTIONS FILE\n"

let anon file =
  let f = (Parser.parse file) in
  let _ = check_sat_file f in
  ()
