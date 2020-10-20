open Arg
open Smtlib
open Extraction
open Extraction.ExtrOcamlIntConv
open Extraction.QFBV
open Bitblasting

let args = [
    ("-d", Unit (fun () -> option_debug := true), "\t\tPrint debug messages")
  ]

let usage = "Usage: coqsmt OPTIONS FILE\n"

let anon file =
  let f = (Parser.parse file) in
  let cnf = bb_file f in
  let _ = coq_output_dimacs stdout cnf in
  ()
