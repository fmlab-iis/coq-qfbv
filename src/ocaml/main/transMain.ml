open Arg
open Smtlib
open Smtcoq
open Util

let smtcoq_mode = ref false
let norm_ite = ref false
let norm_name = ref false
let output_file = ref None

let args = [
    ("-norm_name", Set norm_name, "\t\tNormalize names for SMTCoq");
    ("-norm_ite", Set norm_ite, "\t\tNormalize ite for SMTCoq");
    ("-smtcoq", Set smtcoq_mode, "\t\tDo not translate operators supported by SMTCoq");
    ("-o", String (fun str -> output_file := Some str), "\t\tSet output file")
  ]

let usage = "Usage: trans OPTIONS FILE\n"

let anon file =
  let f = (Parser.parse file) in
  let f' =
    (
      (if !smtcoq_mode
       then Ast.convert_defined_extensions_file ~skip:Smtcoq.supported_extensions
       else Ast.convert_defined_extensions_file ~skip:[Ast.fn_distinct])
      |>
        (if !norm_ite then Smtcoq.norm_ite_file else id)
      |>
        (if !norm_name then Smtcoq.norm_name_file else id)
    ) f in
  let out =
    match !output_file with
    | None -> stdout
    | Some fn -> open_out fn in
  let _ = Ast.pp_file out f' in
  let _ = flush out in
  close_out out
  (*print_endline (Ast.string_of_file f')*)
