
open Smtlib

val supported_extensions : string list

val norm_ite_file : Ast.file -> Ast.file

val norm_name_file : Ast.file -> Ast.file
