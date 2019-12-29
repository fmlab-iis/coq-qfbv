
(* Note: the file name cannot be Extraction.v. *)

From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Coq Require Import ExtrOcamlZInt ExtrOcamlIntConv.
From Coq Require Import List.
From mathcomp Require Import tuple.
From nbits Require Import NBits.
From ssrlib Require Import Var.
From BitBlasting Require Import CNF BBCommon BitBlasting.

Extraction Language OCaml.

(* Avoid name clashes *)
Extraction Blacklist Nat Int List String.

Cd "src/extraction".
Separate Extraction
         seq.catrev nat_of_int n_of_int int_of_nat int_of_n
         from_string from_hex from_bin to_hex
         bexp_to_cnf max_var_of_cnf num_clauses dimacs_cnf_with_header.
Cd "../..".

