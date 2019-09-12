
(* Note: the file name cannot be Extraction.v. *)

From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Coq Require Import ExtrOcamlZInt ExtrOcamlIntConv.
From Coq Require Import List.
From mathcomp Require Import tuple.
From Bits Require Import bits.
From ssrlib Require Import Var.
From BitBlasting Require Import CNFSimple BBCommonSimple BitBlastingSimple.

Extraction Language OCaml.

(* Avoid name clashes *)
Extraction Blacklist Nat Int List String.

Cd "src/extraction".
Separate Extraction seq.catrev toHex nat_of_int n_of_int int_of_nat int_of_n bexp_to_cnf max_var_of_cnf num_clauses dimacs_cnf_with_header.
Cd "../..".

