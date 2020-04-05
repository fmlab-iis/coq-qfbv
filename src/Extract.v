
(* Note: the file name cannot be Extraction.v. *)

From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Coq Require Import ExtrOcamlZInt ExtrOcamlIntConv.
From Coq Require Import List.
From mathcomp Require Import tuple.
From nbits Require Import NBits.
From ssrlib Require Import Var.
From BitBlasting Require Import QFBV CNF BBCommon BitBlasting.
From BBCache Require Import BitBlastingInit BitBlastingCache BitBlastingCCache.

Extraction Language OCaml.

(* Avoid name clashes *)
Extraction Blacklist Nat Int List String.

Cd "src/extraction".
Separate Extraction
         seq.catrev nat_of_int n_of_int int_of_nat int_of_n
         NBitsDef.from_string NBitsDef.from_hex NBitsDef.from_bin
         NBitsDef.to_hex NBitsDef.to_nat NBitsDef.to_bin
         QFBV.well_formed_bexp QFBV.well_formed_bexps
         init_vm init_gen init_cache init_ccache
         Cache.reset_ct CompCache.reset_ct
         bexp_to_cnf bexp_to_cnf_cache bexp_to_cnf_ccache
         max_var_of_cnf num_clauses dimacs_cnf_with_header.
Cd "../..".
