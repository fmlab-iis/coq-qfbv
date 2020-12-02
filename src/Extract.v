
(* Note: the file name cannot be Extraction.v. *)

From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Coq Require Import ExtrOcamlIntConv ExtrOcamlNatInt.
From Coq Require Import Arith List.
From mathcomp Require Import tuple.
From nbits Require Import NBits.
From ssrlib Require Import Var.
From BitBlasting Require Import QFBV CNF BBCommon.
From BBCache Require Import CacheFlatten CacheHash QFBVHash.
From BBCache Require Import BitBlastingInit BitBlastingCacheHash.

Extraction Language OCaml.

(* Avoid name clashes *)
Extraction Blacklist Nat Int List String.

Cd "src/ocaml/extraction".
Separate Extraction
         seq.catrev nat_of_int n_of_int int_of_nat int_of_n
         NBitsDef.from_string NBitsDef.from_hex NBitsDef.from_bin
         NBitsDef.to_hex NBitsDef.to_nat NBitsDef.to_bin
         QFBV.well_formed_bexp QFBV.well_formed_bexps
         init_vm init_gen init_hcache CacheHash.reset_ct
         QFBVHash.hash_exp QFBVHash.hash_bexp QFBVHash.unhash_hashed_exp QFBVHash.unhash_hashed_bexp
         bit_blast_bexp_hcache bit_blast_bexp_hcache_tflatten bit_blast_bexps_hcache_conjs
         Seqs.tflatten add_prelude
         max_var_of_cnf num_clauses dimacs_cnf_with_header.
Cd "../../..".
