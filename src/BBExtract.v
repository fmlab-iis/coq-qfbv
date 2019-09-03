
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple.
From BitBlasting Require Import QFBVSimple CNFSimple BBCommon BBSlice.
From ssrlib Require Import Var ZAriths Tactics.
From Bits Require Import bits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



(* ===== bit_blast_extract ===== *)

Definition bit_blast_extract w i j (g : generator) (ls : (j+(i-j+1)+w).-tuple literal) : generator * cnf * (i-j+1).-tuple literal :=
  bit_blast_slice g ls .

Definition mk_env_extract w i j (E : env) (g : generator) (ls : (j+(i-j+1)+w).-tuple literal) : env * generator * cnf * (i-j+1).-tuple literal :=
  mk_env_slice E g ls .
