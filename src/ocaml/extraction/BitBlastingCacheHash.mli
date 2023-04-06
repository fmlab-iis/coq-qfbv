open BBCommon
open BBConj
open BBConst
open BBDisj
open BBIte
open BBLneg
open BBVar
open BitBlastingCCacheDef
open BitBlastingInit
open CNF
open CacheHash
open EqVar
open QFBVHash
open Seqs
open Seq

val bit_blast_exp_hcache :
  TypEnv.SSATE.env -> vm -> cache -> generator -> hexp ->
  (((vm * cache) * generator) * cnf list) * word

val bit_blast_bexp_hcache :
  TypEnv.SSATE.env -> vm -> cache -> generator -> hbexp ->
  (((vm * cache) * generator) * cnf list) * literal

val init_hcache : cache

val bit_blast_bexp_hcache_tflatten :
  TypEnv.SSATE.env -> vm -> cache -> generator -> hbexp ->
  (((vm * cache) * generator) * clause list) * literal

val bit_blast_hbexps_hcache_conjs_rec :
  TypEnv.SSATE.env -> vm -> cache -> generator -> cnf list -> cnf -> hbexp
  list -> (((vm * cache) * generator) * cnf list) * cnf

val bit_blast_hbexps_hcache_conjs :
  TypEnv.SSATE.env -> vm -> cache -> generator -> hbexp list ->
  (((vm * cache) * generator) * cnf list) * cnf

val bit_blast_bexps_hcache_conjs :
  TypEnv.SSATE.env -> QFBV.QFBV.bexp list -> ((vm * cache) * generator) * cnf
