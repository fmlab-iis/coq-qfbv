
(*
 * Require the following libraries:
 * - coq-nbit from https://github.com/mht208/coq-nbits
 * - ssrlib from https://github.com/mht208/coq-ssrlib.git
 *)

From Coq Require Import Arith ZArith OrderedType.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import Types SsrOrder Var Nats ZAriths Tactics.
From BitBlasting Require Import Typ TypEnv State QFBV CNF BBExport AdhereConform
     BitBlastingDef BitBlastingNewer BitBlastingPreserve BitBlastingCorrect
     BitBlastingMkEnv BitBlastingConsistent BitBlastingSat .

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(* ===== mk_env ===== *)

Definition init_vm := SSAVM.empty word.
Definition init_gen := (var_tt + 1)%positive.
Definition init_env : env := fun _ => true.

Lemma init_newer_than_vm :
  newer_than_vm init_gen init_vm.
Proof.
  done.
Qed.

Lemma init_newer_than_tt :
  newer_than_lit init_gen lit_tt.
Proof.
  done.
Qed.

Lemma init_tt :
  interp_lit init_env lit_tt.
Proof.
  done.
Qed.

Definition mk_env (s : SSAStore.t) (e : QFBV.bexp) : env :=
  let '(m', E', g, cs, lr) := mk_env_bexp init_vm s init_env init_gen e in
  E'.

Lemma init_consistent :
  forall s, consistent init_vm init_env s.
Proof.
  move=> s x. rewrite /consistent1 /init_vm. rewrite SSAVM.Lemmas.empty_o. done.
Qed.

Lemma mk_env_consistent :
  forall s e te m g cs lr,
    bit_blast_bexp te init_vm init_gen e = (m, g, cs, lr) ->
    AdhereConform.conform_bexp e s te ->
    QFBV.well_formed_bexp e te ->
    consistent m (mk_env s e) s.
Proof.
  move=> s e te m g cs lr Hbb Hcf Hwf. rewrite /mk_env.
  case Henv: (mk_env_bexp init_vm s init_env init_gen e) => [[[[m' E'] g'] cs'] lr'].
  move: (mk_env_bexp_is_bit_blast_bexp Hcf Hwf Henv). rewrite Hbb. case=> Hm Hg Hcs Hlr.
  rewrite Hm. apply: (mk_env_bexp_consistent Henv init_newer_than_vm).
  exact: init_consistent.
Qed.

Lemma mk_env_tt :
  forall s e, interp_lit (mk_env s e) lit_tt.
Proof.
  move=> s e. rewrite /mk_env.
  set m' := mk_env_bexp init_vm s init_env init_gen e.
  have: mk_env_bexp init_vm s init_env init_gen e = m' by reflexivity. move: m'.
  case=> [[[[m' E'] g'] cs'] lr'] Henv.
  rewrite (env_preserve_lit (mk_env_bexp_preserve Henv) init_newer_than_tt).
  exact: init_tt.
Qed.

Lemma mk_env_sat :
  forall s e te m g cs lr,
    bit_blast_bexp te init_vm init_gen e = (m, g, cs, lr) ->
    AdhereConform.conform_bexp e s te ->
    QFBV.well_formed_bexp e te ->
    interp_cnf (mk_env s e) cs.
Proof.
  move=> s e te m g cs lr Hbb Hcf Hwf. move: (mk_env_tt s e). rewrite /mk_env.
  set m' := mk_env_bexp init_vm s init_env init_gen e.
  have: mk_env_bexp init_vm s init_env init_gen e = m' by reflexivity. move: m'.
  case=> [[[[m' E'] g'] cs'] lr'] Henv. move: (mk_env_bexp_is_bit_blast_bexp Hcf Hwf Henv).
  rewrite Hbb; case=> _ _ -> _ Htt.
  exact: (mk_env_bexp_sat Henv init_newer_than_vm init_newer_than_tt Hwf).
Qed.


(* ===== mk_state ===== *)

Fixpoint lits_as_bits E (ls : word) : bits :=
  match ls with
  | [::] => [::]
  | hd::tl => joinlsb (interp_lit E hd) (lits_as_bits E tl)
  end .

Lemma enc_bits_lits_as_bits :
  forall E (ls : word),
    enc_bits E ls (lits_as_bits E ls).
Proof.
  move => E .
  elim .
  - done.
  - move => l ls IH .
    rewrite /= enc_bits_cons IH /= /enc_bit eqxx // .
Qed.

(* TypEnv.deftyp is Tuint 0. *)
Definition init_state : SSAStore.t := fun _ => from_nat 0 0.

Definition mk_state (E : env) (m : vm) : SSAStore.t :=
  (SSAVM.fold (fun v ls s => SSAStore.upd v (lits_as_bits E ls) s) m init_state).

Lemma mk_state_find :
  forall E m x ls,
    SSAVM.find x m = Some ls ->
    SSAStore.acc x (mk_state E m) = lits_as_bits E ls.
Proof.
  move=> E m.
  apply: (@SSAVM.Lemmas.OP.P.fold_rec
            word (SSAStore.t)
            (fun m s =>
               forall x ls,
                 SSAVM.find x m = Some ls ->
                 SSAStore.acc x s = lits_as_bits E ls)
            (fun v ls s => SSAStore.upd v (lits_as_bits E ls) s)
            init_state
            m).
  - move=> m0 Hempty x ls Hfind. rewrite (SSAVM.Lemmas.Empty_find _ Hempty) in Hfind.
    discriminate.
  - move=> x lsx s m' m'' Hmapsto_xm Hin_xm' Hadd IH. move=> y lsy Hfind_y.
    case Hyx: (y == x).
    + rewrite (SSAStore.acc_upd_eq Hyx). move: (Hadd y).
      rewrite Hfind_y (SSAVM.Lemmas.find_add_eq Hyx). case=> ->. reflexivity.
    + move/idP/negP: Hyx => Hyx. rewrite (SSAStore.acc_upd_neq  Hyx).
      apply: IH. move: (Hadd y). rewrite Hfind_y. move/negP: Hyx => Hyx.
      rewrite (SSAVM.Lemmas.find_add_neq Hyx). by move=> ->; reflexivity.
Qed.

Lemma mk_state_consistent :
  forall E m, consistent m E (mk_state E m).
Proof.
  move=> E m x. rewrite /consistent1. case Hfind: (SSAVM.find x m); last by trivial.
  rewrite (mk_state_find _ Hfind). exact: enc_bits_lits_as_bits.
Qed.

Lemma size_bit_blast_var' g n g' vs' :
  bit_blast_var' g n = (g', vs') -> size vs' = n .
Proof .
  elim : n g g' vs' => [ |n IH] g g' vs' .
  - case => _ <- // .
  - rewrite /bit_blast_var' /= -/bit_blast_var' .
    dcase (bit_blast_var' (g+1)%positive n) => [[g'' tl] Hbbr] .
    case => _ <- /= .
    rewrite (IH _ _ _ Hbbr) // .
Qed .

Lemma size_lits_as_bits E ls :
  size ls = size (lits_as_bits E ls) .
Proof .
  elim ls; first done .
  move => a l IH .
  rewrite /= IH // .
Qed .

Lemma bit_blast_adhere_exp :
  forall e te m m' g g' cs' lr',
    AdhereConform.adhere m te ->
    bit_blast_exp te m g e = (m', g', cs', lr') ->
    AdhereConform.adhere m' te
with
bit_blast_adhere_bexp :
  forall e te m m' g g' cs' lr',
    AdhereConform.adhere m te ->
    bit_blast_bexp te m g e = (m', g', cs', lr') ->
    AdhereConform.adhere m' te .
Proof .
  (* bit_blast_adhere_exp *)
  elim; rewrite /= .
  - move => v te m m' g g' cs lr Hadm .
    case : (SSAVM.find v m) .
    + move => a; case => <- _ _ _ // .
    + rewrite /bit_blast_var .
      dcase (bit_blast_var' g (SSATE.vsize v te)) => [[g'0 vs] Hbbr ] .
      case => <- _ _ _ .
      rewrite /adhere => u .
      case Heq : (u == v) .
      * rewrite (eqP Heq) => _ .
        have Hfind : (SSAVM.M.find v (SSAVM.M.add v vs m) = Some vs) .
        { apply : SSAVM.Lemmas.find_add_eq; done . }
        exists vs .
        rewrite Hfind (size_bit_blast_var' Hbbr) // .
      * have Hneq : ~(SSAVM.E.eq u v) .
        { rewrite /SSAVM.E.eq Heq // . }
        rewrite (SSAVM.Lemmas.mem_add_neq Hneq) => Hmem .
        rewrite (SSAVM.Lemmas.find_add_neq Hneq) .
        apply : (Hadm u Hmem) .
  - move =>b te m m' g g' cs' lr' Hadm .
    case => <- _ _ _ // .
  - elim => /= [e IHe te m m' g g' cs' lr' Hadm |
                e IHe te m m' g g' cs' lr' Hadm |
                i j e IHe te m m' g g' cs' lr' Hadm |
                n e IHe te m m' g g' cs' lr' Hadm |
                n e IHe te m m' g g' cs' lr' Hadm |
                n e IHe te m m' g g' cs' lr' Hadm |
                n e IHe te m m' g g' cs' lr' Hadm];
      dcase (bit_blast_exp te m g e) => [[[[m1 g1] cs1] ls1] Hbbe] .
    + dcase (bit_blast_not g1 ls1) => [[[gr csr] lsr] _];
      case => <- _ _ _; apply : (IHe _ _ _ _ _ _ _ Hadm Hbbe) .
    + dcase (bit_blast_neg g1 ls1) => [[[gr csr] lsr] _];
      case => <- _ _ _; apply : (IHe _ _ _ _ _ _ _ Hadm Hbbe) .
    + case => <- _ _ _; apply : (IHe _ _ _ _ _ _ _ Hadm Hbbe) .
    + case => <- _ _ _; apply : (IHe _ _ _ _ _ _ _ Hadm Hbbe) .
    + case => <- _ _ _; apply : (IHe _ _ _ _ _ _ _ Hadm Hbbe) .
    + case => <- _ _ _; apply : (IHe _ _ _ _ _ _ _ Hadm Hbbe) .
    + case => <- _ _ _; apply : (IHe _ _ _ _ _ _ _ Hadm Hbbe) .
  - elim => /= e0 IH0 e1 IH1 te m m' g g' cs' lr' Hadm;
      dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] ls1] Hbbe0];
      dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hbbe1];
      move : (IH0 _ _ _ _ _ _ _ Hadm Hbbe0) => {Hadm Hbbe0} Hadm1;
      move : (IH1 _ _ _ _ _ _ _ Hadm1 Hbbe1) => {Hadm1 Hbbe1} Hadm2 .
    + dcase (bit_blast_and g2 ls1 ls2) => [[[gr csr] lsr] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_or g2 ls1 ls2) => [[[gr csr] lsr] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_xor g2 ls1 ls2) => [[[gr csr] lsr] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_add g2 ls1 ls2) => [[[gr csr] lsr] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_sub g2 ls1 ls2) => [[[gr csr] lsr] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_mul g2 ls1 ls2) => [[[gr csr] lsr] _];
      case => <- _ _ _ // .
    + case => <- _ _ _ // .
    + case => <- _ _ _ // .
    + case => <- _ _ _ // .
    + dcase (bit_blast_shl g2 ls1 ls2) => [[[gr csr] lsr] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_lshr g2 ls1 ls2) => [[[gr csr] lsr] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_ashr g2 ls1 ls2) => [[[gr csr] lsr] _];
      case => <- _ _ _ // .
    + case => <- _ _ _ // .
  - move => b e0 IH0 e1 IH1 te m m' g g' cs' lr' Hadm .
    dcase (bit_blast_bexp te m g b) => [[[[mc gc] csc] lc] Hbbc] .
    move : (bit_blast_adhere_bexp b _ _ _ _ _ _ _ Hadm Hbbc) => {Hadm Hbbc} Hadmc .
    dcase (bit_blast_exp te mc gc e0) => [[[[m1 g1] cs1] ls1] Hbbe0] .
    move : (IH0 _ _ _ _ _ _ _ Hadmc Hbbe0) => {Hadmc Hbbe0} Hadm1 .
    dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hbbe1] .
    move : (IH1 _ _ _ _ _ _ _ Hadm1 Hbbe1) => {Hadm1 Hbbe1} Hadm2 .
    dcase (bit_blast_ite g2 lc ls1 ls2) => [[[gr csr] lsr] _ ] .
    case => <- _ _ _ // .
  (* bit_blast_adhere_bexp *)
  elim; rewrite /= .
  - move => te m m' g g' cs' lr' Hadm .
    case => <- _ _ _ // .
  - move => te m m' g g' cs' lr' Hadm .
    case => <- _ _ _ // .
  - elim => e0 e1 te m m' g g' cs' lr' Hadm;
      dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] ls1] Hbbe0];
      move : (bit_blast_adhere_exp e0 _ _ _ _ _ _ _ Hadm Hbbe0) => {Hadm Hbbe0} Hadm1;
      dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hbbe1];
      move : (bit_blast_adhere_exp e1 _ _ _ _ _ _ _ Hadm1 Hbbe1) => {Hadm1 Hbbe1} Hadm2 .
    + dcase (bit_blast_eq g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_ult g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_ule g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_ugt g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_uge g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_slt g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_sle g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_sgt g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_sge g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_uaddo g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_usubo g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_umulo g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_saddo g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_ssubo g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
    + dcase (bit_blast_smulo g2 ls1 ls2) => [[[g'0 cs] r] _];
      case => <- _ _ _ // .
  - move => b IHb te m m' g g' cs' lr' Hadm .
    dcase (bit_blast_bexp te m g b) => [[[[m1 g1] cs1] l1] Hbbe] .
    case => <- _ _ _ .
    apply : (bit_blast_adhere_bexp b _ _ _ _ _ _ _ Hadm Hbbe) .
  - move => b0 IH0 b1 IH1 te m m' g g' cs' lr' Hadm .
    dcase (bit_blast_bexp te m g b0) => [[[[m1 g1] cs1] l1] Hbbe0] .
    move : (IH0 _ _ _ _ _ _ _ Hadm Hbbe0) => {Hadm Hbbe0} Hadm1 .
    dcase (bit_blast_bexp te m1 g1 b1) => [[[[m2 g2] cs2] l2] Hbbe1] .
    move : (IH1 _ _ _ _ _ _ _ Hadm1 Hbbe1) => {Hadm1 Hbbe1} Hadm2 .
    case => <- _ _ _ // .
  - move => b0 IH0 b1 IH1 te m m' g g' cs' lr' Hadm .
    dcase (bit_blast_bexp te m g b0) => [[[[m1 g1] cs1] l1] Hbbe0] .
    move : (IH0 _ _ _ _ _ _ _ Hadm Hbbe0) => {Hadm Hbbe0} Hadm1 .
    dcase (bit_blast_bexp te m1 g1 b1) => [[[[m2 g2] cs2] l2] Hbbe1] .
    move : (IH1 _ _ _ _ _ _ _ Hadm1 Hbbe1) => {Hadm1 Hbbe1} Hadm2 .
    case => <- _ _ _ // .
Qed .

Lemma mk_state_conform_exp :
  forall e te E m',
    AdhereConform.bound_exp e m' ->
    AdhereConform.adhere m' te ->
    AdhereConform.conform_exp e (mk_state E m') te
with
mk_state_conform_bexp :
  forall e te E m',
    AdhereConform.bound_bexp e m' ->
    AdhereConform.adhere m' te ->
    AdhereConform.conform_bexp e (mk_state E m') te .
Proof .
  (* mk_state_conform_exp *)
  elim; rewrite /= .
  - move => v te E m' Hmem Had .
    elim : (Had _ Hmem) => ls [Hfind Hsize] .
    rewrite (eqP Hsize) (mk_state_find _ Hfind) -size_lits_as_bits // .
  - done .
  - elim => /= [e IHe te E m' Hbound Had |
                e IHe te E m' Hbound Had |
                i j e IHe te E m' Hbound Had |
                n e IHe te E m' Hbound Had |
                n e IHe te E m' Hbound Had |
                n e IHe te E m' Hbound Had |
                n e IHe te E m' Hbound Had];
              exact : (IHe _ _ _ Hbound Had) .
  - elim => /= e0 IH0 e1 IH1 te E m' /andP [Hbound0 Hbound1] Had;
      rewrite (IH0 _ _ _ Hbound0 Had) (IH1 _ _ _ Hbound1 Had) // .
  - move => c e0 IH0 e1 IH1 te E m' /andP [/andP [Hboundc Hbound0] Hbound1] Had .
    rewrite (mk_state_conform_bexp c _ _ _ Hboundc Had)
            (IH0 _ _ _ Hbound0 Had) (IH1 _ _ _ Hbound1 Had) // .
  (* mk_state_conform_bexp *)
  elim; rewrite /= .
  - done .
  - done .
  - elim => e0 e1 te E m' /andP [Hbound0 Hbound1] Had;
      rewrite (mk_state_conform_exp e0 _ _ _ Hbound0 Had)
              (mk_state_conform_exp e1 _ _ _ Hbound1 Had) // .
  - move => b IHb te E m'; apply : IHb .
  - move => b0 IH0 b1 IH1 te E m' /andP [Hbound0 Hbound1] Had;
      rewrite (IH0 _ _ _ Hbound0 Had) (IH1 _ _ _ Hbound1 Had) // .
  - move => b0 IH0 b1 IH1 te E m' /andP [Hbound0 Hbound1] Had;
      rewrite (IH0 _ _ _ Hbound0 Had) (IH1 _ _ _ Hbound1 Had) // .
Qed .

Lemma bit_blast_bound_exp :
  forall e te m m' g g' cs' lrs',
    bit_blast_exp te m g e = (m', g', cs', lrs') ->
    AdhereConform.bound_exp e m'
with
bit_blast_bound_bexp :
  forall e te m m' g g' cs' lrs',
    bit_blast_bexp te m g e = (m', g', cs', lrs') ->
    AdhereConform.bound_bexp e m' .
Proof .
  (* bit_blast_bound_exp *)
  elim; rewrite /= .
  - move => v te m m' g g' cs' lrs' .
    case Hf : (SSAVM.find v m) .
    + case => <- _ _ _; exact : (SSAVM.Lemmas.find_some_mem Hf) .
    + dcase (bit_blast_var te g v) => [[[g'0 cs] rs] Hbbr] .
      case => <- _ _ _ .
      exact : SSAVM.Lemmas.mem_add_eq .
  - done .
  - elim => /= [e IHe te m m' g g' cs' lrs' |
                e IHe te m m' g g' cs' lrs' |
                i j e IHe te m m' g g' cs' lrs' |
                n e IHe te m m' g g' cs' lrs' |
                n e IHe te m m' g g' cs' lrs' |
                n e IHe te m m' g g' cs' lrs' |
                n e IHe te m m' g g' cs' lrs'];
      dcase (bit_blast_exp te m g e) => [[[[m1 g1] cs1] ls1] Hbbe] .
    + dcase (bit_blast_not g1 ls1) => [[[gr csr] lsr] Hbbr];
        case => <- _ _ _;
        exact : (IHe _ _ _ _ _ _ _ Hbbe) .
    + dcase (bit_blast_neg g1 ls1) => [[[gr csr] lsr] Hbbr];
        case => <- _ _ _;
        exact : (IHe _ _ _ _ _ _ _ Hbbe) .
    + case => <- _ _ _; exact : (IHe _ _ _ _ _ _ _ Hbbe) .
    + case => <- _ _ _; exact : (IHe _ _ _ _ _ _ _ Hbbe) .
    + case => <- _ _ _; exact : (IHe _ _ _ _ _ _ _ Hbbe) .
    + case => <- _ _ _; exact : (IHe _ _ _ _ _ _ _ Hbbe) .
    + case => <- _ _ _; exact : (IHe _ _ _ _ _ _ _ Hbbe) .
  - elim => /= e0 IH0 e1 IH1 te m m' g g' cs' lrs';
      dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] ls1] Hbbe0];
      dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hbbe1];
      move : (bit_blast_exp_preserve Hbbe0)
             (bit_blast_exp_preserve Hbbe1) => Hmm1 Hm1m2 .
    + dcase (bit_blast_and g2 ls1 ls2) => [[[gr csr] lsr] Hbbr];
      case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_or g2 ls1 ls2) => [[[gr csr] lsr] Hbbr];
      case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_xor g2 ls1 ls2) => [[[gr csr] lsr] Hbbr];
      case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_add g2 ls1 ls2) => [[[gr csr] lsr] Hbbr];
      case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_sub g2 ls1 ls2) => [[[gr csr] lsr] Hbbr];
      case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_mul g2 ls1 ls2) => [[[gr csr] lsr] Hbbr];
      case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_shl g2 ls1 ls2) => [[[gr csr] lsr] Hbbr];
      case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_lshr g2 ls1 ls2) => [[[gr csr] lsr] Hbbr];
      case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_ashr g2 ls1 ls2) => [[[gr csr] lsr] Hbbr];
      case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
    + case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (IH1 _ _ _ _ _ _ _ Hbbe1) // .
  - move => c e0 IH0 e1 IH1 te m m' g g' cs' lrs' .
    dcase (bit_blast_bexp te m g c) => [[[[mc gc] csc] lc] Hbbc] .
    dcase (bit_blast_exp te mc gc e0) => [[[[m1 g1] cs1] ls1] Hbb0] .
    dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hbb1] .
    dcase (bit_blast_ite g2 lc ls1 ls2) => [[[gr csr] lsr] Hbbr] .
    case => <- _ _ _ .
    move : (bit_blast_exp_preserve Hbb0)
           (bit_blast_exp_preserve Hbb1) => Hmcm1 Hm1m2 .
    move : (vm_preserve_trans Hmcm1 Hm1m2) => Hmcm2 .
    rewrite (vm_preserve_bound_bexp (bit_blast_bound_bexp c _ _ _ _ _ _ _ Hbbc) Hmcm2)
            (vm_preserve_bound_exp (IH0 _ _ _ _ _ _ _ Hbb0) Hm1m2)
            (IH1 _ _ _ _ _ _ _ Hbb1) // .
  (* bit_blast_bound_bexp *)
  elim; rewrite /= .
  - done .
  - done .
  - elim => /= e0 e1 te m m' g g' cs' lrs';
      dcase (bit_blast_exp te m g e0) => [[[[m1 g1] cs1] ls1] Hbbe0];
      dcase (bit_blast_exp te m1 g1 e1) => [[[[m2 g2] cs2] ls2] Hbbe1];
      move : (bit_blast_exp_preserve Hbbe1) => Hm1m2 .
    + dcase (bit_blast_eq g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_ult g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_ule g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_ugt g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_uge g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_slt g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_sle g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_sgt g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_sge g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_uaddo g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_usubo g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_umulo g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_saddo g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_ssubo g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
    + dcase (bit_blast_smulo g2 ls1 ls2) => [[[g'0 cs] r] Hbbr]; case => <- _ _ _;
      rewrite (vm_preserve_bound_exp (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe0) Hm1m2)
              (bit_blast_bound_exp _ _ _ _ _ _ _ _ Hbbe1) // .
  - move => c IHc te m m' g g' cs' lrs' .
    dcase (bit_blast_bexp te m g c) => [[[[m1 g1] cs1] l1] Hbbc] .
    case => <- _ _ _ ; rewrite (IHc _ _ _ _ _ _ _ Hbbc) // .
  - move => b0 IH0 b1 IH1 te m m' g g' cs' lrs' .
    dcase (bit_blast_bexp te m g b0) => [[[[m1 g1] cs1] l1] Hbb0] .
    dcase (bit_blast_bexp te m1 g1 b1) => [[[[m2 g2] cs2] l2] Hbb1] .
    case => <- _ _ _ .
    move : (bit_blast_bexp_preserve Hbb1) => Hm1m2 .
    rewrite (vm_preserve_bound_bexp (IH0 _ _ _ _ _ _ _ Hbb0) Hm1m2)
            (IH1 _ _ _ _ _ _ _ Hbb1) // .
  - move => b0 IH0 b1 IH1 te m m' g g' cs' lrs' .
    dcase (bit_blast_bexp te m g b0) => [[[[m1 g1] cs1] l1] Hbb0] .
    dcase (bit_blast_bexp te m1 g1 b1) => [[[[m2 g2] cs2] l2] Hbb1] .
    case => <- _ _ _ .
    move : (bit_blast_bexp_preserve Hbb1) => Hm1m2 .
    rewrite (vm_preserve_bound_bexp (IH0 _ _ _ _ _ _ _ Hbb0) Hm1m2)
            (IH1 _ _ _ _ _ _ _ Hbb1) // .
Qed .

(* ===== Soundness and completeness ===== *)

Lemma valid_implies_unsat :
  forall premises goal,
    (forall E, ~~ interp_cnf E (add_prelude premises) || interp_lit E goal) ->
    ~ (sat (add_prelude ([::neg_lit goal]::premises))).
Proof.
  move=> premises goal H1 [E H2]. move: (H1 E) => {H1} H1.
  rewrite add_prelude_cons in H2. move/andP: H2 => [H2 H3].
  move/orP: H1. case => H1.
  - move/negP: H1. apply. exact: H3.
  - rewrite add_prelude_expand in H2. move/andP: H2 => [_ H2].
    rewrite /= interp_lit_neg_lit in H2. move/negP: H2; apply.
    rewrite H1 // .
Qed.

Lemma unsat_implies_valid :
  forall premises goal,
    ~ (sat (add_prelude ([::neg_lit goal]::premises))) ->
    (forall E, ~~ interp_cnf E (add_prelude premises) || interp_lit E goal).
Proof.
  move=> premises goal H E. case Hgoal: (interp_lit E goal).
  - by rewrite orbT.
  - rewrite orbF. apply/negP => H2. apply: H. exists E.
    rewrite add_prelude_cons H2 /= .
    rewrite add_prelude_expand /=  interp_lit_neg_lit.
    rewrite Hgoal /= . move : (add_prelude_tt H2) => Htt .
    rewrite /interp_lit /lit_tt in Htt .
    rewrite Htt // .
Qed.


(* NOTE: change valid e to
      forall s, conform s te -> QFBV.eval_bexp e s
 *)
Theorem bit_blast_sound :
  forall (e : QFBV.bexp) te m' g' cs lr,
    bit_blast_bexp te init_vm init_gen e = (m', g', cs, lr) ->
    QFBV.well_formed_bexp e te ->
    ~ (sat (add_prelude ([::neg_lit lr]::cs))) ->
    (forall s,
        AdhereConform.conform_bexp e s te ->
        QFBV.eval_bexp e s) .
Proof.
  move=> e te m' g' cs lr Hblast Hwf Hsat s Hcf.
  move: (unsat_implies_valid Hsat) => {Hsat} Hsat.
  move: (Hsat (mk_env s e)) => {Hsat} Hsat.
  move: (mk_env_sat Hblast Hcf Hwf) => Hcs. move: (mk_env_tt s e) => Htt.
  have Hprelude: interp_cnf (mk_env s e) (add_prelude cs)
    by rewrite add_prelude_expand Hcs Htt.
  move: ((bit_blast_bexp_correct Hblast Hcf (mk_env_consistent Hblast Hcf Hwf) Hprelude) Hwf).
  rewrite /enc_bit. move=> /eqP <-.
  rewrite Hprelude /= in Hsat. exact: Hsat.
Qed.

Theorem bit_blast_complete :
  forall (e : QFBV.bexp) te m' g' cs lr,
    bit_blast_bexp te init_vm init_gen e = (m', g', cs, lr) ->
    QFBV.well_formed_bexp e te ->
    (forall s, AdhereConform.conform_bexp e s te ->
               QFBV.eval_bexp e s)
    ->
    ~ (sat (add_prelude ([::neg_lit lr]::cs))).
Proof.
  move=> e te m' g' cs lr Hblast Hwf He.
  move=> [E Hcs].
  rewrite add_prelude_cons in Hcs. move/andP: Hcs => [Hlr Hcs].
  rewrite add_prelude_expand in Hlr. move/andP: Hlr => [Htt Hlr].
  rewrite /= interp_lit_neg_lit in Hlr.
  have init_vm_adhere : (AdhereConform.adhere init_vm te) .
  { done . }
  move : (bit_blast_adhere_bexp init_vm_adhere Hblast) => Hadm' .
  move : (bit_blast_bound_bexp Hblast) => Hbound .
  move : (mk_state_conform_bexp E Hbound Hadm') => Hcf .
  move : (He (mk_state E m') Hcf) => {He} He .
  move: (bit_blast_bexp_correct Hblast Hcf (mk_state_consistent E m') Hcs Hwf).
  rewrite /enc_bit => /eqP H. rewrite -H in He.
  rewrite He in Hlr. exact: not_false_is_true.
Qed.

Definition bexp_to_cnf te e :=
  let '(m', g', cs, lr) := bit_blast_bexp te init_vm init_gen e in
  add_prelude ([::neg_lit lr]::cs).
