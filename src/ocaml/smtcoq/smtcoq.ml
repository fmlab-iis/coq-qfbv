
open Smtlib.Ast

let supported_extensions = [ fn_bvxor; fn_zero_extend; fn_sign_extend; fn_bvule; fn_bvslt; fn_bvsle ]

let gen_tmp g = (g + 1, "__smtcoq_tmp_" ^ string_of_int g ^ "__")

let combine_asserts cmds =
  let is_assert c =
    match c with
    | CAssert _ -> true
    | _ -> false in
  let rec helper res cmds =
    match cmds with
    | [] -> CAssert res
    | (CAssert t)::tl -> helper (make_and res t) tl
    | _ -> failwith ("Never happen") in
  let (asserts, others) = List.partition is_assert cmds in
  let new_asserts =
    match asserts with
    | [] -> []
    | (CAssert t)::tl -> [helper t tl]
    | _ -> failwith ("Never happen") in
  List.rev_append (List.rev others) new_asserts

let prepend_bindings_to_assert vbs cmd =
  match cmd with
  | CAssert t -> CAssert (TLet (vbs, t))
  | _ -> cmd

let rec norm_ite_term g tm fm term =
  match term with
  | TConstant _ -> (g, [], term)
  | TVariable _ -> (g, [], term)
  | TApplication (QIdentifier (ISimple v), b::s::t::[]) when v = fn_ite -> let ty = ttyp_of_term tm fm s in
                                                                           begin
                                                                             match ty with
                                                                             | TBitVec n ->
                                                                                let (g1, cmds1, s') = norm_ite_term g tm fm s in
                                                                                let (g2, cmds2, t') = norm_ite_term g1 tm fm t in
                                                                                let (g3, tmp) = gen_tmp g2 in
                                                                                let tmp_var = make_var tmp in
                                                                                let cmds = [ CDeclareFun (tmp, [], make_bitvec_sort (Z.of_int n));
                                                                                             CAssert (make_ite b (make_eq tmp_var s') (make_eq tmp_var t')) ] in
                                                                                (g3, List.rev (List.rev_append cmds (List.rev_append cmds2 (List.rev cmds1))), tmp_var)
                                                                             | _ -> (g, [], term)
                                                                           end
  | TApplication (fn, fargs) -> let (g', cmds_rev, ts_rev) = List.fold_left (
                                                                 fun (g, cmds_rev, ts_rev) t ->
                                                                 let (g', cmds', t') = norm_ite_term g tm fm t in
                                                                 (g', List.rev_append cmds' cmds_rev, t'::ts_rev)
                                                               ) (g, [], []) fargs in
                                (g', List.rev cmds_rev, TApplication (fn, List.rev ts_rev))
  | TLet (bs, t) -> let (g', tm', cmds_rev, bs_rev) = List.fold_left (
                                                          fun (g, tm, cmds_rev, bs_rev) (v, t) ->
                                                          let (g', cmds', t') = norm_ite_term g tm fm t in
                                                          let tm' = M.add v (ttyp_of_term tm fm t) tm in
                                                          (g', tm', List.rev_append cmds' cmds_rev, (v, t')::bs_rev)
                                                        ) (g, tm, [], []) bs in
                    let bs' = List.rev bs_rev in
                    let (g'', cmds, t') = norm_ite_term g' tm' fm t in
                    let cmds' = List.rev (List.rev_map (prepend_bindings_to_assert bs') (combine_asserts cmds)) in
                    (g'', List.rev (List.rev_append cmds' cmds_rev), TLet (bs', t'))

let norm_ite_command g tm fm c =
  match c with
  | CSetLogic _ -> (g, tm, fm, [], c)
  | CSetInfo _ -> (g, tm, fm, [], c)
  | CSetOption _ -> (g, tm, fm, [], c)
  | CDeclareFun (fn, fargs, fsort) ->
     (* Only update maps *)
     begin
       match fargs with
       | [] -> (g, M.add fn (ttyp_of_sort fsort) tm, fm, [], c)
       | _ -> failwith("Function declaration with nonempty arguments is not supported.")
     end
  | CDefineFun (fn, fargs, fsort, fterm) ->
     begin
       match fargs with
       | [] -> let ty = ttyp_of_sort fsort in
               let tm' = M.add fn ty tm in
               let (g', cmds, fterm') = norm_ite_term g tm' fm fterm in
               (g', tm', fm, cmds, CDefineFun (fn, fargs, fsort, fterm'))
       | _ -> let fm' = M.add fn (fargs, fsort, fterm) fm in
              let (g', cmds, fterm') = norm_ite_term g tm fm' fterm in
              (g', tm, fm', cmds, CDefineFun (fn, fargs, fsort, fterm'))
     end
  | CAssert t -> let (g', cmds, t') = norm_ite_term g tm fm t in
                 (g', tm, fm, cmds, CAssert t')
  | CCheckSat -> (g, tm, fm, [], c)
  | CGetModel -> (g, tm, fm, [], c)
  | CExit -> (g, tm, fm, [], c)
  | CComment _ -> (g, tm, fm, [], c)

let norm_ite_script g tm fm script =
  let (g', tm', fm', cmds_rev) = List.fold_left (
                                     fun (g, tm, fm, cmds_rev) c ->
                                     let (g', tm', fm', cmds, c') = norm_ite_command g tm fm c in
                                     (g', tm', fm', c'::(List.rev_append cmds cmds_rev))
                                   ) (g, tm, fm, []) script in
  (g', tm', fm', List.rev cmds_rev)

(*
 * Thie is used to avoid the error "Uncaught exception Smtcoq_plugin.SmtForm.Make(Atom).NotWellTyped(_)." of SMTCoq.
 * For `ite b x y` where x and y are terms,
 * - replace occurrences of `ite b x y` with a fresh variable z
 * - add the assumption `ite b (= z x) (= z y)`
 *)
let norm_ite_file file =
  let g = 0 in
  let tm = M.empty in
  let fm = M.empty in
  let (_, _, _, cmds) = norm_ite_script g tm fm file in
  cmds




let gen_name g = (g + 1, "x" ^ string_of_int g)

let norm_name_identifier tm id =
  match id with
  | ISimple v -> (try ISimple (M.find v tm)
                  with Not_found -> id)
  | IIndexed (v, is) -> id

let norm_name_qual_identifier tm qi =
  match qi with
  | QIdentifier id -> QIdentifier (norm_name_identifier tm id)
  | QAnnotated (id, s) -> QAnnotated (norm_name_identifier tm id, s)

let rec norm_name_term g tm term =
  match term with
  | TConstant _ -> term
  | TVariable qi -> TVariable (norm_name_qual_identifier tm qi)
  | TApplication (fn, fargs) -> let fn' = norm_name_qual_identifier tm fn in
                                let fargs_rev = List.fold_left (
                                                    fun fargs_rev t ->
                                                    let t' = norm_name_term g tm t in
                                                    t'::fargs_rev
                                                  ) [] fargs in
                                TApplication (fn', List.rev fargs_rev)
  | TLet (bs, t) -> let (g', tm', bs_rev) = List.fold_left (
                                                fun (g, tm, bs_rev) (v, t) ->
                                                let (g', v') = gen_name g in
                                                let tm' = M.add v v' tm in
                                                let t' = norm_name_term g' tm' t in
                                                (g', tm', (v', t')::bs_rev)
                                              ) (g, tm, []) bs in
                    let t' = norm_name_term g' tm' t in
                    TLet (List.rev bs_rev, t')

let norm_name_command g tm c =
  match c with
  | CSetLogic _ -> (g, tm, c)
  | CSetInfo _ -> (g, tm, c)
  | CSetOption _ -> (g, tm, c)
  | CDeclareFun (fn, fargs, fsort) ->
     let (g', fn') = gen_name g in
     let tm' = M.add fn fn' tm in
     (g', tm', CDeclareFun (fn', fargs, fsort))
  | CDefineFun (fn, fargs, fsort, fterm) ->
     let (g1, fn') = gen_name g in
     let (g2, tm1, fargs_rev) = List.fold_left (
                                    fun (g, tm, fargs_rev) (v, s) ->
                                    let (g', v') = gen_name g in
                                    let tm' = M.add v v' tm in
                                    (g', tm', (v', s)::fargs_rev)
                                  ) (g1, tm, []) fargs in
     let fterm' = norm_name_term g2 tm1 fterm in
     let tm2 = M.add fn fn' tm1 in
     (g2, tm2, CDefineFun (fn', List.rev fargs_rev, fsort, fterm'))
  | CAssert t -> let t' = norm_name_term g tm t in
                 (g, tm, CAssert t')
  | CCheckSat -> (g, tm, c)
  | CGetModel -> (g, tm, c)
  | CExit -> (g, tm, c)
  | CComment _ -> (g, tm, c)

let norm_name_script g tm script =
  let (g', tm', cmds_rev) = List.fold_left (
                                fun (g, tm, cmds_rev) c ->
                                let (g', tm', c') = norm_name_command g tm c in
                                (g', tm', c'::cmds_rev)
                              ) (g, tm, []) script in
  (g', tm', List.rev cmds_rev)

let norm_name_file file =
  let g = 0 in
  let tm = M.empty in
  let (_, _, cmds) = norm_name_script g tm file in
  cmds
