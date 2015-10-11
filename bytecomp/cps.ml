open Lambda

let rec is_atom tm =
  match tm with
  | Lvar _ | Lconst _ -> true
  | Lprim (_, args) -> List.for_all is_atom args
  | _ -> false

module C : sig
  type lambda_cps = private lambda
  type cont_ident
  type cont

  type k =
    | Cid of Ident.t
    | Clambda of Ident.t * lambda

  val create_cont_ident : string -> cont_ident
  val std : cont_ident -> Ident.t
  val err : cont_ident -> Ident.t

  val mkcont :
    ?std:k ->
    ?err:k ->
    cont_ident ->
    cont

  val abs_cont : cont_ident -> lambda -> lambda_cps
  val continue_with : cont -> lambda_cps -> lambda

  val assert_cps : lambda -> lambda_cps

end = struct
  type lambda_cps = lambda
  type cont_ident = Ident.t * Ident.t
  type k =
    | Cid of Ident.t
    | Clambda of Ident.t * lambda

  let lambda_of_k = function
    | Cid k -> Lvar k
    | Clambda (i, t) ->
        Lfunction { kind = Curried; params = [i]; body = t }

  type cont = k * k

  let create_cont_ident name =
    (Ident.create (name ^ "k")),
    (Ident.create (name ^ "ke"))

  let std (k, ke) =
    k

  let err (k, ke) =
    ke

  let mkcont ?std ?err (k, ke) =
    let mkk o k = match o with
      | None -> Cid k
      | Some k -> k in
    (mkk std k, mkk err ke)

  let abs_cont (k, ke) t =
    Lfunction {
      kind = Curried;
      params = [k; ke];
      body = t;
    }

  let continue_with (c, ce) tm =
    match tm, c, ce with
    | Lfunction {
      kind;
      params = [k; ke];
      body = Lapply (Lvar k', [atom], _)
    }, c, ce
      when k = k' && is_atom atom ->
        begin match c with
        | Cid k ->
            Lapply (Lvar k, [atom], no_apply_info)
        | Clambda (v, vcont) ->
            subst_lambda (Ident.add v atom Ident.empty) vcont
        end
    | Lfunction { kind; params = [k; ke]; body }, Cid ck, Cid ce ->
        subst_lambda
          (Ident.empty |> Ident.add k (Lvar ck) |> Ident.add ke (Lvar ce))
          body
    | Lapply (f, args, info), c, ce ->
        Lapply (f, args @ [lambda_of_k c; lambda_of_k ce], info)
    | t, c, ce ->
        Lapply (t, [lambda_of_k c; lambda_of_k ce], no_apply_info)

  let assert_cps t =
    t
end

open C

let rec cps_eval_chain
    (default_cont : cont_ident)
    (id_tms: (Ident.t * lambda_cps) list)
    (body: lambda):
  lambda
  =
  List.fold_right (fun (id, tm) acc ->
    continue_with
      (mkcont ~std:(Clambda (id, acc)) default_cont)
      tm
  ) id_tms body

and cps (tm: lambda): lambda_cps =
  match tm with
  | _ when is_atom tm ->
      let k = create_cont_ident "" in
      abs_cont k (Lapply (Lvar (std k), [tm], no_apply_info))

  | Lapply (f, args, info) ->
      let k = create_cont_ident "" in
      let fv = Ident.create "f" in
      let args_cps = List.map cps args in
      let args_idents = List.map (fun _ -> Ident.create "v") args in
      let final_apply =
        continue_with
          (mkcont k)
          (assert_cps
             (Lapply (Lvar fv,
                      List.map (fun i -> Lvar i) args_idents,
                      info)))
      in
      abs_cont k
        (cps_eval_chain k
           (List.combine (fv :: args_idents) (cps f :: args_cps))
           final_apply)

  | Lfunction { kind; params; body } ->
      (* How do we handle kind = Tupled ? *)
      List.fold_right (fun v (acc: lambda_cps) ->
        let k = create_cont_ident "" in
        abs_cont k
          (Lapply (Lvar (std k),
                   [Lfunction {
                      kind = Curried;
                      params = [v];
                      body = (acc :> lambda)
                    }],
                   no_apply_info))
      ) params (cps body)

  | Llet (kind, ident, e1, e2) ->
      let k = create_cont_ident "" in
      abs_cont k
        (cps_eval_chain k
           [(ident, cps e1)]
           (continue_with (mkcont k) (cps e2)))

  | Lsequence (e1, e2) ->
      let dummy = Ident.create "_" in
      cps (Llet (Strict, dummy, e1, e2))

  | Lletrec (decl, body) ->
      let k = create_cont_ident "" in
      let decl_idents = List.map (fun (i, t) ->
        (i, Ident.create ("x" ^ i.Ident.name), t)) decl in
      let decl_cps = List.map (fun (i, xi, t) ->
        (xi, (cps t : lambda_cps :> lambda))
      ) decl_idents in

      abs_cont k
        (Lletrec (
           decl_cps,
           (cps_eval_chain k
              (List.map (fun (i, xi, _) -> (i, assert_cps (Lvar xi))) decl_idents)
              (continue_with (mkcont k) (cps body)))
         ))

  | Lprim (Praise _ (* ? *), [e]) ->
      let k = create_cont_ident "" in
      abs_cont k
        (continue_with
           (mkcont ~std:(Cid (err k)) k)
           (cps e))

  | Lprim (prim, args) ->
      let k = create_cont_ident "" in
      let args_cps = List.map cps args in
      let args_idents = List.map (fun _ -> Ident.create "v") args in
      let final_apply =
        Lapply (
          Lvar (std k),
          [Lprim (prim, List.map (fun i -> Lvar i) args_idents)],
          no_apply_info
        ) in
      abs_cont k
        (cps_eval_chain k
           (List.combine args_idents args_cps)
           final_apply)

  | Ltrywith (body, exn, handle) ->
      let k = create_cont_ident "" in
      abs_cont k
        (continue_with
           (mkcont
              ~err:(Clambda (exn, continue_with (mkcont k) (cps handle)))
              k)
           (cps body))

  | _ -> failwith "not handled"

(* let toplevel_cps tm = *)
(*   let x = Ident.create "x" in *)
(*   let identity = Lfunction { kind = Curried; params = [x]; body = Lvar x } in *)

(*   match tm with *)
(*   | Lprim (Psetglobal ident, [body]) -> *)
(*       Lprim (Psetglobal ident, [ *)
(*         Lapply (cps body, [identity], no_apply_info) *)
(*       ]) *)
(*   | _ -> assert false *)

let cps tm =
  ((cps tm) :> lambda)

let toplevel_cps tm =
  (* TODO: proper uncaught exception handler *)
  let x = Ident.create "x" in
  let identity = Lfunction { kind = Curried; params = [x]; body = Lvar x } in

  Lapply (
    (cps tm :> lambda),
    [identity; identity],
    no_apply_info
  )
