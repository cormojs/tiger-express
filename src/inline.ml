open KNormal

let threshold = ref 100

let rec size = function
  | If ((_, _, _), e1, e2)
  | Let (VarDec (_, _, e1), e2) ->
    1 + size e1 + size e2
  | While ((_, _, _), e)
  | Let (TypeDecs _, e) ->
    1 + size e
  | Let (FunctionDecs fundecs, e) ->
    List.fold_left (fun x y -> x + y) (1 + size e)
    @@ List.map (fun (_, _, _, e) -> size e) fundecs
  | _ -> 1

let rec g env = function
  | If (cond, e1, e2) ->
    If (cond, g env e1, g env e2)
  | While (cond, e) ->
    While (cond, g env e)
  | Sequence es ->
    Sequence (List.map (g env) es)
  | Let (VarDec (name, typ, e1), e2) ->
    Let (VarDec (name, typ, g env e1), g env e2)
  | Let (TypeDecs decs, e) ->
    Let (TypeDecs decs, g env e)
  | Let (FunctionDecs fundecs, e) ->
    let update env (name, args, ret_typ, body) =
      if size body > !threshold 
      then env
      else M.add name (args, body) env in
    let env' = List.fold_left update env fundecs in
    let h env (name, args, ret_typ, body) = 
      (name, args, ret_typ, g env body) in
    let fundecs' = List.map (h env') fundecs in
    Let (FunctionDecs fundecs', g env' e)
  | Call (name, args) when M.mem name env ->
    let (args', body) = M.find name env in
    Format.eprintf "inlining %s@." name;
    let env' =
      List.fold_left2
        (fun env' (z, t) y -> M.add z y env')
        M.empty
        args'
        args in
      Alpha.alpha_convert M.empty env' body
  | e -> e

let f e = g M.empty e
