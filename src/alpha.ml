open KNormal

let find x env = 
  try M.find x env 
  with Not_found -> x

let alpha_convert_lval env = function 
  | SimpleVar name ->
    SimpleVar (find name env)
  | SubscriptVar (name, sub) ->
    SubscriptVar (find name env, find sub env)
  | FieldVar (name, fname) -> 
    FieldVar (find name env, fname)

let rec alpha_convert_dec env = function
  | VarDec (name, typ, exp) ->
    let name' = Id.genid name in
    VarDec (name', typ, alpha_convert env exp), M.add name name' env
  | TypeDecs _ as ty_decs -> ty_decs, env
  | FunctionDecs fundecs ->
    let entry env (name, _, _, _) = 
      M.add name (Id.genid name) env in
    let env' = List.fold_left entry env fundecs in
    let convert env (name, args, ret_ty, exp) =
      let args' = List.map (fun (x, y) -> find x env, y) args in
      find name env, args', ret_ty, alpha_convert env exp in
    let fundecs' = List.map (convert env') fundecs in
    FunctionDecs fundecs', env'

and alpha_convert env = function
  | Unit -> Unit
  | Int i -> Int i
  | String s -> String s
  | Add (x, y) -> Add (find x env, find y env)
  | Sub (x, y) -> Sub (find x env, find y env)
  | Mul (x, y) -> Mul (find x env, find y env)
  | Div (x, y) -> Div (find x env, find y env)
  | Call (name, args) -> 
    Call (find name env, List.map (fun a -> find a env) args)
  | Var lval -> Var (alpha_convert_lval env lval)
  | If ((op, x, y), then_exp, else_exp) ->
    If ((op, find x env, find y env),
	alpha_convert env then_exp,
	alpha_convert env else_exp)
  | CallExt (name, args) ->
    CallExt (name, List.map (fun a -> find a env) args)
  | Assign (lval, name) -> 
    Assign (alpha_convert_lval env lval, find name env)
  | Sequence exps -> 
    Sequence (List.map (alpha_convert env) exps)
  | While ((op, x, y), body_exp) ->
    While ((op, find x env, find y env),
	   alpha_convert env body_exp)
  | Break -> Break
  | Record (fields, rec_name) ->
    let convert (fname, name) = (fname, find name env) in
    Record (List.map convert fields, rec_name)
  | Let (dec, exp) -> 
    let (dec', env') = alpha_convert_dec env dec in
    Let (dec', alpha_convert env' exp)

let f = alpha_convert M.empty
