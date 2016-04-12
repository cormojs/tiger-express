open KNormal

let find x venv = 
  try M.find x venv 
  with Not_found -> x

let alpha_convert_lval venv = function 
  | SimpleVar name ->
    SimpleVar (find name venv)
  | SubscriptVar (name, sub) ->
    SubscriptVar (find name venv, find sub venv)
  | FieldVar (name, fname) -> 
    FieldVar (find name venv, fname)

let rec alpha_convert_dec tenv venv = function
  | VarDec (name, typ, exp) ->
    let name' = Id.genid name in
    VarDec (name', typ, alpha_convert tenv venv exp), 
    tenv, M.add name name' venv
  | TypeDecs tydecs ->
    TypeDecs tydecs, tenv, venv
  | FunctionDecs fundecs ->
    let entry venv (name, _, _, _) = 
      M.add name (Id.genid name) venv in
    let venv' = List.fold_left entry venv fundecs in
    let convert venv (name, args, ret_ty, exp) =
      let args' = List.map (fun (x, y) -> find x venv, y) args in
      find name venv, args', ret_ty, alpha_convert tenv venv exp in
    let fundecs' = List.map (convert venv') fundecs in
    FunctionDecs fundecs', tenv, venv'

and alpha_convert tenv venv = function
  | Unit -> Unit
  | Int i -> Int i
  | String s -> String s
  | Add (x, y) -> Add (find x venv, find y venv)
  | Sub (x, y) -> Sub (find x venv, find y venv)
  | Mul (x, y) -> Mul (find x venv, find y venv)
  | Div (x, y) -> Div (find x venv, find y venv)
  | Call (name, args) ->
    Call (find name venv, List.map (fun a -> find a venv) args)
  | Var lval -> Var (alpha_convert_lval venv lval)
  | If ((op, x, y), then_exp, else_exp) ->
    If ((op, find x venv, find y venv),
	alpha_convert tenv venv then_exp,
	alpha_convert tenv venv else_exp)
  | CallExt (name, args) ->
    CallExt (name, List.map (fun a -> find a venv) args)
  | Assign (lval, name) ->
    Assign (alpha_convert_lval venv lval, find name venv)
  | Sequence exps ->
    Sequence (List.map (alpha_convert tenv venv) exps)
  | While ((op, x, y), body_exp) ->
    While ((op, find x venv, find y venv),
	   alpha_convert tenv venv body_exp)
  | Break -> Break
  | Record (fields, rec_name) ->
    let convert (fname, name) = (fname, find name venv) in
    Record (List.map convert fields, rec_name)
  | Let (dec, exp) ->
    let (dec', tenv', venv') = alpha_convert_dec tenv venv dec in
    Let (dec', alpha_convert tenv' venv' exp)

let f = alpha_convert M.empty M.empty
