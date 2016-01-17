open KNormal

let find x env = 
  try M.find x env 
  with Not_found -> x

let beta_reduction_lval env = function 
  | SimpleVar name ->
    SimpleVar (find name env)
  | SubscriptVar (name, sub) ->
    SubscriptVar (find name env, find sub env)
  | FieldVar (name, fname) -> 
    FieldVar (find name env, fname)

let rec beta_reduction env = function
  | Unit -> Unit
  | Int i -> Int i
  | String s -> String s
  | Add (x, y) -> Add (find x env, find y env)
  | Sub (x, y) -> Sub (find x env, find y env)
  | Mul (x, y) -> Mul (find x env, find y env)
  | Div (x, y) -> Div (find x env, find y env)
  | Call (name, args) -> 
    Call (find name env, List.map (fun a -> find a env) args)
  | Var lval -> Var (beta_reduction_lval env lval)
  | If ((op, x, y), then_exp, else_exp) ->
    If ((op, find x env, find y env),
	beta_reduction env then_exp,
	beta_reduction env else_exp)
  | CallExt (name, args) ->
    CallExt (name, List.map (fun a -> find a env) args)
  | Assign (lval, name) -> 
    Assign (beta_reduction_lval env lval, find name env)
  | Sequence exps -> 
    Sequence (List.map (beta_reduction env) exps)
  | While ((op, x, y), body_exp) ->
    While ((op, find x env, find y env),
	   beta_reduction env body_exp)
  | Break -> Break
  | Record (fields, rec_name) ->
    let convert (fname, name) = (fname, find name env) in
    Record (List.map convert fields, rec_name)
  | Let (VarDec (name, typ, exp1), exp2) -> begin
    match beta_reduction env exp1 with
    | Var (SimpleVar name') ->
      Format.eprintf "beta-reducing %s = %s@." name name';
      beta_reduction (M.add name name' env) exp2
    | exp1' ->
      let exp2' = beta_reduction env exp2 in
      Let (VarDec (name, typ, exp1'), exp2')
  end
  | Let (TypeDecs decs, exp) -> 
    Let (TypeDecs decs, beta_reduction env exp)
  | Let (FunctionDecs fundecs, exp) ->
    let b env (name, args, typ, body_exp) = 
      (name, args, typ, beta_reduction env body_exp) in
    Let (FunctionDecs (List.map (b env) fundecs), 
	 beta_reduction env exp)

let f = beta_reduction M.empty
