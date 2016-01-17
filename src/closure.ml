module K = KNormal

exception UnimplementedError of string

type closure = { entry: Id.l; actual_fv: Id.t list }
[@@deriving show]

type t = 
| Int of int
| String of string
| Add of Id.t * Id.t
| Sub of Id.t * Id.t
| Mul of Id.t * Id.t
| Div of Id.t * Id.t
| Unit
| Var of K.lvalue
| Assign of K.lvalue * Id.t
| If of (K.comp * Id.t * Id.t) * t * t
| While of (K.comp * Id.t * Id.t) * t
| Break
| Sequence of t list
| Record of (Id.t * Id.t) list * Id.t
| LetVar of (Id.t * Type.t * t) * t
| LetType of (Id.t * Type.t) list * t
| MakeCls of (Id.t * Type.t list * Type.t) * closure * t
| AppCls of Id.t * Id.t list
| AppDir of Id.l * Id.t list
[@@deriving show]


type fundef = { name : Id.l * Type.t;
                args : (Id.t * Type.t) list;
                formal_fv : (Id.t * Type.t) list;
                body : t }
[@@deriving show]

type prog = Prog of fundef list * t
[@@deriving show]

let fv_lvalue = function
  | K.SimpleVar x -> S.singleton x
  | K.FieldVar (x, _) -> S.singleton x
  | K.SubscriptVar (x, y) -> S.of_list [x; y]
    
let rec fv = function 
  | Int _ | String _ | Unit | Break -> S.empty
  | Add (x, y) | Sub (x, y) | Mul (x, y) | Div (x, y) ->
    S.of_list [x; y]
  | Var lval -> fv_lvalue lval
  | Assign (lval, name) -> S.add name @@ fv_lvalue lval
  | If ((_, x, y), e1, e2) ->
    S.add x @@ S.add y @@ S.union (fv e1) (fv e2)
  | While ((_, x, y), e) ->
    S.add x @@ S.add y @@ fv e
  | Sequence es ->
    List.fold_left S.union S.empty (List.map fv es)
  | Record (fields, _) ->
    S.of_list @@ List.map snd fields
  | LetVar ((x, _, e1), e2) -> 
    S.union (fv e1) (S.remove x @@ fv e2)
  | LetType (_, e) -> fv e
  | MakeCls ((x, _, _) , { entry = _; actual_fv = ys }, e) -> 
    S.remove x @@ S.union (S.of_list ys) (fv e)
  | AppCls (x, ys) -> S.of_list @@ x::ys
  | AppDir (_, ys) -> S.of_list ys

    
let toplevel : fundef list ref = ref []
    
let rec g venv known = function 
  | K.Unit -> Unit
  | K.Int i -> Int i
  | K.String s -> String s
  | K.Add (x, y) -> Add (x, y)
  | K.Sub (x, y) -> Sub (x, y)
  | K.Mul (x, y) -> Mul (x, y)
  | K.Div (x, y) -> Div (x, y)
  | K.Var lval -> Var lval
  | K.Assign (lval, x) -> Assign (lval, x)
  | K.If ((comp, x, y), e1, e2) -> 
    If ((comp, x, y), g venv known e1, g venv known e2)
  | K.While ((comp, x, y), e) ->
    While ((comp, x, y), g venv known e)
  | K.Break -> Break
  | K.Sequence es -> 
    Sequence (List.map (g venv known) es)
  | K.Record (fields, name) -> Record (fields, name)
  | K.Let (K.VarDec (name, ty, e1), e2) ->
    LetVar ((name, ty, g venv known e1), 
	    g (M.add name (Env.VarEntry ty) venv) known e2)
  | K.Let (K.TypeDecs tydecs, e) ->
    LetType (tydecs, g venv known e)
  | K.Call (name, args) -> 
    if S.mem name known 
    then begin
      Format.eprintf "directory applying %s@." name;
      AppDir(Id.L name, args)
    end else 
      AppCls(name, args)
  | K.CallExt (name, args) ->
    AppDir(Id.L name, args)
  | K.Let (K.FunctionDecs fundecs, e) ->
    let has_no_fv (x, yts, xty, body) =
      let names = List.map fst in
      let ys = names yts in
      let body' = g venv known body in
      S.is_empty @@ S.diff (fv body') (S.add x @@ S.of_list ys) in
    let add_known known ((x, yts, xty, body) as fundec) =
      if has_no_fv fundec 
      then S.add x known
      else known in
    let venv' = M.add_list (List.map (fun (x, yts, xty, _) ->
      x, Env.FunEntry (List.map snd yts, xty)) fundecs) venv in
    let known' = List.fold_left add_known known fundecs in
    let e' = g venv' known' e in
    let make_closure e' ((x, yts, ret_typ, body) as fundec) =
      let body' = g venv' known' body in
      let fvs = List.map fst yts
                |> S.of_list
    		|> S.add x
    		|> S.diff (fv body')
    		|> S.elements in
      List.iter (Format.eprintf "fvs: %s %s@." x) fvs;
      let ty = function
	| Env.VarEntry t -> t
	| Env.FunEntry _ -> raise (UnimplementedError "") in
      let find x venv = 
	try M.find x venv
	with Not_found -> 
	  (Format.eprintf "fv `%s` not found@." x;
	   assert false) in
      toplevel := ({ name = (Id.L x, ret_typ);
                     args = yts;
                     formal_fv = List.map (fun v -> v, ty @@ find v venv) fvs;
                     body = body' }) :: !toplevel;
      if has_no_fv fundec
      then e'
      else MakeCls ((x, List.map snd yts, ret_typ),
		    { entry = Id.L x; actual_fv = fvs }, e') in
    List.fold_left make_closure e' fundecs

let f e =
  toplevel := [];
  let known = S.of_list @@ List.map fst @@ M.bindings Env.base_venv in
  let e' = g Env.base_venv known e in
  Prog(List.rev !toplevel, e')
