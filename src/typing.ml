open Syntax

exception UnifyError of p * Type.t * Type.t
exception UnifyExpError of t * p * Type.t * Type.t
exception Error of p * string

let rec name_ty pos = function
  | Type.Name (name, ty_op_ref) ->
    begin match !ty_op_ref with 
    | Some ty -> name_ty pos ty
    | None -> raise (Error (pos, "incomplete type: " ^ name))
    end
  | ty -> ty
    
let rec unify pos = function 
  | (Type.Name _ as t1), t2 -> unify pos (name_ty pos t1, t2)
  | t1, (Type.Name _ as t2) -> unify pos (t1, name_ty pos t2)
  | (Type.Record (m1, name1) as t1), (Type.Record (m2, name2) as t2) ->
    if name1 <> name2 then begin
      raise (UnifyError (pos, t1, t2));
    end;
    unify_fields pos (Type.M.bindings m1, Type.M.bindings m2)
  | Type.Nil, Type.Record _ -> ()
  | Type.Record _, Type.Nil -> ()
  | t1, t2 when t1 <> t2 -> raise (UnifyError (pos, t1, t2))
  | _, _ -> ()

and is_unified pos (t1, t2) =
  try unify pos (t1, t2);
      true
  with _ -> false

and unify' pos = function
  | (Type.Name _ as t1), t2 -> unify' pos (name_ty pos t1, t2)
  | t1, (Type.Name _ as t2) -> unify' pos (t1, name_ty pos t2)
  | (Type.Record (m1, name1) as t1), (Type.Record (m2, name2) as t2) ->
    if name1 <> name2 then
      raise (UnifyError (pos, t1, t2));
  | Type.Nil, Type.Record _ -> ()
  | Type.Record _, Type.Nil -> ()
  | t1, t2 when t1 <> t2 -> raise (UnifyError (pos, t1, t2))
  | _, _ -> ()
    
and unify_fields pos (f1, f2) =
  List.iter2
    (fun (n1, t1) (n2, t2) ->
      if n1 <> n2 then 
	raise (Error (pos,
		      "field name doesn't match "
		      ^ n1 ^ " with " ^ n2));
      unify' pos (t1, t2))
    f1 f2

    
(* let rec unify_ref pos (t1, t2) = match (t1, t2) with *)
(*   | Type.Record(fields, tyRef), Type.Record(fields', tyRef') -> *)
(*     if unify_fields pos (Type.M.bindings fields, Type.M.bindings fields') *)
(*       && tyRef == tyRef' *)
(*     then () *)
(*     else (raise (UnifyError (pos, t1, t2))) *)
(*   | Type.Array(ty, tyRef), Type.Array(ty', tyRef') -> *)
(*     if name_ty pos ty = name_ty pos ty' && tyRef == tyRef' *)
(*     then () *)
(*     else (raise (UnifyError (pos, t1, t2))) *)
(*   | _, _ -> unify pos (t1, t2) *)
    
let rec infer tenv venv = function 
  | Int _ -> Type.Int
  | String _ -> Type.String
  | Record (fields, name, pos) -> begin
    if not @@ M.mem name tenv
    then raise (Error (pos, "undefined record name: " ^ name))
    else
      let ty = M.find name tenv in
      let of_list : (Id.t * Type.t) list -> Type.t Type.M.t =
	List.fold_left
	(fun m (k, v) -> Type.M.add k v m)
	Type.M.empty in 
      let ty_fields = List.map 
	(fun (name, e) -> (name,  infer tenv venv e)) fields in
      unify pos (ty, Type.Record (of_list ty_fields, name));
      ty
  end 
  | Nil _ -> Type.Nil
  | Unit _ -> Type.Unit
  | Sequence ([], _) -> Type.Unit
  | Sequence ([exp], _) -> infer tenv venv exp
  | Sequence ((exp::exps), pos) -> 
    infer tenv venv exp |> ignore;
    infer tenv venv @@ Sequence (exps, pos)
  | Call (fun_name, args, pos) ->
    if not @@ M.mem fun_name venv
    then (raise (Error (pos, "udefined function name: " ^ fun_name)))
    else begin
      match M.find fun_name venv with
      | Env.VarEntry _ -> raise (Error (pos, "not a function: " ^ fun_name))
      | Env.FunEntry (argsTy, retTy) ->
	let argsTy' = List.map (infer tenv venv) args in 
	if List.length argsTy <> List.length argsTy' then
	  raise (Error (pos, "number of args doesn't match"))
	else begin
	  List.iter2
	    (fun ty ty' -> 
	      if not (is_unified pos (ty, ty')) then
		raise (UnifyError (pos, ty, ty')))
	    argsTy argsTy';
	  retTy
	end
    end
  | Op (op, lhs, rhs, pos) -> 
    begin match op with
    | OpAdd | OpSub | OpMul | OpDiv | OpGe | OpGt | OpLe | OpLt ->
      must_be pos (tenv, venv) lhs Type.Int;
      must_be pos (tenv, venv) rhs Type.Int;
      Type.Int
    | OpEq | OpNeq -> begin
      must_be pos (tenv, venv) rhs (infer tenv venv lhs);
      Type.Int
    end
    end
  | If (test_exp, then_exp, else_exp, pos) ->
    must_be pos (tenv, venv) test_exp Type.Int;
    must_be pos (tenv, venv) else_exp (infer tenv venv then_exp);
    infer tenv venv then_exp
  | Array (name, size_exp, init_exp, pos) ->
    if M.mem name tenv 
    then begin match name_ty pos @@ M.find name tenv with
    | Type.Array(ty, arr_ref) ->
      must_be pos (tenv, venv) size_exp Type.Int;
      must_be pos (tenv, venv) init_exp ty;
      Type.Array(ty, arr_ref)
    | _ -> 
      raise (Error (pos, "not an array type: " ^ name))
    end
    else raise (Error (pos, "undefined array type: " ^ name))
  | Assign (lval, exp, pos) ->
    let lval_typ = infer_lval pos tenv venv lval in
    unify pos (lval_typ, infer tenv venv exp);
    Type.Unit
  | While (test_exp, body_exp, pos) -> 
    must_be pos (tenv, venv) test_exp Type.Int;
    must_be pos (tenv, venv) body_exp Type.Unit;
    Type.Unit
  | For (var_name, lo_exp, hi_exp, body_exp, pos) ->
    unify pos (Type.Int, infer tenv venv lo_exp);
    unify pos (Type.Int, infer tenv venv hi_exp);
    let venv' = M.add var_name (Env.VarEntry Type.Int) venv in
    unify pos (Type.Unit, infer tenv venv' body_exp);
    Type.Unit
  | Break _ -> Type.Unit
  | Var (lval, pos) -> infer_lval pos tenv venv lval
  | Let (decs, body_exp, pos) -> begin
    let (tenv', venv') = List.fold_left insert_dec (tenv, venv) decs in
    infer tenv' venv' body_exp
  end
and must_be pos (tenv, venv) exp typ = 
  try unify pos ((infer tenv venv exp), typ)
  with UnifyError (pos, t1, t2) ->
    raise (UnifyExpError(exp, pos, t1, t2))
and insert_dec (tenv, venv) = function
  | VarDec (name, Some ty_name, exp, pos) ->
    let ty =
      try M.find ty_name tenv 
      with Not_found ->
	(raise (Error (pos, "undefined decl type: " ^ ty_name))) in
    unify pos (ty, infer tenv venv exp);
    tenv, M.add name (Env.VarEntry ty) venv
  | VarDec (name, None, exp, pos) -> 
    let ty = infer tenv venv exp in
    tenv, M.add name (Env.VarEntry ty) venv
  | TypeDecs decs ->
    let add_name tenv (name, _, _) =
      M.add name (Type.Name(name, ref None)) tenv in
    let tenv' = List.fold_left add_name tenv decs in
    let tys =
      List.map (fun (name, ty, pos) -> 
	(name, convert_ty_name name tenv' ty, pos)) decs in
    let update_type (name, ty, pos) = begin
      try begin match M.find name tenv' with
      | Type.Name (_, ty_ref) -> ty_ref := Some (name_ty pos ty)
      | _ -> raise (Error (pos, "not a name type: " ^ name))
      end
      with Not_found -> raise (Error (pos, "undefined type: " ^ name))
    end in
    List.iter update_type tys;
    tenv', venv
  | FunDecs fundecs ->
    let result_ty pos = function 
      | Some ty_name -> begin
	try M.find ty_name tenv
	with Not_found -> 
	  raise (Error (pos, "undefined return type: " ^ ty_name))
      end
      | None -> Type.Unit in
    let entry_fun_dec venv (name, args, result_opt, _, pos) = 
      let tys = List.map (fun (_, ty_name) -> begin 
	try M.find ty_name tenv 
	with Not_found -> 
	  raise (Error (pos, "undefined arg type: " ^ ty_name))
      end) args in begin
	M.add name (Env.FunEntry (tys, result_ty pos result_opt)) venv 
      end in
    let venv' = List.fold_left entry_fun_dec venv fundecs in
    let unify_fun (name, args, result_opt, body_exp, pos) = 
      let name_tys = List.map (fun (name, ty_name) -> 
	(name, Env.VarEntry (M.find ty_name tenv)))
	args in
      let venv'' = List.fold_left 
	(fun m (k, v) -> M.add k v m) venv' name_tys in
      unify pos (result_ty pos result_opt, infer tenv venv'' body_exp)
      in
    List.iter unify_fun fundecs;
    (tenv, venv')
    
and convert_ty_name ty_name tenv = function
  | NameTy (name, pos) -> begin
    try M.find name tenv
    with Not_found -> raise (Error (pos, "undefined type: " ^ name))
  end
  | RecordTy (fields, pos) ->  
    let field_type (name, ty_name) = begin
      try (name, M.find ty_name tenv)
      with Not_found -> raise (Error (pos, "undefined field type: " ^ ty_name))
    end in
    let rec check_dups = function 
      | [] -> ()
      | (name::names) ->
	if List.exists ((=) name) names
	then raise (Error (pos, "duplicate field name: " ^ name))
	else check_dups names in
    let field_types = List.map field_type fields in
    check_dups @@ List.map (fun (name,_) -> name) fields;
    Type.Record (List.fold_left 
		   (fun m (k, v) -> Type.M.add k v m)
		   Type.M.empty
		   field_types, 
		 ty_name)
  | ArrayTy (name, pos) -> begin 
    try Type.Array (M.find name tenv, ty_name)
    with Not_found -> raise (Error (pos, "undefined type: " ^ name))
  end
and infer_lval (pos: p) tenv venv = function
  | SimpleVar name -> 
    if M.mem name venv 
    then begin match M.find name venv with
    | Env.VarEntry ty -> ty
    | _ -> raise (Error (pos, "not a variable: " ^ name))
    end
    else raise (Error (pos, "undefined variable: " ^ name))
  | FieldVar (lval, field_name) ->
    let lval_ty = infer_lval pos tenv venv lval in
    begin match name_ty pos lval_ty with
    | Type.Record (fields, rec_ref) ->
      begin
	try Type.M.find field_name fields
	with Not_found -> raise (Error (pos, "invalid field name: " ^ field_name))
      end
    | _ ->
      raise (Error (pos, "not a record type"))
    end
  | SubscriptVar (lval, exp) ->
    let lval_ty = infer_lval pos tenv venv lval in
    begin match name_ty pos lval_ty with
    | Type.Array (ty, arr_ref) ->
      unify pos (Type.Int, infer tenv venv exp);
      ty
    | _ -> 
      raise (Error (pos, "not an array type")) 
    end

let f exp =
  infer Env.base_tenv Env.base_venv exp |> ignore;
  exp
