exception KNormalizeError of string
exception ConvertError
  
type t = 
| Int of int
| String of string
| Add of Id.t * Id.t
| Sub of Id.t * Id.t
| Mul of Id.t * Id.t
| Div of Id.t * Id.t
| Unit
| Call of Id.t * Id.t list
| Var of lvalue
| Let of dec * t
| If of (comp * Id.t * Id.t) * t * t
| CallExt of Id.t * Id.t list
| Assign of lvalue * Id.t
| While of (comp * Id.t * Id.t) * t
| Break
| Sequence of t list
| Record of (Id.t * Id.t) list * Id.t
(* | Phi of Id.t * Id.t *)
[@@deriving show]
 
and lvalue = 
| SimpleVar of Id.t
| SubscriptVar of Id.t * Id.t
| FieldVar of Id.t * Id.t

and comp = | Eq | Le | Lt

and dec = 
| VarDec of Id.t * Type.t * t
| TypeDecs of (Id.t * Type.t) list
| FunctionDecs of fundec list

and fundec = Id.t * (Id.t * Type.t) list * Type.t * t

let peel_typ = function 
  | Type.Name (_, r) -> begin match !r with
    | Some ty -> ty
    | None -> raise (KNormalizeError "cannot peel type")
  end
  | ty -> ty
  
let insert_let(ex, ty) kont = 
  match ex with 
  | Var (SimpleVar v) -> kont v
  | _ -> 
    let v = Id.gentmp ty in
    let ex', ty' = kont v in
    Let(VarDec (v, ty, ex), ex'), ty'

let dummy = Lexing.dummy_pos

let is_comp_op = function
| Syntax.OpAdd | Syntax.OpSub | Syntax.OpMul | Syntax.OpDiv -> false
| Syntax.OpGe | Syntax.OpGt | Syntax.OpLe
| Syntax.OpLt | Syntax.OpEq | Syntax.OpNeq -> true
      
let convert_comp_op (x, y) = function 
  | Syntax.OpEq | Syntax.OpNeq -> (Eq, x, y)
  | Syntax.OpLe -> (Le, x, y)
  | Syntax.OpGe -> (Le, y, x)
  | Syntax.OpLt -> (Lt, x, y)
  | Syntax.OpGt -> (Lt, y, x)
  | _ -> raise ConvertError

let rec k_normalize_lvalue tenv venv = function
  | Syntax.SimpleVar name ->
    begin try match M.find name venv with
    | Env.VarEntry typ -> Var (SimpleVar name), typ
    | Env.FunEntry _ -> raise (KNormalizeError "This is a function")
    with Not_found -> raise (KNormalizeError ("Variable not found: " ^ name))
    end
  | Syntax.FieldVar (lval, fname) -> 
    let lval_name, lval_typ = k_normalize_lvalue tenv venv lval in
    insert_let (lval_name, lval_typ)
      (fun name -> match peel_typ lval_typ with
      | Type.Record (fields, _) ->
	begin 
	  try Var (FieldVar (name, fname)), Type.M.find fname fields 
	  with Not_found -> raise (KNormalizeError "Field name not found")
	end
      | _ -> raise (KNormalizeError "not a record type"))
  | Syntax.SubscriptVar (lval, exp) ->
    let lval_name, lval_typ = k_normalize_lvalue tenv venv lval in
    insert_let (lval_name, lval_typ)
      (fun name -> insert_let (k_normalize tenv venv exp)
	(fun sub -> match lval_typ with 
	| Type.Array(ty, _) -> Var (SubscriptVar (name, sub)), ty
	| _ -> raise (KNormalizeError "")))

and k_normalize_decs tenv venv dec kont = match dec with
  | Syntax.VarDec (name, _, exp, _) ->
    let init_exp', init_typ = k_normalize tenv venv exp in
    let venv' = M.add name (Env.VarEntry init_typ) venv in
    let body_exp, body_typ = kont (tenv, venv') in
    Let (VarDec (name, init_typ, init_exp'), body_exp), body_typ
  | Syntax.TypeDecs decs as ty_decs ->
    let (tenv', _) = Typing.insert_dec (tenv, venv) ty_decs in
    let convert_dec (name, ty, _) = 
      (name, Typing.convert_ty_name name tenv' ty) in
    let decs' = List.map convert_dec decs in
    let body_exp, body_typ = kont (tenv', venv) in
    Let (TypeDecs decs', body_exp), body_typ
  | Syntax.FunDecs fundecs as fun_decs ->
    let (_, venv') = Typing.insert_dec (tenv, venv) fun_decs in
    let body_exp, body_typ = kont (tenv, venv') in
    let convert_fundec (name, args, ret_op, body, _) = 
      let convert_arg (arg, ty_name) = begin 
	try arg, M.find ty_name tenv
	with Not_found -> raise (KNormalizeError "Type name not found")
      end in
      let args' = List.map convert_arg args in
      let entry venv (name, ty) = M.add name (Env.VarEntry ty) venv in
      let venv'' = List.fold_left entry venv' args' in
      let body_exp, body_ty = k_normalize tenv venv'' body in
      (name, args', body_ty, body_exp) in
    let fundecs' = List.map convert_fundec fundecs in
    Let (FunctionDecs fundecs', body_exp), body_typ
	

and k_normalize tenv venv = function
  (* Int, String, Unitはそのまま変換 *)
  | Syntax.Int (i, _) -> Int i, Type.Int
  | Syntax.String (s, _) -> String s, Type.String
  | Syntax.Unit _ -> Unit, Type.Unit
  (* Nilは0に変換 *)
  | Syntax.Nil _ -> Int 0, Type.Int
  (* 四則演算は全部Int *)
  | Syntax.Op (Syntax.OpAdd, lhs, rhs, _) ->
    insert_let (k_normalize tenv venv lhs)
      (fun x -> insert_let (k_normalize tenv venv rhs)
  	(fun y -> Add(x, y), Type.Int))
  | Syntax.Op (Syntax.OpSub, lhs, rhs, _) ->
    insert_let (k_normalize tenv venv lhs)
      (fun x -> insert_let (k_normalize tenv venv rhs)
  	(fun y -> Sub(x, y), Type.Int))
  | Syntax.Op (Syntax.OpMul, lhs, rhs, _) ->
    insert_let (k_normalize tenv venv lhs)
      (fun x -> insert_let (k_normalize tenv venv rhs)
  	(fun y -> Mul(x, y), Type.Int))
  | Syntax.Op (Syntax.OpDiv, lhs, rhs, _) ->
    insert_let (k_normalize tenv venv lhs)
      (fun x -> insert_let (k_normalize tenv venv rhs)
  	(fun y -> Div(x, y), Type.Int))
  (* 比較演算はSyntax.Ifに変換してからkNormalizeする *)
  | Syntax.Op (Syntax.OpGe, _, _, _)
  | Syntax.Op (Syntax.OpGt, _, _, _)
  | Syntax.Op (Syntax.OpLe, _, _, _)
  | Syntax.Op (Syntax.OpLt, _, _, _)
  | Syntax.Op (Syntax.OpEq, _, _, _)
  | Syntax.Op (Syntax.OpNeq, _, _, _) as cmp ->
    k_normalize tenv venv @@ Syntax.If (cmp,
  			Syntax.Int (1, dummy),
  			Syntax.Int (0, dummy),
  					dummy)
  (* Syntax.EqとSyntax.NeqはEqに合流する *)
  | Syntax.If (Syntax.Op (Syntax.OpEq, lhs, rhs, _), then_exp, else_exp, _) ->
    insert_let (k_normalize tenv venv lhs)
      (fun x -> insert_let (k_normalize tenv venv rhs)
  	(fun y ->
  	  let then_exp', then_typ = k_normalize tenv venv then_exp in
  	  let else_exp', else_typ = k_normalize tenv venv else_exp in
  	  If((Eq, x, y), then_exp', else_exp'), then_typ))
  | Syntax.If (Syntax.Op (Syntax.OpNeq, lhs, rhs, _), then_exp, else_exp, _) ->
    insert_let (k_normalize tenv venv lhs)
      (fun x -> insert_let (k_normalize tenv venv rhs)
  	(fun y ->
  	  let then_exp', then_typ = k_normalize tenv venv then_exp in
  	  let else_exp', else_typ = k_normalize tenv venv else_exp in
  	  If((Eq, x, y), else_exp', then_exp'), then_typ))
  (* 不等号演算子はLtかLeに変換する *)
  | Syntax.If (Syntax.Op (comp_op, lhs, rhs, _), then_exp, else_exp, _) ->
    insert_let (k_normalize tenv venv lhs)
      (fun x -> insert_let (k_normalize tenv venv rhs)
  	(fun y ->
  	  let then_exp', then_typ = k_normalize tenv venv then_exp in
  	  let else_exp', else_typ = k_normalize tenv venv else_exp in
  	  If(convert_comp_op (x, y) comp_op, then_exp', else_exp'), then_typ))
  (* 条件部が比較演算でない場合は比較演算に変換してからkNormalizeする *)
  | Syntax.If (test_exp, then_exp, else_exp, pos) ->
    k_normalize tenv venv (Syntax.If (Syntax.Op (Syntax.OpEq,
  				 test_exp,
  				 Syntax.Int (1, pos),
  				 pos),
  		      then_exp, else_exp, pos))
  (* 配列の初期化は外部関数init_arrayの呼び出しにする *)
  | Syntax.Array (name, size_exp, init_exp, _) ->
    insert_let (k_normalize tenv venv size_exp)
      (fun size ->
  	let init, ty = (k_normalize tenv venv init_exp) in
  	insert_let (init, ty)
  	(fun init ->
  	  CallExt ("init_array", [size; init]), Type.Array (ty, name)))
  (* lvalueは専用の関数で変換する *)
  | Syntax.Var (lval, _) ->
    k_normalize_lvalue tenv venv lval
  (* 単純な変数代入の変換 *)
  | Syntax.Assign (Syntax.SimpleVar (name), rval_exp, _) ->
    let rval_t, rval_typ = k_normalize tenv venv rval_exp in
    insert_let (rval_t, rval_typ)
      (fun rval_name ->
  	Assign (SimpleVar name, rval_name), rval_typ)
  (* 配列の要素への代入の変換 *)
  | Syntax.Assign (Syntax.SubscriptVar (lval, sub_exp), rval_exp, _) ->
    let rval_t, rval_typ = k_normalize tenv venv rval_exp in
    insert_let (k_normalize_lvalue tenv venv lval)
      (fun lval_name -> insert_let (rval_t, rval_typ)
  	(fun rval_name -> insert_let (k_normalize tenv venv sub_exp)
  	  (fun sub_name ->
  	    Assign (SubscriptVar (lval_name, sub_name), rval_name),
  	    rval_typ)))
  (* レコードフィールドへの代入の変換 *)
  | Syntax.Assign (Syntax.FieldVar (lval, fname) , rval_exp, _) ->
    let rval_t, rval_typ = k_normalize tenv venv rval_exp in
    insert_let (k_normalize_lvalue tenv venv lval)
      (fun lval_name -> insert_let (rval_t, rval_typ)
  	(fun rval_name ->
  	    Assign (FieldVar (lval_name, fname), rval_name),
  	    rval_typ))
  (* Whileの変換 - 条件部が比較演算のとき - *)
  | Syntax.While (Syntax.Op (op, lhs, rhs, _), body_exp, _)
      when is_comp_op op ->
    insert_let (k_normalize tenv venv lhs)
      (fun x -> insert_let (k_normalize tenv venv rhs)
  	(fun y ->
  	  let body, _ = k_normalize tenv venv body_exp in begin
  	    While (convert_comp_op (x, y) op, body), Type.Unit
  	  end))
  (* Whileの変換 - 条件部が比較演算でないとき - *)
  | Syntax.While (cond_exp, body_exp, pos) ->
    k_normalize tenv venv @@
      Syntax.While (Syntax.Op (Syntax.OpNeq, cond_exp,
  			       Syntax.Int (0, pos), pos),
  		    body_exp, pos)
  (* Syntax.ForはSyntax.Whileに置き換えてからkNomarlizeする *)
  | Syntax.For (i, lo_exp, hi_exp, body_exp, _) ->
    k_normalize tenv venv @@
      Syntax.Let ([ Syntax.VarDec (i, Some "int", lo_exp, dummy) ],
  		  Syntax.While (Syntax.Op
  				  (Syntax.OpLe,
  				   Syntax.Var (Syntax.SimpleVar i, dummy),
  				   hi_exp, dummy),
  				Syntax.Sequence
  				  ([ body_exp;
  				     Syntax.Assign
  				       (Syntax.SimpleVar i,
  					Syntax.Op (Syntax.OpAdd,
  						   Syntax.Var
  						     (Syntax.SimpleVar i,
  						      dummy),
  						   Syntax.Int (1, dummy),
  						   dummy),
  					dummy) ],
  				   dummy),
  				dummy),
  		  dummy)
  (* Breakの変換 *)
  | Syntax.Break _ -> Break, Type.Unit
  (* Sequenceの変換 *)
  | Syntax.Sequence (exps, _) ->
    let rec last = begin function
      | [] -> raise (KNormalizeError "empty sequence")
      | (e::[]) -> e
      | (e::es) -> last es
    end in
    let typ = begin match exps with
      | []  -> Type.Unit
      | lst -> snd (k_normalize tenv venv @@ last exps)
    end in
    Sequence (List.map (fun e -> fst @@ k_normalize tenv venv e) exps), typ
  | Syntax.Let (dec::decs, body_exp, p) ->
    k_normalize_decs tenv venv dec (fun (tenv', venv') ->
      k_normalize tenv' venv' (Syntax.Let (decs, body_exp, p)))
  | Syntax.Let ([], body_exp, _) ->
    k_normalize tenv venv body_exp
  | Syntax.Call (name, args, _) -> 
    begin try match M.find name venv with
    | Env.VarEntry _ -> raise (KNormalizeError "This is a variable")
    | Env.FunEntry (_, ret_ty) ->
      let convert_arg arg = 
	let exp, ty = k_normalize tenv venv arg in
	(Id.gentmp ty, (exp, ty)) in
      let args' = List.map convert_arg args in
      let call = Call (name, List.map fst args') in
      let entry_let body_exp (name, (exp, ty)) = 
	Let (VarDec (name, ty, exp), body_exp) in
      List.fold_left entry_let call args', ret_ty
      with Not_found -> raise (KNormalizeError ("Variable not found: " ^ name))
    end
  | Syntax.Record (fields, name, _) ->
    let convert_field (fname, synexp) =
      let exp, ty = k_normalize tenv venv synexp in
      ((fname, Id.gentmp ty), (exp, ty)) in
    let fields' = List.map convert_field fields in
    let typ = begin 
      try begin match M.find name tenv with
      | Type.Name (name, t_op_ref) -> (match !t_op_ref with
	| Some ty -> ty
	| None -> raise (KNormalizeError "Record error"))
      | ty -> ty
      end
      with Not_found -> raise (KNormalizeError "Type name not found")
    end in
    let record = Record (List.map fst fields', name) in
    let entry_let body_exp ((_, name), (exp, ty)) =
      Let (VarDec (name, ty, exp), body_exp) in
    List.fold_left entry_let record fields', typ

    

let f e = fst @@ k_normalize Env.base_tenv Env.base_venv e
