open Asm

exception VirtualException of string

let data = ref []


let classify xts ini adds addi = 
  List.fold_left (fun acc (x, t) -> match t with
  | Env.VarEntry Type.Unit -> acc
  | Env.VarEntry Type.String -> adds acc x
  | _ -> addi acc x t) ini xts

let separate xts = classify xts ([], []) 
  (fun (int, string) x -> (int, string @ [x]))
  (fun (int, string) x _ -> (int @ [x], string))

let expand xts ini adds addi = classify xts ini
  (fun (offset, acc) x -> 
    let offset' = align offset in
    offset' + 8, adds x offset' acc)
  (fun (offset, acc) x t -> 
    offset + 4, addi x t offset acc)

let get_field_offset venv x fname =
  begin match Env.peel (M.find x venv) with
  | Env.VarEntry (Type.Record (fields, _)) ->
    let fnames = List.map fst @@ Type.M.bindings fields in
    begin match BatList.index_of fname fnames with
      | Some i -> (
	4 * i)
      | None -> raise (VirtualException (fname ^ " not found"))
    end
  | _ -> raise (VirtualException ("not a variable: " ^ x))
  end

let convert_str s =
  let convert = function 
    | '\n' as c -> "\\" ^ (string_of_int @@ int_of_char c)
    | c -> String.make 1 c in
  (BatString.replace_chars 
     convert
     (Scanf.unescaped @@ Scanf.unescaped s))
  ^ "\\0"
  
let rec g tenv venv = function
  | Closure.Unit -> Ans Nop
  | Closure.Int i -> Ans (Mov (C i))
  | Closure.String s ->
    let l = 
      try fst @@ List.find (fun (_, s') -> s = s') !data 
      with Not_found ->
	let l = Id.L (Id.genid "l") in
	data := (l, convert_str s) :: !data;
	l in
    Ans (MovL l)
  | Closure.Add (x, y) -> Ans (Add (x, V y))
  | Closure.Sub (x, y) -> Ans (Sub (x, V y))
  | Closure.Mul (x, y) -> Ans (Mul (x, V y))
  | Closure.Div (x, y) -> Ans (Div (x, V y))
  | Closure.If ((KNormal.Eq, x, y), e1, e2) ->
    Ans (IfEq (x, V y, g tenv venv e1, g tenv venv e2))
  | Closure.If ((KNormal.Le, x, y), e1, e2) ->
    Ans (IfLe (x, V y, g tenv venv e1, g tenv venv e2))
  | Closure.If ((KNormal.Lt, x, y), e1, e2) ->
    Ans (IfLt (x, V y, g tenv venv e1, g tenv venv e2))
  | Closure.While ((KNormal.Eq, x, y), e) ->
    Ans (WhileEq (x, V y, g tenv venv e))
  | Closure.While ((KNormal.Le, x, y), e) ->
    Ans (WhileLe (x, V y, g tenv venv e))
  | Closure.While ((KNormal.Lt, x, y), e) ->
    Ans (WhileLt (x, V y, g tenv venv e))
  | Closure.Break -> Ans Break
  | Closure.LetVar ((x, ty, e1), e2) ->
    let e1' = g tenv venv e1 in
    let e2' = g tenv (M.add x (Env.VarEntry ty) venv) e2 in
    concat e1' (x, ty) e2'
  | Closure.LetType (ty_decs, e) ->
    let entry tenv (name, ty) = M.add name ty tenv in
    let tenv' = List.fold_left entry tenv ty_decs in
    g tenv' venv e
  | Closure.MakeCls ((x, args_ty, ret_ty),
		     { Closure.entry = l; Closure.actual_fv = ys },
		     e) ->
    let e' = g tenv (M.add x (Env.FunEntry (args_ty, ret_ty)) venv) e in
    let offset, store_fv = List.fold_left (fun (offset, e) y ->
      offset + 4, seq (MovS (y, x, C offset, 1), e)) 
      (4, e')
      ys in
    Let ((x, ret_ty), Mov (V reg_hp),
	 Let ((reg_hp, Type.Int), Add (reg_hp, C (align offset)),
	      let z = Id.genid "l" in
	      Let ((z, Type.Int), MovL l,
		   seq (MovS (z, x, C 0, 1),
			store_fv))))
  | Closure.AppCls (x, ys) ->
    Ans (CallCls (x, ys))
  | Closure.AppDir (Id.L x, ys) ->
    Ans (CallDir (Id.L x, ys))
  | Closure.Record (fields, name) ->
    let y = Id.genid "r" in
    let xs = begin match M.find name tenv with
      | Type.Record (fm, _) -> 
	let rec arrange = function
	  | [], _ -> []
	  | key :: keys, assocs ->
	  let found = List.assoc key assocs in
	  let rest = List.remove_assoc key assocs in
	  found :: arrange (keys, rest) in
	let fnames = List.map fst @@ Type.M.bindings fm in
	arrange (fnames, fields)
      | _ -> raise (VirtualException ("not a record type: " ^ name))
    end in
    let offset, store = List.fold_left (fun (offset, e) x -> 
      offset + 4, seq (MovS (x, y, C offset, 1), e))
      (0, Ans (Mov (V y)))
      xs in
    Let ((y, M.find name tenv), Mov (V reg_hp),
	 Let ((reg_hp, Type.Int), Add (reg_hp, C (align offset)),
	      store))
  | Closure.Var (KNormal.SimpleVar x) -> 
    begin match M.find x venv with
    | Env.VarEntry Type.Unit -> Ans Nop
    | _ -> Ans (Mov (V x))
    end
  | Closure.Var (KNormal.SubscriptVar (x, y)) ->
    begin match Env.peel (M.find x venv) with
    | Env.VarEntry (Type.Array (Type.Unit, _)) -> Ans Nop
    | Env.VarEntry (Type.Array (_, _)) -> Ans (MovO (x, V y, 4))
    | _ -> raise (VirtualException ("not an array: " ^ x))
    end
  | Closure.Var (KNormal.FieldVar (x, fname)) ->
    begin match Env.peel (M.find x venv) with
    | Env.VarEntry (Type.Record (fields, _)) ->
      let offset = get_field_offset venv x fname in
      Ans (MovO (x, C offset, 4))
    | entry -> raise (VirtualException 
			("not a record type: " ^ (Env.show entry)))
    end
  | Closure.Assign (KNormal.SimpleVar x, y) ->
    begin match Env.peel (M.find x venv) with
    | Env.VarEntry t ->
      Ans (MovR (x, V y))
    | entry -> raise (VirtualException ("not a variable: " ^ (Env.show entry)))
    end
  | Closure.Assign (KNormal.SubscriptVar (x, y), z) ->
    Ans (MovS (z, x, V y, 4))
  | Closure.Assign (KNormal.FieldVar (x, fname), y) ->
    let offset = get_field_offset venv x fname in
    Ans (MovS (y, x, C offset, 4))
  | Closure.Sequence [] -> Ans Nop
  | Closure.Sequence (e::es) -> 
    let xt = Id.gentmp Type.Unit, Type.Unit in
    let e1' = g tenv venv e in
    begin match g tenv venv (Closure.Sequence es) with
    | Ans Nop -> e1'
    | e2' -> concat e1' xt e2'
    end


let h { Closure.name = Id.L x, ty; 
	Closure.args = yts;
	Closure.formal_fv = zts;
	Closure.body = body } =
  let venv = M.add x (Env.VarEntry ty)
    @@ M.add_list (List.map (fun (y, ty) -> y, Env.VarEntry ty) yts)
    @@ M.add_list (List.map (fun (y, ty) -> y, Env.VarEntry ty) zts)
      M.empty in
  let offset, load = List.fold_left (fun (offset, e) z ->
    offset + 4, Let ((z, ty), MovO (reg_cl, C offset, 1), e))
    (4, g M.empty venv body)
    (List.map fst zts) in
  { name = Id.L x; args = List.map fst yts; body = load; ret = ty }

let f (Closure.Prog (fundecs, exp)) = 
  data := [];
  let fundecs' = List.map h fundecs in
  let exp' = g M.empty M.empty exp in
  Prog(!data, fundecs', exp')
