open Asm


exception NoReg of Id.t * Type.t

type alloc_result = 
| Alloc of Id.t
| Spill of Id.t

let find x regenv =
  if is_reg x then x else
  try M.find x regenv
  with Not_found -> raise (NoReg (x, Type.Int))

let find' x' regenv =
  match x' with
  | V(x) -> V(find x regenv)
  | c -> c

let add x r regenv = 
  if is_reg x 
  then begin 
    assert (x = r);
    regenv
  end else 
    M.add x r regenv


let rec target' src (dest, t) = function
  | Mov (V x) when x = src && is_reg dest ->
    assert (t <> Type.Unit);
    false, [dest]
  | IfEq (_, _, e1, e2) | IfLe (_, _, e1, e2) | IfLt (_, _, e1, e2) ->
    let c1, rs1 = target src (dest, t) e1 in
    let c2, rs2 = target src (dest, t) e2 in
    c1 && c2, rs1 @ rs2
  | CallCls (x, ys) -> 
    true, (target_args src regs 0 ys @
	     if x = src then [reg_cl] else [])
  | CallDir (_, ys) ->
    true, target_args src regs 0 ys
  | WhileEq (_, _, e) | WhileLe (_, _, e) | WhileLt (_, _, e) ->
    target src (dest, t) e
  | _ -> false, []
and target src dest = function 
  | Ans exp -> target' src dest exp
  | Let (xt, exp, e) ->
    let c1, rs1 = target' src xt exp in
    if c1
    then true, rs1 
    else let c2, rs2 = target src dest e in
	 c2, rs1 @ rs2
and target_args src all n = function 
  | [] -> []
  | y::ys when y = src ->
    all.(n) :: target_args src all (n + 1) ys
  | _::ys -> target_args src all (n + 1) ys

let rec source t = function
  | Ans exp -> source' t exp
  | Let (_, _, e) -> source t e
and source' t = function
  | Mov (V x) | Add (x, C _) | Sub (x, C _) | Mul (x, C _) | Div (x, C _) ->
    [x]
  | Add (x, V y) | Sub (x, V y) | Mul (x, V y) | Div (x, V y) -> 
    [x; y]
  | IfEq(_, _, e1, e2) | IfLt(_, _, e1, e2) | IfLe(_, _, e1, e2) ->
    source t e1 @ source t e2
  | CallCls _ | CallDir _ -> begin match t with
    | Type.Unit -> []
    | _ -> [regs.(0)]
  end
  | WhileEq (_, _, e) | WhileLe (_, _, e) | WhileLt (_, _, e) ->
    source t e
  | _ -> []

let rec alloc cont regenv x t prefer = 
  (* assert (not @@ M.mem x regenv); *)
  let all = match t with 
    | Type.Unit -> []
    | _ -> allregs in
  if all = [] then Alloc "%unit" 
  else if is_reg x then Alloc x
  else let free = fv cont in
       try 
	 let live = List.fold_left (fun live y ->
	   if is_reg y then S.add y live else
	     try S.add (M.find y regenv) live
	     with Not_found -> live)
	   S.empty
	   free in
	 let r = List.find 
	   (fun r -> not @@ S.mem r live) 
	   (prefer @ all) in
	 Format.eprintf "alloc %s@." r;
	 Alloc r
       with Not_found -> 
	 Format.eprintf "register allocation failed for %s@." x;
	 let y = List.find (fun y ->
	   not (is_reg y) && 
	     try List.mem (M.find y regenv) all
	     with Not_found -> false)
	   (List.rev free) in
	 Format.eprintf "spilling %s from %s@." y (M.find y regenv);
	 Spill y


let rec g dest cont regenv = function
  | Ans exp -> g'_and_restore dest cont regenv exp
  | Let ((x, t) as xt, exp, e) ->
    (* assert (not @@ M.mem x regenv); *)
    let cont' = concat e dest cont in
    let e1', regenv1 = g'_and_restore xt cont' regenv exp in
    let _call, targets = target x dest cont' in
    let sources = source t e1' in
    begin match alloc cont' regenv1 x t (targets @ sources) with
    | Alloc r ->
      let e2', regenv2 = g dest cont (add x r regenv1) e in 
      concat e1' (r, t) e2', regenv2
    | Spill y ->
      let r = M.find y regenv1 in 
      let e2', regenv2 = g dest cont (add x r (M.remove y regenv1)) e in
      let save = 
	try Save (M.find y regenv, y)
	with Not_found -> Nop in
      seq (save, concat e1' (r, t) e2'), regenv2
    end

and g'_and_restore dest cont regenv exp = 
  try g' dest cont regenv exp
  with NoReg (x, t) ->
    g dest cont regenv @@ Let((x, t), Restore x, Ans exp)

and g' dest cont regenv = function
  | Nop | MovL _ | Comment _ | Break | Restore _ as exp ->
    Ans exp, regenv
  | Mov x' -> Ans (Mov (find' x' regenv)), regenv
  | Add (x, y') -> Ans (Add (find x regenv, find' y' regenv)), regenv
  | Sub (x, y') -> Ans (Sub (find x regenv, find' y' regenv)), regenv
  | Mul (x, y') -> Ans (Mul (find x regenv, find' y' regenv)), regenv
  | Div (x, y') -> Ans (Div (find x regenv, find' y' regenv)), regenv
  | MovO (x, y', i) ->
    Ans (MovO (find x regenv, find' y' regenv, i)), regenv
  | MovR (x, y') ->
    Ans (MovR (find x regenv, find' y' regenv)), regenv
  | MovS (x, y, z', i) ->
    Ans (MovS (find x regenv, find y regenv, find' z' regenv, i)), regenv
  | IfEq (x, y', e1, e2) as exp -> 
    g'_if dest cont regenv exp (fun e1' e2' ->
      IfEq (find x regenv, find' y' regenv, e1', e2')) e1 e2
  | IfLt (x, y', e1, e2) as exp -> 
    g'_if dest cont regenv exp (fun e1' e2' ->
      IfLt (find x regenv, find' y' regenv, e1', e2')) e1 e2
  | IfLe (x, y', e1, e2) as exp -> 
    g'_if dest cont regenv exp (fun e1' e2' ->
      IfLt (find x regenv, find' y' regenv, e1', e2')) e1 e2
  | CallCls (x, ys) as exp -> 
    g'_call dest cont regenv exp (fun ys -> 
      CallCls (find x regenv, ys)) ys
  | CallDir (l, ys) as exp ->
    g'_call dest cont regenv exp (fun ys ->
      CallDir (l, ys)) ys
  | WhileEq (x, y', e) as exp ->
    g'_while dest cont regenv exp (fun e' ->
      WhileEq (find x regenv, find' y' regenv, e')) e
  | WhileLe (x, y', e) as exp ->
    g'_while dest cont regenv exp (fun e' ->
      WhileLe (find x regenv, find' y' regenv, e')) e
  | WhileLt (x, y', e) as exp ->
    g'_while dest cont regenv exp (fun e' ->
      WhileLt (find x regenv, find' y' regenv, e')) e
  | Save (x, y) -> assert false
    
and g'_if dest cont regenv exp constr e1 e2 =
  let e1', regenv1 = g dest cont regenv e1 in
  let e2', regenv2 = g dest cont regenv e2 in
  let regenv' = List.fold_left (fun regenv' x ->
    try if is_reg x 
      then regenv'
      else let r1 = M.find x regenv1 in 
	   let r2 = M.find x regenv2 in
	   if r1 <> r2 
	   then regenv'
	   else M.add x r1 regenv'
    with Not_found -> regenv')
    M.empty
    (fv cont) in
  List.fold_left (fun e x ->
    if x = fst dest || not (M.mem x regenv) || M.mem x regenv' 
    then e 
    else seq (Save (M.find x regenv, x), e))
    (Ans (constr e1' e2'))
    (fv cont), 
  regenv'

and g'_while dest cont regenv exp constr e =
  let e', regenv' = g dest (Ans (constr cont)) regenv e in
  List.fold_left (fun e x ->
    if x = fst dest || not (M.mem x regenv)
    then e
    else seq (Save (M.find x regenv, x), e))
    (Ans (constr e'))
    (fv cont),
  regenv'

and g'_call dest cont regenv exp constr ys = 
  List.fold_left (fun e x ->
    if x = fst dest || not (M.mem x regenv) 
    then e
    else (seq (Save (M.find x regenv, x), e)))
    (Ans (constr @@ List.map (fun y -> find y regenv) ys))
    (fv cont),
  M.empty

  
let h { name = Id.L x; args = ys; body = e; ret = t } = 
  let regenv = M.add x reg_cl M.empty in
  let (i, arg_regs, regenv) = 
    List.fold_left (fun (i, arg_regs, regenv) y ->
      let r = regs.(i) in
      (i + 1,
       arg_regs @ [r], 
       (assert (not (is_reg y));
	M.add y r regenv)))
      (0, [], regenv)
      ys in
  let a = begin match t with 
    | Type.Unit -> Id.gentmp Type.Unit
    | _ -> regs.(0)
  end in
  let e', regenv' = g (a, t) (Ans (Mov (V a))) regenv e in
  { name = Id.L x; args = arg_regs; body = e'; ret = t }
	  
  
let f (Prog (data, fundecs, exp)) = 
  let fundecs' = List.map h fundecs in
  let exp',_ = g (Id.gentmp Type.Unit, Type.Unit) (Ans Nop) M.empty exp in
  Prog (data, fundecs', exp')
