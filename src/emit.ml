open Asm
open Printf

type dest = Tail | NonTail of Id.t

let stackset = ref S.empty
let stackmap = ref []
let current_label = ref ""

let pp_id_or_imm = function
  | V x -> x
  | C i -> "$" ^ string_of_int i

let locate x = 
  let rec loc = function
    | [] -> []
    | y :: zs when x = y -> 0 :: List.map succ (loc zs)
    | y :: zs -> List.map succ (loc zs) in
  loc !stackmap
    
let offset x = 4 * List.hd (locate x)

let save x =
  Format.eprintf "save %s@." x;
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    stackmap := !stackmap @ [x]

let stacksize () = align (List.length !stackmap * 4)

let rec shuffle sw xys = 
  let _, xys = List.partition (fun (x, y) -> x = y) xys in
  match List.partition (fun (_, y) -> List.mem_assoc y xys) xys with
  | [], [] -> []
  | (x, y)::xys, [] ->
    (y, sw)::(x, y)::shuffle sw (List.map
				   (fun (y', z) ->
				     if y = y'
				     then (sw, z) else (y', z))
				   xys)
  | xys, acyc -> acyc @ shuffle sw xys

let rec g oc = function
  | dest, Ans exp -> g' oc (dest, exp)
  | dest, Let ((x, t), exp, e) ->
    g' oc (NonTail x, exp);
    g oc (dest, e)

and g' oc = function
  | NonTail _, Nop -> ()
  | NonTail x, Mov (V y) -> fprintf oc "\tmovl\t%s, %s\n" y x
  | NonTail x, Mov (C i) -> fprintf oc "\tmovl\t$%d, %s\n" i x
  | NonTail x, MovL (Id.L l) -> fprintf oc "\tmovl\t$%s, %s\n" l x
  | NonTail x, Add (y, z') ->
    if V x = z' 
    then fprintf oc "\taddl\t%s, %s\n" y x
    else begin 
      if x <> y then fprintf oc "\tmovl\t%s, %s\n" y x;
      fprintf oc "\taddl\t%s, %s\n" (pp_id_or_imm z') x
    end
  | NonTail x, Sub (y, z') ->
    if V x = z' 
    then begin 
      fprintf oc "\tsubl\t%s, %s\n" y x;
      fprintf oc "\tnegl\t%s\n" x
    end
    else begin 
      if x <> y then fprintf oc "\tmovl\t%s, %s\n" y x;
      fprintf oc "\tsubl\t%s, %s\n" (pp_id_or_imm z') x
    end
  | NonTail x, Mul (y, z') ->
    if V x = z' 
    then fprintf oc "\timul\t%s, %s\n" y x
    else begin 
      if x <> y then fprintf oc "\tmovl\t%s, %s\n" y x;
      fprintf oc "\timul\t%s, %s\n" (pp_id_or_imm z') x
    end
  | NonTail x, Div (y, z') ->
    if V x = z' 
    then fprintf oc "\tidiv\t%s, %s\n" y x
    else begin 
      if x <> y then fprintf oc "\tmovl\t%s, %s\n" y x;
      fprintf oc "\tidiv\t%s, %s\n" (pp_id_or_imm z') x
    end
  | NonTail x, MovO (y, V z, i) -> 
    fprintf oc "\tmovl\t(%s,%s,%d), %s\n" y z i x
  | NonTail x, MovO (y, C j, i) -> 
    fprintf oc "\tmovl\t%d(%s), %s\n" (j*i) y x
  | NonTail _, MovS (x, y, V z, i) ->
    fprintf oc "\tmovl\t%s, (%s, %s, %d)\n" x y z i
  | NonTail _, MovS (x, y, C j, i) ->
    fprintf oc "\tmovl\t%s, %d(%s)\n" x (j*i) y
  | NonTail v, MovR (x, V y) ->
    fprintf oc "\tmovl\t%s, %s\n" y x;
    if S.mem v !stackset then
      fprintf oc "\tmovl\t%s, %d(%s)\n" x (offset v) reg_sp
  | NonTail v, MovR (x, C i) ->
    fprintf oc "\tmovl\t$%d, %s" i x;
    if S.mem v !stackset then
      fprintf oc "\tmovl\t%s, %d(%s)\n" x (offset v) reg_sp
  | Tail, MovR (x, V y) ->
    fprintf oc "\tmovl\t%s, %s\n" y x;
  | Tail, MovR (x, C i) ->
    fprintf oc "\tmovl\t$%d, %s" i x;
  | NonTail _, Comment s -> fprintf oc "\t# %s\n" s
  | NonTail _, Save (x, y) when List.mem x allregs && not (S.mem y !stackset) ->
    save y;
    fprintf oc "\tmovl\t%s, %d(%s)\n" x (offset y) reg_sp
  | NonTail _, Save (x, y) -> assert (S.mem y !stackset)
  | NonTail x, Restore y ->
    fprintf oc "\tmovl\t%d(%s), %s\n" (offset y) reg_sp x
  | Tail, (Nop | MovS _ | Comment _ | Save _ as exp) ->
    g' oc (NonTail (Id.gentmp Type.Unit), exp);
    fprintf oc "\tret\n";
  | Tail, (Mov _ | MovL _ | MovO _ | Add _ | Sub _ | Mul _ | Div _ as exp) ->
    g' oc (NonTail regs.(0), exp);
    fprintf oc "\tret\n"
  | Tail, (Restore x as exp) ->
    begin match locate x with
    | [i] -> g' oc (NonTail regs.(0), exp)
    | _ -> assert false 
    end;
    fprintf oc "\tret\n"
  | Tail, IfEq (x, y', e1, e2) ->
    fprintf oc "\tcmpl\t%s, %s\n" (pp_id_or_imm y') x;
    g'_tail_if oc e1 e2 "je" "jne"
  | Tail, IfLe (x, y', e1, e2) ->
    fprintf oc "\tcmpl\t%s, %s\n" (pp_id_or_imm y') x;
    g'_tail_if oc e1 e2 "jle" "jg"
  | Tail, IfLt (x, y', e1, e2) ->
    fprintf oc "\tcmpl\t%s, %s\n" (pp_id_or_imm y') x;
    g'_tail_if oc e1 e2 "jl" "jge"
  | NonTail z, IfEq (x, y', e1, e2) ->
    fprintf oc "\tcmpl\t%s, %s\n" (pp_id_or_imm y') x;
    g'_non_tail_if oc (NonTail z) e1 e2 "je" "jne"
  | NonTail z, IfLe (x, y', e1, e2) ->
    fprintf oc "\tcmpl\t%s, %s\n" (pp_id_or_imm y') x;
    g'_non_tail_if oc (NonTail z) e1 e2 "jle" "jg"
  | NonTail z, IfLt (x, y', e1, e2) ->
    fprintf oc "\tcmpl\t%s, %s\n" (pp_id_or_imm y') x;
    g'_non_tail_if oc (NonTail z) e1 e2 "jl" "jge"
  | Tail, WhileEq (x, y', e) -> 
    g'_tail_while oc x y' e "je" "jne"
  | Tail, WhileLe (x, y', e) -> 
    g'_tail_while oc x y' e "jle" "jg"
  | Tail, WhileLt (x, y', e) -> 
    g'_tail_while oc x y' e "jl" "jge"
  | NonTail z, WhileEq (x, y', e) ->
    g'_non_tail_while oc x y' z e "je" "jne"
  | NonTail z, WhileLe (x, y', e) ->
    g'_non_tail_while oc x y' z e "jle" "jg"
  | NonTail z, WhileLt (x, y', e) ->
    g'_non_tail_while oc x y' z e "jl" "jge"
  | _, Break ->
    assert (!current_label <> "");
    fprintf oc "\tjmp\t%s\n" !current_label
  | Tail, CallCls (x, ys) ->
    g'_args oc [(x, reg_cl)] ys;
    fprintf oc "\tjmp\t*(%s)\n" reg_cl
  | Tail, CallDir (Id.L x, ys) ->
    g'_args oc [] ys;
    fprintf oc "\tjmp\t%s\n" x
  | NonTail a, CallCls (x, ys) -> 
    g'_args oc [(x, reg_cl)] ys;
    let ss = stacksize () in
    if ss > 0 then fprintf oc "\taddl\t$%d, %s\n" ss reg_sp;
    fprintf oc "\tcall\t*(%s)\n" reg_cl;
    if ss > 0 then fprintf oc "\tsubl\t$%d, %s\n" ss reg_sp;

    if List.mem a allregs && a <> regs.(0) then
      fprintf oc "\tmovl\t%s, %s\n" regs.(0) a
  | NonTail a, CallDir (Id.L x, ys) ->
    g'_args oc [] ys;
    let ss = stacksize () in
    if ss > 0 then fprintf oc "\taddl\t$%d, %s\n" ss reg_sp;
    fprintf oc "\tcall\t%s\n" x;
    if ss > 0 then fprintf oc "\tsubl\t$%d, %s\n" ss reg_sp;

    if List.mem a allregs && a <> regs.(0) then
      fprintf oc "\tmovl\t%s, %s\n" regs.(0) a

and g'_args oc x_reg_cl ys = 
  assert (List.length ys <= Array.length regs - List.length x_reg_cl);
  let sw = sprintf "%d(%s)" (stacksize ()) reg_sp in
  let (i, yrs) = List.fold_left (fun (i, yrs) y ->
    i + 1, (y, regs.(i)) :: yrs)
    (0, x_reg_cl)
    ys in
  List.iter (fun (y, r) ->
    fprintf oc "\tmovl\t%s, %s\n" y r)
    (shuffle sw yrs)


and g'_non_tail_while oc x y' z e br br_not = 
  let start_label = Id.genid (br ^ "_while_start") in
  let end_label = Id.genid (br ^ "_while_end") in
  current_label := end_label;

  (* save x and y *)
  save x;
  fprintf oc "\tmovl\t%s, %d(%s)\n" x (offset x) reg_sp;
  (match y' with
  | V y -> begin 
    save y;
    fprintf oc "\tmovl\t%s, %d(%s)\n" y (offset y) reg_sp
  end
  | _ -> ());

  (* label *)
  fprintf oc "%s:\n" start_label;

  (* load x and y *)
  fprintf oc "\tmovl\t%d(%s), %s\n" (offset x) reg_sp x;
  (match y' with
  | V y -> fprintf oc "\tmovl\t%d(%s), %s\n" (offset y) reg_sp y
  | _ -> ());

  (* compare and jump *)
  fprintf oc "\tcmpl\t%s, %s\n" (pp_id_or_imm y') x;
  fprintf oc "\t%s\t%s\n" br_not end_label;

  g oc (NonTail z, e);

  fprintf oc "\tjmp\t%s\n" start_label;
  fprintf oc "%s:\n" end_label;
  
      
and g'_tail_while oc x y' e br br_not = 
  let start_label = Id.genid (br ^ "_while_start") in
  let end_label = Id.genid (br ^ "_while_end") in
  current_label := end_label;
  
  (* save x and y *)
  save x;
  fprintf oc "\tmovl\t%s, %d(%s)\n" x (offset x) reg_sp;
  (match y' with
  | V y -> begin 
    save y;
    fprintf oc "\tmovl\t%s, %d(%s)\n" y (offset y) reg_sp
  end
  | _ -> ());

  (* label *)
  fprintf oc "%s:\n" start_label;

  (* load x and y *)
  fprintf oc "\tmovl\t%d(%s), %s\n" (offset x) reg_sp x;
  (match y' with
  | V y -> fprintf oc "\tmovl\t%d(%s), %s\n" (offset y) reg_sp y
  | _ -> ());

  (* compare and jump *)
  fprintf oc "\tcmpl\t%s, %s\n" (pp_id_or_imm y') x;
  fprintf oc "\t%s\t%s\n" br_not end_label;

  g oc (NonTail regs.(0), e);

  fprintf oc "\tjmp\t%s\n" start_label;
  fprintf oc "%s:\n" end_label;
  fprintf oc "\tret\n"
    
      
and g'_tail_if oc e1 e2 br br_not = 
  let br_else_label = Id.genid (br ^ "_else") in
  fprintf oc "\t%s\t%s\n" br_not br_else_label;
  let stackset_back = !stackset in
  g oc (Tail, e1);
  fprintf oc "%s:\n" br_else_label;
  stackset := stackset_back;
  g oc (Tail, e2)

and g'_non_tail_if oc dest e1 e2 br br_not = 
  let else_label = Id.genid (br ^ "_else") in
  let cont_label = Id.genid (br ^ "_cont") in
  fprintf oc "\t %s\t%s\n" br_not else_label;
  
  let stackset_back = !stackset in
  g oc (dest, e1);
  let stackset1 = !stackset in
  fprintf oc "\tjmp\t%s\n" cont_label;

  fprintf oc "%s:\n" else_label;
  stackset := stackset_back;
  g oc (dest, e2);
  
  fprintf oc "%s:\n" cont_label;

  let stackset2 = !stackset in
  stackset := S.inter stackset1 stackset2
  
let h oc { name = Id.L x; args = _; body = e; ret = _ } =
  fprintf oc "%s:\n" x;
  stackset := S.empty;
  stackmap := [];
  g oc (Tail, e)

let f oc (Prog (data, fundecs, e)) =
  fprintf oc ".text\n";
  List.iter
    (fun (Id.L x, s) -> 
      fprintf oc "%s:\n" x;
      fprintf oc "\t.ascii\t\"%s\"\n" s)
    data;

  List.iter (h oc) fundecs;

  fprintf oc ".globl\ttiger_start\n";
  fprintf oc "tiger_start:\n";
  fprintf oc ".globl\t_tiger_start\n";
  fprintf oc "_tiger_start:\n";
  fprintf oc "\tpushl\t%%eax\n";
  fprintf oc "\tpushl\t%%ebx\n";
  fprintf oc "\tpushl\t%%ecx\n";  
  fprintf oc "\tpushl\t%%edx\n";
  fprintf oc "\tpushl\t%%esi\n";
  fprintf oc "\tpushl\t%%edi\n";
  fprintf oc "\tpushl\t%%ebp\n";
  fprintf oc "\tmovl\t32(%%esp),%s\n" reg_sp;
  fprintf oc "\tmovl\t36(%%esp),%s\n" regs.(0);
  fprintf oc "\tmovl\t%s,%s\n" regs.(0) reg_hp;

  stackset := S.empty;
  stackmap := [];
  g oc (NonTail regs.(0), e);

  fprintf oc "\tpopl\t%%ebp\n";
  fprintf oc "\tpopl\t%%edi\n";
  fprintf oc "\tpopl\t%%esi\n";
  fprintf oc "\tpopl\t%%edx\n";
  fprintf oc "\tpopl\t%%ecx\n";
  fprintf oc "\tpopl\t%%ebx\n";
  fprintf oc "\tpopl\t%%eax\n";
  fprintf oc "\tret\n";
