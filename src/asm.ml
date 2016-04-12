type id_or_imm = V of Id.t | C of int
[@@deriving show]

type t =
| Ans of exp
| Let of (Id.t * Type.t) * exp * t
[@@deriving show]

and exp = 
| Nop
| Mov of id_or_imm
| MovL of Id.l
| MovR of Id.t * id_or_imm
| MovS of Id.t * Id.t * id_or_imm * int
| MovO of Id.t * id_or_imm * int
| Add of Id.t * id_or_imm
| Sub of Id.t * id_or_imm
| Mul of Id.t * id_or_imm
| Div of Id.t * id_or_imm
| Comment of string
| IfEq of Id.t * id_or_imm * t * t
| IfLe of Id.t * id_or_imm * t * t
| IfLt of Id.t * id_or_imm * t * t
| WhileEq of Id.t * id_or_imm * t
| WhileLe of Id.t * id_or_imm * t
| WhileLt of Id.t * id_or_imm * t
| Break
| CallCls of Id.t * Id.t list
| CallDir of Id.l * Id.t list
| Save of Id.t * Id.t
| Restore of Id.t
[@@deriving show]

type fundef = { name : Id.l;
		args : Id.t list;
		body : t;
		ret : Type.t }
[@@deriving show]

type prog = Prog of (Id.l * string) list * fundef list * t
[@@deriving show]

let seq (e1, e2) = 
  Let ((Id.gentmp Type.Unit, Type.Unit), e1, e2)

let regs = 
  [| "%eax"; "%ebx"; "%ecx"; "%edx"; "%esi"; "%edi" |]

(* let fregs = Array.init 8 (fun i -> Printf.sprintf "%%xmm%d" i) *)
let allregs = Array.to_list regs
(* let allfregs = Array.to_list fregs *)
let reg_cl = regs.(Array.length regs - 1)

let reg_sp = "%ebp"
let reg_hp = "tiger_hp"
let is_reg x = (x.[0] = '%' || x = reg_hp)

let rec remove_and_uniq xs = function
  | [] -> []
  | x :: ys when S.mem x xs -> remove_and_uniq xs ys
  | x :: ys -> x :: remove_and_uniq (S.add x xs) ys

let fv_id_or_imm = function V(x) -> [x] | _ -> []

let rec fv_exp = function
  | Break | Nop | Mov (C _) | MovL(_) | Comment(_) | Restore(_) -> []
  | Mov (V x) | Save(x, _) -> [x]
  | MovR (x, y') | Add (x, y') | Sub (x, y') 
  | Mul (x, y') | Div (x, y') | MovO(x, y', _) -> x :: fv_id_or_imm y'
  | MovS(x, y, z', _) -> x :: y :: fv_id_or_imm z'
  | IfEq(x, y', e1, e2) | IfLe(x, y', e1, e2) | IfLt(x, y', e1, e2) -> 
    x :: fv_id_or_imm y' @ remove_and_uniq S.empty (fv' e1 @ fv' e2)
  | WhileEq(x, y', e) | WhileLe(x, y', e) | WhileLt(x, y', e) ->
    x :: fv_id_or_imm y' @ remove_and_uniq S.empty (fv' e)
  | CallCls(x, ys) -> x :: ys
  | CallDir(_, ys) -> ys
and fv' = function
  | Ans exp -> fv_exp exp
  | Let ((x, t), exp, e) ->
      fv_exp exp @ remove_and_uniq (S.singleton x) (fv' e)
let fv e = remove_and_uniq S.empty (fv' e)

let rec concat e1 xt e2 =
  match e1 with
  | Ans exp -> Let(xt, exp, e2)
  | Let(yt, exp, e1') -> Let(yt, exp, concat e1' xt e2)

let align i = (if i mod 8 = 0 then i else i + 4)
