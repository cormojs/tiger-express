open KNormal

let memi x env = try begin match M.find x env with
  | Int _ -> true
  | _ -> false
end with Not_found -> false


let findi x env = match M.find x env with
  | Int i -> i
  | _ -> raise Not_found


(* let g env = function *)
(*   | Var (SimpleVar *)


(* let f = g M.empty *)
