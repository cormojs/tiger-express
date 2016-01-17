module M = Map.Make (struct 
  type t = Id.t
  let compare = compare
end)
include M


let add_list xys env =
  List.fold_left (fun env (x, y) -> add x y env) env xys
