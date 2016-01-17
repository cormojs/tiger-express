module S = Set.Make (struct 
  type t = Id.t
  let compare = compare
end)

include S

let of_list = List.fold_left (fun s e -> add e s) empty
