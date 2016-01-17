module rec Type : sig
  type t =
  | Record of t M.t * unique
  | Nil
  | Int
  | String
  | Array of t * unique 
  | Name of string * t option ref
  | Unit
  and unique = string
  val show : t -> string
  val pp : Format.formatter -> t -> unit
  val peel : t -> t
end = struct 
  type t =
  | Record of t M.t * unique
  | Nil
  | Int
  | String
  | Array of t * unique 
  | Name of string * t option ref
  | Unit
  and unique = string
  let rec show = function
    | Record (m, _) ->
      let lst = M.bindings m in
      "Record { " ^
      (String.concat "; "
	(List.map (fun (id, t) -> id ^ ":" ^ show t) lst))
	^ " }"
    | Nil -> "Nil"
    | Int -> "Int"
    | String -> "String"
    | Array (t, _) -> "Array of " ^ show t
    | Name (id, t_op_ref) -> "Named " ^ id
    | Unit -> "Unit"
  and pp fmt t = Format.fprintf fmt "Type.%s" @@ show t
  let peel = function
    | Name (id, t_op_ref) as named -> (match !t_op_ref with
      | Some ty -> ty
      | None -> named)
    | ty -> ty
end
and M : Map.S with type key = string
  = Map.Make(struct 
    type t = string
    let compare = String.compare
  end)

include Type
