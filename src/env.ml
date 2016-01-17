type t = 
| VarEntry of Type.t
| FunEntry of Type.t list * Type.t
[@@deriving show]

let peel = function
  | VarEntry t -> VarEntry (Type.peel t)
  | entry -> entry

let base_tenv = List.fold_left (fun e (k, v) -> M.add k v e)
  M.empty
  [ ("int", Type.Int);
    ("string", Type.String); 
    ("unit", Type.Unit);
    ("nil", Type.Nil); ]

let base_venv : t M.t =
  M.empty
  |> M.add "getchar" @@ FunEntry([], Type.String)
  |> M.add "ord"     @@ FunEntry([Type.String], Type.Int)
  |> M.add "print"   @@ FunEntry([Type.String], Type.Unit)
  |> M.add "print_int" @@ FunEntry([Type.Int], Type.Unit)
  |> M.add "chr"     @@ FunEntry([Type.Int], Type.String)
      
