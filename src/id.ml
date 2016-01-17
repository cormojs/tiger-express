type t = string [@@deriving show]
type l = L of string [@@deriving show]

let counter = ref 0

exception Error

let id_of_typ = function
  | Type.Record _ -> "r"
  | Type.Nil      -> "n"
  | Type.Int      -> "i"
  | Type.String   -> "s"
  | Type.Array _  -> "a"
  | Type.Name _   -> raise Error
  | Type.Unit     -> "u"

let genid s = 
  incr counter;
  Printf.sprintf "%s.%d" s !counter
    
let gentmp typ = 
  incr counter;
  Printf.sprintf "T%s%d" (id_of_typ typ) !counter
