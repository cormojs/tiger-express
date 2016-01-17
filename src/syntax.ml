type p = [%import: Lexing.position] [@@deriving show]

and t = 
| Int of int * p
| String of string * p
| Record of (Id.t * t) list * Id.t * p
| Nil of  p
| Unit of p
| Sequence of t list * p
| Call of Id.t * t list * p
| Op of operator * t * t * p
| If of t * t * t * p
| Array of Id.t * t * t * p
| Assign of lvalue * t * p
| While of t * t * p
| For of Id.t * t * t * t * p
| Break of p
| Let of dec list * t * p
| Var of lvalue * p
[@@deriving show]

and operator = 
| OpAdd
| OpSub
| OpMul
| OpDiv
| OpGe
| OpGt
| OpLe
| OpLt
| OpEq
| OpNeq

and dec = 
| TypeDecs of (Id.t * ty * p) list
| VarDec  of Id.t * Id.t option * t * p
| FunDecs of fundec list

and fundec = Id.t * (Id.t * Id.t) list * Id.t option * t * p

and ty = 
| NameTy of Id.t * p
| RecordTy of (Id.t * Id.t) list * p
| ArrayTy of Id.t * p

and lvalue = 
| SimpleVar of Id.t
| FieldVar of lvalue * Id.t
| SubscriptVar of lvalue * t


