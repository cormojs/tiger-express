open KNormal

let rec f = function 
  | If ((comp, x, y), e1, e2) ->
    If ((comp, x, y), f e1, f e2)
  | Let (VarDec (xname, xtyp, e1), e2) ->
    let rec insert = function
      | Let (VarDec (yname, ytyp, e3), e4) ->
	Let (VarDec (yname, ytyp, e3), insert e4)
      | Let (FunctionDecs fundecs, e) ->
	Let (FunctionDecs fundecs, insert e)
      | Let (TypeDecs tydecs, e) ->
	Let (TypeDecs tydecs, insert e)
      | e ->
	Let (VarDec (xname, xtyp, e), f e2) in
    insert (f e1)
  | Let (TypeDecs ty_decs, e) ->
    Let (TypeDecs ty_decs, f e)
  | Let (FunctionDecs fundecs, e) ->
    Let (FunctionDecs
	   (List.map (fun (name, args, typ, e') ->
	     (name, args, typ, f e')) fundecs),
	    f e)
  | e -> e
