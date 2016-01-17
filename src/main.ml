type token = [%import: Parser.token] [@@deriving show]

exception Error
  
let rec print_lex lexbuf = 
  match Lexer.token lexbuf with
  | Parser.EOF -> print_newline ()
  | tok -> begin
    print_string @@ show_token tok;
    print_char ' ';
    print_lex lexbuf
  end

let parse lexbuf = 
  try Parser.program Lexer.token lexbuf
  with exn -> begin
    let curr = lexbuf.Lexing.lex_curr_p in
    let line = curr.Lexing.pos_lnum in
    let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    let tok = Lexing.lexeme lexbuf in
    let buffer = lexbuf.Lexing.lex_buffer in
    Printf.eprintf "token error line: %d, column: %d, %s\n" line cnum tok;
    print_endline buffer;
    raise exn
  end

let rec optimize n e =
  Format.eprintf "iteration %d@." n;
  if n = 0 
  then e 
  else let e' = 
	 Beta.f e
         |> Assoc.f
	 |> Inline.f
	 (* |> ConstFold.f *)
	 (* |> Elim.f *)
       in
  if e = e'
  then e
  else optimize (n - 1) e'
  
let () =
  let filename = Sys.argv.(1) in
  let file_chan = open_in filename in
  begin
    try
      Lexing.from_channel file_chan
      |> parse
      |> Typing.f
      |> KNormal.f
      |> Alpha.f
      |> Closure.f
      |> Virtual.f
      |> RegAlloc.f
      |> Emit.f stdout
    with 
    | Typing.UnifyError(pos, t1, t2) -> begin
      Format.eprintf "%s@." @@ Syntax.show_p pos;
      Format.eprintf "%s@." @@ "unify error: ";
      Format.eprintf "%s@." @@ Type.show t1 ^ " vs " ^ Type.show t2
    end
    | Typing.UnifyExpError(exp, pos, t1, t2) -> begin
      Format.eprintf "%s@." @@ Syntax.show_p pos;
      Format.eprintf "%s@." @@
	"Expression " ^ Syntax.show exp ^ " has type " ^ Type.show t1
	^ " but expected is type " ^ Type.show t2;
    end
    | Typing.Error (pos, msg) -> begin
      Format.eprintf "%s@." @@ Syntax.show_p pos;
      Format.eprintf "%s@." msg
    end
  end
 
