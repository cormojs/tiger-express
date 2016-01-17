{ 
  open Parser
  open Lexing
}

let space = [' ' '\t' '\r']
let newline = ['\n']
let digit = ['0'-'9']
let alpha = ['A'-'Z' 'a'-'z' '_']
let ident = alpha (alpha | digit)*

rule token = parse
| space+     { token lexbuf }
| newline    { new_line lexbuf;
	       token lexbuf }
| "/*"       { comment lexbuf; 
	       token lexbuf } 
| "type"     { TYPE }
| "var"      { VAR  }
| "function" { FUNCTION }
| "break"    { BREAK }
| "of"       { OF }
| "end"      { END }
| "in"       { IN }
| "nil"      { NIL }
| "let"      { LET }
| "do"       { DO }
| "to"       { TO }
| "for"      { FOR }
| "while"    { WHILE }
| "else"     { ELSE }
| "then"     { THEN }
| "if"       { IF }
| "array"    { ARRAY }
| ":="       { ASSIGN }
| "|"        { OR }
| "&"        { AND }
| ">="       { GE }
| ">"        { GT }
| "<="       { LE }
| "<"        { LT }
| "="        { EQ }
| "<>"       { NEQ }
| "/"        { DIV }
| "*"        { MUL }
| "-"        { SUB }
| "+"        { ADD }
| "."        { DOT }
| "{"        { LBRACE }
| "}"        { RBRACE }
| "["        { LBRACK }
| "]"        { RBRACK }
| "("        { LPAREN }
| ")"        { RPAREN }
| ";"        { SEMICOLON }
| ":"        { COLON }
| ","        { COMMA }
| digit+ as n  { INT (int_of_string n) }
| ident as id  { IDENT id }
| '"'        { string "" lexbuf }
| eof        { EOF }
and string str = parse
| '"' { STRING str }
| _ as c { string (str ^ Char.escaped c) lexbuf }
and comment = parse
| "*/" { () }
| "/*" { comment lexbuf;
	 comment lexbuf }
| _ { comment lexbuf }
