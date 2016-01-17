%{
  open Syntax
  let pos i =
    Parsing.rhs_start_pos i
    (* let p = Parsing.rhs_start_pos i in  *)
    (* Pos (p.Lexing.pos_lnum, p.Lexing.pos_cnum) *)
%}

%token TYPE VAR FUNCTION BREAK
%token ARRAY ASSIGN OR AND 
%token OF END IN NIL LET DO TO
%token FOR WHILE ELSE THEN IF
%token GE GT LE LT EQ NEQ
%token DIV MUL SUB ADD
%token DOT
%token LBRACK RBRACK
%token LBRACE RBRACE 
%token LPAREN RPAREN SEMICOLON COLON COMMA
%token EOF
%token <int> INT
%token <string> IDENT
%token <string> STRING

%type <Syntax.t> program
%start program

%nonassoc prec_if
%nonassoc ELSE
%nonassoc OF DO
%left OR AND
%left EQ NEQ LE LT GE GT
%left ADD SUB
%left MUL DIV
%left prec_uminus

%%

program:
 | exp EOF { $1 }
;
     
exp:
 | INT      { Int ($1, $startpos($1)) }
 | STRING   { String ($1, $startpos($1)) }
 | lvalue   { Var ($1, $startpos($1)) }
 | record   { $1 }
 | NIL      { Nil ($startpos($1)) }
 | unit     { $1 }
 | sequence { $1 }
 | funcCall { $1 }
 | arithexp { $1 }
 | compexp  { $1 }
 | boolexp  { $1 }
 | assign   { $1 }
 | array    { $1 }
 | control  { $1 }
;
  
record: 
 | IDENT LBRACE RBRACE 
     { Record ([], $1, $startpos($1)) }
 | IDENT LBRACE recordFields RBRACE 
     { Record ($3, $1, $startpos($1)) }
;

recordFields:
 | IDENT EQ exp 
     { [($1, $3)] }
 | IDENT EQ exp COMMA recordFields
     { ($1, $3) :: $5 }
;

unit: 
 | LPAREN RPAREN { Unit ($startpos($1)) }
;

sequence:
 | LPAREN seqexp RPAREN { Sequence ($2, $startpos($2)) }
;

seqexp: 
 | exp { [$1] }
 | exp SEMICOLON seqexp 
     { $1 :: $3 }
;

funcCall: 
 | IDENT LPAREN RPAREN
     { Call ($1, [], $startpos($1)) }
 | IDENT LPAREN funcParam RPAREN 
     { Call ($1, $3, $startpos($1)) }
;

funcParam:
 | exp { [$1] }
 | exp COMMA funcParam { $1 :: $3 }
;



arithexp:
 | exp ADD exp 
     { Op (OpAdd, $1, $3, $startpos($1)) } 
 | exp SUB exp 
     { Op (OpSub, $1, $3, $startpos($1)) }
 | exp MUL exp 
     { Op (OpMul, $1, $3, $startpos($1)) } 
 | exp DIV exp
     { Op (OpDiv, $1, $3, $startpos($1)) }
 | SUB exp %prec prec_uminus
     { Op (OpSub, Int (0, $startpos($2)), $2, $startpos($2)) }
;

compexp:
 | exp GE exp 
     { Op (OpGe, $1, $3, $startpos($1)) } 
 | exp GT exp
     { Op (OpGt, $1, $3, $startpos($1)) } 
 | exp LE exp
     { Op (OpLe, $1, $3, $startpos($1)) } 
 | exp LT exp
     { Op (OpLt, $1, $3, $startpos($1)) } 
 | exp EQ exp
     { Op (OpEq, $1, $3, $startpos($1)) } 
 | exp NEQ exp 
     { Op (OpNeq, $1, $3, $startpos($1)) } 

boolexp: 
 | exp AND exp 
     { If ($1, $3, Int (0, $startpos($1)), $startpos($1)) }
 | exp OR exp
     { If ($1, Int (0, $startpos($1)), $3, $startpos($1)) }
;

array:
 | lvalue LBRACK exp RBRACK OF exp
     { match $1 with
     | SimpleVar id -> Array (id, $3, $6, $startpos($1))
     | _ -> raise Parsing.Parse_error }
;


assign:
 | lvalue ASSIGN exp
     { Assign ($1, $3, $startpos($1)) }
;

control:
 | IF exp THEN exp %prec prec_if
     { If ($2, $4, Unit ($startpos($1)), $startpos($2)) }
 | IF exp THEN exp ELSE exp
     { If ($2, $4, $6,   $startpos($2)) }
 | WHILE exp DO exp
     { While ($2, $4, $startpos($2)) }
 | FOR IDENT ASSIGN exp TO exp DO exp
     { For ($2, $4, $6, $8, $startpos($2)) }
 | BREAK 
     { Break ($startpos($1)) }
 | LET decs IN seqexp END
     { Let ($2, Sequence ($4, $startpos($4)),
	    $startpos($2)) }
;

decs: 
 | list(dec)
     { $1 }
;

dec: 
 | tydecs  { TypeDecs $1 }
 | vardec  { $1 }
 | fundecs { FunDecs $1 }
;

tydecs:
 | tydec
     { [$1] }
 | tydec tydecs
     { $1 :: $2 }
;

tydec: 
 | TYPE IDENT EQ ty 
     { ($2, $4, $startpos($2)) }
;

ty:
 | IDENT { NameTy ($1, $startpos($1)) }
 | LBRACE tyfields RBRACE { RecordTy ($2, $startpos($2)) }
 | ARRAY OF IDENT { ArrayTy ($3, $startpos($3)) }
;

tyfields:
 | { [] }
 | tyfields_tail
     { $1 }
;
tyfields_tail:
 | IDENT COLON IDENT
     { [($1, $3)] }
 | IDENT COLON IDENT COMMA tyfields
     { ($1, $3)::$5 }
;

vardec:
 | VAR IDENT ASSIGN exp 
     { VarDec ($2, None, $4, $startpos($2)) }
 | VAR IDENT COLON IDENT ASSIGN exp 
     { VarDec ($2, Some $4, $6, $startpos($2)) }
;

fundecs:
 | nonempty_list(fundec)
     { $1 }
;

fundec:
 | FUNCTION IDENT LPAREN tyfields RPAREN EQ exp
     { ($2, $4, None, $7, $startpos($2)) }
 | FUNCTION IDENT LPAREN tyfields RPAREN COLON IDENT EQ exp
     { ($2, $4, Some $7, $9, $startpos($2)) }
;
		

lvalue:
 | IDENT
     { SimpleVar $1 }
 | lvalue LBRACK exp RBRACK
     { SubscriptVar ($1, $3) }
 | lvalue DOT IDENT
     { FieldVar ($1, $3) }
;
