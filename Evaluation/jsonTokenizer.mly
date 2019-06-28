%token <int> INT
%token <float> FLOAT
%token <string> STRING
%token TRUE
%token FALSE
%token NULL
%token LEFT_BRACE
%token RIGHT_BRACE
%token LEFT_BRACK
%token RIGHT_BRACK
%token COLON
%token COMMA
%token EOF

%start <token list> top

%%

top:
  | hd = json_token; tl = top { hd :: tl }
  | EOF                       { [] } ;

json_token:
  | i = INT { INT i }
  | f = FLOAT { FLOAT f }
  | s = STRING { STRING s }
  | TRUE { TRUE }
  | FALSE { FALSE }
  | NULL { NULL }
  | LEFT_BRACE { LEFT_BRACE }
  | RIGHT_BRACE { RIGHT_BRACE }
  | LEFT_BRACK { LEFT_BRACK }
  | RIGHT_BRACK { RIGHT_BRACK }
  | COLON { COLON }
  | COMMA { COMMA } ;
