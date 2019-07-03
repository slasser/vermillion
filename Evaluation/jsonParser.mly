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

%start <Json.value option> top

%%
top:
  | v = value { Some v }
  | EOF       { None   } ;

value:
  | LEFT_BRACE; prs = pairs; RIGHT_BRACE      { `Assoc prs  }
  | LEFT_BRACK; es  = elts;  RIGHT_BRACK      { `List es    }
  | s = STRING                                { `String s   }
  | n = INT                                   { `Int n      }
  | x = FLOAT                                 { `Float x    }
  | TRUE                                      { `Bool true  }
  | FALSE                                     { `Bool false }
  | NULL                                      { `Null       } ;

pairs:
  |                                           { []          }
  | pr = pair; prs = pairs_tl                 { pr :: prs   } ;

pairs_tl:
  |                                           { []          }
  | COMMA; pr = pair; prs = pairs_tl          { pr :: prs   } ;

pair:
    s = STRING; COLON; v = value              { (s, v)      } ;

elts:
  |                                           { []          }
  | v = value; vs = elts_tl                   { v :: vs     } ;

elts_tl:
  |                                           { []          } 
  | COMMA; v = value; vs = elts_tl            { v :: vs     } ;
