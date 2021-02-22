
%{
	open Ast

%}

%token<string> COMMENT
%token<string> BINARY HEX_DECIMAL DECIMAL NUMERAL STRING SYMBOL KEYWORD
%token PAR_OPEN PAR_CLOSE UNDERSCORE AS
%token CMD_SET_LOGIC CMD_SET_INFO CMD_SET_OPTION CMD_DECLARE_FUN CMD_DEFINE_FUN
%token CMD_ASSERT CMD_CHECK_SAT CMD_GET_MODEL CMD_EXIT
%token BOOL LET
%token TRUE FALSE
%token EOF

%start file
%type <Ast.file> file

%%

file
  : script EOF                          { $1 }
;

script
  :                                     { [] }
  | command script                      { $1::$2 }
;


/* Commands */

command
  : PAR_OPEN CMD_SET_LOGIC symbol PAR_CLOSE
	                                    { CSetLogic $3 }
  | PAR_OPEN CMD_SET_INFO attribute PAR_CLOSE
	                                    { CSetInfo $3 }
  | PAR_OPEN CMD_SET_OPTION solver_option PAR_CLOSE
	                                    { CSetOption $3 }
  | PAR_OPEN CMD_DECLARE_FUN symbol PAR_OPEN sort_list PAR_CLOSE sort PAR_CLOSE
                                        { CDeclareFun ($3, $5, $7) }
  | PAR_OPEN CMD_DEFINE_FUN function_def PAR_CLOSE
                                        { let (a, b, c, d) = $3 in
 										  CDefineFun (a, b, c, d) }
  | PAR_OPEN CMD_ASSERT term PAR_CLOSE  { CAssert $3 }
  | PAR_OPEN CMD_CHECK_SAT PAR_CLOSE    { CCheckSat }
  | PAR_OPEN CMD_GET_MODEL PAR_CLOSE    { CGetModel }
  | PAR_OPEN CMD_EXIT PAR_CLOSE         { CExit }
  | COMMENT                             { CComment $1 }
;

function_def
  : symbol PAR_OPEN sorted_var_list PAR_CLOSE sort term
                                        { ($1, $3, $5, $6) }
;

sorted_var_list
  :                                     { [] }
  | sorted_var sorted_var_list          { $1::$2 }
;

sorted_var
  : PAR_OPEN symbol sort PAR_CLOSE      { ($2, $3) }
;

/* Sorts */

sort
  : identifier                          { SIdentifier $1 }
  | PAR_OPEN identifier sort_list_nonempty PAR_CLOSE
	                                    { SApplication ($2, $3) }
;

sort_list
  :                                     { [] }
  | sort sort_list                      { $1::$2 }
;

sort_list_nonempty
  : sort                                { [$1] }
  | sort sort_list_nonempty             { $1::$2 }
;


/* Terms */

term
  : spec_constant                       { TConstant $1 }
  | qual_identifier                     { TVariable $1 }
  | PAR_OPEN qual_identifier term_list_nontmpey PAR_CLOSE
	                                    { TApplication ($2, $3) }
  | PAR_OPEN LET PAR_OPEN var_binding_list_nonempty PAR_CLOSE term PAR_CLOSE
                                        { TLet ($4, $6) }
;

term_list_nontmpey
  : term                                { [$1] }
  | term term_list_nontmpey             { $1::$2 }
;


/* Variable binding */

var_binding_list_nonempty
  : var_binding                         { [$1] }
  | var_binding var_binding_list_nonempty
                                        { $1::$2 }
;

var_binding
  : PAR_OPEN symbol term PAR_CLOSE      { ($2, $3) }
;


/* Identifiers */

qual_identifier
  : identifier                          { QIdentifier $1 }
  | PAR_OPEN AS identifier sort PAR_CLOSE
                                        { QAnnotated ($3, $4) }
;

identifier
  : symbol                              { ISimple $1 }
  | PAR_OPEN UNDERSCORE symbol index_list_nonempty PAR_CLOSE
                                        { IIndexed ($3, $4) }
;

index
  : numeral                             { INumeral $1 }
  | symbol                              { ISymbol $1 }
;

index_list_nonempty
  : index                               { [$1] }
  | index index_list_nonempty           { $1::$2 }
;



/* Attributes */

keyword
  : KEYWORD                             { $1 }
;

attribute
  : keyword                             { AKeyword $1 }
  | keyword spec_constant               { AConstant ($1, $2) }
  | keyword symbol                      { ASymbol ($1, $2) }
;


/* Solver Options */

solver_option :
  keyword                               { OKeyword $1 }
| keyword spec_constant                 { OConstant ($1, $2) }
| keyword symbol                        { OSymbol ($1, $2) }
;


/* Symbols */

symbol
  : SYMBOL                              { $1 }
  | BOOL                                { bool_type_name }
  | bool_value                          { string_of_bool $1 }
;


/* spec_constant */

spec_constant
  : numeral                             { CNumeral $1 }
  | decimal                             { CDecimal $1 }
  | hexadecimal                         { CHexDecimal $1 }
  | binary                              { CBinary $1 }
  | string                              { CString $1 }
;

numeral
  : NUMERAL                             { Z.of_string $1 }
;

decimal
  : DECIMAL                             { $1 }
;

hexadecimal
  : HEX_DECIMAL                         { String.uppercase_ascii $1 }
;

binary
  : BINARY                              { $1 }
;

string
  : STRING                              { $1 }
;

bool_value
  : TRUE                                { true }
  | FALSE                               { false }
;
