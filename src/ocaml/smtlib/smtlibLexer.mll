{
  open SmtlibParser

  exception Error of string
  let lnum = ref 1
  let cnum = ref 0
  let get_len lexbuf = String.length (Lexing.lexeme lexbuf)
  let upd_cnum lexbuf = cnum := !cnum + get_len lexbuf
  let reset_cnum () = cnum := 0
}

let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z']
let binary_digit = ['0' '1']
let numeral = '0' | ['1'-'9'] digit*
let hex_digit = ['0'-'9' 'a'-'f' 'A'-'F' ]
let special_char = ['+' '-' '/' '*' '=' '%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@' '\'']
let symbol = ('|' [^'|']+ '|') | (letter|special_char)(letter|special_char|digit)*
let escape_space = "\"\""

rule token = parse
| ';' ([^'\r''\n']* as comment)         { upd_cnum lexbuf; COMMENT comment }
| [' ' '\t']                            { upd_cnum lexbuf; token lexbuf }
| ("\r\n"|'\n'|'\r')                    { reset_cnum(); incr lnum; token lexbuf }
| '('                                   { upd_cnum lexbuf; PAR_OPEN }
| ')'                                   { upd_cnum lexbuf; PAR_CLOSE }
| '_'                                   { upd_cnum lexbuf; UNDERSCORE }
| "#b" (binary_digit+ as str)           { upd_cnum lexbuf; BINARY str }
| ':' symbol as str                     { upd_cnum lexbuf; KEYWORD str }
| "#x" (hex_digit+ as str)
                                        { upd_cnum lexbuf; HEX_DECIMAL str }
| numeral '.' '0'* numeral as str       { upd_cnum lexbuf; DECIMAL str }
| '0' | ['1'-'9'] digit* as str         { upd_cnum lexbuf; NUMERAL str }
| '"' (([^'"']|escape_space)* as str) '"'
                                        { upd_cnum lexbuf; STRING str }
| "set-logic"                           { upd_cnum lexbuf; CMD_SET_LOGIC }
| "set-info"                            { upd_cnum lexbuf; CMD_SET_INFO }
| "set-option"                          { upd_cnum lexbuf; CMD_SET_OPTION }
| "assert"                              { upd_cnum lexbuf; CMD_ASSERT }
| "check-sat"                           { upd_cnum lexbuf; CMD_CHECK_SAT }
| "get-model"                           { upd_cnum lexbuf; CMD_GET_MODEL }
| "declare-fun"                         { upd_cnum lexbuf; CMD_DECLARE_FUN }
| "define-fun"                          { upd_cnum lexbuf; CMD_DEFINE_FUN }
| "exit"                                { upd_cnum lexbuf; CMD_EXIT }
| "Bool"                                { upd_cnum lexbuf; BOOL }
| "let"                                 { upd_cnum lexbuf; LET }
| "true"                                { upd_cnum lexbuf; TRUE }
| "false"                               { upd_cnum lexbuf; FALSE }
| "as"                                  { upd_cnum lexbuf; AS }
| symbol as str                         { upd_cnum lexbuf; SYMBOL str }
| eof                                   { upd_cnum lexbuf; EOF }
