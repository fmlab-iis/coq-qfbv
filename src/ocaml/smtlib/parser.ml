open SmtlibParser

let parse file =
  let lexbuf = Lexing.from_channel (open_in file) in
  SmtlibParser.file SmtlibLexer.token lexbuf
