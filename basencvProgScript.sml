open preamble basis ml_progTheory astPP fromSexpTheory astToSexprLib;
open base16Theory base32Theory base64Theory;

val _ = new_theory "basencvProg";

val _ = translation_extends "basisProg"

Definition help_string_def:
  help_string = concat $ MAP (λx. strlit $ x ++ "\n") [
    "basencv - Verified implementations of Base-N data encodings";
    "";
    "Usage: basencv [OPTION]... [FILE]";
    "basencv encodes or decodes FILE, or standard input, to standard output.";
    "";
    "OPTIONS";
    "      --base16  Base16 encoding (RFC4648 section 8)";
    "      --base32  Base32 encoding (RFC4648 section 6)";
    "      --base64  Base64 encoding (RFC4648 section 4)";
    "  -d, --decode  Decode data";
    "  -h, --help    Display help text and exit.";
    "";
    "Decoding fails if the input is not properly padded or contains";
    "non-alphabet bytes in the encoded stream."
  ]
End

Definition missing_encoding_type_string_def:
  missing_encoding_type_string = concat $ MAP (λx. strlit $ x ++ "\n") [
    "basencv: missing encoding type";
    "Try 'basencv --help' for more information."
  ]
End

Theorem help_string_thm = EVAL ``help_string``
Theorem missing_encoding_type_string_thm = EVAL ``missing_encoding_type_string``

(* Base16 *)
val _ = translate base16enc_def
val _ = translate base16dec_def

(* Base32 *)
val _ = translate base32pad_def
val _ = translate base32depad_def
val _ = translate base32enc_def
val _ = translate base32dec_def

(* Base64 *)
val _ = translate base64pad_def
val _ = translate base64depad_def
val _ = translate base64enc_def
val _ = translate base64dec_def

val res = append_prog o process_topdecs $ `
fun main () =
let
  val args = CommandLine.arguments()

  val base16_flags = ["--base16"]
  val base32_flags = ["--base32"]
  val base64_flags = ["--base64"]
  val decode_flags = ["-d", "--decode"]
  val help_flags = ["-h","--help"]

  val base16 = List.exists (fn f => List.member f base16_flags) args
  val base32 = List.exists (fn f => List.member f base32_flags) args
  val base64 = List.exists (fn f => List.member f base64_flags) args
  val decode = List.exists (fn f => List.member f decode_flags) args
  val help = List.exists (fn f => List.member f help_flags) args

  val args_filter = List.filter
    (fn f => not(List.member f (zero_flags @ help_flags))) args

  val split_char = Char.chr (if zero then 0 else 10)

  val content = case args_filter of
     [] => TextIO.inputAll TextIO.stdIn
    | args => String.concat (List.map (TextIO.inputAll o TextIO.openIn) args)

  val content_lines = String.tokens (fn c => c = split_char) content
in
  if help then
    TextIO.print help_string
  else if decode then 
    if base16 then
      TextIO.print "Branch: Decode base16"
    else if base32 then
      TextIO.print "Branch: Decode base32"
    else if base64 then
      TextIO.print "Branch: Decode base64"
    else
      TextIO.print missing_encoding_type_string
  else
    if base16 then
      TextIO.print "Branch: Encode base16"
    else if base32 then
      TextIO.print "Branch: Encode base32"
    else if base64 then
      TextIO.print "Branch: Encode base64"
    else
      TextIO.print missing_encoding_type_string
end;
`;

val prog =
  ``SNOC
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
    ^(get_ml_prog_state() |> get_prog)
  `` |> EVAL |> concl |> rhs

val _ = astToSexprLib.write_ast_to_file "basencvProg.sexp" prog;

val _ = export_theory ();