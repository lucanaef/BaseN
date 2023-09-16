open HolKernel Parse boolLib bossLib;
open listTheory stringTheory wordsTheory wordsLib;

val _ = new_theory "baseN";

(*
   ███████████                      ████  ████████ 
  ░░███░░░░░███                    ░░███ ███░░░░███
   ░███    ░█████████  █████  ██████░███░███   ░░░ 
   ░██████████░░░░░██████░░  ███░░██░███░█████████ 
   ░███░░░░░█████████░░█████░███████░███░███░░░░███
   ░███    ░█████░░███░░░░██░███░░░ ░███░███   ░███
   ██████████░░█████████████░░██████████░░████████ 
  ░░░░░░░░░░░ ░░░░░░░░░░░░░  ░░░░░░░░░░░ ░░░░░░░░  
*)

(* Base16 Alphabet *)

Definition alph_base16_el_def:
  alph_base16_el (w: word4) = (EL (w2n w) "0123456789ABCDEF"): char
End

Definition alph_base16_index_def:
  alph_base16_index (c: char) = (n2w $ THE $ INDEX_OF c "0123456789ABCDEF"): word4
End


(* Base16 Encoding *)

Definition base16enc_def:  
    base16enc ([]: word8 list) = ""
 /\ base16enc (w::ws: word8 list) =
     STRING (alph_base16_el ((7 >< 4) w)) $
     STRING (alph_base16_el ((3 >< 0) w)) (base16enc ws)
End

EVAL ``base16enc [] = ""``
EVAL ``base16enc [0b11011110w; 0b10101101w; 0b10111110w; 0b11101111w] = "DEADBEEF"``


(* Base16 Decoding *)

Definition base16dec_def:
    base16dec ([]: string) = ([]: word8 list)
 /\ base16dec (c1::(c2::cs)) = 
      (alph_base16_index c1 @@ alph_base16_index c2)::(base16dec cs)
End

EVAL ``base16dec "" = []``
EVAL ``base16dec "DEADBEEF" = [0b11011110w; 0b10101101w; 0b10111110w; 0b11101111w]``

val _ = export_theory();
