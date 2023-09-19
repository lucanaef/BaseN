open HolKernel Parse boolLib bossLib;
open listTheory stringTheory wordsTheory wordsLib;

val _ = new_theory "baseN";

(****************************************)
(*               Base16                 *)
(****************************************)

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

(* TODO: How do I handle invalid input in such a definition? Raise HOL_ERR somehow? *)

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

(* Theorems *)

Theorem BASE16_W8_INV_FUN:
  !(w8: word8). base16dec (base16enc ([w8])) = [w8]
Proof
  (*TODO: Can I somehow prove this exhaustively? Use the same strat for all 256 values of w8. *)
  (* `blastLib.BBLAST_TAC` ?*)
  cheat 
QED

Theorem BASE16_INV_FUN:
  !(ws: word8 list). base16dec (base16enc (ws)) = ws
Proof
  cheat 
QED


(****************************************)
(*               Base32                 *)
(****************************************)

(* Base32 Alphabet *)

Definition alph_base32_el_def:
  alph_base32_el (w: word5) = (EL (w2n w) "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"): char
End

Definition alph_base32_index_def:
  alph_base32_index (c: char) = (n2w $ THE $ INDEX_OF c "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"): word5
End


(* Base32 Encoding *)

(* 
  Generalise functions below into one funtion that 
  takes one bs: bool[k] where k % 5 = 0 and retruns a list of k/5 chars 
*) 

Definition alph_base32_ext_8_10_def:
  alph_base32_ext_8_10 (x: bool[8]) = (x @@ (0b0w: bool[2])): bool[10]
End

Definition alph_base32_lookup_8_def: 
  alph_base32_lookup_8 (x: bool[8]) = 
    STRING (alph_base32_el $ (9 >< 5) (alph_base32_ext_8_10 x)) $
    STRING (alph_base32_el $ (4 >< 0) (alph_base32_ext_8_10 x)) ""
End

Definition alph_base32_ext_16_20_def:
  alph_base32_ext_16_20 (x: bool[16]) = (x @@ (0b0w: bool[4])): bool[20]
End

Definition alph_base32_lookup_16_def: 
  alph_base32_lookup_16 (x: bool[16]) =
    STRING (alph_base32_el $ (19 >< 15) (alph_base32_ext_16_20 x)) $
    STRING (alph_base32_el $ (14 >< 10) (alph_base32_ext_16_20 x)) $
    STRING (alph_base32_el $ ( 9 ><  5) (alph_base32_ext_16_20 x)) $
    STRING (alph_base32_el $ ( 4 ><  0) (alph_base32_ext_16_20 x)) ""
End

Definition alph_base32_ext_24_25_def:
  alph_base32_ext_24_25 (x: bool[24]) = (x @@ (0b0w: bool[1])): bool[25]
End

Definition alph_base32_lookup_24_def: 
  alph_base32_lookup_24 (x: bool[24]) =
    STRING (alph_base32_el $ (24 >< 20) (alph_base32_ext_24_25 x)) $
    STRING (alph_base32_el $ (19 >< 15) (alph_base32_ext_24_25 x)) $
    STRING (alph_base32_el $ (14 >< 10) (alph_base32_ext_24_25 x)) $
    STRING (alph_base32_el $ ( 9 ><  5) (alph_base32_ext_24_25 x)) $
    STRING (alph_base32_el $ ( 4 ><  0) (alph_base32_ext_24_25 x)) ""
End

Definition alph_base32_ext_32_35_def:
  alph_base32_ext_32_35 (x: bool[32]) = (x @@ (0b0w: bool[3])): bool[35]
End

Definition alph_base32_lookup_32_def: 
  alph_base32_lookup_32 (x: bool[32]) =
    STRING (alph_base32_el $ (34 >< 30) (alph_base32_ext_32_35 x)) $
    STRING (alph_base32_el $ (29 >< 25) (alph_base32_ext_32_35 x)) $
    STRING (alph_base32_el $ (24 >< 20) (alph_base32_ext_32_35 x)) $
    STRING (alph_base32_el $ (19 >< 15) (alph_base32_ext_32_35 x)) $
    STRING (alph_base32_el $ (14 >< 10) (alph_base32_ext_32_35 x)) $
    STRING (alph_base32_el $ ( 9 ><  5) (alph_base32_ext_32_35 x)) $
    STRING (alph_base32_el $ ( 4 ><  0) (alph_base32_ext_32_35 x)) ""
End

Definition alph_base32_lookup_40_def: 
  alph_base32_lookup_40 (x: bool[40]) =
    STRING (alph_base32_el $ (39 >< 35) x) $
    STRING (alph_base32_el $ (34 >< 30) x) $
    STRING (alph_base32_el $ (29 >< 25) x) $
    STRING (alph_base32_el $ (24 >< 20) x) $
    STRING (alph_base32_el $ (19 >< 15) x) $
    STRING (alph_base32_el $ (14 >< 10) x) $
    STRING (alph_base32_el $ ( 9 ><  5) x) $
    STRING (alph_base32_el $ ( 4 ><  0) x) ""
End


Definition base32enc_def:
    (* Recursive case *)
    base32enc (w1::w2::w3::w4::w5::ws: word8 list) = 
      (alph_base32_lookup_40 (concat_word_list [w5; w4; w3; w2; w1])) ++ (base32enc ws)
    (* Base cases *)
 /\ base32enc (w1::w2::w3::w4::[]: word8 list) = 
      (alph_base32_lookup_32 (concat_word_list [w4; w3; w2; w1]))++ "="
 /\ base32enc (w1::w2::w3::[]: word8 list) = 
      (alph_base32_lookup_24 (concat_word_list [w3; w2; w1])) ++ "==="
 /\ base32enc (w1::w2::[]: word8 list) = 
      (alph_base32_lookup_16 (concat_word_list [w2; w1])) ++ "====" 
 /\ base32enc (w1::[]: word8 list) = 
      (alph_base32_lookup_8 w1) ++ "======" 
 /\ base32enc ([]: word8 list) = ""
End


(* RFC 4648 Test Vectors *)
EVAL ``base32enc [] = ""``
EVAL ``base32enc [0b01100110w] = "MY======"``
EVAL ``base32enc [0b01100110w; 0b01101111w] = "MZXQ===="``
EVAL ``base32enc [0b01100110w; 0b01101111w; 0b01101111w] = "MZXW6==="``
EVAL ``base32enc [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w] = "MZXW6YQ="``
EVAL ``base32enc [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w; 0b01100001w] = "MZXW6YTB"``
EVAL ``base32enc [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w; 0b01100001w; 0b01110010w] = "MZXW6YTBOI======"``


(* Base32 Decoding *)

(* TODO: Why doesn't this work? Too many base cases? *)
Definition base32dec_def:
    (* Base cases *)
    base32dec ([]: string) = ([]: word8 list)
 /\ base32dec (c1::c2::"======") =
      [(9 >< 2) (concat_word_list [alph_base32_index c2; alph_base32_index c1])]
 /\ base32dec (c1::c2::c3::c4::"====") = []
 /\ base32dec (c1::c2::c3::c4::c5::"===") = []
 /\ base32dec (c1::c2::c3::c4::c5::c6::c7::"=") = []
     (* Recursive case*)
 /\ base32dec (c1::c2::c3::c4::c5::c7::c8::cs) = []
End

(* RFC 4648 Test Vectors *)
EVAL ``base32dec "" = []``
EVAL ``base32dec "MY======" = [0b01100110w]``
EVAL ``base32dec "MZXQ====" = [0b01100110w; 0b01101111w]``
EVAL ``base32dec "MZXW6===" = [0b01100110w; 0b01101111w; 0b01101111w]``
EVAL ``base32dec "MZXW6YQ=" = [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w]``
EVAL ``base32dec "MZXW6YTB" = [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w; 0b01100001w]``
EVAL ``base32dec "MZXW6YTBOI======" = [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w; 0b01100001w; 0b01110010w]``

val _ = export_theory();
