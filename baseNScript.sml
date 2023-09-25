open HolKernel Parse boolLib bossLib;
open listTheory stringTheory wordsTheory wordsLib;

val _ = new_theory "baseN";

(****************************************)
(*               Base16                 *)
(****************************************)

(* Base16 Alphabet *)

Definition ALPH_BASE16_DEF:
  ALPH_BASE16 = "0123456789ABCDEF"
End


(* Base16 Encoding *)

Definition base16enc_def:
    base16enc ([]: word8 list) = ([]: num list)
 /\ base16enc (w::ws: word8 list) = 
      (w2n ((7 >< 4) w: word4))::(w2n ((3 >< 0) w: word4))::(base16enc ws)
End

EVAL ``MAP (λi. EL i ALPH_BASE16) $ base16enc [] = ""``
EVAL ``MAP (λi. EL i ALPH_BASE16) $ base16enc [0b11011110w; 0b10101101w; 0b10111110w; 0b11101111w] = "DEADBEEF"``


(* Base16 Decoding *)

Definition base16dec_def:
    base16dec ([]: num list) = ([]: word8 list)
 /\ base16dec (c1::c2::cs) = 
      ((n2w c1: word4) @@ (n2w c2: word4))::(base16dec cs)
End

EVAL ``base16dec $ MAP (λc. THE $ INDEX_OF c ALPH_BASE16) "" = []``
EVAL ``base16dec $ MAP (λc. THE $ INDEX_OF c ALPH_BASE16) "DEADBEEF" = [0b11011110w; 0b10101101w; 0b10111110w; 0b11101111w]``


(* Theorems *)

Theorem BASE16_DEC_ENC_W8S:
  !(ws: word8 list). base16dec (base16enc ws) = ws
Proof
  Induct_on `ws` >- (
    rw [base16enc_def, base16dec_def]
  ) >> (
    rw [base16enc_def, base16dec_def]
    >> Q.SPECL_THEN [`7`, `3`, `0`] MP_TAC $ INST_TYPE [(``:'a`` |-> ``:8``), (``:'b`` |-> ``:4``), (``:'c`` |-> ``:4``), (``:'d`` |-> ``:8``)] wordsTheory.CONCAT_EXTRACT
    >> rw [wordsTheory.EXTRACT_ALL_BITS]
  ) 
QED

Theorem BASE16_DEC_ENC_ID:
  base16dec o base16enc = I
Proof
  rw [FUN_EQ_THM, BASE16_DEC_ENC_W8S]
QED

Theorem BASE16_ENC_DEC_ID:
  base16enc o base16dec = I
Proof
  cheat
QED


(****************************************)
(*               Base32                 *)
(****************************************)

(* Base32 Alphabet *)

Definition ALPH_BASE32_DEF:
  ALPH_BASE32 = "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"
End

Definition alph_base32_el_def:
  alph_base32_el (n: num) = (EL n ALPH_BASE32): char
End

Definition alph_base32_index_def:
  alph_base32_index (c: char) = (THE $ INDEX_OF c ALPH_BASE32): num
End


(* Base32 Padding and De-Padding *)

Definition base32pad_def:
    (* Base cases *)
    base32pad ([]: num list) = ("": string)
 /\ base32pad [n1; n2] =
      (MAP alph_base32_el [n1; n2]) ++ "======"
 /\ base32pad [n1; n2; n3; n4] =  
      (MAP alph_base32_el [n1; n2; n3; n4]) ++ "===="
 /\ base32pad [n1; n2; n3; n4; n5] =
      (MAP alph_base32_el [n1; n2; n3; n4; n5]) ++ "==="
 /\ base32pad [n1; n2; n3; n4; n5; n6; n7] =
      (MAP alph_base32_el [n1; n2; n3; n4; n5; n6; n7]) ++ "="
    (* Recursive case *)
 /\ base32pad (n1::n2::n3::n4::n5::n6::n7::n8::ns: num list) =  
      (MAP alph_base32_el [n1; n2; n3; n4; n5; n6; n7; n8]) ++ (base32pad ns)
End

Definition base32depad_def:
    (* Base cases *)
    base32depad ([]: string) = ([]: num list)
 /\ base32depad (c1::c2::"======") = [] 
 /\ base32depad (c1::c2::c3::c4::"====") = []
 /\ base32depad (c1::c2::c3::c4::c5::"===") = []
 /\ base32depad (c1::c2::c3::c4::c5::c6::c7::"=") = []
    (* Recursive case *)
 /\ base32depad (c1::c2::c3::c4::c5::c6::c7::c8::cs) = [] ++ (base32depad cs)
End
(* TODO: Why doesn't this work ^ *)


(* Base32 Encoding *)

(*
Definition bar_def:
  bar (b: bool['a]) = if dimindex (:'a) >= 5 then 
    (((dimindex(:'a)-1) >< (dimindex(:'a)-5)) b)::(bar (((dimindex(:'a)-6) >< 0) b))
   else
    ([]: word5 list) 
End
*)

Definition b10_to_w5lst_def:
  b10_to_w5lst (b: bool[10]) = [(9 >< 5) b; (4 >< 0) b]: word5 list
End

Definition b20_to_wd5lst_def:
  b20_to_w5lst (b: bool[20]) = (b10_to_w5lst $ (19 >< 10) b) ++ (b10_to_w5lst $ (9 >< 0) b)
End

Definition b25_to_wd5lst_def:
  b25_to_w5lst (b: bool[25]) = ((25 >< 20) b)::(b20_to_w5lst $ (19 >< 0) b)
End

Definition b35_to_w5lst_def:
  b35_to_w5lst (b: bool[35]) = (b10_to_w5lst $ (34 >< 25) b) ++ (b25_to_w5lst $ (24 >< 0) b)
End

Definition b40_to_w5lst_def:
  b40_to_w5lst (b: bool[40]) = (b20_to_w5lst $ (39 >< 20) b) ++ (b20_to_w5lst $ (19 >< 0) b)
End


Definition base32enc_def:
    (* Base cases *)
    base32enc ([]: word8 list) = ([]: num list)
 /\ base32enc [w1] = 
      MAP w2n 
    $ b10_to_w5lst 
    $ w1 @@ (0b0w: bool[2])
 /\ base32enc [w1; w2] =
      MAP w2n 
    $ b20_to_w5lst 
    $ (concat_word_list [w2; w1]: bool[16]) @@ (0b0w: bool[4])
 /\ base32enc [w1; w2; w3] =
      MAP w2n 
    $ b25_to_w5lst 
    $ (concat_word_list [w3; w2; w1]: bool[24]) @@ (0b0w: bool[1])
 /\ base32enc [w1; w2; w3; w4] = 
      MAP w2n 
    $ b35_to_w5lst 
    $ (concat_word_list [w4; w3; w2; w1]: bool[32]) @@ (0b0w: bool[3])
    (* Recursive case *)
 /\ base32enc (w1::w2::w3::w4::w5::ws) = 
      (MAP w2n 
    $ b40_to_w5lst 
    $ (concat_word_list [w5; w4; w3; w2; w1]: bool[40])) ++ (base32enc ws)
End

(* RFC 4648 Test Vectors *)
EVAL ``base32pad $ base32enc [] = ""``
EVAL ``base32pad $ base32enc [0b01100110w] = "MY======"``
EVAL ``base32pad $ base32enc [0b01100110w; 0b01101111w] = "MZXQ===="``
EVAL ``base32pad $ base32enc [0b01100110w; 0b01101111w; 0b01101111w] = "MZXW6==="``
EVAL ``base32pad $ base32enc [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w] = "MZXW6YQ="``
EVAL ``base32pad $ base32enc [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w; 0b01100001w] = "MZXW6YTB"``
EVAL ``base32pad $ base32enc [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w; 0b01100001w; 0b01110010w] = "MZXW6YTBOI======"``


(* Base32 Decoding *)

Definition b8_to_w8lst:
  b8_to_w8lst (b: bool[8]) = [b]: word8 list
End

Definition b16_to_w8lst:
  b16_to_w8lst (b: bool[16]) = ((15 >< 8) b)::(b8_to_w8lst $ (7 >< 0) b)
End

Definition b24_to_w8lst:
  b24_to_w8lst (b: bool[24]) = ((23 >< 16) b)::(b16_to_w8lst $ (15 >< 0) b)
End

Definition b32_to_w8lst:
  b32_to_w8lst (b: bool[32]) = ((31 >< 24) b)::(b24_to_w8lst $ (23 >< 0) b)
End

Definition b40_to_w8lst:
  b40_to_w8lst (b: bool[40]) = ((39 >< 32) b)::(b32_to_w8lst $ (31 >< 0) b)
End

Definition base32dec_def:
    (* Base cases *)
    base32dec ([]: num list) = ([]: word8 list)
 /\ base32dec [n1; n2] = 
      b8_to_w8lst
    $ (9 >< 2)
    $ (concat_word_list
    $ (MAP n2w [n2; n1]: word5 list)): bool[10]
 /\ base32dec [n1; n2; n3; n4] =
      b16_to_w8lst
    $ (19 >< 4)
    $ (concat_word_list
    $ (MAP n2w [n4; n3; n2; n1]: word5 list)): bool[20]
 /\ base32dec [n1; n2; n3; n4; n5] =
      b24_to_w8lst
    $ (24 >< 1)
    $ (concat_word_list
    $ (MAP n2w [n5; n4; n3; n2; n1]: word5 list)): bool[25]
 /\ base32dec [n1; n2; n3; n4; n5; n6; n7] =
      b32_to_w8lst
    $ (34 >< 3)
    $ (concat_word_list
    $ (MAP n2w [n7; n6; n5; n4; n3; n2; n1]: word5 list)): bool[35]
    (* Recursive case *)
 /\ base32dec (n1::n2::n3::n4::n5::n6::n7::n8::ns) =
      (b40_to_w8lst
    $ (concat_word_list
    $ (MAP n2w [n7; n6; n5; n4; n3; n2; n1]: word5 list)): bool[40]) ++ (base32dec ns)
End

(* RFC 4648 Test Vectors *)
EVAL ``base32dec $ base32depad "" = []``
EVAL ``base32dec $ base32depad "MY======" = [0b01100110w]``
EVAL ``base32dec $ base32depad "MZXQ====" = [0b01100110w; 0b01101111w]``
EVAL ``base32dec $ base32depad "MZXW6===" = [0b01100110w; 0b01101111w; 0b01101111w]``
EVAL ``base32dec $ base32depad "MZXW6YQ=" = [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w]``
EVAL ``base32dec $ base32depad "MZXW6YTB" = [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w; 0b01100001w]``
EVAL ``base32dec $ base32depad "MZXW6YTBOI======" = [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w; 0b01100001w; 0b01110010w]``

val _ = export_theory();
