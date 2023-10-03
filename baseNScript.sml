open HolKernel Parse boolLib bossLib;
open listTheory stringTheory arithmeticTheory wordsTheory wordsLib;
open patternMatchesLib;

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
 /\ base16dec (n1::n2::ns) = 
      ((n2w n1: word4) @@ (n2w n2: word4))::(base16dec ns)
End

EVAL ``base16dec $ MAP (λc. THE $ INDEX_OF c ALPH_BASE16) "" = []``
EVAL ``base16dec $ MAP (λc. THE $ INDEX_OF c ALPH_BASE16) "DEADBEEF" = [0b11011110w; 0b10101101w; 0b10111110w; 0b11101111w]``


(* Theorems *)

Theorem BASE16_DEC_ENC:
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
  rw [FUN_EQ_THM, BASE16_DEC_ENC]
QED


Definition wellformed_base16_def:
  wellformed_base16 (ns: num list) = 
       (EVEN (LENGTH ns) /\ !(n: num). (MEM n ns ==> n < LENGTH ALPH_BASE16))
End

Triviality STRLEN_ALPH_BASE16:
  STRLEN ALPH_BASE16 = 16
Proof
  rw [ALPH_BASE16_DEF]
QED

Theorem BASE16_ENC_DEC:
  !(ns: num list). wellformed_base16 ns ==> base16enc (base16dec ns) = ns
Proof
  gen_tac
  >> completeInduct_on `LENGTH ns`
  >> gen_tac 
  >> Cases_on `ns` 
  >- rw [wellformed_base16_def, base16enc_def, base16dec_def]
  >> Cases_on `t` 
  >- rw [wellformed_base16_def]  
  >> rw [wellformed_base16_def]
  >> rw [base16enc_def, base16dec_def] (* TODO: Use `fs` instead to avoid case
  split *)
  >- (    
    Q.SPECL_THEN [`n2w h`, `n2w h'`] MP_TAC $ INST_TYPE [(``:'a`` |-> ``:4``), (``:'b`` |-> ``:4``), (``:'c`` |-> ``:8``)] wordsTheory.EXTRACT_CONCAT
    >> rw []
    >> REWRITE_TAC [GSYM STRLEN_ALPH_BASE16]
    >> qpat_x_assum `∀n. n = h ∨ n = h' ∨ MEM n t' ⇒ n < STRLEN ALPH_BASE16` $ irule_at Any
    >> rw []
  ) >- (
    Q.SPECL_THEN [`n2w h`, `n2w h'`] MP_TAC $ INST_TYPE [(``:'a`` |-> ``:4``), (``:'b`` |-> ``:4``), (``:'c`` |-> ``:8``)] wordsTheory.EXTRACT_CONCAT
    >> rw []
    >> REWRITE_TAC [GSYM STRLEN_ALPH_BASE16]
    >> qpat_x_assum `∀n. n = h ∨ n = h' ∨ MEM n t' ⇒ n < STRLEN ALPH_BASE16` $ irule_at Any
    >> rw []
  ) >> (
    qpat_x_assum `EVEN (SUC (SUC (LENGTH _)))` MP_TAC
    >> ONCE_REWRITE_TAC [EVEN]
    >> ONCE_REWRITE_TAC [GSYM ODD_EVEN]
    >> ONCE_REWRITE_TAC [ODD]
    >> ONCE_REWRITE_TAC [GSYM EVEN_ODD]
    >> qpat_x_assum `∀n. n = h ∨ n = h' ∨ MEM n t' ⇒ n < STRLEN ALPH_BASE16` MP_TAC
    >> rw [DISJ_IMP_THM, FORALL_AND_THM]
    >> qpat_x_assum `∀n. MEM n t' ⇒ n < STRLEN ALPH_BASE16` MP_TAC
    >> qpat_x_assum `EVEN (LENGTH t')` MP_TAC
    >> REWRITE_TAC [AND_IMP_INTRO]
    >> gvs [GSYM wellformed_base16_def]
  )
QED

Theorem BASE16_ENC_DEC_ID:
  !ns. wellformed_base16 ns ==> (base16enc o base16dec) ns = I ns
Proof
  rw [FUN_EQ_THM, BASE16_ENC_DEC]
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
  base32pad ns = case ns of
    (* Base cases *)
    | ([]: num list) => ("": string)
    | [n1; n2] => (MAP alph_base32_el ns) ++ "======"
    | [n1; n2; n3; n4] => (MAP alph_base32_el ns) ++ "===="
    | [n1; n2; n3; n4; n5] => (MAP alph_base32_el ns) ++ "===" 
    | [n1; n2; n3; n4; n5; n6; n7] => (MAP alph_base32_el ns) ++ "="
    (* Recursive case *)
    | (n1::n2::n3::n4::n5::n6::n7::n8::nss: num list) 
    => (MAP alph_base32_el [n1; n2; n3; n4; n5; n6; n7; n8]) ++ (base32pad nss)
End


Definition base32depad_def:
  base32depad cs = case cs of
    (* Base cases *)
    | ([]: string) => ([]: num list)
    | (c1::c2::"======") => MAP alph_base32_index [c1; c2]
    | (c1::c2::c3::c4::"====") => MAP alph_base32_index [c1; c2; c3; c4]
    | (c1::c2::c3::c4::c5::"===") => MAP alph_base32_index [c1; c2; c3; c4; c5]
    | (c1::c2::c3::c4::c5::c6::c7::"=") => MAP alph_base32_index [c1; c2; c3; c4; c5; c6; c7]
    (* Recursive case *)
    | (c1::c2::c3::c4::c5::c6::c7::c8::css) 
    => MAP alph_base32_index [c1; c2; c3; c4; c5; c6; c7; c8] ++ (base32depad css)
End


(* Base32 Encoding *)

Definition b10_to_w5lst_def:
  b10_to_w5lst (b: bool[10]) = [(9 >< 5) b; (4 >< 0) b]: word5 list
End

Definition b20_to_w5lst_def:
  b20_to_w5lst (b: bool[20]) = (b10_to_w5lst $ (19 >< 10) b) ++ (b10_to_w5lst $ (9 >< 0) b)
End

Definition b25_to_w5lst_def:
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

Definition b8_to_w8lst_def:
  b8_to_w8lst (b: bool[8]) = [b]: word8 list
End

Definition b16_to_w8lst_def:
  b16_to_w8lst (b: bool[16]) = ((15 >< 8) b)::(b8_to_w8lst $ (7 >< 0) b)
End

Definition b24_to_w8lst_def:
  b24_to_w8lst (b: bool[24]) = ((23 >< 16) b)::(b16_to_w8lst $ (15 >< 0) b)
End

Definition b32_to_w8lst_def:
  b32_to_w8lst (b: bool[32]) = ((31 >< 24) b)::(b24_to_w8lst $ (23 >< 0) b)
End

Definition b40_to_w8lst_def:
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
    $ (MAP n2w [n8; n7; n6; n5; n4; n3; n2; n1]: word5 list)): bool[40]) ++ (base32dec ns)
End

(* RFC 4648 Test Vectors *)
EVAL ``base32dec $ base32depad "" = []``
EVAL ``base32dec $ base32depad "MY======" = [0b01100110w]``
EVAL ``base32dec $ base32depad "MZXQ====" = [0b01100110w; 0b01101111w]``
EVAL ``base32dec $ base32depad "MZXW6===" = [0b01100110w; 0b01101111w; 0b01101111w]``
EVAL ``base32dec $ base32depad "MZXW6YQ=" = [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w]``
EVAL ``base32dec $ base32depad "MZXW6YTB" = [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w; 0b01100001w]``
EVAL ``base32dec $ base32depad "MZXW6YTBOI======" = [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w; 0b01100001w; 0b01110010w]``


(* Theorems *)

(* Padding Theorems *)

Definition wf_base32_numlst_def:
  wf_base32_numlst (ns: num list) = 
    (MEM (LENGTH ns MOD 8) [0; 2; 5; 7] 
  /\ !(n: num). (MEM n ns ==> n < LENGTH ALPH_BASE32))
End

Triviality ALL_DISTINCT_ALPH_BASE32: 
  ALL_DISTINCT ALPH_BASE32
Proof
  rw [ALPH_BASE32_DEF]
QED

Triviality PAD_NOT_IN_ALPH_BASE32:
  !(n: num). n < LENGTH ALPH_BASE32 ==> alph_base32_el n <> #"="
Proof
  completeInduct_on `n`
  >> rw [alph_base32_el_def, ALPH_BASE32_DEF]
  >> ntac 16 $ EVERY [Cases_on `n`, rw [], Cases_on `n'`, rw []]
  >> fs []
QED

Theorem ALPH_BASE32_INDEX_EL:
  !n. n < STRLEN ALPH_BASE32 ==> alph_base32_index (alph_base32_el n) = n
Proof
  rw [alph_base32_el_def, alph_base32_index_def]
  >> ASSUME_TAC ALL_DISTINCT_ALPH_BASE32 
  >> rw [ALL_DISTINCT_INDEX_OF_EL]
QED


Theorem BASE32_PAD_DEPAD_LENGTH0:
  !ns. LENGTH ns = 0 /\ wf_base32_numlst ns ==> base32depad (base32pad ns) = ns
Proof
  ONCE_REWRITE_TAC [base32pad_def]
  >> ONCE_REWRITE_TAC [base32depad_def]
  >> rw []
QED

Theorem BASE32_PAD_DEPAD_LENGTH2:
  !ns. LENGTH ns = 2 /\ wf_base32_numlst ns ==> base32depad (base32pad ns) = ns
Proof
  Cases_on `ns` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'`
  >> rw [wf_base32_numlst_def]
  >> rw [base32pad_def]
  >> rw [base32depad_def]
  >> rw [ALPH_BASE32_INDEX_EL]
QED

Theorem BASE32_PAD_DEPAD_LENGTH5:
  !ns. LENGTH ns = 5 /\ wf_base32_numlst ns ==> base32depad (base32pad ns) = ns
Proof
  Cases_on `ns` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t`
  >> rw [base32pad_def]
  >> rw [base32depad_def]
  >> fs [wf_base32_numlst_def, ALPH_BASE32_INDEX_EL]
  >> ASSUME_TAC PAD_NOT_IN_ALPH_BASE32
  >> fs [wf_base32_numlst_def]
  >> METIS_TAC []
QED

Theorem BASE32_PAD_DEPAD_LENGTH7:
  !ns. LENGTH ns = 7 /\ wf_base32_numlst ns ==> base32depad (base32pad ns) = ns
Proof
  cheat
QED


(* TODO: Reminaing cases *)

Theorem BASE32_PAD_DEPAD:
  !ns. wf_base32_numlst ns ==> base32depad (base32pad ns) = ns
Proof
  gen_tac 
  >> completeInduct_on `LENGTH ns` 
  >> Cases_on `v < 8`
  (* Base cases *)
    (* Case: base32depad (base32pad [n1]) = [n1] *)
  >- Cases_on `v = 0` >- rw [BASE32_PAD_DEPAD_LENGTH0]
    (* Case: base32depad (base32pad [n1]) = [n1] *)
  >> Cases_on `v = 1` >- rw [wf_base32_numlst_def]
    (* Case: base32depad (base32pad [n1; n2]) = [n1; n2] *)
  >> Cases_on `v = 2` >- rw [BASE32_PAD_DEPAD_LENGTH2]
  >> Cases_on `v = 3` >- rw [wf_base32_numlst_def] 
  >> Cases_on `v = 4` >- rw [wf_base32_numlst_def] 
  >> Cases_on `v = 5` >- rw [BASE32_PAD_DEPAD_LENGTH5] 
  >> Cases_on `v = 6` >- rw [wf_base32_numlst_def]
  >> Cases_on `v = 7` >- rw [BASE32_PAD_DEPAD_LENGTH7]
  >> cheat
QED

(* En- and Decoding Theorems *)

Theorem BASE32_DEC_ENC_LENGTH1:
  !(ws: word8 list). LENGTH ws = 1 ==> base32dec (base32enc ws) = ws
Proof
  Cases_on `ws` 
  >> rw [] 
  >> rw [base32enc_def, b10_to_w5lst_def]
  >> rw [base32dec_def, b8_to_w8lst_def]
  >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
QED

Theorem BASE32_DEC_ENC_LENGTH2:
  !(ws: word8 list). LENGTH ws = 2 ==> base32dec (base32enc ws) = ws
Proof
  (* Trivial cases *)
  Cases_on `ws` >- rw []
  >> Cases_on `t` >- rw []
  (* Main case *)
  >> rw [base32enc_def, b20_to_w5lst_def]
  >> rw [base32dec_def, b10_to_w5lst_def, b16_to_w8lst_def, b8_to_w8lst_def]
  >> ntac 2 $ SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
QED

Theorem BASE32_DEC_ENC_LENGTH3:
  !(ws: word8 list). LENGTH ws = 3 ==> base32dec (base32enc ws) = ws
Proof
  (* Trivial cases *)
  Cases_on `ws` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t`
  (* Main case *)
  >> rw [base32enc_def, b25_to_w5lst_def, b20_to_w5lst_def, b10_to_w5lst_def]
  >> rw [base32dec_def, b16_to_w8lst_def, b24_to_w8lst_def] 
  >> ntac 2 $ SIMP_TAC (std_ss++WORD_LOGIC_ss) []
  >> rw [b8_to_w8lst_def] 
  >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
QED

Theorem BASE32_DEC_ENC_LENGTH4:
  !(ws: word8 list). LENGTH ws = 4 ==> base32dec (base32enc ws) = ws
Proof
  (* Trivial cases *)
  Cases_on `ws` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'`
  (* Main case *)
  >> rw [base32enc_def, b35_to_w5lst_def, b10_to_w5lst_def, b25_to_w5lst_def, b20_to_w5lst_def] 
  >> rw [base32dec_def, b32_to_w8lst_def] >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
  >> rw [b24_to_w8lst_def] >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
  >> rw [b16_to_w8lst_def] >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
  >> rw [b8_to_w8lst_def] >> ntac 2 $ SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [] >> rw []
QED

Theorem BASE32_DEC_ENC:
  !(ws: word8 list). base32dec (base32enc ws) = ws
Proof
  gen_tac
  >> completeInduct_on `LENGTH ws`
  >> Cases_on `v < 5` >- (
    (* Base cases *)
    Cases_on `v = 0` >- rw [base32enc_def, base32dec_def]
    >> Cases_on `v = 1` >- rw [BASE32_DEC_ENC_LENGTH1]
    >> Cases_on `v = 2` >- rw [BASE32_DEC_ENC_LENGTH2]
    >> Cases_on `v = 3` >- rw [BASE32_DEC_ENC_LENGTH3]
    >> Cases_on `v = 4` >- rw [BASE32_DEC_ENC_LENGTH4]
    >> rw []
  ) >> (
    (* Trivial cases *) 
    Cases_on `ws` >- rw [] 
    >> Cases_on `t` >- rw []
    >> Cases_on `t'` >- rw []
    >> Cases_on `t` >- rw []
    >> Cases_on `t'` >- rw []
    (* Recursive case *)
    >> rw [base32enc_def]
    >> rw [b40_to_w5lst_def, b20_to_w5lst_def, b10_to_w5lst_def]
    >> rw [base32dec_def]
    >> rw [b40_to_w8lst_def] >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
    >> rw [b32_to_w8lst_def] >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
    >> rw [b24_to_w8lst_def] >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
    >> rw [b16_to_w8lst_def] >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
    >> rw [b8_to_w8lst_def] >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
  )
QED

Theorem BASE32_DEC_ENC_ID:
  base32dec o base32enc = I
Proof
  rw [FUN_EQ_THM, BASE32_DEC_ENC]
QED



Definition wellformed_base32_def:
  wellformed_base32 (ns: num list) = 
    ((LENGTH ns MOD 8 <> 1) /\ (LENGTH ns MOD 8 <> 3) /\ (LENGTH ns MOD 8 <> 6)
 /\ !(n: num). (MEM n ns ==> n < LENGTH ALPH_BASE32))
End

Triviality STRLEN_ALPH_BASE32:
  STRLEN ALPH_BASE32 = 32
Proof
  rw [ALPH_BASE32_DEF]
QED

Theorem BASE32_ENC_DEC_LENGTH2:
  !(ns: num list). LENGTH ns = 2 /\ wellformed_base32 ns ==> base32enc (base32dec ns) = ns
Proof
  Cases_on `ns` >- rw []
  >> Cases_on `t` >- rw []
  >> rw []
  >> REWRITE_TAC [base32dec_def, b8_to_w8lst_def]
  >> REWRITE_TAC [base32enc_def, b10_to_w5lst_def]
  >> REWRITE_TAC [MAP]
  >> REWRITE_TAC [concat_word_list_def]
  >> SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []
  >> REWRITE_TAC [INST_TYPE [(``:'a`` |-> ``:5``)] w2n_n2w]
  >> first_x_assum mp_tac
  >> REWRITE_TAC [wellformed_base32_def]
  >> rw [STRLEN_ALPH_BASE32]

(*
      ∀n. n = h ∨ n = h' ⇒ n < 32
    --------------------------------
    w2n ((4 >< 2) (n2w h') ≪ 2) = h'
  
  
    This (^) obviously doesn't hold !h':word5.
    Because we are missing the constraint that the 2 LSB of h' MBZ.
    Should this be part of a more elaborate definition of `wellformed_base32`?
*)
QED

Theorem BASE32_ENC_DEC_LENGTH4:
  !(ns: num list). LENGTH ns = 4 /\ wellformed_base32 ns ==> base32enc (base32dec ns) = ns
Proof
  cheat
QED

Theorem BASE32_ENC_DEC_LENGTH5:
  !(ns: num list). LENGTH ns = 5 /\ wellformed_base32 ns ==> base32enc (base32dec ns) = ns
Proof
  cheat
QED

Theorem BASE32_ENC_DEC_LENGTH7:
  !(ns: num list). LENGTH ns = 7 /\ wellformed_base32 ns ==> base32enc (base32dec ns) = ns
Proof
  cheat
QED

Theorem BASE32_ENC_DEC:
  !(ns: num list). wellformed_base32 ns ==> base32enc (base32dec ns) = ns
Proof
  gen_tac
  >> completeInduct_on `LENGTH ns` 
  >> Cases_on `v < 8` >- (
    (* Base cases *)
    Cases_on `v = 0` >- rw [base32dec_def, base32enc_def]
    >> Cases_on `v = 1` >- rw [wellformed_base32_def]
    >> Cases_on `v = 2` >- rw [BASE32_ENC_DEC_LENGTH2]
    >> Cases_on `v = 3` >- rw [wellformed_base32_def]
    >> Cases_on `v = 4` >- rw [BASE32_ENC_DEC_LENGTH4]
    >> Cases_on `v = 5` >- rw [BASE32_ENC_DEC_LENGTH5]
    >> Cases_on `v = 6` >- rw [wellformed_base32_def]
    >> Cases_on `v = 7` >- rw [BASE32_ENC_DEC_LENGTH7]
    >> rw []
  ) >> (
    (* Recursive case *)
    cheat
  )
QED


val _ = export_theory();
