open HolKernel Parse boolLib bossLib;
open listTheory stringTheory arithmeticTheory wordsTheory wordsLib;
open patternMatchesLib blastLib;

val _ = new_theory "baseN";


(*
              :word8 list -> num list              :num list -> string
                    +----------+                       +----------+
 Encoding  +------  |  *_ENC   |---------------------->|  *_PAD   |  ------+
           |        +----------+                       +----------+        |
           |                                                               |
           |                                                               |
           |                                                               |
           |        +----------+                       +----------+        |
           +----->  |  *_DEC   |<----------------------| *_DEPAD  |  <-----+  Decoding
                    +----------+                       +----------+
              :num list -> word8 list              :string -> num list
*)



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
  >> rw [base16enc_def, base16dec_def] >- (    
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

Definition wf_base32_clst_def:
  wf_base32_clst (cs: char list) = 
    ((LENGTH cs MOD 8 = 0)
 /\ (LENGTH cs >= 8 ==> ~(MEM #"=" $ TAKE 8 cs)))
End


Theorem BASE32_DEPAD_PAD:
  !cs. wf_base32_clst cs ==> base32pad (base32depad cs) = cs
Proof
  gen_tac 
  >> completeInduct_on `LENGTH cs`
  (* Base cases *)
  >> Cases_on `v = 0` >- (
    ONCE_REWRITE_TAC [base32depad_def] >> rw []
    >> ONCE_REWRITE_TAC [base32pad_def] >> rw []
  ) >> Cases_on `v = 8` >- ( 
    rw []
    >> cheat
  )
  >> gen_tac
  >> Cases_on `cs = c1::c2::c3::c4::c5::c6::c7::c8::css` >- (
    >> ASM_REWRITE_TAC []
    >> rw [BASE32_DEPAD_PAD_REC_SPLIT]
    (* TODO: Rewriting below does not work. More work needed.*)
    >> fs [BASE32_DEPAD_PAD_LENGTH8]
    >> cheat
  ) >> (
    (* Cannot be the case *)
    fs [wf_base32_clst_def]
    (* TODO: How can I prove this? *)
  )



  (* Recursive case *) 
  >> rw [wf_base32_clst_def]
  >> Cases_on `cs` >- fs []
  >> Cases_on `t` >- fs []
  >> Cases_on `t'` >- fs []
  >> Cases_on `t` >- fs []
  >> Cases_on `t'` >- fs []
  >> Cases_on `t` >- fs []
  >> Cases_on `t'` >- fs []
  >> Cases_on `t` >- fs []
  >> ONCE_REWRITE_TAC [base32depad_def]
  >> ntac 8 $ fs []
  >> ONCE_REWRITE_TAC [base32pad_def] 
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
  Cases_on `ns` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
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

Theorem BASE32_PAD_DEPAD:
  !ns. wf_base32_numlst ns ==> base32depad (base32pad ns) = ns
Proof
  gen_tac 
  >> completeInduct_on `LENGTH ns` 
  >> Cases_on `v < 8`
  (* Base cases *)
  >> Cases_on `v = 0` >- rw [BASE32_PAD_DEPAD_LENGTH0]
  >> Cases_on `v = 1` >- rw [wf_base32_numlst_def]
  >> Cases_on `v = 2` >- rw [BASE32_PAD_DEPAD_LENGTH2]
  >> Cases_on `v = 3` >- rw [wf_base32_numlst_def] 
  >> Cases_on `v = 4` >- rw [wf_base32_numlst_def] 
  >> Cases_on `v = 5` >- rw [BASE32_PAD_DEPAD_LENGTH5] 
  >> Cases_on `v = 6` >- rw [wf_base32_numlst_def]
  >> Cases_on `v = 7` >- rw [BASE32_PAD_DEPAD_LENGTH7]
  >> rw []
  (* Recursive case *)
  Cases_on `ns` >- rw [] 
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t` >- rw []

  (* Notes:
  *     - quantHeuristicsTheory (e.g. LIST_LENGTH_1)
  *     - ntac 7 (qmatch_goalsub_rename_tac `h::t` >> Cases_on `t`)
  *     - (REWRITE_CONV [GSYM rich_listTheory.COUNT_LIST_COUNT,
  *          GSYM pred_setTheory.IN_COUNT] THENC EVAL) ``LENGTH ls < 8n``;
  *
  *)
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


Definition wf_base32_def:
  wf_base32 (ns: num list) = 
    (* Length *)
    ((LENGTH ns MOD 8 <> 1) /\ (LENGTH ns MOD 8 <> 3) /\ (LENGTH ns MOD 8 <> 6)
    (* Domain *)
 /\ (!(n: num). (MEM n ns ==> n < LENGTH ALPH_BASE32))
    (* LSB Constraints *)
 /\ (LENGTH ns MOD 8 = 2 ==> ((1 >< 0) $ (n2w $ LAST ns): word5) = (0b0w: bool[2]))
 /\ (LENGTH ns MOD 8 = 4 ==> ((3 >< 0) $ (n2w $ LAST ns): word5) = (0b0w: bool[4]))
 /\ (LENGTH ns MOD 8 = 5 ==> ((0 >< 0) $ (n2w $ LAST ns): word5) = (0b0w: bool[1]))
 /\ (LENGTH ns MOD 8 = 7 ==> ((2 >< 0) $ (n2w $ LAST ns): word5) = (0b0w: bool[3])))
End

Triviality STRLEN_ALPH_BASE32:
  STRLEN ALPH_BASE32 = 32
Proof
  rw [ALPH_BASE32_DEF]
QED

Triviality SHIFT_2_LSB_MBZ:
 !(h: word5). (1 >< 0) h: bool[2] = 0w ==> (4 >< 2) h ≪ 2 = h
Proof
  BBLAST_TAC
QED

Theorem BASE32_ENC_DEC_LENGTH2:
  !(ns: num list). LENGTH ns = 2 /\ wf_base32 ns ==> base32enc (base32dec ns) = ns
Proof
  Cases_on `ns` >- rw []
  >> Cases_on `t` >- rw []
  >> rw []
  >> REWRITE_TAC [base32dec_def, b8_to_w8lst_def]
  >> REWRITE_TAC [base32enc_def, b10_to_w5lst_def]
  >> REWRITE_TAC [MAP, concat_word_list_def]
  >> SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []
  >> REWRITE_TAC [INST_TYPE [(``:'a`` |-> ``:5``)] w2n_n2w]
  >> first_x_assum mp_tac
  >> REWRITE_TAC [wf_base32_def]
  >> rw [STRLEN_ALPH_BASE32, SHIFT_2_LSB_MBZ]
QED

Triviality SHIFT_4_LSB_MBZ:
 !(h: word5). (3 >< 0) h: bool[4] = 0w ==> (4 >< 4) h ≪ 4 = h
Proof
  BBLAST_TAC
QED

Theorem BASE32_ENC_DEC_LENGTH4:
  !(ns: num list). LENGTH ns = 4 /\ wf_base32 ns ==> base32enc (base32dec ns) = ns
Proof
  Cases_on `ns` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'`
  >> rw []
  >> REWRITE_TAC [base32dec_def, b8_to_w8lst_def, b16_to_w8lst_def]
  >> REWRITE_TAC [base32enc_def, b10_to_w5lst_def, b20_to_w5lst_def]
  >> REWRITE_TAC [MAP, concat_word_list_def]
  >> SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []
  >> REWRITE_TAC [INST_TYPE [(``:'a`` |-> ``:5``)] w2n_n2w]
  >> first_x_assum mp_tac
  >> fs [wf_base32_def, STRLEN_ALPH_BASE32, SHIFT_4_LSB_MBZ]
QED

Triviality SHIFT_1_LSB_MBZ:
 !(h: word5). (0 >< 0) h: bool[1] = 0w ==> (4 >< 1) h ≪ 1 = h
Proof
  BBLAST_TAC
QED

Theorem BASE32_ENC_DEC_LENGTH5:
  !(ns: num list). LENGTH ns = 5 /\ wf_base32 ns ==> base32enc (base32dec ns) = ns
Proof
  Cases_on `ns` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t`
  >> rw []
  >> REWRITE_TAC [base32dec_def, b8_to_w8lst_def, b16_to_w8lst_def, b24_to_w8lst_def]
  >> REWRITE_TAC [base32enc_def, b10_to_w5lst_def, b20_to_w5lst_def, b25_to_w5lst_def]
  >> REWRITE_TAC [MAP, concat_word_list_def]
  >> SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []
  >> REWRITE_TAC [INST_TYPE [(``:'a`` |-> ``:5``)] w2n_n2w]
  >> first_x_assum mp_tac
  >> rw [wf_base32_def, STRLEN_ALPH_BASE32, SHIFT_1_LSB_MBZ]
QED

Triviality SHIFT_3_LSB_MBZ:
 !(h: word5). (2 >< 0) h: bool[3] = 0w ==> (4 >< 3) h ≪ 3 = h
Proof
  BBLAST_TAC
QED

Theorem BASE32_ENC_DEC_LENGTH7:
  !(ns: num list). LENGTH ns = 7 /\ wf_base32 ns ==> base32enc (base32dec ns) = ns
Proof
  Cases_on `ns` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t`
  >> rw []
  >> REWRITE_TAC [base32dec_def, b8_to_w8lst_def, b16_to_w8lst_def, b24_to_w8lst_def, b32_to_w8lst_def]
  >> REWRITE_TAC [base32enc_def, b10_to_w5lst_def, b20_to_w5lst_def, b25_to_w5lst_def, b35_to_w5lst_def]
  >> REWRITE_TAC [MAP, concat_word_list_def]
  >> SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []
  >> first_x_assum mp_tac
  >> rw [wf_base32_def, STRLEN_ALPH_BASE32, SHIFT_3_LSB_MBZ]
QED

Theorem WF_BASE32_REC:
  !h1 h2 h3 h4 h5 h6 h7 h8 t. wf_base32 (h1::h2::h3::h4::h5::h6::h7::h8::t) ==> wf_base32 t
Proof
  gs [wf_base32_def, SUC_ONE_ADD] 
  >> (
    Cases_on `t` >- fs []
    >> Cases_on `t'` >- fs []
    >> rfs [LAST_DEF]
  )
QED

Theorem BASE32_ENC_DEC:
  !(ns: num list). wf_base32 ns ==> base32enc (base32dec ns) = ns
Proof
  gen_tac
  >> completeInduct_on `LENGTH ns` 
  >> Cases_on `v < 8` >- (
    (* Base cases *)
    Cases_on `v = 0` >- rw [base32dec_def, base32enc_def]
    >> Cases_on `v = 1` >- rw [wf_base32_def]
    >> Cases_on `v = 2` >- rw [BASE32_ENC_DEC_LENGTH2]
    >> Cases_on `v = 3` >- rw [wf_base32_def]
    >> Cases_on `v = 4` >- rw [BASE32_ENC_DEC_LENGTH4]
    >> Cases_on `v = 5` >- rw [BASE32_ENC_DEC_LENGTH5]
    >> Cases_on `v = 6` >- rw [wf_base32_def]
    >> Cases_on `v = 7` >- rw [BASE32_ENC_DEC_LENGTH7]
    >> rw []
  ) >> (
    (* Recursive case *)
    Cases_on `ns` >- rw [] 
    >> Cases_on `t` >- rw []
    >> Cases_on `t'` >- rw []
    >> Cases_on `t` >- rw []
    >> Cases_on `t'` >- rw [] 
    >> Cases_on `t` >- rw []
    >> Cases_on `t'` >- rw []
    >> Cases_on `t` >- rw []
    >> REWRITE_TAC [base32dec_def, b40_to_w8lst_def, b32_to_w8lst_def, b24_to_w8lst_def, b16_to_w8lst_def, b8_to_w8lst_def]
    >> REWRITE_TAC [MAP, concat_word_list_def]
    >> SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []
    >> rw [GSYM rich_listTheory.CONS_APPEND]
    >> REWRITE_TAC [base32enc_def, b40_to_w5lst_def, b20_to_w5lst_def, b10_to_w5lst_def]
    >> REWRITE_TAC [MAP, concat_word_list_def]
    >> SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []
    >> rw [wordsTheory.w2n_n2w]
    >- fs [wf_base32_def, STRLEN_ALPH_BASE32]
    >- fs [wf_base32_def, STRLEN_ALPH_BASE32]
    >- fs [wf_base32_def, STRLEN_ALPH_BASE32]
    >- fs [wf_base32_def, STRLEN_ALPH_BASE32]
    >- fs [wf_base32_def, STRLEN_ALPH_BASE32]
    >- fs [wf_base32_def, STRLEN_ALPH_BASE32]
    >- fs [wf_base32_def, STRLEN_ALPH_BASE32]
    >- fs [wf_base32_def, STRLEN_ALPH_BASE32]
    >> Q.SPECL_THEN [`h`, `h'`, `h''`, `h'³'`, `h'⁴'`, `h'⁵'`, `h'⁶'`, `h'⁷'`, `t'`] MP_TAC WF_BASE32_REC
    >> fs []
  )
QED



(****************************************)
(*               Base64                 *)
(****************************************)

(* Base64 Alphabet *)

Definition ALPH_BASE64_DEF:
  ALPH_BASE64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
End

Definition alph_base64_el_def:
  alph_base64_el (n: num) = (EL n ALPH_BASE64): char
End

Definition alph_base64_index_def:
  alph_base64_index (c: char) = (THE $ INDEX_OF c ALPH_BASE64): num
End


(* Base64 Padding and De-Padding *)

Definition base64pad_def:
  base64pad ns = case ns of
    (* Base cases *)
    | ([]: num list) => ("": string)
    | [n1; n2] => (MAP alph_base64_el ns) ++ "=="
    | [n1; n2; n3] => (MAP alph_base64_el ns) ++ "="
    (* Recursive case *)
    | (n1::n2::n3::n4::nss: num list) 
    => (MAP alph_base64_el [n1; n2; n3; n4]) ++ (base64pad nss)
End

Definition base64depad_def:
  base64depad cs = case cs of
    (* Base cases *)
    | ([]: string) => ([]: num list)
    | (c1::c2::"==") => MAP alph_base64_index [c1; c2]
    | (c1::c2::c3::"=") => MAP alph_base64_index [c1; c2; c3]
    (* Recursive case *)
    | (c1::c2::c3::c4::css) 
    => MAP alph_base64_index [c1; c2; c3; c4] ++ (base64depad css)
End

(* Base64 Encoding *)

Definition b6_to_w6lst_def:
  b6_to_w6lst (b: bool[6]) = [b]: word6 list
End

Definition b12_to_w6lst_def:
  b12_to_w6lst (b: bool[12]) = ((11 >< 6) b)::(b6_to_w6lst $ (5 >< 0) b)
End

Definition b18_to_w6lst_def:
  b18_to_w6lst (b: bool[18]) = ((17 >< 12) b)::(b12_to_w6lst $ (11 >< 0) b)
End

Definition b24_to_w6lst_def:
  b24_to_w6lst (b: bool[24]) = ((23 >< 18) b)::(b18_to_w6lst $ (17 >< 0) b)
End

Definition base64enc_def:
    (* Base cases *)
    base64enc ([]: word8 list) = ([]: num list)
 /\ base64enc [w1] = 
      MAP w2n 
    $ b12_to_w6lst 
    $ w1 @@ (0b0w: bool[4])
 /\ base64enc [w1; w2] =
      MAP w2n 
    $ b18_to_w6lst 
    $ (concat_word_list [w2; w1]: bool[16]) @@ (0b0w: bool[2]) 
    (* Recursive case *)
 /\ base64enc (w1::w2::w3::ws) = 
      (MAP w2n 
    $ b24_to_w6lst 
    $ (concat_word_list [w3; w2; w1]: bool[24])) ++ (base64enc ws)
End

(* Base64 Decoding *)

Definition base64dec_def:
    (* Base cases *)
    base64dec ([]: num list) = ([]: word8 list)
 /\ base64dec [n1; n2] = 
      b8_to_w8lst
    $ (11 >< 4)
    $ (concat_word_list
    $ (MAP n2w [n2; n1]: word6 list)): bool[12]
 /\ base64dec [n1; n2; n3] =
      b16_to_w8lst
    $ (17 >< 2)
    $ (concat_word_list
    $ (MAP n2w [n3; n2; n1]: word6 list)): bool[18]
    (* Recursive case *)
 /\ base64dec (n1::n2::n3::n4::ns) =
      (b24_to_w8lst
    $ (concat_word_list
    $ (MAP n2w [n4; n3; n2; n1]: word6 list)): bool[24]) ++ (base64dec ns)
End

(* RFC 4648 Test Vectors *)

EVAL ``base64dec $ base64depad "" = []``
EVAL ``base64dec $ base64depad "Zg==" = [0b01100110w]``
EVAL ``base64dec $ base64depad "Zm8=" = [0b01100110w; 0b01101111w]``
EVAL ``base64dec $ base64depad "Zm9v" = [0b01100110w; 0b01101111w; 0b01101111w]``
EVAL ``base64dec $ base64depad "Zm9vYg==" = [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w]``
EVAL ``base64dec $ base64depad "Zm9vYmE=" = [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w; 0b01100001w]``
EVAL ``base64dec $ base64depad "Zm9vYmFy" = [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w; 0b01100001w; 0b01110010w]``

EVAL ``base64pad $ base64enc [] = ""``
EVAL ``base64pad $ base64enc [0b01100110w] = "Zg=="``
EVAL ``base64pad $ base64enc [0b01100110w; 0b01101111w] = "Zm8="``
EVAL ``base64pad $ base64enc [0b01100110w; 0b01101111w; 0b01101111w] = "Zm9v"``
EVAL ``base64pad $ base64enc [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w] = "Zm9vYg=="``
EVAL ``base64pad $ base64enc [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w; 0b01100001w] = "Zm9vYmE="``
EVAL ``base64pad $ base64enc [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w; 0b01100001w; 0b01110010w] = "Zm9vYmFy"``


(* Theorems *)

(* Padding Theorems *)

Triviality ALL_DISTINCT_ALPH_BASE64: 
  ALL_DISTINCT ALPH_BASE64
Proof
  rw [ALPH_BASE64_DEF]
QED

Triviality STRLEN_ALPH_BASE64:
  STRLEN ALPH_BASE64 = 64
Proof
  rw [ALPH_BASE64_DEF]
QED

Triviality PAD_NOT_IN_ALPH_BASE64:
  !(n: num). n < LENGTH ALPH_BASE64 ==> alph_base64_el n <> #"="
Proof
  completeInduct_on `n`
  >> rw [alph_base64_el_def, ALPH_BASE64_DEF]
  >> ntac 32 $ EVERY [Cases_on `n`, rw [], Cases_on `n'`, rw []]
  >> fs []
QED

Theorem ALPH_BASE64_INDEX_EL:
  !n. n < STRLEN ALPH_BASE64 ==> alph_base64_index (alph_base64_el n) = n
Proof
  rw [alph_base64_el_def, alph_base64_index_def]
  >> ASSUME_TAC ALL_DISTINCT_ALPH_BASE64
  >> rw [ALL_DISTINCT_INDEX_OF_EL]
QED

Definition wf_base64_numlst_def:
  wf_base64_numlst (ns: num list) = 
    ((LENGTH ns MOD 4 <> 1)
 /\ !(n: num). (MEM n ns ==> n < LENGTH ALPH_BASE64))
End

Theorem BASE64_PAD_DEPAD_LENGTH0:
  !ns. LENGTH ns = 0 /\ wf_base64_numlst ns ==> base64depad (base64pad ns) = ns
Proof
  rw []
  >> rw [base64pad_def]
  >> rw [base64depad_def]
QED

Theorem BASE64_PAD_DEPAD_LENGTH2:
  !ns. LENGTH ns = 2 /\ wf_base64_numlst ns ==> base64depad (base64pad ns) = ns
Proof
  Cases_on `ns` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` 
  >> rw [base64pad_def]
  >> rw [base64depad_def]
  >> fs [wf_base64_numlst_def, ALPH_BASE64_INDEX_EL]
QED

Theorem BASE64_PAD_DEPAD_LENGTH3:
  !ns. LENGTH ns = 3 /\ wf_base64_numlst ns ==> base64depad (base64pad ns) = ns
Proof
  Cases_on `ns` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t`
  >> rw [base64pad_def]
  >> rw [base64depad_def]
  >- ( 
    fs [wf_base64_numlst_def]
    >> ASSUME_TAC PAD_NOT_IN_ALPH_BASE64
    >> METIS_TAC []
  )
  >> fs [wf_base64_numlst_def, ALPH_BASE64_INDEX_EL] 
QED

Theorem WF_BASE64_NUMLST_REC:
  !h1 h2 h3 h4 t. wf_base64_numlst (h1::h2::h3::h4::t) ==> wf_base64_numlst t
Proof
  rw [wf_base64_numlst_def, SUC_ONE_ADD]
QED


Triviality BASE64_PAD_EMPTY_STRING:
  !t. wf_base64_numlst t /\ base64pad t = "" ⇒ t = []
Proof
  SPOSE_NOT_THEN STRIP_ASSUME_TAC
  >> qmatch_asmsub_rename_tac `base64pad t`
  >> Cases_on `t`
  >> fs [Once base64pad_def, wf_base64_numlst_def]
  >> fs [AllCaseEqs()]
QED

Theorem BASE64_PAD_DEPAD:
  !ns. wf_base64_numlst ns ==> base64depad (base64pad ns) = ns
Proof
  gen_tac
  >> completeInduct_on `LENGTH ns`
  >> Cases_on `v < 4` >- (
    Cases_on `v = 0` >- rw [BASE64_PAD_DEPAD_LENGTH0] 
    >> Cases_on `v = 1` >- rw [wf_base64_numlst_def] 
    >> Cases_on `v = 2` >- rw [BASE64_PAD_DEPAD_LENGTH2] 
    >> Cases_on `v = 3` >- rw [BASE64_PAD_DEPAD_LENGTH3] 
    >> rw []
  ) >> (
    Cases_on `ns` >- rw []
    >> Cases_on `t` >- rw []
    >> Cases_on `t'` >- rw []
    >> Cases_on `t` >- rw []
    >> ONCE_REWRITE_TAC [base64pad_def] >> rw []
    >> ONCE_REWRITE_TAC [base64depad_def] >> rw []
    >- (
      ASSUME_TAC PAD_NOT_IN_ALPH_BASE64
      >> fs [wf_base64_numlst_def, STRLEN_ALPH_BASE64] 
      >> METIS_TAC []
    ) 
    >- (
      ASSUME_TAC PAD_NOT_IN_ALPH_BASE64
      >> fs [wf_base64_numlst_def, STRLEN_ALPH_BASE64] 
      >> METIS_TAC []
    )
    >> Cases_on `base64pad t'` >- (
      rw []
      >- fs [wf_base64_numlst_def, ALPH_BASE64_INDEX_EL]
      >- fs [wf_base64_numlst_def, ALPH_BASE64_INDEX_EL]
      >- fs [wf_base64_numlst_def, ALPH_BASE64_INDEX_EL]
      >- fs [wf_base64_numlst_def, ALPH_BASE64_INDEX_EL]
      >> ONCE_REWRITE_TAC [base64depad_def]
      >> rw []
      >> first_x_assum mp_tac
      >> Q.SPECL_THEN [`h`, `h'`, `h''`, `h'³'`, `t'`] MP_TAC WF_BASE64_NUMLST_REC
      >> rw [BASE64_PAD_EMPTY_STRING]
    )
    >> rw []
    >- fs [wf_base64_numlst_def, ALPH_BASE64_INDEX_EL]
    >- fs [wf_base64_numlst_def, ALPH_BASE64_INDEX_EL]
    >- fs [wf_base64_numlst_def, ALPH_BASE64_INDEX_EL]
    >- fs [wf_base64_numlst_def, ALPH_BASE64_INDEX_EL]
    >> first_x_assum (mp_tac o SYM)
    >> rw []
    >> Q.SPECL_THEN [`h`, `h'`, `h''`, `h'³'`, `t'`] MP_TAC WF_BASE64_NUMLST_REC
    >> rw []
  )
QED


Definition wf_base64_clst_def:
  wf_base64_clst (cs: char list) = 
    ((LENGTH cs MOD 4 = 0)
 /\ !(c: char). (c = #"=" \/ MEM c ALPH_BASE64)
 /\ (LENGTH (SUFFIX (λc. c = #"=") cs) <= 2))
End

Theorem ALPH_BASE64_EL_INDEX:
  !c. MEM c ALPH_BASE64 ==> alph_base64_el (alph_base64_index c) = c
Proof
  fs [ALPH_BASE64_DEF]
  >> gen_tac
  >> strip_tac
  >> rw [alph_base64_index_def, alph_base64_el_def]
  >> rw [ALPH_BASE64_DEF, INDEX_OF_def, INDEX_FIND_def]
QED

Theorem BASE64_DEPAD_PAD:
  !cs. wf_base64_clst cs ==> base64pad (base64depad cs) = cs
Proof
  gen_tac
  >> completeInduct_on `LENGTH cs`
  >> gen_tac
  >> Cases_on `v = 0` >- (
    ONCE_REWRITE_TAC [base64depad_def] >> rw [] >> rw [base64pad_def]
  )
  >> Cases_on `v = 4` >- (
    gvs [wf_base64_clst_def]
    >> Cases_on `cs` >- rw []
    >> Cases_on `t` >- rw []
    >> Cases_on `t'` >- rw []
    >> Cases_on `t` >- rw []
    >> Cases_on `t'` >- (
      rw [base64depad_def]
      >> rw [base64pad_def]
      >> rw [ALPH_BASE64_EL_INDEX]
      >> fs [rich_listTheory.SUFFIX_DEF]
      >> fs [COND]
      (* TODO: I need `h <> #"="` which is derivable here. *)
    ) >- rw []
    >> cheat 
  ) >> (
    (* Recursive case *)
    cheat
  ) 
QED

f "COND_"

(* En- and Decoding Theorems *)

Theorem BASE64_DEC_ENC_LENGTH1:
  !(ws: word8 list). LENGTH ws = 1 ==> base64dec (base64enc ws) = ws
Proof
  (* Trivial cases *)
  Cases_on `ws` >- rw []
  (* Main case *)
  >> rw [base64enc_def, b12_to_w6lst_def, b6_to_w6lst_def]
  >> rw [base64dec_def, b8_to_w8lst_def]
  >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
QED

Theorem BASE64_DEC_ENC_LENGTH2:
  !(ws: word8 list). LENGTH ws = 2 ==> base64dec (base64enc ws) = ws
Proof
  (* Trivial cases *)
  Cases_on `ws` >- rw []
  >> Cases_on `t` >- rw []
  (* Main case *)
  >> rw [base64enc_def, b18_to_w6lst_def, b12_to_w6lst_def, b6_to_w6lst_def]
  >> rw [base64dec_def, b16_to_w8lst_def, b8_to_w8lst_def]
  >> ntac 2 $ SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
QED

Theorem BASE64_DEC_ENC:
  !(ws: word8 list). base64dec (base64enc ws) = ws
Proof
  gen_tac
  >> completeInduct_on `LENGTH ws`
  >> Cases_on `v < 3` >- (
    (* Base cases *)
    Cases_on `v = 0` >- rw [base64enc_def, base64dec_def]
    >> Cases_on `v = 1` >- rw [BASE64_DEC_ENC_LENGTH1]
    >> Cases_on `v = 2` >- rw [BASE64_DEC_ENC_LENGTH2]
    >> rw []
  ) >> (
    (* Trivial cases *) 
    Cases_on `ws` >- rw [] 
    >> Cases_on `t` >- rw []
    >> Cases_on `t'` >- rw []
    (* Recursive case *)
    >> rw [base64enc_def]
    >> rw [b24_to_w6lst_def, b18_to_w6lst_def, b12_to_w6lst_def, b6_to_w6lst_def]
    >> rw [base64dec_def]
    >> rw [b24_to_w8lst_def, b16_to_w8lst_def, b8_to_w8lst_def]
    >> ntac 3 $ SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []  
  )
QED

Theorem BASE64_DEC_ENC_ID:
  base64dec o base64enc = I
Proof
  rw [FUN_EQ_THM, BASE64_DEC_ENC]
QED


Definition wf_base64_def:
  wf_base64 (ns: num list) = 
    (* Length *)
    ((LENGTH ns MOD 4 <> 1)
    (* Domain *)
 /\ !(n: num). (MEM n ns ==> n < LENGTH ALPH_BASE64)
    (* LSB Constraints *)
 /\ (LENGTH ns MOD 4 = 2 ==> ((3 >< 0) $ (n2w $ LAST ns): word6) = (0b0w: bool[4]))
 /\ (LENGTH ns MOD 4 = 3 ==> ((1 >< 0) $ (n2w $ LAST ns): word6) = (0b0w: bool[2])))
End

Triviality W6_SHIFT_4_LSB_MBZ:
 !(h: word6). (3 >< 0) h: bool[4] = 0w ==> (5 >< 4) h ≪ 4 = h
Proof 
  BBLAST_TAC
QED

Theorem BASE64_ENC_DEC_LENGTH2:
  !(ns: num list). LENGTH ns = 2 /\ wf_base64 ns ==> base64enc (base64dec ns) = ns
Proof
  Cases_on `ns` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'`
  >> rw []
  >> REWRITE_TAC [base64dec_def, b16_to_w8lst_def, b8_to_w8lst_def]
  >> REWRITE_TAC [base64enc_def, b18_to_w6lst_def, b12_to_w6lst_def, b6_to_w6lst_def]
  >> REWRITE_TAC [MAP, concat_word_list_def]
  >> SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []
  >> REWRITE_TAC [INST_TYPE [(``:'a`` |-> ``:6``)] w2n_n2w]
  >> first_x_assum mp_tac
  >> fs [wf_base64_def, STRLEN_ALPH_BASE64, W6_SHIFT_4_LSB_MBZ]
QED

Triviality W6_SHIFT_2_LSB_MBZ:
 !(h: word6). (1 >< 0) h: bool[2] = 0w ==> (5 >< 2) h ≪ 2 = h
Proof 
  BBLAST_TAC
QED

Theorem BASE64_ENC_DEC_LENGTH3:
  !(ns: num list). LENGTH ns = 3 /\ wf_base64 ns ==> base64enc (base64dec ns) = ns
Proof
  Cases_on `ns` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t`
  >> rw []
  >> REWRITE_TAC [base64dec_def, b16_to_w8lst_def, b8_to_w8lst_def]
  >> REWRITE_TAC [base64enc_def, b18_to_w6lst_def, b12_to_w6lst_def, b6_to_w6lst_def]
  >> REWRITE_TAC [MAP, concat_word_list_def]
  >> SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []
  >> REWRITE_TAC [INST_TYPE [(``:'a`` |-> ``:6``)] w2n_n2w]
  >> first_x_assum mp_tac
  >> fs [wf_base64_def, STRLEN_ALPH_BASE64, W6_SHIFT_2_LSB_MBZ]
QED

Theorem WF_BASE64_REC:
  !h1 h2 h3 h4 t. wf_base64 (h1::h2::h3::h4::t) ==> wf_base64 t
Proof
  rw [wf_base64_def, SUC_ONE_ADD]
  >> Cases_on `t` 
  >> fs [LAST_DEF]
QED

Theorem BASE64_ENC_DEC:
  !(ns: num list). wf_base64 ns ==> base64enc (base64dec ns) = ns
Proof
  gen_tac
  >> completeInduct_on `LENGTH ns` 
  >> Cases_on `v < 4` >- (
    (* Base cases *)
    Cases_on `v = 0` >- rw [base64dec_def, base64enc_def]
    >> Cases_on `v = 1` >- rw [wf_base64_def]
    >> Cases_on `v = 2` >- rw [BASE64_ENC_DEC_LENGTH2]
    >> Cases_on `v = 3` >- rw [BASE64_ENC_DEC_LENGTH3]
    >> rw []
  ) >> (
    (* Recursive case *)
    Cases_on `ns` >- rw [] 
    >> Cases_on `t` >- rw []
    >> Cases_on `t'` >- rw []
    >> Cases_on `t` >- rw []
    >> rw []
    >> REWRITE_TAC [base64dec_def, b24_to_w8lst_def, b16_to_w8lst_def, b8_to_w8lst_def]
    >> REWRITE_TAC [MAP, concat_word_list_def]
    >> SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []
    >> rw [GSYM rich_listTheory.CONS_APPEND]
    >> REWRITE_TAC [base64enc_def, b24_to_w6lst_def, b18_to_w6lst_def, b12_to_w6lst_def, b6_to_w6lst_def]
    >> REWRITE_TAC [MAP, concat_word_list_def]
    >> SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []
    >> rw [wordsTheory.w2n_n2w]
    >- fs [wf_base64_def, STRLEN_ALPH_BASE64]
    >- fs [wf_base64_def, STRLEN_ALPH_BASE64]
    >- fs [wf_base64_def, STRLEN_ALPH_BASE64]
    >- fs [wf_base64_def, STRLEN_ALPH_BASE64]
    >> Q.SPECL_THEN [`h`, `h'`, `h''`, `h'³'`, `t'`] MP_TAC WF_BASE64_REC
    >> fs []
  )
QED

Theorem BASE64_ENC_DEC_ID:
  !ns. wf_base64 ns ==> (base64enc o base64dec) ns = I ns
Proof
  rw [FUN_EQ_THM, BASE64_ENC_DEC]
QED

val _ = export_theory();
