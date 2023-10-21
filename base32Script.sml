open HolKernel Parse boolLib bossLib;
open listTheory rich_listTheory stringTheory arithmeticTheory wordsTheory wordsLib;
open baseNUtilsTheory;

val _ = new_theory "base32";

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
(*
EVAL ``base32pad $ base32enc [] = ""``
EVAL ``base32pad $ base32enc [0b01100110w] = "MY======"``
EVAL ``base32pad $ base32enc [0b01100110w; 0b01101111w] = "MZXQ===="``
EVAL ``base32pad $ base32enc [0b01100110w; 0b01101111w; 0b01101111w] = "MZXW6==="``
EVAL ``base32pad $ base32enc [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w] = "MZXW6YQ="``
EVAL ``base32pad $ base32enc [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w; 0b01100001w] = "MZXW6YTB"``
EVAL ``base32pad $ base32enc [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w; 0b01100001w; 0b01110010w] = "MZXW6YTBOI======"``
*)


(* Base32 Decoding *)

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
(*
EVAL ``base32dec $ base32depad "" = []``
EVAL ``base32dec $ base32depad "MY======" = [0b01100110w]``
EVAL ``base32dec $ base32depad "MZXQ====" = [0b01100110w; 0b01101111w]``
EVAL ``base32dec $ base32depad "MZXW6===" = [0b01100110w; 0b01101111w; 0b01101111w]``
EVAL ``base32dec $ base32depad "MZXW6YQ=" = [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w]``
EVAL ``base32dec $ base32depad "MZXW6YTB" = [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w; 0b01100001w]``
EVAL ``base32dec $ base32depad "MZXW6YTBOI======" = [0b01100110w; 0b01101111w; 0b01101111w; 0b01100010w; 0b01100001w; 0b01110010w]``
*)


(* Theorems *)

(* Padding Theorems *)

Triviality ALL_DISTINCT_ALPH_BASE32: 
  ALL_DISTINCT ALPH_BASE32
Proof
  rw [ALPH_BASE32_DEF]
QED

Triviality STRLEN_ALPH_BASE32:
  STRLEN ALPH_BASE32 = 32
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

Theorem ALPH_BASE32_EL_INDEX:
  !c. MEM c ALPH_BASE32 ==> alph_base32_el (alph_base32_index c) = c
Proof
  fs [ALPH_BASE32_DEF]
  >> gen_tac
  >> strip_tac
  >> rw [alph_base32_index_def, alph_base32_el_def]
  >> rw [ALPH_BASE32_DEF, INDEX_OF_def, INDEX_FIND_def]
QED

Theorem ALPH_BASE32_INDEX_EL:
  !n. n < STRLEN ALPH_BASE32 ==> alph_base32_index (alph_base32_el n) = n
Proof
  rw [alph_base32_el_def, alph_base32_index_def]
  >> ASSUME_TAC ALL_DISTINCT_ALPH_BASE32 
  >> rw [ALL_DISTINCT_INDEX_OF_EL]
QED

Definition wf_base32_cs_def:
  wf_base32_cs (cs: char list) = 
    ((LENGTH cs MOD 8 = 0)
 /\ (!(c: char). (c = #"=" \/ MEM c ALPH_BASE32))
 /\ (~(MEM #"=" $ TAKE (LENGTH cs - 8) cs))
 /\ (LENGTH cs >= 8 ==> 
       (* Case (c1::c2::"======") *)
     ((~(MEM #"=" $ TAKE 2 (LASTN 8 cs)) 
       /\ EL 2 (LASTN 8 cs) = #"=" /\ EL 3 (LASTN 8 cs) = #"=" 
       /\ EL 4 (LASTN 8 cs) = #"=" /\ EL 5 (LASTN 8 cs) = #"=" 
       /\ EL 6 (LASTN 8 cs) = #"=" /\ EL 7 (LASTN 8 cs) = #"=")
      (* Case (c1::c2::c3::c4::"====") *)
   \/ (~(MEM #"=" $ TAKE 4 (LASTN 8 cs)) 
       /\ EL 4 (LASTN 8 cs) = #"=" /\ EL 5 (LASTN 8 cs) = #"=" 
       /\ EL 6 (LASTN 8 cs) = #"=" /\ EL 7 (LASTN 8 cs) = #"=")
      (* Case (c1::c2::c3::c4::c5::"===") *)
   \/ (~(MEM #"=" $ TAKE 5 (LASTN 8 cs)) 
       /\ EL 5 (LASTN 8 cs) = #"=" /\ EL 6 (LASTN 8 cs) = #"=" 
       /\ EL 7 (LASTN 8 cs) = #"=")
      (* Case (c1::c2::c3::c4::c5::c6::c7::"=") *)
   \/ (~(MEM #"=" $ TAKE 7 (LASTN 8 cs)) /\ EL 7 (LASTN 8 cs) = #"=")
      (* Case (c1::c2::c3::c4::c5::c6::c7::c8)*)
   \/ (~(MEM #"=" $ LASTN 8 cs)))))
End

Theorem WF_BASE32_CS_REC:
  !h1 h2 h3 h4 h5 h6 h7 h8 t. wf_base32_cs (h1::h2::h3::h4::h5::h6::h7::h8::t) ==> wf_base32_cs t
Proof
  ntac 9 gen_tac
  >> Cases_on `LENGTH t < 8`
  >> gs [wf_base32_cs_def, SUC_ONE_ADD, LASTN_DROP_UNCOND]
QED

Triviality BASE32_DEPAD_PAD_REC:
  ((!m. m < v ==> !cs. m = STRLEN cs ==> 
    wf_base32_cs cs ==> base32pad (base32depad cs) = cs)
  /\ v <> 0 /\ v <> 8)
  ==>
  (v = STRLEN cs ==> wf_base32_cs cs ==> base32pad (base32depad cs) = cs)
Proof
  rpt strip_tac
  >> `LENGTH cs >= 16` by (
    fs [wf_base32_cs_def]
    >> ntac 3 $ WEAKEN_TAC (fn f => true)
    >> first_x_assum mp_tac
    >> WEAKEN_TAC (fn f => true)
    >> ntac 2 $ first_x_assum mp_tac
    >> WEAKEN_TAC (fn f => true)
    >> rw []
    >> Cases_on `cs` >- fs []
    >> Cases_on `t` >- fs []
    >> Cases_on `t'` >- fs []
    >> Cases_on `t` >- fs []
    >> Cases_on `t'` >- fs []
    >> Cases_on `t` >- fs []
    >> Cases_on `t'` >- fs []
    >> Cases_on `t` >- fs []
    >> Cases_on `t'` >- fs []
    >> Cases_on `t` >- fs []
    >> Cases_on `t'` >- fs []
    >> Cases_on `t` >- fs []
    >> Cases_on `t'` >- fs []
    >> Cases_on `t` >- fs []
    >> Cases_on `t'` >- fs []
    >> Cases_on `t` >> fs []
  )
  >> Cases_on `cs` >- fs []
  >> Cases_on `t` >- fs []
  >> Cases_on `t'` >- fs []
  >> Cases_on `t` >- fs []
  >> Cases_on `t'` >- fs []
  >> Cases_on `t` >- fs []
  >> Cases_on `t'` >- fs []
  >> Cases_on `t` >- fs []
  >> Cases_on `t'` >- fs []
  >> rw [Once base32depad_def]
  >> rw [Once base32pad_def]
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h` MP_TAC
    >> fs [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'` MP_TAC
    >> gs [ALPH_BASE32_EL_INDEX, SUC_ONE_ADD, LASTN, MEM]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h''` MP_TAC
    >> gs [ALPH_BASE32_EL_INDEX, SUC_ONE_ADD, LASTN, MEM]
  ) 
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'3'` MP_TAC
    >> gs [ALPH_BASE32_EL_INDEX, SUC_ONE_ADD, LASTN, MEM]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'4'` MP_TAC
    >> gs [ALPH_BASE32_EL_INDEX, SUC_ONE_ADD, LASTN, MEM]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'5'` MP_TAC
    >> gs [ALPH_BASE32_EL_INDEX, SUC_ONE_ADD, LASTN, MEM]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'6'` MP_TAC
    >> gs [ALPH_BASE32_EL_INDEX, SUC_ONE_ADD, LASTN, MEM]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'7'` MP_TAC
    >> gs [ALPH_BASE32_EL_INDEX, SUC_ONE_ADD, LASTN, MEM]
  )
  >> first_x_assum $ match_mp_tac o MP_CANON
  >> csimp []
  >> drule_then irule WF_BASE32_CS_REC
QED

Triviality BASE32_DEPAD_PAD_LENGTH2:
  wf_base32_cs (STRING h (STRING h' "======"))
  ==>
  base32pad [alph_base32_index h; alph_base32_index h'] = STRING h (STRING h' "======")
Proof
  rw [base32pad_def]
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
QED

Triviality BASE32_DEPAD_PAD_LENGTH3:
  wf_base32_cs (STRING h (STRING h' (STRING h'' "====="))) /\ h'' <> #"="
  ==>
  base32pad [alph_base32_index h; alph_base32_index h'; alph_base32_index h''; alph_base32_index #"="] 
   = STRING h (STRING h' (STRING h'' "====="))
Proof
  rw [base32pad_def]
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h''` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- fs [wf_base32_cs_def, LASTN_def, ALPH_BASE32_EL_INDEX]
QED

Triviality BASE32_DEPAD_PAD_LENGTH4:
  wf_base32_cs (STRING h (STRING h' (STRING h'' (STRING h'3' "====")))) /\ h'3' <> #"="
  ==>
  base32pad [alph_base32_index h; alph_base32_index h'; alph_base32_index h''; alph_base32_index h'3'] 
   = STRING h (STRING h' (STRING h'' (STRING h'3' "====")))
Proof
  rw [base32pad_def]
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h''` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'3'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
QED

Triviality BASE32_DEPAD_PAD_LENGTH5:
  wf_base32_cs (STRING h (STRING h' (STRING h'' (STRING h'3' (STRING h'4' "==="))))) /\ h'4' <> #"="
  ==>
  base32pad [alph_base32_index h; alph_base32_index h'; alph_base32_index h''; alph_base32_index h'3'; alph_base32_index h'4'] 
   = STRING h (STRING h' (STRING h'' (STRING h'3' (STRING h'4' "==="))))
Proof
  rw [base32pad_def]
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h''` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'3'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'4'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
QED

Triviality BASE32_DEPAD_PAD_LENGTH6:
  wf_base32_cs (STRING h (STRING h' (STRING h'' (STRING h'3' (STRING h'4' (STRING h'5' "==")))))) /\ h'5' <> #"="
  ==>
  base32pad [alph_base32_index h; alph_base32_index h'; alph_base32_index h''; alph_base32_index h'3'; alph_base32_index h'4'; alph_base32_index h'5'; alph_base32_index #"="]
   = STRING h (STRING h' (STRING h'' (STRING h'3' (STRING h'4' (STRING h'5' "==")))))
Proof
  rw [base32pad_def]
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h''` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'3'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'4'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'5'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- fs [wf_base32_cs_def, LASTN_def, ALPH_BASE32_EL_INDEX]
QED

Triviality BASE32_DEPAD_PAD_LENGTH7:
  wf_base32_cs (STRING h (STRING h' (STRING h'' (STRING h'3' (STRING h'4' (STRING h'5' (STRING h'6' "="))))))) /\ h'6' <> #"="
  ==>
  base32pad [alph_base32_index h; alph_base32_index h'; alph_base32_index h''; alph_base32_index h'3'; alph_base32_index h'4'; alph_base32_index h'5'; alph_base32_index h'6'] 
   = STRING h (STRING h' (STRING h'' (STRING h'3' (STRING h'4' (STRING h'5' (STRING h'6' "="))))))
Proof
  rw [base32pad_def]
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h''` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'3'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'4'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'5'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'6'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
QED

Triviality BASE32_DEPAD_PAD_LENGTH8:
  wf_base32_cs (STRING h (STRING h' (STRING h'' (STRING h'3' (STRING h'4' (STRING h'5' (STRING h'6' (STRING h'7' "")))))))) /\ h'7' <> #"="
  ==>
  base32pad [alph_base32_index h; alph_base32_index h'; alph_base32_index h''; alph_base32_index h'3'; alph_base32_index h'4'; alph_base32_index h'5'; alph_base32_index h'6'; alph_base32_index h'7'] 
   = STRING h (STRING h' (STRING h'' (STRING h'3' (STRING h'4' (STRING h'5' (STRING h'6' (STRING h'7' "")))))))
Proof
  rw [base32pad_def]
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h''` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'3'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'4'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'5'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'6'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
  >- (
    fs [wf_base32_cs_def]
    >> qpat_x_assum `!c. c = #"=" \/ MEM c ALPH_BASE32` $ Q.SPEC_THEN `h'7'` MP_TAC
    >> fs [LASTN_def] 
    >> rw [ALPH_BASE32_EL_INDEX]
  )
QED

Theorem BASE32_DEPAD_PAD:
  !cs. wf_base32_cs cs ==> base32pad (base32depad cs) = cs
Proof
  gen_tac
  >> completeInduct_on `LENGTH cs`
  >> gen_tac
  >> Cases_on `v = 0` >- (
    rw [Once base32depad_def] >> rw [base32pad_def]
  ) >> Cases_on `v = 8` >- (
    Cases_on `cs` >- rw []
    >> Cases_on `t` >- rw []
    >> Cases_on `t'` >- rw []
    >> Cases_on `t` >- rw []
    >> Cases_on `t'` >- rw []
    >> Cases_on `t` >- rw []
    >> Cases_on `t'` >- rw []
    >> Cases_on `t` >- rw []
    >> Cases_on `t'` >- (
      rw [base32depad_def]
      (* Case: [h; h'; "="; "="; "="; "="; "="; "="] *)
      >- fs [BASE32_DEPAD_PAD_LENGTH2]
      (* Case: [h; h'; h''; "="; "="; "="; "="; "="] *)
      >- fs [BASE32_DEPAD_PAD_LENGTH3] 
      (* Case: [h; h'; h''; h'3'; "="; "="; "="; "="] *)
      >- fs [BASE32_DEPAD_PAD_LENGTH4] 
      (* Case: [h; h'; h''; h'3'; h'4'; "="; "="; "="] *)
      >- fs [BASE32_DEPAD_PAD_LENGTH5] 
      (* Case: [h; h'; h''; h'3'; h'4'; h'5'; "="; "="] *)
      >- fs [BASE32_DEPAD_PAD_LENGTH6]
      (* Case: [h; h'; h''; h'3'; h'4'; h'5'; h'6'; "="] *)
      >- fs [BASE32_DEPAD_PAD_LENGTH7]
      (* Case: [h; h'; h''; h'3'; h'4'; h'5'; h'6'; h'7'] *)
      >- fs [BASE32_DEPAD_PAD_LENGTH8] 
    ) 
    >- rw []
  ) 
  >> (
    (* Recursive case *)
    ASSUME_TAC BASE32_DEPAD_PAD_REC >> simp []  
  )
QED

Definition wf_base32_ns_def:
  wf_base32_ns (ns: num list) = 
    (MEM (LENGTH ns MOD 8) [0; 2; 5; 7] 
  /\ !(n: num). (MEM n ns ==> n < LENGTH ALPH_BASE32))
End

Theorem WF_BASE32_NS_REC:
  !h1 h2 h3 h4 h5 h6 h7 h8 t. wf_base32_ns (h1::h2::h3::h4::h5::h6::h7::h8::t) ==> wf_base32_ns t
Proof
  rw [wf_base32_ns_def, SUC_ONE_ADD]
QED

Triviality BASE32_PAD_DEPAD_LENGTH0:
  !ns. LENGTH ns = 0 /\ wf_base32_ns ns ==> base32depad (base32pad ns) = ns
Proof
  rw [Once base32pad_def, Once base32depad_def]
QED

Triviality BASE32_PAD_DEPAD_LENGTH2:
  !ns. LENGTH ns = 2 /\ wf_base32_ns ns ==> base32depad (base32pad ns) = ns
Proof
  Cases_on `ns` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'`
  >> rw [wf_base32_ns_def, Once base32pad_def, Once base32depad_def, ALPH_BASE32_INDEX_EL]
QED

Triviality BASE32_PAD_DEPAD_LENGTH5:
  !ns. LENGTH ns = 5 /\ wf_base32_ns ns ==> base32depad (base32pad ns) = ns
Proof
  Cases_on `ns` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t`
  >> rw [wf_base32_ns_def, Once base32pad_def, Once base32depad_def, ALPH_BASE32_INDEX_EL]
  >> ASSUME_TAC PAD_NOT_IN_ALPH_BASE32
  >> fs [wf_base32_ns_def]
  >> PROVE_TAC []
QED

Triviality BASE32_PAD_DEPAD_LENGTH7:
  !ns. LENGTH ns = 7 /\ wf_base32_ns ns ==> base32depad (base32pad ns) = ns
Proof
  Cases_on `ns` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t`
  >> rw [wf_base32_ns_def, Once base32pad_def, Once base32depad_def, ALPH_BASE32_INDEX_EL]
  >> ASSUME_TAC PAD_NOT_IN_ALPH_BASE32
  >> fs [wf_base32_ns_def]
  >> PROVE_TAC []
QED

Triviality BASE32_PAD_EMPTY_STRING:
  !t. wf_base32_ns t /\ base32pad t = "" ==> t = []
Proof
  SPOSE_NOT_THEN STRIP_ASSUME_TAC
  >> Cases_on `t`
  >> ntac 2 $ fs [Once base32pad_def, wf_base32_ns_def, AllCaseEqs()]
QED

Theorem BASE32_PAD_DEPAD:
  !ns. wf_base32_ns ns ==> base32depad (base32pad ns) = ns
Proof
  gen_tac 
  >> completeInduct_on `LENGTH ns` 
  >> Cases_on `v < 8` >- (
  (* Base cases *)
    Cases_on `v = 0` >- rw [BASE32_PAD_DEPAD_LENGTH0]
    >> Cases_on `v = 1` >- rw [wf_base32_ns_def]
    >> Cases_on `v = 2` >- rw [BASE32_PAD_DEPAD_LENGTH2]
    >> Cases_on `v = 3` >- rw [wf_base32_ns_def] 
    >> Cases_on `v = 4` >- rw [wf_base32_ns_def] 
    >> Cases_on `v = 5` >- rw [BASE32_PAD_DEPAD_LENGTH5] 
    >> Cases_on `v = 6` >- rw [wf_base32_ns_def]
    >> Cases_on `v = 7` >- rw [BASE32_PAD_DEPAD_LENGTH7]
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
    >> rw [Once base32pad_def]
    >> rw [Once base32depad_def]
    >- (
      ASSUME_TAC PAD_NOT_IN_ALPH_BASE32
      >> fs [wf_base32_ns_def, STRLEN_ALPH_BASE32] 
      >> PROVE_TAC []
    )
    >- (
      ASSUME_TAC PAD_NOT_IN_ALPH_BASE32
      >> fs [wf_base32_ns_def, STRLEN_ALPH_BASE32] 
      >> PROVE_TAC []
    )
    >- (
      ASSUME_TAC PAD_NOT_IN_ALPH_BASE32
      >> fs [wf_base32_ns_def, STRLEN_ALPH_BASE32] 
      >> PROVE_TAC []
    )
    >- (
      ASSUME_TAC PAD_NOT_IN_ALPH_BASE32
      >> fs [wf_base32_ns_def, STRLEN_ALPH_BASE32] 
      >> PROVE_TAC []
    )
    >- (
      ASSUME_TAC PAD_NOT_IN_ALPH_BASE32
      >> fs [wf_base32_ns_def, STRLEN_ALPH_BASE32] 
      >> PROVE_TAC []
    )
    >- (
      ASSUME_TAC PAD_NOT_IN_ALPH_BASE32
      >> fs [wf_base32_ns_def, STRLEN_ALPH_BASE32] 
      >> PROVE_TAC []
    )
    >> Cases_on `base32pad t'` >- (
        rw []
        >- fs [wf_base32_ns_def, ALPH_BASE32_INDEX_EL]
        >- fs [wf_base32_ns_def, ALPH_BASE32_INDEX_EL]
        >- fs [wf_base32_ns_def, ALPH_BASE32_INDEX_EL]
        >- fs [wf_base32_ns_def, ALPH_BASE32_INDEX_EL]
        >- fs [wf_base32_ns_def, ALPH_BASE32_INDEX_EL]
        >- fs [wf_base32_ns_def, ALPH_BASE32_INDEX_EL]
        >- fs [wf_base32_ns_def, ALPH_BASE32_INDEX_EL]
        >- fs [wf_base32_ns_def, ALPH_BASE32_INDEX_EL]
        >> ONCE_REWRITE_TAC [base32depad_def]
        >> rw []
        >> first_x_assum mp_tac
        >> Q.SPECL_THEN [`h`, `h'`, `h''`, `h'3'`, `h'4'`, `h'5'`, `h'6'`, `h'7'`, `t'`] MP_TAC WF_BASE32_NS_REC
        >> rw [BASE32_PAD_EMPTY_STRING]
    ) >> (
      rw []
      >- fs [wf_base32_ns_def, ALPH_BASE32_INDEX_EL]
      >- fs [wf_base32_ns_def, ALPH_BASE32_INDEX_EL]
      >- fs [wf_base32_ns_def, ALPH_BASE32_INDEX_EL]
      >- fs [wf_base32_ns_def, ALPH_BASE32_INDEX_EL]
      >- fs [wf_base32_ns_def, ALPH_BASE32_INDEX_EL]
      >- fs [wf_base32_ns_def, ALPH_BASE32_INDEX_EL]
      >- fs [wf_base32_ns_def, ALPH_BASE32_INDEX_EL]
      >- fs [wf_base32_ns_def, ALPH_BASE32_INDEX_EL]
      >> first_x_assum (mp_tac o SYM)
      >> rw []
      >> Q.SPECL_THEN [`h`, `h'`, `h''`, `h'3'`, `h'4'`, `h'5'`, `h'6'`, `h'7'`, `t'`] MP_TAC WF_BASE32_NS_REC
      >> rw []
    )
  )
QED


(* En- and Decoding Theorems *)

Triviality BASE32_DEC_ENC_LENGTH1:
  !(ws: word8 list). LENGTH ws = 1 ==> base32dec (base32enc ws) = ws
Proof
  Cases_on `ws` 
  >> rw [base32enc_def, b10_to_w5lst_def]
  >> rw [base32dec_def, b8_to_w8lst_def]
  >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
QED

Triviality BASE32_DEC_ENC_LENGTH2:
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

Triviality BASE32_DEC_ENC_LENGTH3:
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

Triviality BASE32_DEC_ENC_LENGTH4:
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
  >> rw [base32dec_def, b32_to_w8lst_def] 
  >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
  >> rw [b24_to_w8lst_def] 
  >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
  >> rw [b16_to_w8lst_def]
  >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
  >> rw [b8_to_w8lst_def] 
  >> ntac 2 $ SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [] 
  >> rw []
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
    >> rw [b40_to_w8lst_def] 
    >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
    >> rw [b32_to_w8lst_def]
    >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
    >> rw [b24_to_w8lst_def] 
    >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
    >> rw [b16_to_w8lst_def] 
    >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
    >> rw [b8_to_w8lst_def] 
    >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
  )
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

Triviality BASE32_ENC_DEC_LENGTH2:
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

Triviality BASE32_ENC_DEC_LENGTH4:
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

Triviality BASE32_ENC_DEC_LENGTH5:
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

Triviality BASE32_ENC_DEC_LENGTH7:
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
    >> rw [GSYM CONS_APPEND]
    >> REWRITE_TAC [base32enc_def, b40_to_w5lst_def, b20_to_w5lst_def, b10_to_w5lst_def]
    >> REWRITE_TAC [MAP, concat_word_list_def]
    >> SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []
    >> rw [w2n_n2w]
    >- fs [wf_base32_def, STRLEN_ALPH_BASE32]
    >- fs [wf_base32_def, STRLEN_ALPH_BASE32]
    >- fs [wf_base32_def, STRLEN_ALPH_BASE32]
    >- fs [wf_base32_def, STRLEN_ALPH_BASE32]
    >- fs [wf_base32_def, STRLEN_ALPH_BASE32]
    >- fs [wf_base32_def, STRLEN_ALPH_BASE32]
    >- fs [wf_base32_def, STRLEN_ALPH_BASE32]
    >- fs [wf_base32_def, STRLEN_ALPH_BASE32]
    >> Q.SPECL_THEN [`h`, `h'`, `h''`, `h'3'`, `h'4'`, `h'5'`, `h'6'`, `h'7'`, `t'`] MP_TAC WF_BASE32_REC
    >> fs []
  )
QED

val _ = export_theory();
