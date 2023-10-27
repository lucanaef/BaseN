open HolKernel Parse boolLib bossLib;
open listTheory rich_listTheory stringTheory arithmeticTheory wordsTheory wordsLib;
open baseNUtilsTheory;

val _ = new_theory "base64";

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
(*
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
*)


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

Definition wf_base64_ns_def:
  wf_base64_ns (ns: num list) = 
    ((LENGTH ns MOD 4 <> 1)
 /\ !(n: num). (MEM n ns ==> n < LENGTH ALPH_BASE64))
End

Triviality BASE64_PAD_DEPAD_LENGTH0:
  !ns. LENGTH ns = 0 /\ wf_base64_ns ns ==> base64depad (base64pad ns) = ns
Proof
  rw [Once base64pad_def, Once base64depad_def]
QED

Triviality BASE64_PAD_DEPAD_LENGTH2:
  !ns. LENGTH ns = 2 /\ wf_base64_ns ns ==> base64depad (base64pad ns) = ns
Proof
  Cases_on `ns` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` 
  >> rw [Once base64pad_def, Once base64depad_def]
  >> fs [wf_base64_ns_def, ALPH_BASE64_INDEX_EL]
QED

Triviality BASE64_PAD_DEPAD_LENGTH3:
  !ns. LENGTH ns = 3 /\ wf_base64_ns ns ==> base64depad (base64pad ns) = ns
Proof
  Cases_on `ns` >- rw []
  >> Cases_on `t` >- rw []
  >> Cases_on `t'` >- rw []
  >> Cases_on `t`
  >> rw [Once base64pad_def, Once base64depad_def]
  >- ( 
    fs [wf_base64_ns_def]
    >> ASSUME_TAC PAD_NOT_IN_ALPH_BASE64
    >> PROVE_TAC []
  )
  >> fs [wf_base64_ns_def, ALPH_BASE64_INDEX_EL] 
QED

Theorem WF_BASE64_NS_REC:
  !h1 h2 h3 h4 t. wf_base64_ns (h1::h2::h3::h4::t) ==> wf_base64_ns t
Proof
  rw [wf_base64_ns_def, SUC_ONE_ADD]
QED

Triviality BASE64_PAD_EMPTY_STRING:
  !t. wf_base64_ns t /\ base64pad t = "" ==> t = []
Proof
  SPOSE_NOT_THEN STRIP_ASSUME_TAC
  >> Cases_on `t`
  >> fs [Once base64pad_def, wf_base64_ns_def, AllCaseEqs()]
QED

Theorem BASE64_PAD_DEPAD:
  !ns. wf_base64_ns ns ==> base64depad (base64pad ns) = ns
Proof
  gen_tac
  >> completeInduct_on `LENGTH ns`
  >> Cases_on `v < 4` >- (
    Cases_on `v = 0` >- rw [BASE64_PAD_DEPAD_LENGTH0] 
    >> Cases_on `v = 1` >- rw [wf_base64_ns_def] 
    >> Cases_on `v = 2` >- rw [BASE64_PAD_DEPAD_LENGTH2] 
    >> Cases_on `v = 3` >- rw [BASE64_PAD_DEPAD_LENGTH3] 
    >> rw []
  ) >> (
    Cases_on `ns` >- rw []
    >> Cases_on `t` >- rw []
    >> Cases_on `t'` >- rw []
    >> Cases_on `t` >- rw []
    >> rw [Once base64pad_def, Once base64depad_def]
    >- (
      ASSUME_TAC PAD_NOT_IN_ALPH_BASE64
      >> fs [wf_base64_ns_def, STRLEN_ALPH_BASE64] 
      >> PROVE_TAC []
    ) 
    >- (
      ASSUME_TAC PAD_NOT_IN_ALPH_BASE64
      >> fs [wf_base64_ns_def, STRLEN_ALPH_BASE64] 
      >> PROVE_TAC []
    )
    >> Cases_on `base64pad t'` >- (
      rw []
      >>~- ([`alph_base64_index (alph_base64_el _) = _`],
        fs [wf_base64_ns_def, ALPH_BASE64_INDEX_EL]
      )
      >> ONCE_REWRITE_TAC [base64depad_def]
      >> rw []
      >> first_x_assum mp_tac
      >> Q.SPECL_THEN [`h`, `h'`, `h''`, `h'3'`, `t'`] MP_TAC WF_BASE64_NS_REC
      >> rw [BASE64_PAD_EMPTY_STRING]
    )
    >> rw []
    >>~- ([`alph_base64_index (alph_base64_el _) = _`],
      fs [wf_base64_ns_def, ALPH_BASE64_INDEX_EL]
    )
    >> first_x_assum (mp_tac o SYM)
    >> rw []
    >> Q.SPECL_THEN [`h`, `h'`, `h''`, `h'3'`, `t'`] MP_TAC WF_BASE64_NS_REC
    >> rw []
  )
QED

Definition wf_base64_cs_def:
  wf_base64_cs (cs: char list) = 
    ((LENGTH cs MOD 4 = 0)
 /\ (!(c: char). (MEM c cs ==> c = #"=" \/ MEM c ALPH_BASE64))
 /\ (~(MEM #"=" $ TAKE (LENGTH cs - 4) cs))
 /\ (LENGTH cs >= 4 ==> 
     (* Case [h1; h2; "="; "="] *)
     ((~(MEM #"=" $ TAKE 2 (LASTN 4 cs)) /\ EL 2 (LASTN 4 cs) = #"=" /\ EL 3 (LASTN 4 cs) = #"=")
     (* Case [h1; h2; h3; "="] *)
  \/ (~(MEM #"=" $ TAKE 3 (LASTN 4 cs)) /\ EL 3 (LASTN 4 cs) = #"=")
     (* Case [h1; h2; h3; h4] *)
  \/ (~(MEM #"=" $ LASTN 4 cs)))))
End

Theorem WF_BASE64_CS_REC:
  !h1 h2 h3 h4 t. wf_base64_cs (h1::h2::h3::h4::t) ==> wf_base64_cs t
Proof
  ntac 5 gen_tac
  >> Cases_on `LENGTH t < 4`
  >> fs [wf_base64_cs_def, SUC_ONE_ADD, LASTN_DROP_UNCOND]
QED

Theorem ALPH_BASE64_EL_INDEX:
  !c. MEM c ALPH_BASE64 ==> alph_base64_el (alph_base64_index c) = c
Proof
  fs [ALPH_BASE64_DEF]
  >> gen_tac
  >> strip_tac
  >> rw [alph_base64_index_def, alph_base64_el_def]
  >> rw [ALPH_BASE64_DEF, INDEX_OF_def, INDEX_FIND_def]
QED

Triviality BASE64_DEPAD_PAD_REC:
  ((!m. m < v ==> !cs. m = STRLEN cs ==> 
    wf_base64_cs cs ==> base64pad (base64depad cs) = cs)
  /\ v <> 0 /\ v <> 4)
  ==>
  (v = STRLEN cs ==> wf_base64_cs cs ==> base64pad (base64depad cs) = cs)
Proof
  rpt strip_tac 
  >> `LENGTH cs >= 8` by (
    fs [wf_base64_cs_def]
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
    >> Cases_on `t` >> fs []
  )
  >> Cases_on `cs` >- fs []
  >> Cases_on `t` >- fs []
  >> Cases_on `t'` >- fs []
  >> Cases_on `t` >- fs []
  >> Cases_on `t'` >- fs []
  >> rw [Once base64depad_def]
  >> rw [Once base64pad_def] 
  >- (
    fs [wf_base64_cs_def]
    >> qpat_x_assum `!c. _ \/ _ \/ _ \/ _ \/ _ \/ MEM c t ==> c = #"=" \/ MEM c ALPH_BASE64` $ Q.SPEC_THEN `h` MP_TAC
    >> fs [ALPH_BASE64_EL_INDEX]
  )
  >- (
    fs [wf_base64_cs_def]
    >> qpat_x_assum `!c. _ \/ _ \/ _ \/ _ \/ _ \/ MEM c t ==> c = #"=" \/ MEM c ALPH_BASE64` $ Q.SPEC_THEN `h'` MP_TAC
    >> gvs [ALPH_BASE64_EL_INDEX, SUC_ONE_ADD, LASTN, MEM]
  )
  >- (
    fs [wf_base64_cs_def]
    >> qpat_x_assum `!c. _ \/ _ \/ _ \/ _ \/ _ \/ MEM c t ==> c = #"=" \/ MEM c ALPH_BASE64` $ Q.SPEC_THEN `h''` MP_TAC
    >> gvs [ALPH_BASE64_EL_INDEX, SUC_ONE_ADD, LASTN, MEM]
  )
  >- (
    fs [wf_base64_cs_def]
    >> qpat_x_assum `!c. _ \/ _ \/ _ \/ _ \/ _ \/ MEM c t ==> c = #"=" \/ MEM c ALPH_BASE64` $ Q.SPEC_THEN `h'3'` MP_TAC
    >> gvs [ALPH_BASE64_EL_INDEX, SUC_ONE_ADD, LASTN, MEM]
  )
  >> first_x_assum $ match_mp_tac o MP_CANON
  >> csimp []
  >> drule_then irule WF_BASE64_CS_REC
QED

Theorem BASE64_DEPAD_PAD:
  !cs. wf_base64_cs cs ==> base64pad (base64depad cs) = cs
Proof
  gen_tac
  >> completeInduct_on `LENGTH cs`
  >> gen_tac
  >> Cases_on `v = 0` >- (
    ONCE_REWRITE_TAC [base64depad_def] >> rw [] >> rw [base64pad_def]
  )
  >> Cases_on `v = 4` >- ( 
    Cases_on `cs` >- rw []
    >> Cases_on `t` >- rw []
    >> Cases_on `t'` >- rw []
    >> Cases_on `t` >- rw []
    >> Cases_on `t'` >- (
      rw [base64depad_def]
      >> rw [base64pad_def]
      (* Case: [h; h'; "="; "="] *)
      >- (
        fs [wf_base64_cs_def]
        >> qpat_x_assum `!c. _ \/ _ \/ c = #"=" ==> c = #"=" \/ MEM c ALPH_BASE64` $ Q.SPEC_THEN `h` MP_TAC
        >> fs [LASTN_def] 
        >> rw [ALPH_BASE64_EL_INDEX]
      )
      >- (
        fs [wf_base64_cs_def]
        >> qpat_x_assum `!c. _ \/ _ \/ c = #"=" ==> c = #"=" \/ MEM c ALPH_BASE64` $ Q.SPEC_THEN `h'` MP_TAC
        >> fs [LASTN_def] 
        >> rw [ALPH_BASE64_EL_INDEX]
      )
      (* Case: [h; h'; h''; "="] *)
      >- (
        fs [wf_base64_cs_def]
        >> qpat_x_assum `!c. _ \/ _ \/ _ \/ c = #"=" ==> c = #"=" \/ MEM c ALPH_BASE64` $ Q.SPEC_THEN `h` MP_TAC
        >> fs [LASTN_def]
        >> rw [ALPH_BASE64_EL_INDEX]
      ) 
      >- (
        fs [wf_base64_cs_def]
        >> qpat_x_assum `!c. _ \/ _ \/ _ \/ c = #"=" ==> c = #"=" \/ MEM c ALPH_BASE64` $ Q.SPEC_THEN `h'` MP_TAC
        >> fs [LASTN_def]
        >> rw [ALPH_BASE64_EL_INDEX]
      )
      >- (
        fs [wf_base64_cs_def] 
        >> qpat_x_assum `!c. _ \/ _ \/ _ \/ c = #"=" ==> c = #"=" \/ MEM c ALPH_BASE64` $ Q.SPEC_THEN `h''` MP_TAC
        >> gvs [ALPH_BASE64_EL_INDEX]
        >> rw [ALPH_BASE64_EL_INDEX]
      )
      (* Case: [h; h'; h''; h'3'] *)
      >- (
        fs [wf_base64_cs_def]
        >> qpat_x_assum `!c. _ \/ _ \/ _ \/ _ ==> c = #"=" \/ MEM c ALPH_BASE64` $ Q.SPEC_THEN `h` MP_TAC
        >> fs [LASTN_def]
        >> rw [ALPH_BASE64_EL_INDEX]
      ) 
      >- (
        fs [wf_base64_cs_def]
        >> qpat_x_assum `!c. _ \/ _ \/ _ \/ _ ==> c = #"=" \/ MEM c ALPH_BASE64` $ Q.SPEC_THEN `h'` MP_TAC
        >> fs [LASTN_def]
        >> rw [ALPH_BASE64_EL_INDEX]
      )
      >- (
        fs [wf_base64_cs_def]
        >> qpat_x_assum `!c. _ \/ _ \/ _ \/ _ ==> c = #"=" \/ MEM c ALPH_BASE64` $ Q.SPEC_THEN `h''` MP_TAC
        >> fs [LASTN_def]
        >> rw [ALPH_BASE64_EL_INDEX]
      )
      >- (
        fs [wf_base64_cs_def]
        >> qpat_x_assum `!c. _ \/ _ \/ _ \/ _ ==> c = #"=" \/ MEM c ALPH_BASE64` $ Q.SPEC_THEN `h'3'` MP_TAC
        >> fs [LASTN_def]
        >> rw [ALPH_BASE64_EL_INDEX]
      ) 
    ) >- rw [] 
  ) >> (
    (* Recursive case *)
    ASSUME_TAC BASE64_DEPAD_PAD_REC >> simp [] 
  )
QED

(* En- and Decoding Theorems *)

Triviality BASE64_DEC_ENC_LENGTH1:
  !(ws: word8 list). LENGTH ws = 1 ==> base64dec (base64enc ws) = ws
Proof
  (* Trivial cases *)
  Cases_on `ws` >- rw []
  (* Main case *)
  >> rw [base64enc_def, b12_to_w6lst_def, b6_to_w6lst_def]
  >> rw [base64dec_def, b8_to_w8lst_def]
  >> SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []
QED

Triviality BASE64_DEC_ENC_LENGTH2:
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

Triviality BASE64_ENC_DEC_LENGTH2:
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

Triviality BASE64_ENC_DEC_LENGTH3:
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
    >> rw [GSYM CONS_APPEND]
    >> REWRITE_TAC [base64enc_def, b24_to_w6lst_def, b18_to_w6lst_def, b12_to_w6lst_def, b6_to_w6lst_def]
    >> REWRITE_TAC [MAP, concat_word_list_def]
    >> SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []
    >> rw [w2n_n2w]
    >- fs [wf_base64_def, STRLEN_ALPH_BASE64]
    >- fs [wf_base64_def, STRLEN_ALPH_BASE64]
    >- fs [wf_base64_def, STRLEN_ALPH_BASE64]
    >- fs [wf_base64_def, STRLEN_ALPH_BASE64]
    >> Q.SPECL_THEN [`h`, `h'`, `h''`, `h'3'`, `t'`] MP_TAC WF_BASE64_REC
    >> fs []
  )
QED

val _ = export_theory();
