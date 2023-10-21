open HolKernel Parse boolLib bossLib;
open listTheory rich_listTheory stringTheory arithmeticTheory wordsTheory wordsLib;
open baseNUtilsTheory;

val _ = new_theory "base16";

(* Base16 Alphabet *)

Definition ALPH_BASE16_DEF:
  ALPH_BASE16 = "0123456789ABCDEF"
End

(* Base16 Alphabet Lookup *)

Definition base16pad_def:
  base16pad ns = MAP (λi. EL i ALPH_BASE16) ns
End

Definition base16depad_def:
  base16depad cs = MAP (λc. THE $ INDEX_OF c ALPH_BASE16) cs
End

(* Base16 Encoding *)

Definition base16enc_def:
    base16enc ([]: word8 list) = ([]: num list)
 /\ base16enc (w::ws: word8 list) = 
      (w2n ((7 >< 4) w: word4))::(w2n ((3 >< 0) w: word4))::(base16enc ws)
End

(*
EVAL ``base16pad $ base16enc [] = ""``
EVAL ``base16pad $ base16enc [0b11011110w; 0b10101101w; 0b10111110w; 0b11101111w] = "DEADBEEF"``
*)


(* Base16 Decoding *)

Definition base16dec_def:
    base16dec ([]: num list) = ([]: word8 list)
 /\ base16dec (n1::n2::ns) = 
      ((n2w n1: word4) @@ (n2w n2: word4))::(base16dec ns)
End

(*
EVAL ``base16dec $ base16depad "" = []``
EVAL ``base16dec $ base16depad "DEADBEEF" = [0b11011110w; 0b10101101w; 0b10111110w; 0b11101111w]``
*)


(* Theorems *)

Definition wf_base16_ns_def:
  wf_base16_ns (ns: num list) = 
    !(n: num). (MEM n ns ==> n < LENGTH ALPH_BASE16)
End

Triviality WF_BASE16_NS_REC:
  !h t. wf_base16_ns (h::t) ==> wf_base16_ns t
Proof
  rw [wf_base16_ns_def, SUC_ONE_ADD]
QED

Triviality ALL_DISTINCT_ALPH_BASE16: 
  ALL_DISTINCT ALPH_BASE16
Proof
  rw [ALPH_BASE16_DEF]
QED

Theorem BASE16_PAD_DEPAD:
  !ns. wf_base16_ns ns ==> base16depad (base16pad ns) = ns
Proof
  gen_tac
  >> completeInduct_on `LENGTH ns`
  >> Cases_on `ns` >- (
    rw [Once base16pad_def, Once base16depad_def]
  ) >> (
    rw [Once base16pad_def, Once base16depad_def] 
    >- (
      fs [wf_base16_ns_def]
      >> ASSUME_TAC ALL_DISTINCT_ALPH_BASE16
      >> rw [ALL_DISTINCT_INDEX_OF_EL]
    ) >> (
      rw [GSYM $ Once base16depad_def]
      >> rw [GSYM $ Once base16pad_def]
      >> first_x_assum mp_tac
      >> Q.SPECL_THEN [`h`, `t`] MP_TAC WF_BASE16_NS_REC
      >> rw []
    )
  )
QED

Definition wf_base16_cs_def:
  wf_base16_cs (cs: char list) = 
    !(c: char). (MEM c cs ==> MEM c ALPH_BASE16)
End

Triviality WF_BASE16_CS_REC:
  !h t. wf_base16_cs (h::t) ==> wf_base16_cs t
Proof
  rw [wf_base16_cs_def, SUC_ONE_ADD]
QED

Theorem BASE16_DEPAD_PAD:
  !cs. wf_base16_cs cs ==> base16pad (base16depad cs) = cs
Proof
  gen_tac
  >> completeInduct_on `LENGTH cs`
  >> Cases_on `cs` >- (
    rw [Once base16pad_def, Once base16depad_def]
  ) >> (
    rw [Once base16pad_def, Once base16depad_def] >- ( 
      first_x_assum mp_tac
      >> rw [wf_base16_cs_def]
      >> first_x_assum $ Q.SPECL_THEN [`h`] MP_TAC
      >> rw []
      >> fs [ALPH_BASE16_DEF, INDEX_OF_def, INDEX_FIND_def]
    ) >> (
      rw [GSYM $ Once base16depad_def]
      >> rw [GSYM $ Once base16pad_def]
      >> first_x_assum mp_tac
      >> Q.SPECL_THEN [`h`, `t`] MP_TAC WF_BASE16_CS_REC
      >> rw []
    )
  )
QED

Theorem BASE16_DEC_ENC:
  !(ws: word8 list). base16dec (base16enc ws) = ws
Proof
  Induct_on `ws` >- (
    (* Base case *)
    rw [base16enc_def, base16dec_def]
  ) >> (
    (* Step case *)
    rw [base16enc_def, base16dec_def]
    >> Q.SPECL_THEN [`7`, `3`, `0`] MP_TAC $ INST_TYPE [(``:'a`` |-> ``:8``), (``:'b`` |-> ``:4``), (``:'c`` |-> ``:4``), (``:'d`` |-> ``:8``)] CONCAT_EXTRACT
    >> rw [EXTRACT_ALL_BITS]
  ) 
QED

Definition wf_base16_def:
  wf_base16 (ns: num list) = 
       (EVEN (LENGTH ns) /\ !(n: num). (MEM n ns ==> n < LENGTH ALPH_BASE16))
End

Triviality STRLEN_ALPH_BASE16:
  STRLEN ALPH_BASE16 = 16
Proof
  rw [ALPH_BASE16_DEF]
QED

Theorem BASE16_ENC_DEC:
  !(ns: num list). wf_base16 ns ==> base16enc (base16dec ns) = ns
Proof
  gen_tac
  >> completeInduct_on `LENGTH ns`
  >> gen_tac 
  >> Cases_on `ns` 
  >- rw [wf_base16_def, base16enc_def, base16dec_def]
  >> Cases_on `t` 
  >> rw [wf_base16_def]
  >> rw [base16enc_def, base16dec_def] >- (    
    Q.SPECL_THEN [`n2w h`, `n2w h'`] MP_TAC $ INST_TYPE [(``:'a`` |-> ``:4``), (``:'b`` |-> ``:4``), (``:'c`` |-> ``:8``)] EXTRACT_CONCAT
    >> rw []
    >> REWRITE_TAC [GSYM STRLEN_ALPH_BASE16]
    >> qpat_x_assum `!n. n = h \/ n = h' \/ MEM n t' ==> n < STRLEN ALPH_BASE16` $ irule_at Any
    >> rw []
  ) >- (
    Q.SPECL_THEN [`n2w h`, `n2w h'`] MP_TAC $ INST_TYPE [(``:'a`` |-> ``:4``), (``:'b`` |-> ``:4``), (``:'c`` |-> ``:8``)] EXTRACT_CONCAT
    >> rw []
    >> REWRITE_TAC [GSYM STRLEN_ALPH_BASE16]
    >> qpat_x_assum `!n. n = h \/ n = h' \/ MEM n t' ==> n < STRLEN ALPH_BASE16` $ irule_at Any
    >> rw []
  ) >> (
    qpat_x_assum `EVEN (SUC (SUC (LENGTH _)))` MP_TAC
    >> ONCE_REWRITE_TAC [EVEN]
    >> ONCE_REWRITE_TAC [GSYM ODD_EVEN]
    >> ONCE_REWRITE_TAC [ODD]
    >> ONCE_REWRITE_TAC [GSYM EVEN_ODD]
    >> qpat_x_assum `!n. n = h \/ n = h' \/ MEM n t' ==> n < STRLEN ALPH_BASE16` MP_TAC
    >> rw [DISJ_IMP_THM, FORALL_AND_THM]
    >> qpat_x_assum `!n. MEM n t' ==> n < STRLEN ALPH_BASE16` MP_TAC
    >> qpat_x_assum `EVEN (LENGTH t')` MP_TAC
    >> REWRITE_TAC [AND_IMP_INTRO]
    >> gvs [GSYM wf_base16_def]
  )
QED

val _ = export_theory();
