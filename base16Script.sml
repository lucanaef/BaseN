open HolKernel Parse boolLib bossLib blastLib;
open listTheory rich_listTheory stringTheory arithmeticTheory wordsTheory wordsLib;
open baseNUtilsTheory;

val _ = new_theory "base16";

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

(*
EVAL ``MAP (λi. EL i ALPH_BASE16) $ base16enc [] = ""``
EVAL ``MAP (λi. EL i ALPH_BASE16) $ base16enc [0b11011110w; 0b10101101w; 0b10111110w; 0b11101111w] = "DEADBEEF"``
*)


(* Base16 Decoding *)

Definition base16dec_def:
    base16dec ([]: num list) = ([]: word8 list)
 /\ base16dec (n1::n2::ns) = 
      ((n2w n1: word4) @@ (n2w n2: word4))::(base16dec ns)
End

(*
EVAL ``base16dec $ MAP (λc. THE $ INDEX_OF c ALPH_BASE16) "" = []``
EVAL ``base16dec $ MAP (λc. THE $ INDEX_OF c ALPH_BASE16) "DEADBEEF" = [0b11011110w; 0b10101101w; 0b10111110w; 0b11101111w]``
*)


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
  >- rw [wf_base16_def]  
  >> rw [wf_base16_def]
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
    >> gvs [GSYM wf_base16_def]
  )
QED

Theorem BASE16_ENC_DEC_ID:
  !ns. wf_base16 ns ==> (base16enc o base16dec) ns = I ns
Proof
  rw [FUN_EQ_THM, BASE16_ENC_DEC]
QED


val _ = export_theory();