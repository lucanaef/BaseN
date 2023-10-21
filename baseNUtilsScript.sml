open HolKernel Parse boolLib bossLib wordsTheory wordsLib;

val _ = new_theory "baseNUtils";

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



val _ = export_theory();