/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseTwo.Lower.MatrixBridge.Data

@[expose] public section
set_option linter.style.longLine false
set_option maxRecDepth 4096

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseTwo.Lower.MatrixBridge

@[simp] theorem lookup_literalQ_0_0 : literalQ (0, 0) (0, 0) = (-13693331 / 100000000) := rfl
@[simp] theorem lookup_literalQ_0_1 : literalQ (0, 0) (0, 1) = (-43259 / 200000000) := rfl
@[simp] theorem lookup_literalQ_0_2 : literalQ (0, 0) (1, 0) = (13693331 / 200000000) := rfl
@[simp] theorem lookup_literalQ_0_3 : literalQ (0, 0) (1, 1) = (-57549969 / 500000000) := rfl
@[simp] theorem lookup_literalQ_0_4 : literalQ (0, 0) (2, 0) = (21505073 / 200000000) := rfl
@[simp] theorem lookup_literalQ_0_5 : literalQ (0, 0) (2, 1) = (-108827863 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_0_6 : literalQ (0, 0) (3, 0) = (-1806891 / 40000000) := rfl
@[simp] theorem lookup_literalQ_0_7 : literalQ (0, 0) (3, 1) = (-24982541 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_0_8 : literalQ (0, 0) (4, 0) = (-85743 / 100000000) := rfl
@[simp] theorem lookup_literalQ_0_9 : literalQ (0, 0) (4, 1) = (21255567 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_0_10 : literalQ (0, 0) (5, 0) = (146951 / 50000000) := rfl
@[simp] theorem lookup_literalQ_0_11 : literalQ (0, 0) (5, 1) = (-1514481 / 400000000) := rfl
@[simp] theorem lookup_literalQ_0_12 : literalQ (0, 0) (6, 0) = (433859 / 200000000) := rfl
@[simp] theorem lookup_literalQ_0_13 : literalQ (0, 0) (6, 1) = (7399869 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_0_14 : literalQ (0, 0) (7, 0) = (-113631 / 50000000) := rfl
@[simp] theorem lookup_literalQ_0_15 : literalQ (0, 0) (7, 1) = (-1306329 / 400000000) := rfl
@[simp] theorem lookup_literalQ_1_0 : literalQ (0, 1) (0, 0) = (-43259 / 200000000) := rfl
@[simp] theorem lookup_literalQ_1_1 : literalQ (0, 1) (0, 1) = (-13683331 / 100000000) := rfl
@[simp] theorem lookup_literalQ_1_2 : literalQ (0, 1) (1, 0) = (2217919 / 40000000) := rfl
@[simp] theorem lookup_literalQ_1_3 : literalQ (0, 1) (1, 1) = (40879993 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_1_4 : literalQ (0, 1) (2, 0) = (-2407533 / 200000000) := rfl
@[simp] theorem lookup_literalQ_1_5 : literalQ (0, 1) (2, 1) = (21505073 / 200000000) := rfl
@[simp] theorem lookup_literalQ_1_6 : literalQ (0, 1) (3, 0) = (-1129307 / 25000000) := rfl
@[simp] theorem lookup_literalQ_1_7 : literalQ (0, 1) (3, 1) = (-12491257 / 1000000000) := rfl
@[simp] theorem lookup_literalQ_1_8 : literalQ (0, 1) (4, 0) = (-85743 / 100000000) := rfl
@[simp] theorem lookup_literalQ_1_9 : literalQ (0, 1) (4, 1) = (21255591 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_1_10 : literalQ (0, 1) (5, 0) = (146951 / 50000000) := rfl
@[simp] theorem lookup_literalQ_1_11 : literalQ (0, 1) (5, 1) = (-739871 / 250000000) := rfl
@[simp] theorem lookup_literalQ_1_12 : literalQ (0, 1) (6, 0) = (433859 / 200000000) := rfl
@[simp] theorem lookup_literalQ_1_13 : literalQ (0, 1) (6, 1) = (89571 / 12500000) := rfl
@[simp] theorem lookup_literalQ_1_14 : literalQ (0, 1) (7, 0) = (-113631 / 50000000) := rfl
@[simp] theorem lookup_literalQ_1_15 : literalQ (0, 1) (7, 1) = (-1244891 / 1000000000) := rfl
@[simp] theorem lookup_literalQ_2_0 : literalQ (1, 0) (0, 0) = (13693331 / 200000000) := rfl
@[simp] theorem lookup_literalQ_2_1 : literalQ (1, 0) (0, 1) = (2217919 / 40000000) := rfl
@[simp] theorem lookup_literalQ_2_2 : literalQ (1, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_2_3 : literalQ (1, 0) (1, 1) = (76881057 / 500000000) := rfl
@[simp] theorem lookup_literalQ_2_4 : literalQ (1, 0) (2, 0) = (-2223883 / 40000000) := rfl
@[simp] theorem lookup_literalQ_2_5 : literalQ (1, 0) (2, 1) = (212684433 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_2_6 : literalQ (1, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_2_7 : literalQ (1, 0) (3, 1) = (2223883 / 40000000) := rfl
@[simp] theorem lookup_literalQ_2_8 : literalQ (1, 0) (4, 0) = (-1179711 / 200000000) := rfl
@[simp] theorem lookup_literalQ_2_9 : literalQ (1, 0) (4, 1) = (-1179711 / 200000000) := rfl
@[simp] theorem lookup_literalQ_2_10 : literalQ (1, 0) (5, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_2_11 : literalQ (1, 0) (5, 1) = (1179711 / 200000000) := rfl
@[simp] theorem lookup_literalQ_2_12 : literalQ (1, 0) (6, 0) = (-113429 / 40000000) := rfl
@[simp] theorem lookup_literalQ_2_13 : literalQ (1, 0) (6, 1) = (-113429 / 40000000) := rfl
@[simp] theorem lookup_literalQ_2_14 : literalQ (1, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_2_15 : literalQ (1, 0) (7, 1) = (113429 / 40000000) := rfl
@[simp] theorem lookup_literalQ_3_0 : literalQ (1, 1) (0, 0) = (-57549969 / 500000000) := rfl
@[simp] theorem lookup_literalQ_3_1 : literalQ (1, 1) (0, 1) = (40879993 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_3_2 : literalQ (1, 1) (1, 0) = (76881057 / 500000000) := rfl
@[simp] theorem lookup_literalQ_3_3 : literalQ (1, 1) (1, 1) = (95953317 / 1000000000) := rfl
@[simp] theorem lookup_literalQ_3_4 : literalQ (1, 1) (2, 0) = (-193408917 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_3_5 : literalQ (1, 1) (2, 1) = (-1040827 / 80000000) := rfl
@[simp] theorem lookup_literalQ_3_6 : literalQ (1, 1) (3, 0) = (90344543 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_3_7 : literalQ (1, 1) (3, 1) = (-164047541 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_3_8 : literalQ (1, 1) (4, 0) = (21769947 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_3_9 : literalQ (1, 1) (4, 1) = (-150063 / 250000000) := rfl
@[simp] theorem lookup_literalQ_3_10 : literalQ (1, 1) (5, 0) = (-146951 / 50000000) := rfl
@[simp] theorem lookup_literalQ_3_11 : literalQ (1, 1) (5, 1) = (-14136119 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_3_12 : literalQ (1, 1) (6, 0) = (42423 / 16000000) := rfl
@[simp] theorem lookup_literalQ_3_13 : literalQ (1, 1) (6, 1) = (-937979 / 400000000) := rfl
@[simp] theorem lookup_literalQ_3_14 : literalQ (1, 1) (7, 0) = (113631 / 50000000) := rfl
@[simp] theorem lookup_literalQ_3_15 : literalQ (1, 1) (7, 1) = (-7151683 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_4_0 : literalQ (2, 0) (0, 0) = (21505073 / 200000000) := rfl
@[simp] theorem lookup_literalQ_4_1 : literalQ (2, 0) (0, 1) = (-2407533 / 200000000) := rfl
@[simp] theorem lookup_literalQ_4_2 : literalQ (2, 0) (1, 0) = (-2223883 / 40000000) := rfl
@[simp] theorem lookup_literalQ_4_3 : literalQ (2, 0) (1, 1) = (-193408917 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_4_4 : literalQ (2, 0) (2, 0) = (-5192829 / 50000000) := rfl
@[simp] theorem lookup_literalQ_4_5 : literalQ (2, 0) (2, 1) = (-4154263 / 40000000) := rfl
@[simp] theorem lookup_literalQ_4_6 : literalQ (2, 0) (3, 0) = (5192829 / 100000000) := rfl
@[simp] theorem lookup_literalQ_4_7 : literalQ (2, 0) (3, 1) = (31156981 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_4_8 : literalQ (2, 0) (4, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_4_9 : literalQ (2, 0) (4, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_4_10 : literalQ (2, 0) (5, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_4_11 : literalQ (2, 0) (5, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_4_12 : literalQ (2, 0) (6, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_4_13 : literalQ (2, 0) (6, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_4_14 : literalQ (2, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_4_15 : literalQ (2, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_5_0 : literalQ (2, 1) (0, 0) = (-108827863 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_5_1 : literalQ (2, 1) (0, 1) = (21505073 / 200000000) := rfl
@[simp] theorem lookup_literalQ_5_2 : literalQ (2, 1) (1, 0) = (212684433 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_5_3 : literalQ (2, 1) (1, 1) = (-1040827 / 80000000) := rfl
@[simp] theorem lookup_literalQ_5_4 : literalQ (2, 1) (2, 0) = (-4154263 / 40000000) := rfl
@[simp] theorem lookup_literalQ_5_5 : literalQ (2, 1) (2, 1) = (-5192829 / 50000000) := rfl
@[simp] theorem lookup_literalQ_5_6 : literalQ (2, 1) (3, 0) = (5192829 / 100000000) := rfl
@[simp] theorem lookup_literalQ_5_7 : literalQ (2, 1) (3, 1) = (15578487 / 1000000000) := rfl
@[simp] theorem lookup_literalQ_5_8 : literalQ (2, 1) (4, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_5_9 : literalQ (2, 1) (4, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_5_10 : literalQ (2, 1) (5, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_5_11 : literalQ (2, 1) (5, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_5_12 : literalQ (2, 1) (6, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_5_13 : literalQ (2, 1) (6, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_5_14 : literalQ (2, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_5_15 : literalQ (2, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_6_0 : literalQ (3, 0) (0, 0) = (-1806891 / 40000000) := rfl
@[simp] theorem lookup_literalQ_6_1 : literalQ (3, 0) (0, 1) = (-1129307 / 25000000) := rfl
@[simp] theorem lookup_literalQ_6_2 : literalQ (3, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_6_3 : literalQ (3, 0) (1, 1) = (90344543 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_6_4 : literalQ (3, 0) (2, 0) = (5192829 / 100000000) := rfl
@[simp] theorem lookup_literalQ_6_5 : literalQ (3, 0) (2, 1) = (5192829 / 100000000) := rfl
@[simp] theorem lookup_literalQ_6_6 : literalQ (3, 0) (3, 0) = (-1351203 / 100000000) := rfl
@[simp] theorem lookup_literalQ_6_7 : literalQ (3, 0) (3, 1) = (-6544031 / 100000000) := rfl
@[simp] theorem lookup_literalQ_6_8 : literalQ (3, 0) (4, 0) = (1351203 / 200000000) := rfl
@[simp] theorem lookup_literalQ_6_9 : literalQ (3, 0) (4, 1) = (4053623 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_6_10 : literalQ (3, 0) (5, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_6_11 : literalQ (3, 0) (5, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_6_12 : literalQ (3, 0) (6, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_6_13 : literalQ (3, 0) (6, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_6_14 : literalQ (3, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_6_15 : literalQ (3, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_7_0 : literalQ (3, 1) (0, 0) = (-24982541 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_7_1 : literalQ (3, 1) (0, 1) = (-12491257 / 1000000000) := rfl
@[simp] theorem lookup_literalQ_7_2 : literalQ (3, 1) (1, 0) = (2223883 / 40000000) := rfl
@[simp] theorem lookup_literalQ_7_3 : literalQ (3, 1) (1, 1) = (-164047541 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_7_4 : literalQ (3, 1) (2, 0) = (31156981 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_7_5 : literalQ (3, 1) (2, 1) = (15578487 / 1000000000) := rfl
@[simp] theorem lookup_literalQ_7_6 : literalQ (3, 1) (3, 0) = (-6544031 / 100000000) := rfl
@[simp] theorem lookup_literalQ_7_7 : literalQ (3, 1) (3, 1) = (7398447 / 125000000) := rfl
@[simp] theorem lookup_literalQ_7_8 : literalQ (3, 1) (4, 0) = (1351203 / 200000000) := rfl
@[simp] theorem lookup_literalQ_7_9 : literalQ (3, 1) (4, 1) = (4053609 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_7_10 : literalQ (3, 1) (5, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_7_11 : literalQ (3, 1) (5, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_7_12 : literalQ (3, 1) (6, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_7_13 : literalQ (3, 1) (6, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_7_14 : literalQ (3, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_7_15 : literalQ (3, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_8_0 : literalQ (4, 0) (0, 0) = (-85743 / 100000000) := rfl
@[simp] theorem lookup_literalQ_8_1 : literalQ (4, 0) (0, 1) = (-85743 / 100000000) := rfl
@[simp] theorem lookup_literalQ_8_2 : literalQ (4, 0) (1, 0) = (-1179711 / 200000000) := rfl
@[simp] theorem lookup_literalQ_8_3 : literalQ (4, 0) (1, 1) = (21769947 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_8_4 : literalQ (4, 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_8_5 : literalQ (4, 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_8_6 : literalQ (4, 0) (3, 0) = (1351203 / 200000000) := rfl
@[simp] theorem lookup_literalQ_8_7 : literalQ (4, 0) (3, 1) = (1351203 / 200000000) := rfl
@[simp] theorem lookup_literalQ_8_8 : literalQ (4, 0) (4, 0) = (-3 / 50000000) := rfl
@[simp] theorem lookup_literalQ_8_9 : literalQ (4, 0) (4, 1) = (-675607 / 100000000) := rfl
@[simp] theorem lookup_literalQ_8_10 : literalQ (4, 0) (5, 0) = (3 / 100000000) := rfl
@[simp] theorem lookup_literalQ_8_11 : literalQ (4, 0) (5, 1) = (1 / 80000000) := rfl
@[simp] theorem lookup_literalQ_8_12 : literalQ (4, 0) (6, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_8_13 : literalQ (4, 0) (6, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_8_14 : literalQ (4, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_8_15 : literalQ (4, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_9_0 : literalQ (4, 1) (0, 0) = (21255567 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_9_1 : literalQ (4, 1) (0, 1) = (21255591 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_9_2 : literalQ (4, 1) (1, 0) = (-1179711 / 200000000) := rfl
@[simp] theorem lookup_literalQ_9_3 : literalQ (4, 1) (1, 1) = (-150063 / 250000000) := rfl
@[simp] theorem lookup_literalQ_9_4 : literalQ (4, 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_9_5 : literalQ (4, 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_9_6 : literalQ (4, 1) (3, 0) = (4053623 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_9_7 : literalQ (4, 1) (3, 1) = (4053609 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_9_8 : literalQ (4, 1) (4, 0) = (-675607 / 100000000) := rfl
@[simp] theorem lookup_literalQ_9_9 : literalQ (4, 1) (4, 1) = (9458361 / 1000000000) := rfl
@[simp] theorem lookup_literalQ_9_10 : literalQ (4, 1) (5, 0) = (3 / 100000000) := rfl
@[simp] theorem lookup_literalQ_9_11 : literalQ (4, 1) (5, 1) = (9 / 1000000000) := rfl
@[simp] theorem lookup_literalQ_9_12 : literalQ (4, 1) (6, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_9_13 : literalQ (4, 1) (6, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_9_14 : literalQ (4, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_9_15 : literalQ (4, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_10_0 : literalQ (5, 0) (0, 0) = (146951 / 50000000) := rfl
@[simp] theorem lookup_literalQ_10_1 : literalQ (5, 0) (0, 1) = (146951 / 50000000) := rfl
@[simp] theorem lookup_literalQ_10_2 : literalQ (5, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_10_3 : literalQ (5, 0) (1, 1) = (-146951 / 50000000) := rfl
@[simp] theorem lookup_literalQ_10_4 : literalQ (5, 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_10_5 : literalQ (5, 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_10_6 : literalQ (5, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_10_7 : literalQ (5, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_10_8 : literalQ (5, 0) (4, 0) = (3 / 100000000) := rfl
@[simp] theorem lookup_literalQ_10_9 : literalQ (5, 0) (4, 1) = (3 / 100000000) := rfl
@[simp] theorem lookup_literalQ_10_10 : literalQ (5, 0) (5, 0) = (-58781 / 10000000) := rfl
@[simp] theorem lookup_literalQ_10_11 : literalQ (5, 0) (5, 1) = (-1010283 / 200000000) := rfl
@[simp] theorem lookup_literalQ_10_12 : literalQ (5, 0) (6, 0) = (58781 / 20000000) := rfl
@[simp] theorem lookup_literalQ_10_13 : literalQ (5, 0) (6, 1) = (2920831 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_10_14 : literalQ (5, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_10_15 : literalQ (5, 0) (7, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_11_0 : literalQ (5, 1) (0, 0) = (-1514481 / 400000000) := rfl
@[simp] theorem lookup_literalQ_11_1 : literalQ (5, 1) (0, 1) = (-739871 / 250000000) := rfl
@[simp] theorem lookup_literalQ_11_2 : literalQ (5, 1) (1, 0) = (1179711 / 200000000) := rfl
@[simp] theorem lookup_literalQ_11_3 : literalQ (5, 1) (1, 1) = (-14136119 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_11_4 : literalQ (5, 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_11_5 : literalQ (5, 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_11_6 : literalQ (5, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_11_7 : literalQ (5, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_11_8 : literalQ (5, 1) (4, 0) = (1 / 80000000) := rfl
@[simp] theorem lookup_literalQ_11_9 : literalQ (5, 1) (4, 1) = (9 / 1000000000) := rfl
@[simp] theorem lookup_literalQ_11_10 : literalQ (5, 1) (5, 0) = (-1010283 / 200000000) := rfl
@[simp] theorem lookup_literalQ_11_11 : literalQ (5, 1) (5, 1) = (-2939029 / 500000000) := rfl
@[simp] theorem lookup_literalQ_11_12 : literalQ (5, 1) (6, 0) = (58781 / 20000000) := rfl
@[simp] theorem lookup_literalQ_11_13 : literalQ (5, 1) (6, 1) = (176343 / 200000000) := rfl
@[simp] theorem lookup_literalQ_11_14 : literalQ (5, 1) (7, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_11_15 : literalQ (5, 1) (7, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_12_0 : literalQ (6, 0) (0, 0) = (433859 / 200000000) := rfl
@[simp] theorem lookup_literalQ_12_1 : literalQ (6, 0) (0, 1) = (433859 / 200000000) := rfl
@[simp] theorem lookup_literalQ_12_2 : literalQ (6, 0) (1, 0) = (-113429 / 40000000) := rfl
@[simp] theorem lookup_literalQ_12_3 : literalQ (6, 0) (1, 1) = (42423 / 16000000) := rfl
@[simp] theorem lookup_literalQ_12_4 : literalQ (6, 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_12_5 : literalQ (6, 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_12_6 : literalQ (6, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_12_7 : literalQ (6, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_12_8 : literalQ (6, 0) (4, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_12_9 : literalQ (6, 0) (4, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_12_10 : literalQ (6, 0) (5, 0) = (58781 / 20000000) := rfl
@[simp] theorem lookup_literalQ_12_11 : literalQ (6, 0) (5, 1) = (58781 / 20000000) := rfl
@[simp] theorem lookup_literalQ_12_12 : literalQ (6, 0) (6, 0) = (-113631 / 25000000) := rfl
@[simp] theorem lookup_literalQ_12_13 : literalQ (6, 0) (6, 1) = (-919449 / 200000000) := rfl
@[simp] theorem lookup_literalQ_12_14 : literalQ (6, 0) (7, 0) = (113631 / 50000000) := rfl
@[simp] theorem lookup_literalQ_12_15 : literalQ (6, 0) (7, 1) = (1081087 / 400000000) := rfl
@[simp] theorem lookup_literalQ_13_0 : literalQ (6, 1) (0, 0) = (7399869 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_13_1 : literalQ (6, 1) (0, 1) = (89571 / 12500000) := rfl
@[simp] theorem lookup_literalQ_13_2 : literalQ (6, 1) (1, 0) = (-113429 / 40000000) := rfl
@[simp] theorem lookup_literalQ_13_3 : literalQ (6, 1) (1, 1) = (-937979 / 400000000) := rfl
@[simp] theorem lookup_literalQ_13_4 : literalQ (6, 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_13_5 : literalQ (6, 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_13_6 : literalQ (6, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_13_7 : literalQ (6, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_13_8 : literalQ (6, 1) (4, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_13_9 : literalQ (6, 1) (4, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_13_10 : literalQ (6, 1) (5, 0) = (2920831 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_13_11 : literalQ (6, 1) (5, 1) = (176343 / 200000000) := rfl
@[simp] theorem lookup_literalQ_13_12 : literalQ (6, 1) (6, 0) = (-919449 / 200000000) := rfl
@[simp] theorem lookup_literalQ_13_13 : literalQ (6, 1) (6, 1) = (-43057 / 100000000) := rfl
@[simp] theorem lookup_literalQ_13_14 : literalQ (6, 1) (7, 0) = (113631 / 50000000) := rfl
@[simp] theorem lookup_literalQ_13_15 : literalQ (6, 1) (7, 1) = (340893 / 500000000) := rfl
@[simp] theorem lookup_literalQ_14_0 : literalQ (7, 0) (0, 0) = (-113631 / 50000000) := rfl
@[simp] theorem lookup_literalQ_14_1 : literalQ (7, 0) (0, 1) = (-113631 / 50000000) := rfl
@[simp] theorem lookup_literalQ_14_2 : literalQ (7, 0) (1, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_14_3 : literalQ (7, 0) (1, 1) = (113631 / 50000000) := rfl
@[simp] theorem lookup_literalQ_14_4 : literalQ (7, 0) (2, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_14_5 : literalQ (7, 0) (2, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_14_6 : literalQ (7, 0) (3, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_14_7 : literalQ (7, 0) (3, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_14_8 : literalQ (7, 0) (4, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_14_9 : literalQ (7, 0) (4, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_14_10 : literalQ (7, 0) (5, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_14_11 : literalQ (7, 0) (5, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_14_12 : literalQ (7, 0) (6, 0) = (113631 / 50000000) := rfl
@[simp] theorem lookup_literalQ_14_13 : literalQ (7, 0) (6, 1) = (113631 / 50000000) := rfl
@[simp] theorem lookup_literalQ_14_14 : literalQ (7, 0) (7, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_14_15 : literalQ (7, 0) (7, 1) = (-113631 / 50000000) := rfl
@[simp] theorem lookup_literalQ_15_0 : literalQ (7, 1) (0, 0) = (-1306329 / 400000000) := rfl
@[simp] theorem lookup_literalQ_15_1 : literalQ (7, 1) (0, 1) = (-1244891 / 1000000000) := rfl
@[simp] theorem lookup_literalQ_15_2 : literalQ (7, 1) (1, 0) = (113429 / 40000000) := rfl
@[simp] theorem lookup_literalQ_15_3 : literalQ (7, 1) (1, 1) = (-7151683 / 2000000000) := rfl
@[simp] theorem lookup_literalQ_15_4 : literalQ (7, 1) (2, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_15_5 : literalQ (7, 1) (2, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_15_6 : literalQ (7, 1) (3, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_15_7 : literalQ (7, 1) (3, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_15_8 : literalQ (7, 1) (4, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_15_9 : literalQ (7, 1) (4, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_15_10 : literalQ (7, 1) (5, 0) = 0 := rfl
@[simp] theorem lookup_literalQ_15_11 : literalQ (7, 1) (5, 1) = 0 := rfl
@[simp] theorem lookup_literalQ_15_12 : literalQ (7, 1) (6, 0) = (1081087 / 400000000) := rfl
@[simp] theorem lookup_literalQ_15_13 : literalQ (7, 1) (6, 1) = (340893 / 500000000) := rfl
@[simp] theorem lookup_literalQ_15_14 : literalQ (7, 1) (7, 0) = (-113631 / 50000000) := rfl
@[simp] theorem lookup_literalQ_15_15 : literalQ (7, 1) (7, 1) = (795417 / 250000000) := rfl
@[simp] theorem lookup_literalAction_0_0 : literalAction (0, 0) 0 = (-41353 / 10000000) := rfl
@[simp] theorem lookup_literalAction_0_1 : literalAction (0, 0) 1 = (-87472871 / 500000000) := rfl
@[simp] theorem lookup_literalAction_1_0 : literalAction (0, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_1_1 : literalAction (0, 1) 1 = (-1554021 / 200000000) := rfl
@[simp] theorem lookup_literalAction_2_0 : literalAction (1, 0) 0 = (41353 / 10000000) := rfl
@[simp] theorem lookup_literalAction_2_1 : literalAction (1, 0) 1 = (742298761 / 2000000000) := rfl
@[simp] theorem lookup_literalAction_3_0 : literalAction (1, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_3_1 : literalAction (1, 1) 1 = (1554021 / 200000000) := rfl
@[simp] theorem lookup_literalAction_4_0 : literalAction (2, 0) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_4_1 : literalAction (2, 0) 1 = (-12313763 / 62500000) := rfl
@[simp] theorem lookup_literalAction_5_0 : literalAction (2, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_5_1 : literalAction (2, 1) 1 = (12473869 / 2000000000) := rfl
@[simp] theorem lookup_literalAction_6_0 : literalAction (3, 0) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_6_1 : literalAction (3, 0) 1 = (-11485217 / 1000000000) := rfl
@[simp] theorem lookup_literalAction_7_0 : literalAction (3, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_7_1 : literalAction (3, 1) 1 = (-221527 / 12500000) := rfl
@[simp] theorem lookup_literalAction_8_0 : literalAction (4, 0) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_8_1 : literalAction (4, 0) 1 = (10027501 / 1000000000) := rfl
@[simp] theorem lookup_literalAction_9_0 : literalAction (4, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_9_1 : literalAction (4, 1) 1 = (10756359 / 500000000) := rfl
@[simp] theorem lookup_literalAction_10_0 : literalAction (5, 0) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_10_1 : literalAction (5, 0) 1 = (-7181939 / 2000000000) := rfl
@[simp] theorem lookup_literalAction_11_0 : literalAction (5, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_11_1 : literalAction (5, 1) 1 = (-6009551 / 400000000) := rfl
@[simp] theorem lookup_literalAction_12_0 : literalAction (6, 0) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_12_1 : literalAction (6, 0) 1 = (1173051 / 200000000) := rfl
@[simp] theorem lookup_literalAction_13_0 : literalAction (6, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_13_1 : literalAction (6, 1) 1 = (11907327 / 2000000000) := rfl
@[simp] theorem lookup_literalAction_14_0 : literalAction (7, 0) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_14_1 : literalAction (7, 0) 1 = 0 := rfl
@[simp] theorem lookup_literalAction_15_0 : literalAction (7, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalAction_15_1 : literalAction (7, 1) 1 = (-1914557 / 2000000000) := rfl
@[simp] theorem lookup_literalPrefix_0_0 : literalPrefix (0, 0) 0 = (41353 / 10000000) := rfl
@[simp] theorem lookup_literalPrefix_0_1 : literalPrefix (0, 0) 1 = (87472871 / 500000000) := rfl
@[simp] theorem lookup_literalPrefix_1_0 : literalPrefix (0, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalPrefix_1_1 : literalPrefix (0, 1) 1 = (1554021 / 200000000) := rfl
@[simp] theorem lookup_literalPrefix_2_0 : literalPrefix (1, 0) 0 = 0 := rfl
@[simp] theorem lookup_literalPrefix_2_1 : literalPrefix (1, 0) 1 = (-392407277 / 2000000000) := rfl
@[simp] theorem lookup_literalPrefix_3_0 : literalPrefix (1, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalPrefix_3_1 : literalPrefix (1, 1) 1 = 0 := rfl
@[simp] theorem lookup_literalPrefix_4_0 : literalPrefix (2, 0) 0 = 0 := rfl
@[simp] theorem lookup_literalPrefix_4_1 : literalPrefix (2, 0) 1 = (1633139 / 2000000000) := rfl
@[simp] theorem lookup_literalPrefix_5_0 : literalPrefix (2, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalPrefix_5_1 : literalPrefix (2, 1) 1 = (-12473869 / 2000000000) := rfl
@[simp] theorem lookup_literalPrefix_6_0 : literalPrefix (3, 0) 0 = 0 := rfl
@[simp] theorem lookup_literalPrefix_6_1 : literalPrefix (3, 0) 1 = (24603573 / 2000000000) := rfl
@[simp] theorem lookup_literalPrefix_7_0 : literalPrefix (3, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalPrefix_7_1 : literalPrefix (3, 1) 1 = (22970451 / 2000000000) := rfl
@[simp] theorem lookup_literalPrefix_8_0 : literalPrefix (4, 0) 0 = 0 := rfl
@[simp] theorem lookup_literalPrefix_8_1 : literalPrefix (4, 0) 1 = (4548571 / 2000000000) := rfl
@[simp] theorem lookup_literalPrefix_9_0 : literalPrefix (4, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalPrefix_9_1 : literalPrefix (4, 1) 1 = (-4010997 / 400000000) := rfl
@[simp] theorem lookup_literalPrefix_10_0 : literalPrefix (5, 0) 0 = 0 := rfl
@[simp] theorem lookup_literalPrefix_10_1 : literalPrefix (5, 0) 1 = (1173051 / 200000000) := rfl
@[simp] theorem lookup_literalPrefix_11_0 : literalPrefix (5, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalPrefix_11_1 : literalPrefix (5, 1) 1 = (999277 / 200000000) := rfl
@[simp] theorem lookup_literalPrefix_12_0 : literalPrefix (6, 0) 0 = 0 := rfl
@[simp] theorem lookup_literalPrefix_12_1 : literalPrefix (6, 0) 1 = 0 := rfl
@[simp] theorem lookup_literalPrefix_13_0 : literalPrefix (6, 1) 0 = 0 := rfl
@[simp] theorem lookup_literalPrefix_13_1 : literalPrefix (6, 1) 1 = (-1914557 / 2000000000) := rfl
@[simp] theorem lookup_literalA_0_0 : literalA (0, 0) (0, 0) = (12726347 / 100000000) := rfl
@[simp] theorem lookup_literalA_0_1 : literalA (0, 0) (0, 1) = (-17733 / 20000000) := rfl
@[simp] theorem lookup_literalA_0_2 : literalA (0, 0) (1, 0) = (-5782597 / 100000000) := rfl
@[simp] theorem lookup_literalA_0_3 : literalA (0, 0) (1, 1) = (233347933 / 2000000000) := rfl
@[simp] theorem lookup_literalA_0_4 : literalA (0, 0) (2, 0) = (-5169047 / 50000000) := rfl
@[simp] theorem lookup_literalA_0_5 : literalA (0, 0) (2, 1) = (106990111 / 2000000000) := rfl
@[simp] theorem lookup_literalA_0_6 : literalA (0, 0) (3, 0) = (250373 / 6250000) := rfl
@[simp] theorem lookup_literalA_0_7 : literalA (0, 0) (3, 1) = (559937 / 50000000) := rfl
@[simp] theorem lookup_literalA_0_8 : literalA (0, 0) (4, 0) = (71489 / 100000000) := rfl
@[simp] theorem lookup_literalA_0_9 : literalA (0, 0) (4, 1) = (-7529 / 781250) := rfl
@[simp] theorem lookup_literalA_0_10 : literalA (0, 0) (5, 0) = (-169547 / 100000000) := rfl
@[simp] theorem lookup_literalA_0_11 : literalA (0, 0) (5, 1) = (433341 / 100000000) := rfl
@[simp] theorem lookup_literalA_1_0 : literalA (0, 1) (0, 0) = (-17733 / 20000000) := rfl
@[simp] theorem lookup_literalA_1_1 : literalA (0, 1) (0, 1) = (5352311 / 40000000) := rfl
@[simp] theorem lookup_literalA_1_2 : literalA (0, 1) (1, 0) = (-105587253 / 2000000000) := rfl
@[simp] theorem lookup_literalA_1_3 : literalA (0, 1) (1, 1) = (-854021 / 50000000) := rfl
@[simp] theorem lookup_literalA_1_4 : literalA (0, 1) (2, 0) = (609523 / 50000000) := rfl
@[simp] theorem lookup_literalA_1_5 : literalA (0, 1) (2, 1) = (-2119997 / 20000000) := rfl
@[simp] theorem lookup_literalA_1_6 : literalA (0, 1) (3, 0) = (82849553 / 2000000000) := rfl
@[simp] theorem lookup_literalA_1_7 : literalA (0, 1) (3, 1) = (135991 / 12500000) := rfl
@[simp] theorem lookup_literalA_1_8 : literalA (0, 1) (4, 0) = (4291 / 12500000) := rfl
@[simp] theorem lookup_literalA_1_9 : literalA (0, 1) (4, 1) = (-1119817 / 100000000) := rfl
@[simp] theorem lookup_literalA_1_10 : literalA (0, 1) (5, 0) = (-11031 / 50000000) := rfl
@[simp] theorem lookup_literalA_1_11 : literalA (0, 1) (5, 1) = (34667 / 12500000) := rfl
@[simp] theorem lookup_literalA_2_0 : literalA (1, 0) (0, 0) = (-5782597 / 100000000) := rfl
@[simp] theorem lookup_literalA_2_1 : literalA (1, 0) (0, 1) = (-105587253 / 2000000000) := rfl
@[simp] theorem lookup_literalA_2_2 : literalA (1, 0) (1, 0) = (2104609 / 20000000) := rfl
@[simp] theorem lookup_literalA_2_3 : literalA (1, 0) (1, 1) = (-39649573 / 250000000) := rfl
@[simp] theorem lookup_literalA_2_4 : literalA (1, 0) (2, 0) = (43701 / 12500000) := rfl
@[simp] theorem lookup_literalA_2_5 : literalA (1, 0) (2, 1) = (287709 / 25000000) := rfl
@[simp] theorem lookup_literalA_2_6 : literalA (1, 0) (3, 0) = (-1809101 / 20000000) := rfl
@[simp] theorem lookup_literalA_2_7 : literalA (1, 0) (3, 1) = (-33997 / 50000000) := rfl
@[simp] theorem lookup_literalA_2_8 : literalA (1, 0) (4, 0) = (3861663 / 100000000) := rfl
@[simp] theorem lookup_literalA_2_9 : literalA (1, 0) (4, 1) = (707927 / 50000000) := rfl
@[simp] theorem lookup_literalA_2_10 : literalA (1, 0) (5, 0) = (93007 / 100000000) := rfl
@[simp] theorem lookup_literalA_2_11 : literalA (1, 0) (5, 1) = (-1173043 / 100000000) := rfl
@[simp] theorem lookup_literalA_3_0 : literalA (1, 1) (0, 0) = (233347933 / 2000000000) := rfl
@[simp] theorem lookup_literalA_3_1 : literalA (1, 1) (0, 1) = (-854021 / 50000000) := rfl
@[simp] theorem lookup_literalA_3_2 : literalA (1, 1) (1, 0) = (-39649573 / 250000000) := rfl
@[simp] theorem lookup_literalA_3_3 : literalA (1, 1) (1, 1) = (1558521 / 50000000) := rfl
@[simp] theorem lookup_literalA_3_4 : literalA (1, 1) (2, 0) = (184761 / 4000000) := rfl
@[simp] theorem lookup_literalA_3_5 : literalA (1, 1) (2, 1) = (-247407 / 100000000) := rfl
@[simp] theorem lookup_literalA_3_6 : literalA (1, 1) (3, 0) = (-2849763 / 100000000) := rfl
@[simp] theorem lookup_literalA_3_7 : literalA (1, 1) (3, 1) = (-103183 / 5000000) := rfl
@[simp] theorem lookup_literalA_3_8 : literalA (1, 1) (4, 0) = (53053511 / 2000000000) := rfl
@[simp] theorem lookup_literalA_3_9 : literalA (1, 1) (4, 1) = (1034771 / 100000000) := rfl
@[simp] theorem lookup_literalA_3_10 : literalA (1, 1) (5, 0) = (142429 / 100000000) := rfl
@[simp] theorem lookup_literalA_3_11 : literalA (1, 1) (5, 1) = (-157979 / 50000000) := rfl
@[simp] theorem lookup_literalA_4_0 : literalA (2, 0) (0, 0) = (-5169047 / 50000000) := rfl
@[simp] theorem lookup_literalA_4_1 : literalA (2, 0) (0, 1) = (609523 / 50000000) := rfl
@[simp] theorem lookup_literalA_4_2 : literalA (2, 0) (1, 0) = (43701 / 12500000) := rfl
@[simp] theorem lookup_literalA_4_3 : literalA (2, 0) (1, 1) = (184761 / 4000000) := rfl
@[simp] theorem lookup_literalA_4_4 : literalA (2, 0) (2, 0) = (146999 / 800000) := rfl
@[simp] theorem lookup_literalA_4_5 : literalA (2, 0) (2, 1) = (-116658401 / 2000000000) := rfl
@[simp] theorem lookup_literalA_4_6 : literalA (2, 0) (3, 0) = (-491841 / 12500000) := rfl
@[simp] theorem lookup_literalA_4_7 : literalA (2, 0) (3, 1) = (-114797 / 50000000) := rfl
@[simp] theorem lookup_literalA_4_8 : literalA (2, 0) (4, 0) = (-7541479 / 100000000) := rfl
@[simp] theorem lookup_literalA_4_9 : literalA (2, 0) (4, 1) = (-33957 / 50000000) := rfl
@[simp] theorem lookup_literalA_4_10 : literalA (2, 0) (5, 0) = (728037 / 25000000) := rfl
@[simp] theorem lookup_literalA_4_11 : literalA (2, 0) (5, 1) = (228523 / 25000000) := rfl
@[simp] theorem lookup_literalA_5_0 : literalA (2, 1) (0, 0) = (106990111 / 2000000000) := rfl
@[simp] theorem lookup_literalA_5_1 : literalA (2, 1) (0, 1) = (-2119997 / 20000000) := rfl
@[simp] theorem lookup_literalA_5_2 : literalA (2, 1) (1, 0) = (287709 / 25000000) := rfl
@[simp] theorem lookup_literalA_5_3 : literalA (2, 1) (1, 1) = (-247407 / 100000000) := rfl
@[simp] theorem lookup_literalA_5_4 : literalA (2, 1) (2, 0) = (-116658401 / 2000000000) := rfl
@[simp] theorem lookup_literalA_5_5 : literalA (2, 1) (2, 1) = (253737411 / 2000000000) := rfl
@[simp] theorem lookup_literalA_5_6 : literalA (2, 1) (3, 0) = (-15333 / 12500000) := rfl
@[simp] theorem lookup_literalA_5_7 : literalA (2, 1) (3, 1) = (-773293 / 50000000) := rfl
@[simp] theorem lookup_literalA_5_8 : literalA (2, 1) (4, 0) = (-1099567 / 50000000) := rfl
@[simp] theorem lookup_literalA_5_9 : literalA (2, 1) (4, 1) = (-1642681 / 100000000) := rfl
@[simp] theorem lookup_literalA_5_10 : literalA (2, 1) (5, 0) = (3538611 / 200000000) := rfl
@[simp] theorem lookup_literalA_5_11 : literalA (2, 1) (5, 1) = (777133 / 100000000) := rfl
@[simp] theorem lookup_literalA_6_0 : literalA (3, 0) (0, 0) = (250373 / 6250000) := rfl
@[simp] theorem lookup_literalA_6_1 : literalA (3, 0) (0, 1) = (82849553 / 2000000000) := rfl
@[simp] theorem lookup_literalA_6_2 : literalA (3, 0) (1, 0) = (-1809101 / 20000000) := rfl
@[simp] theorem lookup_literalA_6_3 : literalA (3, 0) (1, 1) = (-2849763 / 100000000) := rfl
@[simp] theorem lookup_literalA_6_4 : literalA (3, 0) (2, 0) = (-491841 / 12500000) := rfl
@[simp] theorem lookup_literalA_6_5 : literalA (3, 0) (2, 1) = (-15333 / 12500000) := rfl
@[simp] theorem lookup_literalA_6_6 : literalA (3, 0) (3, 0) = (15969019 / 100000000) := rfl
@[simp] theorem lookup_literalA_6_7 : literalA (3, 0) (3, 1) = (12009 / 20000000) := rfl
@[simp] theorem lookup_literalA_6_8 : literalA (3, 0) (4, 0) = (-73531 / 2000000) := rfl
@[simp] theorem lookup_literalA_6_9 : literalA (3, 0) (4, 1) = (-109 / 250000) := rfl
@[simp] theorem lookup_literalA_6_10 : literalA (3, 0) (5, 0) = (-1339039 / 25000000) := rfl
@[simp] theorem lookup_literalA_6_11 : literalA (3, 0) (5, 1) = (-31717 / 20000000) := rfl
@[simp] theorem lookup_literalA_7_0 : literalA (3, 1) (0, 0) = (559937 / 50000000) := rfl
@[simp] theorem lookup_literalA_7_1 : literalA (3, 1) (0, 1) = (135991 / 12500000) := rfl
@[simp] theorem lookup_literalA_7_2 : literalA (3, 1) (1, 0) = (-33997 / 50000000) := rfl
@[simp] theorem lookup_literalA_7_3 : literalA (3, 1) (1, 1) = (-103183 / 5000000) := rfl
@[simp] theorem lookup_literalA_7_4 : literalA (3, 1) (2, 0) = (-114797 / 50000000) := rfl
@[simp] theorem lookup_literalA_7_5 : literalA (3, 1) (2, 1) = (-773293 / 50000000) := rfl
@[simp] theorem lookup_literalA_7_6 : literalA (3, 1) (3, 0) = (12009 / 20000000) := rfl
@[simp] theorem lookup_literalA_7_7 : literalA (3, 1) (3, 1) = (116489531 / 2000000000) := rfl
@[simp] theorem lookup_literalA_7_8 : literalA (3, 1) (4, 0) = (-200391 / 50000000) := rfl
@[simp] theorem lookup_literalA_7_9 : literalA (3, 1) (4, 1) = (-352457 / 25000000) := rfl
@[simp] theorem lookup_literalA_7_10 : literalA (3, 1) (5, 0) = (-789233 / 50000000) := rfl
@[simp] theorem lookup_literalA_7_11 : literalA (3, 1) (5, 1) = (-601167 / 50000000) := rfl
@[simp] theorem lookup_literalA_8_0 : literalA (4, 0) (0, 0) = (71489 / 100000000) := rfl
@[simp] theorem lookup_literalA_8_1 : literalA (4, 0) (0, 1) = (4291 / 12500000) := rfl
@[simp] theorem lookup_literalA_8_2 : literalA (4, 0) (1, 0) = (3861663 / 100000000) := rfl
@[simp] theorem lookup_literalA_8_3 : literalA (4, 0) (1, 1) = (53053511 / 2000000000) := rfl
@[simp] theorem lookup_literalA_8_4 : literalA (4, 0) (2, 0) = (-7541479 / 100000000) := rfl
@[simp] theorem lookup_literalA_8_5 : literalA (4, 0) (2, 1) = (-1099567 / 50000000) := rfl
@[simp] theorem lookup_literalA_8_6 : literalA (4, 0) (3, 0) = (-73531 / 2000000) := rfl
@[simp] theorem lookup_literalA_8_7 : literalA (4, 0) (3, 1) = (-200391 / 50000000) := rfl
@[simp] theorem lookup_literalA_8_8 : literalA (4, 0) (4, 0) = (2902601 / 25000000) := rfl
@[simp] theorem lookup_literalA_8_9 : literalA (4, 0) (4, 1) = (-71663 / 25000000) := rfl
@[simp] theorem lookup_literalA_8_10 : literalA (4, 0) (5, 0) = (-20759 / 1000000) := rfl
@[simp] theorem lookup_literalA_8_11 : literalA (4, 0) (5, 1) = (72599 / 25000000) := rfl
@[simp] theorem lookup_literalA_9_0 : literalA (4, 1) (0, 0) = (-7529 / 781250) := rfl
@[simp] theorem lookup_literalA_9_1 : literalA (4, 1) (0, 1) = (-1119817 / 100000000) := rfl
@[simp] theorem lookup_literalA_9_2 : literalA (4, 1) (1, 0) = (707927 / 50000000) := rfl
@[simp] theorem lookup_literalA_9_3 : literalA (4, 1) (1, 1) = (1034771 / 100000000) := rfl
@[simp] theorem lookup_literalA_9_4 : literalA (4, 1) (2, 0) = (-33957 / 50000000) := rfl
@[simp] theorem lookup_literalA_9_5 : literalA (4, 1) (2, 1) = (-1642681 / 100000000) := rfl
@[simp] theorem lookup_literalA_9_6 : literalA (4, 1) (3, 0) = (-109 / 250000) := rfl
@[simp] theorem lookup_literalA_9_7 : literalA (4, 1) (3, 1) = (-352457 / 25000000) := rfl
@[simp] theorem lookup_literalA_9_8 : literalA (4, 1) (4, 0) = (-71663 / 25000000) := rfl
@[simp] theorem lookup_literalA_9_9 : literalA (4, 1) (4, 1) = (14065111 / 400000000) := rfl
@[simp] theorem lookup_literalA_9_10 : literalA (4, 1) (5, 0) = (239937 / 100000000) := rfl
@[simp] theorem lookup_literalA_9_11 : literalA (4, 1) (5, 1) = (-490729 / 50000000) := rfl
@[simp] theorem lookup_literalA_10_0 : literalA (5, 0) (0, 0) = (-169547 / 100000000) := rfl
@[simp] theorem lookup_literalA_10_1 : literalA (5, 0) (0, 1) = (-11031 / 50000000) := rfl
@[simp] theorem lookup_literalA_10_2 : literalA (5, 0) (1, 0) = (93007 / 100000000) := rfl
@[simp] theorem lookup_literalA_10_3 : literalA (5, 0) (1, 1) = (142429 / 100000000) := rfl
@[simp] theorem lookup_literalA_10_4 : literalA (5, 0) (2, 0) = (728037 / 25000000) := rfl
@[simp] theorem lookup_literalA_10_5 : literalA (5, 0) (2, 1) = (3538611 / 200000000) := rfl
@[simp] theorem lookup_literalA_10_6 : literalA (5, 0) (3, 0) = (-1339039 / 25000000) := rfl
@[simp] theorem lookup_literalA_10_7 : literalA (5, 0) (3, 1) = (-789233 / 50000000) := rfl
@[simp] theorem lookup_literalA_10_8 : literalA (5, 0) (4, 0) = (-20759 / 1000000) := rfl
@[simp] theorem lookup_literalA_10_9 : literalA (5, 0) (4, 1) = (239937 / 100000000) := rfl
@[simp] theorem lookup_literalA_10_10 : literalA (5, 0) (5, 0) = (7684479 / 100000000) := rfl
@[simp] theorem lookup_literalA_10_11 : literalA (5, 0) (5, 1) = (-1003 / 1000000) := rfl
@[simp] theorem lookup_literalA_11_0 : literalA (5, 1) (0, 0) = (433341 / 100000000) := rfl
@[simp] theorem lookup_literalA_11_1 : literalA (5, 1) (0, 1) = (34667 / 12500000) := rfl
@[simp] theorem lookup_literalA_11_2 : literalA (5, 1) (1, 0) = (-1173043 / 100000000) := rfl
@[simp] theorem lookup_literalA_11_3 : literalA (5, 1) (1, 1) = (-157979 / 50000000) := rfl
@[simp] theorem lookup_literalA_11_4 : literalA (5, 1) (2, 0) = (228523 / 25000000) := rfl
@[simp] theorem lookup_literalA_11_5 : literalA (5, 1) (2, 1) = (777133 / 100000000) := rfl
@[simp] theorem lookup_literalA_11_6 : literalA (5, 1) (3, 0) = (-31717 / 20000000) := rfl
@[simp] theorem lookup_literalA_11_7 : literalA (5, 1) (3, 1) = (-601167 / 50000000) := rfl
@[simp] theorem lookup_literalA_11_8 : literalA (5, 1) (4, 0) = (72599 / 25000000) := rfl
@[simp] theorem lookup_literalA_11_9 : literalA (5, 1) (4, 1) = (-490729 / 50000000) := rfl
@[simp] theorem lookup_literalA_11_10 : literalA (5, 1) (5, 0) = (-1003 / 1000000) := rfl
@[simp] theorem lookup_literalA_11_11 : literalA (5, 1) (5, 1) = (5993669 / 200000000) := rfl
@[simp] theorem lookup_literalT_0_0 : literalT (0, 0) 0 = (-25009 / 25000000) := rfl
@[simp] theorem lookup_literalT_0_1 : literalT (0, 0) 1 = (-11583 / 50000000) := rfl
@[simp] theorem lookup_literalT_1_0 : literalT (0, 1) 0 = (-2881 / 50000000) := rfl
@[simp] theorem lookup_literalT_1_1 : literalT (0, 1) 1 = (-541187 / 100000000) := rfl
@[simp] theorem lookup_literalT_2_0 : literalT (1, 0) 0 = (779 / 100000000) := rfl
@[simp] theorem lookup_literalT_2_1 : literalT (1, 0) 1 = (7727 / 4000000) := rfl
@[simp] theorem lookup_literalT_3_0 : literalT (1, 1) 0 = (-185967 / 50000000) := rfl
@[simp] theorem lookup_literalT_3_1 : literalT (1, 1) 1 = (91627 / 50000000) := rfl
@[simp] theorem lookup_literalT_4_0 : literalT (2, 0) 0 = (17767 / 10000000) := rfl
@[simp] theorem lookup_literalT_4_1 : literalT (2, 0) 1 = (-270039 / 50000000) := rfl
@[simp] theorem lookup_literalT_5_0 : literalT (2, 1) 0 = (-114929 / 100000000) := rfl
@[simp] theorem lookup_literalT_5_1 : literalT (2, 1) 1 = (-25519 / 50000000) := rfl
@[simp] theorem lookup_literalT_6_0 : literalT (3, 0) 0 = (31843 / 1562500) := rfl
@[simp] theorem lookup_literalT_6_1 : literalT (3, 0) 1 = (50567 / 25000000) := rfl
@[simp] theorem lookup_literalT_7_0 : literalT (3, 1) 0 = (1096917 / 100000000) := rfl
@[simp] theorem lookup_literalT_7_1 : literalT (3, 1) 1 = (229263 / 50000000) := rfl
@[simp] theorem lookup_literalT_8_0 : literalT (4, 0) 0 = (-2249627 / 100000000) := rfl
@[simp] theorem lookup_literalT_8_1 : literalT (4, 0) 1 = (136597 / 100000000) := rfl
@[simp] theorem lookup_literalT_9_0 : literalT (4, 1) 0 = (-293913 / 100000000) := rfl
@[simp] theorem lookup_literalT_9_1 : literalT (4, 1) 1 = (-200007 / 50000000) := rfl
@[simp] theorem lookup_literalT_10_0 : literalT (5, 0) 0 = (-3088031 / 100000000) := rfl
@[simp] theorem lookup_literalT_10_1 : literalT (5, 0) 1 = (67841 / 50000000) := rfl
@[simp] theorem lookup_literalT_11_0 : literalT (5, 1) 0 = (-205901 / 100000000) := rfl
@[simp] theorem lookup_literalT_11_1 : literalT (5, 1) 1 = (-210383 / 20000000) := rfl
@[simp] theorem lookup_literalW_0_0 : literalW 0 0 = (3221293 / 100000000) := rfl
@[simp] theorem lookup_literalW_0_1 : literalW 0 1 = (-52239 / 50000000) := rfl
@[simp] theorem lookup_literalW_1_0 : literalW 1 0 = (-52239 / 50000000) := rfl
@[simp] theorem lookup_literalW_1_1 : literalW 1 1 = (26132923 / 2000000000) := rfl
@[simp] theorem lookup_literalP_0_0 : literalP (0, 0) (0, 0) = (12726347 / 100000000) := rfl
@[simp] theorem lookup_literalP_0_1 : literalP (0, 0) (0, 1) = (-17733 / 20000000) := rfl
@[simp] theorem lookup_literalP_0_2 : literalP (0, 0) (1, 0) = (-5782597 / 100000000) := rfl
@[simp] theorem lookup_literalP_0_3 : literalP (0, 0) (1, 1) = (233347933 / 2000000000) := rfl
@[simp] theorem lookup_literalP_0_4 : literalP (0, 0) (2, 0) = (-5169047 / 50000000) := rfl
@[simp] theorem lookup_literalP_0_5 : literalP (0, 0) (2, 1) = (106990111 / 2000000000) := rfl
@[simp] theorem lookup_literalP_0_6 : literalP (0, 0) (3, 0) = (250373 / 6250000) := rfl
@[simp] theorem lookup_literalP_0_7 : literalP (0, 0) (3, 1) = (559937 / 50000000) := rfl
@[simp] theorem lookup_literalP_0_8 : literalP (0, 0) (4, 0) = (71489 / 100000000) := rfl
@[simp] theorem lookup_literalP_0_9 : literalP (0, 0) (4, 1) = (-7529 / 781250) := rfl
@[simp] theorem lookup_literalP_0_10 : literalP (0, 0) (5, 0) = (-169547 / 100000000) := rfl
@[simp] theorem lookup_literalP_0_11 : literalP (0, 0) (5, 1) = (433341 / 100000000) := rfl
@[simp] theorem lookup_literalP_0_12 : literalP (0, 0) (6, 0) = (-25009 / 25000000) := rfl
@[simp] theorem lookup_literalP_0_13 : literalP (0, 0) (6, 1) = (-11583 / 50000000) := rfl
@[simp] theorem lookup_literalP_1_0 : literalP (0, 1) (0, 0) = (-17733 / 20000000) := rfl
@[simp] theorem lookup_literalP_1_1 : literalP (0, 1) (0, 1) = (5352311 / 40000000) := rfl
@[simp] theorem lookup_literalP_1_2 : literalP (0, 1) (1, 0) = (-105587253 / 2000000000) := rfl
@[simp] theorem lookup_literalP_1_3 : literalP (0, 1) (1, 1) = (-854021 / 50000000) := rfl
@[simp] theorem lookup_literalP_1_4 : literalP (0, 1) (2, 0) = (609523 / 50000000) := rfl
@[simp] theorem lookup_literalP_1_5 : literalP (0, 1) (2, 1) = (-2119997 / 20000000) := rfl
@[simp] theorem lookup_literalP_1_6 : literalP (0, 1) (3, 0) = (82849553 / 2000000000) := rfl
@[simp] theorem lookup_literalP_1_7 : literalP (0, 1) (3, 1) = (135991 / 12500000) := rfl
@[simp] theorem lookup_literalP_1_8 : literalP (0, 1) (4, 0) = (4291 / 12500000) := rfl
@[simp] theorem lookup_literalP_1_9 : literalP (0, 1) (4, 1) = (-1119817 / 100000000) := rfl
@[simp] theorem lookup_literalP_1_10 : literalP (0, 1) (5, 0) = (-11031 / 50000000) := rfl
@[simp] theorem lookup_literalP_1_11 : literalP (0, 1) (5, 1) = (34667 / 12500000) := rfl
@[simp] theorem lookup_literalP_1_12 : literalP (0, 1) (6, 0) = (-2881 / 50000000) := rfl
@[simp] theorem lookup_literalP_1_13 : literalP (0, 1) (6, 1) = (-541187 / 100000000) := rfl
@[simp] theorem lookup_literalP_2_0 : literalP (1, 0) (0, 0) = (-5782597 / 100000000) := rfl
@[simp] theorem lookup_literalP_2_1 : literalP (1, 0) (0, 1) = (-105587253 / 2000000000) := rfl
@[simp] theorem lookup_literalP_2_2 : literalP (1, 0) (1, 0) = (2104609 / 20000000) := rfl
@[simp] theorem lookup_literalP_2_3 : literalP (1, 0) (1, 1) = (-39649573 / 250000000) := rfl
@[simp] theorem lookup_literalP_2_4 : literalP (1, 0) (2, 0) = (43701 / 12500000) := rfl
@[simp] theorem lookup_literalP_2_5 : literalP (1, 0) (2, 1) = (287709 / 25000000) := rfl
@[simp] theorem lookup_literalP_2_6 : literalP (1, 0) (3, 0) = (-1809101 / 20000000) := rfl
@[simp] theorem lookup_literalP_2_7 : literalP (1, 0) (3, 1) = (-33997 / 50000000) := rfl
@[simp] theorem lookup_literalP_2_8 : literalP (1, 0) (4, 0) = (3861663 / 100000000) := rfl
@[simp] theorem lookup_literalP_2_9 : literalP (1, 0) (4, 1) = (707927 / 50000000) := rfl
@[simp] theorem lookup_literalP_2_10 : literalP (1, 0) (5, 0) = (93007 / 100000000) := rfl
@[simp] theorem lookup_literalP_2_11 : literalP (1, 0) (5, 1) = (-1173043 / 100000000) := rfl
@[simp] theorem lookup_literalP_2_12 : literalP (1, 0) (6, 0) = (779 / 100000000) := rfl
@[simp] theorem lookup_literalP_2_13 : literalP (1, 0) (6, 1) = (7727 / 4000000) := rfl
@[simp] theorem lookup_literalP_3_0 : literalP (1, 1) (0, 0) = (233347933 / 2000000000) := rfl
@[simp] theorem lookup_literalP_3_1 : literalP (1, 1) (0, 1) = (-854021 / 50000000) := rfl
@[simp] theorem lookup_literalP_3_2 : literalP (1, 1) (1, 0) = (-39649573 / 250000000) := rfl
@[simp] theorem lookup_literalP_3_3 : literalP (1, 1) (1, 1) = (1558521 / 50000000) := rfl
@[simp] theorem lookup_literalP_3_4 : literalP (1, 1) (2, 0) = (184761 / 4000000) := rfl
@[simp] theorem lookup_literalP_3_5 : literalP (1, 1) (2, 1) = (-247407 / 100000000) := rfl
@[simp] theorem lookup_literalP_3_6 : literalP (1, 1) (3, 0) = (-2849763 / 100000000) := rfl
@[simp] theorem lookup_literalP_3_7 : literalP (1, 1) (3, 1) = (-103183 / 5000000) := rfl
@[simp] theorem lookup_literalP_3_8 : literalP (1, 1) (4, 0) = (53053511 / 2000000000) := rfl
@[simp] theorem lookup_literalP_3_9 : literalP (1, 1) (4, 1) = (1034771 / 100000000) := rfl
@[simp] theorem lookup_literalP_3_10 : literalP (1, 1) (5, 0) = (142429 / 100000000) := rfl
@[simp] theorem lookup_literalP_3_11 : literalP (1, 1) (5, 1) = (-157979 / 50000000) := rfl
@[simp] theorem lookup_literalP_3_12 : literalP (1, 1) (6, 0) = (-185967 / 50000000) := rfl
@[simp] theorem lookup_literalP_3_13 : literalP (1, 1) (6, 1) = (91627 / 50000000) := rfl
@[simp] theorem lookup_literalP_4_0 : literalP (2, 0) (0, 0) = (-5169047 / 50000000) := rfl
@[simp] theorem lookup_literalP_4_1 : literalP (2, 0) (0, 1) = (609523 / 50000000) := rfl
@[simp] theorem lookup_literalP_4_2 : literalP (2, 0) (1, 0) = (43701 / 12500000) := rfl
@[simp] theorem lookup_literalP_4_3 : literalP (2, 0) (1, 1) = (184761 / 4000000) := rfl
@[simp] theorem lookup_literalP_4_4 : literalP (2, 0) (2, 0) = (146999 / 800000) := rfl
@[simp] theorem lookup_literalP_4_5 : literalP (2, 0) (2, 1) = (-116658401 / 2000000000) := rfl
@[simp] theorem lookup_literalP_4_6 : literalP (2, 0) (3, 0) = (-491841 / 12500000) := rfl
@[simp] theorem lookup_literalP_4_7 : literalP (2, 0) (3, 1) = (-114797 / 50000000) := rfl
@[simp] theorem lookup_literalP_4_8 : literalP (2, 0) (4, 0) = (-7541479 / 100000000) := rfl
@[simp] theorem lookup_literalP_4_9 : literalP (2, 0) (4, 1) = (-33957 / 50000000) := rfl
@[simp] theorem lookup_literalP_4_10 : literalP (2, 0) (5, 0) = (728037 / 25000000) := rfl
@[simp] theorem lookup_literalP_4_11 : literalP (2, 0) (5, 1) = (228523 / 25000000) := rfl
@[simp] theorem lookup_literalP_4_12 : literalP (2, 0) (6, 0) = (17767 / 10000000) := rfl
@[simp] theorem lookup_literalP_4_13 : literalP (2, 0) (6, 1) = (-270039 / 50000000) := rfl
@[simp] theorem lookup_literalP_5_0 : literalP (2, 1) (0, 0) = (106990111 / 2000000000) := rfl
@[simp] theorem lookup_literalP_5_1 : literalP (2, 1) (0, 1) = (-2119997 / 20000000) := rfl
@[simp] theorem lookup_literalP_5_2 : literalP (2, 1) (1, 0) = (287709 / 25000000) := rfl
@[simp] theorem lookup_literalP_5_3 : literalP (2, 1) (1, 1) = (-247407 / 100000000) := rfl
@[simp] theorem lookup_literalP_5_4 : literalP (2, 1) (2, 0) = (-116658401 / 2000000000) := rfl
@[simp] theorem lookup_literalP_5_5 : literalP (2, 1) (2, 1) = (253737411 / 2000000000) := rfl
@[simp] theorem lookup_literalP_5_6 : literalP (2, 1) (3, 0) = (-15333 / 12500000) := rfl
@[simp] theorem lookup_literalP_5_7 : literalP (2, 1) (3, 1) = (-773293 / 50000000) := rfl
@[simp] theorem lookup_literalP_5_8 : literalP (2, 1) (4, 0) = (-1099567 / 50000000) := rfl
@[simp] theorem lookup_literalP_5_9 : literalP (2, 1) (4, 1) = (-1642681 / 100000000) := rfl
@[simp] theorem lookup_literalP_5_10 : literalP (2, 1) (5, 0) = (3538611 / 200000000) := rfl
@[simp] theorem lookup_literalP_5_11 : literalP (2, 1) (5, 1) = (777133 / 100000000) := rfl
@[simp] theorem lookup_literalP_5_12 : literalP (2, 1) (6, 0) = (-114929 / 100000000) := rfl
@[simp] theorem lookup_literalP_5_13 : literalP (2, 1) (6, 1) = (-25519 / 50000000) := rfl
@[simp] theorem lookup_literalP_6_0 : literalP (3, 0) (0, 0) = (250373 / 6250000) := rfl
@[simp] theorem lookup_literalP_6_1 : literalP (3, 0) (0, 1) = (82849553 / 2000000000) := rfl
@[simp] theorem lookup_literalP_6_2 : literalP (3, 0) (1, 0) = (-1809101 / 20000000) := rfl
@[simp] theorem lookup_literalP_6_3 : literalP (3, 0) (1, 1) = (-2849763 / 100000000) := rfl
@[simp] theorem lookup_literalP_6_4 : literalP (3, 0) (2, 0) = (-491841 / 12500000) := rfl
@[simp] theorem lookup_literalP_6_5 : literalP (3, 0) (2, 1) = (-15333 / 12500000) := rfl
@[simp] theorem lookup_literalP_6_6 : literalP (3, 0) (3, 0) = (15969019 / 100000000) := rfl
@[simp] theorem lookup_literalP_6_7 : literalP (3, 0) (3, 1) = (12009 / 20000000) := rfl
@[simp] theorem lookup_literalP_6_8 : literalP (3, 0) (4, 0) = (-73531 / 2000000) := rfl
@[simp] theorem lookup_literalP_6_9 : literalP (3, 0) (4, 1) = (-109 / 250000) := rfl
@[simp] theorem lookup_literalP_6_10 : literalP (3, 0) (5, 0) = (-1339039 / 25000000) := rfl
@[simp] theorem lookup_literalP_6_11 : literalP (3, 0) (5, 1) = (-31717 / 20000000) := rfl
@[simp] theorem lookup_literalP_6_12 : literalP (3, 0) (6, 0) = (31843 / 1562500) := rfl
@[simp] theorem lookup_literalP_6_13 : literalP (3, 0) (6, 1) = (50567 / 25000000) := rfl
@[simp] theorem lookup_literalP_7_0 : literalP (3, 1) (0, 0) = (559937 / 50000000) := rfl
@[simp] theorem lookup_literalP_7_1 : literalP (3, 1) (0, 1) = (135991 / 12500000) := rfl
@[simp] theorem lookup_literalP_7_2 : literalP (3, 1) (1, 0) = (-33997 / 50000000) := rfl
@[simp] theorem lookup_literalP_7_3 : literalP (3, 1) (1, 1) = (-103183 / 5000000) := rfl
@[simp] theorem lookup_literalP_7_4 : literalP (3, 1) (2, 0) = (-114797 / 50000000) := rfl
@[simp] theorem lookup_literalP_7_5 : literalP (3, 1) (2, 1) = (-773293 / 50000000) := rfl
@[simp] theorem lookup_literalP_7_6 : literalP (3, 1) (3, 0) = (12009 / 20000000) := rfl
@[simp] theorem lookup_literalP_7_7 : literalP (3, 1) (3, 1) = (116489531 / 2000000000) := rfl
@[simp] theorem lookup_literalP_7_8 : literalP (3, 1) (4, 0) = (-200391 / 50000000) := rfl
@[simp] theorem lookup_literalP_7_9 : literalP (3, 1) (4, 1) = (-352457 / 25000000) := rfl
@[simp] theorem lookup_literalP_7_10 : literalP (3, 1) (5, 0) = (-789233 / 50000000) := rfl
@[simp] theorem lookup_literalP_7_11 : literalP (3, 1) (5, 1) = (-601167 / 50000000) := rfl
@[simp] theorem lookup_literalP_7_12 : literalP (3, 1) (6, 0) = (1096917 / 100000000) := rfl
@[simp] theorem lookup_literalP_7_13 : literalP (3, 1) (6, 1) = (229263 / 50000000) := rfl
@[simp] theorem lookup_literalP_8_0 : literalP (4, 0) (0, 0) = (71489 / 100000000) := rfl
@[simp] theorem lookup_literalP_8_1 : literalP (4, 0) (0, 1) = (4291 / 12500000) := rfl
@[simp] theorem lookup_literalP_8_2 : literalP (4, 0) (1, 0) = (3861663 / 100000000) := rfl
@[simp] theorem lookup_literalP_8_3 : literalP (4, 0) (1, 1) = (53053511 / 2000000000) := rfl
@[simp] theorem lookup_literalP_8_4 : literalP (4, 0) (2, 0) = (-7541479 / 100000000) := rfl
@[simp] theorem lookup_literalP_8_5 : literalP (4, 0) (2, 1) = (-1099567 / 50000000) := rfl
@[simp] theorem lookup_literalP_8_6 : literalP (4, 0) (3, 0) = (-73531 / 2000000) := rfl
@[simp] theorem lookup_literalP_8_7 : literalP (4, 0) (3, 1) = (-200391 / 50000000) := rfl
@[simp] theorem lookup_literalP_8_8 : literalP (4, 0) (4, 0) = (2902601 / 25000000) := rfl
@[simp] theorem lookup_literalP_8_9 : literalP (4, 0) (4, 1) = (-71663 / 25000000) := rfl
@[simp] theorem lookup_literalP_8_10 : literalP (4, 0) (5, 0) = (-20759 / 1000000) := rfl
@[simp] theorem lookup_literalP_8_11 : literalP (4, 0) (5, 1) = (72599 / 25000000) := rfl
@[simp] theorem lookup_literalP_8_12 : literalP (4, 0) (6, 0) = (-2249627 / 100000000) := rfl
@[simp] theorem lookup_literalP_8_13 : literalP (4, 0) (6, 1) = (136597 / 100000000) := rfl
@[simp] theorem lookup_literalP_9_0 : literalP (4, 1) (0, 0) = (-7529 / 781250) := rfl
@[simp] theorem lookup_literalP_9_1 : literalP (4, 1) (0, 1) = (-1119817 / 100000000) := rfl
@[simp] theorem lookup_literalP_9_2 : literalP (4, 1) (1, 0) = (707927 / 50000000) := rfl
@[simp] theorem lookup_literalP_9_3 : literalP (4, 1) (1, 1) = (1034771 / 100000000) := rfl
@[simp] theorem lookup_literalP_9_4 : literalP (4, 1) (2, 0) = (-33957 / 50000000) := rfl
@[simp] theorem lookup_literalP_9_5 : literalP (4, 1) (2, 1) = (-1642681 / 100000000) := rfl
@[simp] theorem lookup_literalP_9_6 : literalP (4, 1) (3, 0) = (-109 / 250000) := rfl
@[simp] theorem lookup_literalP_9_7 : literalP (4, 1) (3, 1) = (-352457 / 25000000) := rfl
@[simp] theorem lookup_literalP_9_8 : literalP (4, 1) (4, 0) = (-71663 / 25000000) := rfl
@[simp] theorem lookup_literalP_9_9 : literalP (4, 1) (4, 1) = (14065111 / 400000000) := rfl
@[simp] theorem lookup_literalP_9_10 : literalP (4, 1) (5, 0) = (239937 / 100000000) := rfl
@[simp] theorem lookup_literalP_9_11 : literalP (4, 1) (5, 1) = (-490729 / 50000000) := rfl
@[simp] theorem lookup_literalP_9_12 : literalP (4, 1) (6, 0) = (-293913 / 100000000) := rfl
@[simp] theorem lookup_literalP_9_13 : literalP (4, 1) (6, 1) = (-200007 / 50000000) := rfl
@[simp] theorem lookup_literalP_10_0 : literalP (5, 0) (0, 0) = (-169547 / 100000000) := rfl
@[simp] theorem lookup_literalP_10_1 : literalP (5, 0) (0, 1) = (-11031 / 50000000) := rfl
@[simp] theorem lookup_literalP_10_2 : literalP (5, 0) (1, 0) = (93007 / 100000000) := rfl
@[simp] theorem lookup_literalP_10_3 : literalP (5, 0) (1, 1) = (142429 / 100000000) := rfl
@[simp] theorem lookup_literalP_10_4 : literalP (5, 0) (2, 0) = (728037 / 25000000) := rfl
@[simp] theorem lookup_literalP_10_5 : literalP (5, 0) (2, 1) = (3538611 / 200000000) := rfl
@[simp] theorem lookup_literalP_10_6 : literalP (5, 0) (3, 0) = (-1339039 / 25000000) := rfl
@[simp] theorem lookup_literalP_10_7 : literalP (5, 0) (3, 1) = (-789233 / 50000000) := rfl
@[simp] theorem lookup_literalP_10_8 : literalP (5, 0) (4, 0) = (-20759 / 1000000) := rfl
@[simp] theorem lookup_literalP_10_9 : literalP (5, 0) (4, 1) = (239937 / 100000000) := rfl
@[simp] theorem lookup_literalP_10_10 : literalP (5, 0) (5, 0) = (7684479 / 100000000) := rfl
@[simp] theorem lookup_literalP_10_11 : literalP (5, 0) (5, 1) = (-1003 / 1000000) := rfl
@[simp] theorem lookup_literalP_10_12 : literalP (5, 0) (6, 0) = (-3088031 / 100000000) := rfl
@[simp] theorem lookup_literalP_10_13 : literalP (5, 0) (6, 1) = (67841 / 50000000) := rfl
@[simp] theorem lookup_literalP_11_0 : literalP (5, 1) (0, 0) = (433341 / 100000000) := rfl
@[simp] theorem lookup_literalP_11_1 : literalP (5, 1) (0, 1) = (34667 / 12500000) := rfl
@[simp] theorem lookup_literalP_11_2 : literalP (5, 1) (1, 0) = (-1173043 / 100000000) := rfl
@[simp] theorem lookup_literalP_11_3 : literalP (5, 1) (1, 1) = (-157979 / 50000000) := rfl
@[simp] theorem lookup_literalP_11_4 : literalP (5, 1) (2, 0) = (228523 / 25000000) := rfl
@[simp] theorem lookup_literalP_11_5 : literalP (5, 1) (2, 1) = (777133 / 100000000) := rfl
@[simp] theorem lookup_literalP_11_6 : literalP (5, 1) (3, 0) = (-31717 / 20000000) := rfl
@[simp] theorem lookup_literalP_11_7 : literalP (5, 1) (3, 1) = (-601167 / 50000000) := rfl
@[simp] theorem lookup_literalP_11_8 : literalP (5, 1) (4, 0) = (72599 / 25000000) := rfl
@[simp] theorem lookup_literalP_11_9 : literalP (5, 1) (4, 1) = (-490729 / 50000000) := rfl
@[simp] theorem lookup_literalP_11_10 : literalP (5, 1) (5, 0) = (-1003 / 1000000) := rfl
@[simp] theorem lookup_literalP_11_11 : literalP (5, 1) (5, 1) = (5993669 / 200000000) := rfl
@[simp] theorem lookup_literalP_11_12 : literalP (5, 1) (6, 0) = (-205901 / 100000000) := rfl
@[simp] theorem lookup_literalP_11_13 : literalP (5, 1) (6, 1) = (-210383 / 20000000) := rfl
@[simp] theorem lookup_literalP_12_0 : literalP (6, 0) (0, 0) = (-25009 / 25000000) := rfl
@[simp] theorem lookup_literalP_12_1 : literalP (6, 0) (0, 1) = (-2881 / 50000000) := rfl
@[simp] theorem lookup_literalP_12_2 : literalP (6, 0) (1, 0) = (779 / 100000000) := rfl
@[simp] theorem lookup_literalP_12_3 : literalP (6, 0) (1, 1) = (-185967 / 50000000) := rfl
@[simp] theorem lookup_literalP_12_4 : literalP (6, 0) (2, 0) = (17767 / 10000000) := rfl
@[simp] theorem lookup_literalP_12_5 : literalP (6, 0) (2, 1) = (-114929 / 100000000) := rfl
@[simp] theorem lookup_literalP_12_6 : literalP (6, 0) (3, 0) = (31843 / 1562500) := rfl
@[simp] theorem lookup_literalP_12_7 : literalP (6, 0) (3, 1) = (1096917 / 100000000) := rfl
@[simp] theorem lookup_literalP_12_8 : literalP (6, 0) (4, 0) = (-2249627 / 100000000) := rfl
@[simp] theorem lookup_literalP_12_9 : literalP (6, 0) (4, 1) = (-293913 / 100000000) := rfl
@[simp] theorem lookup_literalP_12_10 : literalP (6, 0) (5, 0) = (-3088031 / 100000000) := rfl
@[simp] theorem lookup_literalP_12_11 : literalP (6, 0) (5, 1) = (-205901 / 100000000) := rfl
@[simp] theorem lookup_literalP_12_12 : literalP (6, 0) (6, 0) = (3221293 / 100000000) := rfl
@[simp] theorem lookup_literalP_12_13 : literalP (6, 0) (6, 1) = (-52239 / 50000000) := rfl
@[simp] theorem lookup_literalP_13_0 : literalP (6, 1) (0, 0) = (-11583 / 50000000) := rfl
@[simp] theorem lookup_literalP_13_1 : literalP (6, 1) (0, 1) = (-541187 / 100000000) := rfl
@[simp] theorem lookup_literalP_13_2 : literalP (6, 1) (1, 0) = (7727 / 4000000) := rfl
@[simp] theorem lookup_literalP_13_3 : literalP (6, 1) (1, 1) = (91627 / 50000000) := rfl
@[simp] theorem lookup_literalP_13_4 : literalP (6, 1) (2, 0) = (-270039 / 50000000) := rfl
@[simp] theorem lookup_literalP_13_5 : literalP (6, 1) (2, 1) = (-25519 / 50000000) := rfl
@[simp] theorem lookup_literalP_13_6 : literalP (6, 1) (3, 0) = (50567 / 25000000) := rfl
@[simp] theorem lookup_literalP_13_7 : literalP (6, 1) (3, 1) = (229263 / 50000000) := rfl
@[simp] theorem lookup_literalP_13_8 : literalP (6, 1) (4, 0) = (136597 / 100000000) := rfl
@[simp] theorem lookup_literalP_13_9 : literalP (6, 1) (4, 1) = (-200007 / 50000000) := rfl
@[simp] theorem lookup_literalP_13_10 : literalP (6, 1) (5, 0) = (67841 / 50000000) := rfl
@[simp] theorem lookup_literalP_13_11 : literalP (6, 1) (5, 1) = (-210383 / 20000000) := rfl
@[simp] theorem lookup_literalP_13_12 : literalP (6, 1) (6, 0) = (-52239 / 50000000) := rfl
@[simp] theorem lookup_literalP_13_13 : literalP (6, 1) (6, 1) = (26132923 / 2000000000) := rfl
@[simp] theorem lookup_literalMuF_0_0 : literalMu .F none none = 0 := rfl
@[simp] theorem lookup_literalMuF_0_1 : literalMu .F none (some 0) = (145837 / 12500000) := rfl
@[simp] theorem lookup_literalMuF_0_2 : literalMu .F none (some 1) = (734789 / 50000000) := rfl
@[simp] theorem lookup_literalMuF_0_3 : literalMu .F none (some 2) = (128897 / 25000000) := rfl
@[simp] theorem lookup_literalMuF_0_4 : literalMu .F none (some 3) = (263253 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_0_5 : literalMu .F none (some 4) = (34783 / 20000000) := rfl
@[simp] theorem lookup_literalMuF_0_6 : literalMu .F none (some 5) = (67871 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_1_0 : literalMu .F (some 0) none = (1460443 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_1_1 : literalMu .F (some 0) (some 0) = 0 := rfl
@[simp] theorem lookup_literalMuF_1_2 : literalMu .F (some 0) (some 1) = (1240119 / 50000000) := rfl
@[simp] theorem lookup_literalMuF_1_3 : literalMu .F (some 0) (some 2) = (231319 / 50000000) := rfl
@[simp] theorem lookup_literalMuF_1_4 : literalMu .F (some 0) (some 3) = (11499 / 10000000) := rfl
@[simp] theorem lookup_literalMuF_1_5 : literalMu .F (some 0) (some 4) = (79063 / 50000000) := rfl
@[simp] theorem lookup_literalMuF_1_6 : literalMu .F (some 0) (some 5) = (36459 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_2_0 : literalMu .F (some 1) none = (668329 / 50000000) := rfl
@[simp] theorem lookup_literalMuF_2_1 : literalMu .F (some 1) (some 0) = (2051439 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_2_2 : literalMu .F (some 1) (some 1) = 0 := rfl
@[simp] theorem lookup_literalMuF_2_3 : literalMu .F (some 1) (some 2) = (697063 / 50000000) := rfl
@[simp] theorem lookup_literalMuF_2_4 : literalMu .F (some 1) (some 3) = (609677 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_2_5 : literalMu .F (some 1) (some 4) = (356593 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_2_6 : literalMu .F (some 1) (some 5) = (30407 / 25000000) := rfl
@[simp] theorem lookup_literalMuF_3_0 : literalMu .F (some 2) none = (257641 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_3_1 : literalMu .F (some 2) (some 0) = (469719 / 50000000) := rfl
@[simp] theorem lookup_literalMuF_3_2 : literalMu .F (some 2) (some 1) = (238363 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_3_3 : literalMu .F (some 2) (some 2) = 0 := rfl
@[simp] theorem lookup_literalMuF_3_4 : literalMu .F (some 2) (some 3) = (40261 / 20000000) := rfl
@[simp] theorem lookup_literalMuF_3_5 : literalMu .F (some 2) (some 4) = (167921 / 50000000) := rfl
@[simp] theorem lookup_literalMuF_3_6 : literalMu .F (some 2) (some 5) = (7321 / 10000000) := rfl
@[simp] theorem lookup_literalMuF_4_0 : literalMu .F (some 3) none = (118427 / 50000000) := rfl
@[simp] theorem lookup_literalMuF_4_1 : literalMu .F (some 3) (some 0) = (214949 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_4_2 : literalMu .F (some 3) (some 1) = (339277 / 25000000) := rfl
@[simp] theorem lookup_literalMuF_4_3 : literalMu .F (some 3) (some 2) = (9797 / 20000000) := rfl
@[simp] theorem lookup_literalMuF_4_4 : literalMu .F (some 3) (some 3) = 0 := rfl
@[simp] theorem lookup_literalMuF_4_5 : literalMu .F (some 3) (some 4) = (69447 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_4_6 : literalMu .F (some 3) (some 5) = (267 / 200000) := rfl
@[simp] theorem lookup_literalMuF_5_0 : literalMu .F (some 4) none = (127149 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_5_1 : literalMu .F (some 4) (some 0) = (146383 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_5_2 : literalMu .F (some 4) (some 1) = (14523 / 20000000) := rfl
@[simp] theorem lookup_literalMuF_5_3 : literalMu .F (some 4) (some 2) = (124047 / 50000000) := rfl
@[simp] theorem lookup_literalMuF_5_4 : literalMu .F (some 4) (some 3) = (18991 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_5_5 : literalMu .F (some 4) (some 4) = 0 := rfl
@[simp] theorem lookup_literalMuF_5_6 : literalMu .F (some 4) (some 5) = (3289 / 20000000) := rfl
@[simp] theorem lookup_literalMuF_6_0 : literalMu .F (some 5) none = (107557 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_6_1 : literalMu .F (some 5) (some 0) = (106919 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_6_2 : literalMu .F (some 5) (some 1) = (165149 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_6_3 : literalMu .F (some 5) (some 2) = (4611 / 20000000) := rfl
@[simp] theorem lookup_literalMuF_6_4 : literalMu .F (some 5) (some 3) = (148111 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_6_5 : literalMu .F (some 5) (some 4) = (10943 / 100000000) := rfl
@[simp] theorem lookup_literalMuF_6_6 : literalMu .F (some 5) (some 5) = 0 := rfl
@[simp] theorem lookup_literalMuJ_0_0 : literalMu .J none none = 0 := rfl
@[simp] theorem lookup_literalMuJ_0_1 : literalMu .J none (some 0) = (654827 / 25000000) := rfl
@[simp] theorem lookup_literalMuJ_0_2 : literalMu .J none (some 1) = (595937 / 100000000) := rfl
@[simp] theorem lookup_literalMuJ_0_3 : literalMu .J none (some 2) = (245913 / 100000000) := rfl
@[simp] theorem lookup_literalMuJ_0_4 : literalMu .J none (some 3) = (33741 / 25000000) := rfl
@[simp] theorem lookup_literalMuJ_0_5 : literalMu .J none (some 4) = (16 / 15625) := rfl
@[simp] theorem lookup_literalMuJ_0_6 : literalMu .J none (some 5) = (78919 / 100000000) := rfl
@[simp] theorem lookup_literalMuJ_1_0 : literalMu .J (some 0) none = (435519 / 20000000) := rfl
@[simp] theorem lookup_literalMuJ_1_1 : literalMu .J (some 0) (some 0) = 0 := rfl
@[simp] theorem lookup_literalMuJ_1_2 : literalMu .J (some 0) (some 1) = (686059 / 50000000) := rfl
@[simp] theorem lookup_literalMuJ_1_3 : literalMu .J (some 0) (some 2) = (668847 / 100000000) := rfl
@[simp] theorem lookup_literalMuJ_1_4 : literalMu .J (some 0) (some 3) = (123919 / 50000000) := rfl
@[simp] theorem lookup_literalMuJ_1_5 : literalMu .J (some 0) (some 4) = (147529 / 100000000) := rfl
@[simp] theorem lookup_literalMuJ_1_6 : literalMu .J (some 0) (some 5) = (112453 / 100000000) := rfl
@[simp] theorem lookup_literalMuJ_2_0 : literalMu .J (some 1) none = (586061 / 50000000) := rfl
@[simp] theorem lookup_literalMuJ_2_1 : literalMu .J (some 1) (some 0) = (5546507 / 25000000) := rfl
@[simp] theorem lookup_literalMuJ_2_2 : literalMu .J (some 1) (some 1) = 0 := rfl
@[simp] theorem lookup_literalMuJ_2_3 : literalMu .J (some 1) (some 2) = (1435357 / 100000000) := rfl
@[simp] theorem lookup_literalMuJ_2_4 : literalMu .J (some 1) (some 3) = (464203 / 100000000) := rfl
@[simp] theorem lookup_literalMuJ_2_5 : literalMu .J (some 1) (some 4) = (14417 / 6250000) := rfl
@[simp] theorem lookup_literalMuJ_2_6 : literalMu .J (some 1) (some 5) = (15829 / 12500000) := rfl
@[simp] theorem lookup_literalMuJ_3_0 : literalMu .J (some 2) none = (33697 / 20000000) := rfl
@[simp] theorem lookup_literalMuJ_3_1 : literalMu .J (some 2) (some 0) = (31903 / 12500000) := rfl
@[simp] theorem lookup_literalMuJ_3_2 : literalMu .J (some 2) (some 1) = (299843 / 100000000) := rfl
@[simp] theorem lookup_literalMuJ_3_3 : literalMu .J (some 2) (some 2) = 0 := rfl
@[simp] theorem lookup_literalMuJ_3_4 : literalMu .J (some 2) (some 3) = (323939 / 50000000) := rfl
@[simp] theorem lookup_literalMuJ_3_5 : literalMu .J (some 2) (some 4) = (359011 / 100000000) := rfl
@[simp] theorem lookup_literalMuJ_3_6 : literalMu .J (some 2) (some 5) = (6607 / 4000000) := rfl
@[simp] theorem lookup_literalMuJ_4_0 : literalMu .J (some 3) none = (3479 / 5000000) := rfl
@[simp] theorem lookup_literalMuJ_4_1 : literalMu .J (some 3) (some 0) = (91667 / 100000000) := rfl
@[simp] theorem lookup_literalMuJ_4_2 : literalMu .J (some 3) (some 1) = (163 / 160000) := rfl
@[simp] theorem lookup_literalMuJ_4_3 : literalMu .J (some 3) (some 2) = (153361 / 100000000) := rfl
@[simp] theorem lookup_literalMuJ_4_4 : literalMu .J (some 3) (some 3) = 0 := rfl
@[simp] theorem lookup_literalMuJ_4_5 : literalMu .J (some 3) (some 4) = (2691 / 800000) := rfl
@[simp] theorem lookup_literalMuJ_4_6 : literalMu .J (some 3) (some 5) = (44551 / 20000000) := rfl
@[simp] theorem lookup_literalMuJ_5_0 : literalMu .J (some 4) none = (2459 / 6250000) := rfl
@[simp] theorem lookup_literalMuJ_5_1 : literalMu .J (some 4) (some 0) = (23017 / 50000000) := rfl
@[simp] theorem lookup_literalMuJ_5_2 : literalMu .J (some 4) (some 1) = (1289 / 2500000) := rfl
@[simp] theorem lookup_literalMuJ_5_3 : literalMu .J (some 4) (some 2) = (51089 / 50000000) := rfl
@[simp] theorem lookup_literalMuJ_5_4 : literalMu .J (some 4) (some 3) = (27333 / 20000000) := rfl
@[simp] theorem lookup_literalMuJ_5_5 : literalMu .J (some 4) (some 4) = 0 := rfl
@[simp] theorem lookup_literalMuJ_5_6 : literalMu .J (some 4) (some 5) = (134963 / 100000000) := rfl
@[simp] theorem lookup_literalMuJ_6_0 : literalMu .J (some 5) none = (4929 / 25000000) := rfl
@[simp] theorem lookup_literalMuJ_6_1 : literalMu .J (some 5) (some 0) = (22901 / 100000000) := rfl
@[simp] theorem lookup_literalMuJ_6_2 : literalMu .J (some 5) (some 1) = (2383 / 10000000) := rfl
@[simp] theorem lookup_literalMuJ_6_3 : literalMu .J (some 5) (some 2) = (16357 / 50000000) := rfl
@[simp] theorem lookup_literalMuJ_6_4 : literalMu .J (some 5) (some 3) = (43409 / 50000000) := rfl
@[simp] theorem lookup_literalMuJ_6_5 : literalMu .J (some 5) (some 4) = (77509 / 100000000) := rfl
@[simp] theorem lookup_literalMuJ_6_6 : literalMu .J (some 5) (some 5) = 0 := rfl
end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseTwo.Lower.MatrixBridge
