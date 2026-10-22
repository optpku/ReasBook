/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalReconstruction

@[expose] public section

namespace ADMM.FiniteMemory.Reconstruction.MatrixAssembly

@[simp] theorem matrixFinSucc_1_0 : Fin.succ (0 : Fin 1) = (1 : Fin 2) := rfl
@[simp] theorem matrixFinCastSucc_1_0 : Fin.castSucc (0 : Fin 1) = (0 : Fin 2) := rfl
@[simp] theorem matrixFinSucc_2_0 : Fin.succ (0 : Fin 2) = (1 : Fin 3) := rfl
@[simp] theorem matrixFinCastSucc_2_0 : Fin.castSucc (0 : Fin 2) = (0 : Fin 3) := rfl
@[simp] theorem matrixFinSucc_2_1 : Fin.succ (1 : Fin 2) = (2 : Fin 3) := rfl
@[simp] theorem matrixFinCastSucc_2_1 : Fin.castSucc (1 : Fin 2) = (1 : Fin 3) := rfl
@[simp] theorem matrixFinSucc_3_0 : Fin.succ (0 : Fin 3) = (1 : Fin 4) := rfl
@[simp] theorem matrixFinCastSucc_3_0 : Fin.castSucc (0 : Fin 3) = (0 : Fin 4) := rfl
@[simp] theorem matrixFinSucc_3_1 : Fin.succ (1 : Fin 3) = (2 : Fin 4) := rfl
@[simp] theorem matrixFinCastSucc_3_1 : Fin.castSucc (1 : Fin 3) = (1 : Fin 4) := rfl
@[simp] theorem matrixFinSucc_3_2 : Fin.succ (2 : Fin 3) = (3 : Fin 4) := rfl
@[simp] theorem matrixFinCastSucc_3_2 : Fin.castSucc (2 : Fin 3) = (2 : Fin 4) := rfl
@[simp] theorem matrixFinSucc_4_0 : Fin.succ (0 : Fin 4) = (1 : Fin 5) := rfl
@[simp] theorem matrixFinCastSucc_4_0 : Fin.castSucc (0 : Fin 4) = (0 : Fin 5) := rfl
@[simp] theorem matrixFinSucc_4_1 : Fin.succ (1 : Fin 4) = (2 : Fin 5) := rfl
@[simp] theorem matrixFinCastSucc_4_1 : Fin.castSucc (1 : Fin 4) = (1 : Fin 5) := rfl
@[simp] theorem matrixFinSucc_4_2 : Fin.succ (2 : Fin 4) = (3 : Fin 5) := rfl
@[simp] theorem matrixFinCastSucc_4_2 : Fin.castSucc (2 : Fin 4) = (2 : Fin 5) := rfl
@[simp] theorem matrixFinSucc_4_3 : Fin.succ (3 : Fin 4) = (4 : Fin 5) := rfl
@[simp] theorem matrixFinCastSucc_4_3 : Fin.castSucc (3 : Fin 4) = (3 : Fin 5) := rfl
@[simp] theorem matrixFinSucc_5_0 : Fin.succ (0 : Fin 5) = (1 : Fin 6) := rfl
@[simp] theorem matrixFinCastSucc_5_0 : Fin.castSucc (0 : Fin 5) = (0 : Fin 6) := rfl
@[simp] theorem matrixFinSucc_5_1 : Fin.succ (1 : Fin 5) = (2 : Fin 6) := rfl
@[simp] theorem matrixFinCastSucc_5_1 : Fin.castSucc (1 : Fin 5) = (1 : Fin 6) := rfl
@[simp] theorem matrixFinSucc_5_2 : Fin.succ (2 : Fin 5) = (3 : Fin 6) := rfl
@[simp] theorem matrixFinCastSucc_5_2 : Fin.castSucc (2 : Fin 5) = (2 : Fin 6) := rfl
@[simp] theorem matrixFinSucc_5_3 : Fin.succ (3 : Fin 5) = (4 : Fin 6) := rfl
@[simp] theorem matrixFinCastSucc_5_3 : Fin.castSucc (3 : Fin 5) = (3 : Fin 6) := rfl
@[simp] theorem matrixFinSucc_5_4 : Fin.succ (4 : Fin 5) = (5 : Fin 6) := rfl
@[simp] theorem matrixFinCastSucc_5_4 : Fin.castSucc (4 : Fin 5) = (4 : Fin 6) := rfl
@[simp] theorem matrixFinSucc_6_0 : Fin.succ (0 : Fin 6) = (1 : Fin 7) := rfl
@[simp] theorem matrixFinCastSucc_6_0 : Fin.castSucc (0 : Fin 6) = (0 : Fin 7) := rfl
@[simp] theorem matrixFinSucc_6_1 : Fin.succ (1 : Fin 6) = (2 : Fin 7) := rfl
@[simp] theorem matrixFinCastSucc_6_1 : Fin.castSucc (1 : Fin 6) = (1 : Fin 7) := rfl
@[simp] theorem matrixFinSucc_6_2 : Fin.succ (2 : Fin 6) = (3 : Fin 7) := rfl
@[simp] theorem matrixFinCastSucc_6_2 : Fin.castSucc (2 : Fin 6) = (2 : Fin 7) := rfl
@[simp] theorem matrixFinSucc_6_3 : Fin.succ (3 : Fin 6) = (4 : Fin 7) := rfl
@[simp] theorem matrixFinCastSucc_6_3 : Fin.castSucc (3 : Fin 6) = (3 : Fin 7) := rfl
@[simp] theorem matrixFinSucc_6_4 : Fin.succ (4 : Fin 6) = (5 : Fin 7) := rfl
@[simp] theorem matrixFinCastSucc_6_4 : Fin.castSucc (4 : Fin 6) = (4 : Fin 7) := rfl
@[simp] theorem matrixFinSucc_6_5 : Fin.succ (5 : Fin 6) = (6 : Fin 7) := rfl
@[simp] theorem matrixFinCastSucc_6_5 : Fin.castSucc (5 : Fin 6) = (5 : Fin 7) := rfl
@[simp] theorem matrixFinSucc_7_0 : Fin.succ (0 : Fin 7) = (1 : Fin 8) := rfl
@[simp] theorem matrixFinCastSucc_7_0 : Fin.castSucc (0 : Fin 7) = (0 : Fin 8) := rfl
@[simp] theorem matrixFinSucc_7_1 : Fin.succ (1 : Fin 7) = (2 : Fin 8) := rfl
@[simp] theorem matrixFinCastSucc_7_1 : Fin.castSucc (1 : Fin 7) = (1 : Fin 8) := rfl
@[simp] theorem matrixFinSucc_7_2 : Fin.succ (2 : Fin 7) = (3 : Fin 8) := rfl
@[simp] theorem matrixFinCastSucc_7_2 : Fin.castSucc (2 : Fin 7) = (2 : Fin 8) := rfl
@[simp] theorem matrixFinSucc_7_3 : Fin.succ (3 : Fin 7) = (4 : Fin 8) := rfl
@[simp] theorem matrixFinCastSucc_7_3 : Fin.castSucc (3 : Fin 7) = (3 : Fin 8) := rfl
@[simp] theorem matrixFinSucc_7_4 : Fin.succ (4 : Fin 7) = (5 : Fin 8) := rfl
@[simp] theorem matrixFinCastSucc_7_4 : Fin.castSucc (4 : Fin 7) = (4 : Fin 8) := rfl
@[simp] theorem matrixFinSucc_7_5 : Fin.succ (5 : Fin 7) = (6 : Fin 8) := rfl
@[simp] theorem matrixFinCastSucc_7_5 : Fin.castSucc (5 : Fin 7) = (5 : Fin 8) := rfl
@[simp] theorem matrixFinSucc_7_6 : Fin.succ (6 : Fin 7) = (7 : Fin 8) := rfl
@[simp] theorem matrixFinCastSucc_7_6 : Fin.castSucc (6 : Fin 7) = (6 : Fin 8) := rfl
@[simp] theorem matrixFinSucc_8_0 : Fin.succ (0 : Fin 8) = (1 : Fin 9) := rfl
@[simp] theorem matrixFinCastSucc_8_0 : Fin.castSucc (0 : Fin 8) = (0 : Fin 9) := rfl
@[simp] theorem matrixFinSucc_8_1 : Fin.succ (1 : Fin 8) = (2 : Fin 9) := rfl
@[simp] theorem matrixFinCastSucc_8_1 : Fin.castSucc (1 : Fin 8) = (1 : Fin 9) := rfl
@[simp] theorem matrixFinSucc_8_2 : Fin.succ (2 : Fin 8) = (3 : Fin 9) := rfl
@[simp] theorem matrixFinCastSucc_8_2 : Fin.castSucc (2 : Fin 8) = (2 : Fin 9) := rfl
@[simp] theorem matrixFinSucc_8_3 : Fin.succ (3 : Fin 8) = (4 : Fin 9) := rfl
@[simp] theorem matrixFinCastSucc_8_3 : Fin.castSucc (3 : Fin 8) = (3 : Fin 9) := rfl
@[simp] theorem matrixFinSucc_8_4 : Fin.succ (4 : Fin 8) = (5 : Fin 9) := rfl
@[simp] theorem matrixFinCastSucc_8_4 : Fin.castSucc (4 : Fin 8) = (4 : Fin 9) := rfl
@[simp] theorem matrixFinSucc_8_5 : Fin.succ (5 : Fin 8) = (6 : Fin 9) := rfl
@[simp] theorem matrixFinCastSucc_8_5 : Fin.castSucc (5 : Fin 8) = (5 : Fin 9) := rfl
@[simp] theorem matrixFinSucc_8_6 : Fin.succ (6 : Fin 8) = (7 : Fin 9) := rfl
@[simp] theorem matrixFinCastSucc_8_6 : Fin.castSucc (6 : Fin 8) = (6 : Fin 9) := rfl
@[simp] theorem matrixFinSucc_8_7 : Fin.succ (7 : Fin 8) = (8 : Fin 9) := rfl
@[simp] theorem matrixFinCastSucc_8_7 : Fin.castSucc (7 : Fin 8) = (7 : Fin 9) := rfl
@[simp] theorem matrixFinSucc_9_0 : Fin.succ (0 : Fin 9) = (1 : Fin 10) := rfl
@[simp] theorem matrixFinCastSucc_9_0 : Fin.castSucc (0 : Fin 9) = (0 : Fin 10) := rfl
@[simp] theorem matrixFinSucc_9_1 : Fin.succ (1 : Fin 9) = (2 : Fin 10) := rfl
@[simp] theorem matrixFinCastSucc_9_1 : Fin.castSucc (1 : Fin 9) = (1 : Fin 10) := rfl
@[simp] theorem matrixFinSucc_9_2 : Fin.succ (2 : Fin 9) = (3 : Fin 10) := rfl
@[simp] theorem matrixFinCastSucc_9_2 : Fin.castSucc (2 : Fin 9) = (2 : Fin 10) := rfl
@[simp] theorem matrixFinSucc_9_3 : Fin.succ (3 : Fin 9) = (4 : Fin 10) := rfl
@[simp] theorem matrixFinCastSucc_9_3 : Fin.castSucc (3 : Fin 9) = (3 : Fin 10) := rfl
@[simp] theorem matrixFinSucc_9_4 : Fin.succ (4 : Fin 9) = (5 : Fin 10) := rfl
@[simp] theorem matrixFinCastSucc_9_4 : Fin.castSucc (4 : Fin 9) = (4 : Fin 10) := rfl
@[simp] theorem matrixFinSucc_9_5 : Fin.succ (5 : Fin 9) = (6 : Fin 10) := rfl
@[simp] theorem matrixFinCastSucc_9_5 : Fin.castSucc (5 : Fin 9) = (5 : Fin 10) := rfl
@[simp] theorem matrixFinSucc_9_6 : Fin.succ (6 : Fin 9) = (7 : Fin 10) := rfl
@[simp] theorem matrixFinCastSucc_9_6 : Fin.castSucc (6 : Fin 9) = (6 : Fin 10) := rfl
@[simp] theorem matrixFinSucc_9_7 : Fin.succ (7 : Fin 9) = (8 : Fin 10) := rfl
@[simp] theorem matrixFinCastSucc_9_7 : Fin.castSucc (7 : Fin 9) = (7 : Fin 10) := rfl
@[simp] theorem matrixFinSucc_9_8 : Fin.succ (8 : Fin 9) = (9 : Fin 10) := rfl
@[simp] theorem matrixFinCastSucc_9_8 : Fin.castSucc (8 : Fin 9) = (8 : Fin 10) := rfl
@[simp] theorem matrixFinSucc_10_0 : Fin.succ (0 : Fin 10) = (1 : Fin 11) := rfl
@[simp] theorem matrixFinCastSucc_10_0 : Fin.castSucc (0 : Fin 10) = (0 : Fin 11) := rfl
@[simp] theorem matrixFinSucc_10_1 : Fin.succ (1 : Fin 10) = (2 : Fin 11) := rfl
@[simp] theorem matrixFinCastSucc_10_1 : Fin.castSucc (1 : Fin 10) = (1 : Fin 11) := rfl
@[simp] theorem matrixFinSucc_10_2 : Fin.succ (2 : Fin 10) = (3 : Fin 11) := rfl
@[simp] theorem matrixFinCastSucc_10_2 : Fin.castSucc (2 : Fin 10) = (2 : Fin 11) := rfl
@[simp] theorem matrixFinSucc_10_3 : Fin.succ (3 : Fin 10) = (4 : Fin 11) := rfl
@[simp] theorem matrixFinCastSucc_10_3 : Fin.castSucc (3 : Fin 10) = (3 : Fin 11) := rfl
@[simp] theorem matrixFinSucc_10_4 : Fin.succ (4 : Fin 10) = (5 : Fin 11) := rfl
@[simp] theorem matrixFinCastSucc_10_4 : Fin.castSucc (4 : Fin 10) = (4 : Fin 11) := rfl
@[simp] theorem matrixFinSucc_10_5 : Fin.succ (5 : Fin 10) = (6 : Fin 11) := rfl
@[simp] theorem matrixFinCastSucc_10_5 : Fin.castSucc (5 : Fin 10) = (5 : Fin 11) := rfl
@[simp] theorem matrixFinSucc_10_6 : Fin.succ (6 : Fin 10) = (7 : Fin 11) := rfl
@[simp] theorem matrixFinCastSucc_10_6 : Fin.castSucc (6 : Fin 10) = (6 : Fin 11) := rfl
@[simp] theorem matrixFinSucc_10_7 : Fin.succ (7 : Fin 10) = (8 : Fin 11) := rfl
@[simp] theorem matrixFinCastSucc_10_7 : Fin.castSucc (7 : Fin 10) = (7 : Fin 11) := rfl
@[simp] theorem matrixFinSucc_10_8 : Fin.succ (8 : Fin 10) = (9 : Fin 11) := rfl
@[simp] theorem matrixFinCastSucc_10_8 : Fin.castSucc (8 : Fin 10) = (8 : Fin 11) := rfl
@[simp] theorem matrixFinSucc_10_9 : Fin.succ (9 : Fin 10) = (10 : Fin 11) := rfl
@[simp] theorem matrixFinCastSucc_10_9 : Fin.castSucc (9 : Fin 10) = (9 : Fin 11) := rfl

@[simp] theorem matrixFinMk_1_0 (h : 0 < 1) : (⟨0, h⟩ : Fin 1) = 0 := rfl
@[simp] theorem matrixFinMk_2_0 (h : 0 < 2) : (⟨0, h⟩ : Fin 2) = 0 := rfl
@[simp] theorem matrixFinMk_2_1 (h : 1 < 2) : (⟨1, h⟩ : Fin 2) = 1 := rfl
@[simp] theorem matrixFinMk_3_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem matrixFinMk_3_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem matrixFinMk_3_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem matrixFinMk_4_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem matrixFinMk_4_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem matrixFinMk_4_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem matrixFinMk_4_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem matrixFinMk_5_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem matrixFinMk_5_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem matrixFinMk_5_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem matrixFinMk_5_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem matrixFinMk_5_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
@[simp] theorem matrixFinMk_6_0 (h : 0 < 6) : (⟨0, h⟩ : Fin 6) = 0 := rfl
@[simp] theorem matrixFinMk_6_1 (h : 1 < 6) : (⟨1, h⟩ : Fin 6) = 1 := rfl
@[simp] theorem matrixFinMk_6_2 (h : 2 < 6) : (⟨2, h⟩ : Fin 6) = 2 := rfl
@[simp] theorem matrixFinMk_6_3 (h : 3 < 6) : (⟨3, h⟩ : Fin 6) = 3 := rfl
@[simp] theorem matrixFinMk_6_4 (h : 4 < 6) : (⟨4, h⟩ : Fin 6) = 4 := rfl
@[simp] theorem matrixFinMk_6_5 (h : 5 < 6) : (⟨5, h⟩ : Fin 6) = 5 := rfl
@[simp] theorem matrixFinMk_7_0 (h : 0 < 7) : (⟨0, h⟩ : Fin 7) = 0 := rfl
@[simp] theorem matrixFinMk_7_1 (h : 1 < 7) : (⟨1, h⟩ : Fin 7) = 1 := rfl
@[simp] theorem matrixFinMk_7_2 (h : 2 < 7) : (⟨2, h⟩ : Fin 7) = 2 := rfl
@[simp] theorem matrixFinMk_7_3 (h : 3 < 7) : (⟨3, h⟩ : Fin 7) = 3 := rfl
@[simp] theorem matrixFinMk_7_4 (h : 4 < 7) : (⟨4, h⟩ : Fin 7) = 4 := rfl
@[simp] theorem matrixFinMk_7_5 (h : 5 < 7) : (⟨5, h⟩ : Fin 7) = 5 := rfl
@[simp] theorem matrixFinMk_7_6 (h : 6 < 7) : (⟨6, h⟩ : Fin 7) = 6 := rfl
@[simp] theorem matrixFinMk_8_0 (h : 0 < 8) : (⟨0, h⟩ : Fin 8) = 0 := rfl
@[simp] theorem matrixFinMk_8_1 (h : 1 < 8) : (⟨1, h⟩ : Fin 8) = 1 := rfl
@[simp] theorem matrixFinMk_8_2 (h : 2 < 8) : (⟨2, h⟩ : Fin 8) = 2 := rfl
@[simp] theorem matrixFinMk_8_3 (h : 3 < 8) : (⟨3, h⟩ : Fin 8) = 3 := rfl
@[simp] theorem matrixFinMk_8_4 (h : 4 < 8) : (⟨4, h⟩ : Fin 8) = 4 := rfl
@[simp] theorem matrixFinMk_8_5 (h : 5 < 8) : (⟨5, h⟩ : Fin 8) = 5 := rfl
@[simp] theorem matrixFinMk_8_6 (h : 6 < 8) : (⟨6, h⟩ : Fin 8) = 6 := rfl
@[simp] theorem matrixFinMk_8_7 (h : 7 < 8) : (⟨7, h⟩ : Fin 8) = 7 := rfl
@[simp] theorem matrixFinMk_9_0 (h : 0 < 9) : (⟨0, h⟩ : Fin 9) = 0 := rfl
@[simp] theorem matrixFinMk_9_1 (h : 1 < 9) : (⟨1, h⟩ : Fin 9) = 1 := rfl
@[simp] theorem matrixFinMk_9_2 (h : 2 < 9) : (⟨2, h⟩ : Fin 9) = 2 := rfl
@[simp] theorem matrixFinMk_9_3 (h : 3 < 9) : (⟨3, h⟩ : Fin 9) = 3 := rfl
@[simp] theorem matrixFinMk_9_4 (h : 4 < 9) : (⟨4, h⟩ : Fin 9) = 4 := rfl
@[simp] theorem matrixFinMk_9_5 (h : 5 < 9) : (⟨5, h⟩ : Fin 9) = 5 := rfl
@[simp] theorem matrixFinMk_9_6 (h : 6 < 9) : (⟨6, h⟩ : Fin 9) = 6 := rfl
@[simp] theorem matrixFinMk_9_7 (h : 7 < 9) : (⟨7, h⟩ : Fin 9) = 7 := rfl
@[simp] theorem matrixFinMk_9_8 (h : 8 < 9) : (⟨8, h⟩ : Fin 9) = 8 := rfl
@[simp] theorem matrixFinMk_10_0 (h : 0 < 10) : (⟨0, h⟩ : Fin 10) = 0 := rfl
@[simp] theorem matrixFinMk_10_1 (h : 1 < 10) : (⟨1, h⟩ : Fin 10) = 1 := rfl
@[simp] theorem matrixFinMk_10_2 (h : 2 < 10) : (⟨2, h⟩ : Fin 10) = 2 := rfl
@[simp] theorem matrixFinMk_10_3 (h : 3 < 10) : (⟨3, h⟩ : Fin 10) = 3 := rfl
@[simp] theorem matrixFinMk_10_4 (h : 4 < 10) : (⟨4, h⟩ : Fin 10) = 4 := rfl
@[simp] theorem matrixFinMk_10_5 (h : 5 < 10) : (⟨5, h⟩ : Fin 10) = 5 := rfl
@[simp] theorem matrixFinMk_10_6 (h : 6 < 10) : (⟨6, h⟩ : Fin 10) = 6 := rfl
@[simp] theorem matrixFinMk_10_7 (h : 7 < 10) : (⟨7, h⟩ : Fin 10) = 7 := rfl
@[simp] theorem matrixFinMk_10_8 (h : 8 < 10) : (⟨8, h⟩ : Fin 10) = 8 := rfl
@[simp] theorem matrixFinMk_10_9 (h : 9 < 10) : (⟨9, h⟩ : Fin 10) = 9 := rfl

end ADMM.FiniteMemory.Reconstruction.MatrixAssembly
