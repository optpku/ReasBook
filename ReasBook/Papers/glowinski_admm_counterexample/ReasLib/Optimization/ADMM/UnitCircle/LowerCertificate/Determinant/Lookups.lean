/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.QuotientChecks
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.ChunkLookup

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Determinant

open DeterminantPolynomial

def diagonalTree : LookupTree (List ℤ) := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf diagonalNumeratorsChunk0) (.leaf diagonalNumeratorsChunk1)) (.node 1 (.leaf diagonalNumeratorsChunk2) (.leaf diagonalNumeratorsChunk3))) (.node 2 (.node 1 (.leaf diagonalNumeratorsChunk4) (.leaf diagonalNumeratorsChunk5)) (.node 1 (.leaf diagonalNumeratorsChunk6) (.leaf diagonalNumeratorsChunk7)))) (.node 4 (.node 2 (.node 1 (.leaf diagonalNumeratorsChunk8) (.leaf diagonalNumeratorsChunk9)) (.node 1 (.leaf diagonalNumeratorsChunk10) (.leaf diagonalNumeratorsChunk11))) (.node 2 (.node 1 (.leaf diagonalNumeratorsChunk12) (.leaf diagonalNumeratorsChunk13)) (.node 1 (.leaf diagonalNumeratorsChunk14) (.node 1 (.leaf diagonalNumeratorsChunk15) (.leaf diagonalNumeratorsChunk16))))))

theorem diagonalTree_valid : validChunks diagonalTree := by decide +kernel

theorem diagonalTree_flat : flattenChunks diagonalTree = diagonalNumerators := by
  simp only [diagonalTree, flattenChunks, diagonalNumerators, List.append_assoc]

def diagonalCoefficient (i : ℕ) : ℤ :=
  if i < 513 then chunkLookup diagonalTree i 0 else 0

theorem diagonalCoefficient_eq (i : ℕ) :
    diagonalCoefficient i = diagonalNumerators.getD i 0 := by
  by_cases hi : i < 513
  · rw [diagonalCoefficient, if_pos hi]
    have h := chunkLookup_eq_getD diagonalTree diagonalTree_valid i
      (by rw [diagonalTree_flat, diagonal_length]; exact hi) (0 : ℤ)
    simpa only [diagonalTree_flat] using h
  · rw [diagonalCoefficient, if_neg hi, List.getD_eq_default _ _
      (by rw [diagonal_length]; omega)]

def startSecondTree : LookupTree (List ℤ) := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf startSecondNumeratorsChunk0) (.leaf startSecondNumeratorsChunk1)) (.node 1 (.leaf startSecondNumeratorsChunk2) (.leaf startSecondNumeratorsChunk3))) (.node 2 (.node 1 (.leaf startSecondNumeratorsChunk4) (.leaf startSecondNumeratorsChunk5)) (.node 1 (.leaf startSecondNumeratorsChunk6) (.leaf startSecondNumeratorsChunk7)))) (.node 4 (.node 2 (.node 1 (.leaf startSecondNumeratorsChunk8) (.leaf startSecondNumeratorsChunk9)) (.node 1 (.leaf startSecondNumeratorsChunk10) (.leaf startSecondNumeratorsChunk11))) (.node 2 (.node 1 (.leaf startSecondNumeratorsChunk12) (.leaf startSecondNumeratorsChunk13)) (.node 1 (.leaf startSecondNumeratorsChunk14) (.node 1 (.leaf startSecondNumeratorsChunk15) (.leaf startSecondNumeratorsChunk16))))))

theorem startSecondTree_valid : validChunks startSecondTree := by decide +kernel

theorem startSecondTree_flat : flattenChunks startSecondTree = startSecondNumerators := by
  simp only [startSecondTree, flattenChunks, startSecondNumerators, List.append_assoc]

def startSecondCoefficient (i : ℕ) : ℤ :=
  if i < 513 then chunkLookup startSecondTree i 0 else 0

theorem startSecondCoefficient_eq (i : ℕ) :
    startSecondCoefficient i = startSecondNumerators.getD i 0 := by
  by_cases hi : i < 513
  · rw [startSecondCoefficient, if_pos hi]
    have h := chunkLookup_eq_getD startSecondTree startSecondTree_valid i
      (by rw [startSecondTree_flat, startSecond_length]; exact hi) (0 : ℤ)
    simpa only [startSecondTree_flat] using h
  · rw [startSecondCoefficient, if_neg hi, List.getD_eq_default _ _
      (by rw [startSecond_length]; omega)]

def startCrossTree : LookupTree (List ℤ) := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf startCrossNumeratorsChunk0) (.leaf startCrossNumeratorsChunk1)) (.node 1 (.leaf startCrossNumeratorsChunk2) (.leaf startCrossNumeratorsChunk3))) (.node 2 (.node 1 (.leaf startCrossNumeratorsChunk4) (.leaf startCrossNumeratorsChunk5)) (.node 1 (.leaf startCrossNumeratorsChunk6) (.leaf startCrossNumeratorsChunk7)))) (.node 4 (.node 2 (.node 1 (.leaf startCrossNumeratorsChunk8) (.leaf startCrossNumeratorsChunk9)) (.node 1 (.leaf startCrossNumeratorsChunk10) (.leaf startCrossNumeratorsChunk11))) (.node 2 (.node 1 (.leaf startCrossNumeratorsChunk12) (.leaf startCrossNumeratorsChunk13)) (.node 1 (.leaf startCrossNumeratorsChunk14) (.node 1 (.leaf startCrossNumeratorsChunk15) (.leaf startCrossNumeratorsChunk16))))))

theorem startCrossTree_valid : validChunks startCrossTree := by decide +kernel

theorem startCrossTree_flat : flattenChunks startCrossTree = startCrossNumerators := by
  simp only [startCrossTree, flattenChunks, startCrossNumerators, List.append_assoc]

def startCrossCoefficient (i : ℕ) : ℤ :=
  if i < 513 then chunkLookup startCrossTree i 0 else 0

theorem startCrossCoefficient_eq (i : ℕ) :
    startCrossCoefficient i = startCrossNumerators.getD i 0 := by
  by_cases hi : i < 513
  · rw [startCrossCoefficient, if_pos hi]
    have h := chunkLookup_eq_getD startCrossTree startCrossTree_valid i
      (by rw [startCrossTree_flat, startCross_length]; exact hi) (0 : ℤ)
    simpa only [startCrossTree_flat] using h
  · rw [startCrossCoefficient, if_neg hi, List.getD_eq_default _ _
      (by rw [startCross_length]; omega)]

def lowerSecondTree : LookupTree (List ℤ) := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf lowerSecondNumeratorsChunk0) (.leaf lowerSecondNumeratorsChunk1)) (.node 1 (.leaf lowerSecondNumeratorsChunk2) (.leaf lowerSecondNumeratorsChunk3))) (.node 2 (.node 1 (.leaf lowerSecondNumeratorsChunk4) (.leaf lowerSecondNumeratorsChunk5)) (.node 1 (.leaf lowerSecondNumeratorsChunk6) (.leaf lowerSecondNumeratorsChunk7)))) (.node 4 (.node 2 (.node 1 (.leaf lowerSecondNumeratorsChunk8) (.leaf lowerSecondNumeratorsChunk9)) (.node 1 (.leaf lowerSecondNumeratorsChunk10) (.leaf lowerSecondNumeratorsChunk11))) (.node 2 (.node 1 (.leaf lowerSecondNumeratorsChunk12) (.leaf lowerSecondNumeratorsChunk13)) (.node 1 (.leaf lowerSecondNumeratorsChunk14) (.node 1 (.leaf lowerSecondNumeratorsChunk15) (.leaf lowerSecondNumeratorsChunk16))))))

theorem lowerSecondTree_valid : validChunks lowerSecondTree := by decide +kernel

theorem lowerSecondTree_flat : flattenChunks lowerSecondTree = lowerSecondNumerators := by
  simp only [lowerSecondTree, flattenChunks, lowerSecondNumerators, List.append_assoc]

def lowerSecondCoefficient (i : ℕ) : ℤ :=
  if i < 513 then chunkLookup lowerSecondTree i 0 else 0

theorem lowerSecondCoefficient_eq (i : ℕ) :
    lowerSecondCoefficient i = lowerSecondNumerators.getD i 0 := by
  by_cases hi : i < 513
  · rw [lowerSecondCoefficient, if_pos hi]
    have h := chunkLookup_eq_getD lowerSecondTree lowerSecondTree_valid i
      (by rw [lowerSecondTree_flat, lowerSecond_length]; exact hi) (0 : ℤ)
    simpa only [lowerSecondTree_flat] using h
  · rw [lowerSecondCoefficient, if_neg hi, List.getD_eq_default _ _
      (by rw [lowerSecond_length]; omega)]

def lowerCrossTree : LookupTree (List ℤ) := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf lowerCrossNumeratorsChunk0) (.leaf lowerCrossNumeratorsChunk1)) (.node 1 (.leaf lowerCrossNumeratorsChunk2) (.leaf lowerCrossNumeratorsChunk3))) (.node 2 (.node 1 (.leaf lowerCrossNumeratorsChunk4) (.leaf lowerCrossNumeratorsChunk5)) (.node 1 (.leaf lowerCrossNumeratorsChunk6) (.leaf lowerCrossNumeratorsChunk7)))) (.node 4 (.node 2 (.node 1 (.leaf lowerCrossNumeratorsChunk8) (.leaf lowerCrossNumeratorsChunk9)) (.node 1 (.leaf lowerCrossNumeratorsChunk10) (.leaf lowerCrossNumeratorsChunk11))) (.node 2 (.node 1 (.leaf lowerCrossNumeratorsChunk12) (.leaf lowerCrossNumeratorsChunk13)) (.node 1 (.leaf lowerCrossNumeratorsChunk14) (.node 1 (.leaf lowerCrossNumeratorsChunk15) (.leaf lowerCrossNumeratorsChunk16))))))

theorem lowerCrossTree_valid : validChunks lowerCrossTree := by decide +kernel

theorem lowerCrossTree_flat : flattenChunks lowerCrossTree = lowerCrossNumerators := by
  simp only [lowerCrossTree, flattenChunks, lowerCrossNumerators, List.append_assoc]

def lowerCrossCoefficient (i : ℕ) : ℤ :=
  if i < 513 then chunkLookup lowerCrossTree i 0 else 0

theorem lowerCrossCoefficient_eq (i : ℕ) :
    lowerCrossCoefficient i = lowerCrossNumerators.getD i 0 := by
  by_cases hi : i < 513
  · rw [lowerCrossCoefficient, if_pos hi]
    have h := chunkLookup_eq_getD lowerCrossTree lowerCrossTree_valid i
      (by rw [lowerCrossTree_flat, lowerCross_length]; exact hi) (0 : ℤ)
    simpa only [lowerCrossTree_flat] using h
  · rw [lowerCrossCoefficient, if_neg hi, List.getD_eq_default _ _
      (by rw [lowerCross_length]; omega)]

end ADMM.UnitCircle.LowerCertificate.Determinant
