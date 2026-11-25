/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.IndexPermutation
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.Data
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.FirstKind512.Context

@[expose] public section

set_option maxRecDepth 8192
set_option linter.style.longLine false

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial

theorem window512_perm_pairs : (windowIndices 512).Perm (pairedIndices 512) :=
  window_indices_perm_paired 512

def startChunks : LookupTree (List ℤ) := (.node 16 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf Determinant.startDeterminantNumeratorsChunk0) (.leaf Determinant.startDeterminantNumeratorsChunk1)) (.node 1 (.leaf Determinant.startDeterminantNumeratorsChunk2) (.leaf Determinant.startDeterminantNumeratorsChunk3))) (.node 2 (.node 1 (.leaf Determinant.startDeterminantNumeratorsChunk4) (.leaf Determinant.startDeterminantNumeratorsChunk5)) (.node 1 (.leaf Determinant.startDeterminantNumeratorsChunk6) (.leaf Determinant.startDeterminantNumeratorsChunk7)))) (.node 4 (.node 2 (.node 1 (.leaf Determinant.startDeterminantNumeratorsChunk8) (.leaf Determinant.startDeterminantNumeratorsChunk9)) (.node 1 (.leaf Determinant.startDeterminantNumeratorsChunk10) (.leaf Determinant.startDeterminantNumeratorsChunk11))) (.node 2 (.node 1 (.leaf Determinant.startDeterminantNumeratorsChunk12) (.leaf Determinant.startDeterminantNumeratorsChunk13)) (.node 1 (.leaf Determinant.startDeterminantNumeratorsChunk14) (.leaf Determinant.startDeterminantNumeratorsChunk15))))) (.node 8 (.node 4 (.node 2 (.node 1 (.leaf Determinant.startDeterminantNumeratorsChunk16) (.leaf Determinant.startDeterminantNumeratorsChunk17)) (.node 1 (.leaf Determinant.startDeterminantNumeratorsChunk18) (.leaf Determinant.startDeterminantNumeratorsChunk19))) (.node 2 (.node 1 (.leaf Determinant.startDeterminantNumeratorsChunk20) (.leaf Determinant.startDeterminantNumeratorsChunk21)) (.node 1 (.leaf Determinant.startDeterminantNumeratorsChunk22) (.leaf Determinant.startDeterminantNumeratorsChunk23)))) (.node 4 (.node 2 (.node 1 (.leaf Determinant.startDeterminantNumeratorsChunk24) (.leaf Determinant.startDeterminantNumeratorsChunk25)) (.node 1 (.leaf Determinant.startDeterminantNumeratorsChunk26) (.leaf Determinant.startDeterminantNumeratorsChunk27))) (.node 2 (.node 1 (.leaf Determinant.startDeterminantNumeratorsChunk28) (.leaf Determinant.startDeterminantNumeratorsChunk29)) (.node 1 (.leaf Determinant.startDeterminantNumeratorsChunk30) (.node 1 (.leaf Determinant.startDeterminantNumeratorsChunk31) (.leaf Determinant.startDeterminantNumeratorsChunk32)))))))

theorem startChunks_flatten : flattenChunks startChunks = Determinant.startDeterminantNumerators := by
  simp only [startChunks, flattenChunks, Determinant.startDeterminantNumerators, List.append_assoc]

theorem startChunks_valid : validChunks startChunks := by
  decide +kernel

theorem startChunks_length : (flattenChunks startChunks).length = 1025 := by
  decide +kernel

def startCoefficient (i : ℕ) : ℤ := chunkLookup startChunks i 0

theorem startCoefficient_getD (i : ℕ) (hi : i < 1025) :
    startCoefficient i = Determinant.startDeterminantNumerators.getD i 0 := by
  rw [startCoefficient, chunkLookup_eq_getD startChunks startChunks_valid i
    (by rw [startChunks_length]; exact hi), startChunks_flatten]

theorem startVector_length : Determinant.startDeterminantNumerators.length = 1025 := by
  rw [← startChunks_flatten, startChunks_length]

def startLaurent : Laurent :=
  Determinant.rationalLaurent (-512) Determinant.determinantDenominator Determinant.startDeterminantNumerators

def startPaired : Laurent :=
  pairedLaurent 512
    ((startCoefficient 512 : ℚ) / Determinant.determinantDenominator)
    (fun i ↦ (startCoefficient (i.val + 513) : ℚ) / Determinant.determinantDenominator)
    (fun i ↦ (startCoefficient (511 - i.val) : ℚ) / Determinant.determinantDenominator)

theorem startLaurent_perm_paired : startLaurent.Perm startPaired := by
  exact rationalLaurent_pairing 512 Determinant.determinantDenominator Determinant.startDeterminantNumerators
    startVector_length startCoefficient
    (fun i hi ↦ (startCoefficient_getD i hi).symm) window512_perm_pairs

def startChebWeight : Fin 513 → ℤ :=
  Fin.cases (startCoefficient 512)
    (fun i ↦ startCoefficient (i.val + 513) + startCoefficient (511 - i.val))

def startChebPolynomial : List ℤ :=
  IntegerCoefficients.chebyshevTransform FirstKind512.tree.get 512
    startChebWeight

def lowerChunks : LookupTree (List ℤ) := (.node 16 (.node 8 (.node 4 (.node 2 (.node 1 (.leaf Determinant.lowerDeterminantNumeratorsChunk0) (.leaf Determinant.lowerDeterminantNumeratorsChunk1)) (.node 1 (.leaf Determinant.lowerDeterminantNumeratorsChunk2) (.leaf Determinant.lowerDeterminantNumeratorsChunk3))) (.node 2 (.node 1 (.leaf Determinant.lowerDeterminantNumeratorsChunk4) (.leaf Determinant.lowerDeterminantNumeratorsChunk5)) (.node 1 (.leaf Determinant.lowerDeterminantNumeratorsChunk6) (.leaf Determinant.lowerDeterminantNumeratorsChunk7)))) (.node 4 (.node 2 (.node 1 (.leaf Determinant.lowerDeterminantNumeratorsChunk8) (.leaf Determinant.lowerDeterminantNumeratorsChunk9)) (.node 1 (.leaf Determinant.lowerDeterminantNumeratorsChunk10) (.leaf Determinant.lowerDeterminantNumeratorsChunk11))) (.node 2 (.node 1 (.leaf Determinant.lowerDeterminantNumeratorsChunk12) (.leaf Determinant.lowerDeterminantNumeratorsChunk13)) (.node 1 (.leaf Determinant.lowerDeterminantNumeratorsChunk14) (.leaf Determinant.lowerDeterminantNumeratorsChunk15))))) (.node 8 (.node 4 (.node 2 (.node 1 (.leaf Determinant.lowerDeterminantNumeratorsChunk16) (.leaf Determinant.lowerDeterminantNumeratorsChunk17)) (.node 1 (.leaf Determinant.lowerDeterminantNumeratorsChunk18) (.leaf Determinant.lowerDeterminantNumeratorsChunk19))) (.node 2 (.node 1 (.leaf Determinant.lowerDeterminantNumeratorsChunk20) (.leaf Determinant.lowerDeterminantNumeratorsChunk21)) (.node 1 (.leaf Determinant.lowerDeterminantNumeratorsChunk22) (.leaf Determinant.lowerDeterminantNumeratorsChunk23)))) (.node 4 (.node 2 (.node 1 (.leaf Determinant.lowerDeterminantNumeratorsChunk24) (.leaf Determinant.lowerDeterminantNumeratorsChunk25)) (.node 1 (.leaf Determinant.lowerDeterminantNumeratorsChunk26) (.leaf Determinant.lowerDeterminantNumeratorsChunk27))) (.node 2 (.node 1 (.leaf Determinant.lowerDeterminantNumeratorsChunk28) (.leaf Determinant.lowerDeterminantNumeratorsChunk29)) (.node 1 (.leaf Determinant.lowerDeterminantNumeratorsChunk30) (.node 1 (.leaf Determinant.lowerDeterminantNumeratorsChunk31) (.leaf Determinant.lowerDeterminantNumeratorsChunk32)))))))

theorem lowerChunks_flatten : flattenChunks lowerChunks = Determinant.lowerDeterminantNumerators := by
  simp only [lowerChunks, flattenChunks, Determinant.lowerDeterminantNumerators, List.append_assoc]

theorem lowerChunks_valid : validChunks lowerChunks := by
  decide +kernel

theorem lowerChunks_length : (flattenChunks lowerChunks).length = 1025 := by
  decide +kernel

def lowerCoefficient (i : ℕ) : ℤ := chunkLookup lowerChunks i 0

theorem lowerCoefficient_getD (i : ℕ) (hi : i < 1025) :
    lowerCoefficient i = Determinant.lowerDeterminantNumerators.getD i 0 := by
  rw [lowerCoefficient, chunkLookup_eq_getD lowerChunks lowerChunks_valid i
    (by rw [lowerChunks_length]; exact hi), lowerChunks_flatten]

theorem lowerVector_length : Determinant.lowerDeterminantNumerators.length = 1025 := by
  rw [← lowerChunks_flatten, lowerChunks_length]

def lowerLaurent : Laurent :=
  Determinant.rationalLaurent (-512) Determinant.determinantDenominator Determinant.lowerDeterminantNumerators

def lowerPaired : Laurent :=
  pairedLaurent 512
    ((lowerCoefficient 512 : ℚ) / Determinant.determinantDenominator)
    (fun i ↦ (lowerCoefficient (i.val + 513) : ℚ) / Determinant.determinantDenominator)
    (fun i ↦ (lowerCoefficient (511 - i.val) : ℚ) / Determinant.determinantDenominator)

theorem lowerLaurent_perm_paired : lowerLaurent.Perm lowerPaired := by
  exact rationalLaurent_pairing 512 Determinant.determinantDenominator Determinant.lowerDeterminantNumerators
    lowerVector_length lowerCoefficient
    (fun i hi ↦ (lowerCoefficient_getD i hi).symm) window512_perm_pairs

def lowerChebWeight : Fin 513 → ℤ :=
  Fin.cases (lowerCoefficient 512)
    (fun i ↦ lowerCoefficient (i.val + 513) + lowerCoefficient (511 - i.val))

def lowerChebPolynomial : List ℤ :=
  IntegerCoefficients.chebyshevTransform FirstKind512.tree.get 512
    lowerChebWeight

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial
