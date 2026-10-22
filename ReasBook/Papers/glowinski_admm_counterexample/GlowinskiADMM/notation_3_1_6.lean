/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.GlowinskiADMM.definition_8_1_1_RationalCases

@[expose] public section

namespace ADMM.FiniteMemory

/-- Notation 3.1.6 (1): for memory two, the tail-sum formula specializes to
`h₀ = δ₁ + δ₂` and `h₁ = δ₂`. -/
theorem lagCoefficient_two (lagMinus lagPlus : Block → Fin 2 → NNReal) (b : Block) :
    let δ (d : Fin 2) : ℝ := (lagMinus b d : ℝ) - lagPlus b d
    (lagCoefficient lagMinus lagPlus b 0, lagCoefficient lagMinus lagPlus b 1) =
      (δ 0 + δ 1, δ 1) := by
  simp [lagCoefficient, Fin.sum_univ_two]
  ring

end ADMM.FiniteMemory

namespace ADMM.FiniteMemory.Reconstruction

/-- Notation 3.1.6 (2): the exact Case 1 lag coefficients give the displayed
four-term value storage. -/
theorem caseOneValueStorage (Φ : Block → Fin 2 → ℝ) :
    500000 *
        (∑ b : Block, ∑ d : Fin 2,
          ADMM.FiniteMemory.lagCoefficient (lagMinusNNReal caseOneValid)
            (lagPlusNNReal caseOneValid) b d * Φ b d) =
      -17475 * Φ .F 0 + 14011 * Φ .F 1 - 21753 * Φ .J 0 + 18289 * Φ .J 1 := by
  have blocks : (Finset.univ : Finset Block) = {.F, .J} := by decide
  rw [blocks, Finset.sum_pair (by decide : Block.F ≠ Block.J)]
  simp only [ADMM.FiniteMemory.lagCoefficient, lagMinusNNReal_coe, lagPlusNNReal_coe]
  norm_num [
    lagMinusValue, lagPlusValue, caseOne, RationalCase.ofNumerators, RationalCase.rationalList,
    Fin.sum_univ_two]
  ring

/-- Notation 3.1.6 (3): both current function values have negative coefficients
in Case 1. -/
theorem caseOneCurrentCoefficients_neg :
    ADMM.FiniteMemory.lagCoefficient (lagMinusNNReal caseOneValid)
          (lagPlusNNReal caseOneValid) .F 0 < 0 ∧
      ADMM.FiniteMemory.lagCoefficient (lagMinusNNReal caseOneValid)
          (lagPlusNNReal caseOneValid) .J 0 < 0 := by
  simp only [ADMM.FiniteMemory.lagCoefficient, lagMinusNNReal_coe, lagPlusNNReal_coe]
  norm_num [
    lagMinusValue, lagPlusValue, caseOne, RationalCase.ofNumerators, RationalCase.rationalList,
    Fin.sum_univ_two]

/-- Notation 3.1.6 (4): the reconstructed first-block origin-column weights are
the exact pair displayed in the source. -/
theorem caseOneFirstOriginWeights :
    (100000000 * reconstructMu caseOne .F (some 0) none,
        100000000 * reconstructMu caseOne .F (some 1) none) =
      (1717, 1121) := by
  norm_num [reconstructMu, packedMuValue, packedIndex, lagCoefficient,
    lagMinusValue, lagPlusValue, caseOne, RationalCase.ofNumerators, RationalCase.rationalList,
    Fin.sum_univ_two]

/-- Notation 3.1.6 (5): the first reconstructed flow balance is the negative
current-value coefficient `h_{F,0}`. -/
theorem caseOneFirstBalance :
    reconstructMu caseOne .F (some 0) none +
          reconstructMu caseOne .F (some 0) (some 1) -
        reconstructMu caseOne .F none (some 0) -
      reconstructMu caseOne .F (some 1) (some 0) = -699 / 20000 ∧
    (-699 / 20000 : ℚ) =
      lagCoefficient caseOne .F 0 := by
  norm_num [reconstructMu, packedMuValue, packedIndex, lagCoefficient,
    lagMinusValue, lagPlusValue, caseOne, RationalCase.ofNumerators, RationalCase.rationalList,
    Fin.sum_univ_two]

/-- Notation 3.1.6 (6): all Case 1 first-block interpolation weights are
nonnegative. -/
theorem caseOneMuF_nonneg (i j : Option (Fin 2)) :
    0 ≤ reconstructMu caseOne .F i j := by
  exact caseOneValid.mu_nonneg .F i j

/- Notation 3.1.6 (7): the lower matrix represents the quadratic remainder. -/
#check ADMM.FiniteMemory.lowerMatrix_quadratic

/- Canonical companion: valid Case 1 data make each lower endpoint test positive semidefinite. -/
#check endpointLower_posSemidef caseOneValid

end ADMM.FiniteMemory.Reconstruction
