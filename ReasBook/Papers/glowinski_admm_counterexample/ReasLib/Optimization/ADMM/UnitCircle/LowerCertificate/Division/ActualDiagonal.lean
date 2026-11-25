/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Division.Checks.Diagonal
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Division.LagNormalization

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Division

lemma evaluate_normalizedLag0 (z : ℂ) :
    evaluateLaurent normalizedLag0 z = lagMultiplier paperWeights 1 z 0 := by
  rw [normalizedLag0_correct, evaluate_normalizedFromRaw, evaluate_lagLaurent]

lemma evaluate_normalizedLag1 (z : ℂ) :
    evaluateLaurent normalizedLag1 z = lagMultiplier paperWeights 1 z 1 := by
  rw [normalizedLag1_correct, evaluate_normalizedFromRaw, evaluate_lagLaurent]

/-- The common real delay factor in every exact quotient identity. -/
theorem evaluate_delayNorm_normSq {z : ℂ} (hz : ‖z‖ = 1) :
    evaluateLaurent delayNorm z = (Complex.normSq (delaySymbol 1 z) : ℂ) := by
  rw [evaluate_delayNorm hz]
  simpa only [Complex.star_def] using Complex.mul_conj (delaySymbol 1 z)

/-- The diagonal source quotient is common to both multiplier endpoints. -/
theorem diagonal_entry_division (γ : ℚ) {z : ℂ} (hz : ‖z‖ = 1) :
    supplySymbol paperWeights 1 γ z 0 0 =
      (Complex.normSq (delaySymbol 1 z) : ℂ) * evaluateLaurent startDiagonalQuotient z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [← evaluate_fastDiagonal normalizedLag0 hz (evaluate_normalizedLag0 z) γ,
    evaluate_eq_of_normalForm divisionDiagonal z,
    evaluateLaurent_multiply _ _ hz0, evaluate_delayNorm_normSq hz]

end ADMM.UnitCircle.LowerCertificate.Division
