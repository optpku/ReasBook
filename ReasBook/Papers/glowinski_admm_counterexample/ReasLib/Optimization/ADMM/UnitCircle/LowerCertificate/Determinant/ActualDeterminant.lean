/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.SourceTheory
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.ConvolutionChecks.Start
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.ConvolutionChecks.Lower

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Determinant

open ADMM.RefinedEndpoint.Data

/-- The proposed start determinant coefficients are the actual shifted
quotient determinant, through an exact checked integer convolution. -/
theorem start_determinant_eval {z : ℂ} (hz : ‖z‖ = 1) :
    evaluateLaurent startDeterminantLaurent z = startExpression z := by
  rw [startDeterminantLaurent, start_convolution]
  exact start_vector_eval hz

theorem lower_determinant_eval {z : ℂ} (hz : ‖z‖ = 1) :
    evaluateLaurent lowerDeterminantLaurent z = lowerExpression z := by
  rw [lowerDeterminantLaurent, lower_convolution]
  exact lower_vector_eval hz

/-- The exact scalar inequality needed by the Hermitian matrix certificate,
including the full imaginary cross-entry contribution. -/
theorem start_determinant_re {z : ℂ} (hz : ‖z‖ = 1) :
    (evaluateLaurent startDeterminantLaurent z).re =
      ((evaluateLaurent Division.startDiagonalQuotient z).re - (kappa : ℝ)) *
      ((evaluateLaurent Division.startSecondQuotient z).re - (kappa : ℝ)) -
        Complex.normSq (evaluateLaurent Division.startCrossQuotient z) := by
  rw [start_determinant_eval hz]
  exact startExpression_re hz

theorem lower_determinant_re {z : ℂ} (hz : ‖z‖ = 1) :
    (evaluateLaurent lowerDeterminantLaurent z).re =
      ((evaluateLaurent Division.startDiagonalQuotient z).re - (kappa : ℝ)) *
      ((evaluateLaurent Division.lowerSecondQuotient z).re - (kappa : ℝ)) -
        Complex.normSq (evaluateLaurent Division.lowerCrossQuotient z) := by
  rw [lower_determinant_eval hz]
  exact lowerExpression_re hz

/-- The same certified Laurent polynomial is the determinant of the actual
shifted supply after removing its squared delay factor. -/
theorem start_actual_supply_determinant {z : ℂ} (hz : ‖z‖ = 1) :
    Matrix.det (supplySymbol paperWeights 1 ((377 / 200 : ℚ) : ℝ) z -
      ((Complex.normSq (delaySymbol 1 z) * (kappa : ℝ) : ℝ) : ℂ) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      (Complex.normSq (delaySymbol 1 z) : ℂ) ^ 2 * evaluateLaurent startDeterminantLaurent z := by
  rw [start_determinant_eval hz]
  exact start_shifted_supply_determinant hz

theorem lower_actual_supply_determinant {z : ℂ} (hz : ‖z‖ = 1) :
    Matrix.det (supplySymbol paperWeights 1 ((75475298801 / 40000000000 : ℚ) : ℝ) z -
      ((Complex.normSq (delaySymbol 1 z) * (kappa : ℝ) : ℝ) : ℂ) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      (Complex.normSq (delaySymbol 1 z) : ℂ) ^ 2 * evaluateLaurent lowerDeterminantLaurent z := by
  rw [lower_determinant_eval hz]
  exact lower_shifted_supply_determinant hz

end ADMM.UnitCircle.LowerCertificate.Determinant
