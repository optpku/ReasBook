/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.TargetSemantics
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.AssemblyStart
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.AssemblyLower
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.ActualDeterminant

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial

open ADMM.RefinedEndpoint.Data

/-- The exact interval-certificate polynomial is the real part of the actual
shifted determinant Laurent polynomial on the unit circle. -/
theorem startDeterminantPolynomial_eval {z : ℂ} (hz : ‖z‖ = 1) :
    evaluate Data.StartDeterminant z.re = (evaluateLaurent startLaurent z).re := by
  rw [← start_realPolynomial_eq_of_coefficients start_coefficients]
  exact (evaluateLaurent_re _ hz).symm

theorem lowerDeterminantPolynomial_eval {z : ℂ} (hz : ‖z‖ = 1) :
    evaluate Data.LowerDeterminant z.re = (evaluateLaurent lowerLaurent z).re := by
  rw [← lower_realPolynomial_eq_of_coefficients lower_coefficients]
  exact (evaluateLaurent_re _ hz).symm

/-- The polynomial in the start Bernstein certificate is the shifted minor
of the three original, exactly divided supply entries. -/
theorem startDeterminantPolynomial_source {z : ℂ} (hz : ‖z‖ = 1) :
    evaluate Data.StartDeterminant z.re =
      ((evaluateLaurent Division.startDiagonalQuotient z).re - (kappa : ℝ)) *
      ((evaluateLaurent Division.startSecondQuotient z).re - (kappa : ℝ)) -
        Complex.normSq (evaluateLaurent Division.startCrossQuotient z) := by
  rw [startDeterminantPolynomial_eval hz]
  exact Determinant.start_determinant_re hz

theorem lowerDeterminantPolynomial_source {z : ℂ} (hz : ‖z‖ = 1) :
    evaluate Data.LowerDeterminant z.re =
      ((evaluateLaurent Division.startDiagonalQuotient z).re - (kappa : ℝ)) *
      ((evaluateLaurent Division.lowerSecondQuotient z).re - (kappa : ℝ)) -
        Complex.normSq (evaluateLaurent Division.lowerCrossQuotient z) := by
  rw [lowerDeterminantPolynomial_eval hz]
  exact Determinant.lower_determinant_re hz

end ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial
