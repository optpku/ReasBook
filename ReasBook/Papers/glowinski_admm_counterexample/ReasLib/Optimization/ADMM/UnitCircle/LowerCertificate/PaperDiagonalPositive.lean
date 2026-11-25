/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Coverage.Diagonal
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DiagonalPolynomial
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.PaperMatrixSoundness

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

open Division

/-- The seven exact Bernstein certificates prove the first shifted minor of
the actual source quotient, including the zero-frequency point. -/
theorem paper_diagonal_margin {z : ℂ} (hz : ‖z‖ = 1) :
    0 < (evaluateLaurent startDiagonalQuotient z).re -
      (ADMM.RefinedEndpoint.Data.kappa : ℝ) := by
  have hx : z.re ∈ Set.Icc (-1 : ℝ) 1 := by
    exact abs_le.mp (by simpa only [hz] using Complex.abs_re_le_norm z)
  have h := Coverage.diagonal_positive hx
  rw [diagonalPolynomial_source] at h
  rw [evaluateLaurent_re _ hz]
  exact h

/-- With the actual first minor fully certified, the complete lower-circle
claim has only the two actual endpoint determinant checks left. -/
theorem paper_lower_circle_certificate_of_determinants
    (hStart : ∀ z : ℂ, ‖z‖ = 1 →
      0 < ((evaluateLaurent startDiagonalQuotient z).re -
        (ADMM.RefinedEndpoint.Data.kappa : ℝ)) *
        ((evaluateLaurent startSecondQuotient z).re -
          (ADMM.RefinedEndpoint.Data.kappa : ℝ)) -
          Complex.normSq (evaluateLaurent startCrossQuotient z))
    (hLower : ∀ z : ℂ, ‖z‖ = 1 →
      0 < ((evaluateLaurent startDiagonalQuotient z).re -
        (ADMM.RefinedEndpoint.Data.kappa : ℝ)) *
        ((evaluateLaurent lowerSecondQuotient z).re -
          (ADMM.RefinedEndpoint.Data.kappa : ℝ)) -
          Complex.normSq (evaluateLaurent lowerCrossQuotient z)) :
    ADMM.UpdatedTargets.LowerCircleCertificateClaim := by
  exact paper_lower_circle_certificate_of_minors (fun _ hz ↦ paper_diagonal_margin hz)
    hStart hLower

end ADMM.UnitCircle.LowerCertificate
