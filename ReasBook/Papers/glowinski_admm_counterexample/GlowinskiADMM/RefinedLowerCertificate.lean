/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Coverage.StartDeterminant
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Coverage.LowerDeterminant
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.DeterminantPolynomial.Actual
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.PaperDiagonalPositive

@[expose] public section

/-!
# The concrete lower-circle certificate

The exact Bernstein certificates cover the whole real frequency interval.
The determinant source identities transfer their positivity to the actual
quotient minors, and strict continuation gives a positive extension beyond `L`.
-/

namespace ADMM.UpdatedTargets

open UnitCircle.LowerCertificate

/-- The certificate in Appendix C.2, including a uniform positive margin and
strict continuation beyond the displayed lower endpoint. -/
theorem lowerCircleCertificate : LowerCircleCertificateClaim := by
  apply paper_lower_circle_certificate_of_determinants
  · intro z hz
    have hx : z.re ∈ Set.Icc (-1 : ℝ) 1 :=
      abs_le.mp (by simpa only [hz] using Complex.abs_re_le_norm z)
    have h := Coverage.startDeterminant_positive hx
    rw [DeterminantPolynomial.startDeterminantPolynomial_source hz] at h
    exact h
  · intro z hz
    have hx : z.re ∈ Set.Icc (-1 : ℝ) 1 :=
      abs_le.mp (by simpa only [hz] using Complex.abs_re_le_norm z)
    have h := Coverage.lowerDeterminant_positive hx
    rw [DeterminantPolynomial.lowerDeterminantPolynomial_source hz] at h
    exact h

end ADMM.UpdatedTargets
