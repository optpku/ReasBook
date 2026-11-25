/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.GlowinskiADMM.UpdatedTargets
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.QuotientFamily
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Division.ActualDivision

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

open Division

/-- Convert positivity of the three scalar minors into the lower-circle certificate,
including zero frequency and strict continuation. The concrete positivity proofs
are supplied by `PaperDiagonalPositive` and `RefinedLowerCertificate`.
The fixed common margin is the manuscript's exact rational `κ`. -/
theorem paper_lower_circle_certificate_of_minors
    (hA : ∀ z : ℂ, ‖z‖ = 1 →
      0 < (evaluateLaurent startDiagonalQuotient z).re - (ADMM.RefinedEndpoint.Data.kappa : ℝ))
    (hStart : ∀ z : ℂ, ‖z‖ = 1 →
      0 < ((evaluateLaurent startDiagonalQuotient z).re - (ADMM.RefinedEndpoint.Data.kappa : ℝ)) *
        ((evaluateLaurent startSecondQuotient z).re - (ADMM.RefinedEndpoint.Data.kappa : ℝ)) -
          Complex.normSq (evaluateLaurent startCrossQuotient z))
    (hLower : ∀ z : ℂ, ‖z‖ = 1 →
      0 < ((evaluateLaurent startDiagonalQuotient z).re - (ADMM.RefinedEndpoint.Data.kappa : ℝ)) *
        ((evaluateLaurent lowerSecondQuotient z).re - (ADMM.RefinedEndpoint.Data.kappa : ℝ)) -
          Complex.normSq (evaluateLaurent lowerCrossQuotient z)) :
    ADMM.UpdatedTargets.LowerCircleCertificateClaim := by
  apply interval_coercivity_of_endpoint_quotients paperWeights
    (ADMM.RefinedEndpoint.Data.kappa : ℝ) ((377 : ℝ) / 200) ADMM.RefinedEndpoint.lower 2
    ADMM.RefinedEndpoint.classical_bound_lt_lower
    (ADMM.RefinedEndpoint.lower_lt_upper.trans ADMM.RefinedEndpoint.upper_lt_two)
    (evaluateLaurent startDiagonalQuotient) (evaluateLaurent startSecondQuotient)
    (evaluateLaurent startCrossQuotient) (evaluateLaurent startDiagonalQuotient)
    (evaluateLaurent lowerSecondQuotient) (evaluateLaurent lowerCrossQuotient)
  · exact evaluateLaurent_continuous_circle _
  · exact evaluateLaurent_continuous_circle _
  · exact evaluateLaurent_continuous_circle _
  · exact evaluateLaurent_continuous_circle _
  · exact evaluateLaurent_continuous_circle _
  · exact evaluateLaurent_continuous_circle _
  · intro z hz
    refine ⟨?_, ?_, ?_⟩
    · simpa using diagonal_entry_division (377 / 200) hz
    · simpa using start_second_entry_division hz
    · simpa using start_cross_entry_division hz
  · intro z hz
    refine ⟨?_, ?_, ?_⟩
    · simpa [ADMM.RefinedEndpoint.lower] using diagonal_entry_division (75475298801 / 40000000000) hz
    · simpa [ADMM.RefinedEndpoint.lower] using lower_second_entry_division hz
    · simpa [ADMM.RefinedEndpoint.lower] using lower_cross_entry_division hz
  · exact hA
  · exact hStart
  · exact hA
  · exact hLower

end ADMM.UnitCircle.LowerCertificate
