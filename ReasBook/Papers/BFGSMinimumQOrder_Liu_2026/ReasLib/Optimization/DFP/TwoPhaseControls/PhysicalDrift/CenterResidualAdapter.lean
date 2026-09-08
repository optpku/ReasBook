module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap.Observables
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.ResidualFactorization

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-!
This companion names the concrete center residual used by Appendix Lemma A.6.  The
raw-map identity and the quotient estimate remain hypotheses: this file only packages
their stable algebraic consequence, so it can be consumed without reopening the large
observable evaluator.
-/

/-- Helper for Appendix Lemma A.6: the prescribed quadratic coefficient of the incoming
    low-frame full-center displacement. -/
def centerDriftCoefficient (θ : ℝ × ℝ × ℝ) : ℝ :=
  -(2 * θ.1 ^ 2 * (6 * θ.2.2 - θ.2.1 + 96) / 9)

/-- Helper for Appendix Lemma A.6: a cubic factorization of the concrete full-center
    residual and a bounded quotient imply its uniform mixed-variable cubic bound. -/
theorem centerResidual_uniformBound_of_cubicFactorization
    {K : Set (ℝ × ℝ × ℝ)}
    {Q : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (hfactor : ∀ θ r,
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ 2 =
        (θ.1 * r ^ (3 : ℕ)) • Q θ r)
    (hQ : ∃ C > 0, ∃ δ > 0, ∀ θ ∈ K, ∀ r : ℝ, |r| < δ → ‖Q θ r‖ ≤ C) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ K, ∀ r : ℝ, |r| < δ →
      ‖(observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ 2‖ ≤
      C * |θ.1| * |r| ^ (3 : ℝ) := by
  exact norm_le_of_scalar_cubic_factorization hfactor hQ

/-- Helper for Appendix Lemma A.6: an exact equality transporting the concrete center
    residual to a normal-form residual preserves the cubic-factorization certificate. -/
theorem centerResidual_factorization_of_normalForm
    {N Q : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (hmap : ∀ θ r,
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ 2 = N θ r)
    (hfactor : ∀ θ r, N θ r = (θ.1 * r ^ (3 : ℕ)) • Q θ r) :
    ∀ θ r,
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ 2 =
        (θ.1 * r ^ (3 : ℕ)) • Q θ r := by
  intro θ r
  rw [hmap, hfactor]

end DFP.TwoLeg.Mixed
