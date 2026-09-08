module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.ZeroBranchAdapter
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.ObservableGermTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.ZeroBranchAdapter
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.ObservableGermTransport

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
The physical-drift proof separates removable branches from the punctured raw chart.
This file contains only the branch assembly: all evaluator identities and all
punctured certificates remain explicit inputs.
-/

/-- Helper for Appendix Lemma A.6: zero-scale, zero-radius, and punctured
    certificates assemble into one scalar cubic factorization. -/
theorem centerResidual_factorization_of_branchCertificates
    {Q : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (hscale : ∀ θ r, θ.1 = 0 →
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ 2 = 0)
    (hradius : ∀ θ,
      (observableMap θ.1 (input θ 0)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * (0 : ℝ) ^ 2 = 0)
    (hpunctured : ∀ θ r, θ.1 ≠ 0 → r ≠ 0 →
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ 2 =
      (θ.1 * r ^ (3 : ℕ)) • Q θ r) :
    ∀ θ r,
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ 2 =
        (θ.1 * r ^ (3 : ℕ)) • Q θ r := by
  intro θ r
  by_cases hθ : θ.1 = 0
  · rw [hscale θ r hθ, hθ]
    simp
  · by_cases hr : r = 0
    · subst r
      rw [hradius θ]
      simp
    · exact hpunctured θ r hθ hr

/-- Helper for Appendix Lemma A.6: the unconditional zero-radius identity can be combined with
the zero-scale and punctured certificates without repeating its proof at the call site. -/
theorem centerResidual_factorization_of_zeroRadius_and_punctured
    {Q : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (hscale : ∀ θ r, θ.1 = 0 →
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ 2 = 0)
    (hpunctured : ∀ θ r, θ.1 ≠ 0 → r ≠ 0 →
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ 2 =
      (θ.1 * r ^ (3 : ℕ)) • Q θ r) :
    ∀ θ r,
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ 2 =
        (θ.1 * r ^ (3 : ℕ)) • Q θ r := by
  exact centerResidual_factorization_of_branchCertificates hscale
    (fun θ ↦ centerResidual_zeroRadius θ) hpunctured

/-- Helper for Appendix Lemma A.6: an eventual zero-radius-or-certificate
    decomposition transports a scalar family equality on the product filter. -/
theorem uncurryEventuallyEq_of_zeroOrCertificate
    {K : Set (ℝ × ℝ × ℝ)}
    {Y : Type*}
    {f g : (ℝ × ℝ × ℝ) → ℝ → Y}
    {P : (ℝ × ℝ × ℝ) → ℝ → Prop}
    (hbase : ∀ θ, f θ 0 = g θ 0)
    (hcertificate : ∀ θ r, P θ r → f θ r = g θ r)
    (hbranch : ∀ θ, θ ∈ K →
      ∀ᶠ z in 𝓝 (θ, 0), z.2 = 0 ∨ P z.1 z.2) :
    ∀ θ, θ ∈ K →
      Function.uncurry f =ᶠ[𝓝 (θ, 0)] Function.uncurry g := by
  intro θ hθ
  filter_upwards [hbranch θ hθ] with z hz
  change f z.1 z.2 = g z.1 z.2
  rcases hz with hz0 | hzP
  · simpa [hz0] using hbase z.1
  · exact hcertificate z.1 z.2 hzP

end DFP.TwoLeg.Mixed
