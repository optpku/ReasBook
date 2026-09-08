module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterQuotientCompactBound

public section

noncomputable section

open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
The quotient used by the physical center residual is defined to be zero when its
mixed cubic denominator vanishes.  A removable kernel need only agree with that
quotient on the punctured tube; this companion records the corresponding compact
bound without requiring the kernel to vanish on the removable branches.
-/

/-- Helper for Appendix Lemma A.6: a continuous kernel that agrees with a zero-filled
quotient away from its mixed cubic denominator yields a local uniform quotient bound. -/
theorem exists_local_uniform_quotient_bound_of_continuousKernel_on_punctured
    (β B : ℝ) (Q K : (ℝ × ℝ × ℝ) → ℝ → ℝ)
    (hcertificate : ∃ δ > 0,
      ContinuousOn
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ K z.1 z.2)
        (parameterSet β B ×ˢ Set.Icc (-δ) δ) ∧
      (∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
        θ.1 * r ^ (3 : ℕ) ≠ 0 → Q θ r = K θ r))
    (hzero : ∀ θ r, θ.1 * r ^ (3 : ℕ) = 0 → Q θ r = 0) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
      ‖Q θ r‖ ≤ C := by
  obtain ⟨δ, hδ, hKcont, hQeq⟩ := hcertificate
  obtain ⟨C, hC, hKbound⟩ :=
    exists_uniform_quotient_bound_of_continuousOn β B δ K hKcont
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro θ hθ r hr
  by_cases hden : θ.1 * r ^ (3 : ℕ) = 0
  · rw [hzero θ r hden]
    simpa only [norm_zero] using le_of_lt hC
  · rw [hQeq θ hθ r hr hden]
    exact hKbound θ hθ r hr

end DFP.TwoLeg.Mixed
