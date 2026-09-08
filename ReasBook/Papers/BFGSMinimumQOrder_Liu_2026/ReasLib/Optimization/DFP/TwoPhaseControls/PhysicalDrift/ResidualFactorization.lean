module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusJet

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-- Helper for Appendix Lemma A.6: a scalar cubic factorization and a uniform quotient
bound imply the corresponding mixed-variable residual estimate. -/
theorem norm_le_of_scalar_cubic_factorization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ × ℝ)}
    {R Q : (ℝ × ℝ × ℝ) → ℝ → E}
    (hfactor : ∀ θ r, R θ r = (θ.1 * r ^ (3 : ℕ)) • Q θ r)
    (hQ : ∃ C > 0, ∃ δ > 0, ∀ θ ∈ K, ∀ r : ℝ, |r| < δ → ‖Q θ r‖ ≤ C) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ K, ∀ r : ℝ, |r| < δ →
      ‖R θ r‖ ≤ C * |θ.1| * |r| ^ (3 : ℝ) := by
  obtain ⟨C, hC, δ, hδ, hQbound⟩ := hQ
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro θ hθ r hr
  have hboundNat : ‖R θ r‖ ≤ C * |θ.1| * |r| ^ (3 : ℕ) := by
    rw [hfactor, norm_smul, Real.norm_eq_abs, abs_mul, abs_pow]
    have hnonneg : 0 ≤ |θ.1| * |r| ^ (3 : ℕ) := by positivity
    calc
      (|θ.1| * |r| ^ (3 : ℕ)) * ‖Q θ r‖ ≤
          (|θ.1| * |r| ^ (3 : ℕ)) * C :=
        mul_le_mul_of_nonneg_left (hQbound θ hθ r hr) hnonneg
      _ = C * |θ.1| * |r| ^ (3 : ℕ) := by ring
  have hpow : |r| ^ (3 : ℝ) = |r| ^ (3 : ℕ) := by
    norm_num [Real.rpow_natCast]
  rw [hpow]
  exact hboundNat

end DFP.TwoLeg.Mixed
