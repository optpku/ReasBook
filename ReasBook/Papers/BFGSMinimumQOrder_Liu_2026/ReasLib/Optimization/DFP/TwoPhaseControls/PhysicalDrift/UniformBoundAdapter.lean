module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.ResidualFactorization

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
This companion keeps the algebraic cubic-factorization interface separate from the
filter-level statement consumed by the physical-drift wrappers.  In particular, it
does not assume an identity for the raw mixed observable map.
-/

/-- Helper for Appendix Lemma A.6: a scalar cubic factorization with a uniformly
bounded quotient gives a fixed-coefficient big-O estimate for the mixed weight
`|θ.1| * |r| ^ 3` on `principal K ×ˢ 𝓝 0`. -/
theorem isBigOWith_of_scalar_cubic_factorization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set (ℝ × ℝ × ℝ)}
    {R Q : (ℝ × ℝ × ℝ) → ℝ → E}
    (hfactor : ∀ θ r, R θ r = (θ.1 * r ^ (3 : ℕ)) • Q θ r)
    (hQ : ∃ C > 0, ∃ δ > 0, ∀ θ ∈ K, ∀ r : ℝ, |r| < δ → ‖Q θ r‖ ≤ C) :
    ∃ C > 0,
      Asymptotics.IsBigOWith C
        (principal K ×ˢ 𝓝 0)
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ R z.1 z.2)
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ |z.1.1| * |z.2| ^ (3 : ℝ)) := by
  obtain ⟨C, hC, δ, hδ, hbound⟩ :=
    norm_le_of_scalar_cubic_factorization hfactor hQ
  refine ⟨C, hC, ?_⟩
  rw [Asymptotics.isBigOWith_iff]
  refine Metric.eventually_prod_nhds_iff.mpr
    ⟨fun θ ↦ θ ∈ K,
      Filter.eventually_principal.mpr (fun θ hθ ↦ hθ), δ, hδ, ?_⟩
  intro θ hθ r hr
  have hr' : |r| < δ := by
    simpa only [Real.dist_0_eq_abs] using hr
  have hraw := hbound θ hθ r hr'
  simpa only [Real.norm_eq_abs, abs_mul, abs_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg r) (3 : ℝ)), mul_assoc] using hraw

end DFP.TwoLeg.Mixed
