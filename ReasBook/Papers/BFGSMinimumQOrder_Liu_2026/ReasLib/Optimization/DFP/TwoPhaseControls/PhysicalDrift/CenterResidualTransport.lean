module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualAdapter
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.ObservableGermTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.UniformBoundAdapter
public import ReasLib.Analysis.Asymptotics.UniformRemainder

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
This companion is the boundary between a raw center-residual evaluator and its
normal-form representative.  The evaluator identity is deliberately supplied as
an eventual equality on the product filter; the quotient estimate is kept as a
separate uniform hypothesis.
-/

/-- Helper for Appendix Lemma A.6: a product-filter eventual equality transports a
    scalar cubic-factorization estimate from a normal-form representative. -/
theorem isBigOWith_of_eventuallyEq_scalarCubicFactorization
    {K : Set (ℝ × ℝ × ℝ)}
    {R N Q : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (hmap : (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ R z.1 z.2) =ᶠ[
      principal K ×ˢ 𝓝 0]
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ N z.1 z.2))
    (hfactor : ∀ θ r, N θ r = (θ.1 * r ^ (3 : ℕ)) • Q θ r)
    (hQ : ∃ C > 0, ∃ δ > 0, ∀ θ ∈ K, ∀ r : ℝ, |r| < δ → ‖Q θ r‖ ≤ C) :
    ∃ C > 0,
      Asymptotics.IsBigOWith C
        (principal K ×ˢ 𝓝 0)
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ R z.1 z.2)
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ |z.1.1| * |z.2| ^ (3 : ℝ)) := by
  obtain ⟨C, hC, hnormal⟩ :=
    isBigOWith_of_scalar_cubic_factorization hfactor hQ
  refine ⟨C, hC, ?_⟩
  exact hnormal.congr' rfl hmap.symm (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- Helper for Appendix Lemma A.6: the concrete full-center residual inherits the
    cubic normal-form estimate through a raw-map transport equality. -/
theorem centerResidual_isBigOWith_of_normalFormTransport
    {K : Set (ℝ × ℝ × ℝ)}
    {N Q : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (hmap :
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (observableMap z.1.1 (input z.1 z.2)).fullCenterDisplacement 0 -
          centerDriftCoefficient z.1 * z.2 ^ 2) =ᶠ[
        principal K ×ˢ 𝓝 0]
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ N z.1 z.2))
    (hfactor : ∀ θ r, N θ r = (θ.1 * r ^ (3 : ℕ)) • Q θ r)
    (hQ : ∃ C > 0, ∃ δ > 0, ∀ θ ∈ K, ∀ r : ℝ, |r| < δ → ‖Q θ r‖ ≤ C) :
    ∃ C > 0,
      Asymptotics.IsBigOWith C
        (principal K ×ˢ 𝓝 0)
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          (observableMap z.1.1 (input z.1 z.2)).fullCenterDisplacement 0 -
            centerDriftCoefficient z.1 * z.2 ^ 2)
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ |z.1.1| * |z.2| ^ (3 : ℝ)) := by
  exact isBigOWith_of_eventuallyEq_scalarCubicFactorization
    (R := fun θ r ↦
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ 2)
    hmap hfactor hQ

/-- Helper for Appendix Lemma A.6: a uniformly bounded parameter factor converts a
    common-radius weighted cubic estimate into an ordinary uniform remainder. -/
theorem uniformRemainder_of_scalarCubicTransport
    {K : Set (ℝ × ℝ × ℝ)}
    {R N Q : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (hmap : ∃ δ > 0, ∀ θ ∈ K, ∀ r : ℝ, |r| < δ → R θ r = N θ r)
    (hfactor : ∀ θ r, N θ r = (θ.1 * r ^ (3 : ℕ)) • Q θ r)
    (hQ : ∃ C > 0, ∃ δ > 0, ∀ θ ∈ K, ∀ r : ℝ, |r| < δ → ‖Q θ r‖ ≤ C)
    (hθ : ∃ B > 0, ∀ θ ∈ K, |θ.1| ≤ B) :
    ∃ C > 0, Asymptotics.IsUniformRemainderOn R K C (3 : ℝ) := by
  obtain ⟨δmap, hδmap, hmap⟩ := hmap
  obtain ⟨CQ, hCQ, δQ, hδQ, hQ⟩ := hQ
  obtain ⟨B, hB, hθ⟩ := hθ
  let δ := min δmap δQ
  have hδ : 0 < δ := lt_min hδmap hδQ
  refine ⟨CQ * B, mul_pos hCQ hB, ?_⟩
  apply Asymptotics.IsUniformRemainderOn.of_bound hδ
  intro θ hθK r hr
  have hrmap : |r| < δmap := lt_of_lt_of_le hr (min_le_left _ _)
  have hrQ : |r| < δQ := lt_of_lt_of_le hr (min_le_right _ _)
  rw [hmap θ hθK r hrmap, hfactor θ r, norm_smul, Real.norm_eq_abs,
    abs_mul, abs_pow]
  have hQbound := hQ θ hθK r hrQ
  have hrpow_nonneg : 0 ≤ |r| ^ (3 : ℕ) := by positivity
  have hnorm_nonneg : 0 ≤ ‖Q θ r‖ := norm_nonneg _
  have hBpow_nonneg : 0 ≤ B * |r| ^ (3 : ℕ) :=
    mul_nonneg (le_of_lt hB) hrpow_nonneg
  have hweight : |θ.1| * |r| ^ (3 : ℕ) ≤ B * |r| ^ (3 : ℕ) := by
    exact mul_le_mul_of_nonneg_right (hθ θ hθK) hrpow_nonneg
  have hboundNat : |θ.1| * |r| ^ (3 : ℕ) * ‖Q θ r‖ ≤
      CQ * B * |r| ^ (3 : ℕ) := by
    calc
      |θ.1| * |r| ^ (3 : ℕ) * ‖Q θ r‖ ≤
          (B * |r| ^ (3 : ℕ)) * CQ := by
            exact mul_le_mul hweight hQbound hnorm_nonneg hBpow_nonneg
      _ = CQ * B * |r| ^ (3 : ℕ) := by ring
  have hpow : |r| ^ (3 : ℝ) = |r| ^ (3 : ℕ) := by
    norm_num [Real.rpow_natCast]
  rw [hpow]
  exact hboundNat

end DFP.TwoLeg.Mixed
