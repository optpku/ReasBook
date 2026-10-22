/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Definition_7_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Exercise_11_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace Filter MeasureTheory.Filtration
open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

universe u

/- Remark 11.12 is `source-facing`: it asserts the existence of a martingale witnessing that the
`p = 1` analogue of Theorem 11.10 fails. Its `core/canonical` owner layer is the existing
martingale convergence API around `Martingale` and `Filtration.limitProcess`; the earlier
Exercise 11.2.1 counterexample supplies the construction, so no extra public wrapper around these
owner declarations is kept here. -/

-- Proof sketch: use the standard nonnegative martingale from Exercise 11.2.1, which is bounded in
-- `L^1`; keep the ambient filtered probability space and process explicit, identify its almost-sure
-- limit with the canonical `ℱ.limitProcess X μ`, and then note that `L^1` convergence would force
-- the constant `L^1` norm to tend to `0`.
/-- Remark 11.12: the `p = 1` analogue of Theorem 11.10 fails in general; there exists an
`L^1`-bounded martingale that converges almost surely to its canonical limit process but does not
converge to that limit in `L^1`. -/
theorem exists_l1_bounded_martingale_ae_tendsto_limitProcess_not_tendstoInLp :
    ∃ (Ω : Type u) (m0 : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (ℱ : Filtration ℕ m0) (X : ℕ → Ω → ℝ),
        Martingale X ℱ μ ∧
          (∃ C : ℝ≥0, ∀ n, eLpNorm (X n) 1 μ ≤ C) ∧
          (∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω))) ∧
          ¬ TendstoInLp 1 μ X (ℱ.limitProcess X μ) := by
  rcases exists_nonnegative_martingale_with_expectation_one_ae_tendsto_zero with
    ⟨Ω, m0, μ, hμ, ℱ, X, hX, hX_nonneg, hX_expectation, hX_tendsto_zero⟩
  have h_eLpNorm_eq_one : ∀ n, eLpNorm (X n) 1 μ = 1 := by
    intro n
    calc
      eLpNorm (X n) 1 μ = ENNReal.ofReal (∫ ω, ‖X n ω‖ ∂μ) := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        exact (ofReal_integral_norm_eq_lintegral_enorm (hX.integrable n)).symm
      _ = ENNReal.ofReal (μ[X n]) := by
        refine congrArg ENNReal.ofReal ?_
        refine integral_congr_ae ?_
        filter_upwards [Filter.Eventually.of_forall fun ω ↦ hX_nonneg n ω] with ω hω
        rw [Real.norm_eq_abs, abs_of_nonneg hω]
      _ = 1 := by
        rw [hX_expectation n]
        simp
  have h_l1_bounded : ∃ C : ℝ≥0, ∀ n, eLpNorm (X n) 1 μ ≤ C := by
    refine ⟨1, fun n ↦ ?_⟩
    simpa using le_of_eq (h_eLpNorm_eq_one n)
  have h_ae_tendsto_limit :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω)) :=
    hX.submartingale.ae_tendsto_limitProcess fun n ↦ by
      simpa using le_of_eq (h_eLpNorm_eq_one n)
  have h_limit_zero :
      ℱ.limitProcess X μ =ᵐ[μ] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hX_tendsto_zero, h_ae_tendsto_limit] with ω hω_zero hω_limit
    exact tendsto_nhds_unique hω_limit hω_zero
  have h_not_tendsto :
      ¬ Tendsto
        (fun n ↦ eLpNorm (X n - ℱ.limitProcess X μ) 1 μ)
        atTop (𝓝 0) := by
    have h_dist_eq_one :
        ∀ n, eLpNorm (X n - ℱ.limitProcess X μ) 1 μ = 1 := by
      intro n
      calc
        eLpNorm (X n - ℱ.limitProcess X μ) 1 μ = eLpNorm (X n - fun _ ↦ (0 : ℝ)) 1 μ := by
          refine eLpNorm_congr_ae ?_
          filter_upwards [h_limit_zero] with ω hω
          simp [hω]
        _ = eLpNorm (X n) 1 μ := by
          refine eLpNorm_congr_ae (.of_forall fun ω ↦ ?_)
          simp
        _ = 1 := h_eLpNorm_eq_one n
    intro h_tendsto
    have h_const :
        Tendsto (fun n ↦ eLpNorm (X n - ℱ.limitProcess X μ) 1 μ) atTop (𝓝 1) := by
      have h_eq :
          (fun n ↦ eLpNorm (X n - ℱ.limitProcess X μ) 1 μ) = fun _ : ℕ ↦ (1 : ℝ≥0∞) := by
        funext n
        exact h_dist_eq_one n
      simp [h_eq]
    exact one_ne_zero (tendsto_nhds_unique h_const h_tendsto)
  have h_not_tendstoInLp : ¬ TendstoInLp 1 μ X (ℱ.limitProcess X μ) := by
    intro h_tendsto
    exact h_not_tendsto h_tendsto.tendsto_eLpNorm
  exact ⟨Ω, m0, μ, hμ, ℱ, X, hX, h_l1_bounded, h_ae_tendsto_limit, h_not_tendstoInLp⟩

end MeasureTheory
