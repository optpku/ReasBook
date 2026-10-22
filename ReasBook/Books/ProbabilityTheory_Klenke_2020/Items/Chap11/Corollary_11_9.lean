/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap04.Exercise_4_2_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Theorem_6_25

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}

/- Corollary 11.9 is `source-facing`: the mathematical content is the source equivalence for a
nonnegative martingale. Its `core/canonical` owner layer is the existing martingale API around
`UniformIntegrable` and the canonical limit random variable `ℱ.limitProcess X μ`; the reverse
implication is a `bridge/view` argument through the chapter's Scheffé theorem and the Chapter 6
`L¹`/uniform-integrability TFAE, so no extra local convergence wrapper is introduced. -/

-- Proof sketch: if the limit preserves expectation, then the martingale expectations are constant,
-- the process is `L¹`-bounded, and `Submartingale.ae_tendsto_limitProcess` gives almost-sure
-- convergence to `ℱ.limitProcess X μ`; Scheffé's theorem upgrades this to `L¹` convergence, and
-- Theorem 6.25 yields `UniformIntegrable X 1 μ`. Conversely, apply
-- `Martingale.ae_eq_condExp_limitProcess` to a uniformly integrable martingale and integrate the
-- resulting conditional-expectation identity.
/-- Corollary 11.9: if `X` is a nonnegative real-valued discrete-time martingale, then the
expectation of its canonical limit `ℱ.limitProcess X μ` equals the initial expectation exactly
when `X` is uniformly integrable. This is the textbook statement with `X_∞ = lim X_n` rendered by
the canonical limit process. -/
theorem nonnegative_martingale_limitProcess_expectation_eq_iff_uniformIntegrable
    {X : ℕ → Ω → ℝ} (hX : Martingale X ℱ μ) (hX_nonneg : 0 ≤ X) :
    μ[ℱ.limitProcess X μ] = μ[X 0] ↔ UniformIntegrable X 1 μ := by
  let Xlim : Ω → ℝ := ℱ.limitProcess X μ
  constructor
  · intro h_limit_expectation
    have h_expectation_eq : ∀ n, μ[X n] = μ[X 0] := by
      intro n
      simpa [setIntegral_univ] using (hX.setIntegral_eq (Nat.zero_le n) MeasurableSet.univ).symm
    have h_eLpNorm_eq : ∀ n, eLpNorm (X n) 1 μ = ENNReal.ofReal (μ[X 0]) := by
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
        _ = ENNReal.ofReal (μ[X 0]) := by rw [h_expectation_eq n]
    have h_tendsto_ae :
        ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (Xlim ω)) :=
      hX.submartingale.ae_tendsto_limitProcess fun n ↦ le_of_eq (h_eLpNorm_eq n)
    have h_nonneg_ae : ∀ n, 0 ≤ᵐ[μ] X n := fun n ↦ .of_forall (hX_nonneg n)
    have h_expectation_const : Tendsto (fun n ↦ μ[X n]) atTop (𝓝 (μ[X 0])) := by
      have h_eq :
          (fun n ↦ μ[X n]) = fun _ : ℕ ↦ μ[X 0] := by
        funext n
        rw [h_expectation_eq n]
      simp [h_eq]
    obtain ⟨h_limit_integrable, h_tendsto_integral_norm⟩ :=
      scheffe_of_nonnegative_ae_tendsto
        (fun n ↦ hX.integrable n) h_nonneg_ae h_tendsto_ae h_expectation_const
    have h_tendsto_integral_norm_zero :
        Tendsto (fun n ↦ ∫ ω, ‖X n ω - Xlim ω‖ ∂μ) atTop (𝓝 0) := by
      simpa [Xlim, h_limit_expectation] using h_tendsto_integral_norm
    have h_tendsto_eLpNorm :
        Tendsto (fun n ↦ eLpNorm (X n - Xlim) 1 μ) atTop (𝓝 0) := by
      have h_ofReal :
          Tendsto
            (fun n ↦ ENNReal.ofReal (∫ ω, ‖X n ω - Xlim ω‖ ∂μ))
            atTop (𝓝 (ENNReal.ofReal 0)) :=
        (ENNReal.continuous_ofReal.tendsto 0).comp h_tendsto_integral_norm_zero
      have h_eq :
          (fun n ↦ eLpNorm (X n - Xlim) 1 μ) =
            fun n ↦ ENNReal.ofReal (∫ ω, ‖X n ω - Xlim ω‖ ∂μ) := by
        funext n
        rw [eLpNorm_one_eq_lintegral_enorm]
        exact (ofReal_integral_norm_eq_lintegral_enorm
          ((hX.integrable n).sub h_limit_integrable)).symm
      simpa [h_eq] using h_ofReal
    have h_mean : TendstoInMean μ X Xlim := by
      refine (tendstoInMean_iff).2 ?_
      exact ⟨fun n ↦ hX.integrable n, h_limit_integrable, h_tendsto_eLpNorm⟩
    have h_mean_exists : ∃ Y : Ω → ℝ, TendstoInMean μ X Y := ⟨Xlim, h_mean⟩
    rcases ((integrable_sequence_tfae_tendstoInL1_cauchy_uniformIntegrable_tendstoInMeasure
      X (fun n ↦ hX.integrable n)).out 0 2).1 h_mean_exists with ⟨_, _, hUI⟩
    exact hUI
  · intro hUI
    calc
      μ[Xlim] = ∫ ω, (μ[Xlim | ℱ 0]) ω ∂μ := by
        symm
        simpa using integral_condExp (ℱ.le 0)
      _ = μ[X 0] := by
        refine integral_congr_ae ?_
        exact (hX.ae_eq_condExp_limitProcess hUI 0).symm
