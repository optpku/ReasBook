/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Lebesgue measure restricted to the unit interval `[0,1]`.
local notation "unitIntervalVolume" => volume.restrict (Set.Icc (0 : ℝ) 1)

-- Proof sketch: apply `ProbabilityTheory.strong_law_ae_real` to the sequence
-- `n ↦ f ∘ X (n + 1)`, using `hX_indep` for independence and `hX_law` to obtain identical
-- distribution with common law `unitIntervalVolume`; then identify the common expectation with
-- `∫ x, f x ∂unitIntervalVolume` via `HasLaw.integral_comp`.
/-- Example 5.21: for independent samples `X₁, X₂, …` uniformly distributed on `[0,1]`, the
Monte Carlo averages `\frac{1}{n} \sum_{i=1}^n f(X_i)` converge almost surely to the integral
`∫_[0,1] f(x)\,dx` whenever `f` is integrable on `[0,1]`. -/
theorem monte_carlo_integration_ae_tendsto
    (P : Measure Ω) [IsProbabilityMeasure P] {f : ℝ → ℝ} (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_law : ∀ n, HasLaw (X (n + 1)) unitIntervalVolume P)
    (hf : Integrable f unitIntervalVolume) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, f (X (i + 1) ω)) / n) atTop
        (𝓝 (∫ x, f x ∂unitIntervalVolume)) := by
  let Y : ℕ → Ω → ℝ := fun n ω ↦ f (X (n + 1) ω)
  have hf_law : HasLaw f (Measure.map f unitIntervalVolume) unitIntervalVolume := by
    exact ⟨hf.aestronglyMeasurable.aemeasurable, rfl⟩
  have hY_law : ∀ n, HasLaw (Y n) (Measure.map f unitIntervalVolume) P := by
    intro n
    simpa [Y] using hf_law.fun_comp (hX_law n)
  have hY_integrable : Integrable (Y 0) P := by
    have hf_map : Integrable f (Measure.map (X 1) P) := by
      simpa [(hX_law 0).map_eq] using hf
    rw [show Y 0 = f ∘ X 1 by rfl]
    exact hf_map.comp_aemeasurable (hX_law 0).aemeasurable
  have hY_indep : iIndepFun Y P := by
    refine hX_indep.comp₀ (fun _ ↦ f) (fun n ↦ (hX_law n).aemeasurable) ?_
    intro n
    rw [(hX_law n).map_eq]
    exact hf.aestronglyMeasurable.aemeasurable
  have hY_pairwise : Pairwise fun i j ↦ Y i ⟂ᵢ[P] Y j := by
    intro i j hij
    exact hY_indep.indepFun hij
  have hY_ident : ∀ n, IdentDistrib (Y n) (Y 0) P P := by
    intro n
    exact (hY_law n).identDistrib (hY_law 0)
  have hY_expectation : P[Y 0] = ∫ x, f x ∂unitIntervalVolume := by
    simpa [Y] using (hX_law 0).integral_comp hf.aestronglyMeasurable
  simpa [Y, hY_expectation] using
    ProbabilityTheory.strong_law_ae_real Y hY_integrable hY_pairwise hY_ident
