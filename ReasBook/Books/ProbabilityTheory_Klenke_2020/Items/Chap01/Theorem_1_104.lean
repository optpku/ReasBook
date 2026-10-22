/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter

open scoped Topology

-- Proof sketch: realize the probability space by the canonical Stieltjes measure `F.measure`,
-- take `X = id`, use `Measure.map_id`, and identify the cdf of `F.measure` with `F` via
-- `ProbabilityTheory.cdf_measure_stieltjesFunction`.
/-- Theorem 1.104: Every distribution function on `ℝ` is the distribution function of a real
random variable, realized on the canonical probability space `(ℝ, 𝓑(ℝ), F.measure)`. -/
theorem exists_real_randomVariable_with_distributionFunction
    (F : StieltjesFunction ℝ) (hF0 : Tendsto F atBot (𝓝 0)) (hF1 : Tendsto F atTop (𝓝 1)) :
    ∃ X : ℝ → ℝ, Measurable X ∧ ProbabilityTheory.cdf (F.measure.map X) = F := by
  -- We realize the target law on the canonical Stieltjes probability space by the identity map.
  refine ⟨fun x ↦ x, ?_, ?_⟩
  · -- The identity map on `ℝ` is measurable.
    simpa using measurable_id
  · -- Pushing `F.measure` forward along `id` changes nothing, so the standard cdf reconstruction
    -- theorem for Stieltjes measures finishes the argument.
    rw [MeasureTheory.Measure.map_id']
    simpa using ProbabilityTheory.cdf_measure_stieltjesFunction F hF0 hF1
