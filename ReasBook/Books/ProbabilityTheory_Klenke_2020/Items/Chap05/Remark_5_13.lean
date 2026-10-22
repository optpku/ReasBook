/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_12

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory

open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

private theorem aestronglyMeasurable_centered_average
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hX_integrable : ∀ n, Integrable (X n) μ) :
    ∀ n, AEStronglyMeasurable (centered_average μ X n) μ := by
  intro n
  change AEStronglyMeasurable (fun ω ↦ (∑ i ∈ Finset.range n, (X i ω - μ[X i])) / n) μ
  exact ((integrable_finset_sum (Finset.range n) fun i _ ↦
    (hX_integrable i).sub (integrable_const _)).div_const (n : ℝ)).aestronglyMeasurable

/-- Remark 5.13: in the sense of Definition 5.12, the strong law of large numbers implies the weak
law of large numbers. -/
theorem weak_law_of_strong_law
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) :
    satisfies_strong_law_of_large_numbers μ X →
      satisfies_weak_law_of_large_numbers μ X := by
  rintro ⟨hX_integrable, hX_tendsto⟩
  refine ⟨hX_integrable, tendstoInMeasure_of_tendsto_ae ?_ hX_tendsto⟩
  intro n
  exact aestronglyMeasurable_centered_average μ hX_integrable n
