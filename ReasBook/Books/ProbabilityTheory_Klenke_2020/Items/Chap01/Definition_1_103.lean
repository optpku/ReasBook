/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

/- Definition 1.103 (1): Item (i). For a random variable `X : Ω → Ω'` under a probability
measure `P`, its distribution `P_X = P ∘ X⁻¹` is the canonical pushforward measure `P.map X`. -/
recall MeasureTheory.Measure.map

variable {Ω : Type u} [MeasurableSpace Ω]

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- Definition 1.103 (1): a measurable random variable `X` has distribution `P.map X`, expressed
canonically as `HasLaw X (P.map X) P`. -/
theorem hasLaw_map (P : Measure Ω) {X : Ω → Ω'} (hX : Measurable X) :
    HasLaw X (P.map X) P :=
  ⟨hX.aemeasurable, rfl⟩

namespace ProbabilityTheory.HasLaw

/-- Definition 1.103 (2): if `X` has law `μ` under `P`, then the cdf of `μ` is the textbook
distribution function `x ↦ P[X ≤ x]`. -/
theorem cdf_eq_real_preimage_Iic {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    {μ : Measure ℝ} (hX : HasLaw X μ P) (x : ℝ) :
    cdf μ x = P.real (X ⁻¹' Set.Iic x) := by
  haveI : IsProbabilityMeasure μ := (hX.isProbabilityMeasure_iff).1 ‹IsProbabilityMeasure P›
  rw [cdf_eq_real]
  rw [← hX.map_eq]
  simp [Measure.real_def, Measure.map_apply_of_aemeasurable hX.aemeasurable measurableSet_Iic]

end ProbabilityTheory.HasLaw

/-- Definition 1.103 (2): Item (ii). For a real random variable `X`, the textbook distribution
function `x ↦ P[X ≤ x]` is the canonical cdf of the pushforward law `P.map X`. -/
theorem randomVariableDistributionFunction_eq_eventProbability (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X) (x : ℝ) :
    cdf (P.map X) x = P.real (X ⁻¹' Set.Iic x) :=
  (hasLaw_map P hX).cdf_eq_real_preimage_Iic x

/- Definition 1.103 (3): Item (iii). The statement that a random variable `X` has distribution `μ`
is the canonical mathlib predicate `ProbabilityTheory.HasLaw X μ P`. -/
recall ProbabilityTheory.HasLaw

/- Definition 1.103 (4): Item (iv). Two random variables are identically distributed exactly
when they satisfy the canonical relation `ProbabilityTheory.IdentDistrib`; a family `(X i)_{i ∈ I}`
is identically distributed when all pairs `X i`, `X j` satisfy this relation. -/
recall ProbabilityTheory.IdentDistrib
