/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Set

universe u v

variable {Ω : Type u} {ι : Type v}

variable [MeasurableSpace Ω]

/- Definition 2.20: for a finite set of indices `J`, the joint distribution of the family
`(X j)_{j ∈ J}` under `P` is the canonical pushforward measure
`P.map (fun ω ↦ J.restrict (X · ω))`. -/
recall MeasureTheory.Measure.map

/-- Definition 2.20: the finite-dimensional joint distribution is the law of the finite-coordinate
map `ω ↦ J.restrict (X · ω)`. -/
theorem jointDistribution_hasLaw (P : Measure Ω) (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (J : Finset ι) :
    HasLaw (fun ω ↦ J.restrict (X · ω)) (P.map (fun ω ↦ J.restrict (X · ω))) P :=
  ⟨(Finset.measurable_restrict J |>.comp (measurable_pi_lambda _ fun j ↦ hX j)).aemeasurable, rfl⟩

-- Proof sketch: rewrite the lower-orthant mass of the pushforward law using `Measure.map_apply`
-- for the measurable finite-coordinate map `ω ↦ J.restrict (X · ω)`.
/-- The finite-dimensional joint law evaluates lower orthants by the corresponding event
probability. -/
theorem jointDistribution_apply_Iic (P : Measure Ω) (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (J : Finset ι) (x : J → ℝ) :
    P.map (fun ω ↦ J.restrict (X · ω)) (Set.Iic x) =
      P (⋂ j : J, X j ⁻¹' Set.Iic (x j)) := by
  rw [Measure.map_apply]
  · congr
    ext ω
    change J.restrict (X · ω) ≤ x ↔ _
    simp [Pi.le_def]
  · exact Finset.measurable_restrict J |>.comp (measurable_pi_lambda _ fun j ↦ hX j)
  · exact measurableSet_Iic

-- Proof sketch: apply `Measure.real` to `jointDistribution_apply_Iic`.
/-- The joint distribution function evaluates the probability of the lower-orthant event
`X_j ≤ x_j` for all `j ∈ J`. -/
theorem jointDistributionFunction_eq_eventProbability (P : Measure Ω) (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (J : Finset ι) (x : J → ℝ) :
    (P.map (fun ω ↦ J.restrict (X · ω))).real (Set.Iic x) =
      P.real (⋂ j : J, X j ⁻¹' Set.Iic (x j)) := by
  rw [measureReal_def, jointDistribution_apply_Iic P X hX J x, measureReal_def]

-- Proof sketch: combine `jointDistributionFunction_eq_eventProbability` with nonnegativity of
-- `Measure.real` and the probability-measure bound `measureReal_le_one` applied to the same event.
/-- Under a probability measure, the joint distribution function takes values in the unit interval
`[0, 1]`. -/
theorem jointDistributionFunction_mem_unitInterval (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (J : Finset ι) (x : J → ℝ) :
    (P.map (fun ω ↦ J.restrict (X · ω))).real (Set.Iic x) ∈ Set.Icc (0 : ℝ) 1 := by
  rw [jointDistributionFunction_eq_eventProbability P X hX J x]
  exact ⟨measureReal_nonneg, measureReal_le_one⟩
