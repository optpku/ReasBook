/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Remark_1_22

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

private noncomputable def euclideanSpaceFin1MeasurableEquivReal :
    EuclideanSpace ℝ (Fin 1) ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

private theorem exists_nonmeasurableSet_real : ∃ s : Set ℝ, ¬ MeasurableSet s := by
  obtain ⟨t, ht⟩ := exists_non_borel_set_euclidean 1
  refine ⟨euclideanSpaceFin1MeasurableEquivReal '' t, ?_⟩
  intro hs
  apply ht
  have hpre :
      MeasurableSet
        (euclideanSpaceFin1MeasurableEquivReal ⁻¹'
          (euclideanSpaceFin1MeasurableEquivReal '' t)) :=
    (euclideanSpaceFin1MeasurableEquivReal.measurableSet_preimage).2 hs
  simpa using hpre

-- Proof sketch: transport a nonmeasurable subset of `ℝ¹` from Remark 1.22 to a subset of `ℝ`,
-- take its indicator with value `1`, compare it almost everywhere to the measurable zero
-- function for the zero measure, and use the nonmeasurability of the underlying set.
/-- Exercise 1.4.2: in general measure spaces, almost-everywhere equality with a measurable
function does not force measurability; concretely, there exist a measure `μ` on `ℝ`, a
measurable function `f`, and a nonmeasurable function `g` such that `g = f` `μ`-almost
everywhere. -/
theorem exists_ae_eq_not_measurable :
    ∃ (μ : Measure ℝ) (f g : ℝ → ℝ), Measurable f ∧ g =ᵐ[μ] f ∧ ¬ Measurable g := by
  obtain ⟨s, hs⟩ := exists_nonmeasurableSet_real
  refine ⟨0, (fun _ ↦ (0 : ℝ)), s.indicator (fun _ ↦ (1 : ℝ)), measurable_const, ?_, ?_⟩
  · simp [ae_zero, Filter.EventuallyEq]
  · simpa [measurable_indicator_const_iff] using hs
