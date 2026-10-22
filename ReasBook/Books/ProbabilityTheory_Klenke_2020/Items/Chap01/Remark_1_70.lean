/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

universe u

/- Remark 1.70: The completion of a measure space is formalized by
`MeasureTheory.Measure.completion μ`, the canonical extension of `μ` to the `σ`-algebra of
`μ`-null-measurable sets; this completed measure is complete and matches the textbook completion
described by adjoining null sets. -/
recall MeasureTheory.Measure.completion

-- Proof sketch: for the forward direction, use
-- `NullMeasurableSet.exists_measurable_subset_ae_eq` to choose a measurable subset `A ⊆ s` that
-- agrees with `s` almost everywhere; then `s = A ∪ (s \ A)` and `μ (s \ A) = 0`. For the reverse
-- direction, measurable sets are null measurable, null sets are null measurable by
-- `NullMeasurableSet.of_null`, and null measurability is stable under unions.
/-- A set is measurable in the completion exactly when it is the union of an original measurable
set and a `μ`-null set. -/
theorem nullMeasurableSet_iff_exists_measurable_union_null
    {α : Type u} [MeasurableSpace α] (μ : Measure α) (s : Set α) :
    NullMeasurableSet s μ ↔ ∃ A N : Set α, MeasurableSet A ∧ μ N = 0 ∧ s = A ∪ N := by
  constructor
  · intro hs
    rcases hs.exists_measurable_subset_ae_eq with ⟨A, hAs, hA, hAe⟩
    refine ⟨A, s \ A, hA, ae_le_set.1 hAe.symm.le, ?_⟩
    exact (union_diff_cancel hAs).symm
  · rintro ⟨A, N, hA, hN, rfl⟩
    exact hA.nullMeasurableSet.union_null hN

-- Proof sketch: use `Measure.completion_apply` to rewrite the left-hand side as `μ (A ∪ N)`, then
-- apply the standard measure identity for the union of a measurable set with a null set.
/-- The completion measure assigns to `A ∪ N` the same mass as `μ` assigns to the measurable part
`A` when `N` is `μ`-null. -/
theorem completion_apply_union_null
    {α : Type u} [MeasurableSpace α] (μ : Measure α) {A N : Set α}
    (hA : MeasurableSet A) (hN : μ N = 0) :
    μ.completion (A ∪ N) = μ A := by
  rw [Measure.completion_apply]
  calc
    μ (A ∪ N) = μ A + μ N :=
      measure_union₀' hA.nullMeasurableSet (AEDisjoint.of_null_right hN)
    _ = μ A := by simp [hN]
