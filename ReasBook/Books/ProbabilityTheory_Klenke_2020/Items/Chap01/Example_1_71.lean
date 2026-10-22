/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Remark_1_70

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

-- Proof sketch: decompose any completion-measurable set as `A ∪ N` with `A` Borel measurable and
-- `N` `volume`-null using `nullMeasurableSet_iff_exists_measurable_union_null`; the agreement on
-- Borel sets identifies the measurable part, and completeness forces the null part to remain null.
/-- Any complete measure on the Lebesgue completion of `ℝ^n` that agrees with `volume` on Borel
sets is the canonical completion `Measure.completion volume`. -/
theorem complete_extension_volume_eq_completion
    {n : ℕ}
    {μ : Measure (NullMeasurableSpace (Fin n → ℝ) (volume : Measure (Fin n → ℝ)))}
    (hμc : μ.IsComplete)
    (hμ : ∀ s : Set (Fin n → ℝ), MeasurableSet s → μ s = volume s) :
    μ = Measure.completion (volume : Measure (Fin n → ℝ)) := by
  ext s hs
  rcases (nullMeasurableSet_iff_exists_measurable_union_null
      (volume : Measure (Fin n → ℝ)) (show Set (Fin n → ℝ) from s)).1 hs with
      ⟨A, N, hA, hN, rfl⟩
  have hμN : μ N = 0 := by
    rcases exists_measurable_superset_of_null hN with ⟨T, hNT, hT, hT0⟩
    have hμT : μ T = 0 := by
      rw [hμ T hT]
      exact hT0
    exact measure_mono_null hNT hμT
  have hNm : @MeasurableSet
      (NullMeasurableSpace (Fin n → ℝ) (volume : Measure (Fin n → ℝ))) inferInstance N := by
    exact hμc.out N hμN
  calc
    μ (A ∪ N) = μ A := by
      rw [measure_union₀ hNm.nullMeasurableSet (AEDisjoint.of_null_right hμN), hμN, add_zero]
    _ = volume A := hμ A hA
    _ = Measure.completion (volume : Measure (Fin n → ℝ)) (A ∪ N) := by
      symm
      exact completion_apply_union_null (volume : Measure (Fin n → ℝ)) hA hN

-- Proof sketch: use `Measure.completion volume` as the witness, whose completeness is provided by
-- `Measure.completion.isComplete`; uniqueness is `complete_extension_volume_eq_completion`.
/-- Example 1.71: The Lebesgue--Borel measure on `ℝ^n`, formalized as `volume` on `Fin n → ℝ`,
admits a unique complete extension to the `σ`-algebra of Lebesgue measurable sets, namely
`Measure.completion volume`. -/
theorem existsUnique_complete_extension_volume
    (n : ℕ) :
    ∃! μ : Measure (NullMeasurableSpace (Fin n → ℝ) (volume : Measure (Fin n → ℝ))),
      μ.IsComplete ∧
        ∀ s : Set (Fin n → ℝ), MeasurableSet s → μ s = volume s := by
  refine ⟨Measure.completion (volume : Measure (Fin n → ℝ)), ?_, ?_⟩
  · constructor
    · infer_instance
    · intro s hs
      exact Measure.completion_apply (volume : Measure (Fin n → ℝ)) s
  · intro μ hμ
    exact complete_extension_volume_eq_completion hμ.1 hμ.2
