/-
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap07.section03_part1

open scoped BigOperators

section Chap07
section Section03

/-- Helper for Proposition 7.12: any fixed-interval strict-split witness on `Set.Icc (0 : ℝ) 1`
is, in particular, a global strict-split witness for Lebesgue outer measure. -/
lemma helperForProposition_7_12_exists_strictSplitWitness_for_volumeOuterMeasure_of_exists_fixedIcc_strictSplitWitness
    (hExists :
      ∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) <
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
                ((Set.Icc (0 : ℝ) 1) ∩ E) +
              ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
                ((Set.Icc (0 : ℝ) 1) \ E)) :
    ∃ E T : Set ℝ,
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) T <
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T ∩ E) +
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T \ E) := by
  rcases hExists with ⟨E, _, hStrict⟩
  refine ⟨E, Set.Icc (0 : ℝ) 1, ?_⟩
  simpa using hStrict

/-- Helper for Proposition 7.12: for witnesses supported in `Set.Icc (0 : ℝ) 1`, the term
`((Set.Icc (0 : ℝ) 1) ∩ E)` simplifies to `E` in the strict-split inequality. -/
lemma helperForProposition_7_12_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure_iff_interSimplified
    :
    (∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) <
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
              ((Set.Icc (0 : ℝ) 1) ∩ E) +
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
              ((Set.Icc (0 : ℝ) 1) \ E)) ↔
      (∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) <
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) E +
              ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
                ((Set.Icc (0 : ℝ) 1) \ E)) := by
  constructor
  · intro hExists
    rcases hExists with ⟨E, hE_subset, hStrict⟩
    refine ⟨E, hE_subset, ?_⟩
    simpa [Set.inter_eq_right.2 hE_subset] using hStrict
  · intro hExists
    rcases hExists with ⟨E, hE_subset, hStrict⟩
    refine ⟨E, hE_subset, ?_⟩
    simpa [Set.inter_eq_right.2 hE_subset] using hStrict

/-- Helper for Proposition 7.12: a subset `E ⊆ Set.Icc (0 : ℝ) 1` with full outer measure in
`Set.Icc (0 : ℝ) 1` and positive outer measure complement yields the fixed-interval strict-split
witness. -/
lemma helperForProposition_7_12_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure_of_exists_fullOuterMeasure_IccSubset_with_positiveComplement
    (hExists :
      ∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) E =
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) ∧
          0 <
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
              ((Set.Icc (0 : ℝ) 1) \ E)) :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) <
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
              ((Set.Icc (0 : ℝ) 1) ∩ E) +
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
              ((Set.Icc (0 : ℝ) 1) \ E) := by
  rcases hExists with ⟨E, hE_subset, hE_full, hComp_pos⟩
  refine ⟨E, hE_subset, ?_⟩
  have hIcc_ne_top :
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) ≠ ⊤ := by
    simpa [MeasureTheory.Measure.toOuterMeasure_apply, Real.volume_Icc]
  have hAdd0 :
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) + 0 <
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) +
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
            ((Set.Icc (0 : ℝ) 1) \ E) := by
    exact ENNReal.add_lt_add_left hIcc_ne_top hComp_pos
  simpa [Set.inter_eq_right.2 hE_subset, hE_full] using hAdd0

/-- Helper for Proposition 7.12: completeness of Lebesgue measure yields a bounded
non-null-measurable witness inside `Set.Icc (0 : ℝ) 1`. -/
lemma helperForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_of_isComplete
    [((MeasureTheory.volume : MeasureTheory.Measure ℝ).IsComplete)] :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  exact
    helperForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_of_exists_nonNullMeasurableSet_for_volume
      helperForProposition_7_12_exists_nonNullMeasurableSet_for_volume_of_isComplete

/-- Helper for Proposition 7.12: a bounded full-outer-measure witness with positive interval
complement already gives a bounded non-null-measurable witness in `Set.Icc (0 : ℝ) 1`. -/
lemma helperForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_of_exists_fullOuterMeasure_IccSubset_with_positiveComplement
    (hExists :
      ∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) E =
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) ∧
          0 <
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
              ((Set.Icc (0 : ℝ) 1) \ E)) :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  exact
    helperForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_of_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure
      (helperForProposition_7_12_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure_of_exists_fullOuterMeasure_IccSubset_with_positiveComplement
        hExists)

/-- Helper for Proposition 7.12: bounded upstream witness in `Set.Icc (0 : ℝ) 1` that is not
almost-everywhere equal to any measurable set for Lebesgue measure. -/
lemma helperForProposition_7_12_prereq_exists_nonNullMeasurableSet_volume_Icc :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  exact
    helperForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_of_exists_fullOuterMeasure_IccSubset_with_positiveComplement
      prereqForProposition_7_12_exists_fullOuterMeasure_IccSubset_with_positiveComplement

/-- Helper for Proposition 7.12: any bounded non-null-measurable witness in
`Set.Icc (0 : ℝ) 1` yields a fixed-interval strict-split witness for Lebesgue outer measure. -/
lemma helperForProposition_7_12_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure_of_exists_nonNullMeasurableSet_volume_Icc
    (hExists :
      ∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) <
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
              ((Set.Icc (0 : ℝ) 1) ∩ E) +
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
              ((Set.Icc (0 : ℝ) 1) \ E) := by
  have hFull :
      ∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) E =
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) ∧
          0 <
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
              ((Set.Icc (0 : ℝ) 1) \ E) :=
    helperForProposition_7_12_exists_fullOuterMeasure_IccSubset_with_positiveComplement_of_exists_nonNullMeasurableSet_volume_Icc
      hExists
  exact
    helperForProposition_7_12_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure_of_exists_fullOuterMeasure_IccSubset_with_positiveComplement
      hFull

/-- Helper for Proposition 7.12: on `Set.Icc (0 : ℝ) 1`, fixed-interval strict-split witnesses for
Lebesgue outer measure are equivalent to bounded non-null-measurable witnesses. -/
lemma helperForProposition_7_12_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure_iff_exists_nonNullMeasurableSet_volume_Icc
    :
    (∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) <
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
              ((Set.Icc (0 : ℝ) 1) ∩ E) +
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
              ((Set.Icc (0 : ℝ) 1) \ E)) ↔
      (∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  constructor
  · exact
      helperForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_of_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure
  · exact
      helperForProposition_7_12_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure_of_exists_nonNullMeasurableSet_volume_Icc

/-- Helper for Proposition 7.12: fixed-interval strict-split witnesses on `Set.Icc (0 : ℝ) 1`
are equivalent to non-Carathéodory witnesses for Lebesgue outer measure on `ℝ`. -/
lemma helperForProposition_7_12_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure_iff_exists_nonCaratheodorySet
    :
    (∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) <
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
              ((Set.Icc (0 : ℝ) 1) ∩ E) +
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
              ((Set.Icc (0 : ℝ) 1) \ E)) ↔
      (∃ E : Set ℝ,
        ¬ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E) := by
  calc
    (∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) <
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
              ((Set.Icc (0 : ℝ) 1) ∩ E) +
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
              ((Set.Icc (0 : ℝ) 1) \ E)) ↔
        (∃ E : Set ℝ,
          E ⊆ Set.Icc (0 : ℝ) 1 ∧
            ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :=
      helperForProposition_7_12_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure_iff_exists_nonNullMeasurableSet_volume_Icc
    _ ↔
        (∃ E : Set ℝ,
          ¬ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E) :=
      helperForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_iff_exists_nonCaratheodorySet

/-- Helper for Proposition 7.12: any fixed-interval strict-split witness for Lebesgue outer
measure yields a bounded witness in `Set.Icc (0 : ℝ) 1` that is not almost-everywhere equal to any
measurable set. -/
lemma helperForProposition_7_12_exists_IccWitness_notAEEq_any_measurable_of_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure
    (hExists :
      ∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) <
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
                ((Set.Icc (0 : ℝ) 1) ∩ E) +
              ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
                ((Set.Icc (0 : ℝ) 1) \ E)) :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ∀ t : Set ℝ, MeasurableSet t →
          ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t) := by
  rcases
      helperForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_of_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure
        hExists with ⟨E, hE_subset, hE_nonNull⟩
  refine ⟨E, hE_subset, ?_⟩
  exact
    helperForProposition_7_12_notAEEq_any_measurable_of_nonNullMeasurable_for_volume
      (E := E) hE_nonNull

/-- Helper for Proposition 7.12: any fixed-interval strict-split witness on
`Set.Icc (0 : ℝ) 1` yields a global non-null-measurable witness for Lebesgue measure. -/
lemma helperForProposition_7_12_exists_nonNullMeasurableSet_for_volume_of_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure
    (hExists :
      ∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) <
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
                ((Set.Icc (0 : ℝ) 1) ∩ E) +
              ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
                ((Set.Icc (0 : ℝ) 1) \ E)) :
    ∃ E : Set ℝ,
      ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  rcases
      helperForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_of_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure
        hExists with
    ⟨E, _, hE_nonNull⟩
  exact ⟨E, hE_nonNull⟩

/-- Helper for Proposition 7.12: bounded upstream witness in `Set.Icc (0 : ℝ) 1` that is not
almost-everywhere equal to any measurable set for Lebesgue measure. -/
theorem prereqForProposition_7_12_exists_set_notAEEq_any_measurableSet_volume_Icc :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ∀ t : Set ℝ, MeasurableSet t →
          ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t) := by
  exact
    helperForProposition_7_12_exists_IccWitness_notAEEq_any_measurable_of_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure
      prereqForProposition_7_12_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure

/-- Helper for Proposition 7.12: upstream prerequisite witness not almost-everywhere equal to any
measurable set for Lebesgue measure. -/
theorem prereqForProposition_7_12_exists_set_notAEEq_any_measurableSet_volume :
    ∃ E : Set ℝ,
      ∀ t : Set ℝ, MeasurableSet t →
        ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t) := by
  exact
    helperForProposition_7_12_exists_set_notAEEq_any_measurableSet_volume_of_exists_IccWitness
      prereqForProposition_7_12_exists_set_notAEEq_any_measurableSet_volume_Icc

/-- Helper for Proposition 7.12: on the bounded interval `Set.Icc (0 : ℝ) 1`, existence of a
witness not almost-everywhere equal to any measurable set is equivalent to existence of a
non-null-measurable witness for Lebesgue measure. -/
lemma helperForProposition_7_12_exists_IccWitness_notAEEq_any_measurable_iff_exists_IccWitness_nonNullMeasurable_for_volume
    :
    (∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ∀ t : Set ℝ, MeasurableSet t →
          ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t)) ↔
      (∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  constructor
  · intro hExists
    rcases hExists with ⟨E, hE_subset, hE_notAEEq⟩
    refine ⟨E, hE_subset, ?_⟩
    exact
      helperForProposition_7_12_nonNullMeasurable_of_notAEEq_any_measurable_for_volume
        (E := E) hE_notAEEq
  · intro hExists
    rcases hExists with ⟨E, hE_subset, hE_nonNull⟩
    refine ⟨E, hE_subset, ?_⟩
    exact
      helperForProposition_7_12_notAEEq_any_measurable_of_nonNullMeasurable_for_volume
        (E := E) hE_nonNull

/-- Helper for Proposition 7.12: any bounded witness in `Set.Icc (0 : ℝ) 1` that is not
almost-everywhere equal to a measurable set is a bounded non-null-measurable witness. -/
lemma helperForProposition_7_12_exists_IccWitness_nonNullMeasurable_for_volume_of_exists_IccWitness_notAEEq
    (hExists :
      ∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ∀ t : Set ℝ, MeasurableSet t →
            ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t)) :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  exact
    (helperForProposition_7_12_exists_IccWitness_notAEEq_any_measurable_iff_exists_IccWitness_nonNullMeasurable_for_volume
      ).1 hExists

/-- Helper for Proposition 7.12: any bounded non-null-measurable witness in `Set.Icc (0 : ℝ) 1`
upgrades to a bounded witness not almost-everywhere equal to any measurable set. -/
lemma helperForProposition_7_12_exists_IccWitness_notAEEq_any_measurable_for_volume_of_exists_IccWitness_nonNullMeasurable
    (hExists :
      ∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ∀ t : Set ℝ, MeasurableSet t →
          ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t) := by
  exact
    (helperForProposition_7_12_exists_IccWitness_notAEEq_any_measurable_iff_exists_IccWitness_nonNullMeasurable_for_volume
      ).2 hExists

/-- Helper for Proposition 7.12: a global witness not almost-everywhere equal to any measurable
set for Lebesgue measure is equivalent to a bounded non-null-measurable witness in
`Set.Icc (0 : ℝ) 1`. -/
lemma helperForProposition_7_12_exists_set_notAEEq_any_measurableSet_volume_iff_exists_IccWitness_nonNullMeasurable_for_volume
    :
    (∃ E : Set ℝ,
      ∀ t : Set ℝ, MeasurableSet t →
        ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t)) ↔
      (∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  constructor
  · intro hExists
    rcases
        (helperForProposition_7_12_exists_set_notAEEq_any_measurableSet_volume_iff_exists_IccWitness
          ).1 hExists with
      ⟨E, hE_subset, hE_notAEEq⟩
    exact
      (helperForProposition_7_12_exists_IccWitness_notAEEq_any_measurable_iff_exists_IccWitness_nonNullMeasurable_for_volume
        ).1 ⟨E, hE_subset, hE_notAEEq⟩
  · intro hExists
    rcases
        (helperForProposition_7_12_exists_IccWitness_notAEEq_any_measurable_iff_exists_IccWitness_nonNullMeasurable_for_volume
          ).2 hExists with
      ⟨E, hE_subset, hE_notAEEq⟩
    exact
      (helperForProposition_7_12_exists_set_notAEEq_any_measurableSet_volume_iff_exists_IccWitness
        ).2 ⟨E, hE_subset, hE_notAEEq⟩

/-- Helper for Proposition 7.12: direct bounded prerequisite witness in non-null-measurable form
for Lebesgue measure. -/
theorem prereqForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_direct :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  exact helperForProposition_7_12_prereq_exists_nonNullMeasurableSet_volume_Icc

/-- Helper for Proposition 7.12: any bounded non-null-measurable witness in `Set.Icc (0 : ℝ) 1`
yields a non-Carathéodory witness for Lebesgue outer measure. -/
lemma helperForProposition_7_12_exists_nonCaratheodorySet_of_exists_IccWitness_nonNullMeasurable
    (hExists :
      ∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    ∃ E : Set ℝ,
      ¬ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E := by
  rcases hExists with ⟨E, _, hE_nonNull⟩
  exact
    ⟨E,
      (helperForProposition_7_12_not_isCaratheodory_iff_not_nullMeasurable (E := E)).2 hE_nonNull⟩

/-- Helper for Proposition 7.12: any bounded witness in `Set.Icc (0 : ℝ) 1` that is not
almost-everywhere equal to a measurable set yields a non-null-measurable subset of `ℝ`
for Lebesgue measure. -/
lemma helperForProposition_7_12_exists_nonNullMeasurableSet_for_volume_of_exists_IccWitness_notAEEq
    (hExists :
      ∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ∀ t : Set ℝ, MeasurableSet t →
            ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t)) :
    ∃ E : Set ℝ,
      ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  rcases
      (helperForProposition_7_12_exists_IccWitness_notAEEq_any_measurable_iff_exists_IccWitness_nonNullMeasurable_for_volume
        ).1 hExists with
    ⟨E, _, hE_nonNull⟩
  exact ⟨E, hE_nonNull⟩

/-- Helper for Proposition 7.12: prerequisite existence of a non-null-measurable subset of `ℝ`
for Lebesgue measure. -/
lemma helperForProposition_7_12_exists_nonNullMeasurableSet_for_volume :
    ∃ E : Set ℝ,
      ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  exact
    helperForProposition_7_12_exists_nonNullMeasurableSet_for_volume_of_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure
      prereqForProposition_7_12_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure

/-- Helper for Proposition 7.12: any non-null-measurable witness yields a strict-split witness for
Lebesgue outer measure. -/
lemma helperForProposition_7_12_exists_strictSplitWitness_of_exists_nonNullMeasurableSet
    (hExists :
      ∃ E : Set ℝ,
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    ∃ E T : Set ℝ,
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) T <
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T ∩ E) +
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T \ E) := by
  rcases
      helperForProposition_7_12_exists_nonCaratheodorySet_of_exists_nonNullMeasurableSet hExists
    with
    ⟨E, hE⟩
  have hnot :
      ¬ ∀ t : Set ℝ,
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (t ∩ E) +
              ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (t \ E) ≤
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) t := by
    exact
      (not_congr
        (((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).isCaratheodory_iff_le
          (s := E))).1 hE
  rcases not_forall.mp hnot with ⟨T, hT⟩
  exact ⟨E, T, lt_of_not_ge hT⟩

/-- Helper for Proposition 7.12: any strict-split witness for Lebesgue outer measure yields a
non-null-measurable subset of `ℝ`. -/
lemma helperForProposition_7_12_exists_nonNullMeasurableSet_for_volume_of_exists_strictSplitWitness
    (hExists :
      ∃ E T : Set ℝ,
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) T <
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T ∩ E) +
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T \ E)) :
    ∃ E : Set ℝ,
      ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  rcases hExists with ⟨E, T, hStrict⟩
  have hNotCar :
      ¬ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E := by
    intro hCar
    have hle :
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T ∩ E) +
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T \ E) ≤
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) T := by
      exact
        (((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure.isCaratheodory_iff_le
          (s := E)).1 hCar) T
    exact (not_le_of_gt hStrict) hle
  exact ⟨E, (helperForProposition_7_12_not_isCaratheodory_iff_not_nullMeasurable).1 hNotCar⟩

/-- Helper for Proposition 7.12: for Lebesgue outer measure on `ℝ`, strict-split witnesses exist
if and only if non-null-measurable sets exist for Lebesgue measure. -/
lemma helperForProposition_7_12_exists_strictSplitWitness_for_volumeOuterMeasure_iff_exists_nonNullMeasurableSet_for_volume
    :
    (∃ E T : Set ℝ,
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) T <
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T ∩ E) +
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T \ E)) ↔
      (∃ E : Set ℝ,
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  constructor
  · exact
      helperForProposition_7_12_exists_nonNullMeasurableSet_for_volume_of_exists_strictSplitWitness
  · exact
      helperForProposition_7_12_exists_strictSplitWitness_of_exists_nonNullMeasurableSet

/-- Helper for Proposition 7.12: any bounded witness in `Set.Icc (0 : ℝ) 1` that is not
almost-everywhere equal to a measurable set yields a strict-split witness for Lebesgue outer
measure. -/
lemma helperForProposition_7_12_exists_strictSplitWitness_for_volumeOuterMeasure_of_exists_IccWitness_notAEEq
    (hExists :
      ∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ∀ t : Set ℝ, MeasurableSet t →
            ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t)) :
    ∃ E T : Set ℝ,
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) T <
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T ∩ E) +
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T \ E) := by
  have hExistsNonNull :
      ∃ E : Set ℝ,
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    helperForProposition_7_12_exists_nonNullMeasurableSet_for_volume_of_exists_IccWitness_notAEEq
      hExists
  exact
    helperForProposition_7_12_exists_strictSplitWitness_of_exists_nonNullMeasurableSet
      hExistsNonNull

/-- Helper for Proposition 7.12: prerequisite strict-split witness for Lebesgue outer measure on
`ℝ`. -/
lemma helperForProposition_7_12_exists_strictSplitWitness_for_volumeOuterMeasure :
    ∃ E T : Set ℝ,
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) T <
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T ∩ E) +
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T \ E) := by
  exact
    helperForProposition_7_12_exists_strictSplitWitness_for_volumeOuterMeasure_of_exists_fixedIcc_strictSplitWitness
      prereqForProposition_7_12_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure

/-- Helper for Proposition 7.12: any bounded witness in `Set.Icc (0 : ℝ) 1` that is not
almost-everywhere equal to any measurable set yields a non-Carathéodory witness for Lebesgue outer
measure. -/
lemma helperForProposition_7_12_exists_nonCaratheodorySet_of_exists_IccWitness_notAEEq
    (hExists :
      ∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ∀ t : Set ℝ, MeasurableSet t →
            ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t)) :
    ∃ E : Set ℝ,
      ¬ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E := by
  have hExistsNonNull :
      ∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    helperForProposition_7_12_exists_IccWitness_nonNullMeasurable_for_volume_of_exists_IccWitness_notAEEq
      hExists
  exact
    helperForProposition_7_12_exists_nonCaratheodorySet_of_exists_IccWitness_nonNullMeasurable
      hExistsNonNull

/-- Proposition 7.12 helper: there exists a subset of `ℝ` that is not Carathéodory
measurable for Lebesgue outer measure. -/
lemma helperForProposition_7_12_exists_nonCaratheodorySet :
    ∃ E : Set ℝ,
      ¬ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E :=
  by
    exact
      helperForProposition_7_12_exists_nonCaratheodorySet_of_exists_IccWitness_notAEEq
        prereqForProposition_7_12_exists_set_notAEEq_any_measurableSet_volume_Icc

/-- Helper for Proposition 7.12: non-Carathéodory measurability yields a strict split inequality. -/
lemma helperForProposition_7_12_exists_strictSplit {m : MeasureTheory.OuterMeasure ℝ} {E : Set ℝ}
    (hE : ¬ m.IsCaratheodory E) :
    ∃ T : Set ℝ, m T < m (T ∩ E) + m (T \ E) := by
  have hnot : ¬ ∀ t : Set ℝ, m (t ∩ E) + m (t \ E) ≤ m t := by
    exact (not_congr (m.isCaratheodory_iff_le (s := E))).1 hE
  rcases not_forall.mp hnot with ⟨T, hT⟩
  exact ⟨T, lt_of_not_ge hT⟩

/-- Helper for Proposition 7.12: a strict-split witness for Lebesgue outer measure follows from
the non-Carathéodory witness. -/
lemma helperForProposition_7_12_exists_strictSplit_for_volumeOuterMeasure :
    ∃ E T : Set ℝ,
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) T <
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T ∩ E) +
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T \ E) := by
  rcases helperForProposition_7_12_exists_nonCaratheodorySet with ⟨E, hE⟩
  rcases
      helperForProposition_7_12_exists_strictSplit
        (m := (MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) hE with
    ⟨T, hT⟩
  exact ⟨E, T, hT⟩

/-- Helper for Proposition 7.12: any strict split inequality certifies that the set is not
Carathéodory measurable for the outer measure. -/
lemma helperForProposition_7_12_strictSplit_implies_nonCaratheodory
    {m : MeasureTheory.OuterMeasure ℝ} {E T : Set ℝ}
    (hStrict : m T < m (T ∩ E) + m (T \ E)) :
    ¬ m.IsCaratheodory E := by
  intro hE
  have hle : m (T ∩ E) + m (T \ E) ≤ m T := by
    exact (m.isCaratheodory_iff_le (s := E)).1 hE T
  exact (not_le_of_gt hStrict) hle

/-- Helper for Proposition 7.12: non-Carathéodory measurability is equivalent to the existence
of a strict split inequality witness. -/
lemma helperForProposition_7_12_nonCaratheodory_iff_exists_strictSplit
    {m : MeasureTheory.OuterMeasure ℝ} {E : Set ℝ} :
    (¬ m.IsCaratheodory E) ↔ ∃ T : Set ℝ, m T < m (T ∩ E) + m (T \ E) := by
  constructor
  · exact helperForProposition_7_12_exists_strictSplit
  · intro hStrict
    rcases hStrict with ⟨T, hT⟩
    exact helperForProposition_7_12_strictSplit_implies_nonCaratheodory hT

/-- Helper for Proposition 7.12: the two-piece family is pairwise disjoint and unions back to `T`. -/
lemma helperForProposition_7_12_pairwiseDisjointFamilyFromTwoPieces (E T : Set ℝ) :
    Pairwise
        (fun i j : ℕ =>
          Disjoint (helperForProposition_7_12_twoPieceFamily E T i)
            (helperForProposition_7_12_twoPieceFamily E T j)) ∧
      (⋃ n : ℕ, helperForProposition_7_12_twoPieceFamily E T n) = T := by
  have hDisjInterDiff : Disjoint (T ∩ E) (T \ E) := by
    refine Set.disjoint_left.2 ?_
    intro x hxInter hxDiff
    exact hxDiff.2 hxInter.2
  refine ⟨?_, ?_⟩
  · intro i j hij
    cases i with
    | zero =>
        cases j with
        | zero => exact (hij rfl).elim
        | succ j =>
            cases j with
            | zero =>
                simpa [helperForProposition_7_12_twoPieceFamily] using hDisjInterDiff
            | succ j =>
                simp [helperForProposition_7_12_twoPieceFamily]
    | succ i =>
        cases i with
        | zero =>
            cases j with
            | zero =>
                simpa [disjoint_comm, helperForProposition_7_12_twoPieceFamily] using hDisjInterDiff
            | succ j =>
                cases j with
                | zero => exact (hij rfl).elim
                | succ j => simp [helperForProposition_7_12_twoPieceFamily]
        | succ i =>
            cases j with
            | zero => simp [helperForProposition_7_12_twoPieceFamily]
            | succ j =>
                cases j with
                | zero => simp [helperForProposition_7_12_twoPieceFamily]
                | succ j => simp [helperForProposition_7_12_twoPieceFamily]
  · ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
      cases n with
      | zero =>
          have hxInter : x ∈ T ∩ E := by
            simpa [helperForProposition_7_12_twoPieceFamily] using hn
          exact hxInter.1
      | succ n =>
          cases n with
          | zero =>
              have hxDiff : x ∈ T \ E := by
                simpa [helperForProposition_7_12_twoPieceFamily] using hn
              exact hxDiff.1
          | succ n =>
              simp [helperForProposition_7_12_twoPieceFamily] at hn
    · intro hx
      by_cases hxE : x ∈ E
      · have hx0 : x ∈ helperForProposition_7_12_twoPieceFamily E T 0 := by
          simp [helperForProposition_7_12_twoPieceFamily, hx, hxE]
        exact Set.mem_iUnion.mpr ⟨0, hx0⟩
      · have hx1 : x ∈ helperForProposition_7_12_twoPieceFamily E T 1 := by
          simp [helperForProposition_7_12_twoPieceFamily, hx, hxE]
        exact Set.mem_iUnion.mpr ⟨1, hx1⟩

/-- Helper for Proposition 7.12: the outer-measure sum of the two-piece family is the two-term sum. -/
lemma helperForProposition_7_12_tsumFamilyFromTwoPieces (m : MeasureTheory.OuterMeasure ℝ)
    (E T : Set ℝ) :
    (∑' n : ℕ, m (helperForProposition_7_12_twoPieceFamily E T n)) =
      m (T ∩ E) + m (T \ E) := by
  have htsum :
      (∑' n : ℕ, m (helperForProposition_7_12_twoPieceFamily E T n)) =
        (∑ n ∈ ({0, 1} : Finset ℕ), m (helperForProposition_7_12_twoPieceFamily E T n)) := by
    refine tsum_eq_sum ?_
    intro n hn
    have hne0 : n ≠ 0 := by
      intro h
      apply hn
      simp [h]
    have hne1 : n ≠ 1 := by
      intro h
      apply hn
      simp [h]
    simp [helperForProposition_7_12_twoPieceFamily, hne0, hne1]
  rw [htsum]
  simp [helperForProposition_7_12_twoPieceFamily]

/-- Helper for Proposition 7.12: strict two-piece inequality implies failure of countable
additivity for the associated countable family. -/
lemma helperForProposition_7_12_notEq_from_strictSplit (m : MeasureTheory.OuterMeasure ℝ)
    (E T : Set ℝ) (hStrict : m T < m (T ∩ E) + m (T \ E)) :
    m (⋃ n : ℕ, helperForProposition_7_12_twoPieceFamily E T n) ≠
      ∑' n : ℕ, m (helperForProposition_7_12_twoPieceFamily E T n) := by
  intro hEq
  have hUnion : (⋃ n : ℕ, helperForProposition_7_12_twoPieceFamily E T n) = T :=
    (helperForProposition_7_12_pairwiseDisjointFamilyFromTwoPieces E T).2
  have hTsum :
      (∑' n : ℕ, m (helperForProposition_7_12_twoPieceFamily E T n)) =
        m (T ∩ E) + m (T \ E) :=
    helperForProposition_7_12_tsumFamilyFromTwoPieces m E T
  have hEq' : m T = m (T ∩ E) + m (T \ E) := by
    calc
      m T = m (⋃ n : ℕ, helperForProposition_7_12_twoPieceFamily E T n) := by
        simpa [hUnion]
      _ = ∑' n : ℕ, m (helperForProposition_7_12_twoPieceFamily E T n) := hEq
      _ = m (T ∩ E) + m (T \ E) := hTsum
  exact (ne_of_lt hStrict) hEq'

/-- Helper for Proposition 7.12: any strict split witness for Lebesgue outer measure gives a
non-null-measurable subset of `ℝ`. -/
lemma helperForProposition_7_12_nonNullMeasurable_of_strictSplitWitness_for_volumeOuterMeasure
    {E T : Set ℝ}
    (hStrict :
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) T <
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T ∩ E) +
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T \ E)) :
    ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  have hNotCar :
      ¬ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E :=
    helperForProposition_7_12_strictSplit_implies_nonCaratheodory
      (m := (MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
      (E := E) (T := T) hStrict
  exact (helperForProposition_7_12_not_isCaratheodory_iff_not_nullMeasurable).1 hNotCar

/-- Helper for Proposition 7.12: a bounded witness in `Set.Icc (0 : ℝ) 1` that is not
almost-everywhere equal to any measurable set yields a bounded strict-split witness for Lebesgue
outer measure with the same split set. -/
lemma helperForProposition_7_12_exists_IccStrictSplitWitness_for_volumeOuterMeasure_of_exists_IccWitness_notAEEq
    (hExists :
      ∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ∀ t : Set ℝ, MeasurableSet t →
            ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t)) :
    ∃ E T : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) T <
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T ∩ E) +
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T \ E) := by
  rcases hExists with ⟨E, hE_subset, hE_notAEEq⟩
  have hE_nonNull :
      ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    helperForProposition_7_12_nonNullMeasurable_of_notAEEq_any_measurable_for_volume
      (E := E) hE_notAEEq
  have hE_notCar :
      ¬ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E :=
    (helperForProposition_7_12_not_isCaratheodory_iff_not_nullMeasurable (E := E)).2 hE_nonNull
  rcases
      (helperForProposition_7_12_nonCaratheodory_iff_exists_strictSplit
        (m := (MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
        (E := E)).1 hE_notCar with
    ⟨T, hT_strict⟩
  exact ⟨E, T, hE_subset, hT_strict⟩

/-- Helper for Proposition 7.12: a bounded strict-split witness whose split set lies in
`Set.Icc (0 : ℝ) 1` yields a bounded witness not almost-everywhere equal to any measurable set. -/
lemma helperForProposition_7_12_exists_IccWitness_notAEEq_of_exists_IccStrictSplitWitness_for_volumeOuterMeasure
    (hExists :
      ∃ E T : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) T <
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T ∩ E) +
              ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T \ E)) :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ∀ t : Set ℝ, MeasurableSet t →
          ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t) := by
  rcases hExists with ⟨E, T, hE_subset, hStrict⟩
  have hE_nonNull :
      ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    helperForProposition_7_12_nonNullMeasurable_of_strictSplitWitness_for_volumeOuterMeasure
      (E := E) (T := T) hStrict
  exact
    ⟨E, hE_subset,
      helperForProposition_7_12_notAEEq_any_measurable_of_nonNullMeasurable_for_volume
        (E := E) hE_nonNull⟩

/-- Helper for Proposition 7.12: bounded not-a.e.-equal witnesses in `Set.Icc (0 : ℝ) 1` are
equivalent to bounded strict-split witnesses for Lebesgue outer measure with split set in the same
interval. -/
lemma helperForProposition_7_12_exists_IccWitness_notAEEq_iff_exists_IccStrictSplitWitness_for_volumeOuterMeasure
    :
    (∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ∀ t : Set ℝ, MeasurableSet t →
          ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t)) ↔
      (∃ E T : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) T <
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T ∩ E) +
              ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T \ E)) := by
  constructor
  · exact
      helperForProposition_7_12_exists_IccStrictSplitWitness_for_volumeOuterMeasure_of_exists_IccWitness_notAEEq
  · exact
      helperForProposition_7_12_exists_IccWitness_notAEEq_of_exists_IccStrictSplitWitness_for_volumeOuterMeasure

/-- Helper for Proposition 7.12: a bounded strict-split witness on `Set.Icc (0 : ℝ) 1` already
produces a non-null-measurable subset of `ℝ` for Lebesgue measure. -/
lemma helperForProposition_7_12_exists_nonNullMeasurableSet_of_exists_strictSplitWitness_volume_Icc
    (hExists :
      ∃ E T : Set ℝ,
        T ⊆ Set.Icc (0 : ℝ) 1 ∧
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) T <
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T ∩ E) +
              ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T \ E)) :
    ∃ E : Set ℝ,
      ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  rcases hExists with ⟨E, T, _, hStrict⟩
  exact ⟨E,
    helperForProposition_7_12_nonNullMeasurable_of_strictSplitWitness_for_volumeOuterMeasure
      (E := E) (T := T) hStrict⟩

/-- Helper for Proposition 7.12: any strict split witness for Lebesgue outer measure directly
yields a countable pairwise-disjoint family on which outer measure fails countable additivity. -/
lemma helperForProposition_7_12_exists_family_of_exists_strictSplitWitness_for_volumeOuterMeasure
    (hExists :
      ∃ E T : Set ℝ,
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) T <
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T ∩ E) +
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (T \ E)) :
    ∃ A : ℕ → Set ℝ,
      Pairwise (fun i j : ℕ => Disjoint (A i) (A j)) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (⋃ j : ℕ, A j) ≠
          ∑' j : ℕ, ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (A j) := by
  rcases hExists with ⟨E, T, hStrict⟩
  refine ⟨helperForProposition_7_12_twoPieceFamily E T, ?_, ?_⟩
  · exact (helperForProposition_7_12_pairwiseDisjointFamilyFromTwoPieces E T).1
  · exact
      helperForProposition_7_12_notEq_from_strictSplit
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) E T hStrict

/-- Proposition 7.12 (Failure of countable additivity): there exists a countably infinite
family `(A_j)_{j∈ℕ}` of pairwise disjoint subsets of `ℝ` such that Lebesgue outer measure on
`ℝ` is not countably additive on this family:
`m*(⋃ j, A_j) ≠ ∑' j, m*(A_j)`. -/
theorem proposition_7_12 :
    ∃ A : ℕ → Set ℝ,
      Pairwise (fun i j : ℕ => Disjoint (A i) (A j)) ∧
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (⋃ j : ℕ, A j) ≠
          ∑' j : ℕ, ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (A j) := by
  exact
    helperForProposition_7_12_exists_family_of_exists_strictSplitWitness_for_volumeOuterMeasure
      helperForProposition_7_12_exists_strictSplit_for_volumeOuterMeasure

/-- Helper for Proposition 7.13: the finite two-piece family indexed by `Fin 2`,
with `0 ↦ T ∩ E` and `1 ↦ T \ E`. -/
def helperForProposition_7_13_twoPieceFamilyFin (E T : Set ℝ) : Fin 2 → Set ℝ :=
  fun i => if (i : ℕ) = 0 then T ∩ E else T \ E

/-- Helper for Proposition 7.13: the two-piece `Fin 2` family is pairwise disjoint. -/
lemma helperForProposition_7_13_pairwiseDisjoint_twoPieceFamilyFin
    (E T : Set ℝ) :
    Pairwise
      (fun i j : Fin 2 =>
        Disjoint
          (helperForProposition_7_13_twoPieceFamilyFin E T i)
          (helperForProposition_7_13_twoPieceFamilyFin E T j)) := by
  have hDisjInterDiff : Disjoint (T ∩ E) (T \ E) := by
    refine Set.disjoint_left.2 ?_
    intro x hxInter hxDiff
    exact hxDiff.2 hxInter.2
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · simpa [helperForProposition_7_13_twoPieceFamilyFin] using hDisjInterDiff
  · simpa [disjoint_comm, helperForProposition_7_13_twoPieceFamilyFin] using hDisjInterDiff
  · exact (hij rfl).elim

/-- Helper for Proposition 7.13: for the two-piece `Fin 2` family, the union has measure `m T`
and the finite sum is `m (T ∩ E) + m (T \ E)`. -/
lemma helperForProposition_7_13_union_and_sum_twoPieceFamilyFin
    (m : MeasureTheory.OuterMeasure ℝ) (E T : Set ℝ) :
    m (⋃ j : Fin 2, helperForProposition_7_13_twoPieceFamilyFin E T j) = m T ∧
      (∑ j : Fin 2, m (helperForProposition_7_13_twoPieceFamilyFin E T j)) =
        m (T ∩ E) + m (T \ E) := by
  constructor
  · have hUnion : (⋃ j : Fin 2, helperForProposition_7_13_twoPieceFamilyFin E T j) = T := by
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
        fin_cases j
        · have hxInter : x ∈ T ∩ E := by
            simpa [helperForProposition_7_13_twoPieceFamilyFin] using hj
          exact hxInter.1
        · have hxDiff : x ∈ T \ E := by
            simpa [helperForProposition_7_13_twoPieceFamilyFin] using hj
          exact hxDiff.1
      · intro hx
        by_cases hxE : x ∈ E
        · have hx0 : x ∈ helperForProposition_7_13_twoPieceFamilyFin E T 0 := by
            simp [helperForProposition_7_13_twoPieceFamilyFin, hx, hxE]
          exact Set.mem_iUnion.mpr ⟨0, hx0⟩
        · have hx1 : x ∈ helperForProposition_7_13_twoPieceFamilyFin E T 1 := by
            simp [helperForProposition_7_13_twoPieceFamilyFin, hx, hxE]
          exact Set.mem_iUnion.mpr ⟨1, hx1⟩
    simpa [hUnion]
  · simpa [Fin.sum_univ_two, helperForProposition_7_13_twoPieceFamilyFin]

/-- Helper for Proposition 7.13: a strict split inequality forces failure of finite additivity
for the associated two-piece `Fin 2` family. -/
lemma helperForProposition_7_13_notEq_from_strictSplit_fin
    (m : MeasureTheory.OuterMeasure ℝ) (E T : Set ℝ)
    (hStrict : m T < m (T ∩ E) + m (T \ E)) :
    m (⋃ j : Fin 2, helperForProposition_7_13_twoPieceFamilyFin E T j) ≠
      ∑ j : Fin 2, m (helperForProposition_7_13_twoPieceFamilyFin E T j) := by
  intro hEq
  rcases
      helperForProposition_7_13_union_and_sum_twoPieceFamilyFin (m := m) (E := E) (T := T) with
    ⟨hUnion, hSum⟩
  have hEq' : m T = m (T ∩ E) + m (T \ E) := by
    calc
      m T = m (⋃ j : Fin 2, helperForProposition_7_13_twoPieceFamilyFin E T j) := by
        simpa [hUnion]
      _ = ∑ j : Fin 2, m (helperForProposition_7_13_twoPieceFamilyFin E T j) := hEq
      _ = m (T ∩ E) + m (T \ E) := hSum
  exact (ne_of_lt hStrict) hEq'

/-- Proposition 7.13 (Failure of finite additivity): there exists a finite family
`(A_j)_{j∈J}` of pairwise disjoint subsets of `ℝ` such that Lebesgue outer measure on `ℝ`
is not finitely additive on this family:
`m*(⋃ j, A_j) ≠ ∑ j, m*(A_j)`. -/
theorem proposition_7_13 :
    ∃ n : ℕ,
      ∃ A : Fin n → Set ℝ,
        Pairwise (fun i j : Fin n => Disjoint (A i) (A j)) ∧
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (⋃ j : Fin n, A j) ≠
            ∑ j : Fin n, ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (A j) := by
  rcases helperForProposition_7_12_exists_strictSplit_for_volumeOuterMeasure with ⟨E, T, hStrict⟩
  refine ⟨2, helperForProposition_7_13_twoPieceFamilyFin E T, ?_, ?_⟩
  · exact helperForProposition_7_13_pairwiseDisjoint_twoPieceFamilyFin E T
  · exact
      helperForProposition_7_13_notEq_from_strictSplit_fin
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) E T hStrict

end Section03
end Chap07
