/-
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap07.Vitali

open scoped BigOperators

section Chap07
section Section03

/-- Helper for Proposition 7.12: a countable family built from a two-piece split of a set. -/
def helperForProposition_7_12_twoPieceFamily (E T : Set ℝ) : ℕ → Set ℝ :=
  fun n => if n = 0 then T ∩ E else if n = 1 then T \ E else ∅

/-- Helper for Proposition 7.12: a null-measurable set is Carathéodory measurable for the
associated outer measure. -/
lemma helperForProposition_7_12_nullMeasurable_implies_isCaratheodory
    (μ : MeasureTheory.Measure ℝ) {E : Set ℝ}
    (hE : MeasureTheory.NullMeasurableSet E μ) :
    μ.toOuterMeasure.IsCaratheodory E := by
  intro T
  simpa [MeasureTheory.Measure.toOuterMeasure_apply] using
    (MeasureTheory.measure_inter_add_diff₀ (μ := μ) T hE).symm

/-- Helper for Proposition 7.12: for Lebesgue outer measure on `ℝ`, Carathéodory measurability
implies null measurability. -/
lemma helperForProposition_7_12_isCaratheodory_implies_nullMeasurable
    {E : Set ℝ}
    (hE : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E) :
    MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  let U : ℕ → Set ℝ := fun n =>
    MeasureTheory.toMeasurable (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      (E ∩ Set.Icc (-(n : ℝ)) n)
  have hU_meas : ∀ n : ℕ, MeasurableSet (U n) := by
    intro n
    exact MeasureTheory.measurableSet_toMeasurable (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      (E ∩ Set.Icc (-(n : ℝ)) n)
  have hU_diff_zero : ∀ n : ℕ,
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n \ E) = 0 := by
    intro n
    have hU_eq :
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) =
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (E ∩ Set.Icc (-(n : ℝ)) n) := by
      simp [U, MeasureTheory.measure_toMeasurable]
    have hInter_le :
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (E ∩ Set.Icc (-(n : ℝ)) n) ≤
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n ∩ E) := by
      apply MeasureTheory.measure_mono
      intro x hx
      exact ⟨MeasureTheory.subset_toMeasurable (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        (E ∩ Set.Icc (-(n : ℝ)) n) hx, hx.1⟩
    have hUinter_le :
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n ∩ E) ≤
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) := by
      exact MeasureTheory.measure_mono Set.inter_subset_left
    have hUinter_ge :
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) ≤
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n ∩ E) := by
      calc
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) =
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) (E ∩ Set.Icc (-(n : ℝ)) n) := hU_eq
        _ ≤ (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n ∩ E) := hInter_le
    have hUinter_eq :
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n ∩ E) =
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) := by
      exact le_antisymm hUinter_le hUinter_ge
    have hCarU :
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) =
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n ∩ E) +
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n \ E) :=
      hE (U n)
    have hUfinite : (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) ≠ ⊤ := by
      rw [hU_eq]
      refine (lt_of_le_of_lt
        (MeasureTheory.measure_mono
          (Set.inter_subset_right : E ∩ Set.Icc (-(n : ℝ)) n ⊆ Set.Icc (-(n : ℝ)) n))
        ?_).ne
      simpa [Real.volume_Icc]
    have hAdd :
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) + 0 =
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) +
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n \ E) := by
      simpa [hUinter_eq] using hCarU
    have hAdd' :
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) +
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n \ E) =
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n) + 0 :=
      hAdd.symm
    exact (ENNReal.add_right_inj hUfinite).1 hAdd'
  let V : Set ℝ := ⋃ n : ℕ, U n
  have hSubset : E ⊆ V := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    have hxIcc : x ∈ Set.Icc (-(n : ℝ)) n := by
      have habs : -(n : ℝ) ≤ x ∧ x ≤ (n : ℝ) := (abs_le).1 hn
      exact ⟨habs.1, habs.2⟩
    have hxU : x ∈ U n := by
      exact MeasureTheory.subset_toMeasurable (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        (E ∩ Set.Icc (-(n : ℝ)) n) ⟨hx, hxIcc⟩
    exact Set.mem_iUnion.2 ⟨n, hxU⟩
  have hV_meas : MeasurableSet V := by
    exact MeasurableSet.iUnion hU_meas
  have hV_diff_zero : (MeasureTheory.volume : MeasureTheory.Measure ℝ) (V \ E) = 0 := by
    refine le_antisymm ?_ zero_le
    calc
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) (V \ E) =
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) (⋃ n : ℕ, U n \ E) := by
            simp [V, Set.iUnion_diff]
      _ ≤ ∑' n : ℕ, (MeasureTheory.volume : MeasureTheory.Measure ℝ) (U n \ E) :=
            MeasureTheory.measure_iUnion_le (fun n => U n \ E)
      _ = 0 := by simp [hU_diff_zero]
  have hAE : E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] V := by
    refine (MeasureTheory.ae_eq_set).2 ?_
    constructor
    · have hEmpty : E \ V = ∅ := Set.diff_eq_empty.2 hSubset
      simpa [hEmpty]
    · exact hV_diff_zero
  exact ⟨V, hV_meas, hAE⟩

/-- Helper for Proposition 7.12: for Lebesgue outer measure on `ℝ`, failing Carathéodory
measurability is equivalent to failing null measurability for the associated measure. -/
lemma helperForProposition_7_12_not_isCaratheodory_iff_not_nullMeasurable
    {E : Set ℝ} :
    (¬ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E) ↔
      ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  constructor
  · intro hCar hNull
    exact hCar
      (helperForProposition_7_12_nullMeasurable_implies_isCaratheodory
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hNull)
  · intro hNull hCar
    exact hNull
      (helperForProposition_7_12_isCaratheodory_implies_nullMeasurable hCar)

/-- Helper for Proposition 7.12: a non-Carathéodory witness follows from any witness of
non-null-measurability for Lebesgue measure. -/
lemma helperForProposition_7_12_exists_nonCaratheodorySet_of_exists_nonNullMeasurableSet
    (hExists :
      ∃ E : Set ℝ,
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    ∃ E : Set ℝ,
      ¬ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E := by
  rcases hExists with ⟨E, hE⟩
  exact ⟨E, (helperForProposition_7_12_not_isCaratheodory_iff_not_nullMeasurable).2 hE⟩

/-- Helper for Proposition 7.12: any non-Carathéodory witness for Lebesgue outer measure yields a
non-null-measurable set for Lebesgue measure. -/
lemma helperForProposition_7_12_exists_nonNullMeasurableSet_of_exists_nonCaratheodorySet
    (hExists :
      ∃ E : Set ℝ,
        ¬ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E) :
    ∃ E : Set ℝ,
      ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  rcases hExists with ⟨E, hE⟩
  exact ⟨E, (helperForProposition_7_12_not_isCaratheodory_iff_not_nullMeasurable).1 hE⟩

/-- Helper for Proposition 7.12: existence of a non-Carathéodory witness for Lebesgue outer
measure is equivalent to existence of a non-null-measurable witness for Lebesgue measure. -/
lemma helperForProposition_7_12_exists_nonCaratheodorySet_iff_exists_nonNullMeasurableSet_for_volume
    :
    (∃ E : Set ℝ,
      ¬ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E) ↔
      (∃ E : Set ℝ,
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  constructor
  · exact helperForProposition_7_12_exists_nonNullMeasurableSet_of_exists_nonCaratheodorySet
  · exact helperForProposition_7_12_exists_nonCaratheodorySet_of_exists_nonNullMeasurableSet

/-- Helper for Proposition 7.12: by cardinality, there exists a subset of `ℝ` that is not
measurable. -/
lemma helperForProposition_7_12_exists_notMeasurableSet_real :
    ∃ E : Set ℝ, ¬ MeasurableSet E := by
  by_contra hExists
  push_neg at hExists
  have hCountable : Set.Countable (MeasurableSpace.countableGeneratingSet ℝ) :=
    MeasurableSpace.countable_countableGeneratingSet (α := ℝ)
  have hGeneratorCard :
      Cardinal.mk (MeasurableSpace.countableGeneratingSet ℝ) ≤ Cardinal.continuum := by
    exact hCountable.le_aleph0.trans Cardinal.aleph0_le_continuum
  have hMeasurableCard :
      Cardinal.mk { s : Set ℝ // MeasurableSet s } ≤ Cardinal.continuum := by
    rw [← MeasurableSpace.generateFrom_countableGeneratingSet (α := ℝ)]
    exact MeasurableSpace.cardinal_measurableSet_le_continuum
      (s := MeasurableSpace.countableGeneratingSet ℝ) hGeneratorCard
  have hSetToMeasurable :
      Cardinal.mk (Set ℝ) ≤ Cardinal.mk { s : Set ℝ // MeasurableSet s } := by
    refine Cardinal.mk_le_of_injective
      (f := fun s : Set ℝ => (⟨s, hExists s⟩ : { s : Set ℝ // MeasurableSet s })) ?_
    intro s t hst
    exact congrArg Subtype.val hst
  have hSetCardLeContinuum : Cardinal.mk (Set ℝ) ≤ Cardinal.continuum :=
    hSetToMeasurable.trans hMeasurableCard
  have hSetCardEq : Cardinal.mk (Set ℝ) = 2 ^ Cardinal.continuum := by
    calc
      Cardinal.mk (Set ℝ) = 2 ^ Cardinal.mk ℝ := by simpa using (Cardinal.mk_set (α := ℝ))
      _ = 2 ^ Cardinal.continuum := by simpa [Cardinal.mk_real]
  have hContinuumLtSet : Cardinal.continuum < Cardinal.mk (Set ℝ) := by
    rw [hSetCardEq]
    exact Cardinal.cantor Cardinal.continuum
  exact (not_le_of_gt hContinuumLtSet) hSetCardLeContinuum

/-- Helper for Proposition 7.12: any global non-null-measurable witness for Lebesgue measure can
be translated to one contained in `Set.Icc (0 : ℝ) 1`. -/
lemma helperForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_of_exists_nonNullMeasurableSet_for_volume
    (hExists :
      ∃ E : Set ℝ,
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  rcases hExists with ⟨E, hE⟩
  have hPieceExists :
      ∃ n : ℤ,
        ¬ MeasureTheory.NullMeasurableSet (E ∩ Set.Icc (n : ℝ) ((n : ℝ) + 1))
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    have hCover : (⋃ n : ℤ, Set.Icc (n : ℝ) ((n : ℝ) + 1)) = (Set.univ : Set ℝ) := by
      simpa using (iUnion_Icc_intCast ℝ)
    have hDecomp : E = ⋃ n : ℤ, E ∩ Set.Icc (n : ℝ) ((n : ℝ) + 1) := by
      ext x
      constructor
      · intro hx
        have hxCover : x ∈ (⋃ n : ℤ, Set.Icc (n : ℝ) ((n : ℝ) + 1)) := by
          simpa [hCover] using (show x ∈ (Set.univ : Set ℝ) from trivial)
        rcases Set.mem_iUnion.mp hxCover with ⟨n, hn⟩
        exact Set.mem_iUnion.mpr ⟨n, ⟨hx, hn⟩⟩
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
        exact hn.1
    by_contra h
    have hAll : ∀ n : ℤ,
        MeasureTheory.NullMeasurableSet (E ∩ Set.Icc (n : ℝ) ((n : ℝ) + 1))
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
      intro n
      by_contra hn
      exact h ⟨n, hn⟩
    have hE' : MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
      rw [hDecomp]
      exact MeasureTheory.NullMeasurableSet.iUnion hAll
    exact hE hE'
  rcases hPieceExists with ⟨n, hn⟩
  let A : Set ℝ :=
    (fun x : ℝ => x + (-(n : ℝ))) '' (E ∩ Set.Icc (n : ℝ) ((n : ℝ) + 1))
  have hA_subset : A ⊆ Set.Icc (0 : ℝ) 1 := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    constructor
    · have hxleft : (n : ℝ) ≤ x := hx.2.1
      linarith
    · have hxright : x ≤ (n : ℝ) + 1 := hx.2.2
      linarith
  have hA_not_nullMeasurable :
      ¬ MeasureTheory.NullMeasurableSet A (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    intro hA
    have hpre :
        MeasureTheory.NullMeasurableSet
          ((fun x : ℝ => x + (-(n : ℝ))) ⁻¹' A)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
      hA.preimage
        (MeasureTheory.quasiMeasurePreserving_add_right
          (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (g := (-(n : ℝ))))
    have hpre_eq :
        ((fun x : ℝ => x + (-(n : ℝ))) ⁻¹' A) =
          E ∩ Set.Icc (n : ℝ) ((n : ℝ) + 1) := by
      let f : ℝ → ℝ := fun x => x + (-(n : ℝ))
      have hf_inj : Function.Injective f := by
        intro x y hxy
        dsimp [f] at hxy
        linarith
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, hyx⟩
        exact (hf_inj hyx) ▸ hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hPieceNull :
        MeasureTheory.NullMeasurableSet (E ∩ Set.Icc (n : ℝ) ((n : ℝ) + 1))
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
      simpa [hpre_eq] using hpre
    exact hn hPieceNull
  exact ⟨A, hA_subset, hA_not_nullMeasurable⟩

/-- Helper for Proposition 7.12: if Lebesgue measure on `ℝ` were complete, then any witness of
non-measurability would also be a witness of non-null-measurability. -/
lemma helperForProposition_7_12_exists_nonNullMeasurableSet_for_volume_of_isComplete
    [((MeasureTheory.volume : MeasureTheory.Measure ℝ).IsComplete)] :
    ∃ E : Set ℝ,
      ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  rcases helperForProposition_7_12_exists_notMeasurableSet_real with ⟨E, hE_not_measurable⟩
  refine ⟨E, ?_⟩
  intro hE_nullMeasurable
  exact hE_not_measurable hE_nullMeasurable.measurable_of_complete

/-- Helper for Proposition 7.12: for a complete measure on `ℝ`, any non-measurable set cannot be
almost-everywhere equal to a measurable set. -/
lemma helperForProposition_7_12_notAEEq_any_measurable_of_notMeasurable_of_complete
    (μ : MeasureTheory.Measure ℝ) [μ.IsComplete] {E : Set ℝ}
    (hE_not_measurable : ¬ MeasurableSet E) :
    ∀ t : Set ℝ, MeasurableSet t → ¬ (E =ᵐ[μ] t) := by
  intro t ht_meas hEae
  have ht_null : MeasureTheory.NullMeasurableSet t μ := ht_meas.nullMeasurableSet
  have hE_null : MeasureTheory.NullMeasurableSet E μ := ht_null.congr hEae.symm
  exact hE_not_measurable hE_null.measurable_of_complete

/-- Helper for Proposition 7.12: for a complete measure on `ℝ`, existence of a non-measurable set
implies existence of a set not almost-everywhere equal to any measurable set. -/
lemma helperForProposition_7_12_exists_notAEEq_any_measurable_of_exists_notMeasurable_of_complete
    (μ : MeasureTheory.Measure ℝ) [μ.IsComplete]
    (hExists : ∃ E : Set ℝ, ¬ MeasurableSet E) :
    ∃ E : Set ℝ, ∀ t : Set ℝ, MeasurableSet t → ¬ (E =ᵐ[μ] t) := by
  rcases hExists with ⟨E, hE_not_measurable⟩
  exact
    ⟨E,
      helperForProposition_7_12_notAEEq_any_measurable_of_notMeasurable_of_complete
        (μ := μ) hE_not_measurable⟩

/-- Helper for Proposition 7.12: under completeness of Lebesgue measure on `ℝ`, one gets a global
upstream witness not almost-everywhere equal to any measurable set. -/
lemma helperForProposition_7_12_exists_set_notAEEq_any_measurableSet_volume_of_isComplete
    [((MeasureTheory.volume : MeasureTheory.Measure ℝ).IsComplete)] :
    ∃ E : Set ℝ,
      ∀ t : Set ℝ, MeasurableSet t →
        ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t) := by
  exact
    helperForProposition_7_12_exists_notAEEq_any_measurable_of_exists_notMeasurable_of_complete
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      helperForProposition_7_12_exists_notMeasurableSet_real

/-- Helper for Proposition 7.12: a set that is not almost-everywhere equal to any measurable set
cannot be null measurable for Lebesgue measure. -/
lemma helperForProposition_7_12_nonNullMeasurable_of_notAEEq_any_measurable_for_volume
    {E : Set ℝ}
    (hNotAEEq :
      ∀ t : Set ℝ, MeasurableSet t →
        ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t)) :
    ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  intro hE_nullMeasurable
  rcases hE_nullMeasurable.exists_measurable_superset_ae_eq with ⟨t, _, ht_meas, ht_ae_eq⟩
  exact hNotAEEq t ht_meas ht_ae_eq.symm

/-- Helper for Proposition 7.12: a non-null-measurable set cannot be almost-everywhere equal to a
measurable set for Lebesgue measure. -/
lemma helperForProposition_7_12_notAEEq_any_measurable_of_nonNullMeasurable_for_volume
    {E : Set ℝ}
    (hE :
      ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    ∀ t : Set ℝ, MeasurableSet t →
      ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t) := by
  intro t ht_meas hEae
  have ht_null :
      MeasureTheory.NullMeasurableSet t (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    ht_meas.nullMeasurableSet
  have hE_null :
      MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    ht_null.congr hEae.symm
  exact hE hE_null

/-- Helper for Proposition 7.12: for Lebesgue measure, being not almost-everywhere equal to any
measurable set is equivalent to failing null measurability. -/
lemma helperForProposition_7_12_notAEEq_any_measurable_iff_nonNullMeasurable_for_volume
    {E : Set ℝ} :
    (∀ t : Set ℝ, MeasurableSet t →
      ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t)) ↔
      ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  constructor
  · exact helperForProposition_7_12_nonNullMeasurable_of_notAEEq_any_measurable_for_volume
  · exact helperForProposition_7_12_notAEEq_any_measurable_of_nonNullMeasurable_for_volume

/-- Helper for Proposition 7.12: existential forms of the previous equivalence for Lebesgue
measure. -/
lemma helperForProposition_7_12_exists_notAEEq_any_measurable_iff_exists_nonNullMeasurable_for_volume
    :
    (∃ E : Set ℝ,
      ∀ t : Set ℝ, MeasurableSet t →
        ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t)) ↔
      (∃ E : Set ℝ,
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  constructor
  · intro hExists
    rcases hExists with ⟨E, hE⟩
    exact
      ⟨E,
        (helperForProposition_7_12_notAEEq_any_measurable_iff_nonNullMeasurable_for_volume
          (E := E)).1 hE⟩
  · intro hExists
    rcases hExists with ⟨E, hE⟩
    exact
      ⟨E,
        (helperForProposition_7_12_notAEEq_any_measurable_iff_nonNullMeasurable_for_volume
          (E := E)).2 hE⟩

/-- Helper for Proposition 7.12: any witness not almost-everywhere equal to a measurable set gives
a non-null-measurable witness for Lebesgue measure. -/
lemma helperForProposition_7_12_exists_nonNullMeasurableSet_for_volume_of_exists_notAEEq_measurable
    (hExists :
      ∃ E : Set ℝ,
        ∀ t : Set ℝ, MeasurableSet t →
          ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t)) :
    ∃ E : Set ℝ,
      ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  exact
    (helperForProposition_7_12_exists_notAEEq_any_measurable_iff_exists_nonNullMeasurable_for_volume
      ).1 hExists

/-- Helper for Proposition 7.12: a bounded witness on `Set.Icc (0 : ℝ) 1` that is not
almost-everywhere equal to any measurable set is, in particular, such a global witness on `ℝ`. -/
lemma helperForProposition_7_12_exists_set_notAEEq_any_measurableSet_volume_of_exists_IccWitness
    (hExists :
      ∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ∀ t : Set ℝ, MeasurableSet t →
            ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t)) :
    ∃ E : Set ℝ,
      ∀ t : Set ℝ, MeasurableSet t →
        ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t) := by
  rcases hExists with ⟨E, _, hE⟩
  exact ⟨E, hE⟩

/-- Helper for Proposition 7.12: any global witness on `ℝ` that is not almost-everywhere equal to
any measurable set yields a bounded witness inside `Set.Icc (0 : ℝ) 1`. -/
lemma helperForProposition_7_12_exists_IccWitness_of_exists_set_notAEEq_any_measurableSet_volume
    (hExists :
      ∃ E : Set ℝ,
        ∀ t : Set ℝ, MeasurableSet t →
          ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t)) :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ∀ t : Set ℝ, MeasurableSet t →
          ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t) := by
  have hExists_nonNull :
      ∃ E : Set ℝ,
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    helperForProposition_7_12_exists_nonNullMeasurableSet_for_volume_of_exists_notAEEq_measurable
      hExists
  rcases
      helperForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_of_exists_nonNullMeasurableSet_for_volume
        hExists_nonNull with
    ⟨E, hE_subset, hE_nonNull⟩
  refine ⟨E, hE_subset, ?_⟩
  exact
    helperForProposition_7_12_notAEEq_any_measurable_of_nonNullMeasurable_for_volume
      (E := E) hE_nonNull

/-- Helper for Proposition 7.12: existence of a global witness not almost-everywhere equal to any
measurable set is equivalent to existence of such a witness already in `Set.Icc (0 : ℝ) 1`. -/
lemma helperForProposition_7_12_exists_set_notAEEq_any_measurableSet_volume_iff_exists_IccWitness
    :
    (∃ E : Set ℝ,
      ∀ t : Set ℝ, MeasurableSet t →
        ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t)) ↔
      (∃ E : Set ℝ,
        E ⊆ Set.Icc (0 : ℝ) 1 ∧
          ∀ t : Set ℝ, MeasurableSet t →
            ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t)) := by
  constructor
  · exact
      helperForProposition_7_12_exists_IccWitness_of_exists_set_notAEEq_any_measurableSet_volume
  · exact
      helperForProposition_7_12_exists_set_notAEEq_any_measurableSet_volume_of_exists_IccWitness

/-- Helper for Proposition 7.12: bounded upstream witness in `Set.Icc (0 : ℝ) 1` that is not
almost-everywhere equal to any measurable set for Lebesgue measure. -/
lemma helperForProposition_7_12_exists_IccWitness_notAEEq_any_measurableSet_volume_of_isComplete
    [((MeasureTheory.volume : MeasureTheory.Measure ℝ).IsComplete)] :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ∀ t : Set ℝ, MeasurableSet t →
          ¬ (E =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] t) := by
  exact
    helperForProposition_7_12_exists_IccWitness_of_exists_set_notAEEq_any_measurableSet_volume
      helperForProposition_7_12_exists_set_notAEEq_any_measurableSet_volume_of_isComplete

/-- Helper for Proposition 7.12: bounded upstream witness in `Set.Icc (0 : ℝ) 1` that is not
almost-everywhere equal to any measurable set for Lebesgue measure. -/
lemma helperForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_of_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure
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
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  rcases hExists with ⟨E, hE_subset, hStrict⟩
  refine ⟨E, hE_subset, ?_⟩
  intro hE_null
  have hE_car :
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E :=
    helperForProposition_7_12_nullMeasurable_implies_isCaratheodory
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hE_null
  have hEq :
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) =
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) ((Set.Icc (0 : ℝ) 1) ∩ E) +
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) ((Set.Icc (0 : ℝ) 1) \ E) :=
    hE_car (Set.Icc (0 : ℝ) 1)
  have hLtSelf :
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) <
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) := by
    simpa [hEq] using hStrict
  exact (lt_irrefl _ hLtSelf)

/-- Helper for Proposition 7.12: measurable-hull truncation of a set to `Set.Icc (0 : ℝ) 1`. -/
def helperForProposition_7_12_IccMeasurableHull (A : Set ℝ) : Set ℝ :=
  (MeasureTheory.toMeasurable (MeasureTheory.volume : MeasureTheory.Measure ℝ) A) ∩
    Set.Icc (0 : ℝ) 1

/-- Helper for Proposition 7.12: full-outer-measure candidate built from a set inside
`Set.Icc (0 : ℝ) 1`. -/
def helperForProposition_7_12_IccFullOuterMeasureCandidate (A : Set ℝ) : Set ℝ :=
  A ∪ ((Set.Icc (0 : ℝ) 1) \ helperForProposition_7_12_IccMeasurableHull A)

/-- Helper for Proposition 7.12: for `A ⊆ Set.Icc (0 : ℝ) 1`, the measurable-hull construction
stays in the interval, has full Lebesgue outer measure there, and has explicit interval
complement. -/
lemma helperForProposition_7_12_IccFullOuterMeasureCandidate_properties
    {A : Set ℝ} (hA_subset_Icc : A ⊆ Set.Icc (0 : ℝ) 1) :
    helperForProposition_7_12_IccFullOuterMeasureCandidate A ⊆ Set.Icc (0 : ℝ) 1 ∧
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
          (helperForProposition_7_12_IccFullOuterMeasureCandidate A) =
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) ∧
      (Set.Icc (0 : ℝ) 1 \ helperForProposition_7_12_IccFullOuterMeasureCandidate A) =
        helperForProposition_7_12_IccMeasurableHull A \ A := by
  let μ : MeasureTheory.Measure ℝ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)
  let m : MeasureTheory.OuterMeasure ℝ := μ.toOuterMeasure
  let B : Set ℝ := helperForProposition_7_12_IccMeasurableHull A
  let E : Set ℝ := helperForProposition_7_12_IccFullOuterMeasureCandidate A
  have hB_meas : MeasurableSet B := by
    dsimp [B, helperForProposition_7_12_IccMeasurableHull]
    exact (MeasureTheory.measurableSet_toMeasurable μ A).inter measurableSet_Icc
  have hA_subset_B : A ⊆ B := by
    intro x hxA
    dsimp [B, helperForProposition_7_12_IccMeasurableHull]
    exact ⟨MeasureTheory.subset_toMeasurable μ A hxA, hA_subset_Icc hxA⟩
  have hB_subset_Icc : B ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hxB
    exact hxB.2
  have hμB_eq_hμA : μ B = μ A := by
    dsimp [B, helperForProposition_7_12_IccMeasurableHull]
    calc
      μ ((MeasureTheory.toMeasurable μ A) ∩ Set.Icc (0 : ℝ) 1) =
          μ (A ∩ Set.Icc (0 : ℝ) 1) := by
            simpa using
              (MeasureTheory.Measure.measure_toMeasurable_inter_of_sFinite
                (μ := μ) (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc A)
      _ = μ A := by
            congr
            ext x
            constructor
            · intro hx
              exact hx.1
            · intro hx
              exact ⟨hx, hA_subset_Icc hx⟩
  have hE_subset_Icc : E ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hxE
    rcases hxE with hxA | hxC
    · exact hA_subset_Icc hxA
    · exact hxC.1
  have hC_meas : MeasurableSet ((Set.Icc (0 : ℝ) 1) \ B) := by
    exact measurableSet_Icc.diff hB_meas
  have hC_car : m.IsCaratheodory ((Set.Icc (0 : ℝ) 1) \ B) :=
    helperForProposition_7_12_nullMeasurable_implies_isCaratheodory
      (μ := μ) hC_meas.nullMeasurableSet
  have hE_inter_C : E ∩ ((Set.Icc (0 : ℝ) 1) \ B) = ((Set.Icc (0 : ℝ) 1) \ B) := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨Or.inr hx, hx⟩
  have hE_diff_C : E \ ((Set.Icc (0 : ℝ) 1) \ B) = A := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxE, hxNotC⟩
      rcases hxE with hxA | hxC
      · exact hxA
      · exact False.elim (hxNotC hxC)
    · intro hxA
      refine ⟨Or.inl hxA, ?_⟩
      intro hxC
      exact hxC.2 (hA_subset_B hxA)
  have hμB_add_hμC :
      μ B + μ ((Set.Icc (0 : ℝ) 1) \ B) = μ (Set.Icc (0 : ℝ) 1) := by
    have hIcc_inter_B : Set.Icc (0 : ℝ) 1 ∩ B = B := Set.inter_eq_right.2 hB_subset_Icc
    have hInterAddDiff :
        μ (Set.Icc (0 : ℝ) 1 ∩ B) + μ (Set.Icc (0 : ℝ) 1 \ B) = μ (Set.Icc (0 : ℝ) 1) :=
      MeasureTheory.measure_inter_add_diff (μ := μ) (s := Set.Icc (0 : ℝ) 1) hB_meas
    simpa [hIcc_inter_B] using hInterAddDiff
  have hE_full : m E = m (Set.Icc (0 : ℝ) 1) := by
    calc
      m E = m (E ∩ ((Set.Icc (0 : ℝ) 1) \ B)) + m (E \ ((Set.Icc (0 : ℝ) 1) \ B)) := hC_car E
      _ = m ((Set.Icc (0 : ℝ) 1) \ B) + m A := by
            simpa [hE_inter_C, hE_diff_C]
      _ = μ ((Set.Icc (0 : ℝ) 1) \ B) + μ A := by
            simp [m, MeasureTheory.Measure.toOuterMeasure_apply]
      _ = μ ((Set.Icc (0 : ℝ) 1) \ B) + μ B := by rw [hμB_eq_hμA]
      _ = μ (Set.Icc (0 : ℝ) 1) := by
            simpa [add_comm] using hμB_add_hμC
      _ = m (Set.Icc (0 : ℝ) 1) := by simp [m, MeasureTheory.Measure.toOuterMeasure_apply]
  have hComp_eq : (Set.Icc (0 : ℝ) 1) \ E = B \ A := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · have hxNotC : x ∉ ((Set.Icc (0 : ℝ) 1) \ B) := by
          intro hxC
          exact hx.2 (Or.inr hxC)
        by_contra hxNotB
        exact hxNotC ⟨hx.1, hxNotB⟩
      · intro hxA
        exact hx.2 (Or.inl hxA)
    · intro hx
      refine ⟨hB_subset_Icc hx.1, ?_⟩
      intro hxE
      rcases hxE with hxA | hxC
      · exact hx.2 hxA
      · exact hxC.2 hx.1
  refine ⟨hE_subset_Icc, ?_, ?_⟩
  · simpa [μ, m, E, helperForProposition_7_12_IccFullOuterMeasureCandidate] using hE_full
  · simpa [B, E, helperForProposition_7_12_IccMeasurableHull,
      helperForProposition_7_12_IccFullOuterMeasureCandidate] using hComp_eq

/-- Helper for Proposition 7.12: if `A ⊆ Set.Icc (0 : ℝ) 1` is not null measurable for Lebesgue
measure, then the interval complement of the measurable-hull construction has positive outer
measure. -/
lemma helperForProposition_7_12_positiveComplement_of_nonNullMeasurable_IccFullOuterMeasureCandidate
    {A : Set ℝ}
    (hA_subset_Icc : A ⊆ Set.Icc (0 : ℝ) 1)
    (hA_nonNull :
      ¬ MeasureTheory.NullMeasurableSet A (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    0 <
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
        ((Set.Icc (0 : ℝ) 1) \ helperForProposition_7_12_IccFullOuterMeasureCandidate A) := by
  let μ : MeasureTheory.Measure ℝ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)
  let B : Set ℝ := helperForProposition_7_12_IccMeasurableHull A
  have hB_meas : MeasurableSet B := by
    dsimp [B, helperForProposition_7_12_IccMeasurableHull]
    exact (MeasureTheory.measurableSet_toMeasurable μ A).inter measurableSet_Icc
  have hA_subset_B : A ⊆ B := by
    intro x hxA
    dsimp [B, helperForProposition_7_12_IccMeasurableHull]
    exact ⟨MeasureTheory.subset_toMeasurable μ A hxA, hA_subset_Icc hxA⟩
  have hDiff_pos : 0 < μ (B \ A) := by
    have hDiff_ne_zero : μ (B \ A) ≠ 0 := by
      intro hZero
      have hAaeB : A =ᵐ[μ] B := by
        refine (MeasureTheory.ae_eq_set).2 ?_
        constructor
        · have hAB_empty : A \ B = ∅ := Set.diff_eq_empty.2 hA_subset_B
          simpa [hAB_empty]
        · simpa using hZero
      have hA_null : MeasureTheory.NullMeasurableSet A μ :=
        hB_meas.nullMeasurableSet.congr hAaeB.symm
      exact hA_nonNull (by simpa [μ] using hA_null)
    exact lt_of_le_of_ne zero_le (Ne.symm hDiff_ne_zero)
  have hComp_eq :
      (Set.Icc (0 : ℝ) 1 \ helperForProposition_7_12_IccFullOuterMeasureCandidate A) = B \ A := by
    simpa [B] using
      (helperForProposition_7_12_IccFullOuterMeasureCandidate_properties (A := A) hA_subset_Icc).2.2
  have hDiff_pos_outer :
      0 < ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (B \ A) := by
    simpa [μ, MeasureTheory.Measure.toOuterMeasure_apply] using hDiff_pos
  simpa [hComp_eq] using hDiff_pos_outer

/-- Helper for Proposition 7.12: any bounded non-null-measurable witness in `Set.Icc (0 : ℝ) 1`
yields a bounded witness with full outer measure and positive-complement outer measure. -/
lemma helperForProposition_7_12_exists_fullOuterMeasure_IccSubset_with_positiveComplement_of_exists_nonNullMeasurableSet_volume_Icc
    (hExists :
      ∃ A : Set ℝ,
        A ⊆ Set.Icc (0 : ℝ) 1 ∧
          ¬ MeasureTheory.NullMeasurableSet A (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) E =
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) ∧
        0 <
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
            ((Set.Icc (0 : ℝ) 1) \ E) := by
  rcases hExists with ⟨A, hA_subset_Icc, hA_nonNull⟩
  refine ⟨helperForProposition_7_12_IccFullOuterMeasureCandidate A, ?_, ?_, ?_⟩
  · exact
      (helperForProposition_7_12_IccFullOuterMeasureCandidate_properties
        (A := A) hA_subset_Icc).1
  · exact
      (helperForProposition_7_12_IccFullOuterMeasureCandidate_properties
        (A := A) hA_subset_Icc).2.1
  · exact
      helperForProposition_7_12_positiveComplement_of_nonNullMeasurable_IccFullOuterMeasureCandidate
        (A := A) hA_subset_Icc hA_nonNull

/-- Helper for Proposition 7.12: any bounded non-null-measurable witness in
`Set.Icc (0 : ℝ) 1` is in particular a global non-null-measurable witness. -/
lemma helperForProposition_7_12_exists_nonNullMeasurableSet_for_volume_of_exists_nonNullMeasurableSet_volume_Icc
    (hExists :
      ∃ A : Set ℝ,
        A ⊆ Set.Icc (0 : ℝ) 1 ∧
          ¬ MeasureTheory.NullMeasurableSet A (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    ∃ E : Set ℝ,
      ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  rcases hExists with ⟨A, _, hA_nonNull⟩
  exact ⟨A, hA_nonNull⟩

/-- Helper for Proposition 7.12: bounded and global existence forms of non-null-measurable
witnesses for Lebesgue measure are equivalent. -/
lemma helperForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_iff_exists_nonNullMeasurableSet_for_volume
    :
    (∃ A : Set ℝ,
      A ⊆ Set.Icc (0 : ℝ) 1 ∧
        ¬ MeasureTheory.NullMeasurableSet A (MeasureTheory.volume : MeasureTheory.Measure ℝ)) ↔
      (∃ E : Set ℝ,
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  constructor
  · exact
      helperForProposition_7_12_exists_nonNullMeasurableSet_for_volume_of_exists_nonNullMeasurableSet_volume_Icc
  · exact
      helperForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_of_exists_nonNullMeasurableSet_for_volume

/-- Helper for Proposition 7.12: bounded non-null-measurable witnesses in `Set.Icc (0 : ℝ) 1`
are equivalent to non-Carathéodory witnesses for Lebesgue outer measure on `ℝ`. -/
lemma helperForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_iff_exists_nonCaratheodorySet
    :
    (∃ A : Set ℝ,
      A ⊆ Set.Icc (0 : ℝ) 1 ∧
        ¬ MeasureTheory.NullMeasurableSet A (MeasureTheory.volume : MeasureTheory.Measure ℝ)) ↔
      (∃ E : Set ℝ,
        ¬ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E) := by
  constructor
  · intro hExistsIcc
    have hExistsGlobal :
        ∃ E : Set ℝ,
          ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
      helperForProposition_7_12_exists_nonNullMeasurableSet_for_volume_of_exists_nonNullMeasurableSet_volume_Icc
        hExistsIcc
    exact
      helperForProposition_7_12_exists_nonCaratheodorySet_of_exists_nonNullMeasurableSet
        hExistsGlobal
  · intro hExistsCar
    have hExistsGlobal :
        ∃ E : Set ℝ,
          ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
      helperForProposition_7_12_exists_nonNullMeasurableSet_of_exists_nonCaratheodorySet hExistsCar
    exact
      helperForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_of_exists_nonNullMeasurableSet_for_volume
        hExistsGlobal

/-- Helper for Proposition 7.12: any measure-zero set is Carathéodory measurable for the
outer measure induced by the same measure. -/
lemma helperForProposition_7_12_isCaratheodory_of_measure_eq_zero
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) {E : Set α}
    (hE_zero : μ E = 0) :
    μ.toOuterMeasure.IsCaratheodory E := by
  intro T
  simpa [MeasureTheory.Measure.toOuterMeasure_apply] using
    (MeasureTheory.measure_inter_add_diff₀ (μ := μ) T
      (MeasureTheory.NullMeasurableSet.of_null hE_zero)).symm

/-- Helper for Proposition 7.12: if a measure is not complete, then there exists a measure-zero
set that is not measurable. -/
lemma helperForProposition_7_12_exists_zeroMeasure_notMeasurableSet_of_not_isComplete
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (hIncomplete : ¬ μ.IsComplete) :
    ∃ E : Set α, μ E = 0 ∧ ¬ MeasurableSet E := by
  rw [MeasureTheory.Measure.isComplete_iff] at hIncomplete
  push_neg at hIncomplete
  rcases hIncomplete with ⟨E, hE_zero, hE_not_meas⟩
  exact ⟨E, hE_zero, hE_not_meas⟩

/-- Helper for Proposition 7.12: if Lebesgue measure on `ℝ` is complete, then any non-measurable
subset witness yields a non-Carathéodory witness for Lebesgue outer measure. -/
lemma helperForProposition_7_12_exists_nonCaratheodorySet_of_exists_notMeasurableSet_for_volume_of_isComplete
    [((MeasureTheory.volume : MeasureTheory.Measure ℝ).IsComplete)]
    (hExists : ∃ E : Set ℝ, ¬ MeasurableSet E) :
    ∃ E : Set ℝ,
      ¬ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E := by
  have hExistsNonNull :
      ∃ E : Set ℝ,
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    rcases hExists with ⟨E, hE_not_measurable⟩
    refine ⟨E, ?_⟩
    intro hE_nullMeasurable
    exact hE_not_measurable hE_nullMeasurable.measurable_of_complete
  exact
    helperForProposition_7_12_exists_nonCaratheodorySet_of_exists_nonNullMeasurableSet
      hExistsNonNull

/-- Helper for Proposition 7.12: under completeness of Lebesgue measure on `ℝ`, there exists a
non-Carathéodory witness for Lebesgue outer measure. -/
lemma helperForProposition_7_12_exists_nonCaratheodorySet_for_volumeOuterMeasure_of_isComplete
    [((MeasureTheory.volume : MeasureTheory.Measure ℝ).IsComplete)] :
    ∃ E : Set ℝ,
      ¬ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E := by
  exact
    helperForProposition_7_12_exists_nonCaratheodorySet_of_exists_notMeasurableSet_for_volume_of_isComplete
      helperForProposition_7_12_exists_notMeasurableSet_real

/-- Helper for Proposition 7.12: upstream Vitali-type bounded witness in `Set.Icc (0 : ℝ) 1`
that is not null measurable for Lebesgue measure. -/
theorem helperForProposition_7_12_upstream_exists_nonNullMeasurableSet_volume_Icc_real :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  exact exists_nonNullMeasurableSet_volume_Icc_real

/-- Helper for Proposition 7.12: upstream non-Carathéodory witness for Lebesgue outer measure on
`ℝ`. -/
theorem prereqForProposition_7_12_exists_nonCaratheodorySet_for_volumeOuterMeasure_upstream :
    ∃ E : Set ℝ,
      ¬ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E := by
  rcases helperForProposition_7_12_upstream_exists_nonNullMeasurableSet_volume_Icc_real with
    ⟨E, _hE_subset_Icc, hE_not_nullMeasurable⟩
  exact
    helperForProposition_7_12_exists_nonCaratheodorySet_of_exists_nonNullMeasurableSet
      ⟨E, hE_not_nullMeasurable⟩

/-- Helper for Proposition 7.12: upstream bounded non-null-measurable witness inside
`Set.Icc (0 : ℝ) 1` for Lebesgue measure. -/
theorem prereqForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_upstream :
    ∃ A : Set ℝ,
      A ⊆ Set.Icc (0 : ℝ) 1 ∧
        ¬ MeasureTheory.NullMeasurableSet A (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
by
  exact
    (helperForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_iff_exists_nonCaratheodorySet
      ).2 prereqForProposition_7_12_exists_nonCaratheodorySet_for_volumeOuterMeasure_upstream

/-- Helper for Proposition 7.12: upstream global non-null-measurable witness for Lebesgue
measure on `ℝ`, obtained from the bounded upstream witness inside `Set.Icc (0 : ℝ) 1`. -/
theorem prereqForProposition_7_12_exists_nonNullMeasurableSet_for_volume_upstream :
    ∃ E : Set ℝ,
      ¬ MeasureTheory.NullMeasurableSet E (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  exact
    helperForProposition_7_12_exists_nonNullMeasurableSet_for_volume_of_exists_nonNullMeasurableSet_volume_Icc
      prereqForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_upstream

/-- Helper for Proposition 7.12: any non-Carathéodory witness for Lebesgue outer measure yields a
bounded witness in `Set.Icc (0 : ℝ) 1` with full interval outer measure and positive complement
outer measure. -/
lemma helperForProposition_7_12_exists_fullOuterMeasure_IccSubset_with_positiveComplement_of_exists_nonCaratheodorySet
    (hExists :
      ∃ E : Set ℝ,
        ¬ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E) :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) E =
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) ∧
        0 <
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
            ((Set.Icc (0 : ℝ) 1) \ E) := by
  have hExistsNonNullIcc :
      ∃ A : Set ℝ,
        A ⊆ Set.Icc (0 : ℝ) 1 ∧
          ¬ MeasureTheory.NullMeasurableSet A (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    (helperForProposition_7_12_exists_nonNullMeasurableSet_volume_Icc_iff_exists_nonCaratheodorySet
      ).2 hExists
  exact
    helperForProposition_7_12_exists_fullOuterMeasure_IccSubset_with_positiveComplement_of_exists_nonNullMeasurableSet_volume_Icc
      hExistsNonNullIcc

theorem prereqForProposition_7_12_exists_fullOuterMeasure_IccSubset_with_positiveComplement :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) E =
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) ∧
        0 <
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
            ((Set.Icc (0 : ℝ) 1) \ E) := by
  exact
    helperForProposition_7_12_exists_fullOuterMeasure_IccSubset_with_positiveComplement_of_exists_nonCaratheodorySet
      prereqForProposition_7_12_exists_nonCaratheodorySet_for_volumeOuterMeasure_upstream

/-- Helper for Proposition 7.12: any non-Carathéodory witness for Lebesgue outer measure yields a
fixed-interval strict-split witness on `Set.Icc (0 : ℝ) 1`. -/
lemma helperForProposition_7_12_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure_of_exists_nonCaratheodorySet
    (hExists :
      ∃ E : Set ℝ,
        ¬ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure).IsCaratheodory E) :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) <
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
              ((Set.Icc (0 : ℝ) 1) ∩ E) +
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
            ((Set.Icc (0 : ℝ) 1) \ E) := by
  rcases
      helperForProposition_7_12_exists_fullOuterMeasure_IccSubset_with_positiveComplement_of_exists_nonCaratheodorySet
        hExists with
    ⟨E, hE_subset, hE_full, hComp_pos⟩
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

/-- Helper for Proposition 7.12: upstream fixed-interval strict-split witness prerequisite for
Lebesgue outer measure on `Set.Icc (0 : ℝ) 1`. -/
theorem prereqForProposition_7_12_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure :
    ∃ E : Set ℝ,
      E ⊆ Set.Icc (0 : ℝ) 1 ∧
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) <
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
              ((Set.Icc (0 : ℝ) 1) ∩ E) +
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
            ((Set.Icc (0 : ℝ) 1) \ E) := by
  exact
    helperForProposition_7_12_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure_of_exists_nonCaratheodorySet
      prereqForProposition_7_12_exists_nonCaratheodorySet_for_volumeOuterMeasure_upstream

/-- Helper for Proposition 7.12: any strict split at `T = Set.Icc (0 : ℝ) 1` forces the
interval complement term to have positive outer measure. -/
lemma helperForProposition_7_12_positiveComplement_of_fixedIcc_strictSplitWitness_for_volumeOuterMeasure
    {E : Set ℝ}
    (hStrict :
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure) (Set.Icc (0 : ℝ) 1) <
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
            ((Set.Icc (0 : ℝ) 1) ∩ E) +
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
            ((Set.Icc (0 : ℝ) 1) \ E)) :
    0 <
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
        ((Set.Icc (0 : ℝ) 1) \ E) := by
  by_contra hComp_nonpos
  have hComp_zero :
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
          ((Set.Icc (0 : ℝ) 1) \ E) = 0 := by
    exact le_antisymm (le_of_not_gt hComp_nonpos) zero_le
  have hInter_le :
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
          ((Set.Icc (0 : ℝ) 1) ∩ E) ≤
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
          (Set.Icc (0 : ℝ) 1) := by
    exact
      MeasureTheory.measure_mono
        (Set.inter_subset_left : (Set.Icc (0 : ℝ) 1) ∩ E ⊆ Set.Icc (0 : ℝ) 1)
  have hRhs_le :
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
          ((Set.Icc (0 : ℝ) 1) ∩ E) +
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
          ((Set.Icc (0 : ℝ) 1) \ E) ≤
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
        (Set.Icc (0 : ℝ) 1) := by
    calc
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
          ((Set.Icc (0 : ℝ) 1) ∩ E) +
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
          ((Set.Icc (0 : ℝ) 1) \ E)
          =
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
              ((Set.Icc (0 : ℝ) 1) ∩ E) + 0 := by
            simp [hComp_zero]
      _ ≤ ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
            (Set.Icc (0 : ℝ) 1) + 0 := by
            gcongr
      _ = ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
            (Set.Icc (0 : ℝ) 1) := by
            simp
  exact (not_lt_of_ge hRhs_le) hStrict

/-- Helper for Proposition 7.12: any fixed-interval strict-split witness yields a bounded witness
with positive outer-measure complement inside `Set.Icc (0 : ℝ) 1`. -/
lemma helperForProposition_7_12_exists_positiveComplement_of_exists_fixedIcc_strictSplitWitness_for_volumeOuterMeasure
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
        0 <
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ).toOuterMeasure)
            ((Set.Icc (0 : ℝ) 1) \ E) := by
  rcases hExists with ⟨E, hE_subset, hStrict⟩
  refine ⟨E, hE_subset, ?_⟩
  exact
    helperForProposition_7_12_positiveComplement_of_fixedIcc_strictSplitWitness_for_volumeOuterMeasure
      (E := E) hStrict


end Section03
end Chap07
