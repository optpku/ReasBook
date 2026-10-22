/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Dirac

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Example 1.72: if `{ω}` is measurable, then the Dirac measure at `ω` evaluates any
set `s` by the indicator of the membership test `ω ∈ s`. -/
lemma diracApplyAllSets (ω : Ω) (hω : MeasurableSet ({ω} : Set Ω)) (s : Set Ω) :
    Measure.dirac ω s = s.indicator 1 ω := by
  by_cases h : ω ∈ s
  · -- When `ω ∈ s`, the whole Dirac mass is already captured by `s`.
    simp [h, Measure.dirac_apply_of_mem (s := s) h]
  · -- When `ω ∉ s`, the set sits inside the measurable complement of `{ω}`.
    suffices hzero : Measure.dirac ω s = 0 by
      simp [h, hzero]
    apply le_antisymm
    · calc
        Measure.dirac ω s ≤ Measure.dirac ω ({ω}ᶜ : Set Ω) := by
          exact measure_mono (subset_compl_comm.1 <| singleton_subset_iff.2 h)
        _ = 0 := by
          simp [Measure.dirac_apply' _ hω.compl]
    · exact bot_le

/-- Helper for Example 1.72: on the trivial `σ`-algebra, a set has `δ_ω`-measure zero exactly when
it is empty. -/
theorem dirac_null_iff_empty_of_bot_allSets (ω : Ω)
    (hΩ : ‹MeasurableSpace Ω› = ⊥) {s : Set Ω} :
    Measure.dirac ω s = 0 ↔ s = ∅ := by
  rw [hΩ]
  letI : MeasurableSpace Ω := ⊥
  constructor
  · intro hs
    by_contra hsne
    have hsne' : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hsne
    have htm : MeasurableSet (toMeasurable (Measure.dirac ω) s) := measurableSet_toMeasurable _ _
    have htoMeas :
        toMeasurable (Measure.dirac ω) s = (Set.univ : Set Ω) := by
      rcases MeasurableSpace.measurableSet_bot_iff.mp htm with hempty | huniv
      · exfalso
        exact hsne'.ne_empty <|
          subset_empty_iff.mp <| hempty ▸ subset_toMeasurable (Measure.dirac ω) s
      · exact huniv
    have hfull : Measure.dirac ω s = 1 := by
      rw [← measure_toMeasurable (μ := Measure.dirac ω) s, htoMeas]
      exact Measure.dirac_apply_of_mem (s := (Set.univ : Set Ω)) (by simp)
    exact zero_ne_one (hs.symm.trans hfull)
  · intro hs
    simp [hs]

-- Proof sketch: if `{ω}` is measurable, then every set is measurable in the completion by
-- `nullMeasurableSet_dirac_of_singleton`; compare both measures on an arbitrary set `s`, where
-- both sides evaluate as the Dirac mass at `ω`.
/-- Example 1.72 (measurable-singleton branch): if `{ω}` is measurable, then the completion of the
Dirac measure at `ω` is again the Dirac measure at `ω`, now viewed on the completed measurable
space `NullMeasurableSpace Ω (Measure.dirac ω)`. The trivial-`σ`-algebra branch of Example 1.72 is
recorded below by `nullMeasurableSet_dirac_iff_measurableSet_of_bot` and
`dirac_completion_eq_dirac_of_bot`. -/
theorem dirac_completion_eq_dirac (ω : Ω)
    (hω : MeasurableSet ({ω} : Set Ω)) :
    Measure.completion (Measure.dirac ω) =
      (Measure.dirac ω : Measure (NullMeasurableSpace Ω (Measure.dirac ω))) := by
  -- Route correction: the completion is handled directly by comparing both measures on
  -- completion-measurable sets, so the singleton measurability hypothesis is stronger than needed.
  ext s hs
  -- The completion preserves the original set function, while Dirac on the completed space uses
  -- the same indicator formula on measurable sets.
  have hright :
      (Measure.dirac ω : Measure (NullMeasurableSpace Ω (Measure.dirac ω))) s =
        s.indicator 1 ω := by
    exact
      @Measure.dirac_apply' (NullMeasurableSpace Ω (Measure.dirac ω)) inferInstance s ω hs
  rw [Measure.completion_apply, diracApplyAllSets (ω := ω) (hω := hω) (s := (s : Set Ω)), hright]
  rfl

-- Proof sketch: if `ω ∉ s`, then `s` is `δ_ω`-null, hence completion-measurable; if `ω ∈ s`,
-- then `s \ {ω}` is `δ_ω`-null and `s = {ω} ∪ (s \ {ω})`, so the measurability of `{ω}` makes `s`
-- completion-measurable as well.
/-- If `{ω}` is measurable, then every set is `δ_ω`-null-measurable; equivalently, every subset is
measurable in the completion of `Measure.dirac ω`. -/
theorem nullMeasurableSet_dirac_of_singleton (ω : Ω)
    (hω : MeasurableSet ({ω} : Set Ω)) (s : Set Ω) :
    NullMeasurableSet s (Measure.dirac ω) := by
  by_cases h : ω ∈ s
  · -- If `ω ∈ s`, then `sᶜ` misses the Dirac point and hence has zero measure.
    have hcompl : ω ∉ sᶜ := by simpa using h
    apply NullMeasurableSet.of_compl
    apply NullMeasurableSet.of_null
    rw [diracApplyAllSets (ω := ω) (hω := hω) (s := sᶜ)]
    simp [hcompl]
  · -- If `ω ∉ s`, then `s` itself is a Dirac-null set.
    apply NullMeasurableSet.of_null
    rw [diracApplyAllSets (ω := ω) (hω := hω) (s := s)]
    simp [h]

-- Proof sketch: under `hΩ`, the only measurable sets are `∅` and `univ`; since
-- `Measure.dirac ω univ = 1`, among measurable sets the only `δ_ω`-null set is `∅`.
/-- On the trivial `σ`-algebra, the empty set is the only measurable `δ_ω`-null set. -/
theorem dirac_null_iff_empty_of_bot (ω : Ω)
    (hΩ : ‹MeasurableSpace Ω› = ⊥) {s : Set Ω} (hs : MeasurableSet s) :
    Measure.dirac ω s = 0 ↔ s = ∅ := by
  -- The all-sets characterization specializes immediately to measurable sets.
  let _ := hs
  simpa using dirac_null_iff_empty_of_bot_allSets (ω := ω) hΩ (s := s)

-- Proof sketch: by the previous theorem, any null-measurable set agrees a.e. with a measurable
-- set, but a `δ_ω`-null symmetric difference must be empty in the trivial `σ`-algebra.
/-- On the trivial `σ`-algebra, `δ_ω`-null-measurable sets are exactly the measurable sets, so the
completion measurable space is still trivial. -/
theorem nullMeasurableSet_dirac_iff_measurableSet_of_bot (ω : Ω)
    (hΩ : ‹MeasurableSpace Ω› = ⊥) (s : Set Ω) :
    NullMeasurableSet s (Measure.dirac ω) ↔ MeasurableSet s := by
  rw [hΩ]
  letI : MeasurableSpace Ω := ⊥
  constructor
  · intro hs
    -- The measurable hull differs from `s` by a Dirac-null set, hence by the all-sets lemma it
    -- differs from `s` by the empty set.
    have hdiff : Measure.dirac ω (toMeasurable (Measure.dirac ω) s \ s) = 0 := by
      exact ae_le_set.1 <| Filter.EventuallyEq.le hs.toMeasurable_ae_eq
    have hdiff_empty :
        toMeasurable (Measure.dirac ω) s \ s = ∅ :=
      (dirac_null_iff_empty_of_bot_allSets (ω := ω) (hΩ := rfl)).mp hdiff
    have hsubset : toMeasurable (Measure.dirac ω) s ⊆ s := by
      intro x hx
      by_contra hxs
      have : x ∈ toMeasurable (Measure.dirac ω) s \ s := ⟨hx, hxs⟩
      simp [hdiff_empty] at this
    have hs_eq : s = toMeasurable (Measure.dirac ω) s :=
      subset_antisymm (subset_toMeasurable (Measure.dirac ω) s) hsubset
    rw [hs_eq]
    exact measurableSet_toMeasurable (Measure.dirac ω) s
  · intro hs
    exact hs.nullMeasurableSet

-- Proof sketch: once the completion measurable space adds no new measurable sets, the completed
-- measure agrees with the original Dirac measure on every set.
/-- On the trivial `σ`-algebra, completing the Dirac measure still gives the same Dirac measure on
the completed space. -/
theorem dirac_completion_eq_dirac_of_bot (ω : Ω)
    (hΩ : ‹MeasurableSpace Ω› = ⊥) :
    Measure.completion (Measure.dirac ω) =
      (Measure.dirac ω : Measure (NullMeasurableSpace Ω (Measure.dirac ω))) := by
  rw [hΩ]
  letI : MeasurableSpace Ω := ⊥
  -- Route correction: first recover ordinary measurability of completion-measurable sets from the
  -- trivial-`σ`-algebra characterization, then compare both measures directly.
  ext s hs
  -- The completion keeps the original set function, and the right-hand Dirac measure is computed
  -- by the same indicator formula on completion-measurable sets.
  have hs' : @MeasurableSet Ω ⊥ (s : Set Ω) := by
    exact
      (nullMeasurableSet_dirac_iff_measurableSet_of_bot
        (ω := ω) (hΩ := rfl) (s := (s : Set Ω))).mp hs
  have hleft : (Measure.dirac ω : Measure Ω) (s : Set Ω) = (s : Set Ω).indicator 1 ω :=
    Measure.dirac_apply' ω hs'
  have hright :
      (Measure.dirac ω : Measure (NullMeasurableSpace Ω (Measure.dirac ω))) s =
        s.indicator 1 ω := by
    exact
      @Measure.dirac_apply' (NullMeasurableSpace Ω (Measure.dirac ω)) inferInstance s ω hs
  rw [Measure.completion_apply, hleft, hright]

-- Proof sketch: with the trivial `σ`-algebra, two Dirac measures agree on the only measurable
-- sets `∅` and `univ`, so they are equal.
/-- On the trivial `σ`-algebra, Dirac measures at different points cannot be distinguished. -/
theorem dirac_eq_dirac_of_bot (ω₁ ω₂ : Ω) (hΩ : ‹MeasurableSpace Ω› = ⊥) :
    (Measure.dirac ω₁ : Measure Ω) = Measure.dirac ω₂ := by
  rw [hΩ]
  letI : MeasurableSpace Ω := ⊥
  -- Equality of measures is checked on measurable sets, and the bottom `σ`-algebra has only
  -- `∅` and `univ`.
  apply Measure.ext
  intro s hs
  rcases MeasurableSpace.measurableSet_bot_iff.mp hs with rfl | rfl
  · simp
  · simp [Measure.dirac_apply_of_mem (s := (Set.univ : Set Ω)) (by simp)]
