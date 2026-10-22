/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped MeasureTheory
open MeasureTheory

/- Lemma 9.18 (1): Part (i), the pointwise maximum of two stopping times is again a stopping
time. -/
recall MeasureTheory.IsStoppingTime.max

/- Lemma 9.18 (2): Part (i), the pointwise minimum of two stopping times is again a stopping
time. -/
recall MeasureTheory.IsStoppingTime.min

/- Lemma 9.18 (1): Part (ii), the sum of two nonnegative stopping times is again a stopping
time. -/
recall MeasureTheory.IsStoppingTime.add

/- Lemma 9.18 (2): Part (iii), delaying a stopping time by a deterministic nonnegative time
produces another stopping time. -/
recall MeasureTheory.IsStoppingTime.add_const'

/-- Lemma 9.18 (3): Part (iii), a deterministic backward shift of a stopping time need not be a
stopping time in general. -/
-- Proof sketch: Exhibit a filtered probability space and a stopping time `τ` for which the event
-- `{τ - s ≤ t}` depends on strictly more information than is available in the time-`t`
-- σ-algebra.
theorem exists_stoppingTime_sub_const_not_stoppingTime :
    ∃ (Ω : Type u) (m : MeasurableSpace Ω) (ℱ : Filtration NNReal m)
      (τ : Ω → WithTop NNReal), IsStoppingTime ℱ τ ∧
        ∃ s : NNReal, ¬ IsStoppingTime ℱ (fun ω ↦ τ ω - (s : WithTop NNReal)) := by
  -- Use a two-point space with a filtration that jumps from `⊥` to `⊤` at time `1`.
  let seq : NNReal → MeasurableSpace (ULift.{u} Bool) := fun t ↦ if t < 1 then ⊥ else ⊤
  have hmono : Monotone seq := by
    intro s t hst
    by_cases ht : t < 1
    · have hs : s < 1 := lt_of_le_of_lt hst ht
      simp [seq, hs, ht]
    · by_cases hs : s < 1
      · simp [seq, hs, ht]
      · simp [seq, hs, ht]
  have hle : ∀ t : NNReal, seq t ≤ (⊤ : MeasurableSpace (ULift.{u} Bool)) := by
    intro t
    by_cases ht : t < 1 <;> simp [seq, ht]
  let ℱ : Filtration NNReal (⊤ : MeasurableSpace (ULift.{u} Bool)) :=
    { seq := seq, mono' := hmono, le' := hle }
  let τ : ULift.{u} Bool → WithTop NNReal :=
    fun ω ↦ if ω.down then (1 : WithTop NNReal) else (2 : WithTop NNReal)
  -- Before time `1`, neither value of `τ` has occurred yet, so the stopping event is empty.
  have h_event_lt_one : ∀ ⦃t : NNReal⦄, t < 1 → {ω : ULift.{u} Bool | τ ω ≤ t} = ∅ := by
    intro t ht
    have ht_two : t < 2 := by
      have h_one_lt_two : (1 : NNReal) < 2 := by norm_num
      exact lt_trans ht h_one_lt_two
    have h_one_top : (t : WithTop NNReal) < ((1 : NNReal) : WithTop NNReal) := by
      exact_mod_cast ht
    have h_two_top : (t : WithTop NNReal) < ((2 : NNReal) : WithTop NNReal) := by
      exact_mod_cast ht_two
    ext ω
    cases' ω with b
    cases b
    · simp [τ]
      exact h_two_top
    · simp [τ]
      exact h_one_top
  -- After time `1`, the filtration is already `⊤`, so every event is measurable.
  have hτ : IsStoppingTime ℱ τ := by
    intro t
    by_cases ht : t < 1
    · have hFt : ℱ t = (⊥ : MeasurableSpace (ULift.{u} Bool)) := by
        simp [ℱ, seq, ht]
      rw [hFt, h_event_lt_one ht]
      simp
    · have hFt : ℱ t = (⊤ : MeasurableSpace (ULift.{u} Bool)) := by
        simp [ℱ, seq, ht]
      rw [hFt]
      simp
  -- At time `0`, the shifted stopping event becomes `{true}`, which is invisible in `⊥`.
  have h_shift_zero :
      {ω : ULift.{u} Bool | τ ω - (1 : WithTop NNReal) ≤ (0 : NNReal)} =
        ({ULift.up true} : Set _) := by
    have h_two_sub_nn : (2 : NNReal) - 1 = 1 := by
      rw [tsub_eq_iff_eq_add_of_le]
      · norm_num
      · norm_num
    have h_two_sub :
        ((2 : WithTop NNReal) - (1 : WithTop NNReal)) = ((1 : NNReal) : WithTop NNReal) := by
      simpa [WithTop.coe_sub] using congrArg (fun x : NNReal => (x : WithTop NNReal)) h_two_sub_nn
    ext ω
    cases' ω with b
    cases b
    · simp [τ]
      intro h
      have h_one_eq_zero : ((1 : NNReal) : WithTop NNReal) = 0 := by
        exact h_two_sub.symm.trans h
      norm_num at h_one_eq_zero
    · simp [τ]
  have h_singleton :
      ¬ MeasurableSet[(⊥ : MeasurableSpace (ULift.{u} Bool))] ({ULift.up true} : Set _) := by
    intro hmeas
    rw [MeasurableSpace.measurableSet_bot_iff] at hmeas
    rcases hmeas with h_empty | h_univ
    · have hmem : ULift.up true ∈ ({ULift.up true} : Set (ULift.{u} Bool)) := by simp
      simpa [h_empty] using hmem
    · have hmem : ULift.up false ∈ (Set.univ : Set (ULift.{u} Bool)) := by simp
      have : ULift.up false ∈ ({ULift.up true} : Set (ULift.{u} Bool)) := by
        simpa [h_univ] using hmem
      simp at this
  refine ⟨ULift.{u} Bool, ⊤, ℱ, τ, hτ, 1, ?_⟩
  intro h_shift
  -- Rewriting the time-`0` stopping event yields the forbidden singleton measurable set.
  have hmeas :
      MeasurableSet[(⊥ : MeasurableSpace (ULift.{u} Bool))] ({ULift.up true} : Set _) := by
    have hmeas0 :
        MeasurableSet[ℱ 0] {ω : ULift.{u} Bool | τ ω - (1 : WithTop NNReal) ≤ (0 : NNReal)} :=
      h_shift 0
    have hF0 : ℱ 0 = (⊥ : MeasurableSpace (ULift.{u} Bool)) := by
      simp [ℱ, seq]
    rw [hF0, h_shift_zero] at hmeas0
    exact hmeas0
  exact h_singleton hmeas
