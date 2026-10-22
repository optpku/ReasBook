/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Example_2_8

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory

open scoped ENNReal

/-- The event family from Example 2.9: for every `n`, the event `A_n` is that the single die roll
shows six. On the canonical model `Fin 6`, this is the constant family with value `{six_face}`. -/
def single_roll_six_events : ℕ → Set (Fin 6) := fun _ ↦ {six_face}

/-- Each event in the family `single_roll_six_events` is the singleton event that the unique die
roll shows six. -/
@[simp]
theorem single_roll_six_events_apply (n : ℕ) :
    single_roll_six_events n = ({six_face} : Set (Fin 6)) := rfl

/-- The limsup of the constant event family from Example 2.9 is again the singleton event
`{six_face}`. -/
theorem limsup_single_roll_six_events :
    limsup single_roll_six_events atTop = ({six_face} : Set (Fin 6)) := by
  simpa [single_roll_six_events] using
    (Filter.limsup_const ({six_face} : Set (Fin 6)))

/-- The sum of the probabilities of the constant six-events from Example 2.9 diverges. -/
theorem tsum_measure_single_roll_six_events_eq_top :
    (∑' n : ℕ, fair_die_measure (single_roll_six_events n)) = ∞ := by
  simp_rw [single_roll_six_events_apply, fair_die_measure_singleton_six_face]
  exact ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)

/-- The limsup event in Example 2.9 still has probability `1 / 6`. -/
theorem fair_die_measure_limsup_single_roll_six_events :
    fair_die_measure (limsup single_roll_six_events atTop) = (6 : ℝ≥0∞)⁻¹ := by
  rw [limsup_single_roll_six_events]
  exact fair_die_measure_singleton_six_face

/-- Example 2.9: if one rolls a die only once and lets `A_n` be the event that this single roll
shows six for every `n`, then `∑ P[A_n] = ∞` while the limsup event still has probability
`1 / 6`. This is the standard counterexample showing that independence is necessary in the second
Borel-Cantelli lemma. -/
theorem single_roll_six_events_borelCantelli_counterexample :
    ((∑' n : ℕ, fair_die_measure (single_roll_six_events n)) = ∞) ∧
      fair_die_measure (limsup single_roll_six_events atTop) = (6 : ℝ≥0∞)⁻¹ := by
  exact ⟨tsum_measure_single_roll_six_events_eq_top,
    fair_die_measure_limsup_single_roll_six_events⟩
