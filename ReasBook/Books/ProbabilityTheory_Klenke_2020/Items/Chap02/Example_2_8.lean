/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory

open scoped ENNReal

noncomputable section

/-- The one-step law of a fair die, modeled as the uniform probability measure on `Fin 6`. -/
abbrev fair_die_measure : Measure (Fin 6) :=
  (PMF.uniformOfFintype (Fin 6)).toMeasure

/-- The distinguished face encoding the textbook outcome `6` inside `Fin 6`. -/
def six_face : Fin 6 := 5

/-- The event that the `n`th die roll is a six. -/
def six_event (n : ℕ) : Set (ℕ → Fin 6) :=
  Function.eval n ⁻¹' {six_face}

/-- The product measure describing an infinite sequence of independent fair die rolls. -/
abbrev fair_die_process_measure : Measure (ℕ → Fin 6) :=
  Measure.infinitePi (fun _ : ℕ ↦ fair_die_measure)

/-- The fair die assigns probability `1 / 6` to the face corresponding to a six. -/
theorem fair_die_measure_singleton_six_face :
    fair_die_measure {six_face} = (6 : ℝ≥0∞)⁻¹ := by
  simp [fair_die_measure, six_face]

/-- Each coordinate-six event is measurable in the product `σ`-algebra on infinite die-roll
sequences. -/
theorem measurableSet_six_event (n : ℕ) :
    MeasurableSet (six_event n) := by
  simpa [six_event] using measurable_pi_apply n (measurableSet_singleton six_face)

/-- The events that the `n`th roll is a six form an independent family under the fair-die product
measure. -/
theorem iIndepSet_six_event :
    iIndepSet six_event fair_die_process_measure := by
  rw [iIndepSet_iff_meas_biInter measurableSet_six_event]
  intro s
  have hfun : iIndepFun (fun n ω ↦ ω n) fair_die_process_measure := by
    simpa [fair_die_process_measure] using ProbabilityTheory.iIndepFun_infinitePi
      (fun _ ↦ measurable_id)
  simpa [six_event] using
    hfun.measure_inter_preimage_eq_mul s (fun i _ ↦ measurableSet_singleton six_face)

/-- The sum of the probabilities of the coordinate-six events diverges. -/
theorem tsum_measure_six_event_eq_top :
    (∑' n : ℕ, fair_die_process_measure (six_event n)) = ∞ := by
  have hconst : ∀ n : ℕ, fair_die_process_measure (six_event n) = (6 : ℝ≥0∞)⁻¹ := by
    intro n
    have h : MeasurePreserving (Function.eval n) fair_die_process_measure fair_die_measure := by
      simpa [fair_die_process_measure] using
        measurePreserving_eval_infinitePi (fun _ : ℕ ↦ fair_die_measure) n
    calc
      fair_die_process_measure (six_event n) = fair_die_measure {six_face} := by
        rw [six_event]
        rw [← h.map_eq]
        symm
        exact Measure.map_apply h.measurable (measurableSet_singleton six_face)
      _ = (6 : ℝ≥0∞)⁻¹ := fair_die_measure_singleton_six_face
  have htop : (∑' _ : ℕ, (6 : ℝ≥0∞)⁻¹) = ∞ :=
    ENNReal.tsum_const_eq_top_of_ne_zero <| by norm_num
  have hs : (fun n : ℕ ↦ fair_die_process_measure (six_event n)) = fun _ : ℕ ↦ (6 : ℝ≥0∞)⁻¹ := by
    funext n
    exact hconst n
  rw [hs]
  exact htop

/-- Example 2.8: For an infinite sequence of independent fair die rolls, the event that a six
occurs infinitely often has probability one. -/
theorem fair_die_rolls_measure_limsup_six_event_eq_one :
    fair_die_process_measure (limsup six_event atTop) = 1 := by
  simpa using ProbabilityTheory.measure_limsup_eq_one measurableSet_six_event
    iIndepSet_six_event tsum_measure_six_event_eq_top

end
