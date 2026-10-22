/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open scoped MeasureTheory
open MeasureTheory

universe u

variable {Ω : Type u}

section MeasurableSpace

variable [MeasurableSpace Ω]

/-- Definition 20.5 (1): an event is invariant if it is measurable and its preimage under `τ`
is itself. -/
def is_invariant_event (τ : Ω → Ω) (A : Set Ω) : Prop :=
  MeasurableSet A ∧ τ ⁻¹' A = A

/-- This unfolds the definition of an invariant event. -/
@[simp] theorem is_invariant_event_iff (τ : Ω → Ω) (A : Set Ω) :
    is_invariant_event τ A ↔ MeasurableSet A ∧ τ ⁻¹' A = A :=
  Iff.rfl

/-- Definition 20.5 (2): an event is quasiinvariant if it agrees almost everywhere with its
preimage under `τ`. -/
def is_quasiinvariant_event (P : Measure Ω) (τ : Ω → Ω) (A : Set Ω) : Prop :=
  MeasurableSet A ∧ τ ⁻¹' A =ᵐ[P] A

/-- This unfolds the definition of a quasiinvariant event. -/
@[simp] theorem is_quasiinvariant_event_iff (P : Measure Ω) (τ : Ω → Ω) (A : Set Ω) :
    is_quasiinvariant_event P τ A ↔ MeasurableSet A ∧ τ ⁻¹' A =ᵐ[P] A :=
  Iff.rfl

/-- This rewrites quasiinvariance in the indicator-function form used in the text. -/
-- Proof sketch: use `indicator_ae_eq_of_ae_eq_set` for the forward implication and recover the
-- set equality almost everywhere by evaluating the indicator functions.
theorem is_quasiinvariant_event_iff_indicator_ae_eq (P : Measure Ω) (τ : Ω → Ω) (A : Set Ω) :
    is_quasiinvariant_event P τ A ↔
      MeasurableSet A ∧
        (τ ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) =ᵐ[P] A.indicator (fun _ ↦ (1 : ℝ)) := by
  rw [is_quasiinvariant_event]
  constructor
  · rintro ⟨hA, hAeq⟩
    exact ⟨hA, indicator_ae_eq_of_ae_eq_set hAeq⟩
  · rintro ⟨hA, hIndicator⟩
    refine ⟨hA, hIndicator.mono ?_⟩
    intro x hx
    by_cases hxA : x ∈ A
    · by_cases hτxA : τ x ∈ A
      · apply propext
        constructor <;> intro _ <;> assumption
      · have : False := by
          simp [hxA, hτxA] at hx
        exact False.elim this
    · by_cases hτxA : τ x ∈ A
      · have : False := by
          simp [hxA, hτxA] at hx
        exact False.elim this
      · apply propext
        constructor <;> intro h
        · exact False.elim <| hτxA h
        · exact False.elim <| hxA h

/- Definition 20.5 (3): the invariant `σ`-algebra is the canonical measurable-space owner
`MeasurableSpace.invariants τ`. -/
recall MeasurableSpace.invariants

/-- This characterizes the measurable sets of the invariant `σ`-algebra in the source-facing
language of invariant events. -/
theorem measurableSet_invariants_iff_is_invariant_event (τ : Ω → Ω) {A : Set Ω} :
    MeasurableSet[MeasurableSpace.invariants τ] A ↔ is_invariant_event τ A := by
  rw [MeasurableSpace.measurableSet_invariants, is_invariant_event]

/-- Definition 20.5 (4): a `σ`-algebra is `P`-trivial if every one of its events has probability
`0` or `1`. -/
def is_p_trivial (P : Measure Ω) [IsProbabilityMeasure P] (I : MeasurableSpace Ω) : Prop :=
  let _ : MeasurableSpace Ω := I
  ∀ A : Set Ω, MeasurableSet A → P A = 0 ∨ P A = 1

end MeasurableSpace
