/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {E : Type v} [mE : MeasurableSpace E]

/-- Definition 8.24: for an integrable random variable `Y`, a measurable function `φ : E → ℝ` is a
conditional expectation of `Y` given `X = x` if `X` is measurable and `φ` is the factor from
Equation (8.9) for the conditional expectation of `Y` with respect to `σ(X) = mE.comap X`, i.e. if
`P[Y | mE.comap X] = φ ∘ X`. -/
def is_conditional_expectation_given_value
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (X : Ω → E) (φ : E → ℝ) : Prop :=
  Integrable Y P ∧ Measurable X ∧ Measurable φ ∧ P[Y | mE.comap X] = φ ∘ X

/-- For a measurable random variable `X`, Definition 8.24 is realized by a measurable factor of
the canonical conditional expectation `P[Y | σ(X)]`. -/
theorem exists_conditional_expectation_given_value
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (X : Ω → E)
    (hY : Integrable Y P) (hX : Measurable X) :
    ∃ φ : E → ℝ, is_conditional_expectation_given_value P Y X φ := by
  have h_condExp : Measurable[mE.comap X] (P[Y | mE.comap X]) :=
    stronglyMeasurable_condExp.measurable
  obtain ⟨φ, hφ_meas, hφ⟩ := h_condExp.exists_eq_measurable_comp
  exact ⟨φ, hY, hX, hφ_meas, hφ⟩

/-- Applying Definition 8.24 to the indicator `1_A` factors the canonical conditional-probability
expression `P⟦A | σ(X)⟧` through `X`. When `A` is measurable, this is the conditional probability
of the event `A` given `X = x`. -/
theorem exists_conditional_probability_given_value
    (P : Measure Ω) [IsProbabilityMeasure P] {A : Set Ω} (X : Ω → E)
    (hA : MeasurableSet A) (hX : Measurable X) :
    ∃ p : E → ℝ,
      is_conditional_expectation_given_value P (A.indicator fun _ ↦ (1 : ℝ)) X p := by
  exact exists_conditional_expectation_given_value P (A.indicator fun _ ↦ (1 : ℝ)) X
    ((integrable_const (1 : ℝ)).indicator hA) hX
