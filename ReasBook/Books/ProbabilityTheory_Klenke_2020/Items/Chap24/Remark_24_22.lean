/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open MeasureTheory
open scoped CompactlySupported ENNReal NNReal

noncomputable section

universe u

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [Bornology E]

/-- The Laplace transform of a probability law on measures, evaluated at a nonnegative compactly
supported continuous test function. -/
def measureLawLaplaceTransform
    (P : ProbabilityMeasure (Measure E)) (f : C_c(E, ℝ≥0)) : ℝ :=
  ∫ χ, Real.exp (-(∫ x, (f x : ℝ) ∂χ)) ∂(P : Measure (Measure E))

/-- Remark 24.22: a probability law on measures has deterministic part `α` and canonical measure
`ν` when `ν` satisfies the bounded-set truncation condition on bounded measurable sets and the
Laplace transform of the law obeys the Lévy--Khinchin formula from the remark. -/
def HasMeasureLevyKhinchinRepresentation
    (P : ProbabilityMeasure (Measure E)) (α : Measure E) (ν : Measure (Measure E)) : Prop :=
  (∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
      (∫⁻ χ, min (χ A) (1 : ℝ≥0∞) ∂ν) < (⊤ : ℝ≥0∞)) ∧
    ∀ f : C_c(E, ℝ≥0),
      measureLawLaplaceTransform P f =
        Real.exp
          (-(∫ x, (f x : ℝ) ∂α) +
            ∫ χ : Measure E, (Real.exp (-(∫ x, (f x : ℝ) ∂χ)) - 1) ∂ν)

omit [OpensMeasurableSpace E] in
-- Proof sketch: unfold `HasMeasureLevyKhinchinRepresentation`; it is exactly the conjunction of
-- the bounded-set truncation condition on `ν` and the Lévy--Khinchin Laplace-transform identity.
/-- Unfolding `HasMeasureLevyKhinchinRepresentation P α ν` gives the bounded-set truncation
condition on `ν` together with the Lévy--Khinchin Laplace-transform formula. -/
theorem hasMeasureLevyKhinchinRepresentation_iff
    (P : ProbabilityMeasure (Measure E)) (α : Measure E) (ν : Measure (Measure E)) :
    HasMeasureLevyKhinchinRepresentation P α ν ↔
      (∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A →
          (∫⁻ χ, min (χ A) (1 : ℝ≥0∞) ∂ν) < (⊤ : ℝ≥0∞)) ∧
        ∀ f : C_c(E, ℝ≥0),
          measureLawLaplaceTransform P f =
            Real.exp
              (-(∫ x, (f x : ℝ) ∂α) +
                ∫ χ : Measure E, (Real.exp (-(∫ x, (f x : ℝ) ∂χ)) - 1) ∂ν) := sorry
