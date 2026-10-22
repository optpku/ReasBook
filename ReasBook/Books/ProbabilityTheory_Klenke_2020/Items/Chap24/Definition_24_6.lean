/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

universe u v

/-- A nonnegative measurable test function on `E`, corresponding to the textbook space `B⁺(E)`. -/
structure NonnegativeMeasurableFunction (E : Type v) [MeasurableSpace E] where
  /-- The underlying nonnegative measurable function. -/
  toFun : E → ℝ≥0∞
  /-- The underlying function is measurable. -/
  measurable_toFun : Measurable toFun

instance {E : Type v} [MeasurableSpace E] :
    CoeFun (NonnegativeMeasurableFunction E) (fun _ ↦ E → ℝ≥0∞) where
  coe f := f.toFun

/-- A bounded measurable real-valued test function on `E`, corresponding to the textbook space
`B_b^ℝ(E)`. -/
structure RealValuedBoundedMeasurableFunction (E : Type v) [MeasurableSpace E] where
  /-- The underlying bounded measurable real-valued function. -/
  toFun : E → ℝ
  /-- The underlying function is measurable. -/
  measurable_toFun : Measurable toFun
  /-- The underlying function has bounded range. -/
  bound' : ∃ C : ℝ, ∀ x, |toFun x| ≤ C

instance {E : Type v} [MeasurableSpace E] :
    CoeFun (RealValuedBoundedMeasurableFunction E) (fun _ ↦ E → ℝ) where
  coe f := f.toFun

namespace RandomMeasure

variable {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]

/-- Definition 24.6: the Laplace transform of a random measure is the expectation of
`exp (-∫ f dX)` for a nonnegative measurable test function `f`; the companion definition
`RandomMeasure.characteristicFunction` records the characteristic function on bounded measurable
real-valued test functions. -/
def laplaceTransform (X : Kernel Ω E) (P : ProbabilityMeasure Ω)
    (f : NonnegativeMeasurableFunction E) : ℝ :=
  ∫ ω, Real.exp (-((∫⁻ x, f x ∂ X ω).toReal)) ∂(P : Measure Ω)

-- Proof sketch: unfold `RandomMeasure.laplaceTransform`; the displayed integral is exactly the
-- defining expectation `E[exp (-∫ f dX)]` written with Lean's `lintegral` for the nonnegative
-- test function `f`.
/-- Unfolding `RandomMeasure.laplaceTransform` gives the textbook expectation formula
`E[exp (-∫ f dX)]`. -/
theorem laplaceTransform_def (X : Kernel Ω E) (P : ProbabilityMeasure Ω)
    (f : NonnegativeMeasurableFunction E) :
    laplaceTransform X P f =
      ∫ ω, Real.exp (-((∫⁻ x, f x ∂ X ω).toReal)) ∂(P : Measure Ω) := by
  -- The theorem statement is exactly the defining equation of `laplaceTransform`.
  rfl

/-- The characteristic function of a random measure is the expectation of `exp (i ∫ f dX)` for a
bounded measurable real-valued test function `f`. -/
def characteristicFunction (X : Kernel Ω E) (P : ProbabilityMeasure Ω)
    (f : RealValuedBoundedMeasurableFunction E) : ℂ :=
  ∫ ω, Complex.exp (((∫ x, f x ∂ X ω : ℝ) : ℂ) * Complex.I) ∂(P : Measure Ω)

-- Proof sketch: unfold `RandomMeasure.characteristicFunction`; the right-hand side is the defining
-- expectation `E[exp (i ∫ f dX)]` expressed as a complex-valued Bochner integral.
/-- Unfolding `RandomMeasure.characteristicFunction` gives the textbook expectation formula
`E[exp (i ∫ f dX)]`. -/
theorem characteristicFunction_def (X : Kernel Ω E) (P : ProbabilityMeasure Ω)
    (f : RealValuedBoundedMeasurableFunction E) :
    characteristicFunction X P f =
      ∫ ω, Complex.exp (((∫ x, f x ∂ X ω : ℝ) : ℂ) * Complex.I) ∂(P : Measure Ω) := by
  -- The theorem statement is exactly the defining equation of `characteristicFunction`.
  rfl

end RandomMeasure
