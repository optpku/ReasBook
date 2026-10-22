/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Equation (8.4) is `source-facing`: for `X ∈ L¹(P)` and an event `A ∈ 𝒜`, the truncated
expectation `𝔼[X; A] := 𝔼[1_A X]` is represented in Lean by the canonical expectation
`P[A.indicator X]`. Its `core/canonical` owner abstractions are `MeasureTheory.integral` and
`MeasureTheory.integral_indicator`; the set-integral identity is the `bridge/view` connecting the
textbook notation to that owner API. -/

/-- Equation (8.4): the truncated expectation `𝔼[X; A]` is the expectation of the indicator-truncated
random variable `1_A X`. -/
noncomputable def truncatedExpectation (P : Measure Ω) (A : Set Ω) (X : Ω → ℝ) : ℝ :=
  P[A.indicator X]

/-- For a measurable event `A`, Equation (8.4) identifies the truncated expectation with the set
integral of `X` over `A`. -/
theorem truncatedExpectation_eq_setIntegral (P : Measure Ω) {X : Ω → ℝ} {A : Set Ω}
    (hA : MeasurableSet A) :
    truncatedExpectation P A X = ∫ ω in A, X ω ∂P := by
  simpa [truncatedExpectation] using
    (integral_indicator hA : ∫ ω, A.indicator X ω ∂P = ∫ ω in A, X ω ∂P)
