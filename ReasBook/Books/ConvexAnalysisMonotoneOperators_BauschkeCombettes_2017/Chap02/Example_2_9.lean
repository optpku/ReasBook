/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MeasureTheory
open MeasureTheory.L2
open scoped MeasureTheory InnerProductSpace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/- The textbook probability-space structure is the canonical mathlib class
`MeasureTheory.IsProbabilityMeasure P`, and the real `L²` space over `P` is
`MeasureTheory.Lp ℝ 2 P`. The ambient Hilbert-space structure is provided by
the standard `Lp` instances. -/
recall MeasureTheory.IsProbabilityMeasure
recall MeasureTheory.Lp

-- Proof sketch: rewrite the canonical `L²` inner product with `L2.inner_def`, expand the
-- expectation notation `P[·]`, and simplify the real pointwise inner product `⟪X ω, Y ω⟫_ℝ`
-- to the product `X ω * Y ω`.
/-- Example 2.9: on a probability space, the canonical inner product on real `L²(P)` is the
expected value of the pointwise product `XY`. -/
theorem real_probability_l2_inner_eq_expectation_mul [IsProbabilityMeasure P]
    (X Y : Ω →₂[P] ℝ) :
    ⟪X, Y⟫_ℝ = P[fun ω ↦ X ω * Y ω] := by
  rw [inner_def]
  change ∫ ω, ⟪X ω, Y ω⟫_ℝ ∂P = ∫ ω, X ω * Y ω ∂P
  refine integral_congr_ae ?_
  filter_upwards with ω
  change Y ω * star (X ω) = X ω * Y ω
  simp [mul_comm]
