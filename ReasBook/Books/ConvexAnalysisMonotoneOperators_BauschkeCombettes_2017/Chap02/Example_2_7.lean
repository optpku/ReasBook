/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.MeasureTheory.Function.L2Space

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MeasureTheory
open MeasureTheory.L2
open scoped MeasureTheory InnerProductSpace

variable {α : Type u} [MeasurableSpace α] {μ : Measure α}

/- The textbook real-valued `L^p(\Omega,\mathcal{F},\mu)` is the canonical mathlib space
`MeasureTheory.Lp ℝ p μ`. -/
#check MeasureTheory.Lp

-- Proof sketch: rewrite the canonical `L²` inner product using `MeasureTheory.L2.inner_def` and
-- simplify the real pointwise inner product `⟪f x, g x⟫_ℝ` to the product `f x * g x`.
/-- Example 2.7: for a real measure space, the canonical inner product on `L²` is the integral of
the pointwise product. -/
theorem real_l2_inner_eq_integral_mul (f g : α →₂[μ] ℝ) :
    ⟪f, g⟫_ℝ = ∫ x, f x * g x ∂μ := by
  rw [inner_def]
  refine integral_congr_ae ?_
  filter_upwards with x
  change g x * star (f x) = f x * g x
  simp [mul_comm]
