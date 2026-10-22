/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/- Example 7.12: for a real random variable on a probability space, the canonical variance theorem
`ProbabilityTheory.variance_nonneg` gives `Var[X; μ] ≥ 0`; combined with
`ProbabilityTheory.variance_eq_sub`, this is the textbook inequality
`Var[X; μ] = μ[X ^ 2] - μ[X] ^ 2 ≥ 0` for square-integrable `X`. -/
recall variance_nonneg

/- On a probability space and for square-integrable real random variables, the variance is the
textbook difference between the second moment and the square of the expectation. -/
recall variance_eq_sub

/- The same owner abstraction also provides the companion estimate `Var[X; μ] ≤ μ[X ^ 2]`. -/
recall variance_le_expectation_sq

-- Proof sketch: rewrite `Var[X; μ]` as `μ[X ^ 2] - μ[X] ^ 2` using `variance_eq_sub hX`, then
-- rearrange the canonical inequality `variance_nonneg X μ`.
/-- The second moment of a square-integrable real random variable dominates the square of its
expectation. -/
theorem expectation_sq_le_second_moment_of_memLp {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    μ[X] ^ 2 ≤ μ[X ^ 2] := by
  simpa [variance_eq_sub hX, sub_nonneg] using variance_nonneg X μ
