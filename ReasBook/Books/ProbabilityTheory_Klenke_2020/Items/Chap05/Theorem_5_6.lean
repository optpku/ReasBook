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
variable {X : Ω → ℝ}

noncomputable section

/- Theorem 5.6 (1): (i) The textbook identity
`Var[X; μ] = μ[fun ω ↦ (X ω - μ[X]) ^ 2]` is the canonical theorem
`variance_eq_integral`, which holds under the weaker assumption `AEMeasurable X μ`. -/
recall variance_eq_integral

/- Theorem 5.6 (2): (i) The variance is nonnegative; this is the canonical theorem
`variance_nonneg`, again with no square-integrability hypothesis needed. -/
recall variance_nonneg

-- Proof sketch: the forward implication is `ProbabilityTheory.ae_eq_integral_of_variance_eq_zero`;
-- the converse follows by substituting the almost-sure constancy into the variance integral.
/-- Theorem 5.6 (3): (ii) A square-integrable real random variable has variance zero exactly when it
is almost surely equal to its expectation. -/
theorem variance_eq_zero_iff_ae_eq_expectation (hX : MemLp X 2 μ) :
    Var[X; μ] = 0 ↔ X =ᵐ[μ] fun _ ↦ μ[X] := by
  constructor
  · exact ae_eq_integral_of_variance_eq_zero hX
  · intro hX_const
    rw [variance_congr hX_const, variance_eq_integral measurable_const.aemeasurable]
    simp

-- Proof sketch: apply the canonical inequality
-- `ProbabilityTheory.variance_le_expectation_sq` to the shifted variable `ω ↦ X ω - x`, then
-- rewrite its variance back to `Var[X; μ]` via `ProbabilityTheory.variance_sub_const`.
/-- Theorem 5.6 (4): (iii) Among all constants `x : ℝ`, the expected squared distance from `X` to
`x` is minimized at the expectation `μ[X]`; together with Theorem 5.6 (1), this gives the minimum
value `Var[X; μ]`. -/
theorem variance_le_expectation_squared_distance (hX : MemLp X 2 μ) (x : ℝ) :
    Var[X; μ] ≤ μ[fun ω ↦ (X ω - x) ^ 2] := by
  let Y : Ω → ℝ := fun ω ↦ X ω - x
  have hY : MemLp Y 2 μ := hX.sub (memLp_const x)
  simpa [Y, variance_sub_const hX.aestronglyMeasurable x] using
    variance_le_expectation_sq hY.aestronglyMeasurable
