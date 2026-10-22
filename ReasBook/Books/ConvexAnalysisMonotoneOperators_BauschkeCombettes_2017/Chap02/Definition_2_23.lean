/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

namespace LinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Definition 2.23 (1): a linear operator on a real Hilbert space is monotone when
`⟪T x, x⟫_ℝ` is nonnegative for every vector `x`. -/
def IsMonotone (T : H →ₗ[ℝ] H) : Prop :=
  ∀ x, 0 ≤ ⟪T x, x⟫_ℝ

/-- For real Hilbert spaces, positivity is exactly symmetry together with the monotonicity
inequality from Definition 2.23 (1). -/
theorem isPositive_iff_isSymmetric_and_isMonotone (T : H →ₗ[ℝ] H) :
    T.IsPositive ↔ T.IsSymmetric ∧ T.IsMonotone := by
  simpa [IsMonotone] using (LinearMap.isPositive_iff T)

/-- A positive linear operator is monotone after forgetting the symmetry part of positivity. -/
theorem IsPositive.isMonotone {T : H →ₗ[ℝ] H} (hT : T.IsPositive) :
    T.IsMonotone := by
  simpa [IsMonotone] using hT.inner_nonneg_left

/-- Definition 2.23 (2): a linear operator on a real Hilbert space is strictly monotone when
`⟪T x, x⟫_ℝ` is strictly positive for every nonzero vector `x`. -/
def IsStrictlyMonotone (T : H →ₗ[ℝ] H) : Prop :=
  ∀ x, x ≠ 0 → 0 < ⟪T x, x⟫_ℝ

/-- A strictly monotone linear operator is monotone. -/
theorem IsStrictlyMonotone.isMonotone {T : H →ₗ[ℝ] H} (hT : T.IsStrictlyMonotone) :
    T.IsMonotone := by
  change ∀ x, 0 ≤ ⟪T x, x⟫_ℝ
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  · exact le_of_lt (hT x hx)

/-- Definition 2.23 (3): for a positive real scalar `α`, a linear operator on a real Hilbert
space is `α`-strongly monotone when `⟪T x, x⟫_ℝ` dominates `α * ‖x‖ ^ 2` for every vector `x`. -/
def IsStronglyMonotone (T : H →ₗ[ℝ] H) (α : ℝ) : Prop :=
  0 < α ∧ ∀ x, α * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ

/-- The parameter of a strongly monotone operator is positive. -/
theorem IsStronglyMonotone.pos {T : H →ₗ[ℝ] H} {α : ℝ} (hT : T.IsStronglyMonotone α) :
    0 < α :=
  hT.1

/-- A strongly monotone operator satisfies the textbook lower bound at every vector. -/
theorem IsStronglyMonotone.ineq {T : H →ₗ[ℝ] H} {α : ℝ} (hT : T.IsStronglyMonotone α)
    (x : H) :
    α * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ :=
  hT.2 x

/-- An `α`-strongly monotone linear operator is strictly monotone. -/
theorem IsStronglyMonotone.isStrictlyMonotone {T : H →ₗ[ℝ] H} {α : ℝ}
    (hT : T.IsStronglyMonotone α) :
    T.IsStrictlyMonotone := by
  change ∀ x, x ≠ 0 → 0 < ⟪T x, x⟫_ℝ
  intro x hx
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsq : 0 < ‖x‖ ^ 2 := pow_pos hnorm 2
  have hlower : 0 < α * ‖x‖ ^ 2 := mul_pos hT.pos hsq
  exact lt_of_lt_of_le hlower (hT.ineq x)

/-- An `α`-strongly monotone linear operator is monotone. -/
theorem IsStronglyMonotone.isMonotone {T : H →ₗ[ℝ] H} {α : ℝ}
    (hT : T.IsStronglyMonotone α) :
    T.IsMonotone :=
  hT.isStrictlyMonotone.isMonotone

end LinearMap
