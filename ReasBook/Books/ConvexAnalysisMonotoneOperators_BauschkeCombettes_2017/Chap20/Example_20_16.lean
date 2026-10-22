/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_23

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProduct InnerProductSpace

universe u

namespace ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable [CompleteSpace H]

-- Proof sketch: compare the quadratic forms of `A` and `A + A†`; in a real Hilbert space,
-- `⟪(A + A†) x, x⟫_ℝ = 2 * ⟪A x, x⟫_ℝ`, so the two monotonicity conditions are equivalent.
/-- Example 20.16 (1): clause (i). A bounded operator is monotone if and only if `A + A†` is
monotone. -/
theorem isMonotone_iff_add_adjoint_isMonotone (A : H →L[ℝ] H) :
    A.toLinearMap.IsMonotone ↔ (A + A†).toLinearMap.IsMonotone := by
  constructor
  · change (∀ x : H, 0 ≤ ⟪A x, x⟫_ℝ) →
      ∀ x : H, 0 ≤ ⟪(A + A†) x, x⟫_ℝ
    intro hA x
    have hx : 0 ≤ ⟪A x, x⟫_ℝ := hA x
    have hquad : ⟪(A + A†) x, x⟫_ℝ = (2 : ℝ) * ⟪A x, x⟫_ℝ := by
      calc
        ⟪(A + A†) x, x⟫_ℝ = ⟪A x, x⟫_ℝ + ⟪A.adjoint x, x⟫_ℝ := by
          rw [show (A + A†) x = A x + A.adjoint x by rfl, inner_add_left]
        _ = ⟪A x, x⟫_ℝ + ⟪A x, x⟫_ℝ := by
          rw [adjoint_inner_left, real_inner_comm]
        _ = (2 : ℝ) * ⟪A x, x⟫_ℝ := by ring
    rw [hquad]
    nlinarith
  · change (∀ x : H, 0 ≤ ⟪(A + A†) x, x⟫_ℝ) →
      ∀ x : H, 0 ≤ ⟪A x, x⟫_ℝ
    intro hA x
    have hx : 0 ≤ ⟪(A + A†) x, x⟫_ℝ := hA x
    have hquad : ⟪(A + A†) x, x⟫_ℝ = (2 : ℝ) * ⟪A x, x⟫_ℝ := by
      calc
        ⟪(A + A†) x, x⟫_ℝ = ⟪A x, x⟫_ℝ + ⟪A.adjoint x, x⟫_ℝ := by
          rw [show (A + A†) x = A x + A.adjoint x by rfl, inner_add_left]
        _ = ⟪A x, x⟫_ℝ + ⟪A x, x⟫_ℝ := by
          rw [adjoint_inner_left, real_inner_comm]
        _ = (2 : ℝ) * ⟪A x, x⟫_ℝ := by ring
    rw [hquad] at hx
    nlinarith

-- Proof sketch: transport the quadratic-form inequality across the adjoint identity
-- `⟪A x, x⟫_ℝ = ⟪x, A† x⟫_ℝ`; over `ℝ`, these are the same real number.
/-- Example 20.16 (2): clause (i). A bounded operator is monotone if and only if its adjoint is
monotone. -/
theorem isMonotone_iff_adjoint_isMonotone (A : H →L[ℝ] H) :
    A.toLinearMap.IsMonotone ↔ A†.toLinearMap.IsMonotone := by
  constructor
  · intro hA x
    simpa [adjoint_inner_left, real_inner_comm] using hA x
  · intro hA x
    simpa [adjoint_adjoint, adjoint_inner_left, real_inner_comm] using hA x

-- Proof sketch: rewrite `⟪(A† * A) x, x⟫_ℝ` as `⟪A x, A x⟫_ℝ = ‖A x‖^2`, which is
-- nonnegative.
/-- Example 20.16 (3): clause (ii). The positive operator `A† A` is monotone. -/
theorem adjoint_mul_isMonotone (A : H →L[ℝ] H) :
    (A† * A).toLinearMap.IsMonotone := by
  simpa using (isPositive_adjoint_comp_self A).toLinearMap.isMonotone

-- Proof sketch: rewrite `⟪(A * A†) x, x⟫_ℝ` as `⟪A† x, A† x⟫_ℝ`, hence as a
-- squared norm.
/-- Example 20.16 (4): clause (ii). The positive operator `A A†` is monotone. -/
theorem mul_adjoint_isMonotone (A : H →L[ℝ] H) :
    (A * A†).toLinearMap.IsMonotone := by
  simpa using (isPositive_self_comp_adjoint A).toLinearMap.isMonotone

-- Proof sketch: the operator `A - A†` is skew-adjoint, so its quadratic form vanishes on a
-- real Hilbert space; therefore the monotonicity inequality holds with equality.
/-- Example 20.16 (5): clause (ii). The operator `A - A†` is monotone. -/
theorem sub_adjoint_isMonotone (A : H →L[ℝ] H) :
    (A - A†).toLinearMap.IsMonotone := by
  intro x
  change 0 ≤ ⟪(A - A†) x, x⟫_ℝ
  have hquad : ⟪(A - A†) x, x⟫_ℝ = 0 := by
    calc
      ⟪(A - A†) x, x⟫_ℝ = ⟪A x, x⟫_ℝ - ⟪A.adjoint x, x⟫_ℝ := by
        rw [show (A - A†) x = A x - A.adjoint x by rfl, inner_sub_left]
      _ = ⟪A x, x⟫_ℝ - ⟪A x, x⟫_ℝ := by
        rw [adjoint_inner_left, real_inner_comm]
      _ = 0 := by ring
  nlinarith [hquad]

-- Proof sketch: `A - A†` is monotone by the previous clause. If `A† = -A`, then this operator is
-- `2A`, and dividing the resulting quadratic-form inequality by the positive scalar `2` yields
-- monotonicity of `A`.
/-- A skew-adjoint bounded operator on a real Hilbert space is monotone. -/
theorem isMonotone_of_adjoint_eq_neg (A : H →L[ℝ] H) (hA : A.adjoint = -A) :
    A.toLinearMap.IsMonotone := by
  have hsub : (A - A.adjoint).toLinearMap.IsMonotone := sub_adjoint_isMonotone A
  intro x
  have hx := hsub x
  rw [hA] at hx
  simpa [sub_eq_add_neg, two_smul, real_inner_comm, inner_add_left, inner_smul_left] using hx

-- Proof sketch: this is the negative of `A - A†`, so its quadratic form also vanishes
-- identically.
/-- Example 20.16 (6): clause (ii). The operator `A† - A` is monotone. -/
theorem adjoint_sub_isMonotone (A : H →L[ℝ] H) :
    (A† - A).toLinearMap.IsMonotone := by
  intro x
  change 0 ≤ ⟪(A† - A) x, x⟫_ℝ
  have hquad : ⟪(A† - A) x, x⟫_ℝ = 0 := by
    calc
      ⟪(A† - A) x, x⟫_ℝ = ⟪A.adjoint x, x⟫_ℝ - ⟪A x, x⟫_ℝ := by
        rw [show (A† - A) x = A.adjoint x - A x by rfl, inner_sub_left]
      _ = ⟪A x, x⟫_ℝ - ⟪A x, x⟫_ℝ := by
        rw [adjoint_inner_left, real_inner_comm]
      _ = 0 := by ring
  nlinarith [hquad]

end ContinuousLinearMap
