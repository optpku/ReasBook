/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A map on a subset of a real Hilbert space is pseudononexpansive when its values satisfy the
textbook inequality
`‖T x - T y‖² ≤ ‖x - y‖² + ‖(Id - T) x - (Id - T) y‖²` for every `x, y ∈ D`. -/
def PseudononexpansiveOn (D : Set H) (T : D → H) : Prop :=
  ∀ x y : D,
    ‖T x - T y‖ ^ (2 : ℕ) ≤
      ‖((x : H) - y)‖ ^ (2 : ℕ) + ‖residualMap D T x - residualMap D T y‖ ^ (2 : ℕ)

-- Proof sketch: expand the residual difference as
-- `((x : H) - y) - (T x - T y)`, use the real Hilbert-space identity for `‖u - v‖²`, cancel the
-- common `‖T x - T y‖²` term, and rewrite the remaining inequality as the monotonicity inequality
-- for `A = Id - T`.
/-- Example 20.8: a map `T : D → H` is pseudononexpansive if and only if its residual map
`A = Id - T` defines a monotone singleton-valued operator on `D`. -/
theorem pseudononexpansiveOn_iff_residualMap_isMonotone {D : Set H} {T : D → H} :
    PseudononexpansiveOn D T ↔
      (SetValuedOperator.ofFunction D (residualMap D T)).IsMonotone := by
  rw [SetValuedOperator.ofFunction_isMonotone_iff]
  constructor
  · intro h x y
    let a : H := (x : H) - y
    let b : H := T x - T y
    have hres : residualMap D T x - residualMap D T y = a - b := by
      change (((x : H) - T x) - (y - T y)) = a - b
      dsimp [a, b]
      abel_nf
    have hpseudo : ‖b‖ ^ (2 : ℕ) ≤ ‖a‖ ^ (2 : ℕ) + ‖a - b‖ ^ (2 : ℕ) := by
      simpa [a, b, hres] using h x y
    have hinner : ⟪a, a - b⟫_ℝ = ‖a‖ ^ (2 : ℕ) - ⟪a, b⟫_ℝ := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
    have hmono : 0 ≤ ⟪a, a - b⟫_ℝ := by
      nlinarith [norm_sub_sq_real a b, hpseudo, hinner]
    simpa [a, b, hres] using hmono
  · intro h x y
    let a : H := (x : H) - y
    let b : H := T x - T y
    have hmono : 0 ≤ ⟪a, residualMap D T x - residualMap D T y⟫_ℝ := by
      simpa [a] using h x y
    have hres : residualMap D T x - residualMap D T y = a - b := by
      change (((x : H) - T x) - (y - T y)) = a - b
      dsimp [a, b]
      abel_nf
    have hinner : ⟪a, a - b⟫_ℝ = ‖a‖ ^ (2 : ℕ) - ⟪a, b⟫_ℝ := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
    rw [hres] at hmono
    have hnorm : ‖a - b‖ ^ (2 : ℕ) = ‖a‖ ^ (2 : ℕ) - 2 * ⟪a, b⟫_ℝ + ‖b‖ ^ (2 : ℕ) := by
      simpa using norm_sub_sq_real a b
    simpa [a, b, hres] using
      (show ‖b‖ ^ (2 : ℕ) ≤ ‖a‖ ^ (2 : ℕ) + ‖a - b‖ ^ (2 : ℕ) by
        nlinarith [hmono, hinner, hnorm])
