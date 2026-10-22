/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

noncomputable section

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- The matrix from the remark, whose rows are the cyclic first-difference coefficients on `ℝ^3`.
-/
def cyclic_difference_matrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, -1, 0; 0, 1, -1; -1, 0, 1]

/-- The linear operator on `ℝ^3` defined by the matrix of cyclic first differences. -/
def cyclic_difference_operator : R3 →ₗ[ℝ] R3 :=
  cyclic_difference_matrix.toEuclideanLin

/-- The cyclic difference operator sends `(ξ₁, ξ₂, ξ₃)` to
`(ξ₁ - ξ₂, ξ₂ - ξ₃, ξ₃ - ξ₁)`. -/
-- Proof sketch: expand `cyclic_difference_operator`, evaluate the matrix-vector product row by
-- row, and transport back along `EuclideanSpace.equiv`.
theorem cyclic_difference_operator_apply (x : R3) :
    cyclic_difference_operator x =
      (EuclideanSpace.equiv (Fin 3) ℝ).symm ![x 0 - x 1, x 1 - x 2, x 2 - x 0] := by
  -- Compute the three coordinates of the matrix-vector product explicitly.
  ext i
  fin_cases i
  · simp [cyclic_difference_operator, cyclic_difference_matrix, dotProduct, Fin.sum_univ_three,
      sub_eq_add_neg]
  · simp [cyclic_difference_operator, cyclic_difference_matrix, dotProduct, Fin.sum_univ_three,
      sub_eq_add_neg]
  · simp [cyclic_difference_operator, cyclic_difference_matrix, dotProduct, Fin.sum_univ_three,
      sub_eq_add_neg, add_comm]

/-- The squared norm of `Bx` equals twice the inner product `⟪Bx, x⟫` for the cyclic difference
operator `B`. -/
-- Proof sketch: use `cyclic_difference_operator_apply`, expand both sides in coordinates, and
-- simplify the quadratic expressions.
theorem cyclic_difference_operator_norm_sq_eq_two_inner (x : R3) :
    ‖cyclic_difference_operator x‖ ^ (2 : ℕ) =
      2 * inner ℝ (cyclic_difference_operator x) x := by
  -- Rewrite `Bx` in coordinates and compare the two quadratic polynomials.
  rw [cyclic_difference_operator_apply]
  rw [show inner ℝ ((EuclideanSpace.equiv (Fin 3) ℝ).symm
      ![x 0 - x 1, x 1 - x 2, x 2 - x 0]) x =
      x 0 * (x 0 - x 1) + x 1 * (x 1 - x 2) + x 2 * (x 2 - x 0) by
      simpa [dotProduct, Fin.sum_univ_three] using
        (EuclideanSpace.inner_eq_star_dotProduct
          ((EuclideanSpace.equiv (Fin 3) ℝ).symm ![x 0 - x 1, x 1 - x 2, x 2 - x 0]) x)]
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  ring_nf

/-- The squared norm of `Bx` is `3 ‖x‖²` minus the square of the coordinate sum for the cyclic
difference operator `B`. -/
-- Proof sketch: use `cyclic_difference_operator_apply`, expand the coordinate formulas for
-- `‖Bx‖²`, `‖x‖²`, and `(∑ i, x i)^2`, and compare the resulting polynomials.
theorem cyclic_difference_operator_norm_sq_eq_three_norm_sq_sub_sum_sq (x : R3) :
    ‖cyclic_difference_operator x‖ ^ (2 : ℕ) =
      3 * ‖x‖ ^ (2 : ℕ) - (∑ i : Fin 3, x i) ^ (2 : ℕ) := by
  -- Expand both sides to the same coordinate polynomial and finish algebraically.
  rw [cyclic_difference_operator_apply]
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  ring_nf

/-- Helper for Remark 4.15.2: the cyclic difference operator has norm at most `√3` times the
norm of its argument. -/
-- Square the desired estimate, use the quadratic identity, and drop the nonnegative square term.
private lemma cyclic_difference_operator_norm_le_sqrt_three (z : R3) :
    ‖cyclic_difference_operator z‖ ≤ (NNReal.sqrt 3 : ℝ) * ‖z‖ := by
  have hsquare : ‖cyclic_difference_operator z‖ ^ (2 : ℕ) ≤
      ((NNReal.sqrt 3 : ℝ) * ‖z‖) ^ (2 : ℕ) := by
    have hsqrt : ((NNReal.sqrt 3 : ℝ) ^ (2 : ℕ)) = 3 := by
      norm_num [NNReal.sq_sqrt]
    calc
      ‖cyclic_difference_operator z‖ ^ (2 : ℕ)
          = 3 * ‖z‖ ^ (2 : ℕ) - (∑ i : Fin 3, z i) ^ (2 : ℕ) :=
            cyclic_difference_operator_norm_sq_eq_three_norm_sq_sub_sum_sq z
      _ ≤ 3 * ‖z‖ ^ (2 : ℕ) := by
        nlinarith [sq_nonneg (∑ i : Fin 3, z i)]
      _ = ((NNReal.sqrt 3 : ℝ) * ‖z‖) ^ (2 : ℕ) := by
        rw [mul_pow, hsqrt]
  exact le_of_sq_le_sq hsquare (by positivity)

/-- The cyclic difference operator is `1 / 2`-cocoercive on `ℝ^3`. -/
theorem cyclic_difference_operator_cocoerciveOn :
    CocoerciveOn (1 / 2 : ℝ) Set.univ (fun x : Set.univ ↦ cyclic_difference_operator x) := by
  refine ⟨by norm_num, ?_⟩
  intro x y
  have h_identity := cyclic_difference_operator_norm_sq_eq_two_inner ((x : R3) - y)
  have h_eq :
      (1 / 2 : ℝ) * ‖cyclic_difference_operator ((x : R3) - y)‖ ^ (2 : ℕ) =
        inner ℝ (cyclic_difference_operator ((x : R3) - y)) ((x : R3) - y) := by
    nlinarith [h_identity]
  simpa [real_inner_comm] using le_of_eq h_eq

/-- The cyclic difference operator is `√3`-Lipschitz on `ℝ^3`. -/
theorem cyclic_difference_operator_lipschitzWith :
    LipschitzWith (NNReal.sqrt 3) cyclic_difference_operator := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [dist_eq_norm, dist_eq_norm, ← cyclic_difference_operator.map_sub]
  exact cyclic_difference_operator_norm_le_sqrt_three (x - y)

/-- Remark 4.15.2: the cyclic difference operator associated to
`B = [[1, -1, 0], [0, 1, -1], [-1, 0, 1]]` is `1 / 2`-cocoercive on `ℝ^3` and is
`√3`-Lipschitz continuous. -/
-- Proof sketch: apply
-- `cyclic_difference_operator_norm_sq_eq_two_inner` and
-- `cyclic_difference_operator_norm_sq_eq_three_norm_sq_sub_sum_sq` to `x - y`; the first identity
-- gives the `1 / 2`-cocoercivity inequality, and the second gives the `√3` Lipschitz bound from
-- the nonnegativity of `(∑ i, (x - y) i)^2`.
theorem cyclic_difference_operator_cocoercive_and_lipschitz :
    CocoerciveOn (1 / 2 : ℝ) Set.univ (fun x : Set.univ ↦ cyclic_difference_operator x) ∧
    LipschitzWith (NNReal.sqrt 3) cyclic_difference_operator := by
  exact ⟨cyclic_difference_operator_cocoerciveOn, cyclic_difference_operator_lipschitzWith⟩
