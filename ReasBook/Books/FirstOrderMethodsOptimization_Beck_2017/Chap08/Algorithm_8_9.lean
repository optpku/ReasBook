/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {m n : ℕ}

local notation "E" => Fin n → ℝ

/- Algorithm 8.9 is `source-facing` in the linear convex-feasibility API. As in Algorithm 8.6,
the canonical owner is the recursive iterate sequence itself, while the maximizing-row condition
is recorded separately as an admissibility predicate on the row-selection rule rather than hidden
behind a noncanonical argmax choice. The ambient space is kept in the coordinate model
`Fin n → ℝ`, since the source item simultaneously uses row inner products `aᵢᵀ x` and the
coordinatewise positive part `[x]_+ = x⁺`. -/

/-- The normalized residual of the `j`-th affine row `a_jᵀ x = b_j` at `x`. -/
def normalized_row_residual
    (a : Fin m → E) (b : Fin m → ℝ) (x : E) (j : Fin m) : ℝ :=
  |dotProduct (a j) x - b j| / ‖a j‖

-- Proof sketch: unfold `normalized_row_residual`; it is definitionally the normalized absolute
-- affine-row violation `|a_jᵀ x - b_j| / ‖a_j‖`.
/-- Evaluating `normalized_row_residual` gives the normalized absolute violation
`|a_jᵀ x - b_j| / ‖a_j‖`. -/
@[simp] theorem normalized_row_residual_eq
    (a : Fin m → E) (b : Fin m → ℝ) (x : E) (j : Fin m) :
    normalized_row_residual a b x j = |dotProduct (a j) x - b j| / ‖a j‖ := by
  -- Unfolding the residual definition exposes the normalized affine-row violation verbatim.
  rfl

/-- Algorithm 8.9: given affine rows `a_iᵀ x = b_i`, an initial point `x0`, and a rule choosing
at each iterate a row with maximal normalized residual, the greedy linear-feasibility projection
method updates `x^k` either by the orthogonal correction onto the selected row hyperplane or by
the positive part `x⁺ = [x]_+`, according to which correction is farther from the current
iterate. -/
def greedy_linear_feasibility_projection_method
    (a : Fin m → E) (b : Fin m → ℝ) (i : ℕ → E → Fin m) (x0 : E) : ℕ → E
  | 0 => x0
  | k + 1 =>
      let xk := greedy_linear_feasibility_projection_method a b i x0 k
      let ik := i k xk
      if normalized_row_residual a b xk ik > ‖xk - xk⁺‖ then
        xk - ((dotProduct (a ik) xk - b ik) / ‖a ik‖ ^ (2 : ℕ)) • a ik
      else
        xk⁺

/-- A row-selection rule is admissible for the greedy linear-feasibility projection method when,
at each current iterate `x^k`, the selected row attains the maximum of the normalized residual
profile `j ↦ |a_jᵀ x^k - b_j| / ‖a_j‖`. -/
def greedy_linear_feasibility_projection_method_is_admissible
    (a : Fin m → E) (b : Fin m → ℝ) (i : ℕ → E → Fin m) (x0 : E) : Prop :=
  ∀ k,
    let xk := greedy_linear_feasibility_projection_method a b i x0 k
    ∀ j : Fin m,
      normalized_row_residual a b xk j ≤ normalized_row_residual a b xk (i k xk)

section

variable (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
  (i : ℕ → (Fin n → ℝ) → Fin m) (x0 : Fin n → ℝ)

local notation "x[" k "]" => greedy_linear_feasibility_projection_method a b i x0 k

-- Proof sketch: unfold the recursive definition of
-- `greedy_linear_feasibility_projection_method` at `0`.
/-- The greedy linear-feasibility projection sequence starts at the prescribed initial point. -/
theorem greedy_linear_feasibility_projection_method_zero :
    x[0] = x0 := by
  -- The initialization step is exactly the `0` branch of the recursive definition.
  rfl

-- Proof sketch: unfold the recursive definition of
-- `greedy_linear_feasibility_projection_method` at `k + 1`.
/-- One step of the greedy linear-feasibility projection method chooses between the affine
row-correction update along the selected row and the coordinatewise positive part of the current
iterate. -/
theorem greedy_linear_feasibility_projection_method_succ (k : ℕ) :
    x[k + 1] =
      if normalized_row_residual a b x[k] (i k x[k]) > ‖x[k] - x[k]⁺‖ then
        x[k] -
          ((dotProduct (a (i k x[k])) x[k] - b (i k x[k])) /
              ‖a (i k x[k])‖ ^ (2 : ℕ)) •
            a (i k x[k])
      else
        x[k]⁺ := by
  -- Unfolding one recursive step reveals the row-correction/positive-part update verbatim.
  rfl

-- Proof sketch: unfold `greedy_linear_feasibility_projection_method_is_admissible`, specialize
-- at the index `k`, and evaluate the resulting maximality condition at the competitor row `j`.
/-- Under the admissibility condition, the selected row at iteration `k` has normalized residual
at least as large as every other row. -/
theorem greedy_linear_feasibility_projection_method_selected_row_maximizes
    (h : greedy_linear_feasibility_projection_method_is_admissible a b i x0) (k : ℕ)
    (j : Fin m) :
    normalized_row_residual a b x[k] j ≤ normalized_row_residual a b x[k] (i k x[k]) := by
  -- The admissibility predicate stores exactly the maximal normalized-residual inequality.
  simpa [greedy_linear_feasibility_projection_method_is_admissible] using h k j

end

end
