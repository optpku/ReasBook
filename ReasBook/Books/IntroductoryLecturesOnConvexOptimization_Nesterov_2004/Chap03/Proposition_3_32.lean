/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Text_2_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_35

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped CoordinateSubspace

variable {k : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin k)

/- Primary domain: the finite-dimensional Nemirovski hard instance on `ℝ^k`, together with the
prefix-coordinate maximum appearing in the early-iterate lower bound.

Sampled owner-style declarations:
* `firstKCoordinateFamily` in `Chap03/Definition_3_35`, the restricted coordinate family behind
  the hard instance;
* `first_k_coordinate_max` in `Chap03/Definition_3_35`, the canonical prefix-maximum owner;
* `f_k` in `Chap03/Definition_3_35`, the source-facing Nemirovski hard-instance objective.

Best owner abstraction:
* source-facing: the early-iterate nonnegativity statement for the actual hard-instance owner
  `f_k`;
* core/canonical: `f_k` and `first_k_coordinate_max`.

Primitive data:
* the hard-instance parameters `μ` and `γ`;
* the iterate sequence `x`;
* the textbook hypothesis `first_k_coordinate_max k k (x i) = 0` for `i ≤ k - 1`.

Derived API:
* the generic lower bound
  `γ * first_k_coordinate_max k k x ≤ f_k k k μ γ x` when `μ ≥ 0`;
* the early-iterate consequence `0 ≤ f_k k k μ γ (x i)`.

Source/core/bridge triage:
* source-facing: `no_decrease_f_k_first_steps`;
* core/canonical: `f_k`, `first_k_coordinate_max`;
* bridge/view: `scaled_first_k_coordinate_max_le_f_k`.

The source proposition does not use the support statement `x i ∈ ℝ^{i,k}` directly. Its displayed
hypothesis is the stronger explicit equality `max_{1 ≤ j ≤ k} x_i^(j) = 0`, represented here by
`first_k_coordinate_max k k (x i) = 0`. This file therefore keeps the textbook owner `f_k` as the
main declaration, uses the canonical prefix-maximum owner from Definition 3.35, and records the
lower bound `f_k(x_i) ≥ γ max_j x_i^(j)` only through the direct formula for `f_k`. -/

/-- Helper for Proposition 3.32 [Chapter3_2.json:70]: the quadratic term in `f_k` is
nonnegative whenever `μ ≥ 0`. -/
-- Proof sketch: `μ / 2` is nonnegative because both `μ` and `2` are nonnegative, and `‖x‖^2`
-- is nonnegative as a square; multiplying the two nonnegative factors preserves nonnegativity.
theorem f_k_quadratic_term_nonneg
    (μ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    0 ≤ (μ / 2) * ‖x‖ ^ 2 := by
  -- The scalar coefficient stays nonnegative after division by `2`.
  have hcoeff : 0 ≤ μ / 2 := by
    exact div_nonneg hμ (by norm_num)
  -- The squared norm is nonnegative because it is a square in `ℝ`.
  have hsq : 0 ≤ ‖x‖ ^ 2 := by
    simpa [pow_two] using sq_nonneg ‖x‖
  -- Combine the two nonnegative factors.
  exact mul_nonneg hcoeff hsq

/-- Helper for Proposition 3.32 [Chapter3_2.json:70]: the Nemirovski hard-instance value
dominates the scaled maximum of the first `k`
coordinates whenever the quadratic coefficient `μ` is nonnegative. -/
-- Proof sketch: unfold `f_k`; the quadratic term `(μ / 2) * ‖x‖^2` is nonnegative when `μ ≥ 0`,
-- so `f_k` is bounded below by its `γ * first_k_coordinate_max` summand.
theorem scaled_first_k_coordinate_max_le_f_k
    (μ γ : ℝ) (hμ : 0 ≤ μ) (x : E) :
    γ * first_k_coordinate_max k k x ≤ f_k k k μ γ x := by
  -- Unfold `f_k` so the goal becomes a comparison with an added nonnegative term.
  rw [f_k_def]
  have hquad : 0 ≤ (μ / 2) * ‖x‖ ^ 2 := f_k_quadratic_term_nonneg (μ := μ) hμ x
  -- The added quadratic contribution can only increase the value.
  nlinarith

/-- Helper for Proposition 3.32 [Chapter3_2.json:70]: if the maximum among the first `k`
coordinates of `x` is `0`, then the Nemirovski
hard-instance value at `x` is nonnegative whenever `μ ≥ 0`. -/
-- Proof sketch: combine `scaled_first_k_coordinate_max_le_f_k` with the hypothesis
-- `first_k_coordinate_max k k x = 0` and rewrite the left-hand side to `0`.
theorem f_k_nonneg_of_first_k_coordinate_max_eq_zero
    (μ γ : ℝ) (hμ : 0 ≤ μ) {x : E}
    (hmax : first_k_coordinate_max k k x = 0) :
    0 ≤ f_k k k μ γ x := by
  -- First lower-bound `f_k x` by the scaled prefix maximum.
  have hbound := scaled_first_k_coordinate_max_le_f_k (k := k) μ γ hμ x
  -- The textbook hypothesis identifies that scaled maximum with `0`.
  rw [hmax] at hbound
  simpa using hbound

/-- Proposition 3.32 [Chapter3_2.json:70]: if each iterate `x_i` with `0 ≤ i ≤ k - 1` satisfies
`max_{1 ≤ j ≤ k} x_i^(j) = 0`, then along the first `k - 1` nonzero steps one has
`f_k(x_i) ≥ γ max_{1 ≤ j ≤ k} x_i^(j) = 0`; equivalently, `f_k (x_{i+1}) ≥ 0` for every
`i < k - 1`. -/
-- Proof sketch: for `x (i + 1)`, apply `f_k_nonneg_of_first_k_coordinate_max_eq_zero` using the
-- textbook hypothesis at the index `i + 1`; the required bound follows from
-- `Nat.succ_le_of_lt hi`.
theorem no_decrease_f_k_first_steps
    (μ γ : ℝ) (hμ : 0 ≤ μ) (x : ℕ → E)
    (hmax : ∀ i : ℕ, i ≤ k - 1 → first_k_coordinate_max k k (x i) = 0)
    {i : ℕ} (hi : i < k - 1) :
    0 ≤ f_k k k μ γ (x (i + 1)) := by
  -- The hypothesis applies at the shifted index `i + 1` because `i < k - 1`.
  have hmax_succ : first_k_coordinate_max k k (x (i + 1)) = 0 := by
    exact hmax (i + 1) (Nat.succ_le_of_lt hi)
  -- Specialize the generic nonnegativity lemma to the iterate `x (i + 1)`.
  simpa using
    f_k_nonneg_of_first_k_coordinate_max_eq_zero
      (k := k) (μ := μ) (γ := γ) hμ (x := x (i + 1)) hmax_succ

end
