/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Lemma_6_5
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Example 6.14 is `source-facing`: the primitive data are the scalar slope `μ` and the interval
bound `α`. Domain sampling in the chapter shows that the owner abstractions for the same notion are
already upstream:

- Chapter 2's `extendedIndicator` for interval constraints,
- Lemma 6.5's interval-indicator proximal formula,
- Theorem 6.13's affine/quadratic proximal transport.

Accordingly, the file keeps only the source penalty, and derives the closed-form proximal
singleton directly from the owner-level interval-indicator API rather than duplicating a local
bridge definition. -/

/-- The truncated linear penalty `x ↦ μ x` on `[0, α] ∩ ℝ` and `∞` outside that interval. -/
def truncated_linear_penalty (μ : ℝ) (α : ENNReal) : ℝ → EReal :=
  extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)} +
    fun x ↦ ((μ * x : ℝ) : EReal)

/-- Evaluating the truncated linear penalty gives the affine term plus the indicator of the
feasible interval `[0, α] ∩ ℝ`. -/
@[simp] theorem truncated_linear_penalty_apply (μ x : ℝ) (α : ENNReal) :
    truncated_linear_penalty μ α x =
      extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)} x + ((μ * x : ℝ) : EReal) :=
  rfl

-- Proof sketch: apply Theorem 6.13 with `g` equal to the Chapter 2 owner `extendedIndicator` of
-- `[0, α] ∩ ℝ`, `c = 0`, and `a = μ`. This transports the proximal problem to the
-- interval-indicator proximal formula from Lemma 6.5 at the shifted base point `x - μ`.
/-- Example 6.14: for the function `f(x) = μ x` on `[0, α] ∩ ℝ` and `∞` outside, where
`α ∈ [0, ∞]`, the proximal mapping at `x` is the singleton consisting of the projection of
`x - μ` onto `[0, α] ∩ ℝ`. -/
theorem prox_truncated_linear_penalty_eq_singleton
    (μ : ℝ) (α : ENNReal) (x : ℝ) :
    prox[truncated_linear_penalty μ α] x =
      {if α = ⊤ then max (x - μ) 0 else min (max (x - μ) 0) α.toReal} := by
  set C : Set ℝ := {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)}
  have hinner (u : ℝ) : inner ℝ μ u = μ * u := by
    simpa [mul_comm] using real_inner_comm u μ
  calc
    prox[truncated_linear_penalty μ α] x
      = prox[extendedIndicator C] (x - μ) := by
          simpa [truncated_linear_penalty, C, sub_eq_add_neg, hinner, mul_comm] using
            proximal_mapping_quadratic_perturbation
              (extendedIndicator C) 0 (by norm_num) μ x
    _ = {if α = ⊤ then max (x - μ) 0 else min (max (x - μ) 0) α.toReal} := by
      simpa [C] using prox_nonnegative_interval_indicator_eq_singleton α (x - μ)

end
