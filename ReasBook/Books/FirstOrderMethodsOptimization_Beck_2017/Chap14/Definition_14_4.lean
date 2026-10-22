/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

/- Definition 14.4 is `source-facing`: the textbook introduces a specific two-variable convex
objective by an explicit formula. Domain sampling in the local convex-analysis API points to the
following owner split.
- `core/canonical`: `ConvexOn` for the convexity statement;
- `core/canonical`: `convexOn_univ_norm` and `ConvexOn.comp_linearMap` for absolute values of
  linear forms;
- `core/canonical`: `ConvexOn.add` for the sum; and
- `bridge/view`: the Chapter 9 coercion `Function.toEReal` for downstream extended-real uses of the
  same objective.

The primitive data are only the displayed real-valued objective itself. Its evaluation formula,
convexity, and any later `EReal` view are derived API, so this file should reuse those owner
declarations directly instead of introducing local wrapper versions. -/

/-- Definition 14.4: Example 14.5 (failure of alternating minimization II) defines the convex
objective `F : ℝ × ℝ → ℝ` by `F(x₁, x₂) = |3x₁ + 4x₂| + |x₁ - 2x₂|`. -/
def alternating_minimization_failure_ii_objective : ℝ × ℝ → ℝ :=
  fun (x₁, x₂) ↦ |3 * x₁ + 4 * x₂| + |x₁ - 2 * x₂|

-- Proof sketch: unfold `alternating_minimization_failure_ii_objective`; evaluating it on the pair
-- `(x₁, x₂)` gives exactly the displayed formula from the source.
/-- Evaluating `alternating_minimization_failure_ii_objective` at `(x₁, x₂)` reproduces the
displayed formula `|3x₁ + 4x₂| + |x₁ - 2x₂|`. -/
@[simp] theorem alternating_minimization_failure_ii_objective_apply (x₁ x₂ : ℝ) :
    alternating_minimization_failure_ii_objective (x₁, x₂) =
      |3 * x₁ + 4 * x₂| + |x₁ - 2 * x₂| := rfl

-- Proof sketch: the maps `(x₁, x₂) ↦ 3x₁ + 4x₂` and `(x₁, x₂) ↦ x₁ - 2x₂` are affine on
-- `ℝ × ℝ`. Since the absolute value on `ℝ` is convex on `Set.univ`, each summand is convex by
-- affine precomposition, and their sum is convex.
/-- The objective from Example 14.5 is convex on all of `ℝ × ℝ`. -/
theorem alternating_minimization_failure_ii_objective_convex :
    ConvexOn ℝ Set.univ alternating_minimization_failure_ii_objective := by
  let l34 : ℝ × ℝ →ₗ[ℝ] ℝ := 3 • LinearMap.fst ℝ ℝ ℝ + 4 • LinearMap.snd ℝ ℝ ℝ
  let l12 : ℝ × ℝ →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ - 2 • LinearMap.snd ℝ ℝ ℝ
  have h34 : ConvexOn ℝ Set.univ (fun x : ℝ × ℝ ↦ ‖l34 x‖) := by
    simpa using convexOn_univ_norm.comp_linearMap l34
  have h12 : ConvexOn ℝ Set.univ (fun x : ℝ × ℝ ↦ ‖l12 x‖) := by
    simpa using convexOn_univ_norm.comp_linearMap l12
  refine (h34.add h12).congr ?_
  intro x hx
  simp [alternating_minimization_failure_ii_objective, l34, l12, Real.norm_eq_abs]

end
