/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set Real

/- Definition 3.71 lies in the chapter's scalar real-analysis / interval-maximization domain.

Sampled owner-style declarations:
- `levelMethodIterationCap` in `Theorem_3_3_1`, where the chapter already uses the factor
  `α * (1 - α)^2 * (2 - α)` as the `α`-dependent complexity term;
- `completeDataInternalIterationBound` in `Lemma_3_3_9`, which reuses the same owner factor
  downstream;
- `IsMaxOn` and `isMaxOn_iff` from Mathlib's extremum API;
- `IsCompact.exists_isMaxOn` from Mathlib's extreme-value API on compact sets.

Best owner abstraction:
- there is no earlier chapter declaration isolating the scalar factor
  `α * (1 - α)^2 * (2 - α)` as its own owner object, so this file keeps the source-facing
  objective itself as the local owner;
- the canonical optimality property
  `IsMaxOn levelParameterObjective (Set.Icc (0 : ℝ) 1) optimalLevelParameter`.

Primitive data:
- the source-facing scalar objective `levelParameterObjective`, written in the owner form already
  used by the level-method bounds;
- the displayed parameter `optimalLevelParameter`.

Derived API:
- admissibility of `optimalLevelParameter` in `(0, 1)`, hence also in `[0, 1]`;
- the exact optimizer value `levelParameterObjective optimalLevelParameter = 1 / 4`;
- maximality on `[0, 1]` via `IsMaxOn`.

Source/core/bridge triage:
- source-facing: the textbook optimizer and its scalar objective;
- core/canonical: the chapter-side factor `α * (1 - α)^2 * (2 - α)` together with `IsMaxOn` on
  `Set.Icc (0 : ℝ) 1`;
- bridge/view: the algebraic normal form reducing the maximization claim to the square bound
  `0 ≤ (x - 1 / 2)^2`.
-/

/-- Definition 3.71: the level-parameter objective is the chapter's scalar iteration-cap factor
`α ↦ α (1 - α)^2 (2 - α)`, equivalently `(1 - α)^2 (1 - (1 - α)^2)`, on `[0, 1]`. -/
def levelParameterObjective (α : ℝ) : ℝ :=
  α * (1 - α) ^ 2 * (2 - α)

/-- The optimal level parameter `α* = 1 / (2 + √2)`. -/
def optimalLevelParameter : ℝ :=
  1 / (2 + sqrt 2)

/-- The displayed optimizer satisfies the exact bridge identity
`1 - α* = √2 / 2`. -/
theorem one_sub_optimalLevelParameter_eq :
    1 - optimalLevelParameter = sqrt 2 / 2 := by
  rw [optimalLevelParameter]
  field_simp [show (2 + sqrt 2 : ℝ) ≠ 0 by positivity]
  ring_nf
  nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- Completing the square rewrites the level-parameter objective in the canonical form used to
prove its maximum. -/
theorem levelParameterObjective_eq_quarter_sub_sq (α : ℝ) :
    levelParameterObjective α =
      1 / 4 - ((1 - α) ^ 2 - 1 / 2) ^ 2 := by
  unfold levelParameterObjective
  ring

/-- On the admissible interval `(0, 1)`, the level-parameter objective is strictly positive. -/
theorem levelParameterObjective_pos {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    0 < levelParameterObjective α := by
  rcases hα with ⟨hα0, hα1⟩
  have hOneSub : 0 < 1 - α := sub_pos.mpr hα1
  have hTwoSub : 0 < 2 - α := by linarith
  rw [levelParameterObjective]
  exact mul_pos (mul_pos hα0 (pow_pos hOneSub 2)) hTwoSub

private theorem optimalLevelParameter_sq :
    (1 - optimalLevelParameter) ^ 2 = 1 / 2 := by
  rw [one_sub_optimalLevelParameter_eq]
  ring_nf
  nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- Evaluating the level-parameter objective at the displayed optimizer gives the extremal value
`1 / 4`. -/
theorem optimalLevelParameterObjective_eq_quarter :
    levelParameterObjective optimalLevelParameter = 1 / 4 := by
  rw [levelParameterObjective_eq_quarter_sub_sq, optimalLevelParameter_sq]
  ring

/-- The displayed optimizer lies in the admissible interval `(0, 1)`. -/
theorem optimalLevelParameter_mem_Ioo :
    optimalLevelParameter ∈ Ioo (0 : ℝ) 1 := by
  have hsqrt2 : 0 < sqrt 2 := by
    exact sqrt_pos.2 (by norm_num)
  have hsqrt2_lt_two : sqrt 2 < 2 := by
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), hsqrt2]
  rw [mem_Ioo]
  constructor
  · nlinarith [one_sub_optimalLevelParameter_eq, hsqrt2_lt_two]
  · nlinarith [one_sub_optimalLevelParameter_eq, hsqrt2]

/-- The displayed optimizer lies in the feasible interval `[0, 1]`. -/
theorem optimalLevelParameter_mem_Icc :
    optimalLevelParameter ∈ Icc (0 : ℝ) 1 := by
  rcases optimalLevelParameter_mem_Ioo with ⟨h0, h1⟩
  exact ⟨le_of_lt h0, le_of_lt h1⟩

/-- The displayed optimizer maximizes the level-parameter objective on `[0, 1]`. -/
theorem optimalLevelParameter_isMaxOn :
    IsMaxOn levelParameterObjective (Icc (0 : ℝ) 1) optimalLevelParameter := by
  rw [isMaxOn_iff]
  intro α _
  rw [levelParameterObjective_eq_quarter_sub_sq, optimalLevelParameterObjective_eq_quarter]
  nlinarith [sq_nonneg ((1 - α) ^ 2 - 1 / 2)]

end
