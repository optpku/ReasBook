/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Lemma 3.3.2 lies in the chapter's level-method one-step cutting-plane domain.

Sampled owner declarations:
* `maxTypeObjective` in `Chap02/Lemma_2_18`, the project owner for finite maxima of a nonempty
  finite family of real-valued functions
* `maxTypeObjective_apply` in `Chap02/Lemma_2_18`, the canonical evaluation bridge for that owner
* `LevelMethodHistory` in `Lemma_3_3_1`, the owner scalar history
* `LevelMethodHistory.gap` in `Lemma_3_3_1`, the canonical gap `δ_k`
* `LevelMethodHistory.levelValue` in `Lemma_3_3_1`, the canonical level value `ℓ_k(α)`
* `LevelMethodHistory.levelValue_eq_optimal_sub_one_sub_alpha_mul_gap` in `Lemma_3_3_1`, the
  owner scalar rewrite used below

Best owner abstraction:
* the generic finite-max owner `maxTypeObjective`
* the scalar side of the one-step estimate is organized by `LevelMethodHistory`

Primitive data:
* the sampled points `x k`, `x (k + 1)` and chosen slopes `g k`
* the owner scalar history `history`

Derived API:
* `history.gap k`
* `history.levelValue α k`
* the source-facing Kelley specialization `nonsmoothModel f x g k` of `maxTypeObjective`

Accordingly, this file keeps `nonsmoothModel` only as the source-facing Kelley specialization of
the existing finite-max owner `maxTypeObjective`, and states the one-step norm estimate directly
over the scalar-history owner instead of repeating separate sequence-level gap and level-value
definitions.
-/

/-- The nonsmooth model `\hat f_k` is the finite maximum of the sampled affine minorants built
from `x₀, …, x_k` and the chosen subgradients `g₀, …, g_k` in the ambient real inner-product
space. This is the direct Kelley specialization of the project owner `maxTypeObjective`. -/
abbrev nonsmoothModel (f : E → ℝ) (x g : ℕ → E) (k : ℕ) : E → ℝ :=
  maxTypeObjective
    (fun i : Fin (k + 1) ↦ fun y ↦ f (x i) + inner ℝ (g i) (y - x i))

namespace NonsmoothModelNotation

scoped notation:max "f̂[" X:arg "; " f:arg "; " g:arg "](" k:arg ")" =>
  nonsmoothModel f X g k

end NonsmoothModelNotation

open scoped NonsmoothModelNotation

/-- Evaluating `f̂[X; f; g](k)` at `y` gives the finite maximum over the first `k + 1` sampled
affine minorants. -/
-- Proof sketch: unfold `nonsmoothModel`; the displayed `Finset.sup'` expression is exactly the
-- defining finite maximum.
theorem nonsmoothModel_apply
    (f : E → ℝ) (X g : ℕ → E) (k : ℕ) (y : E) :
    f̂[X; f; g](k) y =
      Finset.univ.sup' Finset.univ_nonempty fun i : Fin (k + 1) ↦
        f (X i) + inner ℝ (g i) (y - X i) := by
  simpa using
    (maxTypeObjective_apply
      (fun i : Fin (k + 1) ↦ fun z ↦ f (X i) + inner ℝ (g i) (z - X i))
      y)

/-- Lemma 3.3.2: if the level value at iteration `k` dominates the sampled model at `x_{k+1}`,
the record value satisfies `f_k^* ≤ f(x_k)`, and the selected subgradient norm is bounded by
`M_f`, then the step length satisfies
`‖x_{k+1} - x_k‖ ≥ ((1 - α) δ_k) / M_f`. -/
-- Proof sketch: rewrite `history.levelValue α k` as
-- `history.optimalValue k - (1 - α) * history.gap k`, compare `history.optimalValue k` with
-- `f(x k)`, and use `nonsmoothModel_apply` with the `Fin.last k` term of the finite supremum to get
-- `(1 - α) * δ_k ≤ -⟪g_k, x_{k+1} - x_k⟫`. Then bound the inner product by
-- `‖g_k‖ * ‖x_{k+1} - x_k‖ ≤ M_f * ‖x_{k+1} - x_k‖` and divide by `M_f > 0`.
lemma step_norm_lower_bound_of_level_method_assumptions
    {f : E → ℝ} {X g : ℕ → E} {history : LevelMethodHistory}
    (α Mf : ℝ) {k : ℕ}
    (hrecord_le_current : history.optimalValue k ≤ f (X k))
    (hlevel_ge_model :
      history.levelValue α k ≥
        f̂[X; f; g](k) (X (k + 1)))
    (hsubgradient_bound : ‖g k‖ ≤ Mf)
    (hMf_pos : 0 < Mf) :
    ‖X (k + 1) - X k‖ ≥
      ((1 - α) * history.gap k) / Mf := by
  let step := X (k + 1) - X k
  have hterm_le_model :
      f (X k) + inner ℝ (g k) step ≤
        f̂[X; f; g](k) (X (k + 1)) := by
    rw [nonsmoothModel_apply]
    simpa [step] using
      (Finset.le_sup'
        (fun i : Fin (k + 1) ↦ f (X i) + inner ℝ (g i) (X (k + 1) - X i))
        (by simp : Fin.last k ∈ Finset.univ))
  have hmodel_le_level :
      f (X k) + inner ℝ (g k) step ≤ history.levelValue α k :=
    hterm_le_model.trans hlevel_ge_model
  rw [history.levelValue_eq_optimal_sub_one_sub_alpha_mul_gap α k] at hmodel_le_level
  have hgap_le_neg_inner :
      (1 - α) * history.gap k ≤ -inner ℝ (g k) step := by
    linarith
  have hinner_abs :
      |inner ℝ (g k) step| ≤ ‖g k‖ * ‖step‖ := by
    simpa using abs_real_inner_le_norm (g k) step
  have hgap_le_step_mul :
      (1 - α) * history.gap k ≤ Mf * ‖step‖ := by
    calc
      (1 - α) * history.gap k ≤ -inner ℝ (g k) step := hgap_le_neg_inner
      _ ≤ |inner ℝ (g k) step| := neg_le_abs _
      _ ≤ ‖g k‖ * ‖step‖ := hinner_abs
      _ ≤ Mf * ‖step‖ :=
        mul_le_mul_of_nonneg_right hsubgradient_bound (norm_nonneg _)
  have hdiv :
      ((1 - α) * history.gap k) / Mf ≤ ‖step‖ :=
    (div_le_iff₀ hMf_pos).2 (by simpa [mul_comm] using hgap_le_step_mul)
  simpa [ge_iff_le, step] using hdiv

end
