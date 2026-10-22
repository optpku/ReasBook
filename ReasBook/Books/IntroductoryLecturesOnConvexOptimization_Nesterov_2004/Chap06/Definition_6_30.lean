/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- The penalized dual maximand
`u ↦ ⟪A x, u⟫ - \hat φ(u) - μ₂ d₂(u)` appearing in the smoothed primal objective. -/
def smoothedPrimalObjectiveMaximand
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (hatφ d₂ : E₂ → ℝ) (μ₂ : ℝ) (x : E₁) : E₂ → ℝ :=
  fun u ↦ A x u - hatφ u - μ₂ * d₂ u

/-- Definition 6.30: for a positive smoothing parameter `μ₂` and a prox-function `d₂` on `Q₂`,
`smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂ x` is the smoothed primal objective
`f_{μ₂}(x) = \hat f(x) + max_{u ∈ Q₂} {⟪A x, u⟫ - \hat φ(u) - μ₂ d₂(u)}`, recorded in Lean as
`hatf x + sSup (...)`; this agrees with the displayed maximum whenever a maximizer exists. -/
def smoothedPrimalObjective
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (Q₂ : Set E₂)
    (hatf : E₁ → ℝ) (hatφ d₂ : E₂ → ℝ) (μ₂ : ℝ) : E₁ → ℝ :=
  fun x ↦ hatf x + sSup (smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x '' Q₂)

-- Proof sketch: unfold `smoothedPrimalObjective`; the right-hand side is exactly the defining
-- formula `\hat f(x) + sup_{u ∈ Q₂} (⟪A x, u⟫ - \hat φ(u) - μ₂ d₂(u))`.
/-- Evaluating `smoothedPrimalObjective` recovers the defining sum of `\hat f(x)` and the
supremum of the penalized dual maximand over `Q₂`. -/
@[simp]
theorem smoothedPrimalObjective_apply
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (Q₂ : Set E₂)
    (hatf : E₁ → ℝ) (hatφ d₂ : E₂ → ℝ) (μ₂ : ℝ) (x : E₁) :
    smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂ x =
      hatf x + sSup (smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x '' Q₂) :=
  rfl

/-- The argmax set of the penalized dual maximand at `x`, encoding the admissible choices of the
textbook point `u_{μ₂}(x)` as feasible maximizers on `Q₂`. -/
abbrev smoothedPrimalObjectiveArgmax
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (Q₂ : Set E₂) (hatφ d₂ : E₂ → ℝ) (μ₂ : ℝ) :
    E₁ → Set E₂ :=
  fun x ↦ {u | u ∈ Q₂ ∧ IsMaxOn (smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x) Q₂ u}

-- Proof sketch: unfold `smoothedPrimalObjectiveArgmax`; membership is definitionally the
-- statement that `u` belongs to `Q₂` and maximizes the penalized dual maximand on `Q₂`.
/-- A point belongs to `smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x` exactly when it lies in
the feasible argmax set of `u ↦ ⟪A x, u⟫ - \hat φ(u) - μ₂ d₂(u)` over `Q₂`. -/
@[simp]
theorem mem_smoothedPrimalObjectiveArgmax_iff
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) (Q₂ : Set E₂) (hatφ d₂ : E₂ → ℝ) (μ₂ : ℝ)
    (x : E₁) (u : E₂) :
    u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x ↔
      u ∈ Q₂ ∧ IsMaxOn (smoothedPrimalObjectiveMaximand A hatφ d₂ μ₂ x) Q₂ u :=
  Iff.rfl

end
