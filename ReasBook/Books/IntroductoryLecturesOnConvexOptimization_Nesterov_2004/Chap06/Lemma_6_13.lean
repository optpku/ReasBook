/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_2_8

noncomputable section

open scoped Gradient

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/-
Lemma 6.13 lies in Chapter 6's excessive-gap / smoothed-primal-objective domain.

Mandatory domain-style sampling before refinement:
- `smoothedPrimalObjective` and `smoothedPrimalObjective_apply` in `Chap06/Definition_6_30`, the
  chapter owner of the smoothed primal value `f_{μ₂}`;
- `smoothed_primal_objective_at_x0_le_dual_value_at_V` in `Chap06/Lemma_6_2_8`, the existing
  chapter theorem already stated on the owner surface `smoothedPrimalObjective`;
- `satisfiesExcessiveGapCondition` in `Chap06/Definition_6_34`, the later Chapter 6 owner for the
  direction `f_{μ₂}(\bar x) ≤ φ(\bar u)`.

Best owner abstraction:
- source-facing: the textbook inequality at `\bar x = x₀(u₀)` and `\bar u = V(u₀)`;
- core/canonical: `smoothedPrimalObjective`;
- bridge/view: this recall surface, which reuses the earlier owner theorem directly.

Primitive data:
- the primal-dual data `A`, `Q₂`, `hatf`, `hatφ`, `d₂`;
- the selections `x₀`, `V`, the base point `u₀`, and the smoothing constant `μ₂`;
- the Lipschitz and penalty-corrected model assumptions already used in `Lemma_6_2_8`.

Derived API:
- the owner theorem in `Lemma_6_2_8`;
- later reformulations such as `satisfiesExcessiveGapCondition`.

The previous version duplicated the owner theorem under a second local name. This file now keeps
Lemma 6.13 as a direct recall of the canonical Chapter 6 declaration instead of a parallel theorem
shell.
-/

/-
Lemma 6.13 recalls the Chapter 6 owner theorem for the one-point excessive-gap inequality at
`barx = x₀(u₀)` and `baru = V(u₀)`.
-/
recall smoothed_primal_objective_at_x0_le_dual_value_at_V
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₂ : Set E₂}
    {φ hatφ : E₂ → ℝ} {hatf : E₁ → ℝ} {d₂ : E₂ → ℝ}
    {x₀ : E₂ → E₁} {V : E₂ → E₂} {u₀ : E₂} {μ₂ : NNReal}
    (hQ₂_convex : Convex ℝ Q₂)
    (hu₀ : u₀ ∈ Q₂)
    (hφ_hasGradientWithinAt :
      ∀ ⦃u : E₂⦄, u ∈ Q₂ →
        HasGradientWithinAt φ (gradientWithin φ Q₂ u) Q₂ u)
    (hφ_gradient_lipschitz :
      LipschitzOnWith μ₂ (fun u ↦ gradientWithin φ Q₂ u) Q₂)
    (hV_max :
      IsMaxOn
        (fun u ↦
          φ u₀ +
            inner ℝ (gradientWithin φ Q₂ u₀) (u - u₀) -
              ((μ₂ : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ))
        Q₂
        (V u₀))
    (hφ_eq :
      φ u₀ = -hatφ u₀ + A (x₀ u₀) u₀ + hatf (x₀ u₀))
    (hgradφ_eq :
      gradientWithin φ Q₂ u₀ =
        (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u₀)) - gradientWithin hatφ Q₂ u₀)
    (hhatφ_model :
      ∀ ⦃u : E₂⦄, u ∈ Q₂ →
        -hatφ u ≤
          -hatφ u₀ - inner ℝ (gradientWithin hatφ Q₂ u₀) (u - u₀) +
            (μ₂ : ℝ) * d₂ u -
            ((μ₂ : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ)) :
    smoothedPrimalObjective A Q₂ hatf hatφ d₂ (μ₂ : ℝ) (x₀ u₀) ≤ φ (V u₀)

end
