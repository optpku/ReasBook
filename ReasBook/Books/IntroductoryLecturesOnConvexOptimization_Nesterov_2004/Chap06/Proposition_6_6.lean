/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Proposition 6.6 lies in the convex dual-smoothing uniqueness domain.

Sampled owner-style declarations:
- mathlib `IsMaxOn` and `isMaxOn_iff`, the canonical maximizer owner and its textbook expansion;
- mathlib `StrongConvexOn`, the canonical owner for the displayed `1`-strong convexity estimate;
- mathlib `StrongConvexOn.strictConvexOn`, the passage from strong convexity to strict convexity;
- mathlib `StrictConcaveOn.eq_of_isMaxOn`, the canonical uniqueness theorem for maximizers of a
  strictly concave function.

Best owner abstraction:
- source-facing: uniqueness of a feasible maximizer of the regularized dual maximand;
- core/canonical: `u ∈ Q₂`, `IsMaxOn (...) Q₂ u`, and `StrongConvexOn Q₂ 1 d₂`;
- bridge/view: the derived strict concavity of `u ↦ ℓ u - φ u - μ * d₂ u` on `Q₂`.

Primitive data:
- the feasible set `Q₂`;
- the linear functional `ℓ`;
- the dual penalty `φ`;
- the prox term `d₂`;
- the positivity hypothesis `0 < μ`;
- the convexity hypothesis `ConvexOn ℝ Q₂ φ`;
- the strong-convexity hypothesis `StrongConvexOn Q₂ 1 d₂`.

Derived API:
- the feasible-maximizer hypotheses `u ∈ Q₂`, `v ∈ Q₂`, `IsMaxOn (...) Q₂ u`,
  and `IsMaxOn (...) Q₂ v`;
- uniqueness via `StrictConcaveOn.eq_of_isMaxOn`.

Source/core/bridge triage:
- source-facing: `smoothed_maximizer_unique`;
- core/canonical: `IsMaxOn` and `StrongConvexOn`;
- bridge/view: strict concavity of the regularized maximand.

The previous file duplicated the canonical maximizer owner by introducing the local wrapper
`IsOptimalSolutionOn`, and it restated the strong-convexity owner as a raw Jensen inequality.
This refinement deletes that parallel API and states the proposition directly through the
canonical owners already used across the chapter and mathlib.
-/

-- Proof sketch: `StrongConvexOn Q₂ 1 d₂` makes `u ↦ -μ * d₂ u` strictly concave on `Q₂` when
-- `μ > 0`, the affine term `ℓ` is both convex and concave, and `-φ` is concave because `φ` is
-- convex. Hence the regularized maximand is strictly concave on `Q₂`, and
-- `StrictConcaveOn.eq_of_isMaxOn` shows that two feasible maximizers coincide.
/-- Proposition 6.6: if `\hat φ` is convex on `Q₂`, `d₂` is `1`-strongly convex on `Q₂`, and
`μ > 0`, then the maximization problem
`max_{u ∈ Q₂} {ℓ(u) - \hat φ(u) - μ d₂(u)}` has at most one feasible maximizer. In particular,
whenever the smoothed maximizer exists, it is uniquely defined. -/
theorem smoothed_maximizer_unique
    {Q₂ : Set E} (ℓ : E →L[ℝ] ℝ) {d₂ φ : E → ℝ}
    (hφ : ConvexOn ℝ Q₂ φ) (hd₂ : StrongConvexOn Q₂ 1 d₂) {μ : ℝ} (hμ : 0 < μ)
    {u v : E} (hu_mem : u ∈ Q₂) (hv_mem : v ∈ Q₂)
    (hu : IsMaxOn (fun w ↦ ℓ w - φ w - μ * d₂ w) Q₂ u)
    (hv : IsMaxOn (fun w ↦ ℓ w - φ w - μ * d₂ w) Q₂ v) :
    u = v := by
  have hμd₂ : StrictConvexOn ℝ Q₂ (fun w ↦ μ * d₂ w) := by
    have hd₂_strict : StrictConvexOn ℝ Q₂ d₂ :=
      hd₂.strictConvexOn zero_lt_one
    refine ⟨hd₂.1, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have hstrict := hd₂_strict.2 hx hy hxy ha hb hab
    calc
      μ * d₂ (a • x + b • y) < μ * (a • d₂ x + b • d₂ y) :=
        mul_lt_mul_of_pos_left hstrict hμ
      _ = a • (μ * d₂ x) + b • (μ * d₂ y) := by ring
  have hstrict :
      StrictConcaveOn ℝ Q₂ (fun w ↦ ℓ w - φ w - μ * d₂ w) :=
    (ℓ.toLinearMap.concaveOn hd₂.1).sub hφ |>.sub_strictConvexOn hμd₂
  exact hstrict.eq_of_isMaxOn hu hv hu_mem hv_mem

end
