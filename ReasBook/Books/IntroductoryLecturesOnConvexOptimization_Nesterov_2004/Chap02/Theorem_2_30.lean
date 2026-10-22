/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace StrongConvexOn

/- Theorem 2.30 lies in the chapter's strong-convexity / quadratic-growth domain on real normed
spaces.

Sampled owner-style declarations:
* `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem` in `Definition_2_14`
* `strongConvexOnWith_normSeminorm_iff` in `Definition_2_14`
* mathlib `StrongConvexOn`

Best owner abstraction:
* core/canonical: `StrongConvexOnWith (normSeminorm ℝ E) μ Q f`
* bridge/view public surface: `StrongConvexOn Q μ f`

Primitive data:
* the strong-convexity hypothesis `hf : StrongConvexOn Q μ f`
* a feasible minimizer `hxStar : IsMinOn f Q xStar`

Derived API:
* the ambient-norm quadratic-growth estimate at feasible points
* the whole-space specialization

Source/core/bridge triage:
* source-facing: Theorem 2.30, stated on the ambient owner `StrongConvexOn`
* core/canonical: `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem`
* bridge/view: `strongConvexOnWith_normSeminorm_iff`

This file therefore keeps only the ambient bridge theorem and derives it from the owner theorem in
`Definition_2_14`, instead of re-proving the same quadratic-growth argument locally.
-/

variable {μ : ℝ} {Q : Set E} {f : E → ℝ}

/-- A minimizer of a strongly convex function on a feasible set satisfies the standard quadratic
growth bound at every feasible point. -/
theorem quadratic_growth_of_isMinOn_of_mem
    (hf : StrongConvexOn Q μ f) {xStar : E}
    (hxStar_mem : xStar ∈ Q) (hxStar : IsMinOn f Q xStar)
    (x : E) (hx : x ∈ Q) :
    f x ≥ f xStar + (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
  -- Route correction: reuse the canonical `StrongConvexOnWith` quadratic-growth theorem rather
  -- than rebuilding a separate first-order optimality argument in this item file.
  by_cases hμ : 0 < μ
  · have hf' : StrongConvexOnWith (normSeminorm ℝ E) μ Q f :=
      strongConvexOnWith_normSeminorm_iff.2 ⟨hμ, hf⟩
    -- In the positive-curvature branch, the normed-space statement is exactly the owner theorem.
    simpa using hf'.quadratic_growth_of_isMinOn_of_mem hxStar_mem hxStar x hx
  · have hμ_nonpos : μ ≤ 0 := le_of_not_gt hμ
    have hmin : f xStar ≤ f x := hxStar hx
    -- When `μ ≤ 0`, the quadratic term is nonpositive, so minimality alone gives the bound.
    nlinarith [sq_nonneg ‖x - xStar‖]

/-- Theorem 2.30: if `f : E → ℝ` is `μ`-strongly convex on the normed space `E`, `xStar` is a
global minimizer of `f`, then every point `x` satisfies the quadratic growth bound
`f x ≥ f xStar + (μ / 2) ‖x - xStar‖²`. -/
theorem quadratic_growth_of_isMinOn
    (hf : StrongConvexOn Set.univ μ f) {xStar : E}
    (hxStar : IsMinOn f Set.univ xStar) (x : E) :
    f x ≥ f xStar + (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ) :=
  -- Specialize the feasible-set estimate to the whole space.
  hf.quadratic_growth_of_isMinOn_of_mem (by simp) hxStar x (by simp)

end StrongConvexOn
