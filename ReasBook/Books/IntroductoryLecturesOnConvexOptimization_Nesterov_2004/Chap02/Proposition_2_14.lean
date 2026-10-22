/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_30

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Proposition 2.14 lies in the regularized minimization owner domain on a real inner-product space.

Sampled owner-style declarations in this domain:
* `quadraticallyRegularizedObjective` in `Definition_1_4_17`, the chapter owner of the centered
  quadratic regularization;
* mathlib `strongConvexOn_iff_convex`, the canonical owner criterion for strong convexity in a real
  inner-product space;
* `StrongConvexOn.add_convexOn` in `Proposition_2_3`, the bridge adding a convex perturbation to a
  strongly convex owner;
* `StrongConvexOn.quadratic_growth_of_isMinOn` in `Theorem_2_30`, the canonical quadratic-growth
  consequence at a minimizer.

Best owner abstraction:
* source-facing: Proposition 2.14, the regularized minimizer estimate;
* core/canonical: `quadraticallyRegularizedObjective f δ x0` together with whole-space
  `StrongConvexOn Set.univ δ` and `IsMinOn`;
* bridge/view: the Euclidean `ℝⁿ` specialization obtained by instantiating
  `E := EuclideanSpace ℝ (Fin n)`.

Primitive data:
* the convex objective `f`,
* the base point `x0`,
* the regularization parameter `δ > 0`,
* a minimizer `xStar` of `f`,
* a minimizer `xDeltaStar` of `quadraticallyRegularizedObjective f δ x0`.

Derived API for the proof:
* `quadraticallyRegularizedObjective_zero_strongConvexOn`, the owner strong-convexity theorem for
  the centered quadratic penalty;
* `StrongConvexOn.add_convexOn` upgrades `quadraticallyRegularizedObjective f δ x0` to a
  `δ`-strongly convex objective on `Set.univ`;
* `StrongConvexOn.quadratic_growth_of_isMinOn` gives the quadratic growth estimate at the
  regularized minimizer.

No parallel public wrapper around that owner strong-convexity API is introduced here.
-/

/-- Proposition 2.14: if `xStar` minimizes a convex function `f` on a real inner-product space and
`xDeltaStar`
minimizes the quadratically regularized objective
`x ↦ f x + (δ / 2) ‖x - x₀‖²` with `δ > 0`, then the regularized minimizer satisfies the squared
distance contraction
`‖xDeltaStar - x₀‖² + ‖xDeltaStar - xStar‖² ≤ ‖x₀ - xStar‖²`. The textbook `ℝⁿ` statement is the
Euclidean specialization. -/
-- Proof sketch: the centered quadratic penalty is `δ`-strongly convex, so adding it to the
-- convex objective `f` makes `quadraticallyRegularizedObjective f δ x0` `δ`-strongly convex on
-- `Set.univ`. Applying the owner quadratic-growth theorem at the minimizer `xDeltaStar` and then
-- comparing the objective values of `xStar` and `xDeltaStar` yields the displayed squared-distance
-- inequality.
theorem regularized_minimizer_sqdist_add_sqdist_le_sqdist
    (f : E → ℝ) (hf_conv : ConvexOn ℝ Set.univ f)
    (xStar : E) (hxStar : IsMinOn f Set.univ xStar)
    (x0 xDeltaStar : E) {δ : ℝ} (hδ : 0 < δ)
    (hxDeltaStar : IsMinOn (quadraticallyRegularizedObjective f δ x0) Set.univ xDeltaStar) :
    ‖xDeltaStar - x0‖ ^ 2 + ‖xDeltaStar - xStar‖ ^ 2 ≤ ‖x0 - xStar‖ ^ 2 := by
  have hsum :
      f + quadraticallyRegularizedObjective (fun _ : E ↦ 0) δ x0 =
        quadraticallyRegularizedObjective f δ x0 := by
    funext x
    simp [quadraticallyRegularizedObjective_apply]
  have hstrong : StrongConvexOn Set.univ δ (quadraticallyRegularizedObjective f δ x0) := by
    rw [← hsum]
    exact
      (quadraticallyRegularizedObjective_zero_strongConvexOn x0 δ).add_convexOn hf_conv
  have hquad := StrongConvexOn.quadratic_growth_of_isMinOn hstrong hxDeltaStar xStar
  have hmin : f xStar ≤ f xDeltaStar := hxStar (by simp)
  have hquad' :
      f xStar + (δ / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) ≥
        f xDeltaStar + (δ / 2) * ‖xDeltaStar - xStar‖ ^ (2 : ℕ) +
          (δ / 2) * ‖xDeltaStar - x0‖ ^ (2 : ℕ) := by
    simpa [quadraticallyRegularizedObjective_apply, add_assoc, add_left_comm, add_comm,
      norm_sub_rev xStar xDeltaStar, norm_sub_rev xStar x0] using hquad
  nlinarith [hδ, hmin, hquad']

/-- If the reference radius `R₀` dominates the distance from `x₀` to a minimizer `xStar`, then
the minimizer of the quadratically regularized objective lies in the closed ball of radius `R₀`
centered at `x₀`. -/
-- Proof sketch: apply
-- `regularized_minimizer_sqdist_add_sqdist_le_sqdist` to get
-- `‖xDeltaStar - x₀‖² ≤ ‖x₀ - xStar‖²`, combine this with `‖x₀ - xStar‖ ≤ R₀`, and take square
-- roots using nonnegativity of norms.
theorem regularized_minimizer_norm_le_of_norm_le
    (f : E → ℝ) (hf_conv : ConvexOn ℝ Set.univ f)
    (xStar : E) (hxStar : IsMinOn f Set.univ xStar)
    (x0 xDeltaStar : E) {δ : ℝ} (hδ : 0 < δ)
    (hxDeltaStar : IsMinOn (quadraticallyRegularizedObjective f δ x0) Set.univ xDeltaStar)
    {R0 : ℝ} (hR0 : ‖x0 - xStar‖ ≤ R0) :
    ‖xDeltaStar - x0‖ ≤ R0 := by
  have hsq : ‖xDeltaStar - x0‖ ^ 2 ≤ ‖x0 - xStar‖ ^ 2 := by
    have hsq_add :=
      regularized_minimizer_sqdist_add_sqdist_le_sqdist
        f hf_conv xStar hxStar x0 xDeltaStar hδ hxDeltaStar
    nlinarith [sq_nonneg ‖xDeltaStar - xStar‖]
  have hR0_nonneg : 0 ≤ R0 := le_trans (norm_nonneg _) hR0
  have hx0_sq : ‖x0 - xStar‖ ^ 2 ≤ R0 ^ 2 := by
    simpa [pow_two] using (sq_le_sq₀ (norm_nonneg _) hR0_nonneg).2 hR0
  have hDelta_sq : ‖xDeltaStar - x0‖ ^ 2 ≤ R0 ^ 2 := le_trans hsq hx0_sq
  simpa [pow_two] using
    (sq_le_sq₀ (norm_nonneg _) hR0_nonneg).1 (by simpa [pow_two] using hDelta_sq)
