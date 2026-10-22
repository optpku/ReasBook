/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_29

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient StrongConvex

noncomputable section

universe u

section Core

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {p : Seminorm ℝ E} {μ : ℝ} {f : E → ℝ}

/- Definition 2.13 lies in the whole-space strong-convexity domain over a real vector space with
an arbitrary seminorm.

Sampled owner-style declarations:
* `StrongConvexOnWith` in `Definition_2_14`, the chapter owner for strong convexity with respect
  to a seminorm;
* `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem` in `Definition_2_14`, the canonical
  minimizer-to-growth consequence;
* `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt` in `Theorem_2_29`, the
  first-order minimizer criterion for convex functions;
* `hasGradientAt_zero_iff_gradient_eq_zero` in `Definition_1_4_15`, the stationary-point bridge
  from the canonical owner `HasGradientAt f 0 xStar` to the textbook equation `∇ f xStar = 0`.

Source/core/bridge triage:
* source-facing: Definition 2.13 as the whole-space notion of `μ`-strong convexity with respect
  to the seminorm `p`;
* core/canonical: `StrongConvexOnWith p μ Set.univ f`;
* bridge/view: the stationary-point consequences stated below in the Hilbert-space section.

Primitive data:
* the whole-space owner `StrongConvexOnWith p μ Set.univ f`.

Derived API:
* a stationary point is a global minimizer;
* the owner quadratic-growth bound at a stationary point, in both `HasGradientAt` and
  `∇ f xStar = 0` forms;
* the ambient-norm specialization on the source-facing class surface `f ∈ 𝓛^1[μ]`.
-/

/- Definition 2.13: the textbook whole-space strong-convexity condition with respect to `p`
is the chapter owner predicate `StrongConvexOnWith p μ Set.univ f`. -/
#check (StrongConvexOnWith p μ Set.univ f : Prop)

end Core

section InnerProduct

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {p : Seminorm ℝ E} {μ : ℝ} {f : E → ℝ}

namespace StrongConvexOnWith

/-- For a whole-space strongly convex objective, every stationary point is a global minimizer. -/
theorem isMinOn_of_hasGradientAt_zero
    (hf : StrongConvexOnWith p μ Set.univ f) {xStar : E}
    (hgrad : HasGradientAt f 0 xStar) :
    IsMinOn f Set.univ xStar := by
  refine
    (hf.convexOn.isMinOn_iff_variational_inequality_of_hasGradientAt (by simp) hgrad).2 ?_
  intro x hx
  simp

/-- Definition 2.13 implies the standard quadratic-growth bound at every stationary point. -/
theorem quadratic_growth_of_hasGradientAt_zero
    (hf : StrongConvexOnWith p μ Set.univ f) {xStar x : E}
    (hgrad : HasGradientAt f 0 xStar) :
    f x ≥ f xStar + (μ / 2) * (p (x - xStar)) ^ (2 : ℕ) := by
  exact
    hf.quadratic_growth_of_isMinOn_of_mem
      (by simp)
      (hf.isMinOn_of_hasGradientAt_zero hgrad)
      x
      (by simp)

/-- The quadratic-growth consequence can be invoked from the textbook equation `∇ f xStar = 0`
once differentiability at `xStar` is supplied. -/
theorem quadratic_growth_of_gradient_eq_zero
    (hf : StrongConvexOnWith p μ Set.univ f) {xStar x : E}
    (hdiff : DifferentiableAt ℝ f xStar) (hgrad : ∇ f xStar = 0) :
    f x ≥ f xStar + (μ / 2) * (p (x - xStar)) ^ (2 : ℕ) := by
  exact
    hf.quadratic_growth_of_hasGradientAt_zero
      ((hasGradientAt_zero_iff_gradient_eq_zero hdiff).2 hgrad)

end StrongConvexOnWith

/-- Theorem 2.9 on the source-facing class surface `𝓛^1[μ]`: a stationary point of a whole-space
`μ`-strongly convex objective has the standard quadratic-growth lower bound in the ambient norm.
-/
theorem quadratic_growth_of_gradient_eq_zero
    (hf : f ∈ 𝓛^1[μ]) {xStar x : E}
    (hdiff : DifferentiableAt ℝ f xStar) (hgrad : ∇ f xStar = 0) :
    f x ≥ f xStar + (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
  simpa using
    (StrongConvexOnWith.quadratic_growth_of_gradient_eq_zero
      (p := normSeminorm ℝ E) hf hdiff hgrad)

end InnerProduct

end
