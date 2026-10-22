/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_6_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: first-order smooth optimization on real Hilbert spaces.

Sampled owner-style declarations:
* `LipschitzWith L (∇ f)` in `Definition_1_5_2`, the canonical gradient-Lipschitz owner
  hypothesis;
* mathlib `contDiff_one_iff_fderiv`, which identifies `C¹` regularity with differentiability plus
  continuity of `fderiv`;
* `gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient` in `Lemma_1_6_6`, the
  owner one-step descent theorem with arbitrary stepsize.

Best owner abstraction:
* `source-facing`: Lemma 2.16's reciprocal-`L` gradient-step descent estimate on the real
  inner-product-space owner layer, whose specialization `E = EuclideanSpace ℝ (Fin n)` recovers
  the textbook `ℝⁿ` statement;
* `core/canonical`: the Chapter 1 owner theorem
  `gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient`;
* `bridge/view`: the gradient-to-derivative identification
  `fderiv ℝ f = fun x ↦ (InnerProductSpace.toDual ℝ E) (∇ f x)`, which turns Lipschitz continuity
  of `∇ f` into continuity of `fderiv`.

Primitive data:
* `Differentiable ℝ f`;
* the `L`-Lipschitz gradient bound on the ambient norm.

Derived API:
* the local `ContDiff ℝ 1 f` bridge obtained from differentiability and the Lipschitz-gradient
  hypothesis;
* the reciprocal-`L` specialization of the owner one-step descent theorem.

The Chapter 2 theorem remains source-facing because its hypotheses are weaker than the Chapter 1
owner theorem, but its proof should route through that owner theorem rather than reprove the same
descent estimate from scratch, so the intermediate `C¹` upgrade is kept local to the proof rather
than exposed as a second public owner. -/

/-- Lemma 2.16 on the real inner-product-space owner layer: for a differentiable function with
`L`-Lipschitz gradient, the gradient step of size `1 / L` decreases the objective by at least
`(1 / (2 * L)) * ‖∇ f x‖²` at every point. The textbook `ℝⁿ` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: Lipschitz continuity of `∇ f` makes `x ↦ fderiv ℝ f x` continuous via the Riesz
-- identification, so `f` is `C¹` by `contDiff_one_iff_fderiv`. Then Lemma 1.6.6 applies with
-- stepsize `h = 1 / L`.
theorem gradient_step_value_descent_of_lipschitzGradient
    (f : E → ℝ) {L : ℝ} (hL : 0 < L)
    (hf : Differentiable ℝ f)
    (hgrad : LipschitzWith ⟨L, le_of_lt hL⟩ (∇ f))
    (x : E) :
    f (x - (1 / L) • ∇ f x) ≤
      f x - (1 / (2 * L)) * ‖∇ f x‖ ^ (2 : ℕ) := by
  have hfC1 : ContDiff ℝ 1 f := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨hf, ?_⟩
    have hEq : fderiv ℝ f = fun y ↦ InnerProductSpace.toDual ℝ E (∇ f y) := by
      funext y
      simpa using (hf y).hasGradientAt.hasFDerivAt.fderiv
    have hcont : Continuous (fun y ↦ InnerProductSpace.toDual ℝ E (∇ f y)) :=
      (InnerProductSpace.toDual ℝ E).continuous.comp hgrad.continuous
    simpa [hEq] using hcont
  have hcoeff : (1 / L) * (1 - (L * (1 / L)) / 2) = 1 / (2 * L) := by
    field_simp [ne_of_gt hL]
    ring
  calc
    f (x - (1 / L) • ∇ f x) ≤
        f x - ((1 / L) * (1 - (L * (1 / L)) / 2)) * ‖∇ f x‖ ^ (2 : ℕ) := by
      simpa using
        gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient
          hfC1 hgrad x (1 / L)
    _ = f x - (1 / (2 * L)) * ‖∇ f x‖ ^ (2 : ℕ) := by
      rw [hcoeff]
